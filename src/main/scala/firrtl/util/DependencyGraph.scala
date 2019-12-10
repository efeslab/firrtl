
package firrtl

import firrtl.ir._
import firrtl.passes._
import firrtl.annotations._
import firrtl.graph._
import firrtl.analyses.InstanceGraph
import firrtl.Mappers._
import firrtl.Utils.{throwInternalError, kind}
import firrtl.MemoizedHash._

import collection.mutable

package object util {

  /** 
   * Based on LogicNode ins CheckCombLoops, currently kind of faking it.
   *
   * WrappedExpression is basically an Expression. MemoizedHash just has some
   * hashCode stuff wrapped around it too.
   *
   * See [[firrtl.transforms.CheckCombLoops]] for inspiration.
   */
  type LogicNode = MemoizedHash[WrappedExpression]

  object LogicNode {
    // iangneal: The apply function is syntatic sugar for method invocation, so
    // LogicNode(...) is equivalent to LogicNode.apply(...). 
    def apply(moduleName: String, expr: Expression): LogicNode =
      WrappedExpression(Utils.mergeRef(WRef(moduleName), expr))
    def apply(moduleName: String, name: String): LogicNode = apply(moduleName, WRef(name))
    def apply(component: ComponentName): LogicNode = {
      // Currently only leaf nodes are supported TODO implement
      val loweredName = LowerTypes.loweredName(component.name.split('.'))
      apply(component.module.name, WRef(loweredName))
    }
    /** External Modules are representated as a single node driven by all inputs and driving all
      * outputs
      */
    def apply(ext: ExtModule): LogicNode = LogicNode(ext.name, ext.name)
  }

  /**
   * This constructs a dependency graph.
   *
   * See [[firrtl.transforms.DeadCodeElimination]] for the inspiration code.
   */

  object DependencyGraph {


    /** Expression used to represent outputs in the circuit (# is illegal in names) */
    private val circuitSink = LogicNode("#Top", "#Sink")

    /** Extract all References and SubFields from a possibly nested Expression */
    def extractRefs(expr: Expression): Seq[Expression] = {
      val refs = mutable.ArrayBuffer.empty[Expression]
      // Recursive call to extract all the references.
      def rec(e: Expression): Expression = {
        e match {
          case ref @ (_: WRef | _: WSubField) => refs += ref
          case nested @ (_: Mux | _: DoPrim | _: ValidIf) => nested map rec
          case ignore @ (_: Literal) => // Do nothing
          case unexpected => throwInternalError()
        }
        e
      }
      rec(expr)
      refs
    }

    /**
     * Gets all dependencies and constructs LogicNodes from them.
     *
     * Essentially, for each reference/subfield contained in expr, generate all
     * logic nodes.
     */
    private def getDepsImpl(mname: String,
                            instMap: collection.Map[String, String])
                           (expr: Expression): Seq[LogicNode] =
      extractRefs(expr).map { e =>
        if (kind(e) == InstanceKind) {
          val (inst, tail) = Utils.splitRef(e)
          LogicNode(instMap(inst.name), tail)
        } else {
          LogicNode(mname, e)
        }
      }


    /**
     * Construct the dependency graph within this module.
     */
    private def setupDepGraph(depGraph: MutableDiGraph[LogicNode],
                              instMap: collection.Map[String, String])
                             (mod: Module): Unit = {

      // Just some currying.
      def getDeps(expr: Expression): Seq[LogicNode] = getDepsImpl(mod.name, instMap)(expr)

      /**
       * For each type of statement, we do slightly different things.
       */
      def onStmt(stmt: Statement): Unit = stmt match {
        // 
        case DefRegister(_, name, _, clock, reset, init) =>
          val node = LogicNode(mod.name, name)
          depGraph.addVertex(node)
          Seq(clock, reset, init).flatMap(getDeps(_)).foreach(ref => depGraph.addPairWithEdge(node, ref))
        case DefNode(_, name, value) =>
          val node = LogicNode(mod.name, name)
          depGraph.addVertex(node)
          getDeps(value).foreach(ref => depGraph.addPairWithEdge(node, ref))
        case DefWire(_, name, _) =>
          depGraph.addVertex(LogicNode(mod.name, name))
        case mem: DefMemory =>
          // Treat DefMems as a node with outputs depending on the node and node depending on inputs
          // From perpsective of the module or instance, SourceFlow expressions are inputs, SinkFlow are outputs
          val memRef = WRef(mem.name, MemPortUtils.memType(mem), ExpKind, SinkFlow)
          val exprs = Utils.create_exps(memRef).groupBy(Utils.flow(_))
          val sources = exprs.getOrElse(SourceFlow, List.empty).flatMap(getDeps(_))
          val sinks = exprs.getOrElse(SinkFlow, List.empty).flatMap(getDeps(_))
          val memNode = getDeps(memRef) match { case Seq(node) => node }
          depGraph.addVertex(memNode)
          sinks.foreach(sink => depGraph.addPairWithEdge(sink, memNode))
          sources.foreach(source => depGraph.addPairWithEdge(memNode, source))
        case Attach(_, exprs) => // Add edge between each expression
          exprs.flatMap(getDeps(_)).toSet.subsets(2).map(_.toList).foreach {
            case Seq(a, b) =>
              depGraph.addPairWithEdge(a, b)
              depGraph.addPairWithEdge(b, a)
          }
        case Connect(_, loc, expr) =>
          // This match enforces the low Firrtl requirement of expanded connections
          val node = getDeps(loc) match { case Seq(elt) => elt }
          getDeps(expr).foreach(ref => depGraph.addPairWithEdge(node, ref))
        // Simulation constructs are treated as top-level outputs
        case Stop(_,_, clk, en) =>
          Seq(clk, en).flatMap(getDeps(_)).foreach(ref => depGraph.addPairWithEdge(circuitSink, ref))
        case Print(_, _, args, clk, en) =>
          (args :+ clk :+ en).flatMap(getDeps(_)).foreach(ref => depGraph.addPairWithEdge(circuitSink, ref))
        case Block(stmts) => stmts.foreach(onStmt(_))
        case ignore @ (_: IsInvalid | _: WDefInstance | EmptyStmt) => // do nothing
        case other => throw new Exception(s"Unexpected Statement $other")
      }

      // Add all ports as vertices
      mod.ports.foreach {
        case Port(_, name, _, _: GroundType) => depGraph.addVertex(LogicNode(mod.name, name))
        case other => {
          import scala.reflect.ClassTag
          
          def f[T](v: T)(implicit ev: ClassTag[T]) = {
            ev.toString
          }

          throwInternalError(s"Ports foreach: other is type ${f(other)}")
        }
      }
      onStmt(mod.body)
    }

    // TODO Make immutable?
    private def createDependencyGraph(instMaps: collection.Map[String, collection.Map[String, String]],
                                      doTouchExtMods: Set[String],
                                      c: Circuit): MutableDiGraph[LogicNode] = {
      val depGraph = new MutableDiGraph[LogicNode]
      c.modules.foreach {
        case mod: Module => setupDepGraph(depGraph, instMaps(mod.name))(mod)
        case ext: ExtModule =>
          // Connect all inputs to all outputs
          val node = LogicNode(ext)
          // Don't touch external modules *unless* they are specifically marked as doTouch
          // Simply marking the extmodule itself is sufficient to prevent inputs from being removed
          if (!doTouchExtMods.contains(ext.name)) depGraph.addPairWithEdge(circuitSink, node)
          ext.ports.foreach {
            case Port(_, pname, _, AnalogType(_)) =>
              depGraph.addPairWithEdge(LogicNode(ext.name, pname), node)
              depGraph.addPairWithEdge(node, LogicNode(ext.name, pname))
            case Port(_, pname, Output, _) =>
              val portNode = LogicNode(ext.name, pname)
              depGraph.addPairWithEdge(portNode, node)
              // Also mark all outputs as circuit sinks (unless marked doTouch obviously)
              if (!doTouchExtMods.contains(ext.name)) depGraph.addPairWithEdge(circuitSink, portNode)
            case Port(_, pname, Input, _) => depGraph.addPairWithEdge(node, LogicNode(ext.name, pname))
          }
      }
      // Connect circuitSink to ALL top-level ports (we don't want to change the top-level interface)
      val topModule = c.modules.find(_.name == c.main).get
      val topOutputs = topModule.ports.foreach { port =>
        depGraph.addPairWithEdge(circuitSink, LogicNode(c.main, port.name))
      }

      depGraph
    }

    def apply(c: Circuit): DiGraph[LogicNode] = {
      val depGraph = new MutableDiGraph[LogicNode]

      val moduleMap = c.modules.map(m => m.name -> m).toMap
      val iGraph = new InstanceGraph(c)
      val moduleDeps = iGraph.graph.getEdgeMap.map({ case (k,v) =>
        k.module -> v.map(i => i.name -> i.module).toMap
      })

      c.modules.foreach {
        case mod: Module => setupDepGraph(depGraph, moduleDeps(mod.name))(mod)
        case ext: ExtModule =>
          // Connect all inputs to all outputs
          val node = LogicNode(ext)
          ext.ports.foreach {
            case Port(_, pname, _, AnalogType(_)) =>
              depGraph.addPairWithEdge(LogicNode(ext.name, pname), node)
              depGraph.addPairWithEdge(node, LogicNode(ext.name, pname))
            case Port(_, pname, Output, _) =>
              val portNode = LogicNode(ext.name, pname)
              depGraph.addPairWithEdge(portNode, node)
            case Port(_, pname, Input, _) => depGraph.addPairWithEdge(node, LogicNode(ext.name, pname))
          }
      }
      // Connect circuitSink to ALL top-level ports (we don't want to change the top-level interface)
      val topModule = c.modules.find(_.name == c.main).get
      val topOutputs = topModule.ports.foreach { port =>
        depGraph.addPairWithEdge(circuitSink, LogicNode(c.main, port.name))
      }

      DiGraph(depGraph)
    }
  }
}
