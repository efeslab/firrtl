// See LICENSE for license details.

/**
  * For this experiment, I want to check for the following things per modules:
  * 1. Does this module (or any sub-modules) have any state?
  * - Stateless modules are inherently safe from wrong-path leakages, as they
  *   are implicitly squashed.
  * 2. If the module has state, is it memory state or register state?
  * - Memory state is inherently vulnerable to wrong-path leakages, so these
  *   modules need external analysis to see if wrong-path information leaks to
  *   them.
  * - Register state is potentially unsafe, depending on how the registers are
  *   reset.
  * 3. If the module has registers, are the reset signals tied to a module-level
  * input?
  * - If so, the module is safe, assuming that the module is used correctly. We
  *   can call this "conditionally safe". Needs further external analysis.
  * - If not, the module needs further analysis to see if internal logic doesn't
  *   leak tainted information.
  *
  * Future work:
  * 4. If the module has uncleared registers, are output signals conditionally
  * dependent on the uncleared state?
  * - Can leverage ready-valid here.
  *
  */

package firrtl
package analyses

// Compiler Infrastructure
import firrtl._
// Firrtl IR classes
import firrtl.ir._
// Map functions
import firrtl.Mappers._
// Dependency graph
import firrtl.graph._
import firrtl.annotations.transforms._
import firrtl.util.{DependencyGraph, LogicNode}
// Other
import firrtl.Utils.throwInternalError
// Scala's mutable collections
import scala.collection.mutable


/**
 * Tracks information about DefRegister reset signals and their sources.
 *
 * For a module's set of registers, we want to know the following:
 *
 * - Can the state be flash-cleared? We define flash clearing as the following:
 *   1. All registers are reset only by a combination of module-level inputs.
 *   2. There exists a satisfiable assignment of all signals that simultaneously
 *   asserts all register resets.
 *
 */
case class RegisterResetInfo(moduleName: String, 
                             depGraph: DiGraph[LogicNode],
                             resetSignalInfo: Map[String, ResetSignalInfo]) {
  private val regDefs = mutable.Set[LogicNode]()
  private val regNames = mutable.Set[String]()
  private val regResets = mutable.Set[LogicNode]()
  private val regResetExpr = mutable.Set[Expression]()
  private val regAssign = mutable.Set[LogicNode]()
  private val inputPorts = mutable.Set[LogicNode]()
  private val inputNames = mutable.Set[String]()
  
  def addRegisterDef(r: DefRegister): Unit = {
    if (resetSignalInfo contains r.name) {
      regDefs += LogicNode(moduleName, r.name)
      regNames += r.name
      val resetExpr = resetSignalInfo(r.name).resetSignal
      regResetExpr += resetExpr
      regResets ++= DependencyGraph.extractRefs(resetExpr).map(e => LogicNode(moduleName, e))
      println(s"+\t${r.name} in map")
    } else {
      println(s"-\t${r.name} not in map")
    }
  }

  def addRegAssignment(s: Statement): Unit = s match {
    // "loc" should not be a nested expression
    case Connect(_, loc, _) => regAssign += LogicNode(moduleName, loc)
    case x => throwInternalError(s"I don't know how to handle '${x.serialize}'!")
  }

  def addInputPort(p: Port): Unit = p match {
    case Port(_, name, direction, _) if direction.serialize == "input" => {
      inputPorts += LogicNode(moduleName, p.name)
      inputNames += p.name
    }
    case x => throwInternalError(s"'${x.serialize}' is not an input port!")
  }

  /**
   * For each register, see if its definition reaches any other register reset
   * assignment. If so, that register depends on this register.
   *
   * Do this analysis for each register definition.
   */
  private def regRegDepsExist: Boolean = {
    def regDependsOn(x: LogicNode): Boolean = {
      val regReaches = depGraph.reachableFrom(x)
      !(regReaches intersect regResets).isEmpty
    }

    !regDefs.filter(regDependsOn).isEmpty
  }

  /**
   * For each register definition, determine if the assignment of module inputs
   * to the register is satisfiable.
   */
  private def regAssignmentsSat: Boolean = {
    throwInternalError("TODO: Implement!")
    false
  }

  /**
   * This is a simplier check: are the reset port definitions directly connected
   * to the inputs?
   */
  private def regResetDirect: Boolean = {
    regResetExpr.forall((e: Expression) => e match {
      case Reference(name, _) if inputNames.contains(name) => true
      case WRef(name, _, _, _) if inputNames.contains(name) => true
      case _: Literal => false
      case x => {
        import scala.reflect.ClassTag
        
        def f[T](v: T)(implicit ev: ClassTag[T]) = ev.toString
        throwInternalError(s"Don't know what to do with ${f(x)} '${x.serialize}'!")
      }
    })
  }

  /** 
   * For each register definition, first determine if the resets are even 
   * reachable.
   */
  private def regResetsConnected: Boolean = {
    regResets.forall(l => depGraph.contains(l))
  }

  def getRegNames: Set[String] = regNames.toSet

  def hasRegs: Boolean = !regDefs.isEmpty

  def isSafe: Boolean = {
    regDefs.isEmpty || (regResetsConnected && !regRegDepsExist && regResetDirect)
  }

  def serialize: String = {
    if (regDefs.isEmpty) "has no registers"
    else if (!regResetsConnected) "has registers with disconnected resets"
    else if (!regResetDirect) "has indirect reset signals for registers"
    else if (regRegDepsExist) "has register-register reset dependencies"
    else "has NO clue!!!"
  }
}

/*
 * This [[ModuleSafetyInfo]] class does some stuff.
 */
case class ModuleSafetyInfo(moduleName: String, 
                            depGraph: DiGraph[LogicNode],
                            regResetInfoMap: Map[String, ResetSignalInfo]) {
  // Tracking info about submodules
  private val submodules = mutable.Set[String]()
  private val submoduleInfo = mutable.Map[String, ModuleSafetyInfo]()

  // Tracking info about registers, so we can later do dependency analysis.
  private val regDefs = mutable.Set[LogicNode]()
  // Tracks nodes that aren't reset by the signal
  private val resetSignal = mutable.Map[LogicNode, Set[LogicNode]]()
  private val regInfo = new RegisterResetInfo(moduleName, depGraph, regResetInfoMap)
  
  // Safety information about the immediate module.
  private var hasMemory: Boolean = false

  def updateSubmoduleInfo(submodule: DefModule, msi: ModuleSafetyInfo): Unit = {
    submodules += submodule.name
    submoduleInfo(submodule.name) = msi
  }

  def setHasMemory(b: Boolean): Unit = {
    hasMemory = b
  }

  def addRegisterDef(r: DefRegister): Unit = regInfo.addRegisterDef(r)
  def addRegAssign(s: Statement): Unit = s match {
    case Connect(_, loc, _) => {
      if (regInfo.getRegNames.contains(loc.serialize)) regInfo.addRegAssignment(s)
    }
    case x => ()
  }
  def addInputPort(p: Port): Unit = regInfo.addInputPort(p)

  /*
   * "Immediately" means the immediate module, i.e. excluding submodules.
   */
  def isImmediatelyUnsafe: Boolean = {
    hasMemory || !regInfo.isSafe
  }

  def isSafe: Boolean = {
    val submoduleSafety: Boolean = submodules.map(x => submoduleInfo(x).isSafe).forall(x => x) 
    submoduleSafety && !isImmediatelyUnsafe
  }

  def serialize: String = {
    val is_safe = if (isSafe) "is safe" else "is not safe"
    val submodule = if (isImmediatelyUnsafe || submodules.isEmpty) "because it" else "because one of its submodules"
    val state = if (hasMemory) {
      "has memory (inherently unsafe)"
    } else if (regInfo.hasRegs) {
      regInfo.serialize
    } else {
      "is stateless"
    }
    val subs = submodules map { case modName =>
      s"\t\tsubmodule $modName"
    } mkString "\n"
    val verbose = s"(is immediately unsafe=${isImmediatelyUnsafe}, nsubmodules=${submodules.size}, regstate=${regInfo.serialize})\n$subs"
    s"$moduleName $is_safe, $submodule $state\n\t$verbose"
  }
}

/*
 * This [[Ledger]] class will be passed along as we walk our circuit and help 
 * us track [[firrtl.ir.DefModule]] information.
 *
 * See [[experiment2.AnalyzeCircuit]]
 */
class Ledger {
  // All encountered modules
  private val modules = mutable.Set[String]()
  private val moduleSafety = mutable.Map[String, ModuleSafetyInfo]()

  def hasModule(moduleName: String): Boolean = {
    moduleSafety contains moduleName 
  }

  def addModule(modName: String, modInfo: ModuleSafetyInfo): Unit = hasModule(modName) match {
    case true => sys.error(s"$modName already contained in ledger")
    case false => moduleSafety(modName) = modInfo
  }

  def serialize: String = {
    moduleSafety map { case (modName, modInfo) =>
      s"$modName => ${modInfo.serialize}"
    } mkString "\n"
  }
}


/** AnalyzeCircuit Transform
  *
  * Walks [[firrtl.ir.Circuit Circuit]], and records the number of muxes it finds, per module.
  *
  * While some compiler frameworks operate on graphs, we represent a Firrtl circuit using a tree representation:
  *   - A Firrtl [[firrtl.ir.Circuit Circuit]] contains a sequence of [[firrtl.ir.DefModule DefModule]]s.
  *   - A [[firrtl.ir.DefModule DefModule]] contains a sequence of [[firrtl.ir.Port Port]]s, and maybe a
  *     [[firrtl.ir.Statement Statement]].
  *   - A [[firrtl.ir.Statement Statement]] can contain other [[firrtl.ir.Statement Statement]]s, or
  *     [[firrtl.ir.Expression Expression]]s.
  *   - A [[firrtl.ir.Expression Expression]] can contain other [[firrtl.ir.Expression Expression]]s.
  *
  * To visit all Firrtl IR nodes in a circuit, we write functions that recursively walk down this tree. To record
  * statistics, we will pass along the [[Ledger]] class and use it when we come across a [[firrtl.ir.Mux Mux]].
  *
  * See the following links for more detailed explanations:
  * Firrtl's IR:
  *   - https://github.com/ucb-bar/firrtl/wiki/Understanding-Firrtl-Intermediate-Representation
  * Traversing a circuit:
  *   - https://github.com/ucb-bar/firrtl/wiki/traversing-a-circuit for more
  * Common Pass Idioms:
  *   - https://github.com/ucb-bar/firrtl/wiki/Common-Pass-Idioms
  */
class CheckSpeculativeSafety extends Transform {
  /** Requires the [[firrtl.ir.Circuit Circuit]] form to be "low" */
  def inputForm = LowForm
  /** Indicates the output [[firrtl.ir.Circuit Circuit]] form to be "low" */
  def outputForm = LowForm

  /** Called by [[firrtl.Compiler Compiler]] to run your pass. [[firrtl.CircuitState CircuitState]] contains the circuit
    * and its form, as well as other related data.
    */
  def execute(state: CircuitState): CircuitState = {

    val ledger = new Ledger()
    val circuit = state.circuit

    /* Execute the function walkModule(ledger) on every [[firrtl.ir.DefModule DefModule]] in circuit, returning a new
     * [[Circuit]] with new [[scala.collection.Seq Seq]] of [[firrtl.ir.DefModule DefModule]].
     *   - "higher order functions" - using a function as an object
     *   - "function currying" - partial argument notation
     *   - "infix notation" - fancy function calling syntax
     *   - "map" - classic functional programming concept
     *   - discard the returned new [[firrtl.ir.Circuit Circuit]] because circuit is unmodified
     */
    circuit map walkModule(state, ledger)

    // Print our ledger
    println(ledger.serialize)

    // Return an unchanged [[firrtl.CircuitState CircuitState]]
    state
  }

  /** Deeply visits every [[firrtl.ir.Statement Statement]] in m. */
  def walkModule(state: CircuitState, ledger: Ledger)(m: DefModule): DefModule = {
    /*
     * Check if we've done this one before. If so, terminate.
     */
    if (ledger.hasModule(m.name)) {
      println(s"Already did ${m.name}")
      return m
    }

    /* 
     * We do a depth-first search so we accumulate all the submodule information
     * before computing the safety of this module.
     */
    m map walkSubmodules(state, ledger)

    val depGraph: DiGraph[LogicNode] = DependencyGraph(state.circuit)
    val annotations = state.annotations.collect(
                      {case a: ResetSignalInfo => a}).map(a => a.regName -> a).toMap
    val modInfo = new ModuleSafetyInfo(m.name, depGraph, annotations)
    /*
     * Now, we check this module.
     *
     * Step 1: determine if the module is stateful or not.
     * Step 2: If the module is stateful, check if it has a reset signal. If not,
     * it is definitely unsafe.
     */
    m map walkStatements(modInfo)

    /*
     * Step 3: Find this module's reset signal, if it has one. If it does, 
     * follow the dependency graph to see if all registers are connected to the
     * top reset signal.
     *
     * This is equivalent to finding a path from the top-level reset to the 
     * reset signal of the register.
     */

    m map walkPorts(state, depGraph, m.name, modInfo)

    // Add the modInfo to the ledger
    ledger.addModule(m.name, modInfo)

    m
  }

  /**
   * Implemented as a map over ports.
   */
  def walkPorts(state: CircuitState, depGraph: DiGraph[LogicNode], 
    moduleName: String, modInfo: ModuleSafetyInfo)(p: Port): Port = {

    p match {
      case Port(_, name, direction, _) if direction.serialize == "input" => {
        modInfo.addInputPort(p)
      }
      case x => x
    }

    p
  }

  def walkSubmodules(state: CircuitState, ledger: Ledger)(s: Statement): Statement = {
    /*
     * Examine the statement. If it is an instance statement, it instantiates a
     * module. We can extract the module and walk it from the circuit.
     */
    s match {
      case DefInstance(_, _, mName) => {
        state.circuit.modules.find(m => m.name == mName) match {
          case None => None
          case Some(module) => walkModule(state, ledger)(module)
        }
      }
      case notinst => notinst
    }

    // Return the unchanged Statement
    s
  }

  def walkStatements(modInfo: ModuleSafetyInfo)(s: Statement): Statement = {
    s match {
      case r: DefRegister => modInfo.addRegisterDef(r)
      case _: DefMemory => modInfo.setHasMemory(true)
      case x @ (_: Connect) => modInfo.addRegAssign(x)
      case notStateful => notStateful
    }

    // But, statements can contain other statements!
    s map walkStatements(modInfo)
  }
}
