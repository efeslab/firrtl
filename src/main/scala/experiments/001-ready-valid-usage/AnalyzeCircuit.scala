// See LICENSE for license details.

package experiments
package experiment1

// Compiler Infrastructure
import firrtl.{Transform, LowForm, CircuitState, Utils}
// Firrtl IR classes
import firrtl.ir.{DefModule, Port}
// Map functions
import firrtl.Mappers._
// Scala's mutable collections
import scala.collection.mutable

/** Ledger tracks [[firrtl.ir.Circuit]] statistics
  *
  * In this experiment, I want to see if I can determine what the names of a 
  * module's inputs and outputs are. This way, I can see if they conform to some
  * kind of read-valid interface.
  *
  * This [[Ledger]] class will be passed along as we walk our circuit and help 
  * us track [[firrtl.ir.DefModule]] information.
  *
  * See [[experiment0.AnalyzeCircuit]]
  */
class Ledger {
  // Current module name
  private var moduleName: Option[String] = None
  // All encountered modules
  private val modules = mutable.Set[String]()
  private val modulePortMap = mutable.Map[String, mutable.Set[String]]()

  def foundPort(port: Port): Unit = moduleName match {
    case None => sys.error("Module name not defined in Ledger!")
    case Some(name) => {
      modulePortMap get name match {
        case None => modulePortMap(name) = mutable.Set[String]()
        case Some(name) => name
      }

      val pName = port.name toLowerCase

      if (pName.contains("ready") || pName.contains("valid")) {
        modulePortMap(name) += port.serialize
      }
    }
  }

  def getModuleName: String = moduleName match {
    case None => Utils.error("Module name not defined in Ledger!")
    case Some(name) => name
  }

  def setModuleName(myName: String): Unit = {
    modules += myName
    moduleName = Some(myName)
  }

  def serialize: String = {
    modules map { myName =>
      s"$myName => ${if (modulePortMap(myName) isEmpty) "is not ready-valid" else modulePortMap(myName).size}}"
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
class AnalyzeCircuit extends Transform {
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
    circuit map walkModule(ledger)

    // Print our ledger
    println(ledger.serialize)

    // Return an unchanged [[firrtl.CircuitState CircuitState]]
    state
  }

  /** Deeply visits every [[firrtl.ir.Statement Statement]] in m. */
  def walkModule(ledger: Ledger)(m: DefModule): DefModule = {
    // Set ledger to current module name
    ledger.setModuleName(m.name)

    /* For each port, run the foundPort method.
     */
    m foreachPort { case port: Port => ledger.foundPort(port) } 
    m
  }
}
