/**
  *
  */

package firrtl.annotations.transforms

// Compiler Infrastructure
import firrtl._
// Firrtl IR classes
import firrtl.ir._
// Map functions
import firrtl.Mappers._
// Dependency graph
import firrtl.graph._
import firrtl.util.{DependencyGraph, LogicNode}
// Other
import firrtl.Utils.throwInternalError
// Scala's mutable collections
import scala.collection.mutable


/** AddResetSignalInformation
  *
  */
class AddResetSignalInformation extends Transform {
  /** Requires the [[firrtl.ir.Circuit Circuit]] form to be "low" */
  def inputForm = MidForm
  /** Indicates the output [[firrtl.ir.Circuit Circuit]] form to be "low" */
  def outputForm = MidForm

  /** Called by [[firrtl.Compiler Compiler]] to run your pass. [[firrtl.CircuitState CircuitState]] contains the circuit
    * and its form, as well as other related data.
    */
  def execute(state: CircuitState): CircuitState = {

    // Return an unchanged [[firrtl.CircuitState CircuitState]]
    state
  }
}
