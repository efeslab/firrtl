// See LICENSE for license details.
package firrtl.transforms
package ProductProgram

import firrtl._
import firrtl.ir._

// Map functions
import firrtl.Mappers._

import scala.collection.mutable


/** Punch out annotated ports out to the toplevel of the circuit.
    This also has an option to pass a function as a parmeter to generate
    custom output files as a result of the additional ports
  * @note This *does* work for deduped modules
  */
class ProductProgram extends Transform {
  def inputForm: CircuitForm = LowForm
  def outputForm: CircuitForm = LowForm

  def walkModule(m: DefModule): DefModule = {
    val updated = m.map(walkPort(_))
    updated.map(walkStatement(_))
  }

  def walkPort(p: Port): Port = {
    p
  }

  def walkStatement(s: Statement): Statement = {
    val block = mutable.ArrayBuffer[Statement]()
    val 
    val updated = s.map(walkStatement(_))
    updated.map(walkExpression(_))
  }

  def walkExpression(e: Expression): Expression = {
    e
  }

  def execute(state: CircuitState): CircuitState = {
    val c = state.circuit
    val newCircuit = c.copy(modules = c.modules.map(walkModule))
    state.copy(circuit = newCircuit)
  }
}
