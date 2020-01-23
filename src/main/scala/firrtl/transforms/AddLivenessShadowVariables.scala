package firrtl.transforms
package ProductProgram

import firrtl._
import firrtl.ir._

import firrtl.Mappers._

import scala.collection.mutable


/** Adds a shadow liveness variable to each variable in a circuit, according
  * to Iodine's definition. That is, for a variable x, x_liveness is created
  * and set to 1 if it control- or data-dependent on a live value
  */
class AddLivenessShadowVariables extends Transform {
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