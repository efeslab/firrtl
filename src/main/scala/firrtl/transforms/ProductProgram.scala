// See LICENSE for license details.
package firrtl.transforms
package ProductProgram

import firrtl._
import firrtl.ir._

// Map functions
import firrtl.Mappers._

import scala.collection.mutable


/** Creates a product program according to Iodine's definition.
  * Each original variable x is duplicated to x_r, and statements using
  * x are duplicated to use x_r
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
