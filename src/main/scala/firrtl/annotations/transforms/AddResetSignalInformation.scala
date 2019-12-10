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
import firrtl.annotations._
// Scala's mutable collections
import scala.collection.mutable

/**
 * See [[firrtl.transforms.DontTouchAnnotation]] for inspiration.
 *
 * See [[firrtl.transforms.InferResets]] for how to transform Expressions into
 * ReferenceTargets.
 */

case class ResetSignalInfo(regName: String, 
                           resetSignal: Expression, 
                           initValue: Expression) extends NoTargetAnnotation {
 
  override def serialize: String = {
    s"$regName has reset signal ${resetSignal.serialize} with value ${initValue.serialize}"
  }

  def isConnected: Boolean = resetSignal match {
    case _: Literal => false
    case _ => true
  }
}

object ResetSignalInfo {
  def apply(r: DefRegister): ResetSignalInfo = ResetSignalInfo(r.name, r.reset, r.init)
}

case class AnnotationAccumulator(state: CircuitState) extends Serializable {
  private val annotations = mutable.ListBuffer.empty[ResetSignalInfo]

  def apply(m: DefModule, s: Statement): Statement = s match {
    case r: DefRegister => {
      annotations += ResetSignalInfo(r)
      s
    }
    case _ => s
  }

  def toAnnotationSeq: AnnotationSeq = AnnotationSeq(annotations.toSeq)

  def serialize: String = {
    annotations map { x =>
      x.serialize
    } mkString "\n"
  }
}

/** AddResetSignalInformation Transform
  *
  */
class AddResetSignalInformation extends Transform {
  /** Requires the [[firrtl.ir.Circuit Circuit]] form to be "low" */
  def inputForm = MidForm
  /** Indicates the output [[firrtl.ir.Circuit Circuit]] form to be "low" */
  def outputForm = MidForm

  /** 
   * To modify the CircuitState, 
   *
   * See [[firrtl.transforms.DeadCodeElimination]] for more examples.
   */
  def execute(state: CircuitState): CircuitState = {
    val accumulator = AnnotationAccumulator(state)
    state.circuit map walkModule(accumulator)

    val newAnnotations = accumulator.toAnnotationSeq ++ state.annotations
    state.copy(annotations = newAnnotations)
  }

  def walkModule(aa: AnnotationAccumulator)(m: DefModule): DefModule = {
    m map walkStatement(aa, m)
    m
  }

  def walkStatement(accumulator: AnnotationAccumulator, m: DefModule)(s: Statement): Statement = {
    accumulator(m, s) 
    s map walkStatement(accumulator, m)
    s
  }
}
