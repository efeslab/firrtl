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

// Proto stuff
import FirrtlProtos._
import firrtl.proto._
import firrtl.passes._

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

  /*
  lazy val resetSignal = ToWorkingIR.toExp(FromProto.convert(resetSignalProto))
  lazy val initValue = ToWorkingIR.toExp(FromProto.convert(initValueProto))
  */
}

object ResetSignalInfo {
  // Remove the WIR forms because they are not consumed by the protobuffers.
  private def toExp(e: Expression): Expression = e map toExp match {
    case ex: WRef => Reference(ex.name, ex.tpe)
    case ex: WSubField => SubField(ex.expr, ex.name, ex.tpe)
    case ex: WSubIndex => SubIndex(ex.expr, ex.value, ex.tpe)
    case ex: WSubAccess => SubAccess(ex.expr, ex.index, ex.tpe)
    case ex => ex // This might look like a case to use case _ => e, DO NOT!
  }

  def apply(r: DefRegister): ResetSignalInfo = {
    /*
    import scala.reflect.ClassTag
    
    def f[T](v: T)(implicit ev: ClassTag[T]) = {
      ev.toString
    }

    println(s"${f(r.reset)} ${r.reset} ${f(r.init)} ${r.init}")
    r foreachExpr(x => x match {
      case r: WRef => println(s"\tWRef ${f(r)} ${x}")
      case x => println(s"\t${f(x)} ${x}")
    })
    val resetProto = ToProto.convert(toExp(r.reset)).build
    val initProto = ToProto.convert(toExp(r.init)).build
    ResetSignalInfo(r.name, resetProto, initProto)
    */
    ResetSignalInfo(r.name, r.reset, r.init)
  }
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
    println(accumulator.serialize)
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
