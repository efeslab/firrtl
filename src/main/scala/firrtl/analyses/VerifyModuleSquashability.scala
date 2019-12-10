package firrtl.analyses

// Compiler Infrastructure
import firrtl._
// Firrtl IR classes
import firrtl.ir._
// Map functions
import firrtl.Mappers._

import firrtl.annotations.transforms.AddResetSignalInformation
import firrtl.analyses.CheckSpeculativeSafety

/** VerifyModuleSquashability SeqTransform
  * 
  * Composes
  */
class VerifyModuleSquashability extends SeqTransform {
  def inputForm = MidForm
  def outputForm = LowForm

  def transforms = Seq(
    new AddResetSignalInformation, 
    new CheckSpeculativeSafety)
}
