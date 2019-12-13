    package firrtl.analyses
    
    // Compiler Infrastructure
    import firrtl._
    // Firrtl IR classes
    import firrtl.ir._
    // Map functions
    import firrtl.Mappers._
    
    import firrtl.passes._
    import firrtl.annotations.transforms.AddResetSignalInformation
    import firrtl.analyses.CheckSpeculativeSafety
    
    /**
     * VerifyModuleSquashability SeqTransform
     */
    class VerifyModuleSquashability extends SeqTransform {
      def inputForm = MidForm
      def outputForm = LowForm
    
      def transforms = Seq(
        /*
         * Simplify aggregate types to generate all the register definitions
         * that would exist in the final circuit.
         */
        passes.LowerTypes,
        passes.ResolveKinds,
        passes.InferTypes,
        passes.ResolveFlows,
        new passes.InferWidths,
        passes.Legalize,
        /*
         * SpecCheck: Analyze reset signals and annotate the FIRRTL.
         */
        new AddResetSignalInformation, 
        /*
         * SpecCheck: Lower to LowFIRRTL so we can generate an accurate
         * dependency graph.
         */
        new MiddleFirrtlToLowFirrtl,
        /*
         * SpecCheck: Analyze modules to determine which are safe/unsafe.
         */
        new CheckSpeculativeSafety)
    }


