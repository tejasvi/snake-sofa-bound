import Sofa3D

open Sofa3D

/-! The proved statements (each `example` restates the `Prop` it proves). -/
example : MainStatement := main
example : WeakStatement := weak
example : ShortStatement := short
example : TwoTubeStatement := two_tube
example : RelaxStatement := relax
example : RelaxValueStatement := relax_value
example : BoundedStatement := bounded

/-! The statements of the other proved theorems. -/
#check @Sofa3D.main_ge
#check @Sofa3D.chord_sq_le_one
#check @Sofa3D.tilt
#check @Sofa3D.prop45
#check @Sofa3D.one_le_Vstar

#print axioms Sofa3D.main
#print axioms Sofa3D.weak
#print axioms Sofa3D.short
#print axioms Sofa3D.main_ge
#print axioms Sofa3D.two_tube
#print axioms Sofa3D.relax
#print axioms Sofa3D.relax_value
#print axioms Sofa3D.bounded
#print axioms Sofa3D.chord_sq_le_one
#print axioms Sofa3D.tilt
#print axioms Sofa3D.prop45
#print axioms Sofa3D.one_le_Vstar
