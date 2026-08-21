import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Fiber

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial
open scoped ValuativeRel

attribute [local instance] Ideal.Quotient.field

universe u

#check Module.Finite.of_finite
#check Algebra.IsAlgebraic.of_finite
#check Algebra.IsSeparable.of_algEquiv
#check Algebra.FormallyUnramified.of_map_maximalIdeal
#check Algebra.Etale.of_formallyUnramified_of_flat
#check Module.Flat.of_free

end GaloisForLFunctions.HTGeometry.ABHN
