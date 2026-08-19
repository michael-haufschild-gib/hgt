import GaloisForLFunctions.RHTower.SelfDualAnalyticRealZeros
import GaloisForLFunctions.RHTower.DeningerQ8SymplecticGeneratorRealization
import Mathlib.Algebra.Ring.Parity

/-!
# The Artin central-parity reduction in Deninger's no-go theorem

The finite `Q₈` calculation supplies the symplectic type.  This file
formalizes the exact final implication in Deninger Theorem 2.13: a root number
`-1` forces an odd central order, while a real descended symplectic isotypic
component has even multiplicity.  An identification of those two integers is
therefore contradictory.

The structure below intentionally records, rather than fabricates, the
missing arithmetic/cohomological inputs: a quaternion number field with the
specified Artin root number and property (2.12).  The theorem is the literal
unconditional logical reduction from those inputs.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The central numerical data extracted from a proposed real cohomological
realization of an Artin factor.  `order_eq_multiplicity` is Deninger's property
(2.12) at the centre; `multiplicity_even_of_real_descent` is the real
representation-theoretic symplectic parity conclusion. -/
structure DeningerArtinCentralRealization {T : Type*}
    (F : CompletedSelfDualAnalyticFamily T) (t : T) where
  multiplicity : ℕ
  order_eq_multiplicity :
    (analyticOrderAt (F.completed t) (F.center : ℂ)).toNat = multiplicity
  multiplicity_even_of_real_descent : Even multiplicity

/-- A signed self-dual Artin factor has odd central order at root number `-1`. -/
theorem CompletedSelfDualAnalyticFamily.centralOrder_odd_of_rootNumber_neg_one
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T)
    (hroot : F.rootNumber t = -1) :
    Odd (analyticOrderAt (F.completed t) (F.center : ℂ)).toNat := by
  apply (neg_one_pow_eq_neg_one_iff_odd (R := ℂ) (by norm_num : (-1 : ℂ) ≠ 1)).mp
  rw [F.centralParity_sign t, hroot]

/-- Deninger's final contradiction: no real descended symplectic realization
can identify its even isotypic multiplicity with an Artin central order forced
odd by root number `-1`. -/
theorem not_deningerArtinCentralRealization_of_rootNumber_neg_one
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T)
    (hroot : F.rootNumber t = -1) :
    ¬ Nonempty (DeningerArtinCentralRealization F t) := by
  rintro ⟨D⟩
  have hodd : Odd D.multiplicity := by
    rw [← D.order_eq_multiplicity]
    exact F.centralOrder_odd_of_rootNumber_neg_one t hroot
  exact (Nat.not_even_iff_odd.mpr hodd) D.multiplicity_even_of_real_descent

end

end GaloisForLFunctions.RHTower
