import GaloisForLFunctions.RHTower.SigmaDivisorJet
import GaloisForLFunctions.RHTower.WeldWeylMultiplicity

/-!
# Local divisor-jet module Weyl no-go

The local divisor jet `C[X]/(X^m)` is a cyclic rank-one module over itself.  Its module
endomorphisms are therefore multiplication operators, and all such endomorphisms commute.  Two
invertible endomorphisms that preserve the complete local-module structure cannot obey a
nontrivial projective Weyl relation.

This corrects the compatibility condition in the dyadic weld--Weyl route.  A live Weyl generator
cannot be linear over the whole local divisor-jet algebra.  The positive successor is a semilinear
or crossed-product action: one generator multiplies in the local algebra while the other twists
the local coordinate, for example by `X -> zeta X`.

The commutant calculation is standard rank-one module theory.  It is recorded as a bridge and a
positive no-go, not as new scientific knowledge.
-/

noncomputable section

namespace RHTower

/-- Endomorphisms of a commutative semiring as a rank-one module over itself commute. -/
theorem moduleEnd_self_commute
    (A : Type*) [CommSemiring A] (U V : Module.End A A) :
    U.comp V = V.comp U := by
  apply LinearMap.ext
  intro x
  calc
    U (V x) = (V x) * U 1 := by
      simpa only [smul_eq_mul, mul_one] using U.map_smul (V x) 1
    _ = (x * V 1) * U 1 := by
      congr 1
      simpa only [smul_eq_mul, mul_one] using V.map_smul x 1
    _ = (x * U 1) * V 1 := by ring
    _ = (U x) * V 1 := by
      congr 1
      symm
      simpa only [smul_eq_mul, mul_one] using U.map_smul x 1
    _ = V (U x) := by
      symm
      simpa only [smul_eq_mul, mul_one] using V.map_smul (U x) 1

/-- Specialization to the complete local divisor-jet module. -/
theorem localDivisorJet_moduleEnd_commute (m : ℕ)
    (U V : Module.End (LocalDivisorJet ℂ m) (LocalDivisorJet ℂ m)) :
    U.comp V = V.comp U :=
  moduleEnd_self_commute (LocalDivisorJet ℂ m) U V

/-- Constant jets remain injective whenever the truncation has positive length. -/
theorem constLocalDivisorJet_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun z : ℂ => jetClass ℂ m (Polynomial.C z)) := by
  intro a b hab
  have hzero : jetClass ℂ m (Polynomial.C (a - b)) = 0 := by
    rw [jetClass]
    change Ideal.Quotient.mk (jetIdeal ℂ m) (Polynomial.C (a - b)) = 0
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr hab
  have hcoeff := (jetClass_eq_zero_iff_coeff_lt_eq_zero ℂ m).mp hzero 0 hm
  exact sub_eq_zero.mp (by simpa using hcoeff)

/-- A projective relation between rank-one module endomorphisms has trivial phase as soon as their
product acts by a unit on the cyclic generator. -/
theorem phase_eq_one_of_moduleEnd_weyl
    (A : Type*) [CommSemiring A] (zeta : A) (U V : Module.End A A)
    (hunit : IsUnit ((U.comp V) 1))
    (hweyl : U.comp V = zeta • (V.comp U)) :
    zeta = 1 := by
  have hcomm := moduleEnd_self_commute A U V
  have hunit' : IsUnit ((V.comp U) 1) := by
    rw [← hcomm]
    exact hunit
  rw [hcomm] at hweyl
  have hw := congrArg (fun W : Module.End A A => W 1) hweyl
  apply hunit'.mul_right_cancel
  simpa [mul_comm] using hw.symm

/-- The image of the cyclic generator under an invertible rank-one module endomorphism is a unit. -/
theorem moduleLinearEquiv_apply_one_isUnit
    (A : Type*) [CommSemiring A] (U : A ≃ₗ[A] A) :
    IsUnit (U 1) := by
  refine ⟨{
    val := U 1
    inv := U.symm 1
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · have happly : U (U.symm 1) = 1 := U.apply_symm_apply 1
    have hlinear : U (U.symm 1) = (U.symm 1) * U 1 := by
      simpa only [smul_eq_mul, mul_one] using U.map_smul (U.symm 1) 1
    rw [hlinear] at happly
    simpa [mul_comm] using happly
  · have happly : U (U.symm 1) = 1 := U.apply_symm_apply 1
    have hlinear : U (U.symm 1) = (U.symm 1) * U 1 := by
      simpa only [smul_eq_mul, mul_one] using U.map_smul (U.symm 1) 1
    rwa [hlinear] at happly

/-- Hence an invertible projective pair in the rank-one module category has phase one. -/
theorem phase_eq_one_of_moduleLinearEquiv_weyl
    (A : Type*) [CommSemiring A] (zeta : A) (U V : A ≃ₗ[A] A)
    (hweyl : U.toLinearMap.comp V.toLinearMap =
      zeta • (V.toLinearMap.comp U.toLinearMap)) :
    zeta = 1 := by
  apply phase_eq_one_of_moduleEnd_weyl A zeta U.toLinearMap V.toLinearMap
  · have hU := moduleLinearEquiv_apply_one_isUnit A U
    have hV := moduleLinearEquiv_apply_one_isUnit A V
    change IsUnit (U (V 1))
    have hlinear : U (V 1) = V 1 * U 1 := by
      simpa only [smul_eq_mul, mul_one] using U.map_smul (V 1) 1
    rw [hlinear]
    exact hV.mul hU
  · exact hweyl

/-- Local divisor-jet form of the phase-one theorem. -/
theorem localDivisorJet_phase_eq_one_of_moduleEnd_weyl (m : ℕ)
    (zeta : LocalDivisorJet ℂ m)
    (U V : Module.End (LocalDivisorJet ℂ m) (LocalDivisorJet ℂ m))
    (hunit : IsUnit ((U.comp V) 1))
    (hweyl : U.comp V = zeta • (V.comp U)) :
    zeta = 1 :=
  phase_eq_one_of_moduleEnd_weyl (LocalDivisorJet ℂ m) zeta U V hunit hweyl

/-- **Dyadic module-linearity no-go.** At every positive dyadic depth, no pair of invertible
endomorphisms linear over the complete positive-length local divisor-jet algebra can realize the
Böttcher Weyl phase. -/
theorem no_dyadic_localDivisorJet_moduleLinearEquiv_weyl
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (U V : LocalDivisorJet ℂ m ≃ₗ[LocalDivisorJet ℂ m] LocalDivisorJet ℂ m) :
    ¬ U.toLinearMap.comp V.toLinearMap =
      jetClass ℂ m (Polynomial.C (Bottcher.dyadicRoot k)) •
        (V.toLinearMap.comp U.toLinearMap) := by
  intro hweyl
  have hphase := phase_eq_one_of_moduleLinearEquiv_weyl
    (LocalDivisorJet ℂ m) (jetClass ℂ m (Polynomial.C (Bottcher.dyadicRoot k))) U V hweyl
  have hphase' : jetClass ℂ m (Polynomial.C (Bottcher.dyadicRoot k)) =
      jetClass ℂ m (Polynomial.C 1) := by
    simpa [jetClass] using hphase
  have hroot : Bottcher.dyadicRoot k = 1 :=
    constLocalDivisorJet_injective hm hphase'
  have horder : 1 < 2 ^ k := one_lt_pow₀ (by omega) hk.ne'
  exact (dyadicWeylPhase_isPrimitiveRoot k).ne_one horder hroot

end RHTower
