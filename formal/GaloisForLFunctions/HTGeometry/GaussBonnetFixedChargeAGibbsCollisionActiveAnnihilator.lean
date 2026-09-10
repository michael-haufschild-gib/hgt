import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelPolynomialKernel
import Mathlib.Algebra.Polynomial.Div

/-!
# The intrinsic annihilator of the surviving collision spectrum

The polynomial contains exactly the active collision nodes. Divisibility
by this monic polynomial classifies every finite Hankel null vector, and
its degree agrees with the previously proved spectral rank count.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Polynomial

/-- The monic polynomial of the active collision support; the empty support gives one. -/
def egbFixedChargeAGibbsCollisionActiveAnnihilator (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Polynomial ℝ :=
  (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 then 1 else Polynomial.X - Polynomial.C (4 / 9 : ℝ)) *
    (if egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 1 else Polynomial.X - Polynomial.C (1 / 36 : ℝ))

private theorem product_dvd_iff_roots (p : Polynomial ℝ) :
    (Polynomial.X - Polynomial.C (4 / 9 : ℝ)) *
      (Polynomial.X - Polynomial.C (1 / 36 : ℝ)) ∣ p ↔
      p.eval (4 / 9) = 0 ∧ p.eval (1 / 36) = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    constructor <;> simp [hq, Polynomial.eval_mul]
  · rintro ⟨hr, hs⟩
    have hd : Polynomial.X - Polynomial.C (4 / 9 : ℝ) ∣ p :=
      Polynomial.dvd_iff_isRoot.mpr hr
    obtain ⟨q, hq⟩ := hd
    have hqs : q.eval (1 / 36) = 0 := by
      rw [hq, Polynomial.eval_mul] at hs
      have he : (Polynomial.X - Polynomial.C (4 / 9 : ℝ)).eval (1 / 36) =
          (1 / 36 : ℝ) - 4 / 9 := by simp
      rw [he] at hs
      exact (mul_eq_zero.mp hs).resolve_left (by norm_num)
    have hdq : Polynomial.X - Polynomial.C (1 / 36 : ℝ) ∣ q :=
      Polynomial.dvd_iff_isRoot.mpr hqs
    obtain ⟨u, hu⟩ := hdq
    refine ⟨u, ?_⟩
    rw [hq, hu]
    ring

/-- The complete finite Hankel kernel consists precisely of multiples of the active annihilator polynomial. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_kernel_iff_divisible (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (v : Fin d → ℝ) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).mulVec v = 0 ↔
      egbFixedChargeAGibbsCollisionActiveAnnihilator n β E ∣
        _root_.HTGeometry.finiteHankelNullPolynomial v := by
  rw [egbFixedChargeAGibbsCollisionHankelMatrix_kernel_iff_roots,
    egbFixedChargeAGibbsCollisionActiveAnnihilator]
  by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 <;>
    by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp [ha, hb]
  · rw [if_pos ha, if_neg hb, one_mul]
    simp only [ha, hb, true_or, false_or, true_and]
    exact Polynomial.dvd_iff_isRoot.symm
  · rw [if_neg ha, if_pos hb, mul_one]
    simp only [ha, hb, true_or, false_or, and_true]
    exact Polynomial.dvd_iff_isRoot.symm
  · rw [if_neg ha, if_neg hb]
    simp only [ha, hb, false_or]
    exact (product_dvd_iff_roots _).symm

/-- The intrinsic support polynomial is monic in every spectral class. -/
theorem egbFixedChargeAGibbsCollisionActiveAnnihilator_monic (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionActiveAnnihilator n β E).Monic := by
  by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 <;>
    by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simpa [egbFixedChargeAGibbsCollisionActiveAnnihilator, ha, hb] using
      (Polynomial.monic_one : (1 : Polynomial ℝ).Monic)
  · simpa [egbFixedChargeAGibbsCollisionActiveAnnihilator, ha, hb] using
      Polynomial.monic_X_sub_C (1 / 36 : ℝ)
  · simpa [egbFixedChargeAGibbsCollisionActiveAnnihilator, ha, hb] using
      Polynomial.monic_X_sub_C (4 / 9 : ℝ)
  · simpa [egbFixedChargeAGibbsCollisionActiveAnnihilator, ha, hb] using
      (Polynomial.monic_X_sub_C (4 / 9 : ℝ)).mul (Polynomial.monic_X_sub_C (1 / 36 : ℝ))

/-- The annihilator degree is exactly the number of surviving collision sectors. -/
theorem egbFixedChargeAGibbsCollisionActiveAnnihilator_degree (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (egbFixedChargeAGibbsCollisionActiveAnnihilator n β E).natDegree =
      egbFixedChargeAGibbsCollisionActiveModeCount n β E := by
  have hp := Polynomial.Monic.natDegree_mul
    (Polynomial.monic_X_sub_C (4 / 9 : ℝ)) (Polynomial.monic_X_sub_C (1 / 36 : ℝ))
  by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 <;>
    by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp [egbFixedChargeAGibbsCollisionActiveAnnihilator,
      egbFixedChargeAGibbsCollisionActiveModeCount, ha, hb]
  · simp [egbFixedChargeAGibbsCollisionActiveAnnihilator,
      egbFixedChargeAGibbsCollisionActiveModeCount, ha, hb, Polynomial.natDegree_X_sub_C]
  · simp [egbFixedChargeAGibbsCollisionActiveAnnihilator,
      egbFixedChargeAGibbsCollisionActiveModeCount, ha, hb, Polynomial.natDegree_X_sub_C]
  · rw [egbFixedChargeAGibbsCollisionActiveAnnihilator, if_neg ha, if_neg hb, hp]
    simp [egbFixedChargeAGibbsCollisionActiveModeCount, ha, hb, Polynomial.natDegree_X_sub_C]

end
end GaloisForLFunctions.HTGeometry
