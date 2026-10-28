import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticSectionSpace
import GaloisForLFunctions.RHTower.WeilFullConeSpectralConsistency

/-!
# A common prime horizon for all profiles on a bounded window

The mixed prime source has finitely many possible shifts on a fixed support
window. Each shift is bounded by the two actual square masses. The resulting
bound is uniform over profiles and their derivatives; it needs no coefficient
presentation and no sign condition on the tests.
-/

open MeasureTheory Set Filter Complex
open Zeta23 RHTower RHTower.WeilSpectral

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

/-- Real mixed Weil correlations are the oriented source correlations. -/
theorem weilTest_eq_sectionCorr (f g : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (cx f) (cx g) x = (sectionCorr f g (-x) : ℂ) := by
  rw [WeilSpectral.weilTest_apply, sectionCorr, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [cx, Complex.conj_ofReal, sub_eq_add_neg, Complex.ofReal_mul]

theorem norm_weilTest_le_sectionMass {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (x : ℝ) :
    ‖EF.weilTest (cx f) (cx g) x‖ ≤ (sectionMass f + sectionMass g) / 2 := by
  rw [weilTest_eq_sectionCorr, Complex.norm_real, Real.norm_eq_abs]
  exact abs_sectionCorr_le hf hfc hg hgc (-x)

/-- A common bounded support imposes a common mixed prime horizon. -/
theorem weilTest_eq_zero_of_common_window {f g : ℝ → ℝ} {R x : ℝ}
    (hf : ∀ u, R < |u| → f u = 0) (hg : ∀ u, R < |u| → g u = 0)
    (hx : 2 * R < |x|) : EF.weilTest (cx f) (cx g) x = 0 := by
  rw [weilTest_eq_sectionCorr]
  have hzero : sectionCorr f g (-x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    change f u * g (u + -x) = 0
    by_cases hu : R < |u|
    · rw [hf u hu, zero_mul]
    · have hux : R < |u + -x| := by
        have ht := abs_sub_abs_le_abs_sub x u
        rw [abs_sub_comm x u, sub_eq_add_neg u x] at ht
        linarith only [hx, ht, le_of_not_gt hu]
      rw [hg _ hux, mul_zero]
  rw [hzero, Complex.ofReal_zero]

/-- The actual nonnegative coefficient in the prime comb. -/
def sourcePrimeCoefficient (n : ℕ) : ℝ :=
  if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0

theorem sourcePrimeCoefficient_nonneg (n : ℕ) : 0 ≤ sourcePrimeCoefficient n := by
  unfold sourcePrimeCoefficient
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The prime part has a square-mass bound uniform over all tests in a fixed window. -/
theorem exists_primePart_window_mass_bound (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℝ → ℝ,
      Continuous f → HasCompactSupport f → Continuous g → HasCompactSupport g →
      (∀ u, R < |u| → f u = 0) → (∀ u, R < |u| → g u = 0) →
      |(primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (cx f) (cx g))).re| ≤ C * (sectionMass f + sectionMass g) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (2 * R))
  let C := ∑ n ∈ Finset.range N, sourcePrimeCoefficient n
  have hC : 0 ≤ C := Finset.sum_nonneg fun n _ => sourcePrimeCoefficient_nonneg n
  refine ⟨C, hC, ?_⟩
  intro f g hf hfc hg hgc hs_f hs_g
  have hlarge (n : ℕ) (hn : N ≤ n) : 2 * R < Real.log n := by
    have hne : Real.exp (2 * R) < n := hN.trans_le (by exact_mod_cast hn)
    exact (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hne)).mpr hne
  have hfinite : primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (cx f) (cx g)) =
      ∑ n ∈ Finset.range N, (sourcePrimeCoefficient n : ℂ) *
        (EF.weilTest (cx f) (cx g) (Real.log n) +
          EF.weilTest (cx f) (cx g) (-Real.log n)) := by
    apply tsum_eq_sum
    intro n hn
    have hlog := hlarge n (le_of_not_gt (by simpa only [Finset.mem_range] using hn))
    have hplus := weilTest_eq_zero_of_common_window hs_f hs_g (hlog.trans_le (le_abs_self _))
    have hminus := weilTest_eq_zero_of_common_window hs_f hs_g
      (show 2 * R < |-Real.log n| by rw [abs_neg]; exact hlog.trans_le (le_abs_self _))
    rw [hplus, hminus, add_zero, mul_zero]
  have hterm (n : ℕ) :
      ‖(sourcePrimeCoefficient n : ℂ) *
        (EF.weilTest (cx f) (cx g) (Real.log n) +
          EF.weilTest (cx f) (cx g) (-Real.log n))‖ ≤
      sourcePrimeCoefficient n * (sectionMass f + sectionMass g) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sourcePrimeCoefficient_nonneg n)]
    apply mul_le_mul_of_nonneg_left _ (sourcePrimeCoefficient_nonneg n)
    have h1 := norm_weilTest_le_sectionMass hf hfc hg hgc (Real.log n)
    have h2 := norm_weilTest_le_sectionMass hf hfc hg hgc (-Real.log n)
    have ht := norm_add_le (EF.weilTest (cx f) (cx g) (Real.log n))
      (EF.weilTest (cx f) (cx g) (-Real.log n))
    linarith only [h1, h2, ht]
  rw [hfinite]
  calc
    _ ≤ ‖∑ n ∈ Finset.range N, (sourcePrimeCoefficient n : ℂ) *
        (EF.weilTest (cx f) (cx g) (Real.log n) +
          EF.weilTest (cx f) (cx g) (-Real.log n))‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ n ∈ Finset.range N, ‖(sourcePrimeCoefficient n : ℂ) *
        (EF.weilTest (cx f) (cx g) (Real.log n) +
          EF.weilTest (cx f) (cx g) (-Real.log n))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, sourcePrimeCoefficient n * (sectionMass f + sectionMass g) :=
      Finset.sum_le_sum fun n _ => hterm n
    _ = C * (sectionMass f + sectionMass g) := (Finset.sum_mul _ _ _).symm

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_primePart_window_mass_bound
