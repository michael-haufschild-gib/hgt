import GaloisForLFunctions.RHTower.CCMActualHeadMatchedSymmetricFirstMomentControl
import GaloisForLFunctions.RHTower.CCMActualHeadGammaWallOutgoingProducer

/-!
# Finite support of matched prime--polar cells on every aperture head

Mass matching and finite physical aperture interact more rigidly than an ambient Fourier-moment
estimate suggests.  Beyond twice the aperture, the actual-head translation defect is exactly the
constant `2 * ‖f‖²`.  The matched cell radius is at most one, while its center `log n` escapes to
infinity.  Hence every sufficiently remote cell lies wholly in this constant-defect region.

On such a cell, its prime anchor and symmetric outgoing polar mass cancel exactly.  More strongly,
both internal signed streams vanish separately: the asymmetric Suzuki sine current is zero and the
even symmetric rebate residual is zero.  Thus, for every literal aperture head, all three matched
families are eventually zero and therefore summable without any Fourier first-moment hypothesis.

This converts the all-prime matched producer on a fixed CCM aperture into an exact finite problem.
No smoothness, spectral approximation, prime-gap estimate, computation, or RH premise enters.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

private lemma log_le_two_mul_sqrt_local {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hlog : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hhalf : Real.log (Real.sqrt t) = Real.log t / 2 :=
    Real.log_sqrt ht.le
  rw [hhalf] at hlog
  linarith

/-- The exact matched prime--polar radius is uniformly at most one away from `n = 0`. -/
theorem ccmActualHeadMatchedPrimePolarRadius_le_one_of_one_le
    {n : ℕ} (hn : 1 ≤ n) :
    ccmActualHeadMatchedPrimePolarRadius n ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hweight : criticalMellinAtomWeight n ≤ 2 := by
    rw [criticalMellinAtomWeight_eq_div_sqrt]
    have hvm := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have hlog := log_le_two_mul_sqrt_local hnpos
    calc
      ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
          Real.log n / Real.sqrt n :=
        div_le_div_of_nonneg_right hvm hsqrtpos.le
      _ ≤ (2 * Real.sqrt n) / Real.sqrt n :=
        div_le_div_of_nonneg_right hlog hsqrtpos.le
      _ = 2 := by field_simp
  have hA : 1 ≤ Real.exp (Real.log n / 2) := by
    exact Real.one_le_exp
      (div_nonneg (Real.log_natCast_nonneg n) (by norm_num))
  calc
    ccmActualHeadMatchedPrimePolarRadius n ≤
        criticalMellinAtomWeight n /
          (2 * Real.exp (Real.log n / 2)) :=
      ccmActualHeadMatchedPrimePolarRadius_le_weight_div n
    _ ≤ 2 / (2 * 1) := by gcongr
    _ = 1 := by norm_num

/-- **Exact remote-cell cancellation.**  If a matched cell lies beyond physical aperture diameter,
its prime anchor equals its entire outgoing polar cell. -/
theorem ccmActualHeadMatchedPrimePolarCellDifference_eq_zero_of_apertureSeparation
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hsep : 2 * a.1 <
      Real.log n - ccmActualHeadMatchedPrimePolarRadius n) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f.1 -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1 = 0 := by
  let s := Real.log n
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  have hρ : 0 ≤ ρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hs : 2 * a.1 < s := lt_of_lt_of_le hsep (sub_le_self s hρ)
  have hanchor := integral_ccmActualHeadMatchedPrimePolar_anchor n f.1
  rw [← hanchor, ccmActualHeadOutgoingPolarSymmetricCell_eq_pairIntegral]
  have hE : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f.1 := by
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f.1).sub continuous_const).norm).pow 2
  have hleft : IntervalIntegrable (fun r : ℝ =>
      2 * Real.exp (s / 2) * Real.cosh (r / 2) *
        ccmActualHeadTranslationDefect s f.1) volume 0 ρ :=
    (by fun_prop : Continuous fun r : ℝ =>
      2 * Real.exp (s / 2) * Real.cosh (r / 2) *
        ccmActualHeadTranslationDefect s f.1).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun r : ℝ =>
      Real.exp ((s + r) / 2) * ccmActualHeadTranslationDefect (s + r) f.1 +
        Real.exp ((s - r) / 2) * ccmActualHeadTranslationDefect (s - r) f.1)
      volume 0 ρ :=
    (by fun_prop : Continuous fun r : ℝ =>
      Real.exp ((s + r) / 2) * ccmActualHeadTranslationDefect (s + r) f.1 +
        Real.exp ((s - r) / 2) * ccmActualHeadTranslationDefect (s - r) f.1).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hleft hright]
  calc
    (∫ r in (0 : ℝ)..ρ,
        2 * Real.exp (s / 2) * Real.cosh (r / 2) *
            ccmActualHeadTranslationDefect s f.1 -
          (Real.exp ((s + r) / 2) * ccmActualHeadTranslationDefect (s + r) f.1 +
            Real.exp ((s - r) / 2) * ccmActualHeadTranslationDefect (s - r) f.1)) =
        ∫ _r in (0 : ℝ)..ρ, 0 := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) ρ := by
        simpa [uIcc_of_le hρ] using hr
      have hr0 : 0 ≤ r := hr'.1
      have hrρ : r ≤ ρ := hr'.2
      have hminus : 2 * a.1 < s - r :=
        lt_of_lt_of_le hsep (sub_le_sub_left hrρ s)
      have hplus : 2 * a.1 < s + r :=
        lt_of_lt_of_le hs (le_add_of_nonneg_right hr0)
      have hexpPlus : Real.exp ((s + r) / 2) =
          Real.exp (s / 2) * Real.exp (r / 2) := by
        rw [show (s + r) / 2 = s / 2 + r / 2 by ring, Real.exp_add]
      have hexpMinus : Real.exp ((s - r) / 2) =
          Real.exp (s / 2) * Real.exp (-(r / 2)) := by
        rw [show (s - r) / 2 = s / 2 + -(r / 2) by ring, Real.exp_add]
      change
        2 * Real.exp (s / 2) * Real.cosh (r / 2) *
              ccmActualHeadTranslationDefect s f.1 -
            (Real.exp ((s + r) / 2) * ccmActualHeadTranslationDefect (s + r) f.1 +
              Real.exp ((s - r) / 2) * ccmActualHeadTranslationDefect (s - r) f.1) = 0
      rw [ccmActualHeadTranslationDefect_eq_two_norm_sq_of_two_aperture_lt a f hs,
        ccmActualHeadTranslationDefect_eq_two_norm_sq_of_two_aperture_lt a f hplus,
        ccmActualHeadTranslationDefect_eq_two_norm_sq_of_two_aperture_lt a f hminus,
        hexpPlus, hexpMinus, Real.cosh_eq]
      ring
    _ = 0 := by simp

/-- Past aperture separation, the asymmetric Suzuki current vanishes before assembly. -/
theorem ccmActualHeadMatchedSuzukiCurrent_eq_zero_of_apertureSeparation
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hsep : 2 * a.1 <
      Real.log n - ccmActualHeadMatchedPrimePolarRadius n) :
    ccmActualHeadMatchedSuzukiCurrent n f.1 = 0 := by
  let s := Real.log n
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  have hρ : 0 ≤ ρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hs : 2 * a.1 < s := lt_of_lt_of_le hsep (sub_le_self s hρ)
  unfold ccmActualHeadMatchedSuzukiCurrent
  change (∫ r in (0 : ℝ)..ρ,
      Real.exp (s / 2) * Real.sinh (r / 2) *
        ccmActualHeadTranslationSineCurrent s r f.1) = 0
  calc
    (∫ r in (0 : ℝ)..ρ,
        Real.exp (s / 2) * Real.sinh (r / 2) *
          ccmActualHeadTranslationSineCurrent s r f.1) =
        ∫ _r in (0 : ℝ)..ρ, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) ρ := by
        simpa [uIcc_of_le hρ] using hr
      have hr0 : 0 ≤ r := hr'.1
      have hrρ : r ≤ ρ := hr'.2
      have hminus : 2 * a.1 < s - r :=
        lt_of_lt_of_le hsep (sub_le_sub_left hrρ s)
      have hplus : 2 * a.1 < s + r :=
        lt_of_lt_of_le hs (le_add_of_nonneg_right hr0)
      unfold ccmActualHeadTranslationSineCurrent
      change Real.exp (s / 2) * Real.sinh (r / 2) *
        (ccmActualHeadTranslationDefect (s + r) f.1 -
          ccmActualHeadTranslationDefect (s - r) f.1) = 0
      rw [ccmActualHeadTranslationDefect_eq_two_norm_sq_of_two_aperture_lt a f hplus,
        ccmActualHeadTranslationDefect_eq_two_norm_sq_of_two_aperture_lt a f hminus]
      ring
    _ = 0 := by simp

/-- Past aperture separation, the even matched residual also vanishes separately. -/
theorem ccmActualHeadMatchedSymmetricCellResidual_eq_zero_of_apertureSeparation
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hsep : 2 * a.1 <
      Real.log n - ccmActualHeadMatchedPrimePolarRadius n) :
    ccmActualHeadMatchedSymmetricCellResidual n f.1 = 0 := by
  have hcell :=
    ccmActualHeadMatchedPrimePolarCellDifference_eq_zero_of_apertureSeparation
      a f n hsep
  have hsuzuki :=
    ccmActualHeadMatchedSuzukiCurrent_eq_zero_of_apertureSeparation a f n hsep
  have hsplit :=
    ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_symmetric_sub_suzuki n f.1
  linarith

/-- Explicit coarse support boundary for an intact matched cell. -/
theorem ccmActualHeadMatchedPrimePolarCellDifference_eq_zero_of_log_gt
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) {n : ℕ}
    (hn : 1 ≤ n) (hlog : 2 * a.1 + 1 < Real.log n) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f.1 -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1 = 0 := by
  apply ccmActualHeadMatchedPrimePolarCellDifference_eq_zero_of_apertureSeparation a f n
  have hρ := ccmActualHeadMatchedPrimePolarRadius_le_one_of_one_le hn
  linarith

theorem ccmActualHeadMatchedSuzukiCurrent_eq_zero_of_log_gt
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) {n : ℕ}
    (hn : 1 ≤ n) (hlog : 2 * a.1 + 1 < Real.log n) :
    ccmActualHeadMatchedSuzukiCurrent n f.1 = 0 := by
  apply ccmActualHeadMatchedSuzukiCurrent_eq_zero_of_apertureSeparation a f n
  have hρ := ccmActualHeadMatchedPrimePolarRadius_le_one_of_one_le hn
  linarith

theorem ccmActualHeadMatchedSymmetricCellResidual_eq_zero_of_log_gt
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) {n : ℕ}
    (hn : 1 ≤ n) (hlog : 2 * a.1 + 1 < Real.log n) :
    ccmActualHeadMatchedSymmetricCellResidual n f.1 = 0 := by
  apply ccmActualHeadMatchedSymmetricCellResidual_eq_zero_of_apertureSeparation a f n
  have hρ := ccmActualHeadMatchedPrimePolarRadius_le_one_of_one_le hn
  linarith

/-- The intact prime-minus-matched-polar family is eventually exactly zero on every aperture. -/
theorem eventually_ccmActualHeadMatchedPrimePolarCellDifference_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᶠ n : ℕ in atTop,
      criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f.1 -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1 = 0 := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (2 * a.1 + 1),
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hlogn hn
  exact ccmActualHeadMatchedPrimePolarCellDifference_eq_zero_of_log_gt a f hn hlogn

/-- The asymmetric current has finite support on every aperture head. -/
theorem eventually_ccmActualHeadMatchedSuzukiCurrent_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᶠ n : ℕ in atTop, ccmActualHeadMatchedSuzukiCurrent n f.1 = 0 := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (2 * a.1 + 1),
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hlogn hn
  exact ccmActualHeadMatchedSuzukiCurrent_eq_zero_of_log_gt a f hn hlogn

/-- The even matched residual has finite support on every aperture head. -/
theorem eventually_ccmActualHeadMatchedSymmetricCellResidual_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᶠ n : ℕ in atTop,
      ccmActualHeadMatchedSymmetricCellResidual n f.1 = 0 := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (2 * a.1 + 1),
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hlogn hn
  exact ccmActualHeadMatchedSymmetricCellResidual_eq_zero_of_log_gt a f hn hlogn

/-- Unconditional all-prime matched-cell convergence on every literal aperture head. -/
theorem summable_ccmActualHeadMatchedPrimePolarCellDifference_of_aperture
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    Summable (fun n : ℕ =>
      criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f.1 -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1) := by
  exact summable_zero.congr_atTop
    ((eventually_ccmActualHeadMatchedPrimePolarCellDifference_eq_zero a f).mono
      fun _ hn => hn.symm)

theorem summable_ccmActualHeadMatchedSuzukiCurrent_of_aperture
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    Summable (fun n : ℕ => ccmActualHeadMatchedSuzukiCurrent n f.1) := by
  exact summable_zero.congr_atTop
    ((eventually_ccmActualHeadMatchedSuzukiCurrent_eq_zero a f).mono
      fun _ hn => hn.symm)

theorem summable_ccmActualHeadMatchedSymmetricCellResidual_of_aperture
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    Summable (fun n : ℕ => ccmActualHeadMatchedSymmetricCellResidual n f.1) := by
  exact summable_zero.congr_atTop
    ((eventually_ccmActualHeadMatchedSymmetricCellResidual_eq_zero a f).mono
      fun _ hn => hn.symm)

/-- The infinite matched prime--polar producer is literally one finite block on every aperture. -/
theorem exists_tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_finiteBlock
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∃ N : ℕ,
      (∑' n : ℕ,
        (criticalMellinAtomWeight n *
              ccmActualHeadTranslationDefect (Real.log n) f.1 -
            ccmActualHeadOutgoingPolarSymmetricCell
              (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1)) =
        ccmActualHeadMatchedPrimePolarFiniteBlock (Finset.range N) f.1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_ccmActualHeadMatchedPrimePolarCellDifference_eq_zero a f)
  refine ⟨N, ?_⟩
  rw [tsum_eq_sum (s := Finset.range N)]
  · rfl
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact hN n hn

theorem exists_tsum_ccmActualHeadMatchedSymmetricCellResidual_eq_finiteBlock
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∃ N : ℕ,
      (∑' n : ℕ, ccmActualHeadMatchedSymmetricCellResidual n f.1) =
        ccmActualHeadMatchedSymmetricFiniteBlock (Finset.range N) f.1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_ccmActualHeadMatchedSymmetricCellResidual_eq_zero a f)
  refine ⟨N, ?_⟩
  rw [tsum_eq_sum (s := Finset.range N)]
  · rfl
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact hN n hn

theorem exists_tsum_ccmActualHeadMatchedSuzukiCurrent_eq_finiteBlock
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∃ N : ℕ,
      (∑' n : ℕ, ccmActualHeadMatchedSuzukiCurrent n f.1) =
        ccmActualHeadMatchedSuzukiFiniteBlock (Finset.range N) f.1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_ccmActualHeadMatchedSuzukiCurrent_eq_zero a f)
  refine ⟨N, ?_⟩
  rw [tsum_eq_sum (s := Finset.range N)]
  · rfl
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact hN n hn

/-- The exact signed split survives infinite assembly because all three families have finite
support on an aperture head. -/
theorem tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_symmetric_sub_suzuki
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∑' n : ℕ,
      (criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f.1 -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1)) =
      (∑' n : ℕ, ccmActualHeadMatchedSymmetricCellResidual n f.1) -
        ∑' n : ℕ, ccmActualHeadMatchedSuzukiCurrent n f.1 := by
  rw [← (summable_ccmActualHeadMatchedSymmetricCellResidual_of_aperture a f).tsum_sub
    (summable_ccmActualHeadMatchedSuzukiCurrent_of_aperture a f)]
  apply tsum_congr
  intro n
  exact ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_symmetric_sub_suzuki n f.1

end RHTower
