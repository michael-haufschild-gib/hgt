import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundFrequencyLocalization
import GaloisForLFunctions.RHTower.CCMRestrictedWeilFormTranslation
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConstrainedSmoothCore

/-!
# Exact outer-shell prime transport

For `a < h`, squaring the actual symmetric translation compressed to `[-a,a]` gives
cutoff to its two endpoint overlap intervals. Its norm is at most one, and it vanishes
when `2a ≤ h`. For `a < h < 2a`, nonzero form-domain vectors with both pole moments zero
attain eigenvalues `+1` and `-1`; hence the contraction constant one remains sharp on
that constrained sector.

The literal finite-prime operator therefore satisfies the improved two-scale bound
`21 * (exp a + exp (a/2))`. No all-aperture Weil positivity follows from this bound.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower

/-- The actual aperture compression is literal pointwise cutoff after the source operator. -/
theorem ccmApertureCompression_val (a : SuzukiPositiveAperture)
    (A : SoninL2 →L[ℂ] SoninL2) (f : suzukiApertureHilbert a) :
    (ccmApertureCompression a A f : SoninL2) =
      indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) (A f.1) := by
  change ((suzukiApertureHilbert a).subtypeL.adjoint (A f.1) : SoninL2) = _
  rw [(suzukiApertureHilbert a).adjoint_subtypeL,
    Submodule.coe_orthogonalProjectionOnto_apply,
    indicatorCutoff_eq_physicalForbidden_starProjection]

private theorem translation_coeFn (h : ℝ) (f : SoninL2) :
    (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + h) := by
  exact (Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)).trans
      (Eventually.of_forall fun _ => rfl)

/-- Pointwise formula for the compressed two-direction prime shift. -/
theorem ccmApertureSymmetricTranslation_coeFn (a : SuzukiPositiveAperture)
    (h : ℝ) (f : suzukiApertureHilbert a) :
    ((ccmApertureCompression a (ccmSymmetricLogTranslation h) f : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] (centralInterval a.1).indicator
        (fun x => f.1 (x + h) + f.1 (x - h)) := by
  rw [ccmApertureCompression_val]
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) (ccmSymmetricLogTranslation h f.1),
    Lp.coeFn_add (logTranslationCLM h f.1) (logTranslationCLM (-h) f.1),
    translation_coeFn h f.1, translation_coeFn (-h) f.1] with x hc hs hp hm
  rw [hc]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx]
    change (logTranslationCLM h f.1 + logTranslationCLM (-h) f.1) x = _
    rw [hs]
    change logTranslationCLM h f.1 x + logTranslationCLM (-h) f.1 x = _
    rw [hp, hm, sub_eq_add_neg]
  · simp only [indicator_of_notMem hx]

private theorem aperture_zero_outside (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    ∀ᵐ x, x ∉ centralInterval a.1 → f.1 x = 0 := by
  have hc := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hc
  filter_upwards [hc] with x hx hn
  rw [hx, indicator_of_notMem hn]

/-- The two endpoint pieces paired by an outer-shell shift. -/
def ccmOuterShiftSupport (a : SuzukiPositiveAperture) (h : ℝ) : Set ℝ :=
  Icc (-a.1) (a.1 - h) ∪ Icc (-a.1 + h) a.1

theorem measurableSet_ccmOuterShiftSupport (a : SuzukiPositiveAperture) (h : ℝ) :
    MeasurableSet (ccmOuterShiftSupport a h) := measurableSet_Icc.union measurableSet_Icc

/-- Above the half-diameter, squaring the symmetric shift gives an exact endpoint projection. -/
theorem ccmApertureSymmetricTranslation_sq_val (a : SuzukiPositiveAperture)
    {h : ℝ} (hh : a.1 < h) (f : suzukiApertureHilbert a) :
    (ccmApertureCompression a (ccmSymmetricLogTranslation h)
      (ccmApertureCompression a (ccmSymmetricLogTranslation h) f) : SoninL2) =
      indicatorCutoff (ccmOuterShiftSupport a h) (measurableSet_ccmOuterShiftSupport a h) f.1 := by
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation h)
  have hs := ccmApertureSymmetricTranslation_coeFn a h f
  have hsp := hs.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have hsm := hs.comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.tendsto_ae
  have hz := aperture_zero_outside a f
  have hzp := (MellinL2.realTranslation_measurePreserving (2*h)).quasiMeasurePreserving.tendsto_ae.eventually hz
  have hzm := (MellinL2.realTranslation_measurePreserving (-2*h)).quasiMeasurePreserving.tendsto_ae.eventually hz
  apply Lp.ext
  filter_upwards [ccmApertureSymmetricTranslation_coeFn a h (S f),
    hsp, hsm, hzp, hzm,
    indicatorCutoff_ae (ccmOuterShiftSupport a h)
      (measurableSet_ccmOuterShiftSupport a h) f.1] with x hss hp hm hzp hzm hc
  change (S f : SoninL2) (x+h) = (centralInterval a.1).indicator
    (fun y => f.1 (y+h) + f.1 (y-h)) (x+h) at hp
  change (S f : SoninL2) (x+ -h) = (centralInterval a.1).indicator
    (fun y => f.1 (y+h) + f.1 (y-h)) (x+ -h) at hm
  change (S (S f) : SoninL2) x = _
  rw [hss, hc]
  have hpos : 0 < h := lt_trans a.property hh
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    change -a.1 ≤ x ∧ x ≤ a.1 at hx
    have hzp' : f.1 (x + 2*h) = 0 := hzp (by
      change ¬ (-a.1 ≤ x+2*h ∧ x+2*h ≤ a.1)
      intro hn; linarith [hn.2])
    have hzm' : f.1 (x + -2*h) = 0 := hzm (by
      change ¬ (-a.1 ≤ x+ -2*h ∧ x+ -2*h ≤ a.1)
      intro hn; linarith [hn.1])
    have hmp : x - h = x + -h := by ring
    rw [hp, hmp, hm]
    by_cases hxp : x + h ∈ centralInterval a.1 <;>
      by_cases hxm : x + -h ∈ centralInterval a.1
    · change -a.1 ≤ x+h ∧ x+h ≤ a.1 at hxp
      change -a.1 ≤ x+ -h ∧ x+ -h ≤ a.1 at hxm
      exfalso; linarith [hxp.2, hxm.1]
    · rw [indicator_of_mem hxp, indicator_of_notMem hxm]
      have hout : x ∈ ccmOuterShiftSupport a h := Or.inl ⟨hx.1, by
        change -a.1 ≤ x+h ∧ x+h ≤ a.1 at hxp
        linarith [hxp.2]⟩
      rw [indicator_of_mem hout]
      convert add_zero (f.1 x) using 1; simp only [show x+h+h=x+2*h by ring,
        show x+h-h=x by ring, hzp', zero_add, add_zero]
    · rw [indicator_of_notMem hxp, indicator_of_mem hxm]
      have hout : x ∈ ccmOuterShiftSupport a h := Or.inr ⟨by
        change -a.1 ≤ x+ -h ∧ x+ -h ≤ a.1 at hxm
        linarith [hxm.1], hx.2⟩
      rw [indicator_of_mem hout]
      simp only [show x + -h + h = x by ring,
        show x + -h - h = x + -2*h by ring, hzm', add_zero, zero_add]
    · rw [indicator_of_notMem hxp, indicator_of_notMem hxm, zero_add]
      have hout : x ∉ ccmOuterShiftSupport a h := by
        rintro (hl | hr)
        · apply hxp
          change -a.1 ≤ x+h ∧ x+h ≤ a.1
          constructor <;> linarith [hl.1, hl.2]
        · apply hxm
          change -a.1 ≤ x+ -h ∧ x+ -h ≤ a.1
          constructor <;> linarith [hr.1, hr.2]
      rw [indicator_of_notMem hout]
  · rw [indicator_of_notMem hx]
    have hout : x ∉ ccmOuterShiftSupport a h := by
      rintro (hl | hr) <;> apply hx <;>
        change -a.1 ≤ x ∧ x ≤ a.1
      · constructor <;> linarith [hl.1, hl.2]
      · constructor <;> linarith [hr.1, hr.2]
    rw [indicator_of_notMem hout]

/-- Outer-shell symmetric prime transport has norm at most one, not two. -/
theorem norm_ccmApertureSymmetricTranslation_le_one (a : SuzukiPositiveAperture)
    {h : ℝ} (hh : a.1 < h) :
    ‖ccmApertureCompression a (ccmSymmetricLogTranslation h)‖ ≤ 1 := by
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation h)
  have hsa : S.adjoint = S := ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (ccmApertureCompression_isSelfAdjoint a (ccmSymmetricLogTranslation_isSelfAdjoint h))
  have hb : ‖S.comp S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖(S (S f) : SoninL2)‖ ≤ 1 * ‖f‖
    rw [ccmApertureSymmetricTranslation_sq_val a hh,
      indicatorCutoff_eq_physicalForbidden_starProjection, one_mul]
    exact Submodule.norm_starProjection_apply_le _ f.1
  have heq := ContinuousLinearMap.norm_adjoint_comp_self S
  rw [hsa] at heq
  change ‖S‖ ≤ 1
  nlinarith [norm_nonneg S]

/-- Literal prime transport gains the factor two whenever its logarithmic lag exceeds `a`. -/
theorem norm_ccmPrimeTransportOperator_le_outerShell (a : SuzukiPositiveAperture)
    (n : ℕ) (hn : a.1 < Real.log n) :
    ‖ccmPrimeTransportOperator a n‖ ≤ 1 / Real.sqrt n := by
  have hc : 0 ≤ 1 / Real.sqrt (n : ℝ) := one_div_nonneg.mpr (Real.sqrt_nonneg _)
  unfold ccmPrimeTransportOperator
  calc
    _ ≤ ‖((1 / Real.sqrt n : ℝ) : ℂ)‖ *
        ‖ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))‖ :=
      norm_smul_continuousLinearMap_le _ _
    _ = (1 / Real.sqrt n) *
        ‖ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ (1 / Real.sqrt n) * 1 := mul_le_mul_of_nonneg_left
      (norm_ccmApertureSymmetricTranslation_le_one a hn) hc
    _ = _ := mul_one _

/-- Actual source budget retaining the exact outer-shell factor. -/
def ccmPrimeOuterShellBudget (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))),
    (if a.1 < Real.log n then 1 else 2) *
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n)

/-- The literal finite-prime operator satisfies the improved shell-weighted budget. -/
theorem norm_ccmFinitePrimeOperator_le_outerShellBudget (a : SuzukiPositiveAperture) :
    ‖ccmFinitePrimeOperator a‖ ≤ ccmPrimeOuterShellBudget a := by
  classical
  unfold ccmFinitePrimeOperator ccmPrimeOuterShellBudget
  refine (norm_sum_le (Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))))
    (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) • ccmPrimeTransportOperator a n :
      suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a))).trans
        (Finset.sum_le_sum ?_)
  intro n hn
  have hvm := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hnorm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
      ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hvm]
  calc
    _ ≤ ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * ‖ccmPrimeTransportOperator a n‖ :=
      norm_smul_continuousLinearMap_le _ _
    _ = ArithmeticFunction.vonMangoldt n * ‖ccmPrimeTransportOperator a n‖ := by rw [hnorm]
    _ ≤ _ := by
      by_cases hlag : a.1 < Real.log n
      · rw [if_pos hlag, one_mul]
        have hb := mul_le_mul_of_nonneg_left
          (norm_ccmPrimeTransportOperator_le_outerShell a n hlag) hvm
        have heq : ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt n) =
            ArithmeticFunction.vonMangoldt n / Real.sqrt n := by ring
        rw [heq] at hb
        exact hb
      · rw [if_neg hlag]
        have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
        have hb := mul_le_mul_of_nonneg_left (norm_ccmPrimeTransportOperator_le a hn1) hvm
        have heq : ArithmeticFunction.vonMangoldt n * (2 / Real.sqrt n) =
            2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by ring
        rw [heq] at hb
        exact hb

/-- The new budget never exceeds the previous atomwise budget. -/
theorem ccmPrimeOuterShellBudget_le_naive (a : SuzukiPositiveAperture) :
    ccmPrimeOuterShellBudget a ≤
      2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2*a.1))),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  classical
  rw [ccmPrimeOuterShellBudget, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hv : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  split_ifs <;> nlinarith

/-- Closed two-scale prime-mass envelope: the outer shell is counted once. -/
theorem ccmPrimeOuterShellBudget_le_twoScaleMass (a : SuzukiPositiveAperture) :
    ccmPrimeOuterShellBudget a ≤
      primeMassHalf (Real.exp (2*a.1)) + primeMassHalf (Real.exp a.1) := by
  classical
  let N := Nat.floor (Real.exp (2*a.1))
  let w : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / Real.sqrt n
  have hw : ∀ n, 0 ≤ w n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hsplit : ccmPrimeOuterShellBudget a =
      (∑ n ∈ Finset.Icc 2 N, w n) +
        ∑ n ∈ (Finset.Icc 2 N).filter (fun (n : ℕ) => Real.log (n : ℝ) ≤ a.1), w n := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    unfold ccmPrimeOuterShellBudget
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [w]
    by_cases h : a.1 < Real.log n
    · rw [if_pos h, if_neg (not_le.mpr h)]; ring
    · rw [if_neg h, if_pos (le_of_not_gt h)]; ring
  have hl : (∑ n ∈ Finset.Icc 2 N, w n) ≤ primeMassHalf (Real.exp (2*a.1)) := by
    unfold primeMassHalf
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_Icc.mp hn).2⟩
    · intro n _ _; exact hw n
  have hs : (∑ n ∈ (Finset.Icc 2 N).filter (fun (n : ℕ) => Real.log (n : ℝ) ≤ a.1), w n) ≤
      primeMassHalf (Real.exp a.1) := by
    unfold primeMassHalf
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn, hlog⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast
        (show 0 < n from lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hn).1)
      apply Finset.mem_Icc.mpr
      refine ⟨Nat.zero_le n, Nat.le_floor ?_⟩
      calc
        (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp a.1 := Real.exp_le_exp.mpr hlog
    · intro n _ _; exact hw n
  rw [hsplit]
  exact add_le_add hl hs

/-- Explicit improved source norm: `21(exp(a)+exp(a/2))`, replacing `42 exp(a)`. -/
theorem norm_ccmFinitePrimeOperator_le_twoScaleExp (a : SuzukiPositiveAperture) :
    ‖ccmFinitePrimeOperator a‖ ≤ 21 * (Real.exp a.1 + Real.exp (a.1/2)) := by
  have hlarge := primeMassHalf_le_sqrt (X := Real.exp (2*a.1))
    (Real.one_le_exp (by linarith [a.property]))
  have hsmall := primeMassHalf_le_sqrt (X := Real.exp a.1)
    (Real.one_le_exp a.property.le)
  have hexp : ∀ x : ℝ, Real.sqrt (Real.exp (2*x)) = Real.exp x := by
    intro x
    rw [show Real.exp (2*x) = Real.exp x ^ 2 by
      rw [← Real.exp_nat_mul]; norm_num]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hexp] at hlarge
  have hsq : Real.sqrt (Real.exp a.1) = Real.exp (a.1/2) := by
    convert hexp (a.1/2) using 1; congr 2; ring
  rw [hsq] at hsmall
  have hb := (norm_ccmFinitePrimeOperator_le_outerShellBudget a).trans
    (ccmPrimeOuterShellBudget_le_twoScaleMass a)
  nlinarith

/-- At and beyond the aperture diameter the actual symmetric transport vanishes. -/
theorem ccmApertureSymmetricTranslation_eq_zero_of_diameter (a : SuzukiPositiveAperture)
    {h : ℝ} (hh : 2*a.1 ≤ h) :
    ccmApertureCompression a (ccmSymmetricLogTranslation h) = 0 := by
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation h)
  have hsa := (ccmApertureCompression_isSelfAdjoint a
    (ccmSymmetricLogTranslation_isSelfAdjoint h)).isSymmetric
  have hcut : ∀ f : SoninL2, indicatorCutoff (ccmOuterShiftSupport a h)
      (measurableSet_ccmOuterShiftSupport a h) f = 0 := by
    intro f
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (ccmOuterShiftSupport a h)
        (measurableSet_ccmOuterShiftSupport a h) f,
      volume.ae_ne (-a.1), volume.ae_ne a.1,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x hc hl hr hz
    rw [hc, hz]
    have hn : x ∉ ccmOuterShiftSupport a h := by
      rintro (hx | hx)
      · apply hl; apply le_antisymm <;> linarith [hx.1, hx.2]
      · apply hr; apply le_antisymm <;> linarith [hx.1, hx.2]
    rw [indicator_of_notMem hn]
    rfl
  have hsq : ∀ f, S (S f) = 0 := by
    intro f
    apply Subtype.ext
    rw [ccmApertureSymmetricTranslation_sq_val a (by linarith [a.property]), hcut]
    rfl
  apply ContinuousLinearMap.ext
  intro f
  change S f = 0
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have heq : inner ℂ (S (S f)) f = inner ℂ (S f) (S f) := hsa (S f) f
  rw [hsq, inner_zero_left] at heq
  exact heq.symm

/-- A prime at the diameter has zero transport, including the endpoint itself. -/
theorem ccmPrimeTransportOperator_eq_zero_of_diameter (a : SuzukiPositiveAperture)
    (n : ℕ) (hn : 2*a.1 ≤ Real.log n) : ccmPrimeTransportOperator a n = 0 := by
  rw [ccmPrimeTransportOperator, ccmApertureSymmetricTranslation_eq_zero_of_diameter a hn]
  apply ContinuousLinearMap.ext
  intro f
  exact smul_zero ((1 / Real.sqrt n : ℝ) : ℂ)


private theorem cutoff_translation_off_aperture (a b : SuzukiPositiveAperture)
    {h : ℝ} (hh : a.1 + b.1 < |h|) (f : suzukiApertureHilbert b) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (logTranslationCLM h f.1) = 0 := by
  have hz := aperture_zero_outside b f
  have hzs := (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae.eventually hz
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) (logTranslationCLM h f.1),
    translation_coeFn h f.1, hzs, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)]
    with x hc ht hz h0
  rw [hc, h0]
  change (centralInterval a.1).indicator (fun x => logTranslationCLM h f.1 x) x = 0
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, ht]
    apply hz
    intro hb
    have hxa : |x| ≤ a.1 := abs_le.mpr hx
    have hxb : |x+h| ≤ b.1 := abs_le.mpr hb
    have habs := abs_add_le (x+h) (-x)
    rw [show x+h+ -x=h by ring, abs_neg] at habs
    linarith
  · rw [indicator_of_notMem hx]

/-- The two pole constraints do not improve the sharp outer-shell bound: both signs have
nonzero representatives in the actual form domain. -/
theorem exists_polarConstrained_outerShell_eigenvectors (a : SuzukiPositiveAperture)
    {h : ℝ} (hlo : a.1 < h) (hhi : h < 2*a.1) :
    ∃ u v : CCMArchimedeanFormDomain a,
      IsPolarConstrained a u ∧ IsPolarConstrained a v ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ccmArchimedeanFormToAperture a v ≠ 0 ∧
      ccmApertureCompression a (ccmSymmetricLogTranslation h)
        (ccmArchimedeanFormToAperture a u) = ccmArchimedeanFormToAperture a u ∧
      ccmApertureCompression a (ccmSymmetricLogTranslation h)
        (ccmArchimedeanFormToAperture a v) = -ccmArchimedeanFormToAperture a v := by
  let b : SuzukiPositiveAperture := ⟨(2*a.1-h)/4, by linarith⟩
  have hp : 0 < h := lt_trans a.property hlo
  have hfitp : b.1 + |h/2| ≤ a.1 := by
    dsimp [b]; rw [abs_of_pos (by linarith : 0 < h/2)]; linarith
  have hfitm : b.1 + |-(h/2)| ≤ a.1 := by rwa [abs_neg]
  obtain ⟨g, hg, hgn⟩ := exists_polarConstrained_smooth_ne_zero b
  let up := ccmArchimedeanFormTranslate (h/2) hfitp g.toCCMFormVector
  let um := ccmArchimedeanFormTranslate (-(h/2)) hfitm g.toCCMFormVector
  let J := ccmArchimedeanFormToAperture a
  let f : suzukiApertureHilbert b := ccmArchimedeanFormToAperture b g.toCCMFormVector
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation h)
  have hup : IsPolarConstrained a up := hg.translate _ hfitp
  have hum : IsPolarConstrained a um := hg.translate _ hfitm
  have heqp : (J up : SoninL2) = logTranslationCLM (h/2) f.1 :=
    ccmArchimedeanFormTranslate_physical _ _ _
  have heqm : (J um : SoninL2) = logTranslationCLM (-(h/2)) f.1 :=
    ccmArchimedeanFormTranslate_physical _ _ _
  have hoffp : indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (logTranslationCLM (3*h/2) f.1) = 0 :=
    cutoff_translation_off_aperture a b (by
      dsimp [b]; rw [abs_of_pos (by linarith : 0 < 3*h/2)]; linarith) f
  have hoffm : indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (logTranslationCLM (-(3*h/2)) f.1) = 0 :=
    cutoff_translation_off_aperture a b (by
      rw [abs_neg]; dsimp [b]; rw [abs_of_pos (by linarith : 0 < 3*h/2)]; linarith) f
  have hSp : S (J up) = J um := by
    apply Subtype.ext
    rw [ccmApertureCompression_val]
    change indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (logTranslationCLM h (J up : SoninL2) + logTranslationCLM (-h) (J up : SoninL2)) = _
    rw [heqp, map_add, logTranslationCLM_add_apply, logTranslationCLM_add_apply,
      show h+h/2=3*h/2 by ring, show -h+h/2= -(h/2) by ring, hoffp, zero_add,
      ← heqm, indicatorCutoff_suzukiApertureHilbert]
  have hSm : S (J um) = J up := by
    apply Subtype.ext
    rw [ccmApertureCompression_val]
    change indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (logTranslationCLM h (J um : SoninL2) + logTranslationCLM (-h) (J um : SoninL2)) = _
    rw [heqm, map_add, logTranslationCLM_add_apply, logTranslationCLM_add_apply,
      show h+ -(h/2)=h/2 by ring, show -h+ -(h/2)= -(3*h/2) by ring, hoffm, add_zero,
      ← heqp, indicatorCutoff_suzukiApertureHilbert]
  have horth : inner ℂ (J up) (J um) = 0 := by
    change inner ℂ (J up : SoninL2) (J um : SoninL2) = 0
    rw [heqp, heqm]
    have hunit := (MellinL2.additiveTranslationUnitary (h/2)).inner_map_map
      (logTranslationCLM (h/2) f.1) (logTranslationCLM (-(h/2)) f.1)
    change inner ℂ (logTranslationCLM (h/2) (logTranslationCLM (h/2) f.1))
      (logTranslationCLM (h/2) (logTranslationCLM (-(h/2)) f.1)) = _ at hunit
    rw [logTranslationCLM_add_apply, logTranslationCLM_add_apply,
      show h/2+h/2=h by ring, show h/2+ -(h/2)=0 by ring,
      logTranslationCLM_zero_apply] at hunit
    rw [← hunit]
    apply inner_logTranslationCLM_eq_zero_of_aperture b f
    dsimp [b]; linarith
  have hpn : J up ≠ 0 := by
    intro hz
    have hn := ccmArchimedeanFormTranslate_physical (h/2) hfitp g.toCCMFormVector
    have hzero : logTranslationCLM (h/2) f.1 = 0 := by rw [← heqp, hz]; rfl
    have hnorm := (MellinL2.additiveTranslationUnitary (h/2)).norm_map f.1
    change ‖logTranslationCLM (h/2) f.1‖ = ‖f.1‖ at hnorm
    rw [hzero, norm_zero] at hnorm
    apply hgn
    exact Subtype.ext (norm_eq_zero.mp hnorm.symm)
  have hcn : J (up + um) ≠ 0 := by
    rw [map_add]
    intro hz
    have hi := congrArg (fun w => inner ℂ (J up) w) hz
    rw [inner_add_right, horth, inner_zero_right, add_zero] at hi
    exact hpn (inner_self_eq_zero.mp hi)
  have hdn : J (up - um) ≠ 0 := by
    rw [map_sub]
    intro hz
    have hi := congrArg (fun w => inner ℂ (J up) w) hz
    rw [inner_sub_right, horth, inner_zero_right, sub_zero] at hi
    exact hpn (inner_self_eq_zero.mp hi)
  have hc : IsPolarConstrained a (up+um) := by
    unfold IsPolarConstrained at hup hum ⊢
    rw [map_add, inner_add_right, inner_add_right, hup.1, hup.2, hum.1, hum.2]
    exact ⟨by simp, by simp⟩
  have hd : IsPolarConstrained a (up-um) := by
    unfold IsPolarConstrained at hup hum ⊢
    rw [map_sub, inner_sub_right, inner_sub_right, hup.1, hup.2, hum.1, hum.2]
    exact ⟨by simp, by simp⟩
  refine ⟨up+um, up-um, hc, hd, hcn, hdn, ?_, ?_⟩
  · change S (J (up+um)) = J (up+um)
    rw [map_add, map_add, hSp, hSm, add_comm]
  · change S (J (up-um)) = -J (up-um)
    rw [map_sub, map_sub, hSp, hSm, neg_sub]

/-- Exact norm in the nonempty two-chain range. -/
theorem norm_ccmApertureSymmetricTranslation_eq_one (a : SuzukiPositiveAperture)
    {h : ℝ} (hlo : a.1 < h) (hhi : h < 2*a.1) :
    ‖ccmApertureCompression a (ccmSymmetricLogTranslation h)‖ = 1 := by
  apply le_antisymm (norm_ccmApertureSymmetricTranslation_le_one a hlo)
  obtain ⟨u, v, hu, hv, hun, hvn, hue, hve⟩ :=
    exists_polarConstrained_outerShell_eigenvectors a hlo hhi
  have hop := (ccmApertureCompression a (ccmSymmetricLogTranslation h)).le_opNorm
    (ccmArchimedeanFormToAperture a u)
  rw [hue] at hop
  have hp := norm_pos_iff.mpr hun
  nlinarith

/-- Exact prime-atom norm on the outer logarithmic shell. -/
theorem norm_ccmPrimeTransportOperator_eq_outerShell (a : SuzukiPositiveAperture)
    (n : ℕ) (hlo : a.1 < Real.log n) (hhi : Real.log n < 2*a.1) :
    ‖ccmPrimeTransportOperator a n‖ = 1 / Real.sqrt n := by
  apply le_antisymm (norm_ccmPrimeTransportOperator_le_outerShell a n hlo)
  obtain ⟨u, v, hu, hv, hun, hvn, hue, hve⟩ :=
    exists_polarConstrained_outerShell_eigenvectors a hlo hhi
  have hop := (ccmPrimeTransportOperator a n).le_opNorm (ccmArchimedeanFormToAperture a u)
  change ‖((1 / Real.sqrt n : ℝ) : ℂ) •
      ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))
        (ccmArchimedeanFormToAperture a u)‖ ≤ _ at hop
  rw [hue, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _))] at hop
  have hp := norm_pos_iff.mpr hun
  nlinarith

/-- Sharp classification of every uniform constrained outer-shell contraction constant. -/
theorem polarConstrained_outerShell_bound_iff (a : SuzukiPositiveAperture)
    {h : ℝ} (hlo : a.1 < h) (hhi : h < 2*a.1) (C : ℝ) :
    (∀ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u →
      ‖ccmApertureCompression a (ccmSymmetricLogTranslation h)
          (ccmArchimedeanFormToAperture a u)‖ ≤
        C * ‖ccmArchimedeanFormToAperture a u‖) ↔ 1 ≤ C := by
  constructor
  · intro hb
    obtain ⟨u, v, hu, hv, hun, hvn, hue, hve⟩ :=
      exists_polarConstrained_outerShell_eigenvectors a hlo hhi
    have hbu := hb u hu
    rw [hue] at hbu
    have hp := norm_pos_iff.mpr hun
    nlinarith
  · intro hC u hu
    have hb := (ccmApertureCompression a (ccmSymmetricLogTranslation h)).le_opNorm
      (ccmArchimedeanFormToAperture a u)
    rw [norm_ccmApertureSymmetricTranslation_eq_one a hlo hhi, one_mul] at hb
    exact hb.trans (by nlinarith [norm_nonneg (ccmArchimedeanFormToAperture a u)])

end RHTower
