import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBoundaryPrimitive
import GaloisForLFunctions.RHTower.ConnesFractionalSymbolGrowth

/-!
# An absolute Mellin overlap for the actual Fourier primitive

Subtracting the primitive's value at zero replaces each cosine by cosine minus
one. The existing Levy-kernel scaling law then makes the sum of weighted L1
norms finite on `1 < re s < 2`, using only the original cubic datum. Absolute
Fubini identifies its Mellin transform with the actual Dirichlet quotient.
The scalar cosine kernel's Gamma evaluation and cutoff-defect continuation
remain separate steps; no sparse-deficit regularity is asserted here.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open scoped ENNReal
namespace RHTower.WeilHigherDenominator


private def primitiveMellinTerm (q : ℕ → ℂ) (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 3) * (q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
    ((Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) - 1))

private lemma norm_primitiveMellinTerm (q : ℕ → ℂ) (s : ℂ) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    ‖primitiveMellinTerm q s n x‖ =
      (‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
        connesLevyKernelAt (2 - s.re) (2 * Real.pi * (n + 1)) x := by
  have hc : ‖(Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) - 1‖ =
      1 - Real.cos (2 * Real.pi * (n + 1) * x) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    ring
  simp only [primitiveMellinTerm, norm_mul, norm_div, norm_pow, Complex.norm_natCast,
    hc, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.re_ofNat,
    connesLevyKernelAt]
  rw [show -1 - (2 - s.re) = s.re - 3 by ring]
  ring

private lemma integrable_primitiveMellinTerm (q : ℕ → ℂ) {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) (n : ℕ) :
    IntegrableOn (primitiveMellinTerm q s n) (Ioi 0) := by
  have hm : AEStronglyMeasurable (primitiveMellinTerm q s n) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · exact fun x hx => (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr (ne_of_gt hx))).continuousWithinAt
    · exact (by fun_prop : Continuous fun x : ℝ => q (n + 1) /
        ((n + 1 : ℕ) : ℂ) ^ 2 *
          ((Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) - 1)).continuousOn
  apply (integrable_norm_iff hm).mp
  apply ((connes_levyAt_integrableOn (α := 2 - s.re) (by linarith)
    (by linarith) (2 * Real.pi * (n + 1))).const_mul
      (‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (norm_primitiveMellinTerm q s n hx).symm

private lemma integral_norm_primitiveMellinTerm (q : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖primitiveMellinTerm q s n x‖) =
      (connesLevyConstant (2 - s.re) * (2 * Real.pi) ^ (2 - s.re)) *
        (‖q (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => norm_primitiveMellinTerm q s n hx), integral_const_mul]
  simp only [connesLevyKernelAt]
  rw [connes_levy_scaling (by positivity)]
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hp : 0 < 2 * Real.pi := by positivity
  rw [Real.mul_rpow hp.le (by positivity)]
  have hpow : ((n + 1 : ℕ) : ℝ) ^ (2 - s.re) =
      ((n + 1 : ℕ) : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
    rw [← Real.rpow_two, ← Real.rpow_add hn]
    congr 1
  push_cast at hpow hn ⊢
  rw [hpow]
  field_simp

private lemma hasFiniteIntegral_tsum_of_integral_norm {F : ℕ → ℝ → ℂ}
    {μ : Measure ℝ} (hi : ∀ n, Integrable (F n) μ)
    (hs : Summable fun n => ∫ x, ‖F n x‖ ∂μ) :
    HasFiniteIntegral (fun x => ∑' n, F n x) μ := by
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x, ‖∑' n, F n x‖ₑ ∂μ) ≤ ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ :=
      lintegral_tsum (fun n => (hi n).aestronglyMeasurable.enorm)
    _ = ∑' n, ENNReal.ofReal (∫ x, ‖F n x‖ ∂μ) := by
      apply tsum_congr
      intro n
      exact (ofReal_integral_norm_eq_lintegral_enorm (hi n)).symm
    _ < ∞ := hs.tsum_ofReal_lt_top

private lemma primitiveMellin_series_eq {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (s : ℂ) (x : ℝ) :
    (x : ℂ) ^ (s - 3) * (fourierBoundaryPrimitive q x - fourierBoundaryPrimitive q 0) =
      (∑' n, primitiveMellinTerm q s n x) / (Real.pi : ℂ) ^ 2 := by
  rw [fourierBoundaryPrimitive_sub_zero hq]
  simp only [primitiveMellinTerm, tsum_mul_left, mul_div_assoc]

/-- The zero-subtracted primitive has an absolutely convergent Mellin overlap. -/
theorem integrable_fourierBoundaryPrimitive_mellin {q : ℕ → ℂ} {s : ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (hqs : Summable fun n : ℕ => ‖q (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re))
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 3) *
      (fourierBoundaryPrimitive q x - fourierBoundaryPrimitive q 0)) (Ioi 0) := by
  have hi := integrable_primitiveMellinTerm q hs0 hs2
  have hsum : Summable fun n => ∫ x in Ioi (0 : ℝ), ‖primitiveMellinTerm q s n x‖ := by
    simp_rw [integral_norm_primitiveMellinTerm]
    exact hqs.mul_left _
  have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 3) *
      (fourierBoundaryPrimitive q x - fourierBoundaryPrimitive q 0)) (Ioi 0) := by
    apply ContinuousOn.mul
    · exact fun x hx => (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr (ne_of_gt hx))).continuousWithinAt
    · exact ((continuous_fourierBoundaryPrimitive hq).sub continuous_const).continuousOn
  have heq : (fun x => ∑' n, primitiveMellinTerm q s n x) =
      fun x : ℝ => ((x : ℂ) ^ (s - 3) *
        (fourierBoundaryPrimitive q x - fourierBoundaryPrimitive q 0)) * (Real.pi : ℂ) ^ 2 := by
    ext x
    rw [primitiveMellin_series_eq hq]
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact (div_mul_cancel₀ _ (pow_ne_zero _ hp)).symm
  have hmi : Integrable (fun x => ∑' n, primitiveMellinTerm q s n x)
      (volume.restrict (Ioi 0)) := by
    refine ⟨?_, hasFiniteIntegral_tsum_of_integral_norm hi hsum⟩
    rw [heq]
    exact (hc.mul continuousOn_const).aestronglyMeasurable measurableSet_Ioi
  exact (hmi.div_const _).congr (Eventually.of_forall
    (fun x => (primitiveMellin_series_eq hq s x).symm))

/-- Absolute Mellin convergence from the original cubic datum, without a cusp-regularity premise. -/
theorem degreeTwoQuotient_primitive_mellinConvergent {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    MellinConvergent (fun x => fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x -
      fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) 0) (s - 2) := by
  have hqs := (summable_nat_add_iff 1).mpr (degreeTwoQuotientCoeff_weighted_summable hD hs1)
  have hi := integrable_fourierBoundaryPrimitive_mellin
    (degreeTwoQuotientCoeff_summable_shift_square hD) hqs (by linarith) hs2
  simpa only [MellinConvergent, smul_eq_mul, show s - 2 - 1 = s - 3 by ring] using hi

/-- The real weighted L1 estimate needed for smooth cutoff limits. -/
theorem degreeTwoQuotient_primitive_weighted_integrable {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) :
    IntegrableOn (fun x : ℝ => x ^ (σ - 3) *
      ‖fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x -
        fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) 0‖) (Ioi 0) := by
  have h := degreeTwoQuotient_primitive_mellinConvergent hD
    (s := (σ : ℂ)) hσ1 hσ2
  apply h.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.re_ofNat, Complex.one_re]
  rw [show σ - 2 - 1 = σ - 3 by ring]


/-- The absolutely regularized cosine Mellin kernel; its Gamma evaluation is separate. -/
def cosineDifferenceMellin (s : ℂ) : ℂ :=
  mellin (fun x : ℝ => (Real.cos (2 * Real.pi * x) : ℂ) - 1) (s - 2)

private lemma integral_primitiveMellinTerm (q : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), primitiveMellinTerm q s n x) =
      (q (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s)) * cosineDifferenceMellin s := by
  let K := fun x : ℝ => (Real.cos (2 * Real.pi * x) : ℂ) - 1
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hnC : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hscale := mellin_comp_mul_left K (s - 2) hn
  have hpow : (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-(s - 2)) =
      ((n + 1 : ℕ) : ℂ) ^ 2 * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    have hncast : (((n + 1 : ℕ) : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by norm_cast
    rw [hncast, show -(s - 2) = 2 + (-s) by ring,
      Complex.cpow_add _ _ hnC, Complex.cpow_two]
  calc
    (∫ x in Ioi (0 : ℝ), primitiveMellinTerm q s n x) =
        q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
          mellin (fun x => K (((n + 1 : ℕ) : ℝ) * x)) (s - 2) := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      simp only [primitiveMellinTerm, K, smul_eq_mul,
        show s - 2 - 1 = s - 3 by ring]
      have hf : 2 * Real.pi * (n + 1) * x =
          2 * Real.pi * (((n + 1 : ℕ) : ℝ) * x) := by push_cast; ring
      rw [hf]
      ring
    _ = _ := by
      rw [hscale, smul_eq_mul, hpow]
      change q (n + 1) / ((n + 1 : ℕ) : ℂ) ^ 2 *
        (((n + 1 : ℕ) : ℂ) ^ 2 * ((n + 1 : ℕ) : ℂ) ^ (-s) * cosineDifferenceMellin s) = _
      field_simp

/-- The original quotient is the exact Mellin coefficient of the continuous primitive.
No boundary regularity or infinite residue expansion is assumed. -/
theorem hasMellin_degreeTwoQuotient_primitive {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    HasMellin (fun x => fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x -
      fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) 0) (s - 2)
        ((LSeries g s / riemannZeta s) * cosineDifferenceMellin s / (Real.pi : ℂ) ^ 2) := by
  refine ⟨degreeTwoQuotient_primitive_mellinConvergent hD hs1 hs2, ?_⟩
  have hq := degreeTwoQuotientCoeff_summable_shift_square hD
  have hqs := (summable_nat_add_iff 1).mpr (degreeTwoQuotientCoeff_weighted_summable hD hs1)
  have hi := integrable_primitiveMellinTerm (degreeTwoQuotientCoeff g) (by linarith) hs2
  have hsum : Summable fun n => ∫ x in Ioi (0 : ℝ),
      ‖primitiveMellinTerm (degreeTwoQuotientCoeff g) s n x‖ := by
    simp_rw [integral_norm_primitiveMellinTerm]
    exact hqs.mul_left _
  have hLs := degreeTwoQuotientCoeff_summable (hD.summable s hs1) hs1
  have hshift : LSeries (degreeTwoQuotientCoeff g) s =
      ∑' n, degreeTwoQuotientCoeff g (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    rw [LSeries, hLs.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
  simp only [mellin, smul_eq_mul, show s - 2 - 1 = s - 3 by ring]
  simp_rw [primitiveMellin_series_eq hq]
  rw [integral_div, ← integral_tsum_of_summable_integral_norm hi hsum]
  simp_rw [integral_primitiveMellinTerm]
  rw [tsum_mul_right, ← hshift, LSeries_degreeTwoQuotientCoeff (hD.summable s hs1) hs1]

end RHTower.WeilHigherDenominator
