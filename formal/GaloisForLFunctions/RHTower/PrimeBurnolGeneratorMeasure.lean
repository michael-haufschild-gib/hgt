import GaloisForLFunctions.HTGeometry.InfinitesimalCompleteMonotonicity
import GaloisForLFunctions.RHTower.PrimeBurnolOperatorExponential
import GaloisForLFunctions.RHTower.PrimeBurnolJumpMeasure

/-! Infinitesimal Bernstein extraction and canonical finite-jump recovery from positive prime dynamics. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexOrder NNReal
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

private lemma exists_boundedNNRealLaplaceMeasure {H : ℝ → ℝ}
    (hH : CompletelyMonotoneOn H) (hb : BddAbove (H '' Ioi 0)) :
    ∃ τ : Measure ℝ≥0, IsFiniteMeasure τ ∧
      ∀ x : ℝ, 0 < x → H x = burnolMeasureLaplace τ x := by
  have hant : AntitoneOn H (Ioi 0) := fun _ hx _ _ hxy =>
    completelyMonotoneDiff_antitone hH.1 hx hxy
  obtain ⟨ν, hν, hsupp, hLap⟩ :=
    exists_finiteLaplaceMeasure_of_completelyMonotoneOn hH (hant.tendsto_nhdsGT hb)
  letI : IsFiniteMeasure ν := hν
  let τ : Measure ℝ≥0 := ν.map Real.toNNReal
  have hνpos : ∀ᵐ r ∂ν, 0 ≤ r := ae_iff.mpr hsupp
  refine ⟨τ, inferInstance, fun x hx => ?_⟩
  rw [hLap x hx, burnolMeasureLaplace]
  change _ = ∫ h : ℝ≥0, Real.exp (-(x * h)) ∂ν.map Real.toNNReal
  rw [integral_map continuous_real_toNNReal.measurable.aemeasurable
    (by exact (by fun_prop : Continuous (fun h : ℝ≥0 => Real.exp (-(x * h)))).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [hνpos] with r hr
  rw [Real.coe_toNNReal r hr]
  congr 1
  ring

/-- Positivity of every exponential forces a finite positive scalar correction of the generator. -/
theorem primeBurnol_positive_generator_measure
    (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, A (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hpos : ∀ t : ℝ, 0 ≤ t → BurnolPreservesNonnegativity (burnolEvolution A t)) :
    ∃ τ : Measure ℝ≥0, IsFiniteMeasure τ ∧
      ∀ f, A f + (‖A‖ : ℂ) • f = ∫ h, burnolWeightedShift h f ∂τ := by
  have hreal : ∀ x : ℝ, 0 < x → (burnolOperatorSymbol A x).im = 0 := by
    intro x hx
    apply im_eq_zero_of_exp_nonneg
    intro t ht
    have hp := burnolOperatorSymbol_real_nonneg (burnolEvolution A t)
      (fun p => Complex.exp ((t : ℂ) * a p)) (burnolEvolution_prime A a ha t)
      (hpos t ht.le).packetTest x hx
    rwa [burnolEvolution_symbol A a ha t (z := (x : ℂ)) hx] at hp
  have hcm : ∀ t : ℝ, 0 < t →
      CompletelyMonotoneDiff (fun x : ℝ => Real.exp (t * (burnolOperatorSymbol A x).re)) := by
    intro t ht
    have hp := burnolOperatorSymbol_completelyMonotone (burnolEvolution A t)
      (fun p => Complex.exp ((t : ℂ) * a p)) (burnolEvolution_prime A a ha t)
      (hpos t ht.le).packetTest
    apply completelyMonotoneDiff_congr_Ioi (hF := hp.1)
    intro x hx
    change (burnolOperatorSymbol (burnolEvolution A t) (x : ℂ)).re =
      Real.exp (t * (burnolOperatorSymbol A (x : ℂ)).re)
    rw [burnolEvolution_symbol A a ha t (z := (x : ℂ)) hx]
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, hreal x hx]
  let H : ℝ → ℝ := fun x => (burnolOperatorSymbol A x).re + ‖A‖
  have hH : CompletelyMonotoneOn H := by
    constructor
    · apply completelyMonotoneDiff_infinitesimal (h := hcm)
      intro x hx
      have hn := Complex.re_le_norm (-burnolOperatorSymbol A (x : ℂ))
      have hb := burnolOperatorSymbol_bound A a ha (z := (x : ℂ)) hx
      simp only [Complex.neg_re, norm_neg] at hn
      linarith
    · intro x hx
      exact ((Complex.continuous_re.continuousAt.comp
        ((burnolOperatorSymbol_analytic A (x : ℂ) hx).continuousAt.comp
          Complex.continuous_ofReal.continuousAt)).add continuousAt_const).continuousWithinAt
  have hb : BddAbove (H '' Ioi 0) := by
    refine ⟨2 * ‖A‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change (burnolOperatorSymbol A x).re + ‖A‖ ≤ 2 * ‖A‖
    have h1 := Complex.re_le_norm (burnolOperatorSymbol A (x : ℂ))
    have h2 := burnolOperatorSymbol_bound A a ha (z := (x : ℂ)) hx
    linarith
  obtain ⟨τ, hτ, hLap⟩ := exists_boundedNNRealLaplaceMeasure hH hb
  letI : IsFiniteMeasure τ := hτ
  have hscalar : ∀ x : ℝ, 0 < x → (burnolMeasureLaplace τ x : ℂ) =
      burnolOperatorSymbol A x + (‖A‖ : ℂ) := by
    intro x hx
    apply Complex.ext
    · exact (hLap x hx).symm
    · simp [hreal x hx]
  have he : A + (‖A‖ : ℂ) • 1 = burnolPositiveShiftMixture τ := by
    apply primeBurnol_operator_ext
    intro p
    change A (primeLogCriticalLaplaceFeatureL2 p) +
      (‖A‖ : ℂ) • primeLogCriticalLaplaceFeatureL2 p = _
    rw [ha, (primeBurnol_positive_measure_realization τ).2.1 p, ← add_smul]
    have hp := hscalar (Real.log (p : ℝ)) (Real.log_pos (by exact_mod_cast p.property.one_lt))
    rw [burnolOperatorSymbol_prime A a ha p] at hp
    rw [hp]
  exact ⟨τ, hτ, fun f => congrArg (fun T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 => T f) he⟩

/-- Contractivity at one positive time already makes the canonical killing rate nonnegative. -/
theorem primeBurnol_positive_contraction_generator_exists
    (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, A (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hpos : ∀ t : ℝ, 0 ≤ t → BurnolPreservesNonnegativity (burnolEvolution A t))
    (hnorm : ‖burnolEvolution A 1‖ ≤ 1) :
    ∃ D : BurnolJumpData, A = D.generator := by
  obtain ⟨τ, hτ, he⟩ := primeBurnol_positive_generator_measure A a ha hpos
  letI : IsFiniteMeasure τ := hτ
  have hA : A = burnolPositiveShiftMixture τ - (‖A‖ : ℂ) • 1 := by
    apply eq_sub_iff_add_eq.mpr
    exact ContinuousLinearMap.ext he
  have hrate : ∀ x : ℝ, ∀ hx : 0 < x, A (burnolRateFeature x hx) =
      ((burnolMeasureLaplace τ x - ‖A‖ : ℝ) : ℂ) • burnolRateFeature x hx := by
    intro x hx
    conv_lhs => rw [hA]
    change burnolPositiveShiftMixture τ (burnolRateFeature x hx) -
      (‖A‖ : ℂ) • burnolRateFeature x hx = _
    rw [burnolPositiveShiftMixture_rate, ← sub_smul, Complex.ofReal_sub]
  have hbound : ∀ x : ℝ, 0 < x → burnolMeasureLaplace τ x ≤ ‖A‖ := by
    intro x hx
    have hn : burnolRateFeature x hx ≠ 0 := by
      simpa only [burnolComplexFeature_ofReal, burnolRateFeature] using
        burnolComplexFeature_ne_zero (z := (x : ℂ)) hx
    have hexp : burnolEvolution A 1 (burnolRateFeature x hx) =
        (Real.exp (burnolMeasureLaplace τ x - ‖A‖) : ℂ) • burnolRateFeature x hx := by
      simpa only [burnolEvolution, Complex.ofReal_one, one_mul, Complex.ofReal_exp] using
        operator_exp_eigen A (hrate x hx) (1 : ℂ)
    have hb := (burnolEvolution A 1).le_opNorm (burnolRateFeature x hx)
    rw [hexp, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hb
    have hle : Real.exp (burnolMeasureLaplace τ x - ‖A‖) ≤ 1 :=
      (le_of_mul_le_mul_right hb (norm_pos_iff.mpr hn)).trans hnorm
    have hh := Real.exp_le_one_iff.mp hle
    linarith
  have hmass : (τ univ).toReal ≤ ‖A‖ := by
    apply le_of_tendsto (tendsto_burnolMeasureLaplace_zero τ)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hbound x hx
  let D : BurnolJumpData := {
    measure := burnolJumpMeasure τ
    finite := inferInstance
    zero_atom := burnolJumpMeasure_zero τ
    killing := ⟨‖A‖ - (τ univ).toReal, sub_nonneg.mpr hmass⟩ }
  refine ⟨D, ?_⟩
  have hc : (D.killing : ℝ) + (D.measure univ).toReal = ‖A‖ - (τ {0}).toReal := by
    change ‖A‖ - (τ univ).toReal + (burnolJumpMeasure τ univ).toReal = _
    rw [burnolJumpMeasure_mass_split τ]
    ring
  rw [hA, burnolPositiveShiftMixture_jump_split]
  change burnolPositiveShiftMixture (burnolJumpMeasure τ) + ((τ {0}).toReal : ℂ) • 1 -
    (‖A‖ : ℂ) • 1 = burnolPositiveShiftMixture (burnolJumpMeasure τ) -
      (((D.killing : ℝ) + (D.measure univ).toReal : ℝ) : ℂ) • 1
  rw [hc, Complex.ofReal_sub, sub_smul]
  abel

end RHTower
