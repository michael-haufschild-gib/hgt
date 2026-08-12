import GaloisForLFunctions.RHTower.HedenmalmThetaPrimeQuantileHaarCarrier
import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

/-!
# Prime anomaly cyclicity on the forced Haar carrier

Every nontrivial normalized integer-translation anomaly is an `L¹ ∩ L²` function on the additive
Haar line.  Its exact Fourier profile is

`shiftMultiplier n (-2πξ) * XiC (-2πξ)`.

The Xi zero set is countable, and the additional prime multiplier has only a countable lattice of
zeros.  Hence the profile is nonzero almost everywhere, so Wiener's theorem makes the anomaly's
complete real-translation orbit cyclic in `L²(ℝ)`.

This produces a sharp carrier obstruction for Route P.  The same nonzero anomaly vanishes under
every Xi conormal character, but no nonzero continuous reporter on any carrier with dense Haar-
`L²` image can kill its complete orbit.  The retained divisor quotient must therefore cross a
genuinely singular rigging boundary; it cannot be a regular Hausdorff Hilbert completion of the
forced P-G106 carrier.
-/

open Complex MeasureTheory Set Filter
open scoped FourierTransform

namespace RHTower
noncomputable section

open MellinL2
open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

namespace HedenmalmThetaSource

/-- The coefficient-one normalized integer-translation anomaly in additive Haar `L²`. -/
def thetaIntegerAnomalyL2 (n : ℕ) (hn : 1 ≤ n) :
    Lp (α := ℝ) ℂ 2 volume :=
  (integerAnomaly_memLp_haar thetaSource hn).toLp _

/-- Exact classical Fourier profile of the theta integer anomaly. -/
def thetaIntegerAnomalyFourierProfile (n : ℕ) (xi : ℝ) : ℂ :=
  shiftMultiplier n (((-2 * Real.pi * xi : ℝ) : ℂ)) *
    XiC (((-2 * Real.pi * xi : ℝ) : ℂ))

/-- Frequency-side character orbit of the theta integer anomaly. -/
def thetaIntegerAnomalyFourierOrbit (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    Lp (α := ℝ) ℂ 2 volume :=
  fourierPhaseMulUnitary a (𝓕 (thetaIntegerAnomalyL2 n hn))

/-- Physical real-translation orbit of the theta integer anomaly. -/
def thetaIntegerAnomalyTranslationOrbit (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    Lp (α := ℝ) ℂ 2 volume :=
  additiveTranslationUnitary a (thetaIntegerAnomalyL2 n hn)

/-- The unitary `L²` Fourier transform of the anomaly equals its source-factorized classical
profile almost everywhere.  The only excluded frequency in the pointwise derivation is zero,
which is Haar-null. -/
theorem fourier_thetaIntegerAnomalyL2_ae
    {n : ℕ} (hn : 1 ≤ n) :
    (𝓕 (thetaIntegerAnomalyL2 n hn) : Lp (α := ℝ) ℂ 2 volume) =ᵐ[volume]
      thetaIntegerAnomalyFourierProfile n := by
  let f : Lp (α := ℝ) ℂ 2 volume := thetaIntegerAnomalyL2 n hn
  have hcoe : (f : ℝ → ℂ) =ᵐ[volume] integerAnomaly thetaSource n :=
    MemLp.coeFn_toLp (integerAnomaly_memLp_haar thetaSource hn)
  have hfint : Integrable (f : ℝ → ℂ) :=
    (integrable_integerAnomaly_haar thetaSource hn).congr hcoe.symm
  let f1 : Lp (α := ℝ) ℂ 1 volume :=
    (memLp_one_iff_integrable.mpr hfint).toLp f
  have hcoe1 : (f1 : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hfint)
  have hbridge := l2_fourier_coeFn_eq_l1_fourier_of_integrable f hfint
  have hne : ∀ᵐ xi : ℝ ∂volume, xi ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hbridge, hne] with xi hxi hxi0
  change (𝓕 f : Lp (α := ℝ) ℂ 2 volume) xi = _
  rw [hxi, Real.Lp.fourierTransform_apply]
  unfold thetaIntegerAnomalyFourierProfile
  have hz0 : (((-2 * Real.pi * xi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi0)
  have hzstrip : |(((-2 * Real.pi * xi : ℝ) : ℂ)).im| < 1 := by simp
  rw [← integral_integerAnomaly_sourceChar hn hzstrip hz0]
  apply integral_congr_ae
  filter_upwards [hcoe1, hcoe] with x hx1 hx
  rw [hx1, hx]
  rw [show ((innerₗ ℝ) x) xi = x * xi by exact Real.inner_apply x xi]
  change (Real.fourierChar (-(x * xi))) • integerAnomaly thetaSource n x = _
  rw [Circle.smul_def, smul_eq_mul,
    Real.fourierChar_apply, sourceChar]
  have hexp : Complex.exp (((2 * Real.pi * (-(x * xi)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (((-2 * Real.pi * xi : ℝ) : ℂ)) * (x : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- For every nontrivial integer label, the real-frequency zero set of the prime shift multiplier
is countable. -/
theorem countable_thetaIntegerAnomalyShiftMultiplier_zeroSet
    {n : ℕ} (hn : 2 ≤ n) :
    {xi : ℝ | shiftMultiplier n (((-2 * Real.pi * xi : ℝ) : ℂ)) = 0}.Countable := by
  let A : ℝ → ℂ := fun xi => (((-2 * Real.pi * xi : ℝ) : ℂ)) * (Real.log n : ℂ)
  have hlog : Real.log n ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hn)))
  have hAinj : Function.Injective A := by
    intro x y hxy
    dsimp only [A] at hxy
    have hcoef : -2 * Real.pi * Real.log n ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hlog
    have hxyR0 : (-2 * Real.pi * x) * Real.log n =
        (-2 * Real.pi * y) * Real.log n := by exact_mod_cast hxy
    have hxyR : (-2 * Real.pi * Real.log n) * x =
        (-2 * Real.pi * Real.log n) * y := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hxyR0
    exact mul_left_cancel₀ hcoef hxyR
  have hcount :
      ({0} ∪ ⋃ j : ℤ, A ⁻¹' {((2 * Real.pi : ℝ) : ℂ) * (j : ℂ)}).Countable := by
    apply Set.Countable.union (Set.countable_singleton 0)
    apply Set.countable_iUnion
    intro j
    exact (Set.countable_singleton _).preimage hAinj
  refine hcount.mono ?_
  intro xi hxi
  by_cases hxi0 : xi = 0
  · exact Set.mem_union_left _ (by simp [hxi0])
  · have hz0 : (((-2 * Real.pi * xi : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi0)
    obtain ⟨j, hj⟩ := (shiftMultiplier_eq_zero_iff hn hz0).mp hxi
    apply Set.mem_union_right
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨j, by simpa [A] using hj⟩

/-- The complete anomaly Fourier profile has only countably many real zeros: a countable prime
lattice union the countable Xi divisor. -/
theorem countable_thetaIntegerAnomalyFourierProfile_zeroSet
    {n : ℕ} (hn : 2 ≤ n) :
    {xi : ℝ | thetaIntegerAnomalyFourierProfile n xi = 0}.Countable := by
  let Zxi : Set ℝ :=
    (fun xi : ℝ => (((-2 * Real.pi * xi : ℝ) : ℂ))) ⁻¹' {z : ℂ | XiC z = 0}
  have hscale : Function.Injective
      (fun xi : ℝ => (((-2 * Real.pi * xi : ℝ) : ℂ))) := by
    intro x y hxy
    have hcoef : -2 * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hxyR : -2 * Real.pi * x = -2 * Real.pi * y :=
      Complex.ofReal_injective hxy
    exact mul_left_cancel₀ hcoef hxyR
  have hZxi : Zxi.Countable := XiC_zeroSet_countable.preimage hscale
  have hZshift := countable_thetaIntegerAnomalyShiftMultiplier_zeroSet hn
  refine (hZshift.union hZxi).mono ?_
  intro xi hzero
  change shiftMultiplier n (((-2 * Real.pi * xi : ℝ) : ℂ)) *
      XiC (((-2 * Real.pi * xi : ℝ) : ℂ)) = 0 at hzero
  rw [mul_eq_zero] at hzero
  exact hzero.elim (fun h => Or.inl h) (fun h => Or.inr h)

/-- The anomaly Fourier profile is nonzero almost everywhere on the Haar line. -/
theorem thetaIntegerAnomalyFourierProfile_ne_zero_ae
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ xi ∂(volume : Measure ℝ), thetaIntegerAnomalyFourierProfile n xi ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff] using
    (countable_thetaIntegerAnomalyFourierProfile_zeroSet hn).measure_zero volume

/-- Frequency-side Wiener cyclicity of every nontrivial integer anomaly. -/
theorem isCyclicFamily_thetaIntegerAnomalyFourierOrbit
    {n : ℕ} (hn : 2 ≤ n) :
    IsCyclicFamily (𝕜 := ℂ)
      (thetaIntegerAnomalyFourierOrbit n (hn.trans' one_le_two)) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let g : Lp (α := ℝ) ℂ 2 volume :=
    (InnerProductSpace.toDual ℂ (Lp (α := ℝ) ℂ 2 volume)).symm L
  have hinner (a : ℝ) :
      inner ℂ g (thetaIntegerAnomalyFourierOrbit n (hn.trans' one_le_two) a) = 0 := by
    have h := hL a
    change L (thetaIntegerAnomalyFourierOrbit n (hn.trans' one_le_two) a) = 0 at h
    simpa [g, InnerProductSpace.toDual_symm_apply] using h
  let F : Lp (α := ℝ) ℂ 2 volume := 𝓕 (thetaIntegerAnomalyL2 n (hn.trans' one_le_two))
  let f : ℝ → ℂ := fun x => inner ℂ (g x) (F x)
  have hfmeas : Measurable f := by
    exact ((Lp.stronglyMeasurable g).inner (Lp.stronglyMeasurable F)).measurable
  have hfint : Integrable f := L2.integrable_inner g F
  have hfourier (t : ℝ) : ∫ x, realProbCharacter t x * f x = 0 := by
    let a : ℝ := t / (2 * Real.pi)
    have ht := hinner a
    rw [L2.inner_def] at ht
    have hpoint :
        (fun x : ℝ => inner ℂ (g x)
          (thetaIntegerAnomalyFourierOrbit n (hn.trans' one_le_two) a x)) =ᵐ[volume]
          fun x => realProbCharacter t x * f x := by
      filter_upwards [fourierPhaseMulAux_ae a F] with x hx
      change inner ℂ (g x) (fourierPhaseMulAux a F x) = _
      rw [hx, fourierPhase_div_twoPi_eq_realProbCharacter]
      simp only [f, inner]
      ring
    rw [integral_congr_ae hpoint] at ht
    exact ht
  have hfzero := ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero_complex
    (volume : Measure ℝ) hfmeas hfint hfourier
  have hgzero : g = 0 := by
    apply Lp.ext
    filter_upwards [hfzero, fourier_thetaIntegerAnomalyL2_ae (hn.trans' one_le_two),
      thetaIntegerAnomalyFourierProfile_ne_zero_ae hn,
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hfx hprofile hnonzero hzero
    rw [hzero]
    have hmul : thetaIntegerAnomalyFourierProfile n x * (starRingEnd ℂ) (g x) = 0 := by
      simpa [f, F, hprofile] using hfx
    have hgstar : (starRingEnd ℂ) (g x) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hnonzero
    have := congrArg (starRingEnd ℂ) hgstar
    simpa using this
  calc
    L = (InnerProductSpace.toDual ℂ (Lp (α := ℝ) ℂ 2 volume)) g := by
      symm
      exact (InnerProductSpace.toDual ℂ
        (Lp (α := ℝ) ℂ 2 volume)).apply_symm_apply L
    _ = 0 := by rw [hgzero]; simp

/-- Plancherel intertwines the physical translation orbit with the displayed phase orbit. -/
theorem fourier_thetaIntegerAnomalyTranslationOrbit
    {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    𝓕 (thetaIntegerAnomalyTranslationOrbit n hn a) =
      thetaIntegerAnomalyFourierOrbit n hn a := by
  rw [thetaIntegerAnomalyTranslationOrbit, thetaIntegerAnomalyFourierOrbit,
    fourier_additiveTranslation]

/-- **P-G107.** Every nontrivial coefficient-one prime anomaly is cyclic under complete real
translation in the additive Haar `L²` carrier forced by P-G106. -/
theorem isCyclicFamily_thetaIntegerAnomalyTranslationOrbit
    {n : ℕ} (hn : 2 ≤ n) :
    IsCyclicFamily (𝕜 := ℂ)
      (thetaIntegerAnomalyTranslationOrbit n (hn.trans' one_le_two)) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let LF : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ :=
    L.comp (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.toContinuousLinearMap
  have hLF (a : ℝ) :
      LF (thetaIntegerAnomalyFourierOrbit n (hn.trans' one_le_two) a) = 0 := by
    change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (thetaIntegerAnomalyFourierOrbit n (hn.trans' one_le_two) a)) = 0
    rw [← fourier_thetaIntegerAnomalyTranslationOrbit]
    change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
      ((Lp.fourierTransformₗᵢ ℝ ℂ)
        (thetaIntegerAnomalyTranslationOrbit n (hn.trans' one_le_two) a))) = 0
    simpa using hL a
  have hLFzero := continuousLinearFunctional_eq_zero_of_isCyclicFamily
    (isCyclicFamily_thetaIntegerAnomalyFourierOrbit hn) LF hLF
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun M : Lp (α := ℝ) ℂ 2 volume →L[ℂ] ℂ =>
      M ((Lp.fourierTransformₗᵢ ℝ ℂ) x)) hLFzero
  change L ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
    ((Lp.fourierTransformₗᵢ ℝ ℂ) x)) = 0 at hx
  simpa using hx

/-- **Continuous-quotient collapse.** A continuous reporter on a carrier with dense Haar-`L²`
image which kills every translate of one nontrivial prime anomaly is identically zero. -/
theorem thetaIntegerAnomaly_continuousBoundaryReporter_eq_zero
    {B Y : Type*}
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {n : ℕ} (hn : 2 ≤ n)
    (j : Lp (α := ℝ) ℂ 2 volume →L[ℂ] B) (hj : DenseRange j)
    (q : B →L[ℂ] Y)
    (hkill : ∀ a : ℝ,
      q (j (thetaIntegerAnomalyTranslationOrbit n (hn.trans' one_le_two) a)) = 0) :
    q = 0 :=
  continuousBoundaryReporter_eq_zero_of_cyclic_denseRange
    (thetaIntegerAnomalyTranslationOrbit n (hn.trans' one_le_two))
    (isCyclicFamily_thetaIntegerAnomalyTranslationOrbit hn)
    j hj q hkill

end HedenmalmThetaSource
end
end RHTower
