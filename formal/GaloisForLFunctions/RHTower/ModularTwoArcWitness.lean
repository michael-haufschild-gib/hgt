import GaloisForLFunctions.RHTower.UnitCircleLineVector
import GaloisForLFunctions.RHTower.UnitCircleGeneratorComparison
import GaloisForLFunctions.RHTower.ModularSideArcCuspDecay

/-!
# A two-arc witness: integer-blind, self-reciprocal, strictly positive definite, zero mass

Two positive measures on the unit semicircle annihilate every nonconstant decaying Whittaker
function at `s = ½`:
* on the bottom arc `{|z| = 1, |Re z| ≤ ½}` the probability measure `μ_A` of
  `exists_probabilityMeasure_arc_annihilating`, with generator points `z = u + i√(1 − u²)`;
* on the side arcs `{|z| = 1, ½ ≤ |Re z| < 1}` the measure `κ_S = w μ_S`, `w = 1/K₀(c_0 y)`, built
  from `exists_probabilityMeasure_sideArc_annihilating`, with generator points
  `z = (1 − |s|) + i y(s)`.

Superpose the even Poisson pairs `P_z(x) = |x − z|^{−1} + |x + z̄|^{−1}` (divided by `√y`):
`H_A = ∫ P_z dμ_A`, `H_S = ∫ P_z dκ_S`, and put

`h = H_S/κ_S(univ) − H_A`  (`twoArcWitness`).

**Theorem** (`twoArcWitness_properties`).  `h` is even, `h(1/x) = |x| h(x)`, `h'` is integrable,
`∫ h'(x) sin(2π(n+1)x) dx = ∫ h'(x) cos(2π(n+1)x) dx = 0` for every `n`, and the log profile
`e^{v/2} h(e^v)` has strictly positive cosine transform at every real frequency.

Proof of positive definiteness.  The cosine transform is
`2^{−1/2}(⟨Ŝ_c(τ)⟩_S − ⟨Ŝ_c(τ)⟩_A)` with normalized averages.  Side-arc points have `|c| ≥ ½`,
bottom arc points `|c| ≤ ½`, and `Ŝ_c(τ)` increases with `|c|`
(`integral_cos_mul_symCoshKernel_le_of_abs_le`), so the difference is at least
`Ŝ_{1/2}(τ) − Ŝ_{1/2}(τ) = 0`.  It is strict because `μ_S` charges `0 < |s| < ½`: a measure carried
by the corners and the cusp cannot annihilate the first normalized mode.

The two masses are normalized to `1`, so the `e^{−|v|/2}` tails of the two profiles cancel.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### The bottom-arc data -/

/-- The real part `c = u` of a bottom-arc point. -/
def arcPointRe (u : ArcParam) : ℝ := u

/-- The height `y = √(1 − u²)` of a bottom-arc point. -/
def arcPointIm (u : ArcParam) : ℝ := modularArcHeight u

theorem circleData_arc (μ : Measure ArcParam) [IsFiniteMeasure μ] :
    CircleData μ arcPointRe arcPointIm where
  meas_c := continuous_subtype_val.measurable
  meas_y := (by unfold modularArcHeight; fun_prop : Continuous fun u : ArcParam =>
    modularArcHeight u).measurable
  circle := Eventually.of_forall fun u => modularArcHeight_sq u.2
  pos := Eventually.of_forall fun u => modularArcHeight_pos u.2
  inv_sq := by
    refine (BoundedContinuousFunction.mkOfCompact ⟨fun u : ArcParam => 1 / modularArcHeight u ^ 2,
      ?_⟩).integrable μ
    have hc : Continuous fun u : ArcParam => modularArcHeight u := by
      unfold modularArcHeight; fun_prop
    exact continuous_const.div (hc.pow 2) fun u => (pow_pos (modularArcHeight_pos u.2) 2).ne'

/-! ### The side-arc data -/

/-- The real part `c = 1 − |s|` of the unit-circle point attached to a side-arc parameter. -/
def sidePointRe (s : ArcParam) : ℝ := 1 - |(s : ℝ)|

/-- The height `y(s)` of a side-arc point. -/
def sidePointIm (s : ArcParam) : ℝ := sideArcHeight s

theorem sidePoint_circle (s : ArcParam) : sidePointRe s ^ 2 + sidePointIm s ^ 2 = 1 := by
  unfold sidePointRe sidePointIm
  rw [sideArcHeight_sq s.2, ← sq_abs (s : ℝ)]
  ring

/-- The weight `w` as a nonnegative real function. -/
def sideKWeightNN (s : ArcParam) : NNReal := (sideKWeight s).toNNReal

theorem coe_sideKWeightNN (s : ArcParam) : (sideKWeightNN s : ℝ) = sideKWeight s :=
  Real.coe_toNNReal _ (sideKWeight_nonneg _)

theorem measurable_sideKWeightNN : Measurable sideKWeightNN :=
  continuous_sideKWeight.measurable.real_toNNReal

/-- The side-arc generator measure `κ_S = w μ_S`. -/
def sideGenMeasure (μ : Measure ArcParam) : Measure ArcParam :=
  μ.withDensity fun s => (sideKWeightNN s : ℝ≥0∞)

theorem integral_sideGenMeasure (μ : Measure ArcParam) (g : ArcParam → ℝ) :
    ∫ s, g s ∂(sideGenMeasure μ) = ∫ s, sideKWeight s * g s ∂μ := by
  unfold sideGenMeasure
  rw [integral_withDensity_eq_integral_smul measurable_sideKWeightNN]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  show sideKWeightNN s • g s = sideKWeight s * g s
  rw [NNReal.smul_def, coe_sideKWeightNN, smul_eq_mul]

instance (μ : Measure ArcParam) [IsFiniteMeasure μ] : IsFiniteMeasure (sideGenMeasure μ) := by
  unfold sideGenMeasure
  refine isFiniteMeasure_withDensity ?_
  have hint := integrable_sideKWeight μ
  have h := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun s =>
    sideKWeight_nonneg s)
  have e : ∀ s : ArcParam, ENNReal.ofReal (sideKWeight s) = (sideKWeightNN s : ℝ≥0∞) := by
    intro s; rw [← coe_sideKWeightNN, ENNReal.ofReal_coe_nnreal]
  simp_rw [e] at h
  rw [← h]
  exact ENNReal.ofReal_ne_top

theorem sideGenMeasure_ac (μ : Measure ArcParam) : sideGenMeasure μ ≪ μ :=
  withDensity_absolutelyContinuous _ _

theorem ae_sidePointIm_pos {μ : Measure ArcParam} (hcusp : μ sideCusp = 0) :
    ∀ᵐ s ∂μ, 0 < sidePointIm s := by
  rw [ae_iff]
  refine measure_mono_null (fun s hs => ?_) hcusp
  simp only [mem_setOf_eq, not_lt] at hs
  show (s : ℝ) = 0
  by_contra h0
  exact absurd (sideArcHeight_pos s.2 h0) (not_lt.mpr hs)

theorem circleData_side (μ : Measure ArcParam) [IsFiniteMeasure μ] (hcusp : μ sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μ = 0) :
    CircleData (sideGenMeasure μ) sidePointRe sidePointIm where
  meas_c := (continuous_const.sub (continuous_abs.comp continuous_subtype_val)).measurable
  meas_y := (continuous_sideArcHeight.comp continuous_subtype_val).measurable
  circle := Eventually.of_forall sidePoint_circle
  pos := (sideGenMeasure_ac μ).ae_le (ae_sidePointIm_pos hcusp)
  inv_sq := by
    have h := integrable_sideKWeight_div_height_sq μ hann
    unfold sideGenMeasure
    rw [integrable_withDensity_iff_integrable_smul measurable_sideKWeightNN]
    refine h.congr (Eventually.of_forall fun s => ?_)
    simp only [sidePointIm, NNReal.smul_def, coe_sideKWeightNN, smul_eq_mul]
    ring

/-! ### Annihilation in generator form -/

theorem cos_arcFreq_mul_sidePointRe (n : ℕ) (s : ArcParam) :
    Real.cos (arcFreq n * sidePointRe s) = Real.cos (arcFreq n * s) := by
  unfold sidePointRe arcFreq
  have e : 2 * Real.pi * ((n : ℝ) + 1) * (1 - |(s : ℝ)|) =
      ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) - 2 * Real.pi * ((n : ℝ) + 1) * |(s : ℝ)| := by
    push_cast; ring
  rw [e, Real.cos_nat_mul_two_pi_sub]
  rcases abs_cases (s : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, mul_neg, Real.cos_neg]

theorem sideKWeight_mul_kMoment {n : ℕ} {s : ArcParam} (hs : (s : ℝ) ≠ 0) :
    sideKWeight s * kMoment 0 (arcFreq n * sidePointIm s) = kRatio n (sideArcHeight s) := by
  have hy := sideArcHeight_pos s.2 hs
  unfold sideKWeight sidePointIm
  rw [if_neg hy.ne', kRatio_of_ne hy.ne']
  ring

/-- The side generator measure annihilates every decaying Whittaker mode. -/
theorem integral_side_whittaker_eq_zero {μ : Measure ArcParam} [IsFiniteMeasure μ]
    (hcusp : μ sideCusp = 0) (hann : ∀ n, ∫ s, sideCosMode n s ∂μ = 0) (n : ℕ) :
    ∫ p, kMoment 0 (arcFreq n * sidePointIm p) * Real.cos (arcFreq n * sidePointRe p)
      ∂(sideGenMeasure μ) = 0 := by
  rw [integral_sideGenMeasure, ← hann n]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s : ArcParam ∂μ, (s : ℝ) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hcusp
    simp only [mem_setOf_eq, not_not] at hs
    exact hs
  filter_upwards [hae] with s hs
  rw [sideCosMode_apply, cos_arcFreq_mul_sidePointRe, ← mul_assoc, sideKWeight_mul_kMoment hs]

/-- The bottom-arc measure annihilates every decaying Whittaker mode. -/
theorem integral_arc_whittaker_eq_zero {μ : Measure ArcParam}
    (hann : ∀ n, ∫ u, arcCosMode n u ∂μ = 0) (n : ℕ) :
    ∫ p, kMoment 0 (arcFreq n * arcPointIm p) * Real.cos (arcFreq n * arcPointRe p) ∂μ = 0 :=
  hann n

/-! ### Spectral comparison -/

theorem sideSpectrum_ge (τ : ℝ) {s : ArcParam} (hs : (s : ℝ) ≠ 0) :
    ∫ v, Real.cos (τ * v) * symCoshKernel (1 / 2) v ≤
      ∫ v, Real.cos (τ * v) * symCoshKernel (sidePointRe s) v := by
  have h1 : |(s : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [s.2.1], s.2.2⟩
  have hp := abs_pos.mpr hs
  have hc : |sidePointRe s| < 1 := by
    unfold sidePointRe; rw [abs_lt]; constructor <;> linarith [abs_nonneg (s : ℝ)]
  refine integral_cos_mul_symCoshKernel_le_of_abs_le hc ?_ τ
  unfold sidePointRe
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg (by linarith)]
  linarith

theorem sideSpectrum_gt (τ : ℝ) {s : ArcParam} (hs : (s : ℝ) ≠ 0) (hs2 : |(s : ℝ)| < 1 / 2) :
    ∫ v, Real.cos (τ * v) * symCoshKernel (1 / 2) v <
      ∫ v, Real.cos (τ * v) * symCoshKernel (sidePointRe s) v := by
  have hp := abs_pos.mpr hs
  have hc : |sidePointRe s| < 1 := by
    unfold sidePointRe; rw [abs_lt]; constructor <;> linarith [abs_nonneg (s : ℝ)]
  refine integral_cos_mul_symCoshKernel_lt_of_abs_lt hc ?_ τ
  unfold sidePointRe
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg (by linarith)]
  linarith

theorem arcSpectrum_le (τ : ℝ) (u : ArcParam) :
    ∫ v, Real.cos (τ * v) * symCoshKernel (arcPointRe u) v ≤
      ∫ v, Real.cos (τ * v) * symCoshKernel (1 / 2) v := by
  refine integral_cos_mul_symCoshKernel_le_of_abs_le (by norm_num) ?_ τ
  unfold arcPointRe
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact abs_le.mpr ⟨by linarith [u.2.1], u.2.2⟩

/-! ### The side measure charges the open side arcs -/

/-- The open side arcs `0 < |s| < ½`, away from the corners and the cusp. -/
def sideOpen : Set ArcParam := {s | (s : ℝ) ≠ 0 ∧ |(s : ℝ)| < 1 / 2}

theorem measurableSet_sideOpen : MeasurableSet sideOpen := by
  have h1 : MeasurableSet {s : ArcParam | (s : ℝ) ≠ 0} :=
    (measurableSet_singleton (0 : ℝ)).compl.preimage continuous_subtype_val.measurable
  have h2 : MeasurableSet {s : ArcParam | |(s : ℝ)| < 1 / 2} :=
    measurableSet_lt (continuous_abs.comp continuous_subtype_val).measurable measurable_const
  exact h1.inter h2

theorem sideCosMode_zero_of_corner {s : ArcParam} (hs : (s : ℝ) ≠ 0) (h2 : ¬ |(s : ℝ)| < 1 / 2) :
    sideCosMode 0 s = -1 := by
  have hs2 : |(s : ℝ)| = 1 / 2 :=
    le_antisymm (abs_le.mpr ⟨by linarith [s.2.1], s.2.2⟩) (not_lt.mp h2)
  have hy := sideArcHeight_pos s.2 hs
  have hK := kMoment_zero_pos_of_pos (mul_pos (arcFreq_pos 0) hy)
  rw [sideCosMode_apply, kRatio_of_ne hy.ne', div_self hK.ne', one_mul]
  have hc : arcFreq 0 = 2 * Real.pi := by unfold arcFreq; simp
  rw [hc]
  rcases abs_cases (s : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at hs2
    rw [show 2 * Real.pi * (s : ℝ) = Real.pi by rw [hs2]; ring, Real.cos_pi]
  · rw [h] at hs2
    have hs3 : (s : ℝ) = -(1 / 2) := by linarith
    rw [show 2 * Real.pi * (s : ℝ) = -Real.pi by rw [hs3]; ring, Real.cos_neg, Real.cos_pi]

/-- An annihilating probability measure on the side arcs without cusp mass charges the open side
arcs. -/
theorem sideOpen_pos {μ : Measure ArcParam} [IsProbabilityMeasure μ] (hcusp : μ sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μ = 0) : 0 < μ sideOpen := by
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  have hae : ∀ᵐ s ∂μ, sideCosMode 0 s = -1 := by
    have h1 : ∀ᵐ s : ArcParam ∂μ, s ∉ sideOpen := by
      rw [ae_iff]; simpa using h0
    have h2 : ∀ᵐ s : ArcParam ∂μ, s ∉ sideCusp := by
      rw [ae_iff]; simpa using hcusp
    filter_upwards [h1, h2] with s hs1 hs2
    have hs0 : (s : ℝ) ≠ 0 := hs2
    have hlt : ¬ |(s : ℝ)| < 1 / 2 := fun h => hs1 ⟨hs0, h⟩
    exact sideCosMode_zero_of_corner hs0 hlt
  have hint := hann 0
  rw [integral_congr_ae hae, integral_const, smul_eq_mul, probReal_univ] at hint
  norm_num at hint

theorem sideGenMeasure_sideOpen_pos {μ : Measure ArcParam} [IsProbabilityMeasure μ]
    (hcusp : μ sideCusp = 0) (hann : ∀ n, ∫ s, sideCosMode n s ∂μ = 0) :
    0 < sideGenMeasure μ sideOpen := by
  rw [pos_iff_ne_zero]
  intro h0
  unfold sideGenMeasure at h0
  rw [withDensity_apply_eq_zero measurable_sideKWeightNN.coe_nnreal_ennreal] at h0
  have hsub : sideOpen ⊆ {s : ArcParam | (sideKWeightNN s : ℝ≥0∞) ≠ 0} ∩ sideOpen := by
    intro s hs
    refine ⟨?_, hs⟩
    have hy := sideArcHeight_pos s.2 hs.1
    have hw : 0 < sideKWeight s := by
      unfold sideKWeight
      rw [if_neg hy.ne']
      exact inv_pos.mpr (kMoment_zero_pos_of_pos (mul_pos (arcFreq_pos 0) hy))
    simp only [mem_setOf_eq, ne_eq, ENNReal.coe_eq_zero]
    intro hz
    have : (sideKWeightNN s : ℝ) = 0 := by rw [hz]; rfl
    rw [coe_sideKWeightNN] at this
    linarith
  exact (sideOpen_pos hcusp hann).ne' (measure_mono_null hsub h0)

/-! ### The witness -/

/-- The two-arc line vector `h = H_S/κ_S(univ) − H_A/μ_A(univ)`. -/
def twoArcLine (μA μS : Measure ArcParam) (x : ℝ) : ℝ :=
  circleLine (sideGenMeasure μS) sidePointRe sidePointIm x / (sideGenMeasure μS).real univ -
    circleLine μA arcPointRe arcPointIm x / μA.real univ

/-- Its derivative. -/
def twoArcDeriv (μA μS : Measure ArcParam) (x : ℝ) : ℝ :=
  circleLineDeriv (sideGenMeasure μS) sidePointRe sidePointIm x / (sideGenMeasure μS).real univ -
    circleLineDeriv μA arcPointRe arcPointIm x / μA.real univ

section Witness

variable {μA μS : Measure ArcParam} [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]

omit [IsProbabilityMeasure μA] [IsProbabilityMeasure μS] in
theorem twoArcLine_neg (x : ℝ) : twoArcLine μA μS (-x) = twoArcLine μA μS x := by
  unfold twoArcLine; rw [circleLine_neg, circleLine_neg]

theorem twoArcLine_inv (hcusp : μS sideCusp = 0) (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0)
    {x : ℝ} (hx : x ≠ 0) : twoArcLine μA μS (1 / x) = |x| * twoArcLine μA μS x := by
  unfold twoArcLine
  rw [circleLine_inv (circleData_side μS hcusp hann) hx, circleLine_inv (circleData_arc μA) hx]
  ring

theorem hasDerivAt_twoArcLine (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) (x : ℝ) :
    HasDerivAt (twoArcLine μA μS) (twoArcDeriv μA μS x) x :=
  ((hasDerivAt_circleLine (circleData_side μS hcusp hann) x).div_const _).sub
    ((hasDerivAt_circleLine (circleData_arc μA) x).div_const _)

theorem integrable_twoArcDeriv (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) : Integrable (twoArcDeriv μA μS) :=
  ((integrable_circleLineDeriv (circleData_side μS hcusp hann)).div_const _).sub
    ((integrable_circleLineDeriv (circleData_arc μA)).div_const _)

/-- **Blindness at every nonzero integer frequency (sine).** -/
theorem integral_twoArcDeriv_mul_sin (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) (hannA : ∀ n, ∫ u, arcCosMode n u ∂μA = 0)
    (n : ℕ) : ∫ x, twoArcDeriv μA μS x * Real.sin (arcFreq n * x) = 0 := by
  have hS := circleData_side μS hcusp hann
  have hA := circleData_arc μA
  have hsin : Continuous fun x => Real.sin (arcFreq n * x) := by fun_prop
  have hb : ∀ x, |Real.sin (arcFreq n * x)| ≤ 1 := fun x => Real.abs_sin_le_one _
  have i1 := (integrable_circleLineDeriv_mul hS hsin hb).div_const ((sideGenMeasure μS).real univ)
  have i2 := (integrable_circleLineDeriv_mul hA hsin hb).div_const (μA.real univ)
  have e : (fun x => twoArcDeriv μA μS x * Real.sin (arcFreq n * x)) = fun x =>
      circleLineDeriv (sideGenMeasure μS) sidePointRe sidePointIm x * Real.sin (arcFreq n * x) /
        (sideGenMeasure μS).real univ -
      circleLineDeriv μA arcPointRe arcPointIm x * Real.sin (arcFreq n * x) / μA.real univ := by
    funext x; unfold twoArcDeriv; ring
  rw [e, integral_sub i1 i2, integral_div, integral_div,
    integral_circleLineDeriv_mul_sin hS (arcFreq_pos n),
    integral_circleLineDeriv_mul_sin hA (arcFreq_pos n),
    integral_side_whittaker_eq_zero hcusp hann n, integral_arc_whittaker_eq_zero hannA n]
  simp

/-- **Blindness at every nonzero integer frequency (cosine).** -/
theorem integral_twoArcDeriv_mul_cos (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) (a : ℝ) :
    ∫ x, twoArcDeriv μA μS x * Real.cos (a * x) = 0 := by
  have hS := circleData_side μS hcusp hann
  have hA := circleData_arc μA
  have hcos : Continuous fun x => Real.cos (a * x) := by fun_prop
  have hb : ∀ x, |Real.cos (a * x)| ≤ 1 := fun x => Real.abs_cos_le_one _
  have i1 := (integrable_circleLineDeriv_mul hS hcos hb).div_const ((sideGenMeasure μS).real univ)
  have i2 := (integrable_circleLineDeriv_mul hA hcos hb).div_const (μA.real univ)
  have e : (fun x => twoArcDeriv μA μS x * Real.cos (a * x)) = fun x =>
      circleLineDeriv (sideGenMeasure μS) sidePointRe sidePointIm x * Real.cos (a * x) /
        (sideGenMeasure μS).real univ -
      circleLineDeriv μA arcPointRe arcPointIm x * Real.cos (a * x) / μA.real univ := by
    funext x; unfold twoArcDeriv; ring
  rw [e, integral_sub i1 i2, integral_div, integral_div, integral_circleLineDeriv_mul_cos,
    integral_circleLineDeriv_mul_cos]
  simp

theorem sideGenMeasure_real_pos (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) : 0 < (sideGenMeasure μS).real univ := by
  rw [measureReal_def, ENNReal.toReal_pos_iff]
  exact ⟨lt_of_lt_of_le (sideGenMeasure_sideOpen_pos hcusp hann) (measure_mono (subset_univ _)),
    measure_lt_top _ _⟩

/-- **Strict positive definiteness of the two-arc profile.** -/
theorem integral_cos_mul_twoArcProfile_pos (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)) := by
  have hS := circleData_side μS hcusp hann
  have hA := circleData_arc μA
  set mS := (sideGenMeasure μS).real univ with hmS
  have hmS0 : 0 < mS := sideGenMeasure_real_pos hcusp hann
  have hmA : μA.real univ = 1 := probReal_univ
  set Sh : ℝ := ∫ v, Real.cos (τ * v) * symCoshKernel (1 / 2) v with hSh
  have i1 := (integrable_cos_mul_circleProfile hS τ).div_const mS
  have i2 := (integrable_cos_mul_circleProfile hA τ).div_const (μA.real univ)
  have e : (fun v => Real.cos (τ * v) * (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v))) =
      fun v => Real.cos (τ * v) * (Real.exp (v / 2) *
          circleLine (sideGenMeasure μS) sidePointRe sidePointIm (Real.exp v)) / mS -
        Real.cos (τ * v) * (Real.exp (v / 2) *
          circleLine μA arcPointRe arcPointIm (Real.exp v)) / μA.real univ := by
    funext v; unfold twoArcLine; ring
  rw [e, integral_sub i1 i2, integral_div, integral_div, integral_cos_mul_circleProfile hS τ,
    integral_cos_mul_circleProfile hA τ, hmA, div_one]
  -- the side average exceeds `Ŝ_{1/2}(τ)` strictly
  have hspecS := integrable_circleSpectrum hS τ
  have h0 : ∀ᵐ s : ArcParam ∂μS, (s : ℝ) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hcusp
    simp only [mem_setOf_eq, not_not] at hs
    exact hs
  have hae : ∀ᵐ p : ArcParam ∂(sideGenMeasure μS), (p : ℝ) ≠ 0 :=
    (sideGenMeasure_ac μS).ae_le h0
  have hgap : 0 < ∫ p, ((∫ v, Real.cos (τ * v) * symCoshKernel (sidePointRe p) v) - Sh)
      ∂(sideGenMeasure μS) := by
    have hint : Integrable (fun p => (∫ v, Real.cos (τ * v) * symCoshKernel (sidePointRe p) v) -
        Sh) (sideGenMeasure μS) := hspecS.sub (integrable_const Sh)
    have hnn : 0 ≤ᵐ[sideGenMeasure μS] fun p =>
        (∫ v, Real.cos (τ * v) * symCoshKernel (sidePointRe p) v) - Sh := by
      filter_upwards [hae] with p hp
      exact sub_nonneg.mpr (sideSpectrum_ge τ hp)
    refine (integral_pos_iff_support_of_nonneg_ae hnn hint).mpr ?_
    refine lt_of_lt_of_le (sideGenMeasure_sideOpen_pos hcusp hann) (measure_mono ?_)
    intro p hp
    simp only [Function.mem_support]
    exact (sub_pos.mpr (sideSpectrum_gt τ hp.1 hp.2)).ne'
  rw [integral_sub hspecS (integrable_const _), integral_const, smul_eq_mul] at hgap
  -- the bottom-arc average is at most `Ŝ_{1/2}(τ)`
  have hspecA := integrable_circleSpectrum hA τ
  have hle : ∫ p, (∫ v, Real.cos (τ * v) * symCoshKernel (arcPointRe p) v) ∂μA ≤ Sh := by
    calc ∫ p, (∫ v, Real.cos (τ * v) * symCoshKernel (arcPointRe p) v) ∂μA
        ≤ ∫ _p, Sh ∂μA := integral_mono hspecA (integrable_const _) fun p => arcSpectrum_le τ p
      _ = Sh := by rw [integral_const, probReal_univ, one_smul]
  have h1 : Sh < (∫ p, (∫ v, Real.cos (τ * v) * symCoshKernel (sidePointRe p) v)
      ∂(sideGenMeasure μS)) / mS := by
    rw [lt_div_iff₀ hmS0]; linarith
  have hsq : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr two_pos)
  have h2 := mul_lt_mul_of_pos_left (lt_of_le_of_lt hle h1) hsq
  rw [mul_div_assoc]
  linarith

end Witness

/-- **The two-arc witness.**  There is an even function `h` with `h(1/x) = |x| h(x)`, integrable
derivative orthogonal to `sin(2π(n+1)x)` and `cos(2π(n+1)x)` for every `n`, and strictly positive
definite log profile.  It is the normalized difference of the side-arc and bottom-arc Poisson
superpositions. -/
theorem exists_twoArcWitness :
    ∃ μA μS : ProbabilityMeasure ArcParam,
      (∀ x, twoArcLine μA μS (-x) = twoArcLine μA μS x) ∧
      (∀ x, x ≠ 0 → twoArcLine μA μS (1 / x) = |x| * twoArcLine μA μS x) ∧
      (∀ x, HasDerivAt (twoArcLine μA μS) (twoArcDeriv μA μS x) x) ∧
      Integrable (twoArcDeriv μA μS) ∧
      (∀ n : ℕ, ∫ x, twoArcDeriv μA μS x * Real.sin (arcFreq n * x) = 0 ∧
        ∫ x, twoArcDeriv μA μS x * Real.cos (arcFreq n * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) *
        (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)) := by
  obtain ⟨μA, hA⟩ := exists_probabilityMeasure_arc_annihilating
  obtain ⟨μS, hS, hcusp⟩ := exists_probabilityMeasure_sideArc_annihilating
  have hannS : ∀ n, ∫ s, sideCosMode n s ∂(μS : Measure ArcParam) = 0 := fun n => (hS n).1
  have hannA : ∀ n, ∫ u, arcCosMode n u ∂(μA : Measure ArcParam) = 0 := fun n => (hA n).1
  exact ⟨μA, μS, twoArcLine_neg, fun x hx => twoArcLine_inv hcusp hannS hx,
    hasDerivAt_twoArcLine hcusp hannS, integrable_twoArcDeriv hcusp hannS,
    fun n => ⟨integral_twoArcDeriv_mul_sin hcusp hannS hannA n,
      integral_twoArcDeriv_mul_cos hcusp hannS _⟩,
    integral_cos_mul_twoArcProfile_pos hcusp hannS⟩

end

end RHTower
