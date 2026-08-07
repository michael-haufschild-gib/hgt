import GaloisForLFunctions.RHTower.HedenmalmQuantileMetric

/-!
# The universal rank-two boundary flux

The pinned boundary operator `R₂ = C† + C` has kernel `1-t-u`.  Its quadratic form is the
hyperbolic boundary pairing of the two lowest moments

`m(g) = ∫₀¹ g`,  `c(g) = ∫₀¹ (t - 1/2) g`,

namely `⟪R₂ g, g⟫ = -2 Re(c(g) conj m(g))`, equivalently the difference of the squared incoming and
outgoing boundary amplitudes `(m ∓ c)/√2`.  Its kernel is exactly the codimension-two moment space,
and its two nonzero eigenvalues are `± 1/√12`.

Evaluated on a quantile root mode `i q (C g) = λ g` the pairing becomes the spectral flux law

`⟪R₂ g, g⟫ = 2 Im(λ) ⟪G g, g⟫`,

so a nonreal spectral coordinate is exactly a nonzero rank-two boundary flux.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ### The boundary quadratic form -/

/-- The centered first moment `c(g) = ∫₀¹ (t - 1/2) g`. -/
def pinnedCentered (g : H) : ℂ := pinnedFirstMoment g - (1 / 2 : ℂ) * pinnedMean g

/-- The incoming boundary amplitude `(m - c)/√2`. -/
def pinnedInAmplitude (g : H) : ℂ :=
  (pinnedMean g - pinnedCentered g) / ((Real.sqrt 2 : ℝ) : ℂ)

/-- The outgoing boundary amplitude `(m + c)/√2`. -/
def pinnedOutAmplitude (g : H) : ℂ :=
  (pinnedMean g + pinnedCentered g) / ((Real.sqrt 2 : ℝ) : ℂ)

theorem integral_conj_pinnedBoundaryFun (g : H) :
    ∫ t : ℝ, (starRingEnd ℂ) (pinnedBoundaryFun g t) * g t ∂unitIntervalMeasure
      = (starRingEnd ℂ) (pinnedMean g) * pinnedMean g
        - (starRingEnd ℂ) (pinnedMean g) * pinnedFirstMoment g
        - (starRingEnd ℂ) (pinnedFirstMoment g) * pinnedMean g := by
  have h1 : Integrable (fun t : ℝ => (starRingEnd ℂ) (pinnedMean g) * g t) unitIntervalMeasure :=
    (integrable_coe g).const_mul _
  have h2 : Integrable
      (fun t : ℝ => (starRingEnd ℂ) (pinnedMean g) * (((t : ℝ) : ℂ) * g t))
      unitIntervalMeasure := (integrable_coordinate_mul g).const_mul _
  have h3 : Integrable
      (fun t : ℝ => (starRingEnd ℂ) (pinnedFirstMoment g) * g t) unitIntervalMeasure :=
    (integrable_coe g).const_mul _
  have hrw : ∫ t : ℝ, (starRingEnd ℂ) (pinnedBoundaryFun g t) * g t ∂unitIntervalMeasure
      = ∫ t : ℝ, ((starRingEnd ℂ) (pinnedMean g) * g t
          - (starRingEnd ℂ) (pinnedMean g) * (((t : ℝ) : ℂ) * g t)
          - (starRingEnd ℂ) (pinnedFirstMoment g) * g t) ∂unitIntervalMeasure := by
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [pinnedBoundaryFun, map_sub, map_mul, map_sub, map_one, Complex.conj_ofReal]
    ring
  have h12 : Integrable (fun t : ℝ => (starRingEnd ℂ) (pinnedMean g) * g t
      - (starRingEnd ℂ) (pinnedMean g) * (((t : ℝ) : ℂ) * g t)) unitIntervalMeasure := h1.sub h2
  rw [hrw, MeasureTheory.integral_sub h12 h3, MeasureTheory.integral_sub h1 h2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  rfl

/-- **The boundary quadratic form is the hyperbolic pairing of the two lowest moments.** -/
theorem inner_pinnedBoundaryCLM_eq (g : H) :
    (inner ℂ (pinnedBoundaryCLM g) g : ℂ)
      = -((starRingEnd ℂ) (pinnedMean g) * pinnedCentered g
        + (starRingEnd ℂ) (pinnedCentered g) * pinnedMean g) := by
  rw [inner_lp_eq]
  have hcongr : (fun t => (starRingEnd ℂ) ((pinnedBoundaryCLM g) t) * g t)
      =ᵐ[unitIntervalMeasure] fun t => (starRingEnd ℂ) (pinnedBoundaryFun g t) * g t := by
    filter_upwards [pinnedBoundaryCLM_coeFn g] with t ht
    rw [ht]
  rw [integral_congr_ae hcongr, integral_conj_pinnedBoundaryFun, pinnedCentered]
  simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat]
  ring

/-- **The boundary quadratic form is the difference of the two boundary intensities.** -/
theorem inner_pinnedBoundaryCLM_eq_amplitudes (g : H) :
    (inner ℂ (pinnedBoundaryCLM g) g : ℂ)
      = ((‖pinnedInAmplitude g‖ : ℂ) ^ 2 - (‖pinnedOutAmplitude g‖ : ℂ) ^ 2) := by
  have hsq2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast h.ne'
  have hnorm : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = (starRingEnd ℂ) z * z := by
    intro z
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    exact (Complex.normSq_eq_norm_sq z).symm
  rw [inner_pinnedBoundaryCLM_eq, hnorm, hnorm, pinnedInAmplitude, pinnedOutAmplitude,
    map_div₀, map_div₀, map_sub, map_add, Complex.conj_ofReal]
  field_simp
  linear_combination (-((starRingEnd ℂ) (pinnedMean g) * pinnedCentered g
      + (starRingEnd ℂ) (pinnedCentered g) * pinnedMean g)) * hsq2

/-! ### The exact kernel and the two nonzero eigenvalues -/

/-- **The kernel of the boundary operator is the codimension-two moment space.** -/
theorem pinnedBoundaryCLM_eq_zero_iff (g : H) :
    pinnedBoundaryCLM g = 0 ↔ pinnedMean g = 0 ∧ pinnedFirstMoment g = 0 := by
  constructor
  · intro h
    have hcomb := pinnedBoundaryCLM_eq_affine_combination g
    rw [h] at hcomb
    have hzero : (pinnedMean g - pinnedFirstMoment g) • pinnedOne
        + (-pinnedMean g) • pinnedCoordinate = 0 := by
      rw [neg_smul, ← sub_eq_add_neg]
      exact hcomb.symm
    obtain ⟨ha, hb⟩ := (LinearIndependent.pair_iff.mp pinnedOne_coordinate_linearIndependent)
      (pinnedMean g - pinnedFirstMoment g) (-pinnedMean g) hzero
    have hm : pinnedMean g = 0 := by
      simpa using hb
    refine ⟨hm, ?_⟩
    rw [hm] at ha
    simpa using ha.symm
  · rintro ⟨hm, hfm⟩
    rw [pinnedBoundaryCLM_eq_affine_combination, hm, hfm]
    module

private theorem sqrt_three_sq : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = (3 : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

private theorem sqrt_three_ne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast h.ne'

/-- The `+1/√12` eigenvector of the boundary operator. -/
def pinnedFluxPositive : H := pinnedOne - ((2 * Real.sqrt 3 : ℝ) : ℂ) • pinnedCenter

/-- The `-1/√12` eigenvector of the boundary operator. -/
def pinnedFluxNegative : H := pinnedOne + ((2 * Real.sqrt 3 : ℝ) : ℂ) • pinnedCenter

/-- **The positive boundary eigenvalue is `1/√12 = 1/(2√3)`.** -/
theorem pinnedBoundaryCLM_pinnedFluxPositive :
    pinnedBoundaryCLM pinnedFluxPositive
      = ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) • pinnedFluxPositive := by
  have hcoef : ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) * ((2 * Real.sqrt 3 : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [sqrt_three_ne]
  have hscale : ((2 * Real.sqrt 3 : ℝ) : ℂ) * -(1 / 12 : ℂ)
      = -((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) := by
    push_cast
    field_simp [sqrt_three_ne]
    linear_combination (2 : ℂ) * sqrt_three_sq
  have key : ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) • pinnedFluxPositive
      = ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) • pinnedOne - pinnedCenter := by
    rw [pinnedFluxPositive, smul_sub, smul_smul, hcoef, one_smul]
  rw [key, pinnedFluxPositive, map_sub, map_smul, pinnedBoundaryCLM_pinnedOne_eq_neg_center,
    pinnedBoundaryCLM_pinnedCenter, smul_smul, hscale]
  module

/-- **The negative boundary eigenvalue is `-1/√12 = -1/(2√3)`.** -/
theorem pinnedBoundaryCLM_pinnedFluxNegative :
    pinnedBoundaryCLM pinnedFluxNegative
      = ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) • pinnedFluxNegative := by
  have hcoef : ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) * ((2 * Real.sqrt 3 : ℝ) : ℂ) = -1 := by
    push_cast
    field_simp [sqrt_three_ne]
  have hscale : ((2 * Real.sqrt 3 : ℝ) : ℂ) * -(1 / 12 : ℂ)
      = ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) := by
    push_cast
    field_simp [sqrt_three_ne]
    linear_combination (-10 : ℂ) * sqrt_three_sq
  have key : ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) • pinnedFluxNegative
      = ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) • pinnedOne + (-1 : ℂ) • pinnedCenter := by
    rw [pinnedFluxNegative, smul_add, smul_smul, hcoef]
  rw [key, pinnedFluxNegative, map_add, map_smul, pinnedBoundaryCLM_pinnedOne_eq_neg_center,
    pinnedBoundaryCLM_pinnedCenter, smul_smul, hscale]
  module

end

end RHTower
