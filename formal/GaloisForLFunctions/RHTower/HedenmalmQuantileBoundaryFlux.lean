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

private theorem inv_two_sqrt_three : (1 / (2 * Real.sqrt 3) : ℝ) = Real.sqrt 3 / 6 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hmul : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  linear_combination (-2 : ℝ) * hmul

/-- The `+1/√12` eigenvector of the boundary operator. -/
def pinnedFluxPositive : H := pinnedOne - ((2 * Real.sqrt 3 : ℝ) : ℂ) • pinnedCenter

/-- The `-1/√12` eigenvector of the boundary operator. -/
def pinnedFluxNegative : H := pinnedOne + ((2 * Real.sqrt 3 : ℝ) : ℂ) • pinnedCenter

/-- **The positive boundary eigenvalue is `1/√12 = 1/(2√3)`.** -/
theorem pinnedBoundaryCLM_pinnedFluxPositive :
    pinnedBoundaryCLM pinnedFluxPositive
      = ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) • pinnedFluxPositive := by
  have hcoef : ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) * ((2 * Real.sqrt 3 : ℝ) : ℂ) = 1 := by
    rw [inv_two_sqrt_three]
    push_cast
    linear_combination (1 / 3 : ℂ) * sqrt_three_sq
  have hscale : ((2 * Real.sqrt 3 : ℝ) : ℂ) * -(1 / 12 : ℂ)
      = -((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) := by
    rw [inv_two_sqrt_three]
    push_cast
    ring
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
    rw [inv_two_sqrt_three]
    push_cast
    linear_combination (-1 / 3 : ℂ) * sqrt_three_sq
  have hscale : ((2 * Real.sqrt 3 : ℝ) : ℂ) * -(1 / 12 : ℂ)
      = ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) := by
    rw [inv_two_sqrt_three]
    push_cast
    ring
  have key : ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) • pinnedFluxNegative
      = ((-(1 / (2 * Real.sqrt 3)) : ℝ) : ℂ) • pinnedOne + (-1 : ℂ) • pinnedCenter := by
    rw [pinnedFluxNegative, smul_add, smul_smul, hcoef]
  rw [key, pinnedFluxNegative, map_add, map_smul, pinnedBoundaryCLM_pinnedOne_eq_neg_center,
    pinnedBoundaryCLM_pinnedCenter, smul_smul, hscale]
  module

/-! ### The spectral flux law on a root mode -/

namespace HedenmalmQuantile

variable (S : PositiveDensitySource)

/-- A quantile root mode at spectral value `lam`: the pointwise relation `i q (C g) = lam g`. -/
def IsQuantileRootMode (lam : ℂ) (g : H) : Prop :=
  (fun t => Complex.I * ((quantileSpeed S t : ℝ) : ℂ) * (pinnedVolterra g) t)
    =ᵐ[unitIntervalMeasure] fun t => lam * g t

theorem pinnedVolterra_ae_of_rootMode {lam : ℂ} {g : H}
    (h : IsQuantileRootMode S lam g) :
    (fun t => (pinnedVolterra g) t)
      =ᵐ[unitIntervalMeasure] fun t => (-Complex.I * lam) * (metricSymbol S t * g t) := by
  filter_upwards [h] with t ht
  have hq : (0 : ℝ) < quantileSpeed S t := quantileSpeed_pos S t
  have hqc : ((quantileSpeed S t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsym : metricSymbol S t = ((quantileSpeed S t : ℝ) : ℂ)⁻¹ := by
    rw [metricSymbol_eq_inv_quantileSpeed]
    push_cast
    ring
  rw [hsym]
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hX : (pinnedVolterra g) t
      = (Complex.I * ((quantileSpeed S t : ℝ) : ℂ))⁻¹ * (lam * g t) := by
    rw [← ht]
    field_simp
  rw [hX, mul_inv, Complex.inv_I]
  ring

/-- The `C`-pairing of a root mode is a scalar multiple of the metric pairing. -/
theorem inner_pinnedVolterra_rootMode {lam : ℂ} {g : H}
    (h : IsQuantileRootMode S lam g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    (inner ℂ (pinnedVolterra g) g : ℂ)
      = (starRingEnd ℂ) (-Complex.I * lam) * inner ℂ (metricOperator S hC0 hC g) g := by
  rw [inner_lp_eq, inner_lp_eq]
  have hcongr : (fun t => (starRingEnd ℂ) ((pinnedVolterra g) t) * g t)
      =ᵐ[unitIntervalMeasure] fun t => (starRingEnd ℂ) (-Complex.I * lam) *
        ((starRingEnd ℂ) ((metricOperator S hC0 hC g) t) * g t) := by
    filter_upwards [pinnedVolterra_ae_of_rootMode S h, metricOperator_coeFn S hC0 hC g]
      with t h1 h2
    rw [h1, h2, map_mul]
    ring
  rw [integral_congr_ae hcongr, MeasureTheory.integral_const_mul]

/-- Cross-polarized `C`-pairing of a root mode against an arbitrary second vector.  Unlike the
diagonal specialization, this retains the complete complex source metric pairing. -/
theorem inner_pinnedVolterra_rootMode_pair {lam : ℂ} {g h : H}
    (hg : IsQuantileRootMode S lam g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    (inner ℂ (pinnedVolterra g) h : ℂ) =
      (starRingEnd ℂ) (-Complex.I * lam) *
        inner ℂ (metricOperator S hC0 hC g) h := by
  rw [inner_lp_eq, inner_lp_eq]
  have hcongr :
      (fun t => (starRingEnd ℂ) ((pinnedVolterra g) t) * h t)
        =ᵐ[unitIntervalMeasure]
      fun t => (starRingEnd ℂ) (-Complex.I * lam) *
        ((starRingEnd ℂ) ((metricOperator S hC0 hC g) t) * h t) := by
    filter_upwards [pinnedVolterra_ae_of_rootMode S hg,
      metricOperator_coeFn S hC0 hC g] with t h1 h2
    rw [h1, h2, map_mul]
    ring
  rw [integral_congr_ae hcongr, MeasureTheory.integral_const_mul]

/-- **Cross-polarized spectral Green law.**  For two generalized root modes, the universal
rank-two boundary pairing is the canonical source-metric pairing multiplied by
`conj(-iλ) - iμ`.  Thus line-conjugate spectral parameters are boundary-orthogonal, whereas
ordinary-conjugate parameters are not; this is the exact obstruction to a rank-two inertia proof
of critical-line rigidity. -/
theorem inner_pinnedBoundaryCLM_rootMode_pair
    {lam mu : ℂ} {g h : H}
    (hg : IsQuantileRootMode S lam g)
    (hh : IsQuantileRootMode S mu h)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    (inner ℂ (pinnedBoundaryCLM g) h : ℂ) =
      ((starRingEnd ℂ) (-Complex.I * lam) + (-Complex.I * mu)) *
        inner ℂ (metricOperator S hC0 hC g) h := by
  have hleft := inner_pinnedVolterra_rootMode_pair S hg hC0 hC (h := h)
  have hright0 := inner_pinnedVolterra_rootMode_pair S hh hC0 hC (h := g)
  have hright :
      (inner ℂ g (pinnedVolterra h) : ℂ) =
        (-Complex.I * mu) * inner ℂ (metricOperator S hC0 hC g) h := by
    calc
      (inner ℂ g (pinnedVolterra h) : ℂ) =
          (starRingEnd ℂ) (inner ℂ (pinnedVolterra h) g : ℂ) := by
            rw [inner_conj_symm]
      _ = (starRingEnd ℂ)
          ((starRingEnd ℂ) (-Complex.I * mu) *
            inner ℂ (metricOperator S hC0 hC h) g) := by rw [hright0]
      _ = (-Complex.I * mu) *
          inner ℂ g (metricOperator S hC0 hC h) := by
            rw [map_mul, Complex.conj_conj, inner_conj_symm]
      _ = (-Complex.I * mu) *
          inner ℂ (metricOperator S hC0 hC g) h := by
            rw [metricOperator_inner]
  have hadj :
      (inner ℂ (pinnedVolterraAdjointCLM g) h : ℂ) =
        inner ℂ g (pinnedVolterra h) := by
    rw [pinnedVolterraAdjointCLM_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hclm : pinnedVolterraCLM g = pinnedVolterra g := rfl
  rw [pinnedBoundaryCLM, add_apply, inner_add_left, hadj, hclm, hleft, hright]
  ring

/-- **The spectral flux law.**  On a quantile root mode the universal boundary form is twice the
imaginary part of the spectral value times the canonical metric form. -/
theorem inner_pinnedBoundaryCLM_rootMode {lam : ℂ} {g : H}
    (h : IsQuantileRootMode S lam g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    (inner ℂ (pinnedBoundaryCLM g) g : ℂ)
      = ((2 * lam.im : ℝ) : ℂ) * inner ℂ (metricOperator S hC0 hC g) g := by
  have hAreal : (starRingEnd ℂ) (inner ℂ (metricOperator S hC0 hC g) g : ℂ)
      = inner ℂ (metricOperator S hC0 hC g) g := by
    rw [inner_conj_symm, metricOperator_inner]
  have hC1 := inner_pinnedVolterra_rootMode S h hC0 hC
  have hsplit : (inner ℂ (pinnedBoundaryCLM g) g : ℂ)
      = inner ℂ (pinnedVolterra g) g + (starRingEnd ℂ) (inner ℂ (pinnedVolterra g) g) := by
    have hadj : (inner ℂ (pinnedVolterraAdjointCLM g) g : ℂ)
        = (starRingEnd ℂ) (inner ℂ (pinnedVolterra g) g) := by
      rw [pinnedVolterraAdjointCLM_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
        ← inner_conj_symm]
      rfl
    rw [pinnedBoundaryCLM, add_apply, inner_add_left, hadj]
    rfl
  have hre : (starRingEnd ℂ) (-Complex.I * lam) + (-Complex.I * lam)
      = ((2 * lam.im : ℝ) : ℂ) := by
    rw [add_comm, Complex.add_conj]
    norm_num
  rw [hsplit, hC1,
    show (starRingEnd ℂ) ((starRingEnd ℂ) (-Complex.I * lam) *
        (inner ℂ (metricOperator S hC0 hC g) g : ℂ))
        = (-Complex.I * lam) * (inner ℂ (metricOperator S hC0 hC g) g : ℂ) by
      rw [map_mul, hAreal, Complex.conj_conj],
    ← add_mul, hre]

end HedenmalmQuantile

end

end RHTower
