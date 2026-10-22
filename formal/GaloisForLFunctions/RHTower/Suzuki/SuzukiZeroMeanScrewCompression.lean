import GaloisForLFunctions.RHTower.Suzuki.SuzukiCenteredScrewApertureOperator
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Suzuki's zero-mean aperture and compressed screw operator

Suzuki's 2026 operator `G_a = P_a G P_a` acts on the codimension-one Hilbert space
`L²₀(-a,a)`.  This file constructs that literal space inside the already formalized interval
`L²`, identifies membership with vanishing Lebesgue integral, and compresses Suzuki's exact
centered screw-kernel operator by the genuine orthogonal projection.

The raw-convolution identification is deliberately kept separate: the operator below is named a
centered compression until the rank-one centering terms have been proved to vanish on both
zero-mean arguments.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Constant function `1` in the literal interval space `L²(-a,a)`. -/
def suzukiApertureIntervalOne (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 :=
  Lp.const 2 (volume : Measure (SuzukiApertureInterval a.1)) (1 : ℂ)

theorem suzukiApertureIntervalOne_coeFn (a : SuzukiPositiveAperture) :
    (suzukiApertureIntervalOne a : SuzukiApertureInterval a.1 → ℂ)
      =ᵐ[volume] fun _ => 1 :=
  Lp.coeFn_const 2 (volume : Measure (SuzukiApertureInterval a.1)) (1 : ℂ)

/-- Literal Lebesgue mean on `L²(-a,a)`.  Finite aperture makes every `L²` vector `L¹`. -/
def suzukiApertureIntervalMean (a : SuzukiPositiveAperture)
    (f : SuzukiApertureIntervalL2 a.1) : ℂ :=
  ∫ x : SuzukiApertureInterval a.1, f x ∂volume

theorem inner_suzukiApertureIntervalOne
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    inner ℂ (suzukiApertureIntervalOne a) f = suzukiApertureIntervalMean a f := by
  rw [MeasureTheory.L2.inner_def, suzukiApertureIntervalMean]
  apply integral_congr_ae
  filter_upwards [suzukiApertureIntervalOne_coeFn a] with x hx
  rw [hx]
  simp

/-- Suzuki's literal codimension-one space `L²₀(-a,a)`. -/
def SuzukiApertureZeroMean (a : SuzukiPositiveAperture) :
    Submodule ℂ (SuzukiApertureIntervalL2 a.1) :=
  (ℂ ∙ suzukiApertureIntervalOne a)ᗮ

theorem mem_suzukiApertureZeroMean_iff
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    f ∈ SuzukiApertureZeroMean a ↔ suzukiApertureIntervalMean a f = 0 := by
  rw [SuzukiApertureZeroMean,
    Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_suzukiApertureIntervalOne]

theorem suzukiApertureZeroMean_isClosed (a : SuzukiPositiveAperture) :
    IsClosed (SuzukiApertureZeroMean a : Set (SuzukiApertureIntervalL2 a.1)) := by
  simpa only [SuzukiApertureZeroMean] using
    (Submodule.isClosed_orthogonal
      (ℂ ∙ suzukiApertureIntervalOne a :
        Submodule ℂ (SuzukiApertureIntervalL2 a.1)))

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- The genuine orthogonal projection `P_a : L²(-a,a) → L²₀(-a,a)`. -/
def suzukiApertureZeroMeanProjection (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureZeroMean a :=
  (SuzukiApertureZeroMean a).orthogonalProjectionOnto

theorem suzukiApertureZeroMeanProjection_apply_of_mem
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a) :
    suzukiApertureZeroMeanProjection a (f : SuzukiApertureIntervalL2 a.1) = f := by
  exact (SuzukiApertureZeroMean a).orthogonalProjectionOnto_mem_subspace_eq_self f

/-! ## Raw convolution form and cancellation of the centering ranks -/

/-- Suzuki's raw convolution pairing before the outer mean-zero compressions. -/
def suzukiRawScrewIntervalForm (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) : ℂ :=
  ∫ t : SuzukiApertureInterval a, ∫ u : SuzukiApertureInterval a,
    suzukiScrewG ((t : ℝ) - (u : ℝ)) * f u * (starRingEnd ℂ) (g t)

/-- Suzuki's explicit screw function is continuous unconditionally. -/
theorem continuous_suzukiScrewG : Continuous suzukiScrewG := by
  unfold suzukiScrewG
  exact (Complex.continuous_ofReal.comp continuous_suzukiPsi).neg

theorem continuous_suzukiRawScrewKernel_on_aperture (a : ℝ) :
    Continuous fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      suzukiScrewG ((p.1 : ℝ) - (p.2 : ℝ)) := by
  exact continuous_suzukiScrewG.comp
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd))

theorem exists_suzukiRawScrewKernel_norm_bound (a : ℝ) :
    ∃ C : ℝ, ∀ t u : SuzukiApertureInterval a,
      ‖suzukiScrewG ((t : ℝ) - (u : ℝ))‖ ≤ C := by
  have hcont : Continuous fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      ‖suzukiScrewG ((p.1 : ℝ) - (p.2 : ℝ))‖ :=
    (continuous_suzukiRawScrewKernel_on_aperture a).norm
  obtain ⟨C, hC⟩ := (isCompact_univ.bddAbove_image hcont.continuousOn)
  refine ⟨C, fun t u => hC ?_⟩
  exact ⟨(t, u), Set.mem_univ _, rfl⟩

theorem integrable_bounded_aperture_kernel_pair
    {a C : ℝ}
    {K : SuzukiApertureInterval a × SuzukiApertureInterval a → ℂ}
    (hK : AEStronglyMeasurable K
      ((volume : Measure (SuzukiApertureInterval a)).prod volume))
    (hC : ∀ p, ‖K p‖ ≤ C)
    (f g : SuzukiApertureIntervalL2 a) :
    Integrable (fun p => K p * f p.2 * (starRingEnd ℂ) (g p.1))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) := by
  have hf : Integrable (fun u : SuzukiApertureInterval a => f u) :=
    (Lp.memLp f).integrable (by norm_num)
  have hg : Integrable (fun t : SuzukiApertureInterval a => (starRingEnd ℂ) (g t)) :=
    ((Lp.memLp g).integrable (by norm_num)).norm.mono'
      (Complex.continuous_conj.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable g))
      (Filter.Eventually.of_forall fun t => by rw [RCLike.norm_conj])
  have hprod : Integrable (fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      (starRingEnd ℂ) (g p.1) * f p.2)
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) :=
    hg.mul_prod hf
  have hb := hprod.bdd_mul (c := C) hK (Filter.Eventually.of_forall hC)
  exact hb.congr (Filter.Eventually.of_forall fun p => by ring)

theorem integrable_suzukiRawScrewKernel_pair (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) :
    Integrable (fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      suzukiScrewG ((p.1 : ℝ) - (p.2 : ℝ)) * f p.2 *
        (starRingEnd ℂ) (g p.1))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) := by
  obtain ⟨C, hC⟩ := exists_suzukiRawScrewKernel_norm_bound a
  exact integrable_bounded_aperture_kernel_pair
    (continuous_suzukiRawScrewKernel_on_aperture a).aestronglyMeasurable
    (fun p => hC p.1 p.2) f g

theorem integrable_suzukiCenteredScrewKernel_pair (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) :
    Integrable (fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      suzukiScrewKernel (p.1 : ℝ) (p.2 : ℝ) * f p.2 *
        (starRingEnd ℂ) (g p.1))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) := by
  obtain ⟨C, hC⟩ := exists_suzukiScrewKernel_norm_bound a
  exact integrable_bounded_aperture_kernel_pair
    (continuous_suzukiScrewKernel_on_aperture a).aestronglyMeasurable
    (fun p => hC p.1 p.2) f g

theorem integral_conj_suzukiAperture_eq_zero
    (a : SuzukiPositiveAperture) (g : SuzukiApertureZeroMean a) :
    (∫ t : SuzukiApertureInterval a.1,
      (starRingEnd ℂ) ((g : SuzukiApertureIntervalL2 a.1) t) ∂volume) = 0 := by
  calc
    (∫ t : SuzukiApertureInterval a.1,
        (starRingEnd ℂ) ((g : SuzukiApertureIntervalL2 a.1) t) ∂volume) =
      (starRingEnd ℂ) (∫ t : SuzukiApertureInterval a.1,
        (g : SuzukiApertureIntervalL2 a.1) t ∂volume) := integral_conj
    _ = 0 := by
      have hmean := (mem_suzukiApertureZeroMean_iff a _).mp g.property
      change (∫ t : SuzukiApertureInterval a.1,
        (g : SuzukiApertureIntervalL2 a.1) t ∂volume) = 0 at hmean
      rw [hmean]
      simp

/-- The centered kernel and raw convolution have exactly the same compression to
`L²₀(-a,a)`: all three centering ranks vanish, with every Fubini and integrability obligation
discharged. -/
theorem suzukiScrewIntervalForm_eq_raw_of_zeroMean
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureZeroMean a) :
    suzukiScrewIntervalForm a.1
        (f : SuzukiApertureIntervalL2 a.1)
        (g : SuzukiApertureIntervalL2 a.1) =
      suzukiRawScrewIntervalForm a.1
        (f : SuzukiApertureIntervalL2 a.1)
        (g : SuzukiApertureIntervalL2 a.1) := by
  let F : SuzukiApertureIntervalL2 a.1 := f
  let H : SuzukiApertureIntervalL2 a.1 := g
  let μ : Measure (SuzukiApertureInterval a.1) := volume
  let A : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 → ℂ := fun p =>
    suzukiScrewG ((p.1 : ℝ) - (p.2 : ℝ)) * F p.2 * (starRingEnd ℂ) (H p.1)
  let B : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 → ℂ := fun p =>
    suzukiScrewG (p.1 : ℝ) * F p.2 * (starRingEnd ℂ) (H p.1)
  let C : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 → ℂ := fun p =>
    suzukiScrewG (-(p.2 : ℝ)) * F p.2 * (starRingEnd ℂ) (H p.1)
  have hFint : Integrable (fun u : SuzukiApertureInterval a.1 => F u) :=
    (Lp.memLp F).integrable (by norm_num)
  have hHint : Integrable (fun t : SuzukiApertureInterval a.1 =>
      (starRingEnd ℂ) (H t)) :=
    ((Lp.memLp H).integrable (by norm_num)).norm.mono'
      (Complex.continuous_conj.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable H))
      (Filter.Eventually.of_forall fun t => by rw [RCLike.norm_conj])
  obtain ⟨M, hM⟩ := exists_suzukiRawScrewKernel_norm_bound a.1
  let z : SuzukiApertureInterval a.1 := ⟨0, by constructor <;> linarith [a.2]⟩
  have hGt : Integrable (fun t : SuzukiApertureInterval a.1 =>
      suzukiScrewG (t : ℝ) * (starRingEnd ℂ) (H t)) := by
    exact hHint.bdd_mul
      (continuous_suzukiScrewG.comp continuous_subtype_val).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        simpa only [z, sub_zero] using hM t z)
  have hGu : Integrable (fun u : SuzukiApertureInterval a.1 =>
      suzukiScrewG (-(u : ℝ)) * F u) := by
    exact hFint.bdd_mul
      (continuous_suzukiScrewG.comp
        continuous_subtype_val.neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        have hz := hM z u
        simpa only [z, zero_sub] using hz)
  have hA : Integrable A (μ.prod μ) := by
    simpa only [A, F, H, μ] using
      integrable_suzukiRawScrewKernel_pair a.1 F H
  have hK : Integrable (fun p : SuzukiApertureInterval a.1 ×
      SuzukiApertureInterval a.1 =>
        suzukiScrewKernel (p.1 : ℝ) (p.2 : ℝ) * F p.2 *
          (starRingEnd ℂ) (H p.1)) (μ.prod μ) := by
    simpa only [F, H, μ] using
      integrable_suzukiCenteredScrewKernel_pair a.1 F H
  have hB : Integrable B (μ.prod μ) := by
    have hp := hGt.mul_prod hFint
    exact hp.congr (Filter.Eventually.of_forall fun p => by
      simp only [B]
      ring)
  have hC : Integrable C (μ.prod μ) := by
    have hp := hHint.mul_prod hGu
    exact hp.congr (Filter.Eventually.of_forall fun p => by
      simp only [C]
      ring)
  have hmeanF : ∫ u : SuzukiApertureInterval a.1, F u ∂volume = 0 := by
    exact (mem_suzukiApertureZeroMean_iff a _).mp f.property
  have hmeanH : ∫ t : SuzukiApertureInterval a.1,
      (starRingEnd ℂ) (H t) ∂volume = 0 := by
    exact integral_conj_suzukiAperture_eq_zero a g
  rw [suzukiScrewIntervalForm, suzukiRawScrewIntervalForm]
  change (∫ t, ∫ u,
      suzukiScrewKernel (t : ℝ) (u : ℝ) * F u *
        (starRingEnd ℂ) (H t) ∂μ ∂μ) =
    ∫ t, ∫ u, A (t, u) ∂μ ∂μ
  rw [integral_integral hK, integral_integral hA]
  calc
    (∫ p, suzukiScrewKernel (p.1 : ℝ) (p.2 : ℝ) * F p.2 *
        (starRingEnd ℂ) (H p.1) ∂(μ.prod μ)) =
      ∫ p, A p - B p - C p ∂(μ.prod μ) := by
        apply integral_congr_ae
        filter_upwards with p
        simp only [A, B, C, suzukiScrewKernel, suzukiScrewG_zero]
        ring
    _ = (∫ p, A p ∂(μ.prod μ)) -
        (∫ p, B p ∂(μ.prod μ)) -
        (∫ p, C p ∂(μ.prod μ)) := by
      change (∫ p, ((A - B) - C) p ∂(μ.prod μ)) = _
      calc
        (∫ p, ((A - B) - C) p ∂(μ.prod μ)) =
            (∫ p, (A - B) p ∂(μ.prod μ)) -
              ∫ p, C p ∂(μ.prod μ) := by
          simpa only [Pi.sub_apply] using integral_sub (hA.sub hB) hC
        _ = _ := by
          rw [show (∫ p, (A - B) p ∂(μ.prod μ)) =
              (∫ p, A p ∂(μ.prod μ)) -
                ∫ p, B p ∂(μ.prod μ) by
            simpa only [Pi.sub_apply] using integral_sub hA hB]
    _ = ∫ p, A p ∂(μ.prod μ) := by
      have hBzero : (∫ p, B p ∂(μ.prod μ)) = 0 := by
        calc
          (∫ p, B p ∂(μ.prod μ)) =
              ∫ p, (suzukiScrewG (p.1 : ℝ) *
                (starRingEnd ℂ) (H p.1)) * F p.2 ∂(μ.prod μ) := by
            apply integral_congr_ae
            filter_upwards with p
            simp only [B]
            ring
          _ = (∫ t : SuzukiApertureInterval a.1,
                suzukiScrewG (t : ℝ) * (starRingEnd ℂ) (H t) ∂μ) *
              ∫ u : SuzukiApertureInterval a.1, F u ∂μ :=
            integral_prod_mul (μ := μ) (ν := μ)
              (fun t : SuzukiApertureInterval a.1 =>
                suzukiScrewG (t : ℝ) * (starRingEnd ℂ) (H t))
              (fun u : SuzukiApertureInterval a.1 => F u)
          _ = 0 := by
            change _ * (∫ u : SuzukiApertureInterval a.1, F u ∂volume) = 0
            rw [hmeanF, mul_zero]
      have hCzero : (∫ p, C p ∂(μ.prod μ)) = 0 := by
        calc
          (∫ p, C p ∂(μ.prod μ)) =
              ∫ p, (starRingEnd ℂ) (H p.1) *
                (suzukiScrewG (-(p.2 : ℝ)) * F p.2) ∂(μ.prod μ) := by
            apply integral_congr_ae
            filter_upwards with p
            simp only [C]
            ring
          _ = (∫ t : SuzukiApertureInterval a.1,
                (starRingEnd ℂ) (H t) ∂μ) *
              ∫ u : SuzukiApertureInterval a.1,
                suzukiScrewG (-(u : ℝ)) * F u ∂μ :=
            integral_prod_mul (μ := μ) (ν := μ)
              (fun t : SuzukiApertureInterval a.1 =>
                (starRingEnd ℂ) (H t))
              (fun u : SuzukiApertureInterval a.1 =>
                suzukiScrewG (-(u : ℝ)) * F u)
          _ = 0 := by
            change (∫ t : SuzukiApertureInterval a.1,
              (starRingEnd ℂ) (H t) ∂volume) * _ = 0
            rw [hmeanH, zero_mul]
      rw [hBzero, hCzero, sub_zero, sub_zero]

/-- Orthogonal compression of Suzuki's literal centered screw-kernel operator to
`L²₀(-a,a)`. -/
def suzukiCenteredScrewZeroMeanOperator (a : SuzukiPositiveAperture) :
    SuzukiApertureZeroMean a →L[ℂ] SuzukiApertureZeroMean a :=
  suzukiApertureZeroMeanProjection a ∘L
    suzukiScrewIntegralOperator a.1 ∘L (SuzukiApertureZeroMean a).subtypeL

/-- Exact pairing of the compressed operator with Suzuki's literal centered kernel form. -/
theorem inner_suzukiCenteredScrewZeroMeanOperator_eq_intervalForm
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureZeroMean a) :
    inner ℂ g (suzukiCenteredScrewZeroMeanOperator a f) =
      suzukiScrewIntervalForm a.1
        (f : SuzukiApertureIntervalL2 a.1)
        (g : SuzukiApertureIntervalL2 a.1) := by
  change inner ℂ g ((SuzukiApertureZeroMean a).orthogonalProjectionOnto
      (suzukiScrewIntegralOperator a.1
        (f : SuzukiApertureIntervalL2 a.1))) = _
  rw [(SuzukiApertureZeroMean a).inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact inner_suzukiScrewIntegralOperator_eq_intervalForm_pair a.2.le _ _

/-- **Suzuki's 2026 operator `G_a=P_aGP_a`.**  The definition uses the already constructed
bounded centered-kernel operator; `inner_suzukiScrewZeroMeanOperator_eq_raw` below proves that its
pairing is the literal raw convolution pairing on `L²₀(-a,a)`, so this is not an abstract proxy. -/
def suzukiScrewZeroMeanOperator (a : SuzukiPositiveAperture) :
    SuzukiApertureZeroMean a →L[ℂ] SuzukiApertureZeroMean a :=
  suzukiCenteredScrewZeroMeanOperator a

/-- Exact raw-convolution realization of Suzuki's compressed operator `G_a`. -/
theorem inner_suzukiScrewZeroMeanOperator_eq_raw
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureZeroMean a) :
    inner ℂ g (suzukiScrewZeroMeanOperator a f) =
      suzukiRawScrewIntervalForm a.1
        (f : SuzukiApertureIntervalL2 a.1)
        (g : SuzukiApertureIntervalL2 a.1) := by
  rw [suzukiScrewZeroMeanOperator,
    inner_suzukiCenteredScrewZeroMeanOperator_eq_intervalForm,
    suzukiScrewIntervalForm_eq_raw_of_zeroMean]

/-- Unconditional self-adjointness of the zero-mean centered compression. -/
theorem suzukiCenteredScrewZeroMeanOperator_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (suzukiCenteredScrewZeroMeanOperator a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change inner ℂ ((SuzukiApertureZeroMean a).orthogonalProjectionOnto
      (suzukiScrewIntegralOperator a.1
        (f : SuzukiApertureIntervalL2 a.1))) g =
    inner ℂ f ((SuzukiApertureZeroMean a).orthogonalProjectionOnto
      (suzukiScrewIntegralOperator a.1
        (g : SuzukiApertureIntervalL2 a.1)))
  rw [(SuzukiApertureZeroMean a).inner_orthogonalProjectionOnto_eq_of_mem_right,
    (SuzukiApertureZeroMean a).inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact suzukiScrewIntegralOperator_isSymmetric a.2.le
    (f : SuzukiApertureIntervalL2 a.1) (g : SuzukiApertureIntervalL2 a.1)

/-- Unconditional self-adjointness of Suzuki's literal compressed raw-convolution operator `G_a`. -/
theorem suzukiScrewZeroMeanOperator_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (suzukiScrewZeroMeanOperator a) := by
  exact suzukiCenteredScrewZeroMeanOperator_isSelfAdjoint a

/-- Suzuki's compressed raw-convolution operator `G_a` is compact.  This is inherited from the
trace-class centered kernel before orthogonal compression. -/
theorem suzukiScrewZeroMeanOperator_isCompact
    (a : SuzukiPositiveAperture) :
    IsCompactOperator (suzukiScrewZeroMeanOperator a) := by
  have hc : IsCompactOperator (suzukiScrewIntegralOperator a.1) :=
    (_root_.RHTower.IsTraceClass.memSchattenClass_one
      (suzukiScrewIntegralOperator_isTraceClass a.1)).isCompactOperator one_pos
  exact (hc.comp_clm (SuzukiApertureZeroMean a).subtypeL).clm_comp
    (suzukiApertureZeroMeanProjection a)

end RHTower

end
