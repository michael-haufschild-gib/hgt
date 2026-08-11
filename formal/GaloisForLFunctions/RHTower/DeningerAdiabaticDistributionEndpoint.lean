import GaloisForLFunctions.RHTower.DeningerAdiabaticMobiusEndpoint
import GaloisForLFunctions.RHTower.DeningerCommutatorExactKernel

/-!
# The adiabatic inverse as a strict tempered-distribution path

The strict ray endpoint proved for the full all-integer inverse is transported to the line by even
extension.  This is an exact operation at the `L¹` level: the distance of two even extensions is
twice their distance on the positive ray.  The continuous embedding `L¹(ℝ) → 𝓢'(ℝ)` then gives the
critical distribution endpoint without any weak compactness premise.

At `a = 0` the resulting two-collar boundary is literally the previously constructed
Möbius--Fourier commutator.  Its zero set is therefore exactly the Meyer--Poisson image.
-/

namespace RHTower

open Filter Topology MeasureTheory SchwartzMap FourierTransform

noncomputable section

/-- Even extension of the full adiabatic inverse from the positive ray to the line. -/
def deningerAdiabaticEvenPreimage (a : ℝ) (h : DeningerMeyerSource) (x : ℝ) : ℂ :=
  deningerAdiabaticMobiusPreimage a h |x|

@[simp]
theorem deningerAdiabaticEvenPreimage_even
    (a : ℝ) (h : DeningerMeyerSource) (x : ℝ) :
    deningerAdiabaticEvenPreimage a h (-x) = deningerAdiabaticEvenPreimage a h x := by
  rw [deningerAdiabaticEvenPreimage, deningerAdiabaticEvenPreimage, abs_neg]

theorem deningerAdiabaticEvenPreimage_of_pos
    (a : ℝ) (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    deningerAdiabaticEvenPreimage a h x = deningerAdiabaticMobiusPreimage a h x := by
  rw [deningerAdiabaticEvenPreimage, abs_of_pos hx]

/-- The critical specialization is literal on the whole line, including the null origin. -/
@[simp]
theorem deningerAdiabaticEvenPreimage_zero
    (h : DeningerMeyerSource) (x : ℝ) :
    deningerAdiabaticEvenPreimage 0 h x =
      deningerEvenPreimage
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x := by
  rw [deningerAdiabaticEvenPreimage, deningerEvenPreimage,
    deningerAdiabaticMobiusPreimage, deningerAdiabaticSource_zero]
  simp [Real.rpow_zero]

/-- Every nonnegative adiabatic inverse has an integrable even extension. -/
theorem deningerAdiabaticEvenPreimage_integrable
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) :
    Integrable (deningerAdiabaticEvenPreimage a h) := by
  have hpos : IntegrableOn (deningerAdiabaticMobiusPreimage a h) (Set.Ioi (0 : ℝ)) := by
    have hmoment := deningerAdiabaticMobiusPreimage_moment_integrable ha 0 h
    refine hmoment.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp
  have hpos' : IntegrableOn (deningerAdiabaticEvenPreimage a h) (Set.Ioi (0 : ℝ)) :=
    hpos.congr_fun
      (fun x hx => (deningerAdiabaticEvenPreimage_of_pos a h hx).symm) measurableSet_Ioi
  have hneg : IntegrableOn (deningerAdiabaticEvenPreimage a h) (Set.Iio (0 : ℝ)) := by
    have href := deningerEvenPreimage_integrableOn_Iio hpos
    refine href.congr_fun (fun x hx => ?_) measurableSet_Iio
    have hxneg : x < 0 := hx
    rw [deningerAdiabaticEvenPreimage, abs_of_neg hxneg]
  exact deningerIntegrable_of_rays hpos' hneg

/-- Full-line `L¹` realization of the even adiabatic inverse. -/
def deningerAdiabaticEvenPreimageLp
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) :
    Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  (deningerAdiabaticEvenPreimage_integrable ha h).toL1
    (deningerAdiabaticEvenPreimage a h)

/-- Full-line adiabatic inverse as a tempered distribution. -/
def deningerAdiabaticPreimageDistribution
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistribution (deningerAdiabaticEvenPreimageLp ha h)

/-- At the critical endpoint the adiabatic distribution is the canonical preimage distribution. -/
@[simp]
theorem deningerAdiabaticPreimageDistribution_zero
    (h : DeningerMeyerSource) :
    deningerAdiabaticPreimageDistribution (a := 0) le_rfl h =
      deningerPreimageDistribution (DeningerMeyerSource.toSource h) := by
  ext g
  rw [deningerAdiabaticPreimageDistribution,
    MeasureTheory.Lp.toTemperedDistribution_apply,
    deningerPreimageDistribution, deningerL1Distribution,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  simp only [deningerAdiabaticEvenPreimageLp]
  apply integral_congr_ae
  filter_upwards [
    Integrable.coeFn_toL1
      (deningerAdiabaticEvenPreimage_integrable (a := 0) le_rfl h),
    Integrable.coeFn_toL1
      (deningerEvenPreimage_integrable (DeningerMeyerSource.toSource h).2)] with x hx hy
  rw [hx, hy, deningerAdiabaticEvenPreimage_zero]

/-- Integral of an integrable even real function is twice its positive-ray integral. -/
theorem deninger_integral_even_eq_two_Ioi
    {F : ℝ → ℝ} (hF : Integrable F) (hev : ∀ x : ℝ, F (-x) = F x) :
    (∫ x : ℝ, F x) = 2 * ∫ x in Set.Ioi (0 : ℝ), F x := by
  have hsplit :
      (∫ x in Set.Iic (0 : ℝ), F x) + ∫ x in Set.Ioi (0 : ℝ), F x =
        ∫ x : ℝ, F x :=
    intervalIntegral.integral_Iic_add_Ioi hF.integrableOn hF.integrableOn
  have hrefl :
      (∫ x in Set.Ioi (0 : ℝ), F (-x)) = ∫ x in Set.Iic (0 : ℝ), F x := by
    simpa only [neg_zero] using integral_comp_neg_Ioi (0 : ℝ) F
  have heven : (∫ x in Set.Ioi (0 : ℝ), F (-x)) = ∫ x in Set.Ioi (0 : ℝ), F x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => hev x
  rw [← hsplit, ← hrefl, heven]
  ring

/-- Exact metric cost of even extension: full-line distance is twice ray distance. -/
theorem deningerAdiabaticEvenPreimageLp_dist_eq_two_mul
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) :
    dist (deningerAdiabaticEvenPreimageLp ha h)
        (deningerAdiabaticEvenPreimageLp (a := 0) le_rfl h) =
      2 * dist (deningerAdiabaticMomentLp ha 0 h) (deningerMomentLp 0 h) := by
  let F : ℝ → ℝ := fun x =>
    dist (deningerAdiabaticEvenPreimage a h x)
      (deningerAdiabaticEvenPreimage 0 h x)
  have hF : Integrable F := by
    simpa only [F, dist_eq_norm, Pi.sub_apply] using
      ((deningerAdiabaticEvenPreimage_integrable ha h).sub
        (deningerAdiabaticEvenPreimage_integrable (a := 0) le_rfl h)).norm
  have hFeven : ∀ x : ℝ, F (-x) = F x := by
    intro x
    simp only [F, deningerAdiabaticEvenPreimage_even]
  calc
    dist (deningerAdiabaticEvenPreimageLp ha h)
        (deningerAdiabaticEvenPreimageLp (a := 0) le_rfl h) =
        ∫ x : ℝ, F x := by
      rw [L1.dist_eq_integral_dist]
      simp only [deningerAdiabaticEvenPreimageLp]
      apply integral_congr_ae
      filter_upwards [
        Integrable.coeFn_toL1 (deningerAdiabaticEvenPreimage_integrable ha h),
        Integrable.coeFn_toL1
          (deningerAdiabaticEvenPreimage_integrable (a := 0) le_rfl h)] with x hx hy
      rw [hx, hy]
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), F x :=
      deninger_integral_even_eq_two_Ioi hF hFeven
    _ = 2 * dist (deningerAdiabaticMomentLp ha 0 h) (deningerMomentLp 0 h) := by
      congr 1
      rw [L1.dist_eq_integral_dist]
      simp only [deningerAdiabaticMomentLp, deningerMomentLp]
      apply integral_congr_ae
      filter_upwards [
        MemLp.coeFn_toLp (deningerAdiabaticMomentFun_memLp ha 0 h),
        MemLp.coeFn_toLp (deningerMomentFun_memLp 0 h),
        ae_restrict_mem measurableSet_Ioi] with x hx hy hxpos
      rw [hx, hy]
      simp only [F, deningerAdiabaticMomentFun, deningerMomentFun, pow_zero,
        Complex.ofReal_one, one_mul]
      rw [deningerAdiabaticEvenPreimage_of_pos a h hxpos,
        deningerAdiabaticEvenPreimage_zero,
        deningerEvenPreimage_of_pos _ hxpos]

/-- **Strict critical endpoint in full-line `L¹`.** -/
theorem tendsto_deningerAdiabaticEvenPreimageLp_zero
    (h : DeningerMeyerSource) :
    Tendsto
      (fun a : Set.Ioi (0 : ℝ) => deningerAdiabaticEvenPreimageLp a.property.le h)
      atBot (𝓝 (deningerAdiabaticEvenPreimageLp (a := 0) le_rfl h)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hray := (tendsto_iff_dist_tendsto_zero.mp
    (tendsto_deningerAdiabaticMomentLp_zero 0 h)).const_mul 2
  convert hray using 1
  · funext a
    exact deningerAdiabaticEvenPreimageLp_dist_eq_two_mul a.property.le h
  · simp

/-- **Strict critical endpoint in tempered distributions.**  This is continuity of the canonical
`L¹(ℝ) → 𝓢'(ℝ)` embedding, not a separately assumed weak-limit principle. -/
theorem tendsto_deningerAdiabaticPreimageDistribution_zero
    (h : DeningerMeyerSource) :
    Tendsto
      (fun a : Set.Ioi (0 : ℝ) =>
        deningerAdiabaticPreimageDistribution a.property.le h)
      atBot (𝓝 (deningerPreimageDistribution (DeningerMeyerSource.toSource h))) := by
  rw [← deningerAdiabaticPreimageDistribution_zero]
  have hmap :=
    (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1).continuous.continuousAt.tendsto.comp
      (tendsto_deningerAdiabaticEvenPreimageLp_zero h)
  change Tendsto
    ((MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1) ∘
      fun a : Set.Ioi (0 : ℝ) => deningerAdiabaticEvenPreimageLp a.property.le h)
    atBot
    (𝓝 ((MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1)
      (deningerAdiabaticEvenPreimageLp (a := 0) le_rfl h)))
  exact hmap

/-- Collar exchange transported to the Meyer-topologized source. -/
def deningerMeyerCollarExchange (h : DeningerMeyerSource) : DeningerMeyerSource :=
  DeningerMeyerSource.toSource.symm
    (deningerCollarExchange (DeningerMeyerSource.toSource h))

@[simp]
theorem deningerMeyerCollarExchange_toSource (h : DeningerMeyerSource) :
    DeningerMeyerSource.toSource (deningerMeyerCollarExchange h) =
      deningerCollarExchange (DeningerMeyerSource.toSource h) := by
  rw [deningerMeyerCollarExchange, LinearEquiv.apply_symm_apply]

@[simp]
theorem deningerMeyerCollarExchange_involutive (h : DeningerMeyerSource) :
    deningerMeyerCollarExchange (deningerMeyerCollarExchange h) = h := by
  apply DeningerMeyerSource.toSource.injective
  rw [deningerMeyerCollarExchange_toSource, deningerMeyerCollarExchange_toSource,
    deningerCollarExchange_involutive]

/-- Two-collar adiabatic boundary `ℱ(E M_a h) - E M_a(Jh)`. -/
def deningerAdiabaticMobiusBoundary
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  𝓕 (deningerAdiabaticPreimageDistribution ha h) -
    deningerAdiabaticPreimageDistribution ha (deningerMeyerCollarExchange h)

/-- At `a = 0` the adiabatic boundary is literally the canonical Möbius--Fourier commutator. -/
@[simp]
theorem deningerAdiabaticMobiusBoundary_zero (h : DeningerMeyerSource) :
    deningerAdiabaticMobiusBoundary (a := 0) le_rfl h =
      deningerMobiusCommutator (DeningerMeyerSource.toSource h) := by
  rw [deningerAdiabaticMobiusBoundary, deningerAdiabaticPreimageDistribution_zero,
    deningerAdiabaticPreimageDistribution_zero, deningerMobiusCommutator,
    deningerMeyerCollarExchange_toSource]

/-- The critical boundary kernel is exactly the concrete Meyer--Poisson image. -/
theorem deningerAdiabaticMobiusBoundary_zero_iff
    (h : DeningerMeyerSource) :
    deningerAdiabaticMobiusBoundary (a := 0) le_rfl h = 0 ↔
      DeningerMeyerSource.toSource h ∈ Set.range deningerPoissonSource := by
  rw [deningerAdiabaticMobiusBoundary_zero]
  exact Set.ext_iff.mp deningerCommutator_exact_kernel (DeningerMeyerSource.toSource h)

/-- Exact set-valued critical kernel theorem on the Meyer source. -/
theorem deningerAdiabaticMobiusBoundary_exact_kernel :
    {h : DeningerMeyerSource |
      deningerAdiabaticMobiusBoundary (a := 0) le_rfl h = 0} =
    {h : DeningerMeyerSource |
      DeningerMeyerSource.toSource h ∈ Set.range deningerPoissonSource} := by
  ext h
  exact deningerAdiabaticMobiusBoundary_zero_iff h

end

end RHTower
