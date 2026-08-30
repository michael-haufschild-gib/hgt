import GaloisForLFunctions.RHTower.SuzukiLimitingLogClosedMarkov

/-!
# Suzuki's limiting logarithmic ground-state simplicity

This module closes the irreducibility/simplicity step in Suzuki (2026), Theorem 1.4 directly at
closed-form level.  Smooth modulus approximants retain exact jump energy at closure, yielding a
quantitative sign-crossing defect.  Every real ground minimizer therefore has fixed sign.  Exact
complexification of the complete form domain, real polarization of the shifted nonnegative form,
and a cone/orthogonalization argument then prove that the bottom eigenspace of the represented
limiting logarithmic operator is one-dimensional over `ℂ`.

No positivity-improving semigroup, irreducibility premise, spectral-gap premise, or added axiom is
used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiLimitingLogGroundSimplicityLocalInst1 : SFinite ccmArchimedeanFormMeasure := by
  unfold ccmArchimedeanFormMeasure
  infer_instance

local instance suzukiLimitingLogGroundSimplicityLocalInst2 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem tendsto_suzukiSmoothAbsoluteScale_apply (x : ℝ) :
    Tendsto (fun n => suzukiSmoothAbsolute (suzukiSmoothAbsoluteScale n) x)
      atTop (nhds |x|) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hs := (Metric.tendsto_atTop.1 tendsto_suzukiSmoothAbsoluteScale_zero) ε hε
  obtain ⟨N, hN⟩ := hs
  refine ⟨N, fun n hn => ?_⟩
  have hscale := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_pos (suzukiSmoothAbsoluteScale_pos n)] at hscale
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt
    (abs_sub_suzukiSmoothAbsolute_le
      (suzukiSmoothAbsoluteScale_pos n).le) hscale

theorem tendsto_suzukiFinitePartDifferenceEnergy_smoothAbsolute
    (u : SuzukiRestrictedWeilCore 1) :
    Tendsto (fun n => suzukiFinitePartDifferenceEnergy 1
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))) atTop
      (nhds (suzukiFinitePartDifferenceEnergy 1 (suzukiRealAbsolute u))) := by
  let μ := (volume.restrict (Ioc (-1 : ℝ) 1)).prod
    (volume.restrict (Ioc (-1 : ℝ) 1))
  let F : ℕ → ℝ × ℝ → ℝ := fun n z =>
    suzukiUnitJumpKernel
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n)) z
  let f : ℝ × ℝ → ℝ := suzukiUnitJumpKernel (suzukiRealAbsolute u)
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (integrable_suzukiUnitJumpKernel_product
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))).aestronglyMeasurable
  have hbound : Integrable (suzukiUnitJumpKernel u) μ :=
    integrable_suzukiUnitJumpKernel_product u
  have hle (n : ℕ) : ∀ᵐ z ∂μ, ‖F n z‖ ≤ suzukiUnitJumpKernel u z := by
    filter_upwards with z
    rw [Real.norm_eq_abs,
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg _ z)]
    unfold suzukiUnitJumpKernel
    exact mul_le_mul_of_nonneg_right
      (sq_le_sq.mpr (abs_suzukiSmoothAbsolute_sub_le
        (suzukiSmoothAbsoluteScale_pos n) (u z.1) (u z.2)))
      (inv_nonneg.mpr (abs_nonneg _))
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n => F n z) atTop (nhds (f z)) := by
    filter_upwards with z
    unfold F f suzukiUnitJumpKernel
    exact (((tendsto_suzukiSmoothAbsoluteScale_apply (u z.1)).sub
      (tendsto_suzukiSmoothAbsoluteScale_apply (u z.2))).pow 2).mul
        tendsto_const_nhds
  have hD := tendsto_integral_of_dominated_convergence
    (suzukiUnitJumpKernel u) hmeas hbound hle hlim
  convert hD using 1
  · funext n
    exact suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))
      (integrable_suzukiUnitJumpKernel_product
        (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
          (suzukiSmoothAbsoluteScale_pos n)))
  · exact congrArg nhds
      (suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable
        (suzukiRealAbsolute u) (integrable_suzukiUnitAbsoluteJumpKernel_product u))

theorem tendsto_suzukiFinitePartLogPotential_smoothAbsolute
    (u : SuzukiRestrictedWeilCore 1) :
    Tendsto (fun n => suzukiFinitePartLogPotential 1
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))) atTop
      (nhds (suzukiFinitePartLogPotential 1 (suzukiRealAbsolute u))) := by
  let μ := volume.restrict (Ioc (-1 : ℝ) 1)
  let F : ℕ → ℝ → ℝ := fun n x =>
    Real.log (1 ^ 2 - x ^ 2) *
      (suzukiSmoothAbsolute (suzukiSmoothAbsoluteScale n) (u x)) ^ 2
  let f : ℝ → ℝ := fun x =>
    Real.log (1 ^ 2 - x ^ 2) * (suzukiRealAbsolute u x) ^ 2
  let B : ℝ → ℝ := fun x =>
    |Real.log (1 ^ 2 - x ^ 2) * u x ^ 2|
  have huP := suzukiFinitePartLogPotential_integrable_upper
    (by norm_num : (0 : ℝ) < 1) u.supportRadius_nonneg
      u.supportRadius_lt_aperture u.continuous u.support_subset
  have huPint : Integrable
      (fun x => Real.log (1 ^ 2 - x ^ 2) * u x ^ 2) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (-1 : ℝ) ≤ 1)).mp huP.1
  have hB : Integrable B μ := by
    simpa only [B, Real.norm_eq_abs] using huPint.norm
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (suzukiFinitePartLogPotential_integrable_upper
      (by norm_num : (0 : ℝ) < 1)
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n)).supportRadius_nonneg
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n)).supportRadius_lt_aperture
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n)).continuous
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n)).support_subset).1.aestronglyMeasurable
  have hle (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ B x := by
    filter_upwards with x
    rw [Real.norm_eq_abs]
    unfold F B
    rw [abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_sq, abs_sq]
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg _)
        (abs_suzukiSmoothAbsolute_le
          (suzukiSmoothAbsoluteScale_pos n).le) 2)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x)) := by
    filter_upwards with x
    unfold F f
    exact tendsto_const_nhds.mul
      ((tendsto_suzukiSmoothAbsoluteScale_apply (u x)).pow 2)
  have hP := tendsto_integral_of_dominated_convergence B hmeas hB hle hlim
  unfold suzukiFinitePartLogPotential
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  convert hP using 1
  · funext n
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rfl

theorem tendsto_suzukiFinitePartEnergy_smoothAbsolute
    (u : SuzukiRestrictedWeilCore 1) :
    Tendsto (fun n => suzukiFinitePartEnergy 1
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))) atTop
      (nhds (suzukiFinitePartEnergy 1 (suzukiRealAbsolute u))) := by
  unfold suzukiFinitePartEnergy
  exact (tendsto_suzukiFinitePartDifferenceEnergy_smoothAbsolute u).const_mul
      (1 / 4 : ℝ) |>.sub
    ((tendsto_suzukiFinitePartLogPotential_smoothAbsolute u).const_mul
      (1 / 2 : ℝ))

/-- Exact core modulus closure: none of the strictly positive jump defect is lost when the
smooth modulus approximation enters the complete form domain. -/
theorem exists_suzukiCoreAbsoluteRealFormVector_exact
    (u : SuzukiRestrictedWeilCore 1) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2Modulus (suzukiLimitingCoreIntervalVector u) ∧
      (suzukiLimitingLogClosedForm w w).re ≤
        suzukiFinitePartEnergy 1 (suzukiRealAbsolute u) := by
  let q : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture :=
    fun n => suzukiSmoothAbsoluteCoreFormVector u n
  let M := Real.sqrt (suzukiCoreShiftedEnergy u)
  obtain ⟨w, φ, hφ, _hwM, hweak, hcompact⟩ :=
    exists_suzukiLimitingLogForm_weakSubseq q M
      (norm_suzukiSmoothAbsoluteCoreFormVector_le_sqrt u)
  have hqmem (n : ℕ) : q n ∈ suzukiLimitingRealCoreSubmodule := by
    exact suzukiRestrictedWeilCoreCCMFormVector_mem_realCoreSubmodule
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))
  have hwreal : w ∈ SuzukiLimitingRealFormDomain := by
    exact mem_topologicalClosure_of_complexWeak_limit
      suzukiLimitingRealCoreSubmodule (fun n => q (φ n)) w
        (fun n => hqmem (φ n)) hweak
  have hphysicalW : Tendsto (fun n => suzukiLimitingLogFormEmbedding (q (φ n)))
      atTop (nhds (suzukiLimitingLogFormEmbedding w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hcompact
  have hphysicalAbs : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (q (φ n))) atTop
      (nhds (suzukiCoreAbsoluteIntervalVector u)) := by
    exact (tendsto_suzukiLimitingLogFormEmbedding_smoothAbsoluteCoreFormVector u).comp
      hφ.tendsto_atTop
  have hrepAbs : suzukiLimitingLogFormEmbedding w =
      suzukiCoreAbsoluteIntervalVector u :=
    tendsto_nhds_unique hphysicalW hphysicalAbs
  have hclosed : Tendsto
      (fun n => (suzukiLimitingLogClosedForm (q n) (q n)).re) atTop
      (nhds (suzukiFinitePartEnergy 1 (suzukiRealAbsolute u))) := by
    convert tendsto_suzukiFinitePartEnergy_smoothAbsolute u using 1
    funext n
    dsimp only [q, suzukiSmoothAbsoluteCoreFormVector]
    rw [suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock]
    have he := suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture
      (suzukiSmoothAbsoluteCore u (suzukiSmoothAbsoluteScale n)
        (suzukiSmoothAbsoluteScale_pos n))
    dsimp only [suzukiLimitingUnitAperture] at he
    rw [he]
    rfl
  have hclosedSub : Tendsto
      (fun n => (suzukiLimitingLogClosedForm (q (φ n)) (q (φ n))).re) atTop
      (nhds (suzukiFinitePartEnergy 1 (suzukiRealAbsolute u))) :=
    hclosed.comp hφ.tendsto_atTop
  have hnorm : Tendsto
      (fun n => ‖suzukiLimitingLogFormEmbedding (q (φ n))‖) atTop
      (nhds ‖suzukiCoreAbsoluteIntervalVector u‖) :=
    (continuous_norm.tendsto _).comp hphysicalAbs
  have hnormSq := hnorm.pow 2
  have hboundTend : Tendsto (fun n =>
      (suzukiLimitingLogClosedForm (q (φ n)) (q (φ n))).re +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiLimitingLogFormEmbedding (q (φ n))‖ ^ 2) atTop
      (nhds (suzukiFinitePartEnergy 1 (suzukiRealAbsolute u) +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiCoreAbsoluteIntervalVector u‖ ^ 2)) :=
    hclosedSub.add (tendsto_const_nhds.mul hnormSq)
  have hshifted : suzukiLimitingLogShiftedEnergy w ≤
      suzukiFinitePartEnergy 1 (suzukiRealAbsolute u) +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiCoreAbsoluteIntervalVector u‖ ^ 2 := by
    apply suzukiLimitingLogShiftedEnergy_le_of_weak_limit_upper_tendsto
      (fun n => q (φ n)) w hweak _ _ hboundTend
    intro n
    unfold suzukiLimitingLogShiftedEnergy
    exact le_rfl
  refine ⟨w, hwreal, ?_, ?_⟩
  · rw [hrepAbs, suzukiCoreAbsoluteIntervalVector_eq_modulus]
  · unfold suzukiLimitingLogShiftedEnergy at hshifted
    rw [hrepAbs] at hshifted
    exact (add_le_add_iff_right
      (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
        ‖suzukiCoreAbsoluteIntervalVector u‖ ^ 2)).mp hshifted

/-- On the unit interval, the positive-to-negative jump kernel dominates one half of the
uncoupled product. -/
theorem half_mul_positivePart_mul_negativePart_le_signCrossKernel
    (u : SuzukiRestrictedWeilCore 1) {x y : ℝ}
    (hx : x ∈ Ioc (-1 : ℝ) 1) (hy : y ∈ Ioc (-1 : ℝ) 1) :
    (1 / 2 : ℝ) *
        (suzukiRealPositivePart u x * suzukiRealNegativePart u y) ≤
      suzukiUnitSignCrossKernel u (x, y) := by
  by_cases hxy : x = y
  · subst y
    have hzero := suzukiRealPositivePart_mul_negativePart u x
    unfold suzukiUnitSignCrossKernel
    rw [hzero, zero_mul]
    norm_num
  · have habspos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have habsle : |x - y| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hinv : (1 / 2 : ℝ) ≤ |x - y|⁻¹ := by
      simpa only [one_div] using
        ((inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) habspos).mpr habsle)
    have hpn : 0 ≤ suzukiRealPositivePart u x * suzukiRealNegativePart u y :=
      mul_nonneg (suzukiRealPositivePart_nonneg u x)
        (suzukiRealNegativePart_nonneg u y)
    unfold suzukiUnitSignCrossKernel
    change (1 / 2 : ℝ) *
      (suzukiRealPositivePart u x * suzukiRealNegativePart u y) ≤
        (suzukiRealPositivePart u x * suzukiRealNegativePart u y) * |x - y|⁻¹
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hinv hpn

/-- Quantitative connectedness of Suzuki's unit jump kernel. The coarse constant `1/2`
comes only from the diameter of `(-1,1)`; it is enough to make the closed-domain argument
uniform under form-core approximation. -/
theorem half_mul_posPartIntegral_mul_negPartIntegral_le_signInteraction
    (u : SuzukiRestrictedWeilCore 1) :
    (1 / 2 : ℝ) *
        (∫ x in (-1 : ℝ)..1, suzukiRealPositivePart u x) *
        (∫ x in (-1 : ℝ)..1, suzukiRealNegativePart u x) ≤
      suzukiUnitSignInteraction u := by
  let S : Set ℝ := Ioc (-1 : ℝ) 1
  let μ : Measure ℝ := volume.restrict S
  let p : ℝ → ℝ := suzukiRealPositivePart u
  let n : ℝ → ℝ := suzukiRealNegativePart u
  have hpI : Integrable p μ := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (-1 : ℝ) ≤ 1)).mp
    exact (continuous_suzukiRealPositivePart u.continuous).intervalIntegrable _ _
  have hnI : Integrable n μ := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (-1 : ℝ) ≤ 1)).mp
    exact (continuous_suzukiRealNegativePart u.continuous).intervalIntegrable _ _
  have hprodI : Integrable (fun z : ℝ × ℝ =>
      (1 / 2 : ℝ) * (p z.1 * n z.2)) (μ.prod μ) :=
    (hpI.mul_prod hnI).const_mul (1 / 2 : ℝ)
  have hcrossI : Integrable (suzukiUnitSignCrossKernel u) (μ.prod μ) := by
    simpa only [μ, S] using integrable_suzukiUnitSignCrossKernel_product u
  have hswapI : Integrable
      (fun z : ℝ × ℝ => suzukiUnitSignCrossKernel u (z.2, z.1))
      (μ.prod μ) := by
    simpa only [μ, S] using integrable_suzukiUnitSignCrossKernel_swap_product u
  have hpoint : ∀ᵐ z ∂μ.prod μ,
      (1 / 2 : ℝ) * (p z.1 * n z.2) ≤ suzukiUnitSignCrossKernel u z := by
    have hmem : ∀ᵐ z ∂μ.prod μ, z.1 ∈ S ∧ z.2 ∈ S := by
      dsimp only [S]
      have hm : MeasurableSet {z : ℝ × ℝ |
          z.1 ∈ Ioc (-1 : ℝ) 1 ∧ z.2 ∈ Ioc (-1 : ℝ) 1} := by
        exact (measurableSet_Ioc.preimage measurable_fst).inter
          (measurableSet_Ioc.preimage measurable_snd)
      rw [Measure.ae_prod_iff_ae_ae hm]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact ⟨hx, hy⟩
    filter_upwards [hmem] with z hz
    exact half_mul_positivePart_mul_negativePart_le_signCrossKernel u hz.1 hz.2
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  change (1 / 2 : ℝ) * (∫ x, p x ∂μ) * (∫ x, n x ∂μ) ≤ _
  calc
    (1 / 2 : ℝ) * (∫ x, p x ∂μ) * (∫ x, n x ∂μ) =
        ∫ z : ℝ × ℝ, (1 / 2 : ℝ) * (p z.1 * n z.2) ∂μ.prod μ := by
      rw [integral_const_mul, integral_prod_mul]
      ring
    _ ≤ ∫ z : ℝ × ℝ, suzukiUnitSignCrossKernel u z ∂μ.prod μ :=
      integral_mono_ae hprodI hcrossI hpoint
    _ ≤ ∫ z : ℝ × ℝ,
        (suzukiUnitSignCrossKernel u z +
          suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ.prod μ := by
      apply integral_mono_ae hcrossI (hcrossI.add hswapI)
      filter_upwards with z
      exact le_add_of_nonneg_right
        (suzukiUnitSignCrossKernel_nonneg u (z.2, z.1))
    _ = suzukiUnitSignInteraction u := by
      rfl

/-- Real part of a physical complex `L²` vector, as a real `L²` vector. -/
def suzukiIntervalL2RealPart :
    SuzukiApertureIntervalL2 1 →L[ℝ]
      Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1)) :=
  Complex.reCLM.compLpL 2 volume

theorem suzukiIntervalL2RealPart_coeFn (f : SuzukiApertureIntervalL2 1) :
    (suzukiIntervalL2RealPart f : SuzukiApertureInterval 1 → ℝ) =ᵐ[volume]
      fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f

def suzukiIntervalL2RealPositivePart (f : SuzukiApertureIntervalL2 1) :
    Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1)) :=
  Lp.posPart (suzukiIntervalL2RealPart f)

def suzukiIntervalL2RealNegativePart (f : SuzukiApertureIntervalL2 1) :
    Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1)) :=
  Lp.negPart (suzukiIntervalL2RealPart f)

theorem continuous_suzukiIntervalL2RealPositivePart :
    Continuous suzukiIntervalL2RealPositivePart :=
  Lp.continuous_posPart.comp suzukiIntervalL2RealPart.continuous

theorem continuous_suzukiIntervalL2RealNegativePart :
    Continuous suzukiIntervalL2RealNegativePart :=
  Lp.continuous_negPart.comp suzukiIntervalL2RealPart.continuous

def suzukiIntervalRealOne :
    Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1)) :=
  (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))

theorem suzukiIntervalRealOne_coeFn :
    (suzukiIntervalRealOne : SuzukiApertureInterval 1 → ℝ) =ᵐ[volume]
      fun _ => 1 := by
  exact (memLp_const (1 : ℝ)).coeFn_toLp

def suzukiIntervalPositiveMass (f : SuzukiApertureIntervalL2 1) : ℝ :=
  inner ℝ suzukiIntervalRealOne (suzukiIntervalL2RealPositivePart f)

def suzukiIntervalNegativeMass (f : SuzukiApertureIntervalL2 1) : ℝ :=
  inner ℝ suzukiIntervalRealOne (suzukiIntervalL2RealNegativePart f)

theorem continuous_suzukiIntervalPositiveMass :
    Continuous suzukiIntervalPositiveMass := by
  exact (continuous_const.inner (𝕜 := ℝ)
    continuous_suzukiIntervalL2RealPositivePart)

theorem continuous_suzukiIntervalNegativeMass :
    Continuous suzukiIntervalNegativeMass := by
  exact (continuous_const.inner (𝕜 := ℝ)
    continuous_suzukiIntervalL2RealNegativePart)

private theorem integral_subtype_unitIcc_eq_intervalIntegral_real
    (F : ℝ → ℝ) :
    (∫ x : SuzukiApertureInterval 1, F (x : ℝ) ∂volume) =
      ∫ x in (-1 : ℝ)..1, F x := by
  calc
    (∫ x : SuzukiApertureInterval 1, F (x : ℝ) ∂volume) =
        ∫ x in Icc (-1 : ℝ) 1, F x := by
      exact MeasureTheory.integral_subtype measurableSet_Icc F
    _ = ∫ x in Ioc (-1 : ℝ) 1, F x :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in (-1 : ℝ)..1, F x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]

theorem suzukiIntervalPositiveMass_core (u : SuzukiRestrictedWeilCore 1) :
    suzukiIntervalPositiveMass (suzukiLimitingCoreIntervalVector u) =
      ∫ x in (-1 : ℝ)..1, suzukiRealPositivePart u x := by
  unfold suzukiIntervalPositiveMass
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval 1,
        inner ℝ (suzukiIntervalRealOne x)
          (suzukiIntervalL2RealPositivePart
            (suzukiLimitingCoreIntervalVector u) x)) =
      ∫ x : SuzukiApertureInterval 1,
        suzukiRealPositivePart u (x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [suzukiIntervalRealOne_coeFn,
        Lp.coeFn_posPart
          (suzukiIntervalL2RealPart (suzukiLimitingCoreIntervalVector u)),
        suzukiIntervalL2RealPart_coeFn (suzukiLimitingCoreIntervalVector u),
        suzukiLimitingCoreIntervalVector_coeFn u] with x hone hpos hre hcore
      change inner ℝ (suzukiIntervalRealOne x)
        ((Lp.posPart (suzukiIntervalL2RealPart
          (suzukiLimitingCoreIntervalVector u))) x) = _
      rw [hone, hpos, hre, hcore]
      simp [suzukiRealPositivePart, RCLike.inner_apply, posPart_def]
    _ = _ := integral_subtype_unitIcc_eq_intervalIntegral_real _

theorem suzukiIntervalNegativeMass_core (u : SuzukiRestrictedWeilCore 1) :
    suzukiIntervalNegativeMass (suzukiLimitingCoreIntervalVector u) =
      ∫ x in (-1 : ℝ)..1, suzukiRealNegativePart u x := by
  unfold suzukiIntervalNegativeMass
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval 1,
        inner ℝ (suzukiIntervalRealOne x)
          (suzukiIntervalL2RealNegativePart
            (suzukiLimitingCoreIntervalVector u) x)) =
      ∫ x : SuzukiApertureInterval 1,
        suzukiRealNegativePart u (x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [suzukiIntervalRealOne_coeFn,
        Lp.coeFn_negPart_eq_max
          (suzukiIntervalL2RealPart (suzukiLimitingCoreIntervalVector u)),
        suzukiIntervalL2RealPart_coeFn (suzukiLimitingCoreIntervalVector u),
        suzukiLimitingCoreIntervalVector_coeFn u] with x hone hneg hre hcore
      change inner ℝ (suzukiIntervalRealOne x)
        ((Lp.negPart (suzukiIntervalL2RealPart
          (suzukiLimitingCoreIntervalVector u))) x) = _
      rw [hone, hneg, hre, hcore]
      simp [suzukiRealNegativePart, RCLike.inner_apply, negPart_def]
    _ = _ := integral_subtype_unitIcc_eq_intervalIntegral_real _

theorem half_mul_positiveMass_mul_negativeMass_le_signInteraction
    (u : SuzukiRestrictedWeilCore 1) :
    (1 / 2 : ℝ) *
        suzukiIntervalPositiveMass (suzukiLimitingCoreIntervalVector u) *
        suzukiIntervalNegativeMass (suzukiLimitingCoreIntervalVector u) ≤
      suzukiUnitSignInteraction u := by
  rw [suzukiIntervalPositiveMass_core, suzukiIntervalNegativeMass_core]
  exact half_mul_posPartIntegral_mul_negPartIntegral_le_signInteraction u

/-- Strict closed-domain modulus inequality. The positive Suzuki jump kernel leaves a
quantitative defect depending only on the positive and negative physical masses of the
closed form vector. -/
theorem exists_suzukiRealFormDomainModulus_with_signDefect
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q) ∧
      (suzukiLimitingLogClosedForm w w).re ≤
        (suzukiLimitingLogClosedForm q q).re -
          (1 / 2 : ℝ) *
            suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
            suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) := by
  change q ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hq
  obtain ⟨z, hzcore, hzlim⟩ := mem_closure_iff_seq_limit.mp hq
  have htests (n : ℕ) : ∃ t : SuzukiRestrictedWeilRealTest 1,
      suzukiLimitingRealTestFormLinearMap t = z n := hzcore n
  choose t ht using htests
  let u : ℕ → SuzukiRestrictedWeilCore 1 := fun n =>
    suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture (t n)
  have hzform (n : ℕ) : z n =
      suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture (u n) := by
    rw [← ht n]
    rfl
  have hcoreExists (n : ℕ) := exists_suzukiCoreAbsoluteRealFormVector_exact (u n)
  choose v hvreal hvrep hvclosed using hcoreExists
  have hvrepz (n : ℕ) : suzukiLimitingLogFormEmbedding (v n) =
      suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding (z n)) := by
    rw [hvrep n, hzform n,
      ← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  have hzclosed (n : ℕ) :
      (suzukiLimitingLogClosedForm (z n) (z n)).re =
        suzukiFinitePartEnergy 1 (u n) := by
    rw [hzform n, suzukiLimitingLogClosedForm_core_eq_weilFinitePartBlock]
    have he := suzukiWeilFinitePartBlock_eq_energy suzukiLimitingUnitAperture (u n)
    dsimp only [suzukiLimitingUnitAperture] at he
    rw [he]
    rfl
  have hdefect (n : ℕ) :
      (suzukiLimitingLogClosedForm (v n) (v n)).re ≤
        (suzukiLimitingLogClosedForm (z n) (z n)).re -
          (1 / 2 : ℝ) *
            suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding (z n)) *
            suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding (z n)) := by
    have hinter := half_mul_positiveMass_mul_negativeMass_le_signInteraction (u n)
    have hinterz : (1 / 2 : ℝ) *
        suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding (z n)) *
        suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding (z n)) ≤
        suzukiUnitSignInteraction (u n) := by
      rw [hzform n, ← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
      exact hinter
    have hsplit := suzukiFinitePartEnergy_absolute_split (u n)
    rw [hzclosed n]
    linarith [hvclosed n, hinterz]
  have hvclosed_le_z (n : ℕ) :
      (suzukiLimitingLogClosedForm (v n) (v n)).re ≤
        (suzukiLimitingLogClosedForm (z n) (z n)).re := by
    calc
      (suzukiLimitingLogClosedForm (v n) (v n)).re ≤
          suzukiFinitePartEnergy 1 (suzukiRealAbsolute (u n)) := hvclosed n
      _ ≤ suzukiFinitePartEnergy 1 (u n) :=
        suzukiFinitePartEnergy_absolute_le (u n)
      _ = _ := (hzclosed n).symm
  have hzshifted : Tendsto (fun n => suzukiLimitingLogShiftedEnergy (z n)) atTop
      (nhds (suzukiLimitingLogShiftedEnergy q)) :=
    (continuous_suzukiLimitingLogShiftedEnergy.tendsto q).comp hzlim
  have hzenergyBounded : Bornology.IsBounded
      (Set.range (fun n : ℕ => suzukiLimitingLogShiftedEnergy (z n)) : Set ℝ) :=
    Metric.isBounded_range_of_tendsto
      (fun n => suzukiLimitingLogShiftedEnergy (z n)) hzshifted
  obtain ⟨C, hCrange⟩ :=
    (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hzenergyBounded
  have hCpos : 0 < C :=
    lt_of_le_of_lt dist_nonneg (hCrange ⟨0, rfl⟩)
  have hzshifted_le (n : ℕ) : suzukiLimitingLogShiftedEnergy (z n) ≤ C := by
    calc
      suzukiLimitingLogShiftedEnergy (z n) ≤
          |suzukiLimitingLogShiftedEnergy (z n)| := le_abs_self _
      _ = dist (suzukiLimitingLogShiftedEnergy (z n)) 0 := by
        rw [Real.dist_eq, sub_zero]
      _ ≤ C := (hCrange ⟨n, rfl⟩).le
  have hvshifted_z (n : ℕ) : suzukiLimitingLogShiftedEnergy (v n) ≤
      suzukiLimitingLogShiftedEnergy (z n) := by
    unfold suzukiLimitingLogShiftedEnergy
    rw [hvrepz n, norm_suzukiIntervalL2Modulus]
    exact add_le_add (hvclosed_le_z n) le_rfl
  have hvnorm (n : ℕ) : ‖v n‖ ≤ Real.sqrt C := by
    have hcoer : ‖v n‖ ^ 2 ≤ suzukiLimitingLogShiftedEnergy (v n) := by
      have h := boundedPerturbedFormRiesz_coercive
        suzukiLimitingLogFormEmbedding suzukiLimitingLogBoundedRemainder (v n)
      rwa [← suzukiLimitingLogShiftedEnergy_eq_riesz] at h
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hCpos.le]
    exact hcoer.trans ((hvshifted_z n).trans (hzshifted_le n))
  obtain ⟨w, φ, hφ, _hwC, hweak, hcompact⟩ :=
    exists_suzukiLimitingLogForm_weakSubseq v (Real.sqrt C) hvnorm
  have hwrealClosure : w ∈ SuzukiLimitingRealFormDomain.topologicalClosure :=
    mem_topologicalClosure_of_complexWeak_limit SuzukiLimitingRealFormDomain
      (fun n => v (φ n)) w (fun n => hvreal (φ n)) hweak
  have hwreal : w ∈ SuzukiLimitingRealFormDomain := by
    rw [isClosed_suzukiLimitingRealFormDomain.submodule_topologicalClosure_eq]
      at hwrealClosure
    exact hwrealClosure
  have hphysicalW : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (v (φ n))) atTop
      (nhds (suzukiLimitingLogFormEmbedding w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hcompact
  have hzsub : Tendsto (fun n => z (φ n)) atTop (nhds q) :=
    hzlim.comp hφ.tendsto_atTop
  have hzphysical : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (z (φ n))) atTop
      (nhds (suzukiLimitingLogFormEmbedding q)) :=
    (suzukiLimitingLogFormEmbedding.continuous.tendsto q).comp hzsub
  have hmodphysical : Tendsto
      (fun n => suzukiIntervalL2Modulus
        (suzukiLimitingLogFormEmbedding (z (φ n)))) atTop
      (nhds (suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q))) :=
    continuous_suzukiIntervalL2Modulus.tendsto _ |>.comp hzphysical
  have hvphysical : Tendsto
      (fun n => suzukiLimitingLogFormEmbedding (v (φ n))) atTop
      (nhds (suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q))) := by
    convert hmodphysical using 1
    funext n
    exact hvrepz (φ n)
  have hrep : suzukiLimitingLogFormEmbedding w =
      suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q) :=
    tendsto_nhds_unique hphysicalW hvphysical
  have hzclosedTend : Tendsto
      (fun n => (suzukiLimitingLogClosedForm (z (φ n)) (z (φ n))).re) atTop
      (nhds (suzukiLimitingLogClosedForm q q).re) :=
    (continuous_suzukiLimitingLogClosedEnergy.tendsto q).comp hzsub
  have hpTend : Tendsto
      (fun n => suzukiIntervalPositiveMass
        (suzukiLimitingLogFormEmbedding (z (φ n)))) atTop
      (nhds (suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q))) :=
    (continuous_suzukiIntervalPositiveMass.tendsto _).comp hzphysical
  have hnTend : Tendsto
      (fun n => suzukiIntervalNegativeMass
        (suzukiLimitingLogFormEmbedding (z (φ n)))) atTop
      (nhds (suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q))) :=
    (continuous_suzukiIntervalNegativeMass.tendsto _).comp hzphysical
  have hdefectTend : Tendsto (fun n => (1 / 2 : ℝ) *
      suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding (z (φ n))) *
      suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding (z (φ n)))) atTop
      (nhds ((1 / 2 : ℝ) *
        suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
        suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q))) :=
    (tendsto_const_nhds.mul hpTend).mul hnTend
  have hnormTend : Tendsto
      (fun n => ‖suzukiLimitingLogFormEmbedding (z (φ n))‖ ^ 2) atTop
      (nhds (‖suzukiLimitingLogFormEmbedding q‖ ^ 2)) := by
    simpa only [Function.comp_apply] using
      (((continuous_norm.tendsto _).comp hzphysical).pow 2)
  have hboundTend : Tendsto (fun n =>
      (suzukiLimitingLogClosedForm (z (φ n)) (z (φ n))).re -
        (1 / 2 : ℝ) *
          suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding (z (φ n))) *
          suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding (z (φ n))) +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiLimitingLogFormEmbedding (z (φ n))‖ ^ 2) atTop
      (nhds ((suzukiLimitingLogClosedForm q q).re -
        (1 / 2 : ℝ) *
          suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
          suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)) :=
    (hzclosedTend.sub hdefectTend).add (tendsto_const_nhds.mul hnormTend)
  have hshifted : suzukiLimitingLogShiftedEnergy w ≤
      (suzukiLimitingLogClosedForm q q).re -
        (1 / 2 : ℝ) *
          suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
          suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) +
        boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
          ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
    apply suzukiLimitingLogShiftedEnergy_le_of_weak_limit_upper_tendsto
      (fun n => v (φ n)) w hweak _ _ hboundTend
    intro n
    unfold suzukiLimitingLogShiftedEnergy
    rw [hvrepz (φ n), norm_suzukiIntervalL2Modulus]
    exact add_le_add (hdefect (φ n)) le_rfl
  refine ⟨w, hwreal, hrep, ?_⟩
  unfold suzukiLimitingLogShiftedEnergy at hshifted
  rw [hrep, norm_suzukiIntervalL2Modulus] at hshifted
  exact (add_le_add_iff_right
    (boundedPerturbedFormShift suzukiLimitingLogBoundedRemainder *
      ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)).mp hshifted

theorem suzukiIntervalPositiveMass_eq_integral
    (f : SuzukiApertureIntervalL2 1) :
    suzukiIntervalPositiveMass f =
      ∫ x : SuzukiApertureInterval 1, suzukiIntervalL2RealPositivePart f x := by
  unfold suzukiIntervalPositiveMass
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [suzukiIntervalRealOne_coeFn] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

theorem suzukiIntervalNegativeMass_eq_integral
    (f : SuzukiApertureIntervalL2 1) :
    suzukiIntervalNegativeMass f =
      ∫ x : SuzukiApertureInterval 1, suzukiIntervalL2RealNegativePart f x := by
  unfold suzukiIntervalNegativeMass
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [suzukiIntervalRealOne_coeFn] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

theorem suzukiIntervalPositiveMass_nonneg (f : SuzukiApertureIntervalL2 1) :
    0 ≤ suzukiIntervalPositiveMass f := by
  rw [suzukiIntervalPositiveMass_eq_integral]
  exact integral_nonneg_of_ae (by
    filter_upwards [Lp.coeFn_posPart (suzukiIntervalL2RealPart f)] with x hx
    change (0 : ℝ) ≤ (Lp.posPart (suzukiIntervalL2RealPart f)) x
    rw [hx]
    exact le_max_right _ _)

theorem suzukiIntervalNegativeMass_nonneg (f : SuzukiApertureIntervalL2 1) :
    0 ≤ suzukiIntervalNegativeMass f := by
  rw [suzukiIntervalNegativeMass_eq_integral]
  exact integral_nonneg_of_ae (by
    filter_upwards [Lp.coeFn_negPart_eq_max (suzukiIntervalL2RealPart f)] with x hx
    change (0 : ℝ) ≤ (Lp.negPart (suzukiIntervalL2RealPart f)) x
    rw [hx]
    exact le_max_right _ _)

/-- A closed real ground minimizer cannot carry both positive and negative mass. -/
theorem suzukiRealGroundMinimizer_positiveMass_mul_negativeMass_eq_zero
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
      suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) = 0 := by
  obtain ⟨w, _hwreal, hwrep, hwenergy⟩ :=
    exists_suzukiRealFormDomainModulus_with_signDefect q hq
  have hfloor := suzukiLimitingLogOperatorGroundEnergy_mul_formNorm_sq_le w
  rw [hwrep, norm_suzukiIntervalL2Modulus] at hfloor
  have hp := suzukiIntervalPositiveMass_nonneg (suzukiLimitingLogFormEmbedding q)
  have hn := suzukiIntervalNegativeMass_nonneg (suzukiLimitingLogFormEmbedding q)
  rw [hground] at hwenergy
  have hnonneg : 0 ≤
      suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
        suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) :=
    mul_nonneg hp hn
  nlinarith

theorem suzukiRealGroundMinimizer_fixedMassSign
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) = 0 ∨
      suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) = 0 :=
  mul_eq_zero.mp
    (suzukiRealGroundMinimizer_positiveMass_mul_negativeMass_eq_zero q hq hground)

theorem ae_realPart_nonpos_of_suzukiIntervalPositiveMass_eq_zero
    {f : SuzukiApertureIntervalL2 1}
    (h : suzukiIntervalPositiveMass f = 0) :
    ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).re ≤ 0 := by
  let g := suzukiIntervalL2RealPositivePart f
  have hgint : Integrable (fun x => g x) volume :=
    (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgnonneg : 0 ≤ᵐ[volume] fun x => g x := by
    filter_upwards [Lp.coeFn_posPart (suzukiIntervalL2RealPart f)] with x hx
    change (0 : ℝ) ≤ g x
    rw [show g x = (Lp.posPart (suzukiIntervalL2RealPart f)) x by rfl, hx]
    exact le_max_right _ _
  have hgzero : (fun x => g x) =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae hgnonneg hgint).mp
    change ∫ x : SuzukiApertureInterval 1,
      suzukiIntervalL2RealPositivePart f x = 0
    rw [← suzukiIntervalPositiveMass_eq_integral]
    exact h
  filter_upwards [hgzero,
    Lp.coeFn_posPart (suzukiIntervalL2RealPart f),
    suzukiIntervalL2RealPart_coeFn f] with x hzero hpos hre
  change g x = 0 at hzero
  rw [show g x = (Lp.posPart (suzukiIntervalL2RealPart f)) x by rfl,
    hpos, hre] at hzero
  exact max_eq_right_iff.mp hzero

theorem ae_realPart_nonneg_of_suzukiIntervalNegativeMass_eq_zero
    {f : SuzukiApertureIntervalL2 1}
    (h : suzukiIntervalNegativeMass f = 0) :
    ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, 0 ≤ (f x).re := by
  let g := suzukiIntervalL2RealNegativePart f
  have hgint : Integrable (fun x => g x) volume :=
    (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgnonneg : 0 ≤ᵐ[volume] fun x => g x := by
    filter_upwards [Lp.coeFn_negPart_eq_max (suzukiIntervalL2RealPart f)] with x hx
    change (0 : ℝ) ≤ g x
    rw [show g x = (Lp.negPart (suzukiIntervalL2RealPart f)) x by rfl, hx]
    exact le_max_right _ _
  have hgzero : (fun x => g x) =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae hgnonneg hgint).mp
    change ∫ x : SuzukiApertureInterval 1,
      suzukiIntervalL2RealNegativePart f x = 0
    rw [← suzukiIntervalNegativeMass_eq_integral]
    exact h
  filter_upwards [hgzero,
    Lp.coeFn_negPart_eq_max (suzukiIntervalL2RealPart f),
    suzukiIntervalL2RealPart_coeFn f] with x hzero hneg hre
  change g x = 0 at hzero
  rw [show g x = (Lp.negPart (suzukiIntervalL2RealPart f)) x by rfl,
    hneg, hre] at hzero
  have hle : -(f x).re ≤ 0 := max_eq_right_iff.mp hzero
  linarith

theorem suzukiRealGroundMinimizer_fixedSign_ae
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        (suzukiLimitingLogFormEmbedding q x).re ≤ 0) ∨
      (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        0 ≤ (suzukiLimitingLogFormEmbedding q x).re) := by
  rcases suzukiRealGroundMinimizer_fixedMassSign q hq hground with hp | hn
  · exact Or.inl (ae_realPart_nonpos_of_suzukiIntervalPositiveMass_eq_zero hp)
  · exact Or.inr (ae_realPart_nonneg_of_suzukiIntervalNegativeMass_eq_zero hn)

/-- Imaginary part on physical `L²`. -/
def suzukiIntervalL2ImagPart :
    SuzukiApertureIntervalL2 1 →L[ℝ]
      Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1)) :=
  Complex.imCLM.compLpL 2 volume

theorem suzukiIntervalL2ImagPart_coeFn (f : SuzukiApertureIntervalL2 1) :
    (suzukiIntervalL2ImagPart f : SuzukiApertureInterval 1 → ℝ) =ᵐ[volume]
      fun x => (f x).im :=
  Complex.imCLM.coeFn_compLpL f

def suzukiLimitingPhysicalImaginary :
    CCMArchimedeanFormDomain suzukiLimitingUnitAperture →L[ℝ]
      Lp ℝ 2 (volume : Measure (SuzukiApertureInterval 1)) :=
  suzukiIntervalL2ImagPart.comp
    (suzukiLimitingLogFormEmbedding.restrictScalars ℝ)

theorem suzukiLimitingPhysicalImaginary_realTestFormVector
    (u : SuzukiRestrictedWeilRealTest 1) :
    suzukiLimitingPhysicalImaginary (suzukiLimitingRealTestFormVector u) = 0 := by
  change suzukiIntervalL2ImagPart
    (suzukiLimitingLogFormEmbedding (suzukiLimitingRealTestFormVector u)) = 0
  apply MeasureTheory.Lp.ext
  filter_upwards [
    suzukiIntervalL2ImagPart_coeFn
      (suzukiLimitingLogFormEmbedding (suzukiLimitingRealTestFormVector u)),
    suzukiLimitingLogFormEmbedding_realTestFormVector_coeFn u,
    MeasureTheory.Lp.coeFn_zero ℝ 2 volume] with x him hreal hzero
  rw [him, hreal, hzero]
  simp

/-- The canonical closed real form domain consists of physically real `L²` vectors. -/
theorem suzukiLimitingPhysicalImaginary_eq_zero_of_mem_realFormDomain
    {q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture}
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    suzukiLimitingPhysicalImaginary q = 0 := by
  have hcore : suzukiLimitingRealCoreSubmodule ≤
      suzukiLimitingPhysicalImaginary.ker := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    exact suzukiLimitingPhysicalImaginary_realTestFormVector u
  exact Submodule.topologicalClosure_minimal _ hcore
    (ContinuousLinearMap.isClosed_ker suzukiLimitingPhysicalImaginary) hq

theorem suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain
    {q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture}
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      (suzukiLimitingLogFormEmbedding q x).im = 0 := by
  have him := suzukiIntervalL2ImagPart_coeFn (suzukiLimitingLogFormEmbedding q)
  have hzero := suzukiLimitingPhysicalImaginary_eq_zero_of_mem_realFormDomain hq
  change suzukiIntervalL2ImagPart (suzukiLimitingLogFormEmbedding q) = 0 at hzero
  have hcoe0 :
      (suzukiIntervalL2ImagPart (suzukiLimitingLogFormEmbedding q) :
        SuzukiApertureInterval 1 → ℝ) =ᵐ[volume] fun _ => 0 := by
    rw [hzero]
    exact MeasureTheory.Lp.coeFn_zero ℝ 2 volume
  filter_upwards [him.symm.trans hcoe0] with x hx
  exact hx

theorem suzukiRealGroundMinimizer_fixedComplexSign_ae
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ((∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        (suzukiLimitingLogFormEmbedding q x).im = 0 ∧
          (suzukiLimitingLogFormEmbedding q x).re ≤ 0) ∨
      (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        (suzukiLimitingLogFormEmbedding q x).im = 0 ∧
          0 ≤ (suzukiLimitingLogFormEmbedding q x).re)) := by
  have him := suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hq
  rcases suzukiRealGroundMinimizer_fixedSign_ae q hq hground with hnonpos | hnonneg
  · exact Or.inl (him.and hnonpos)
  · exact Or.inr (him.and hnonneg)

/-- Orthogonal real and imaginary form directions satisfy the exact Pythagorean identity in the
complete form norm.  This is the coercive estimate that prevents complex-core decompositions from
losing their real or imaginary parts at form closure. -/
theorem norm_sq_suzukiRealFormDomain_add_I_smul
    (r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hr : r ∈ SuzukiLimitingRealFormDomain)
    (hs : s ∈ SuzukiLimitingRealFormDomain) :
    ‖r + Complex.I • s‖ ^ 2 = ‖r‖ ^ 2 + ‖s‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ)]
  have him := inner_im_eq_zero_of_mem_suzukiLimitingRealFormDomain hr hs
  rw [inner_smul_right r s Complex.I]
  norm_num [Complex.mul_re, norm_smul]
  exact him

/-- Every vector in Suzuki's complete complex form domain has real and imaginary parts in the
closed real form domain.  This is an equality in the native form-domain Hilbert space, not merely
an `L²` decomposition. -/
theorem exists_suzukiLimitingRealFormDomain_add_I_smul
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    ∃ r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      r ∈ SuzukiLimitingRealFormDomain ∧
      s ∈ SuzukiLimitingRealFormDomain ∧
      q = r + Complex.I • s := by
  have hqclosure : q ∈ closure suzukiLimitingComplexSmoothCore := by
    rw [dense_suzukiLimitingComplexSmoothCore.closure_eq]
    exact mem_univ q
  obtain ⟨z, hzcore, hztend⟩ :=
    mem_closure_iff_seq_limit.mp hqclosure
  have hsource : ∀ n : ℕ, ∃ u : SuzukiRestrictedWeilComplexTest 1,
      suzukiLimitingComplexCoreFormVector u = z n := by
    intro n
    exact hzcore n
  choose u hu using hsource
  let r : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture := fun n =>
    suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
      (suzukiRestrictedWeilRealTestToCore
        GaloisForLFunctions.RHTower.suzukiUnitAperture (u n).realPart)
  let s : ℕ → CCMArchimedeanFormDomain suzukiLimitingUnitAperture := fun n =>
    suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
      (suzukiRestrictedWeilRealTestToCore
        GaloisForLFunctions.RHTower.suzukiUnitAperture (u n).imagPart)
  have hzsplit (n : ℕ) : z n = r n + Complex.I • s n := by
    rw [← hu n]
    exact suzukiLimitingComplexCoreFormVector_eq_real_add_I_imag (u n)
  have hrmem (n : ℕ) : r n ∈ SuzukiLimitingRealFormDomain := by
    apply suzukiLimitingRealCoreSubmodule.le_topologicalClosure
    exact suzukiRestrictedWeilCoreCCMFormVector_mem_realCoreSubmodule _
  have hsmem (n : ℕ) : s n ∈ SuzukiLimitingRealFormDomain := by
    apply suzukiLimitingRealCoreSubmodule.le_topologicalClosure
    exact suzukiRestrictedWeilCoreCCMFormVector_mem_realCoreSubmodule _
  have hzcauchy : CauchySeq z := hztend.cauchySeq
  have hrcauchy : CauchySeq r := by
    rw [Metric.cauchySeq_iff] at hzcauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hzcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdiff : z m - z n =
        (r m - r n) + Complex.I • (s m - s n) := by
      rw [hzsplit m, hzsplit n]
      module
    have hsq := norm_sq_suzukiRealFormDomain_add_I_smul
      (r m - r n) (s m - s n)
      (SuzukiLimitingRealFormDomain.sub_mem (hrmem m) (hrmem n))
      (SuzukiLimitingRealFormDomain.sub_mem (hsmem m) (hsmem n))
    have hsqle : ‖r m - r n‖ ^ 2 ≤ ‖z m - z n‖ ^ 2 := by
      rw [hdiff, hsq]
      nlinarith [sq_nonneg ‖s m - s n‖]
    have hle : ‖r m - r n‖ ≤ ‖z m - z n‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsqle
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hle (by simpa [dist_eq_norm] using hN m hm n hn)
  have hscauchy : CauchySeq s := by
    rw [Metric.cauchySeq_iff] at hzcauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hzcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdiff : z m - z n =
        (r m - r n) + Complex.I • (s m - s n) := by
      rw [hzsplit m, hzsplit n]
      module
    have hsq := norm_sq_suzukiRealFormDomain_add_I_smul
      (r m - r n) (s m - s n)
      (SuzukiLimitingRealFormDomain.sub_mem (hrmem m) (hrmem n))
      (SuzukiLimitingRealFormDomain.sub_mem (hsmem m) (hsmem n))
    have hsqle : ‖s m - s n‖ ^ 2 ≤ ‖z m - z n‖ ^ 2 := by
      rw [hdiff, hsq]
      nlinarith [sq_nonneg ‖r m - r n‖]
    have hle : ‖s m - s n‖ ≤ ‖z m - z n‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsqle
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hle (by simpa [dist_eq_norm] using hN m hm n hn)
  obtain ⟨r₀, hrtend⟩ := cauchySeq_tendsto_of_complete hrcauchy
  obtain ⟨s₀, hstend⟩ := cauchySeq_tendsto_of_complete hscauchy
  have hr₀ : r₀ ∈ SuzukiLimitingRealFormDomain :=
    isClosed_suzukiLimitingRealFormDomain.mem_of_tendsto hrtend
      (Filter.Eventually.of_forall hrmem)
  have hs₀ : s₀ ∈ SuzukiLimitingRealFormDomain :=
    isClosed_suzukiLimitingRealFormDomain.mem_of_tendsto hstend
      (Filter.Eventually.of_forall hsmem)
  have hsum : Tendsto z atTop (nhds (r₀ + Complex.I • s₀)) := by
    have hraw := hrtend.add (hstend.const_smul Complex.I)
    convert hraw using 1
    funext n
    exact hzsplit n
  refine ⟨r₀, s₀, hr₀, hs₀, ?_⟩
  exact tendsto_nhds_unique hztend hsum

theorem suzukiLimitingLogClosedForm_realDomain_left_core_im_eq_zero
    (x : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (u : SuzukiRestrictedWeilCore 1) :
    (suzukiLimitingLogClosedForm x
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)).im = 0 := by
  change x ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hx
  obtain ⟨z, hzcore, hztend⟩ := mem_closure_iff_seq_limit.mp hx
  have hclosed : IsClosed {w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture |
      (suzukiLimitingLogClosedForm w
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u)).im = 0} := by
    apply isClosed_eq
    · apply Complex.continuous_im.comp
      unfold suzukiLimitingLogClosedForm
      exact ((continuous_id : Continuous (fun w :
          CCMArchimedeanFormDomain suzukiLimitingUnitAperture => w)).inner
            (𝕜 := ℂ) continuous_const).add
        ((suzukiLimitingLogBoundedRemainder.continuous.comp
            suzukiLimitingLogFormEmbedding.continuous).inner
          (𝕜 := ℂ) continuous_const)
    · fun_prop
  apply hclosed.mem_of_tendsto hztend
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨t, ht⟩ := hzcore n
  rw [← ht]
  exact suzukiLimitingLogClosedForm_realCore_mixed_im_eq_zero
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t) u

/-- The closed limiting form is real on the entire closed real domain. -/
theorem suzukiLimitingLogClosedForm_realDomain_mixed_im_eq_zero
    (x y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (hy : y ∈ SuzukiLimitingRealFormDomain) :
    (suzukiLimitingLogClosedForm x y).im = 0 := by
  change y ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hy
  obtain ⟨z, hzcore, hztend⟩ := mem_closure_iff_seq_limit.mp hy
  have hclosed : IsClosed {w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture |
      (suzukiLimitingLogClosedForm x w).im = 0} := by
    apply isClosed_eq
    · apply Complex.continuous_im.comp
      unfold suzukiLimitingLogClosedForm
      exact ((continuous_const : Continuous (fun _ :
          CCMArchimedeanFormDomain suzukiLimitingUnitAperture => x)).inner
            (𝕜 := ℂ) continuous_id).add
        ((continuous_const : Continuous (fun _ :
            CCMArchimedeanFormDomain suzukiLimitingUnitAperture =>
              suzukiLimitingLogBoundedRemainder
                (suzukiLimitingLogFormEmbedding x))).inner
          (𝕜 := ℂ) suzukiLimitingLogFormEmbedding.continuous)
    · fun_prop
  apply hclosed.mem_of_tendsto hztend
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨t, ht⟩ := hzcore n
  rw [← ht]
  exact suzukiLimitingLogClosedForm_realDomain_left_core_im_eq_zero x hx
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t)

/-- Exact closed-form energy splitting across the real/imaginary decomposition. -/
theorem suzukiLimitingLogClosedForm_real_add_I_real
    (r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hr : r ∈ SuzukiLimitingRealFormDomain)
    (hs : s ∈ SuzukiLimitingRealFormDomain) :
    suzukiLimitingLogClosedForm (r + I • s) (r + I • s) =
      suzukiLimitingLogClosedForm r r + suzukiLimitingLogClosedForm s s := by
  have hsymm : suzukiLimitingLogClosedForm r s =
      suzukiLimitingLogClosedForm s r := by
    rw [← star_suzukiLimitingLogClosedForm_swap]
    exact Complex.conj_eq_iff_im.mpr
      (suzukiLimitingLogClosedForm_realDomain_mixed_im_eq_zero s r hs hr)
  simp only [suzukiLimitingLogClosedForm_add_left,
    suzukiLimitingLogClosedForm_add_right,
    suzukiLimitingLogClosedForm_smul_left,
    suzukiLimitingLogClosedForm_smul_right]
  change suzukiLimitingLogClosedForm r r +
      star I * suzukiLimitingLogClosedForm s r +
      I * (suzukiLimitingLogClosedForm r s +
        star I * suzukiLimitingLogClosedForm s s) =
    suzukiLimitingLogClosedForm r r + suzukiLimitingLogClosedForm s s
  have hI : star I = -I := Complex.conj_I
  rw [hI, hsymm]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem inner_suzukiLimitingLogFormEmbedding_realDomain_left_core_im_eq_zero
    (x : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (u : SuzukiRestrictedWeilCore 1) :
    (inner ℂ (suzukiLimitingLogFormEmbedding x)
      (suzukiLimitingLogFormEmbedding
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u))).im = 0 := by
  change x ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hx
  obtain ⟨z, hzcore, hztend⟩ := mem_closure_iff_seq_limit.mp hx
  have hclosed : IsClosed {w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture |
      (inner ℂ (suzukiLimitingLogFormEmbedding w)
        (suzukiLimitingLogFormEmbedding
          (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u))).im = 0} := by
    apply isClosed_eq
    · exact Complex.continuous_im.comp
        (suzukiLimitingLogFormEmbedding.continuous.inner
          (𝕜 := ℂ) continuous_const)
    · fun_prop
  apply hclosed.mem_of_tendsto hztend
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨t, ht⟩ := hzcore n
  rw [← ht]
  change (inner ℂ
    (suzukiLimitingLogFormEmbedding
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
        (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t)))
    (suzukiLimitingLogFormEmbedding
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture u))).im = 0
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding,
    ← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  exact inner_suzukiLimitingCoreIntervalVector_mixed_im_eq_zero
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t) u

/-- Physical `L²` inner products of two closed real-form vectors are real. -/
theorem inner_suzukiLimitingLogFormEmbedding_realDomain_mixed_im_eq_zero
    (x y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (hy : y ∈ SuzukiLimitingRealFormDomain) :
    (inner ℂ (suzukiLimitingLogFormEmbedding x)
      (suzukiLimitingLogFormEmbedding y)).im = 0 := by
  change y ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hy
  obtain ⟨z, hzcore, hztend⟩ := mem_closure_iff_seq_limit.mp hy
  have hclosed : IsClosed {w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture |
      (inner ℂ (suzukiLimitingLogFormEmbedding x)
        (suzukiLimitingLogFormEmbedding w)).im = 0} := by
    apply isClosed_eq
    · exact Complex.continuous_im.comp
        ((continuous_const : Continuous (fun _ :
          CCMArchimedeanFormDomain suzukiLimitingUnitAperture =>
            suzukiLimitingLogFormEmbedding x)).inner
          (𝕜 := ℂ) suzukiLimitingLogFormEmbedding.continuous)
    · fun_prop
  apply hclosed.mem_of_tendsto hztend
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨t, ht⟩ := hzcore n
  rw [← ht]
  exact inner_suzukiLimitingLogFormEmbedding_realDomain_left_core_im_eq_zero x hx
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t)

/-- Exact physical-mass splitting across the closed real/imaginary decomposition. -/
theorem norm_sq_suzukiLimitingLogFormEmbedding_real_add_I_real
    (r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hr : r ∈ SuzukiLimitingRealFormDomain)
    (hs : s ∈ SuzukiLimitingRealFormDomain) :
    ‖suzukiLimitingLogFormEmbedding (r + I • s)‖ ^ 2 =
      ‖suzukiLimitingLogFormEmbedding r‖ ^ 2 +
        ‖suzukiLimitingLogFormEmbedding s‖ ^ 2 := by
  rw [map_add, map_smul, norm_add_sq (𝕜 := ℂ)]
  have him := inner_suzukiLimitingLogFormEmbedding_realDomain_mixed_im_eq_zero
    r s hr hs
  rw [inner_smul_right]
  norm_num [Complex.mul_re, norm_smul]
  exact him

/-- Real polarization of Suzuki's form after subtracting the exact ground floor. -/
def suzukiGroundShiftedRealBilinForm :
    LinearMap.BilinForm ℝ
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :=
  LinearMap.mk₂ ℝ
    (fun u v => (suzukiLimitingLogClosedForm u v).re -
      suzukiLimitingLogOperatorGroundEnergy *
        (inner ℂ (suzukiLimitingLogFormEmbedding u)
          (suzukiLimitingLogFormEmbedding v)).re)
    (by
      intro u₁ u₂ v
      rw [suzukiLimitingLogClosedForm_add_left, map_add, inner_add_left]
      simp only [Complex.add_re]
      ring)
    (by
      intro c u v
      change (suzukiLimitingLogClosedForm ((c : ℂ) • u) v).re -
          suzukiLimitingLogOperatorGroundEnergy *
            (inner ℂ (suzukiLimitingLogFormEmbedding ((c : ℂ) • u))
              (suzukiLimitingLogFormEmbedding v)).re =
        c * ((suzukiLimitingLogClosedForm u v).re -
          suzukiLimitingLogOperatorGroundEnergy *
            (inner ℂ (suzukiLimitingLogFormEmbedding u)
              (suzukiLimitingLogFormEmbedding v)).re)
      rw [suzukiLimitingLogClosedForm_smul_left, map_smul, inner_smul_left]
      norm_num [Complex.mul_re]
      ring)
    (by
      intro u v₁ v₂
      rw [suzukiLimitingLogClosedForm_add_right, map_add, inner_add_right]
      simp only [Complex.add_re]
      ring)
    (by
      intro c u v
      change (suzukiLimitingLogClosedForm u ((c : ℂ) • v)).re -
          suzukiLimitingLogOperatorGroundEnergy *
            (inner ℂ (suzukiLimitingLogFormEmbedding u)
              (suzukiLimitingLogFormEmbedding ((c : ℂ) • v))).re =
        c * ((suzukiLimitingLogClosedForm u v).re -
          suzukiLimitingLogOperatorGroundEnergy *
            (inner ℂ (suzukiLimitingLogFormEmbedding u)
              (suzukiLimitingLogFormEmbedding v)).re)
      rw [suzukiLimitingLogClosedForm_smul_right, map_smul, inner_smul_right]
      norm_num [Complex.mul_re]
      ring)

theorem suzukiGroundShiftedRealBilinForm_apply
    (u v : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiGroundShiftedRealBilinForm u v =
      (suzukiLimitingLogClosedForm u v).re -
        suzukiLimitingLogOperatorGroundEnergy *
          (inner ℂ (suzukiLimitingLogFormEmbedding u)
            (suzukiLimitingLogFormEmbedding v)).re := rfl

theorem suzukiGroundShiftedRealBilinForm_nonneg
    (u : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    0 ≤ suzukiGroundShiftedRealBilinForm u u := by
  rw [suzukiGroundShiftedRealBilinForm_apply, inner_self_eq_norm_sq_to_K]
  norm_num [Complex.mul_re, pow_two]
  simpa [pow_two] using
    suzukiLimitingLogOperatorGroundEnergy_mul_formNorm_sq_le u

theorem suzukiGroundShiftedRealBilinForm_isSymm :
    LinearMap.IsSymm suzukiGroundShiftedRealBilinForm := by
  apply LinearMap.IsSymm.mk
  intro u v
  simp only [RingHom.id_apply]
  rw [suzukiGroundShiftedRealBilinForm_apply,
    suzukiGroundShiftedRealBilinForm_apply]
  have hform := congrArg Complex.re
    (star_suzukiLimitingLogClosedForm_swap u v)
  have hinner := congrArg Complex.re
    (inner_conj_symm (suzukiLimitingLogFormEmbedding v)
      (suzukiLimitingLogFormEmbedding u))
  simp only [Complex.star_def, Complex.conj_re] at hform hinner
  rw [hform, hinner]

/-- Equality at the ground Rayleigh floor annihilates the full real polarized shifted form. -/
theorem suzukiGroundShiftedRealBilinForm_eq_zero_left
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ∀ v, suzukiGroundShiftedRealBilinForm q v = 0 := by
  have hdiag : suzukiGroundShiftedRealBilinForm q q = 0 := by
    rw [suzukiGroundShiftedRealBilinForm_apply, inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re, pow_two]
    nlinarith
  have hker := (suzukiGroundShiftedRealBilinForm.apply_apply_same_eq_zero_iff
    suzukiGroundShiftedRealBilinForm_nonneg
    suzukiGroundShiftedRealBilinForm_isSymm).mp hdiag
  intro v
  exact DFunLike.congr_fun (LinearMap.mem_ker.mp hker) v

/-- A ground minimizer satisfies the full complex weak eigen-equation against every form vector. -/
theorem suzukiGroundShiftedComplexForm_eq_zero_left
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ∀ v, suzukiLimitingLogClosedForm q v =
      (suzukiLimitingLogOperatorGroundEnergy : ℂ) *
        inner ℂ (suzukiLimitingLogFormEmbedding q)
          (suzukiLimitingLogFormEmbedding v) := by
  intro v
  have hre := suzukiGroundShiftedRealBilinForm_eq_zero_left q hground v
  rw [suzukiGroundShiftedRealBilinForm_apply] at hre
  have him := suzukiGroundShiftedRealBilinForm_eq_zero_left q hground (I • v)
  rw [suzukiGroundShiftedRealBilinForm_apply,
    suzukiLimitingLogClosedForm_smul_right, map_smul,
    inner_smul_right] at him
  apply Complex.ext
  · norm_num [Complex.mul_re]
    nlinarith
  · norm_num [Complex.mul_re] at him ⊢
    nlinarith

/-- Every closed-form ground minimizer lies in the represented operator domain and is a literal
bottom eigenvector. -/
theorem suzukiFormGroundMinimizer_exists_groundEigenstate
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ∃ hmem : suzukiLimitingLogFormEmbedding q ∈ suzukiLimitingLogOperator.domain,
      suzukiLimitingLogOperator
          ⟨suzukiLimitingLogFormEmbedding q, hmem⟩ =
        (suzukiLimitingLogOperatorGroundEnergy : ℂ) •
          suzukiLimitingLogFormEmbedding q := by
  apply boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    suzukiLimitingLogFormEmbedding
    suzukiLimitingLogBoundedRemainder
    suzukiLimitingLogBoundedRemainder_isSelfAdjoint
    suzukiLimitingLogFormEmbedding_injective
    denseRange_suzukiLimitingLogFormEmbedding
    q ((suzukiLimitingLogOperatorGroundEnergy : ℂ) •
      suzukiLimitingLogFormEmbedding q)
  intro v
  change suzukiLimitingLogClosedForm q v =
    inner ℂ ((suzukiLimitingLogOperatorGroundEnergy : ℂ) •
      suzukiLimitingLogFormEmbedding q) (suzukiLimitingLogFormEmbedding v)
  rw [suzukiGroundShiftedComplexForm_eq_zero_left q hground v,
    inner_smul_left]
  have hstar : (starRingEnd ℂ)
      (suzukiLimitingLogOperatorGroundEnergy : ℂ) =
        (suzukiLimitingLogOperatorGroundEnergy : ℂ) :=
    Complex.conj_ofReal _
  rw [hstar]

/-- Both closed real components of a complex ground minimizer attain the same exact floor. -/
theorem suzukiFormGroundMinimizer_real_components_ground
    (q r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hr : r ∈ SuzukiLimitingRealFormDomain)
    (hs : s ∈ SuzukiLimitingRealFormDomain)
    (hq : q = r + I • s)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ((suzukiLimitingLogClosedForm r r).re =
        suzukiLimitingLogOperatorGroundEnergy *
          ‖suzukiLimitingLogFormEmbedding r‖ ^ 2) ∧
      ((suzukiLimitingLogClosedForm s s).re =
        suzukiLimitingLogOperatorGroundEnergy *
          ‖suzukiLimitingLogFormEmbedding s‖ ^ 2) := by
  have hsum : (suzukiLimitingLogClosedForm r r).re +
        (suzukiLimitingLogClosedForm s s).re =
      suzukiLimitingLogOperatorGroundEnergy *
        (‖suzukiLimitingLogFormEmbedding r‖ ^ 2 +
          ‖suzukiLimitingLogFormEmbedding s‖ ^ 2) := by
    rw [hq, suzukiLimitingLogClosedForm_real_add_I_real r s hr hs,
      norm_sq_suzukiLimitingLogFormEmbedding_real_add_I_real r s hr hs] at hground
    simpa only [Complex.add_re] using hground
  have hrfloor := suzukiLimitingLogOperatorGroundEnergy_mul_formNorm_sq_le r
  have hsfloor := suzukiLimitingLogOperatorGroundEnergy_mul_formNorm_sq_le s
  constructor <;> nlinarith

/-- Ground minimizers are closed under real orthogonalization. -/
theorem suzukiFormGroundMinimizer_sub_real_smul
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hrground : (suzukiLimitingLogClosedForm r r).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding r‖ ^ 2)
    (c : ℝ) :
    (suzukiLimitingLogClosedForm (r - c • q) (r - c • q)).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding (r - c • q)‖ ^ 2 := by
  have hqzero := suzukiGroundShiftedRealBilinForm_eq_zero_left q hqground
  have hrzero := suzukiGroundShiftedRealBilinForm_eq_zero_left r hrground
  have hzero : suzukiGroundShiftedRealBilinForm (r - c • q) (r - c • q) = 0 := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hrzero, hqzero, mul_zero, sub_zero]
  rw [suzukiGroundShiftedRealBilinForm_apply,
    inner_self_eq_norm_sq_to_K] at hzero
  norm_num [Complex.mul_re, pow_two] at hzero
  have hmap : suzukiLimitingLogFormEmbedding (r - c • q) =
      suzukiLimitingLogFormEmbedding r - c • suzukiLimitingLogFormEmbedding q := by
    change suzukiLimitingLogFormEmbedding (r - (c : ℂ) • q) =
      suzukiLimitingLogFormEmbedding r - (c : ℂ) • suzukiLimitingLogFormEmbedding q
    rw [map_sub, map_smul]
  rw [← hmap] at hzero
  simpa [pow_two] using sub_eq_zero.mp hzero

theorem inner_re_nonneg_of_ae_real_nonneg
    (f g : SuzukiApertureIntervalL2 1)
    (hfreal : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).im = 0)
    (hgreal : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (g x).im = 0)
    (hf : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, 0 ≤ (f x).re)
    (hg : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, 0 ≤ (g x).re) :
    0 ≤ (inner ℂ f g).re := by
  rw [MeasureTheory.L2.inner_def]
  change 0 ≤ RCLike.re
    (∫ x : SuzukiApertureInterval 1, inner ℂ (f x) (g x))
  rw [← integral_re (MeasureTheory.L2.integrable_inner f g)]
  apply integral_nonneg_of_ae
  filter_upwards [hfreal, hgreal, hf, hg] with x hfri hgri hfr hgr
  change 0 ≤ (inner ℂ (f x) (g x)).re
  simp [RCLike.inner_apply, Complex.mul_re, hfri, hgri]
  exact mul_nonneg hgr hfr

theorem inner_re_nonpos_of_ae_real_nonpos_nonneg
    (f g : SuzukiApertureIntervalL2 1)
    (hfreal : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).im = 0)
    (hgreal : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (g x).im = 0)
    (hf : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).re ≤ 0)
    (hg : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, 0 ≤ (g x).re) :
    (inner ℂ f g).re ≤ 0 := by
  have hnegReal : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, ((-f) x).im = 0 := by
    filter_upwards [hfreal, MeasureTheory.Lp.coeFn_neg f] with x hfri hneg
    rw [hneg]
    simp [hfri]
  have hnegNonneg : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      0 ≤ ((-f) x).re := by
    filter_upwards [hf, MeasureTheory.Lp.coeFn_neg f] with x hfx hneg
    rw [hneg]
    simp
    exact hfx
  have h := inner_re_nonneg_of_ae_real_nonneg (-f) g
    hnegReal hgreal hnegNonneg hg
  rw [inner_neg_left, Complex.neg_re] at h
  linarith

/-- Two nonzero nonnegative real ground minimizers cannot be physically orthogonal.  Their
difference would be another ground minimizer, but its overlaps force both signs. -/
theorem not_orthogonal_nonzero_nonnegative_suzukiRealGroundMinimizers
    (q w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hwreal : w ∈ SuzukiLimitingRealFormDomain)
    (hqground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hwground : (suzukiLimitingLogClosedForm w w).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding w‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0)
    (hwne : suzukiLimitingLogFormEmbedding w ≠ 0)
    (hqnonneg : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      0 ≤ (suzukiLimitingLogFormEmbedding q x).re)
    (hwnonneg : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      0 ≤ (suzukiLimitingLogFormEmbedding w x).re)
    (horth : inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding w) = 0) : False := by
  let d := q - w
  have hdreal : d ∈ SuzukiLimitingRealFormDomain :=
    SuzukiLimitingRealFormDomain.sub_mem hqreal hwreal
  have hdground : (suzukiLimitingLogClosedForm d d).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding d‖ ^ 2 := by
    have h := suzukiFormGroundMinimizer_sub_real_smul
      w q hwground hqground 1
    simpa only [one_smul] using h
  have hqimag :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hqreal
  have hwimag :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hwreal
  have hdimag :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hdreal
  have horthRev : inner ℂ (suzukiLimitingLogFormEmbedding w)
      (suzukiLimitingLogFormEmbedding q) = 0 := by
    rw [← inner_conj_symm]
    simp [horth]
  have hdembed : suzukiLimitingLogFormEmbedding d =
      suzukiLimitingLogFormEmbedding q - suzukiLimitingLogFormEmbedding w := by
    dsimp only [d]
    rw [map_sub]
  have hposOverlap : 0 < (inner ℂ (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding q)).re := by
    rw [hdembed, inner_sub_left, horthRev, sub_zero,
      inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re, pow_two]
    exact hqne
  have hnegOverlap : (inner ℂ (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding w)).re < 0 := by
    rw [hdembed, inner_sub_left, horth, zero_sub,
      inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re, pow_two]
    exact hwne
  rcases suzukiRealGroundMinimizer_fixedSign_ae d hdreal hdground with
      hdnonpos | hdnonneg
  · have hle := inner_re_nonpos_of_ae_real_nonpos_nonneg
      (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding q)
      hdimag hqimag hdnonpos hqnonneg
    linarith
  · have hge := inner_re_nonneg_of_ae_real_nonneg
      (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding w)
      hdimag hwimag hdnonneg hwnonneg
    linarith

theorem suzukiFormGroundMinimizer_neg
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    (suzukiLimitingLogClosedForm (-q) (-q)).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding (-q)‖ ^ 2 := by
  have hform : suzukiLimitingLogClosedForm (-q) (-q) =
      suzukiLimitingLogClosedForm q q := by
    rw [show -q = (-1 : ℂ) • q by simp]
    rw [suzukiLimitingLogClosedForm_smul_left,
      suzukiLimitingLogClosedForm_smul_right]
    norm_num
  rw [hform, map_neg, norm_neg]
  exact hground

theorem exists_nonnegative_orientation_suzukiRealGroundMinimizer
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hqground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0) :
    ∃ qpos : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      qpos ∈ SuzukiLimitingRealFormDomain ∧
      (suzukiLimitingLogClosedForm qpos qpos).re =
        suzukiLimitingLogOperatorGroundEnergy *
          ‖suzukiLimitingLogFormEmbedding qpos‖ ^ 2 ∧
      suzukiLimitingLogFormEmbedding qpos ≠ 0 ∧
      (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        0 ≤ (suzukiLimitingLogFormEmbedding qpos x).re) ∧
      (qpos = q ∨ qpos = -q) := by
  rcases suzukiRealGroundMinimizer_fixedSign_ae q hqreal hqground with
      hnonpos | hnonneg
  · refine ⟨-q, SuzukiLimitingRealFormDomain.neg_mem hqreal,
      suzukiFormGroundMinimizer_neg q hqground, ?_, ?_, Or.inr rfl⟩
    · simpa using hqne
    · rw [map_neg]
      filter_upwards [MeasureTheory.Lp.coeFn_neg
        (suzukiLimitingLogFormEmbedding q), hnonpos] with x hneg hx
      rw [hneg]
      simp
      exact hx
  · exact ⟨q, hqreal, hqground, hqne, hnonneg, Or.inl rfl⟩

/-- Arbitrary nonzero real ground minimizers cannot be physically orthogonal. -/
theorem not_orthogonal_nonzero_suzukiRealGroundMinimizers
    (q w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hwreal : w ∈ SuzukiLimitingRealFormDomain)
    (hqground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hwground : (suzukiLimitingLogClosedForm w w).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding w‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0)
    (hwne : suzukiLimitingLogFormEmbedding w ≠ 0)
    (horth : inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding w) = 0) : False := by
  obtain ⟨qpos, hqposReal, hqposGround, hqposNe, hqposNonneg, hqorient⟩ :=
    exists_nonnegative_orientation_suzukiRealGroundMinimizer
      q hqreal hqground hqne
  obtain ⟨wpos, hwposReal, hwposGround, hwposNe, hwposNonneg, hworient⟩ :=
    exists_nonnegative_orientation_suzukiRealGroundMinimizer
      w hwreal hwground hwne
  have horthPos : inner ℂ (suzukiLimitingLogFormEmbedding qpos)
      (suzukiLimitingLogFormEmbedding wpos) = 0 := by
    rcases hqorient with rfl | rfl <;>
      rcases hworient with rfl | rfl <;>
      simp [horth]
  exact not_orthogonal_nonzero_nonnegative_suzukiRealGroundMinimizers
    qpos wpos hqposReal hwposReal hqposGround hwposGround hqposNe hwposNe
    hqposNonneg hwposNonneg horthPos

/-- The real closed-form ground space is a single real line. -/
theorem exists_real_smul_eq_of_suzukiRealGroundMinimizers
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hrreal : r ∈ SuzukiLimitingRealFormDomain)
    (hqground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hrground : (suzukiLimitingLogClosedForm r r).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding r‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0) :
    ∃ c : ℝ, r = c • q := by
  let c : ℝ :=
    (inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding r)).re /
      ‖suzukiLimitingLogFormEmbedding q‖ ^ 2
  let w := r - c • q
  have hwreal : w ∈ SuzukiLimitingRealFormDomain :=
    SuzukiLimitingRealFormDomain.sub_mem hrreal
      (SuzukiLimitingRealFormDomain.smul_mem c hqreal)
  have hwground : (suzukiLimitingLogClosedForm w w).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding w‖ ^ 2 :=
    suzukiFormGroundMinimizer_sub_real_smul q r hqground hrground c
  have hinnerReal :=
    inner_suzukiLimitingLogFormEmbedding_realDomain_mixed_im_eq_zero
      q r hqreal hrreal
  have hnormSqNe : ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hqne)
  have hwembed : suzukiLimitingLogFormEmbedding w =
      suzukiLimitingLogFormEmbedding r -
        (c : ℂ) • suzukiLimitingLogFormEmbedding q := by
    dsimp only [w]
    change suzukiLimitingLogFormEmbedding (r - (c : ℂ) • q) = _
    rw [map_sub, map_smul]
  have horth : inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding w) = 0 := by
    rw [hwembed, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    let z := inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding r)
    let N := ‖suzukiLimitingLogFormEmbedding q‖ ^ 2
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [z, Complex.ofReal_im] using hinnerReal
    have hcN : c * N = z.re := by
      dsimp only [c, N, z]
      exact div_mul_cancel₀ _ hnormSqNe
    have hcastN : (‖suzukiLimitingLogFormEmbedding q‖ : ℂ) ^ 2 =
        (N : ℂ) := by
      dsimp only [N]
      push_cast
      rfl
    change z - (c : ℂ) * (‖suzukiLimitingLogFormEmbedding q‖ : ℂ) ^ 2 = 0
    rw [hcastN, hzreal]
    rw [← hcN]
    push_cast
    ring
  by_cases hwzero : suzukiLimitingLogFormEmbedding w = 0
  · have wz : w = 0 := suzukiLimitingLogFormEmbedding_injective
      (hwzero.trans (map_zero suzukiLimitingLogFormEmbedding).symm)
    refine ⟨c, ?_⟩
    exact sub_eq_zero.mp wz
  · exact (not_orthogonal_nonzero_suzukiRealGroundMinimizers
      q w hqreal hwreal hqground hwground hqne hwzero horth).elim

/-- The attained bottom eigenstate supplies a nonzero generator in the canonical closed real form
domain. -/
theorem exists_nonzero_suzukiRealGroundMinimizer :
    ∃ q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      q ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding q ≠ 0 ∧
      (suzukiLimitingLogClosedForm q q).re =
        suzukiLimitingLogOperatorGroundEnergy *
          ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
  obtain ⟨x, hxne, hx⟩ := suzukiLimitingLogOperator_exists_groundEigenstate
  obtain ⟨q, hqrep, hqform⟩ := suzukiLimitingLogOperator_exists_formLift x
  have hinner :
      (inner ℂ (suzukiLimitingLogOperator x)
        (x : SuzukiApertureIntervalL2 1)).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖(x : SuzukiApertureIntervalL2 1)‖ ^ 2 := by
    rw [hx, inner_smul_left]
    rw [show (starRingEnd ℂ)
      (suzukiLimitingLogOperatorGroundEnergy : ℂ) =
        (suzukiLimitingLogOperatorGroundEnergy : ℂ) by
          exact Complex.conj_ofReal _]
    rw [inner_self_eq_norm_sq_to_K]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simp [pow_two, Complex.mul_re]
  have hqground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
    calc
      _ = (inner ℂ (suzukiLimitingLogOperator x)
          (x : SuzukiApertureIntervalL2 1)).re := congrArg Complex.re hqform
      _ = suzukiLimitingLogOperatorGroundEnergy *
          ‖(x : SuzukiApertureIntervalL2 1)‖ ^ 2 := hinner
      _ = _ := by rw [hqrep]
  obtain ⟨r, s, hrreal, hsreal, hqsplit⟩ :=
    exists_suzukiLimitingRealFormDomain_add_I_smul q
  obtain ⟨hrground, hsground⟩ :=
    suzukiFormGroundMinimizer_real_components_ground
      q r s hrreal hsreal hqsplit hqground
  have hqembed : suzukiLimitingLogFormEmbedding q =
      suzukiLimitingLogFormEmbedding r +
        I • suzukiLimitingLogFormEmbedding s := by
    rw [hqsplit, map_add, map_smul]
  by_cases hrzero : suzukiLimitingLogFormEmbedding r = 0
  · have hsne : suzukiLimitingLogFormEmbedding s ≠ 0 := by
      intro hszero
      apply hxne
      rw [← hqrep, hqembed, hrzero, hszero]
      simp
    exact ⟨s, hsreal, hsne, hsground⟩
  · exact ⟨r, hrreal, hrzero, hrground⟩

/-- Every complex closed-form ground minimizer is a complex multiple of any nonzero real ground
minimizer. -/
theorem exists_complex_smul_eq_of_suzukiFormGroundMinimizers
    (q p : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hqground : (suzukiLimitingLogClosedForm q q).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0)
    (hpground : (suzukiLimitingLogClosedForm p p).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2) :
    ∃ c : ℂ, p = c • q := by
  obtain ⟨r, s, hrreal, hsreal, hpsplit⟩ :=
    exists_suzukiLimitingRealFormDomain_add_I_smul p
  obtain ⟨hrground, hsground⟩ :=
    suzukiFormGroundMinimizer_real_components_ground
      p r s hrreal hsreal hpsplit hpground
  obtain ⟨a, hra⟩ := exists_real_smul_eq_of_suzukiRealGroundMinimizers
    q r hqreal hrreal hqground hrground hqne
  obtain ⟨b, hsb⟩ := exists_real_smul_eq_of_suzukiRealGroundMinimizers
    q s hqreal hsreal hqground hsground hqne
  refine ⟨(a : ℂ) + I * (b : ℂ), ?_⟩
  rw [hpsplit, hra, hsb]
  change (a : ℂ) • q + I • ((b : ℂ) • q) =
    ((a : ℂ) + I * (b : ℂ)) • q
  module

/-- **Suzuki ground-state simplicity.**  The bottom eigenspace of the represented limiting
logarithmic operator is a single complex line.  No irreducibility or positivity hypothesis is
left as a premise. -/
theorem suzukiLimitingLogOperator_groundEigenspace_simple :
    ∃ e : suzukiLimitingLogOperator.domain,
      (e : SuzukiApertureIntervalL2 1) ≠ 0 ∧
      suzukiLimitingLogOperator e =
        (suzukiLimitingLogOperatorGroundEnergy : ℂ) •
          (e : SuzukiApertureIntervalL2 1) ∧
      ∀ x : suzukiLimitingLogOperator.domain,
        suzukiLimitingLogOperator x =
          (suzukiLimitingLogOperatorGroundEnergy : ℂ) •
            (x : SuzukiApertureIntervalL2 1) →
        ∃ c : ℂ, (x : SuzukiApertureIntervalL2 1) =
          c • (e : SuzukiApertureIntervalL2 1) := by
  obtain ⟨q, hqreal, hqne, hqground⟩ :=
    exists_nonzero_suzukiRealGroundMinimizer
  obtain ⟨hqmem, hqeigen⟩ :=
    suzukiFormGroundMinimizer_exists_groundEigenstate q hqground
  let e : suzukiLimitingLogOperator.domain :=
    ⟨suzukiLimitingLogFormEmbedding q, hqmem⟩
  refine ⟨e, hqne, hqeigen, ?_⟩
  intro x hx
  obtain ⟨p, hprep, hpform⟩ := suzukiLimitingLogOperator_exists_formLift x
  have hinner :
      (inner ℂ (suzukiLimitingLogOperator x)
        (x : SuzukiApertureIntervalL2 1)).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖(x : SuzukiApertureIntervalL2 1)‖ ^ 2 := by
    rw [hx, inner_smul_left]
    rw [show (starRingEnd ℂ)
      (suzukiLimitingLogOperatorGroundEnergy : ℂ) =
        (suzukiLimitingLogOperatorGroundEnergy : ℂ) by
          exact Complex.conj_ofReal _]
    rw [inner_self_eq_norm_sq_to_K]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simp [pow_two, Complex.mul_re]
  have hpground : (suzukiLimitingLogClosedForm p p).re =
      suzukiLimitingLogOperatorGroundEnergy *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2 := by
    calc
      _ = (inner ℂ (suzukiLimitingLogOperator x)
          (x : SuzukiApertureIntervalL2 1)).re := congrArg Complex.re hpform
      _ = suzukiLimitingLogOperatorGroundEnergy *
          ‖(x : SuzukiApertureIntervalL2 1)‖ ^ 2 := hinner
      _ = _ := by rw [hprep]
  obtain ⟨c, hpc⟩ := exists_complex_smul_eq_of_suzukiFormGroundMinimizers
    q p hqreal hqground hqne hpground
  refine ⟨c, ?_⟩
  change (x : SuzukiApertureIntervalL2 1) =
    c • suzukiLimitingLogFormEmbedding q
  rw [← hprep, hpc, map_smul]

end RHTower
