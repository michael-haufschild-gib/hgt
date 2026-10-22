import GaloisForLFunctions.RHTower.Suzuki.SuzukiH01FormDomain

/-!
# Suzuki's `H₀¹` core lies in the exact restricted Weil operator domain

The Fourier transform of an interval primitive decays like `O(1 / |ξ|)`.  The square-logarithmic
upgrade proved in `SuzukiH01FormDomain` therefore puts the exact digamma weight times that Fourier
transform in ordinary `L²`.  This module constructs its full-line Riesz representative, compresses
it to the literal interval, adds the exact polar-plus-finite-prime remainder, and applies the first
representation theorem.

The result is an unconditional operator-domain statement: every vector in Suzuki's literal
Dirichlet domain `H₀¹(-a,a)` belongs to the domain of the exact restricted Weil Friedrichs
operator, with an explicit operator value.  No form-domain premise or abstract representative is
left to the caller.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Exact digamma-weighted Fourier profile associated with a CCM form vector. -/
def ccmArchimedeanMultiplierProfile (u : CCMArchimedeanFourierL2) (ξ : ℝ) : ℂ :=
  (ccmArchimedeanFormWeight ξ : ℂ) * u ξ

def ccmArchimedeanMultiplierL2 (u : CCMArchimedeanFourierL2)
    (hu : MemLp (ccmArchimedeanMultiplierProfile u) 2 (volume : Measure ℝ)) : SoninL2 :=
  hu.toLp (ccmArchimedeanMultiplierProfile u)

/-- Full-line Riesz representative of the exact CCM archimedean form functional. -/
def ccmArchimedeanOperatorRepresentative (u : CCMArchimedeanFourierL2)
    (hu : MemLp (ccmArchimedeanMultiplierProfile u) 2 (volume : Measure ℝ)) : SoninL2 :=
  fourierUnitary.symm (ccmArchimedeanMultiplierL2 u hu)

theorem inner_ccmArchimedeanOperatorRepresentative
    (u v : CCMArchimedeanFourierL2)
    (hu : MemLp (ccmArchimedeanMultiplierProfile u) 2 (volume : Measure ℝ)) :
    inner ℂ u v =
      inner ℂ (ccmArchimedeanOperatorRepresentative u hu)
        (ccmArchimedeanFourierToTime v) := by
  rw [ccmArchimedeanOperatorRepresentative, ccmArchimedeanFourierToTime]
  rw [ContinuousLinearMap.comp_apply]
  change inner ℂ u v =
    inner ℂ (fourierUnitary.symm (ccmArchimedeanMultiplierL2 u hu))
      (fourierUnitary.symm (ccmArchimedeanWeightedToL2 v))
  rw [fourierUnitary.symm.inner_map_map]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  unfold ccmArchimedeanFormMeasure
  rw [integral_withDensity_eq_integral_smul
    measurable_ccmArchimedeanFormWeightNNReal]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp,
    ccmArchimedeanWeightedToL2_coeFn v] with ξ huξ hvξ
  change (Real.toNNReal (ccmArchimedeanFormWeight ξ)) •
      inner ℂ (u ξ) (v ξ) =
    inner ℂ ((hu.toLp (ccmArchimedeanMultiplierProfile u) : SoninL2) ξ)
      (ccmArchimedeanWeightedToL2 v ξ)
  rw [huξ, hvξ]
  unfold ccmArchimedeanMultiplierProfile
  rw [NNReal.smul_def, coe_ccmArchimedeanFormWeightNNReal]
  rw [RCLike.inner_apply, RCLike.inner_apply, Complex.real_smul, map_mul]
  rw [Complex.conj_ofReal]
  ring

theorem suzukiAperturePrimitiveCCMFormVector_coeFn_volume
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    ((suzukiAperturePrimitiveCCMFormVector a f).1 : ℝ → ℂ) =ᵐ[volume]
      𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) := by
  let g := suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)
  let h1 : Integrable g :=
    integrable_suzukiApertureZeroExtend a (suzukiAperturePrimitive a.1 f)
  let hE : Integrable (fun ξ : ℝ => suzukiLogWeight ξ * ‖𝓕 g ξ‖ ^ 2) :=
    integrable_suzukiAperturePrimitive_hlogEnergy a f
  have hforward := (ccmLogToArchimedean_coeFn
    (suzukiHlogFourierVector g h1 hE)).filter_mono
      (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have hfourier := (suzukiHlogFourierVector_coeFn g h1 hE).filter_mono
    (ae_mono volume_le_suzukiHlogMeasure)
  change ((ccmLogToArchimedean
    (suzukiHlogFourierVector g h1 hE) : CCMArchimedeanFourierL2) : ℝ → ℂ) =ᵐ[volume]
      𝓕 g
  exact hforward.trans hfourier

/-- Exact digamma weight squared is integrable against every interval primitive Fourier energy. -/
theorem integrable_ccmArchimedeanFormWeight_sq_mul_primitiveFourier
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ ^ 2 *
      ‖𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ‖ ^ 2) := by
  let C := ccmArchimedeanLogComparisonConstant
  have hC0 : 0 ≤ C :=
    zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant
  have hbase :=
    (integrable_suzukiAperturePrimitive_hlogEnergy_sq a f).const_mul (C ^ 2)
  refine Integrable.mono' hbase
    (measurable_ccmArchimedeanFormWeight.aestronglyMeasurable.pow 2 |>.mul
      ((GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
        (integrable_suzukiApertureZeroExtend a
          (suzukiAperturePrimitive a.1 f))).norm.pow 2).aestronglyMeasurable) ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hw := ccmArchimedeanFormWeight_le_logComparison ξ
  have hw0 := ccmArchimedeanFormWeight_pos ξ |>.le
  have hlog0 := suzukiLogWeight_nonneg ξ
  have hsq : ccmArchimedeanFormWeight ξ ^ 2 ≤
      C ^ 2 * suzukiLogWeight ξ ^ 2 := by
    nlinarith [mul_nonneg hC0 hlog0]
  calc
    ccmArchimedeanFormWeight ξ ^ 2 *
        ‖𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ‖ ^ 2
      ≤ (C ^ 2 * suzukiLogWeight ξ ^ 2) *
        ‖𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ‖ ^ 2 := by
          gcongr
    _ = C ^ 2 * (suzukiLogWeight ξ ^ 2 *
        ‖𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f)) ξ‖ ^ 2) := by
          ring

theorem memLp_ccmArchimedeanMultiplierProfile_primitiveCCMFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    MemLp (ccmArchimedeanMultiplierProfile
      (suzukiAperturePrimitiveCCMFormVector a f).1) 2 (volume : Measure ℝ) := by
  let u := (suzukiAperturePrimitiveCCMFormVector a f).1
  let F := 𝓕 (suzukiApertureZeroExtend (suzukiAperturePrimitive a.1 f))
  have huF : (u : ℝ → ℂ) =ᵐ[volume] F :=
    suzukiAperturePrimitiveCCMFormVector_coeFn_volume a f
  have hmeas : AEStronglyMeasurable (ccmArchimedeanMultiplierProfile u)
      (volume : Measure ℝ) :=
    (Complex.continuous_ofReal.measurable.comp
      measurable_ccmArchimedeanFormWeight).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable u).mono_measure
        volume_le_ccmArchimedeanFormMeasure)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  refine (integrable_ccmArchimedeanFormWeight_sq_mul_primitiveFourier a f).congr ?_
  filter_upwards [huF] with ξ huξ
  unfold ccmArchimedeanMultiplierProfile
  rw [huξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (ccmArchimedeanFormWeight_pos ξ)]
  ring

/-- Literal zero-extension map from interval coordinates to full-line `L²`. -/
def suzukiApertureZeroExtensionCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SoninL2 :=
  (suzukiApertureHilbert a).subtypeL ∘L suzukiApertureToPhysicalCLM a

theorem suzukiApertureZeroExtensionCLM_weilIntervalFormEmbedding
    (a : SuzukiPositiveAperture) (v : CCMArchimedeanFormDomain a) :
    suzukiApertureZeroExtensionCLM a (suzukiWeilIntervalFormEmbedding a v) =
      ccmArchimedeanFourierToTime v.1 := by
  change ((suzukiApertureL2Equiv a)
      ((suzukiApertureL2Equiv a).symm
        (ccmArchimedeanFormToAperture a v)) : suzukiApertureHilbert a).1 =
    ccmArchimedeanFourierToTime v.1
  rw [(suzukiApertureL2Equiv a).apply_symm_apply]
  rfl

/-- Interval Riesz representative of the exact archimedean form on a primitive. -/
def suzukiAperturePrimitiveArchimedeanRepresentative
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    SuzukiApertureIntervalL2 a.1 :=
  (suzukiApertureZeroExtensionCLM a).adjoint
    (ccmArchimedeanOperatorRepresentative
      (suzukiAperturePrimitiveCCMFormVector a f).1
      (memLp_ccmArchimedeanMultiplierProfile_primitiveCCMFormVector a f))

theorem inner_suzukiAperturePrimitiveArchimedeanRepresentative
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ (suzukiAperturePrimitiveCCMFormVector a f) v =
      inner ℂ (suzukiAperturePrimitiveArchimedeanRepresentative a f)
        (suzukiWeilIntervalFormEmbedding a v) := by
  rw [suzukiAperturePrimitiveArchimedeanRepresentative,
    (suzukiApertureZeroExtensionCLM a).adjoint_inner_left,
    suzukiApertureZeroExtensionCLM_weilIntervalFormEmbedding]
  exact inner_ccmArchimedeanOperatorRepresentative _ _ _

/-- Exact archimedean, polar, and finite-prime representative on an interval primitive. -/
def suzukiAperturePrimitiveWeilRepresentative
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    SuzukiApertureIntervalL2 a.1 :=
  suzukiAperturePrimitiveArchimedeanRepresentative a f +
    suzukiWeilIntervalBoundedRemainder a
      (suzukiAperturePrimitive a.1 f)

theorem suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiWeilIntervalFormEmbedding a
        (suzukiAperturePrimitiveCCMFormVector a f) =
      suzukiAperturePrimitive a.1 f := by
  change (suzukiApertureL2Equiv a).symm
      (ccmArchimedeanFormToAperture a
        (suzukiAperturePrimitiveCCMFormVector a f)) = _
  rw [ccmArchimedeanFormToAperture_primitiveCCMFormVector,
    (suzukiApertureL2Equiv a).symm_apply_apply]

theorem suzukiAperturePrimitiveWeilRepresentative_represents_form
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (v : CCMArchimedeanFormDomain a) :
    inner ℂ (suzukiAperturePrimitiveCCMFormVector a f) v +
        inner ℂ
          (suzukiWeilIntervalBoundedRemainder a
            (suzukiWeilIntervalFormEmbedding a
              (suzukiAperturePrimitiveCCMFormVector a f)))
          (suzukiWeilIntervalFormEmbedding a v) =
      inner ℂ (suzukiAperturePrimitiveWeilRepresentative a f)
        (suzukiWeilIntervalFormEmbedding a v) := by
  rw [suzukiAperturePrimitiveWeilRepresentative, inner_add_left,
    ← inner_suzukiAperturePrimitiveArchimedeanRepresentative]
  rw [suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector]

/-- Every one-sided primitive lies in the exact restricted Weil operator domain. -/
theorem suzukiWeilFriedrichsOperator_primitive_mem_domain
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiAperturePrimitive a.1 f ∈
      (suzukiWeilFriedrichsOperator a).domain := by
  have hrep := boundedPerturbedFriedrichsOperator_mem_domain_of_represents
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
      (suzukiWeilIntervalFormEmbedding_injective a)
      (denseRange_suzukiWeilIntervalFormEmbedding a)
      (suzukiAperturePrimitiveCCMFormVector a f)
      (suzukiAperturePrimitiveWeilRepresentative a f)
      (suzukiAperturePrimitiveWeilRepresentative_represents_form a f)
  rw [suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector] at hrep
  exact hrep.choose

/-- Exact restricted Weil operator value on every one-sided primitive. -/
theorem suzukiWeilFriedrichsOperator_primitive_apply
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiWeilFriedrichsOperator a
      ⟨suzukiAperturePrimitive a.1 f,
        suzukiWeilFriedrichsOperator_primitive_mem_domain a f⟩ =
      suzukiAperturePrimitiveWeilRepresentative a f := by
  have hrep := boundedPerturbedFriedrichsOperator_mem_domain_of_represents
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
      (suzukiWeilIntervalFormEmbedding_injective a)
      (denseRange_suzukiWeilIntervalFormEmbedding a)
      (suzukiAperturePrimitiveCCMFormVector a f)
      (suzukiAperturePrimitiveWeilRepresentative a f)
      (suzukiAperturePrimitiveWeilRepresentative_represents_form a f)
  rw [suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector] at hrep
  exact hrep.choose_spec

/-- `L²` derivative coordinate of a literal vector in Suzuki's `H₀¹` domain. -/
def suzukiDirichletDomainDerivativeCoordinate (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    SuzukiApertureIntervalL2 a.1 :=
  (((suzukiDirichletInverseRangeEquiv a).symm
    (suzukiDirichletDomainToH01 a v) : SuzukiApertureZeroMean a) :
      SuzukiApertureIntervalL2 a.1)

theorem suzukiAperturePrimitive_dirichletDomainDerivativeCoordinate
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    suzukiAperturePrimitive a.1
        (suzukiDirichletDomainDerivativeCoordinate a v) = v.1 := by
  let e := suzukiDirichletInverseRangeEquiv a
  let w : SuzukiApertureH01 a := suzukiDirichletDomainToH01 a v
  have he := e.apply_symm_apply w
  exact congrArg Subtype.val he

def suzukiDirichletCoreWeilRepresentative (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    SuzukiApertureIntervalL2 a.1 :=
  suzukiAperturePrimitiveWeilRepresentative a
    (suzukiDirichletDomainDerivativeCoordinate a v)

/-- Suzuki's literal Dirichlet core `H₀¹(-a,a)` is contained in `D(A_a)`. -/
theorem suzukiWeilFriedrichsOperator_dirichletDomain_mem
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    v.1 ∈ (suzukiWeilFriedrichsOperator a).domain := by
  rw [← suzukiAperturePrimitive_dirichletDomainDerivativeCoordinate a v]
  exact suzukiWeilFriedrichsOperator_primitive_mem_domain a
    (suzukiDirichletDomainDerivativeCoordinate a v)

/-- Explicit exact restricted Weil operator value on Suzuki's `H₀¹` core. -/
theorem suzukiWeilFriedrichsOperator_dirichletDomain_apply
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    suzukiWeilFriedrichsOperator a
        ⟨v.1, suzukiWeilFriedrichsOperator_dirichletDomain_mem a v⟩ =
      suzukiDirichletCoreWeilRepresentative a v := by
  let f := suzukiDirichletDomainDerivativeCoordinate a v
  have hv : suzukiAperturePrimitive a.1 f = v.1 :=
    suzukiAperturePrimitive_dirichletDomainDerivativeCoordinate a v
  have happ := suzukiWeilFriedrichsOperator_primitive_apply a f
  have heq : (⟨v.1,
      suzukiWeilFriedrichsOperator_dirichletDomain_mem a v⟩ :
        (suzukiWeilFriedrichsOperator a).domain) =
      ⟨suzukiAperturePrimitive a.1 f,
        suzukiWeilFriedrichsOperator_primitive_mem_domain a f⟩ :=
    Subtype.ext hv.symm
  rw [heq]
  exact happ

end RHTower
