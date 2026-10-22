import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniHilbertOne
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanBoundaryLayerFormCore
import GaloisForLFunctions.RHTower.CCM.CCMGalerkinDiagonalTransfer
import GaloisForLFunctions.RHTower.CCM.CCMNestedFloorNoEvacuation
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Connes--Consani finite Laurent sections recover the restricted Weil ground energy

For a positive aperture `a`, let `E_N` be the span of the exact aperture characters with
`|k| <= N`, transported into the literal shifted Riemann--Siegel form domain.  This file proves
that the Rayleigh floors of the literal restricted Weil source form on `E_N` decrease to the
ground energy of its Friedrichs operator.

The second half constructs the actual finite-dimensional self-adjoint compression in the
physical `L²` norm.  Its least eigenvalue is the same Rayleigh floor.  Thus the convergence theorem
has the precise ``smallest eigenvalue'' meaning of Connes--Consani (2021), Corollary `Hilbert2`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

/-! ## Exact Laurent sections and their Rayleigh floors -/

/-- Physical `L²` mass of an archimedean form-domain vector. -/
def ccmRestrictedWeilMass (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) : ℝ :=
  ‖ccmArchimedeanFormToAperture a u‖ ^ 2

/-- Literal restricted Weil Rayleigh quotient. -/
def ccmRestrictedWeilRayleigh (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a u / ccmRestrictedWeilMass a u

theorem continuous_ccmRestrictedWeilMass (a : SuzukiPositiveAperture) :
    Continuous (ccmRestrictedWeilMass a) := by
  unfold ccmRestrictedWeilMass
  fun_prop

theorem continuousAt_ccmRestrictedWeilRayleigh
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hu : ccmRestrictedWeilMass a u ≠ 0) :
    ContinuousAt (ccmRestrictedWeilRayleigh a) u := by
  unfold ccmRestrictedWeilRayleigh
  exact (continuous_ccmRestrictedWeilSourceQuadratic a).continuousAt.div
    (continuous_ccmRestrictedWeilMass a).continuousAt hu

/-- The `N`th exact CCM Laurent section. -/
def ccmArchimedeanLaurentGalerkinSubmodule
    (a : SuzukiPositiveAperture) (N : ℕ) :
    Submodule ℂ (CCMArchimedeanFormDomain a) :=
  Submodule.span ℂ
    ((fun k : ℤ => ccmLogFormToArchimedean a
      (suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1))) ''
      {k : ℤ | k.natAbs ≤ N})

theorem ccmArchimedeanLaurentGalerkinSubmodule_mono
    (a : SuzukiPositiveAperture) {M N : ℕ} (hMN : M ≤ N) :
    ccmArchimedeanLaurentGalerkinSubmodule a M ≤
      ccmArchimedeanLaurentGalerkinSubmodule a N := by
  refine Submodule.span_mono ?_
  rintro q ⟨k, hk, rfl⟩
  exact ⟨k, hk.trans hMN, rfl⟩

theorem finite_ccmArchimedeanLaurentGalerkin_generators
    (a : SuzukiPositiveAperture) (N : ℕ) :
    ((fun k : ℤ => ccmLogFormToArchimedean a
      (suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1))) ''
      {k : ℤ | k.natAbs ≤ N}).Finite := by
  apply Set.Finite.image
  rw [show {k : ℤ | k.natAbs ≤ N} = Icc (-(N : ℤ)) (N : ℤ) by
    ext k
    simp only [mem_setOf_eq, mem_Icc]
    constructor
    · intro hk
      have hk' : k.natAbs ≤ (N : ℤ).natAbs := by simpa using hk
      have hsquare : k ^ 2 ≤ (N : ℤ) ^ 2 :=
        Int.natAbs_le_iff_sq_le.mp hk'
      constructor <;> nlinarith
    · rintro ⟨hleft, hright⟩
      have hsquare : k ^ 2 ≤ (N : ℤ) ^ 2 := by nlinarith
      have hk' : k.natAbs ≤ (N : ℤ).natAbs :=
        Int.natAbs_le_iff_sq_le.mpr hsquare
      simpa using hk']
  exact Set.finite_Icc _ _

theorem iSup_ccmArchimedeanLaurentGalerkinSubmodule
    (a : SuzukiPositiveAperture) :
    (⨆ N : ℕ, ccmArchimedeanLaurentGalerkinSubmodule a N) =
      ccmArchimedeanLaurentSubmodule a := by
  rw [show ccmArchimedeanLaurentSubmodule a =
      Submodule.span ℂ (Set.range fun k : ℤ => ccmLogFormToArchimedean a
        (suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1))) by
    rw [ccmArchimedeanLaurentSubmodule, suzukiHlogLaurentSubmodule,
      Submodule.map_span]
    congr 1
    change ccmLogFormToArchimedean a ''
        (Set.range fun k : ℤ => suzukiApertureModeFormVector a
          (Real.pi * (k : ℝ) / a.1)) = _
    ext q
    simp]
  apply le_antisymm
  · refine iSup_le fun N => Submodule.span_le.mpr ?_
    rintro q ⟨k, hkN, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro q ⟨k, rfl⟩
    exact Submodule.mem_iSup_of_mem k.natAbs
      (Submodule.subset_span ⟨k, (show k.natAbs ≤ k.natAbs by rfl), rfl⟩)

theorem ccmArchimedeanApertureModeFormVector_zero_ne_zero
    (a : SuzukiPositiveAperture) :
    ccmArchimedeanApertureModeFormVector a 0 ≠ 0 := by
  intro hzero
  have hmode :=
    ccmArchimedeanFormEmbedding_apertureModeFormVector_coeFn a 0
  rw [hzero, map_zero] at hmode
  have hzeroCoe : ∀ᵐ x : ℝ ∂volume,
      suzukiApertureModeCutoff a.1 0 x = 0 := by
    filter_upwards [hmode, MeasureTheory.Lp.coeFn_zero ℂ 2 volume]
      with x hmodeX hz
    calc
      suzukiApertureModeCutoff a.1 0 x = (0 : SoninL2) x := hmodeX.symm
      _ = (0 : ℂ) := by simpa using hz
  have hout : ∀ᵐ x : ℝ ∂volume, x ∉ Ioo (-a.1) a.1 := by
    filter_upwards [hzeroCoe] with x hx
    intro hxin
    rw [suzukiApertureModeCutoff, indicator_of_mem (Ioo_subset_Icc_self hxin),
      suzukiApertureMode] at hx
    norm_num at hx
  rw [ae_iff] at hout
  have hvol : (volume : Measure ℝ) (Ioo (-a.1) a.1) = 0 := by
    simpa only [not_not, setOf_mem_eq] using hout
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hvol
  linarith [a.2]

theorem ccmRestrictedWeilMass_ne_zero_of_ne_zero
    (a : SuzukiPositiveAperture) {u : CCMArchimedeanFormDomain a} (hu : u ≠ 0) :
    ccmRestrictedWeilMass a u ≠ 0 := by
  unfold ccmRestrictedWeilMass
  apply pow_ne_zero
  rw [norm_ne_zero_iff]
  intro hJu
  apply hu
  apply ccmArchimedeanFormToAperture_injective a
  simpa using hJu

theorem ccmLaurentGalerkin_quotient_nonempty
    (a : SuzukiPositiveAperture) (N : ℕ) :
    (GaloisForLFunctions.RHTower.rayleighQuotientSet
      (ccmRestrictedWeilSourceQuadratic a) (ccmRestrictedWeilMass a)
      (ccmArchimedeanLaurentGalerkinSubmodule a N :
        Set (CCMArchimedeanFormDomain a))).Nonempty := by
  let u := ccmLogFormToArchimedean a (suzukiApertureModeFormVector a 0)
  have hu0 : u ≠ 0 := by
    change ccmArchimedeanApertureModeFormVector a 0 ≠ 0
    exact ccmArchimedeanApertureModeFormVector_zero_ne_zero a
  have huN : u ∈ ccmArchimedeanLaurentGalerkinSubmodule a N := by
    exact Submodule.subset_span ⟨0, by simp, by simp [u]⟩
  exact ⟨ccmRestrictedWeilRayleigh a u, u, huN,
    ccmRestrictedWeilMass_ne_zero_of_ne_zero a hu0, rfl⟩

theorem ccmLaurentGalerkin_quotient_bddBelow
    (a : SuzukiPositiveAperture) (N : ℕ) :
    BddBelow (GaloisForLFunctions.RHTower.rayleighQuotientSet
      (ccmRestrictedWeilSourceQuadratic a) (ccmRestrictedWeilMass a)
      (ccmArchimedeanLaurentGalerkinSubmodule a N :
        Set (CCMArchimedeanFormDomain a))) := by
  refine ⟨ccmRestrictedWeilGroundEnergy a, ?_⟩
  rintro r ⟨u, huN, hmass, rfl⟩
  have hmassPos : 0 < ccmRestrictedWeilMass a u := by
    unfold ccmRestrictedWeilMass
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hmass)
  rw [le_div_iff₀ hmassPos]
  exact ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u

/-- Rayleigh floor of the literal restricted Weil form on the `N`th Laurent section. -/
def ccmLaurentGalerkinFloor (a : SuzukiPositiveAperture) (N : ℕ) : ℝ :=
  GaloisForLFunctions.RHTower.rayleighFloor
    (ccmRestrictedWeilSourceQuadratic a) (ccmRestrictedWeilMass a)
    (ccmArchimedeanLaurentGalerkinSubmodule a N :
      Set (CCMArchimedeanFormDomain a))

theorem ccmRestrictedWeilGroundEnergy_le_ccmLaurentGalerkinFloor
    (a : SuzukiPositiveAperture) (N : ℕ) :
    ccmRestrictedWeilGroundEnergy a ≤ ccmLaurentGalerkinFloor a N := by
  unfold ccmLaurentGalerkinFloor GaloisForLFunctions.RHTower.rayleighFloor
  refine le_csInf (ccmLaurentGalerkin_quotient_nonempty a N) ?_
  rintro r ⟨u, huN, hmass, rfl⟩
  have hmassPos : 0 < ccmRestrictedWeilMass a u := by
    unfold ccmRestrictedWeilMass
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hmass)
  rw [le_div_iff₀ hmassPos]
  exact ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u

theorem antitone_ccmLaurentGalerkinFloor (a : SuzukiPositiveAperture) :
    Antitone (ccmLaurentGalerkinFloor a) := by
  intro M N hMN
  exact GaloisForLFunctions.RHTower.rayleighFloor_antitone _ _
    (ccmArchimedeanLaurentGalerkinSubmodule_mono a hMN)
    (ccmLaurentGalerkin_quotient_bddBelow a N)
    (ccmLaurentGalerkin_quotient_nonempty a M)

theorem exists_ccmLaurentGalerkinFloor_lt_ground_add
    (a : SuzukiPositiveAperture) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ,
      ccmLaurentGalerkinFloor a N < ccmRestrictedWeilGroundEnergy a + epsilon := by
  obtain ⟨u, hJu, hground⟩ := ccmRestrictedWeilSource_exists_groundFormState a
  have hu : u ≠ 0 := by
    intro hu0
    rw [hu0, map_zero] at hJu
    exact hJu rfl
  have hmass : ccmRestrictedWeilMass a u ≠ 0 :=
    ccmRestrictedWeilMass_ne_zero_of_ne_zero a hu
  have hrayleigh :
      ccmRestrictedWeilRayleigh a u = ccmRestrictedWeilGroundEnergy a := by
    unfold ccmRestrictedWeilRayleigh ccmRestrictedWeilMass
    rw [hground]
    field_simp [norm_ne_zero_iff.mpr hJu]
  have hcont : ContinuousAt (ccmRestrictedWeilRayleigh a) u :=
    continuousAt_ccmRestrictedWeilRayleigh a u hmass
  have hrayNhds :
      {v | ccmRestrictedWeilRayleigh a v <
        ccmRestrictedWeilGroundEnergy a + epsilon} ∈ 𝓝 u := by
    have hIio : Iio (ccmRestrictedWeilGroundEnergy a + epsilon) ∈
        𝓝 (ccmRestrictedWeilRayleigh a u) := by
      rw [hrayleigh]
      exact Iio_mem_nhds (by linarith)
    exact hcont hIio
  have hneNhds : ({0}ᶜ : Set (CCMArchimedeanFormDomain a)) ∈ 𝓝 u :=
    isOpen_compl_singleton.mem_nhds hu
  obtain ⟨s, hsub, hsopen, hus⟩ :=
    mem_nhds_iff.mp (inter_mem hrayNhds hneNhds)
  obtain ⟨v, hvLaurent, hvs⟩ :=
    (dense_ccmArchimedeanLaurentSubmodule a).exists_mem_open hsopen ⟨u, hus⟩
  have hvBoth := hsub hvs
  have hvRay : ccmRestrictedWeilRayleigh a v <
      ccmRestrictedWeilGroundEnergy a + epsilon := hvBoth.1
  have hvne : v ≠ 0 := by simpa using hvBoth.2
  have hvSup : v ∈ ⨆ N : ℕ, ccmArchimedeanLaurentGalerkinSubmodule a N := by
    rw [iSup_ccmArchimedeanLaurentGalerkinSubmodule]
    exact hvLaurent
  obtain ⟨N, hvN⟩ :=
    (Submodule.mem_iSup_of_directed (ccmArchimedeanLaurentGalerkinSubmodule a)
      (fun i j => ⟨max i j,
        ccmArchimedeanLaurentGalerkinSubmodule_mono a (le_max_left _ _),
        ccmArchimedeanLaurentGalerkinSubmodule_mono a (le_max_right _ _)⟩)).mp hvSup
  refine ⟨N, lt_of_le_of_lt ?_ hvRay⟩
  exact GaloisForLFunctions.RHTower.rayleighFloor_le_of_witness _ _
    (ccmLaurentGalerkin_quotient_bddBelow a N) hvN
    (ccmRestrictedWeilMass_ne_zero_of_ne_zero a hvne) le_rfl

/-- Exact Laurent-section Rayleigh floors decrease to the restricted Weil ground energy. -/
theorem tendsto_ccmLaurentGalerkinFloor_groundEnergy
    (a : SuzukiPositiveAperture) :
    Tendsto (ccmLaurentGalerkinFloor a) atTop
      (𝓝 (ccmRestrictedWeilGroundEnergy a)) := by
  exact GaloisForLFunctions.RHTower.tendsto_of_antitone_of_approx
    (antitone_ccmLaurentGalerkinFloor a)
    (ccmRestrictedWeilGroundEnergy_le_ccmLaurentGalerkinFloor a)
    (fun epsilon hepsilon =>
      exists_ccmLaurentGalerkinFloor_lt_ground_add a hepsilon)

/-! ## Literal finite-dimensional compressed operators -/

noncomputable instance instFiniteDimensionalCCMArchimedeanLaurentGalerkinSubmodule
    (a : SuzukiPositiveAperture) (N : ℕ) :
    FiniteDimensional ℂ (ccmArchimedeanLaurentGalerkinSubmodule a N) :=
  FiniteDimensional.span_of_finite ℂ
    (finite_ccmArchimedeanLaurentGalerkin_generators a N)

/-- Physical embedding of the `N`th Laurent section. -/
def ccmLaurentGalerkinEmbedding (a : SuzukiPositiveAperture) (N : ℕ) :
    ccmArchimedeanLaurentGalerkinSubmodule a N →ₗ[ℂ]
      suzukiApertureHilbert a :=
  (ccmArchimedeanFormToAperture a).toLinearMap.comp
    (ccmArchimedeanLaurentGalerkinSubmodule a N).subtype

theorem ccmLaurentGalerkinEmbedding_injective
    (a : SuzukiPositiveAperture) (N : ℕ) :
    Function.Injective (ccmLaurentGalerkinEmbedding a N) := by
  intro u v huv
  apply Subtype.ext
  apply ccmArchimedeanFormToAperture_injective a
  exact huv

/-- Physical `L²` Laurent section.  This is the space denoted `E_N` in the spectral statement. -/
def ccmPhysicalLaurentGalerkinSubmodule
    (a : SuzukiPositiveAperture) (N : ℕ) :
    Submodule ℂ (suzukiApertureHilbert a) :=
  LinearMap.range (ccmLaurentGalerkinEmbedding a N)

noncomputable local instance ccmPhysicalLaurentGalerkinInnerProductSpace
    (a : SuzukiPositiveAperture) (N : ℕ) :
    InnerProductSpace ℂ (ccmPhysicalLaurentGalerkinSubmodule a N) :=
  Submodule.innerProductSpace (ccmPhysicalLaurentGalerkinSubmodule a N)

/-- Exact linear equivalence from the form-domain Laurent section onto its physical image. -/
def ccmLaurentGalerkinEquivPhysical
    (a : SuzukiPositiveAperture) (N : ℕ) :
    ccmArchimedeanLaurentGalerkinSubmodule a N ≃ₗ[ℂ]
      ccmPhysicalLaurentGalerkinSubmodule a N :=
  LinearEquiv.ofInjective (ccmLaurentGalerkinEmbedding a N)
    (ccmLaurentGalerkinEmbedding_injective a N)

noncomputable instance instFiniteDimensionalCCMPhysicalLaurentGalerkinSubmodule
    (a : SuzukiPositiveAperture) (N : ℕ) :
    FiniteDimensional ℂ (ccmPhysicalLaurentGalerkinSubmodule a N) :=
  FiniteDimensional.of_surjective
    (ccmLaurentGalerkinEquivPhysical a N).toLinearMap
    (ccmLaurentGalerkinEquivPhysical a N).surjective

noncomputable instance instNontrivialCCMPhysicalLaurentGalerkinSubmodule
    (a : SuzukiPositiveAperture) (N : ℕ) :
    Nontrivial (ccmPhysicalLaurentGalerkinSubmodule a N) := by
  let u : ccmArchimedeanLaurentGalerkinSubmodule a N :=
    ⟨ccmLogFormToArchimedean a (suzukiApertureModeFormVector a 0),
      Submodule.subset_span ⟨0, by simp, by simp⟩⟩
  have hu : u ≠ 0 := by
    intro hzero
    have hval := congrArg Subtype.val hzero
    apply ccmArchimedeanApertureModeFormVector_zero_ne_zero a
    exact hval
  exact nontrivial_of_ne (ccmLaurentGalerkinEquivPhysical a N u) 0
    (by
      intro hzero
      apply hu
      apply (ccmLaurentGalerkinEquivPhysical a N).injective
      simpa using hzero)

/-- Inverse physical-to-form map on the finite Laurent section. -/
def ccmLaurentGalerkinPreimage (a : SuzukiPositiveAperture) (N : ℕ) :
    ccmPhysicalLaurentGalerkinSubmodule a N →L[ℂ]
      CCMArchimedeanFormDomain a :=
  ⟨(ccmArchimedeanLaurentGalerkinSubmodule a N).subtype.comp
      (ccmLaurentGalerkinEquivPhysical a N).symm.toLinearMap,
    ((ccmArchimedeanLaurentGalerkinSubmodule a N).subtype.comp
      (ccmLaurentGalerkinEquivPhysical a N).symm.toLinearMap).continuous_of_finiteDimensional⟩

/-- Inclusion of the physical Laurent section into the aperture Hilbert space. -/
def ccmPhysicalLaurentGalerkinInclusion
    (a : SuzukiPositiveAperture) (N : ℕ) :
    ccmPhysicalLaurentGalerkinSubmodule a N →L[ℂ]
      suzukiApertureHilbert a :=
  (ccmPhysicalLaurentGalerkinSubmodule a N).subtypeL

private def ccmPhysicalLaurentGalerkinInclusionAdjoint
    (a : SuzukiPositiveAperture) (N : ℕ) :
    suzukiApertureHilbert a →L[ℂ]
      ccmPhysicalLaurentGalerkinSubmodule a N :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := ccmPhysicalLaurentGalerkinSubmodule a N)
    (F := suzukiApertureHilbert a)
    (ccmPhysicalLaurentGalerkinInclusion a N)

private def ccmLaurentGalerkinPreimageAdjoint
    (a : SuzukiPositiveAperture) (N : ℕ) :
    CCMArchimedeanFormDomain a →L[ℂ]
      ccmPhysicalLaurentGalerkinSubmodule a N :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := ccmPhysicalLaurentGalerkinSubmodule a N)
    (F := CCMArchimedeanFormDomain a)
    (ccmLaurentGalerkinPreimage a N)

/-- Exact finite-dimensional CCM compression in the physical `L²` metric.

The first summand represents the unbounded archimedean form on the finite section; the second is
the compression of the literal bounded polar-and-prime remainder. -/
def ccmLaurentGalerkinOperator (a : SuzukiPositiveAperture) (N : ℕ) :
    ccmPhysicalLaurentGalerkinSubmodule a N →L[ℂ]
      ccmPhysicalLaurentGalerkinSubmodule a N :=
  (ccmLaurentGalerkinPreimageAdjoint a N).comp
      (ccmLaurentGalerkinPreimage a N) +
    (ccmPhysicalLaurentGalerkinInclusionAdjoint a N).comp
      ((ccmRestrictedWeilBoundedRemainder a).comp
        (ccmPhysicalLaurentGalerkinInclusion a N))

theorem ccmLaurentGalerkinOperator_isSymmetric
    (a : SuzukiPositiveAperture) (N : ℕ) :
    @LinearMap.IsSymmetric ℂ (ccmPhysicalLaurentGalerkinSubmodule a N)
      inferInstance inferInstance
      (Submodule.innerProductSpace (ccmPhysicalLaurentGalerkinSubmodule a N))
      (ccmLaurentGalerkinOperator a N).toLinearMap := by
  intro x y
  unfold ccmLaurentGalerkinOperator
  change inner ℂ
      (ccmLaurentGalerkinPreimageAdjoint a N (ccmLaurentGalerkinPreimage a N x) +
        ccmPhysicalLaurentGalerkinInclusionAdjoint a N
          (ccmRestrictedWeilBoundedRemainder a
            (ccmPhysicalLaurentGalerkinInclusion a N x))) y =
    inner ℂ x
      (ccmLaurentGalerkinPreimageAdjoint a N (ccmLaurentGalerkinPreimage a N y) +
        ccmPhysicalLaurentGalerkinInclusionAdjoint a N
          (ccmRestrictedWeilBoundedRemainder a
            (ccmPhysicalLaurentGalerkinInclusion a N y)))
  rw [@inner_add_left ℂ (ccmPhysicalLaurentGalerkinSubmodule a N)
      inferInstance inferInstance
      (Submodule.innerProductSpace (ccmPhysicalLaurentGalerkinSubmodule a N)),
    @inner_add_right ℂ (ccmPhysicalLaurentGalerkinSubmodule a N)
      inferInstance inferInstance
      (Submodule.innerProductSpace (ccmPhysicalLaurentGalerkinSubmodule a N))]
  congr 1
  · unfold ccmLaurentGalerkinPreimageAdjoint
    rw [ContinuousLinearMap.adjoint_inner_left (𝕜 := ℂ)
      (E := ccmPhysicalLaurentGalerkinSubmodule a N)
      (F := CCMArchimedeanFormDomain a)
      (ccmLaurentGalerkinPreimage a N) y (ccmLaurentGalerkinPreimage a N x)]
    rw [ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ)
      (E := ccmPhysicalLaurentGalerkinSubmodule a N)
      (F := CCMArchimedeanFormDomain a)
      (ccmLaurentGalerkinPreimage a N) x (ccmLaurentGalerkinPreimage a N y)]
  · unfold ccmPhysicalLaurentGalerkinInclusionAdjoint
    rw [ContinuousLinearMap.adjoint_inner_left (𝕜 := ℂ)
      (E := ccmPhysicalLaurentGalerkinSubmodule a N)
      (F := suzukiApertureHilbert a)
      (ccmPhysicalLaurentGalerkinInclusion a N) y
      (ccmRestrictedWeilBoundedRemainder a
        (ccmPhysicalLaurentGalerkinInclusion a N x))]
    have hR :
        inner ℂ
            (ccmRestrictedWeilBoundedRemainder a
              (ccmPhysicalLaurentGalerkinInclusion a N x))
            (ccmPhysicalLaurentGalerkinInclusion a N y) =
          inner ℂ (ccmPhysicalLaurentGalerkinInclusion a N x)
            (ccmRestrictedWeilBoundedRemainder a
              (ccmPhysicalLaurentGalerkinInclusion a N y)) := by
      exact (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric
        (ccmPhysicalLaurentGalerkinInclusion a N x)
        (ccmPhysicalLaurentGalerkinInclusion a N y)
    rw [hR]
    rw [ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ)
      (E := ccmPhysicalLaurentGalerkinSubmodule a N)
      (F := suzukiApertureHilbert a)
      (ccmPhysicalLaurentGalerkinInclusion a N) x
      (ccmRestrictedWeilBoundedRemainder a
        (ccmPhysicalLaurentGalerkinInclusion a N y))]

theorem ccmPhysicalLaurentGalerkinInclusion_eq_formToAperture
    (a : SuzukiPositiveAperture) (N : ℕ)
    (x : ccmPhysicalLaurentGalerkinSubmodule a N) :
    ccmPhysicalLaurentGalerkinInclusion a N x =
      ccmArchimedeanFormToAperture a (ccmLaurentGalerkinPreimage a N x) := by
  have h := congrArg Subtype.val
    ((ccmLaurentGalerkinEquivPhysical a N).apply_symm_apply x)
  exact h.symm

theorem ccmLaurentGalerkinPreimage_apply_equivPhysical
    (a : SuzukiPositiveAperture) (N : ℕ)
    (u : ccmArchimedeanLaurentGalerkinSubmodule a N) :
    ccmLaurentGalerkinPreimage a N (ccmLaurentGalerkinEquivPhysical a N u) = u := by
  exact congrArg Subtype.val
    ((ccmLaurentGalerkinEquivPhysical a N).symm_apply_apply u)

/-- The compressed operator has exactly the literal CCM source quadratic on its diagonal. -/
theorem ccmLaurentGalerkinOperator_inner_self_re
    (a : SuzukiPositiveAperture) (N : ℕ)
    (x : ccmPhysicalLaurentGalerkinSubmodule a N) :
    (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re =
      ccmRestrictedWeilSourceQuadratic a (ccmLaurentGalerkinPreimage a N x) := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source]
  unfold ccmLaurentGalerkinOperator ccmRestrictedWeilForm
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  apply congrArg Complex.re
  unfold ccmLaurentGalerkinPreimageAdjoint
    ccmPhysicalLaurentGalerkinInclusionAdjoint
  rw [@inner_add_left ℂ (ccmPhysicalLaurentGalerkinSubmodule a N)
      inferInstance inferInstance
      (Submodule.innerProductSpace (ccmPhysicalLaurentGalerkinSubmodule a N)),
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [ccmPhysicalLaurentGalerkinInclusion_eq_formToAperture]

theorem ccmLaurentGalerkinOperator_rayleigh_eq
    (a : SuzukiPositiveAperture) (N : ℕ)
    (x : ccmPhysicalLaurentGalerkinSubmodule a N) :
    (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re / ‖x‖ ^ 2 =
      ccmRestrictedWeilRayleigh a (ccmLaurentGalerkinPreimage a N x) := by
  rw [ccmLaurentGalerkinOperator_inner_self_re]
  unfold ccmRestrictedWeilRayleigh ccmRestrictedWeilMass
  congr 1
  rw [← ccmPhysicalLaurentGalerkinInclusion_eq_formToAperture]
  rfl

private theorem ccmLaurentGalerkinOperator_has_iInf_eigenvalue
    (a : SuzukiPositiveAperture) (N : ℕ) :
    Module.End.HasEigenvalue (ccmLaurentGalerkinOperator a N).toLinearMap
      ((⨅ x : {x : ccmPhysicalLaurentGalerkinSubmodule a N // x ≠ 0},
        (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re /
          ‖(x : ccmPhysicalLaurentGalerkinSubmodule a N)‖ ^ 2 : ℝ) : ℂ) := by
  exact @LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional
    ℂ inferInstance (ccmPhysicalLaurentGalerkinSubmodule a N) inferInstance
    (ccmPhysicalLaurentGalerkinInnerProductSpace a N)
    (instFiniteDimensionalCCMPhysicalLaurentGalerkinSubmodule a N)
    (ccmLaurentGalerkinOperator a N).toLinearMap
    (instNontrivialCCMPhysicalLaurentGalerkinSubmodule a N)
    (ccmLaurentGalerkinOperator_isSymmetric a N)

theorem range_ccmLaurentGalerkinOperatorRayleigh_eq_quotientSet
    (a : SuzukiPositiveAperture) (N : ℕ) :
    Set.range
        (fun x : {x : ccmPhysicalLaurentGalerkinSubmodule a N // x ≠ 0} =>
          (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re /
            ‖(x : ccmPhysicalLaurentGalerkinSubmodule a N)‖ ^ 2) =
      GaloisForLFunctions.RHTower.rayleighQuotientSet
        (ccmRestrictedWeilSourceQuadratic a) (ccmRestrictedWeilMass a)
        (ccmArchimedeanLaurentGalerkinSubmodule a N :
          Set (CCMArchimedeanFormDomain a)) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    let u := ccmLaurentGalerkinPreimage a N x.1
    have huN : u ∈ ccmArchimedeanLaurentGalerkinSubmodule a N := by
      exact ((ccmLaurentGalerkinEquivPhysical a N).symm x.1).property
    have hu : u ≠ 0 := by
      intro hu0
      apply x.2
      apply Subtype.ext
      have hxu := ccmPhysicalLaurentGalerkinInclusion_eq_formToAperture a N x.1
      change ccmLaurentGalerkinPreimage a N x.1 = 0 at hu0
      rw [hu0, map_zero] at hxu
      exact hxu
    refine ⟨u, huN, ccmRestrictedWeilMass_ne_zero_of_ne_zero a hu, ?_⟩
    simpa only [ccmRestrictedWeilRayleigh] using
      ccmLaurentGalerkinOperator_rayleigh_eq a N x.1
  · rintro ⟨u, huN, hmass, rfl⟩
    let uG : ccmArchimedeanLaurentGalerkinSubmodule a N := ⟨u, huN⟩
    let x : ccmPhysicalLaurentGalerkinSubmodule a N :=
      ccmLaurentGalerkinEquivPhysical a N uG
    have hu : u ≠ 0 := by
      intro hu0
      apply hmass
      simp [ccmRestrictedWeilMass, hu0]
    have hx : x ≠ 0 := by
      intro hx0
      apply hu
      have huG : uG = 0 := by
        apply (ccmLaurentGalerkinEquivPhysical a N).injective
        simpa [x] using hx0
      exact congrArg Subtype.val huG
    refine ⟨⟨x, hx⟩, ?_⟩
    change (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re / ‖x‖ ^ 2 =
      ccmRestrictedWeilSourceQuadratic a u / ccmRestrictedWeilMass a u
    rw [ccmLaurentGalerkinOperator_rayleigh_eq]
    unfold ccmRestrictedWeilRayleigh
    rw [show ccmLaurentGalerkinPreimage a N x = u by
      change ccmLaurentGalerkinPreimage a N
        (ccmLaurentGalerkinEquivPhysical a N uG) = u
      exact ccmLaurentGalerkinPreimage_apply_equivPhysical a N uG]

theorem iInf_ccmLaurentGalerkinOperatorRayleigh_eq_floor
    (a : SuzukiPositiveAperture) (N : ℕ) :
    (⨅ x : {x : ccmPhysicalLaurentGalerkinSubmodule a N // x ≠ 0},
      (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re /
        ‖(x : ccmPhysicalLaurentGalerkinSubmodule a N)‖ ^ 2 : ℝ) =
      ccmLaurentGalerkinFloor a N := by
  unfold ccmLaurentGalerkinFloor GaloisForLFunctions.RHTower.rayleighFloor
  change sInf
      (Set.range
        (fun x : {x : ccmPhysicalLaurentGalerkinSubmodule a N // x ≠ 0} =>
          (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re /
            ‖(x : ccmPhysicalLaurentGalerkinSubmodule a N)‖ ^ 2)) = _
  rw [range_ccmLaurentGalerkinOperatorRayleigh_eq_quotientSet]

/-- Every Laurent-section floor is an actual eigenvalue of the literal finite CCM compression. -/
theorem ccmLaurentGalerkinOperator_has_floor_eigenvalue
    (a : SuzukiPositiveAperture) (N : ℕ) :
    Module.End.HasEigenvalue (ccmLaurentGalerkinOperator a N).toLinearMap
      (ccmLaurentGalerkinFloor a N : ℂ) := by
  simpa only [iInf_ccmLaurentGalerkinOperatorRayleigh_eq_floor] using
    ccmLaurentGalerkinOperator_has_iInf_eigenvalue a N

/-- The floor eigenvalue is the smallest eigenvalue of the finite CCM compression. -/
theorem ccmLaurentGalerkinFloor_le_eigenvalue_re
    (a : SuzukiPositiveAperture) (N : ℕ) {mu : ℂ}
    (hmu : Module.End.HasEigenvalue
      (ccmLaurentGalerkinOperator a N).toLinearMap mu) :
    ccmLaurentGalerkinFloor a N ≤ mu.re := by
  obtain ⟨x, hx⟩ := hmu.exists_hasEigenvector
  have hbdd : BddBelow
      (Set.range
        (fun y : {y : ccmPhysicalLaurentGalerkinSubmodule a N // y ≠ 0} =>
          (inner ℂ (ccmLaurentGalerkinOperator a N y) y).re /
            ‖(y : ccmPhysicalLaurentGalerkinSubmodule a N)‖ ^ 2)) := by
    rw [range_ccmLaurentGalerkinOperatorRayleigh_eq_quotientSet]
    exact ccmLaurentGalerkin_quotient_bddBelow a N
  have hfloor : ccmLaurentGalerkinFloor a N ≤
      (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re / ‖x‖ ^ 2 := by
    rw [← iInf_ccmLaurentGalerkinOperatorRayleigh_eq_floor]
    exact ciInf_le hbdd ⟨x, hx.2⟩
  have hquot :
      (inner ℂ (ccmLaurentGalerkinOperator a N x) x).re / ‖x‖ ^ 2 =
        mu.re := by
    have heig : ccmLaurentGalerkinOperator a N x = mu • x := hx.apply_eq_smul
    rw [heig,
      @inner_smul_left ℂ (ccmPhysicalLaurentGalerkinSubmodule a N)
        inferInstance inferInstance
        (Submodule.innerProductSpace (ccmPhysicalLaurentGalerkinSubmodule a N)),
      Submodule.coe_inner, inner_self_eq_norm_sq_to_K]
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hre (r : ℝ) : ((r : ℂ) ^ 2).re = r ^ 2 := by
      rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have him (r : ℝ) : ((r : ℂ) ^ 2).im = 0 := by
      rw [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hreX :
        ((‖(x : suzukiApertureHilbert a)‖ : ℂ) ^ 2).re =
          ‖(x : suzukiApertureHilbert a)‖ ^ 2 := hre _
    have himX :
        ((‖(x : suzukiApertureHilbert a)‖ : ℂ) ^ 2).im = 0 := him _
    change
      (mu.re * ((‖(x : suzukiApertureHilbert a)‖ : ℂ) ^ 2).re -
        -mu.im * ((‖(x : suzukiApertureHilbert a)‖ : ℂ) ^ 2).im) /
          ‖(x : suzukiApertureHilbert a)‖ ^ 2 = mu.re
    rw [hreX, himX]
    simp only [mul_zero, sub_zero]
    have hxAmbient : (x : suzukiApertureHilbert a) ≠ 0 := by
      intro hzero
      apply hx.2
      exact Subtype.ext hzero
    field_simp [norm_ne_zero_iff.mpr hxAmbient]
  exact hfloor.trans_eq hquot

/-- **Connes--Consani (2021), Corollary `Hilbert2`, literal restricted-Weil form.**

The smallest eigenvalues of the exact finite Laurent compressions converge to the ground energy
of the restricted Weil Friedrichs operator.  `ccmLaurentGalerkinOperator_has_floor_eigenvalue`
proves that each term is a genuine eigenvalue, while the Rayleigh characterization makes it the
least eigenvalue. -/
theorem connesConsani_Hilbert2
    (a : SuzukiPositiveAperture) :
    Tendsto (ccmLaurentGalerkinFloor a) atTop
      (𝓝 (ccmRestrictedWeilGroundEnergy a)) :=
  tendsto_ccmLaurentGalerkinFloor_groundEnergy a

end RHTower

end
