import GaloisForLFunctions.RHTower.CCMArchimedeanLaurentFormCore
import GaloisForLFunctions.RHTower.CCMArchimedeanBoundaryLayerFormCore
import GaloisForLFunctions.RHTower.CCMRestrictedWeilFriedrichsOperator
import GaloisForLFunctions.RHTower.CCMGalerkinDiagonalTransfer
import GaloisForLFunctions.RHTower.CCMNestedFloorNoEvacuation
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

theorem continuous_ccmRestrictedWeilSourceQuadratic (a : SuzukiPositiveAperture) :
    Continuous (ccmRestrictedWeilSourceQuadratic a) := by
  have heq : ccmRestrictedWeilSourceQuadratic a = fun u =>
      (ccmRestrictedWeilForm a u u).re := by
    funext u
    exact (ccmRestrictedWeilForm_self_re_eq_source a u).symm
  rw [heq]
  unfold ccmRestrictedWeilForm
  exact Complex.continuous_re.comp
    ((continuous_id.inner continuous_id).add
      (((ccmRestrictedWeilBoundedRemainder a).continuous.comp
          (ccmArchimedeanFormToAperture a).continuous).inner
        (ccmArchimedeanFormToAperture a).continuous))

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

end RHTower

end
