import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsAreLaplaceTransforms
import GaloisForLFunctions.HTGeometry.TwoSidedLaplaceVanishing
import GaloisForLFunctions.HTGeometry.HardyPaleyWienerTransport
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import Mathlib.Topology.Sequences

/-!
# Strong Hardy boundaries of finite-energy defects

The vertical traces are Fourier transforms of exponentially damped Mellin sources.
Strong convergence of the damping identifies their limit with the canonical boundary
operator. Its range is the Hardy boundary space obtained from positive-half-line data.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ExactEventTheory

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

private def arclengthFourier : DefectL2 →L[ℂ] DefectL2 :=
  (Real.sqrt (2 * Real.pi) : ℂ) •
    ((_root_.RHTower.dilation (2 * Real.pi)⁻¹ (by positivity)).toContinuousLinearMap.comp
      (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearIsometry.toContinuousLinearMap)

private def laplaceBoundary : HalfLineL2 →L[ℂ] DefectL2 :=
  arclengthFourier.comp
    _root_.RHTower.suzukiPositiveZeroExtensionIsometry.toContinuousLinearMap

private def boundaryFromMellinSource : DefectL2 →L[ℂ] DefectL2 :=
  laplaceBoundary.comp defectMellinSource

/-- The `L²` vertical trace. At nonpositive real parts the damping is held at zero. -/
def defectVerticalL2 (g : DefectL2) (σ : ℝ) : DefectL2 :=
  arclengthFourier
    ((memLp_two_rayDamp (Lp.memLp (defectMellinSource g)) (le_max_right σ 0)).toLp
      (rayDamp (defectMellinSource g) (max σ 0)))

private theorem rayDamp_zero_toLp (ψ : HalfLineL2) :
    (memLp_two_rayDamp (Lp.memLp ψ) le_rfl).toLp (rayDamp ψ 0) =
      _root_.RHTower.suzukiPositiveZeroExtension ψ := by
  apply Lp.ext
  filter_upwards [(memLp_two_rayDamp (Lp.memLp ψ) le_rfl).coeFn_toLp,
    _root_.RHTower.suzukiPositiveZeroExtension_ae ψ] with u hu hv
  rw [hu, hv]
  simp only [rayDamp, expRay, _root_.RHTower.suzukiPositiveZeroExtensionFun,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]

private theorem defectVerticalL2_zero_source (g : DefectL2) :
    defectVerticalL2 g 0 = boundaryFromMellinSource g := by
  simp only [defectVerticalL2, max_self, rayDamp_zero_toLp]
  rfl

private theorem continuousAt_defectVerticalL2_zero_source (g : DefectL2) :
    ContinuousAt (defectVerticalL2 g) 0 := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro σ hσ
  have hm : Tendsto (fun n => max (σ n) 0) atTop (𝓝 (0 : ℝ)) := by
    simpa using hσ.max (tendsto_const_nhds (x := (0 : ℝ)))
  have hd := tendsto_toLp_rayDamp (Lp.memLp (defectMellinSource g))
    (fun n => le_max_right (σ n) 0) hm
  have h := (arclengthFourier.continuous.tendsto _).comp hd
  simpa only [Function.comp_def, defectVerticalL2, max_self] using h

/-- Every positive vertical trace represents the actual Hamburger integral. -/
theorem defectVerticalL2_ae (g : DefectL2) {σ : ℝ} (hσ : 0 < σ) :
    (defectVerticalL2 g σ : ℝ → ℂ) =ᵐ[volume]
      fun y => defectLaplace (g : ℝ → ℂ) (hardyVerticalLine σ y) := by
  let d : DefectL2 :=
    (memLp_two_rayDamp (Lp.memLp (defectMellinSource g)) hσ.le).toLp
      (rayDamp (defectMellinSource g) σ)
  let f : DefectL2 := (Lp.fourierTransformₗᵢ ℝ ℂ) d
  have hf : (f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => laplaceRay (defectMellinSource g) (rayLine σ ξ) :=
    coeFn_fourierTransform_rayDamp (Lp.memLp (defectMellinSource g)) hσ
  have hfp := (_root_.RHTower.realMul_quasiMeasurePreserving (2 * Real.pi)⁻¹
    (by positivity)).ae hf
  have hcoef : (Real.sqrt (2 * Real.pi) : ℂ) *
      (Real.sqrt (2 * Real.pi)⁻¹ : ℂ) = 1 := by
    exact_mod_cast _root_.RHTower.sqrt_mul_sqrt_inv (2 * Real.pi) (by positivity)
  have he : defectVerticalL2 g σ = (Real.sqrt (2 * Real.pi) : ℂ) •
      _root_.RHTower.dilation (2 * Real.pi)⁻¹ (by positivity) f := by
    simp only [defectVerticalL2, max_eq_left hσ.le]
    rfl
  rw [he]
  filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * Real.pi) : ℂ)
    (_root_.RHTower.dilation (2 * Real.pi)⁻¹ (by positivity) f),
    _root_.RHTower.dilation_ae (2 * Real.pi)⁻¹ (by positivity) f, hfp]
      with y hs hd hf
  rw [hs]
  change (Real.sqrt (2 * Real.pi) : ℂ) *
    _root_.RHTower.dilation (2 * Real.pi)⁻¹ _ f y = _
  rw [hd]
  change f ((2 * Real.pi)⁻¹ * y) =
    laplaceRay (defectMellinSource g) (rayLine σ ((2 * Real.pi)⁻¹ * y)) at hf
  rw [hf, ← mul_assoc, hcoef, one_mul, rayLine_eq_hardyVerticalLine,
    defectLaplace_eq_laplaceRay g (by simpa using hσ)]

private theorem boundaryFromMellinSource_agrees (g : DefectL2)
    (hg : Integrable (g : ℝ → ℂ)) :
    (boundaryFromMellinSource g : ℝ → ℂ) =ᵐ[volume] defectBoundary g := by
  let σ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hσpos : ∀ n, 0 < σ n := fun n => by dsimp [σ]; positivity
  have hσ : Tendsto σ atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hσgt : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hL : Tendsto (fun n => defectVerticalL2 g (σ n)) atTop
      (𝓝 (boundaryFromMellinSource g)) := by
    rw [← defectVerticalL2_zero_source]
    exact (continuousAt_defectVerticalL2_zero_source g).tendsto.comp hσ
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂(volume : Measure ℝ), ∀ i : ℕ,
      defectVerticalL2 g (σ (ns i)) y =
        defectLaplace (g : ℝ → ℂ) (hardyVerticalLine (σ (ns i)) y) :=
    ae_all_iff.mpr fun i => defectVerticalL2_ae g (hσpos (ns i))
  filter_upwards [hae, hall, volume.ae_ne (0 : ℝ)] with y hy hall hy0
  have hp := (tendsto_defectLaplace_boundary hg hy0).comp
    (hσgt.comp hns.tendsto_atTop)
  have he : (fun i => defectVerticalL2 g (σ (ns i)) y) =
      fun i => defectLaplace (g : ℝ → ℂ) (hardyVerticalLine (σ (ns i)) y) :=
    funext hall
  rw [he] at hy
  exact tendsto_nhds_unique hy hp

private theorem boundaryFromMellinSource_eq :
    boundaryFromMellinSource = defectBoundaryL2 :=
  defectBoundaryL2_unique boundaryFromMellinSource boundaryFromMellinSource_agrees

/-- The zero-damping Fourier trace is the previously constructed canonical boundary. -/
theorem defectVerticalL2_zero (g : DefectL2) :
    defectVerticalL2 g 0 = defectBoundaryL2 g := by
  rw [defectVerticalL2_zero_source, boundaryFromMellinSource_eq]

/-- Strong boundary convergence follows from strong convergence of exponential damping. -/
theorem tendsto_defectVerticalL2 (g : DefectL2) :
    Tendsto (defectVerticalL2 g) (𝓝[>] (0 : ℝ)) (𝓝 (defectBoundaryL2 g)) := by
  rw [← defectVerticalL2_zero]
  exact (continuousAt_defectVerticalL2_zero_source g).tendsto.mono_left
    nhdsWithin_le_nhds

/-- Every `L²` test pairs continuously with the actual interior defect as the boundary
is approached. This includes all bounded compactly supported tests and tents. -/
theorem tendsto_integral_defectLaplace_L2_boundary (g k : DefectL2) :
    Tendsto (fun σ : ℝ => ∫ y : ℝ, (starRingEnd ℂ) (k y) *
      defectLaplace (g : ℝ → ℂ) (hardyVerticalLine σ y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y : ℝ, (starRingEnd ℂ) (k y) * defectBoundaryL2 g y)) := by
  have hinner : ∀ f : DefectL2,
      inner ℂ k f = ∫ y : ℝ, (starRingEnd ℂ) (k y) * f y := by
    intro f
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change inner ℂ (k y) (f y) = (starRingEnd ℂ) (k y) * f y
      rw [RCLike.inner_apply, mul_comm]
  have hlim : Tendsto (fun σ => inner ℂ k (defectVerticalL2 g σ))
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℂ k (defectBoundaryL2 g))) :=
    ((continuous_const.inner continuous_id).tendsto (defectBoundaryL2 g)).comp
      (tendsto_defectVerticalL2 g)
  simp only [hinner] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  apply integral_congr_ae
  filter_upwards [defectVerticalL2_ae g hσ] with y hy
  rw [hy]

/-- The canonical boundary is the Paley–Wiener transform of its actual Mellin source. -/
theorem defectBoundaryL2_eq_PaleyWiener (g : DefectL2) :
    defectBoundaryL2 g = (Real.sqrt (2 * Real.pi) : ℂ) •
      (lowerHardyPaleyWienerUnitary (defectMellinSource g) : DefectL2) := by
  rw [← boundaryFromMellinSource_eq]
  change (Real.sqrt (2 * Real.pi) : ℂ) •
      _root_.RHTower.dilation (2 * Real.pi)⁻¹ (by positivity)
        (_root_.RHTower.fourierUnitary
          (_root_.RHTower.suzukiPositiveZeroExtension (defectMellinSource g))) =
    (Real.sqrt (2 * Real.pi) : ℂ) •
      _root_.RHTower.fourierUnitary (_root_.RHTower.dilation (2 * Real.pi) (by positivity)
        (_root_.RHTower.suzukiPositiveZeroExtension (defectMellinSource g)))
  rw [_root_.RHTower.fourierUnitary_dilation]

theorem defectBoundaryL2_mem_hardy (g : DefectL2) :
    defectBoundaryL2 g ∈ _root_.RHTower.hardyL2ᗮ := by
  rw [defectBoundaryL2_eq_PaleyWiener]
  exact (_root_.RHTower.hardyL2ᗮ).smul_mem _
    (lowerHardyPaleyWienerUnitary (defectMellinSource g)).property

/-- Every Hardy boundary value has a finite-energy defect preimage. -/
theorem defectBoundaryL2_surjective_hardy (f : LowerHardyL2) :
    ∃ g : DefectL2, defectBoundaryL2 g = (f : DefectL2) := by
  have hc : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne'
  obtain ⟨g, hg⟩ := defectMellinSource_bijective.2
    (lowerHardyPaleyWienerUnitary.symm ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • f))
  refine ⟨g, ?_⟩
  rw [defectBoundaryL2_eq_PaleyWiener, hg, LinearIsometryEquiv.apply_symm_apply]
  change (Real.sqrt (2 * Real.pi) : ℂ) •
    ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • (f : DefectL2)) = (f : DefectL2)
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The range is exactly the Fourier image of positive-half-line data. -/
theorem range_defectBoundaryL2 :
    LinearMap.range defectBoundaryL2.toLinearMap = _root_.RHTower.hardyL2ᗮ := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact defectBoundaryL2_mem_hardy g
  · intro hf
    obtain ⟨g, hg⟩ := defectBoundaryL2_surjective_hardy ⟨f, hf⟩
    exact ⟨g, hg⟩

private def normalizedHardyBoundary : DefectL2 →ₗᵢ[ℂ] LowerHardyL2 where
  toFun g := ⟨normalizedDefectBoundaryL2 g,
    (_root_.RHTower.hardyL2ᗮ).smul_mem (Real.sqrt Real.pi : ℂ)
      (defectBoundaryL2_mem_hardy g)⟩
  map_add' g h := Subtype.ext (normalizedDefectBoundaryL2.map_add g h)
  map_smul' c g := Subtype.ext (normalizedDefectBoundaryL2.map_smul c g)
  norm_map' g := normalizedDefectBoundaryL2.norm_map g

private theorem normalizedHardyBoundary_surjective :
    Function.Surjective normalizedHardyBoundary := by
  intro f
  have hc : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  obtain ⟨g, hg⟩ := defectBoundaryL2_surjective_hardy ((Real.sqrt Real.pi : ℂ)⁻¹ • f)
  refine ⟨g, Subtype.ext ?_⟩
  change (Real.sqrt Real.pi : ℂ) • defectBoundaryL2 g = (f : DefectL2)
  rw [hg]
  change (Real.sqrt Real.pi : ℂ) •
    ((Real.sqrt Real.pi : ℂ)⁻¹ • (f : DefectL2)) = (f : DefectL2)
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- `√π B` is unitary onto the Hardy boundary space of the right half-plane. -/
def normalizedDefectBoundaryHardyUnitary : DefectL2 ≃ₗᵢ[ℂ] LowerHardyL2 :=
  LinearIsometryEquiv.ofSurjective normalizedHardyBoundary normalizedHardyBoundary_surjective

theorem normalizedDefectBoundaryHardyUnitary_coe (g : DefectL2) :
    (normalizedDefectBoundaryHardyUnitary g : DefectL2) = normalizedDefectBoundaryL2 g := rfl

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_defectVerticalL2
#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_integral_defectLaplace_L2_boundary
#print axioms GaloisForLFunctions.EulerFETransportTheory.range_defectBoundaryL2
#print axioms GaloisForLFunctions.EulerFETransportTheory.normalizedDefectBoundaryHardyUnitary
