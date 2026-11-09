import GaloisForLFunctions.EulerFETransportTheory.TheBoundaryPreservesDefectEnergy
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The canonical finite-energy boundary

The actual Hamburger boundary on integrable square-integrable data extends by density
to every square-integrable defect. Its exact energy is preserved, and the extension
agrees with the original integral wherever both constructions apply.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The integral boundary depends only on the almost-everywhere class of its source. -/
theorem defectBoundary_congr_ae {g h : ℝ → ℂ} (hgh : g =ᵐ[volume] h) :
    defectBoundary g = defectBoundary h := by
  funext y
  unfold defectBoundary closedDefectLaplace
  congr 1
  apply integral_congr_ae
  filter_upwards [hgh] with t ht
  rw [ht]

theorem defectBoundary_add {g h : ℝ → ℂ} (hg : Integrable g) (hh : Integrable h) :
    defectBoundary (g + h) = defectBoundary g + defectBoundary h := by
  funext y
  by_cases hy : y = 0
  · simp [hy]
  have hz0 : (y : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hy) I_ne_zero
  have hz : 0 ≤ ((y : ℂ) * I).re := by simp
  simp only [defectBoundary, closedDefectLaplace, Pi.add_apply, add_mul]
  rw [integral_add (integrable_closedDefectLaplace_integrand hg hz hz0)
    (integrable_closedDefectLaplace_integrand hh hz hz0), mul_add]

theorem defectBoundary_smul (c : ℂ) (g : ℝ → ℂ) :
    defectBoundary (c • g) = c • defectBoundary g := by
  funext y
  simp only [defectBoundary, closedDefectLaplace, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  ring

/-- The Hilbert space of finite-energy uncompleted defects. -/
abbrev DefectL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Integrable representatives form the original domain inside the energy space. -/
def integrableDefectL2 : Submodule ℂ DefectL2 where
  carrier := {f : DefectL2 | Integrable (f : ℝ → ℂ) (volume : Measure ℝ)}
  zero_mem' := by
    change Integrable ((0 : DefectL2) : ℝ → ℂ) volume
    exact (integrable_zero ℝ ℂ volume).congr (Lp.coeFn_zero ℂ 2 volume).symm
  add_mem' := by
    intro f g hf hg
    have hf' : Integrable (f : ℝ → ℂ) volume := hf
    have hg' : Integrable (g : ℝ → ℂ) volume := hg
    change Integrable ((f + g : DefectL2) : ℝ → ℂ) volume
    exact (hf'.add hg').congr (Lp.coeFn_add f g).symm
  smul_mem' := by
    intro c f hf
    have hf' : Integrable (f : ℝ → ℂ) volume := hf
    change Integrable ((c • f : DefectL2) : ℝ → ℂ) volume
    exact (hf'.const_mul c).congr (Lp.coeFn_smul c f).symm

private def integrableBoundary (g : integrableDefectL2) : DefectL2 :=
  (memLp_defectBoundary g.property (Lp.memLp g.val)).toLp (defectBoundary g.val)

private theorem integrableBoundary_ae (g : integrableDefectL2) :
    (integrableBoundary g : ℝ → ℂ) =ᵐ[volume] defectBoundary g.val :=
  (memLp_defectBoundary g.property (Lp.memLp g.val)).coeFn_toLp

private def integrableBoundaryLinear : integrableDefectL2 →ₗ[ℂ] DefectL2 where
  toFun := integrableBoundary
  map_add' g h := by
    apply Lp.ext
    have hval : (g + h).val = g.val + h.val := rfl
    have hs := (defectBoundary_congr_ae (Lp.coeFn_add g.val h.val)).trans
      (defectBoundary_add g.property h.property)
    filter_upwards [integrableBoundary_ae (g + h),
      Lp.coeFn_add (integrableBoundary g) (integrableBoundary h),
      integrableBoundary_ae g, integrableBoundary_ae h] with y hgh hadd hg hh
    rw [hgh, hadd]
    simpa only [hval, Pi.add_apply, hg, hh] using congrFun hs y
  map_smul' c g := by
    apply Lp.ext
    simp only [RingHom.id_apply]
    have hval : (c • g).val = c • g.val := rfl
    have hs := (defectBoundary_congr_ae (Lp.coeFn_smul c g.val)).trans
      (defectBoundary_smul c g.val)
    filter_upwards [integrableBoundary_ae (c • g),
      Lp.coeFn_smul c (integrableBoundary g), integrableBoundary_ae g] with y hcg hsm hg
    rw [hcg, hsm]
    simpa only [hval, Pi.smul_apply, hg] using congrFun hs y

private theorem integrableBoundary_norm_sq (g : integrableDefectL2) :
    ‖integrableBoundary g‖ ^ 2 = Real.pi⁻¹ * ‖g.val‖ ^ 2 := by
  rw [Lp_two_norm_sq_eq_integral (integrableBoundary g)]
  calc
    _ = ∫ y : ℝ, ‖defectBoundary g.val y‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [integrableBoundary_ae g] with y hy
      rw [hy]
    _ = Real.pi⁻¹ * ∫ t : ℝ, ‖(g.val : ℝ → ℂ) t‖ ^ 2 :=
      integral_norm_sq_defectBoundary g.property (Lp.memLp g.val)
    _ = _ := by rw [← Lp_two_norm_sq_eq_integral g.val]

private theorem integrableBoundary_norm (g : integrableDefectL2) :
    ‖integrableBoundary g‖ = (Real.sqrt Real.pi)⁻¹ * ‖g.val‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  rw [integrableBoundary_norm_sq, mul_pow, inv_pow, Real.sq_sqrt Real.pi_pos.le]

/-- Schwartz density places every finite-energy datum in the closure of the original domain. -/
theorem integrableDefectL2_dense : DenseRange integrableDefectL2.subtype := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  apply Dense.mono (s₁ := Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ))) ?_ hd
  rintro _ ⟨f, rfl⟩
  refine ⟨⟨f.toLp 2 volume, ?_⟩, rfl⟩
  exact f.integrable.congr (f.coeFn_toLp 2 volume).symm

/-- The continuous extension of the actual Hamburger boundary to every finite-energy source. -/
def defectBoundaryL2 : DefectL2 →L[ℂ] DefectL2 :=
  integrableBoundaryLinear.extendOfNorm integrableDefectL2.subtype

private theorem defectBoundaryL2_integrable (g : integrableDefectL2) :
    defectBoundaryL2 g.val = integrableBoundary g := by
  apply LinearMap.extendOfNorm_eq integrableDefectL2_dense
  exact ⟨(Real.sqrt Real.pi)⁻¹, fun h => (integrableBoundary_norm h).le⟩

/-- Completion agrees with the original integral for every `L¹ ∩ L²` representative. -/
theorem defectBoundaryL2_agrees {g : ℝ → ℂ} (hg : Integrable g) (hg2 : MemLp g 2) :
    (defectBoundaryL2 (hg2.toLp g) : ℝ → ℂ) =ᵐ[volume] defectBoundary g := by
  let u : integrableDefectL2 := ⟨hg2.toLp g, hg.congr hg2.coeFn_toLp.symm⟩
  have hu : defectBoundaryL2 (hg2.toLp g) = integrableBoundary u := defectBoundaryL2_integrable u
  rw [hu]
  filter_upwards [integrableBoundary_ae u] with y hy
  rw [hy]
  exact congrFun (defectBoundary_congr_ae hg2.coeFn_toLp) y

/-- The exact norm survives completion; the extension neither loses nor creates energy. -/
theorem norm_defectBoundaryL2 (g : DefectL2) :
    ‖defectBoundaryL2 g‖ = (Real.sqrt Real.pi)⁻¹ * ‖g‖ := by
  have he : (fun u : DefectL2 => ‖defectBoundaryL2 u‖) =
      (fun u : DefectL2 => (Real.sqrt Real.pi)⁻¹ * ‖u‖) :=
    integrableDefectL2_dense.equalizer (by fun_prop) (by fun_prop) (by
      funext u
      change ‖defectBoundaryL2 u.val‖ = (Real.sqrt Real.pi)⁻¹ * ‖u.val‖
      rw [defectBoundaryL2_integrable, integrableBoundary_norm])
  exact congrFun he g

theorem norm_sq_defectBoundaryL2 (g : DefectL2) :
    ‖defectBoundaryL2 g‖ ^ 2 = Real.pi⁻¹ * ‖g‖ ^ 2 := by
  rw [norm_defectBoundaryL2, mul_pow, inv_pow, Real.sq_sqrt Real.pi_pos.le]

/-- After multiplication by `√π`, the finite-energy boundary is an isometric embedding. -/
def normalizedDefectBoundaryL2 : DefectL2 →ₗᵢ[ℂ] DefectL2 where
  toLinearMap := ((Real.sqrt Real.pi : ℂ) • defectBoundaryL2).toLinearMap
  norm_map' g := by
    change ‖(Real.sqrt Real.pi : ℂ) • defectBoundaryL2 g‖ = ‖g‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_defectBoundaryL2, ← mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr Real.pi_pos).ne', one_mul]

/-- Agreement on the original integral domain characterizes the completed boundary uniquely. -/
theorem defectBoundaryL2_unique (T : DefectL2 →L[ℂ] DefectL2)
    (hT : ∀ g : DefectL2, Integrable (g : ℝ → ℂ) →
      (T g : ℝ → ℂ) =ᵐ[volume] defectBoundary g) : T = defectBoundaryL2 := by
  apply DFunLike.coe_injective
  apply integrableDefectL2_dense.equalizer T.continuous defectBoundaryL2.continuous
  funext g
  change T g.val = defectBoundaryL2 g.val
  rw [defectBoundaryL2_integrable]
  exact Lp.ext ((hT g.val g.property).trans (integrableBoundary_ae g).symm)

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.defectBoundaryL2_agrees
#print axioms GaloisForLFunctions.EulerFETransportTheory.norm_sq_defectBoundaryL2
#print axioms GaloisForLFunctions.EulerFETransportTheory.normalizedDefectBoundaryL2
#print axioms GaloisForLFunctions.EulerFETransportTheory.defectBoundaryL2_unique
