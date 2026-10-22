import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.WeilNearRadicalDimension
import GaloisForLFunctions.RHTower.CCM.CCMSmoothSupportUncertainty
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarStrictDomain

/-!
# Actual physical near-radical subspaces

The smooth zeta near radical embeds injectively into the complete CCM source
domain. Its physical dimension, both pole constraints, and its uniform bound
on the full Weil energy survive exactly.
-/

open Complex MeasureTheory Set Zeta23
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- Exact Fourier interpretation of every real exponential pole coordinate. -/
theorem ccmSmooth_polar_eq_paperFT {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
      (ccmArchimedeanFormToAperture a u.toCCMFormVector) =
        paperFT u (-(s : ℂ) * I) := by
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector, paperFT]
  apply integral_congr_ae
  filter_upwards with x
  have he : I * (-(s : ℂ) * I) * (x : ℂ) = ((s * x : ℝ) : ℂ) := by
    calc
      _ = -(s : ℂ) * (x : ℂ) * (I * I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; push_cast; ring
  rw [he, Complex.ofReal_exp]
  ring

private def smoothSubspaceSource (a : SuzukiPositiveAperture)
    (V : Submodule ℂ (ℝ → ℂ))
    (hV : ∀ f ∈ V, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Ioo (-a.1) a.1)
    (f : V) : CCMComplexSmoothInteriorSource a where
  toFun := f.1
  smooth := (hV f f.2).1
  hasCompactSupport := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    ((hV f f.2).2.trans Ioo_subset_Icc_self)
  tsupport_subset := (hV f f.2).2

private def smoothSubspacePhysicalMap (a : SuzukiPositiveAperture)
    (V : Submodule ℂ (ℝ → ℂ))
    (hV : ∀ f ∈ V, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Ioo (-a.1) a.1) :
    V →ₗ[ℂ] SoninL2 where
  toFun f := ccmArchimedeanFormEmbedding a (smoothSubspaceSource a V hV f).toCCMFormVector
  map_add' f g := by
    apply Lp.ext
    have hf := (smoothSubspaceSource a V hV f).toCCMFormVector_physical_coeFn
    have hg := (smoothSubspaceSource a V hV g).toCCMFormVector_physical_coeFn
    have hfg := (smoothSubspaceSource a V hV (f + g)).toCCMFormVector_physical_coeFn
    filter_upwards [hf, hg, hfg, Lp.coeFn_add
      (ccmArchimedeanFormEmbedding a (smoothSubspaceSource a V hV f).toCCMFormVector)
      (ccmArchimedeanFormEmbedding a (smoothSubspaceSource a V hV g).toCCMFormVector)]
      with x hfx hgx hfgx hx
    rw [hx, Pi.add_apply, ← ccmArchimedeanFormToAperture_coe,
      ← ccmArchimedeanFormToAperture_coe, ← ccmArchimedeanFormToAperture_coe,
      hfx, hgx, hfgx]
    rfl
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    have hf := (smoothSubspaceSource a V hV f).toCCMFormVector_physical_coeFn
    have hcf := (smoothSubspaceSource a V hV (c • f)).toCCMFormVector_physical_coeFn
    filter_upwards [hf, hcf, Lp.coeFn_smul c
      (ccmArchimedeanFormEmbedding a (smoothSubspaceSource a V hV f).toCCMFormVector)]
      with x hfx hcfx hx
    rw [hx, Pi.smul_apply, ← ccmArchimedeanFormToAperture_coe,
      ← ccmArchimedeanFormToAperture_coe, hfx, hcfx]
    rfl

private theorem smoothSubspacePhysicalMap_injective (a : SuzukiPositiveAperture)
    (V : Submodule ℂ (ℝ → ℂ))
    (hV : ∀ f ∈ V, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Ioo (-a.1) a.1) :
    Function.Injective (smoothSubspacePhysicalMap a V hV) := by
  intro f g h
  have hf := (smoothSubspaceSource a V hV f).toCCMFormVector_physical_coeFn
  have hg := (smoothSubspaceSource a V hV g).toCCMFormVector_physical_coeFn
  change (smoothSubspacePhysicalMap a V hV f : ℝ → ℂ) =ᵐ[volume] f.1 at hf
  change (smoothSubspacePhysicalMap a V hV g : ℝ → ℂ) =ᵐ[volume] g.1 at hg
  rw [h] at hf
  apply Subtype.ext
  exact (Continuous.ae_eq_iff_eq volume (hV f f.2).1.continuous
    (hV g g.2).1.continuous).mp (hf.symm.trans hg)

/-- Large near-null spaces of actual, smooth, two-pole-constrained sources.
The energy bound controls every vector in the subspace, hence every coefficient cross term. -/
theorem ccm_actual_near_radical_dimension :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      ∃ V : Submodule ℂ SoninL2, FiniteDimensional ℂ V ∧
        Real.exp (2 * a.1 - 4) / 20 ≤ (Module.finrank ℂ V : ℝ) ∧
        ∀ f ∈ V, ∃ u : ccmPolarConstraintSubmodule a,
          ccmArchimedeanFormEmbedding a u.1 = f ∧
          |ccmRestrictedWeilSourceQuadratic a u.1| ≤
            Real.exp (-Real.exp (2 * a.1 - 4)) * ‖f‖ ^ 2 := by
  obtain ⟨L₀, hL₀⟩ := zeta_weil_near_radical_dimension_smooth
  refine ⟨L₀ + 1, fun a ha => ?_⟩
  obtain ⟨W, hWfin, hdim, hW, hQ⟩ := hL₀ (a.1 - 1) (by linarith)
  letI := hWfin
  have hs : ∀ f ∈ W, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Ioo (-a.1) a.1 := by
    intro f hf
    refine ⟨(hW f hf).1, fun x hx => ?_⟩
    have hb := (hW f hf).2.1 hx
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  let T := smoothSubspacePhysicalMap a W hs
  refine ⟨LinearMap.range T, inferInstance, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (smoothSubspacePhysicalMap_injective a W hs)]
    rw [show 2 * (a.1 - 1) - 2 = 2 * a.1 - 4 by ring] at hdim
    exact hdim
  · rintro f ⟨w, rfl⟩
    let u := smoothSubspaceSource a W hs w
    have hp : IsPolarConstrained a u.toCCMFormVector := by
      constructor
      · rw [ccmSmooth_polar_eq_paperFT]
        have he : -((1 / 2 : ℝ) : ℂ) * I = -(I / 2) := by push_cast; ring
        rw [he]
        exact (hW w w.2).2.2.2
      · rw [ccmSmooth_polar_eq_paperFT]
        have he : -((-1 / 2 : ℝ) : ℂ) * I = I / 2 := by push_cast; ring
        rw [he]
        exact (hW w w.2).2.2.1
    refine ⟨⟨u.toCCMFormVector, hp⟩, rfl, ?_⟩
    rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]
    have hq := (Complex.abs_re_le_norm (zetaZeroConfig.W w w)).trans (hQ w w.2)
    have hn := ccmSmooth_integral_norm_sq_eq_physical u
    change (∫ x : ℝ, ‖w.1 x‖ ^ 2) = ‖T w‖ ^ 2 at hn
    rw [hn] at hq
    rw [show 2 * (a.1 - 1) - 2 = 2 * a.1 - 4 by ring] at hq
    exact hq

end RHTower
