import GaloisForLFunctions.HTGeometry.MeromorphicDifferentialField

/-!
# The contracting scaling operator on a meromorphic germ field

A disc about the origin is carried into itself by `w ↦ μ w` whenever `‖μ‖ ≤ 1`, so precomposition
by that scaling is an endomorphism of the analytic-germ domain of the disc and, through the
fraction field, of its meromorphic germ field.  The chain rule for the ordinary derivative,
`(f ∘ (μ·))′ = μ · (f′ ∘ (μ·))`, says that this endomorphism twists the meromorphic derivation by
the constant `μ`, and the twisting survives the quotient rule.

This is the operator a Poincaré germ at a *repelling* fixed point lives with: the expanding shift
`f(z) ↦ f(λz)` does not preserve a disc, while its inverse does.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Set
open Bottcher
open scoped Differential

noncomputable section

/-- The scaling self-map of the plane. -/
def scaleMap (mu : ℂ) : ℂ → ℂ := fun w => mu * w

theorem analyticOnNhd_scaleMap (mu : ℂ) (U : Set ℂ) : AnalyticOnNhd ℂ (scaleMap mu) U := by
  intro w _
  exact (analyticAt_const.mul analyticAt_id)

theorem mapsTo_scaleMap {mu : ℂ} (hmu : ‖mu‖ ≤ 1) (r : ℝ) :
    Set.MapsTo (scaleMap mu) (Metric.ball (0 : ℂ) r) (Metric.ball (0 : ℂ) r) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw ⊢
  rw [scaleMap, norm_mul]
  calc ‖mu‖ * ‖w‖ ≤ 1 * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right hmu (norm_nonneg w)
    _ = ‖w‖ := one_mul _
    _ < r := hw

@[simp] theorem deriv_scaleMap (mu : ℂ) (w : ℂ) : deriv (scaleMap mu) w = mu := by
  show deriv (fun x : ℂ => mu * x) w = mu
  have h : HasDerivAt (fun x : ℂ => mu * x) mu w := by
    simpa using ((hasDerivAt_id w).const_mul mu)
  exact h.deriv

theorem isOpen_image_scaleMap {mu : ℂ} (hmu : mu ≠ 0) {U : Set ℂ} (hUo : IsOpen U) :
    IsOpen (scaleMap mu '' U) := by
  have h : scaleMap mu '' U = (Homeomorph.mulLeft₀ mu hmu) '' U := rfl
  rw [h]
  exact (Homeomorph.mulLeft₀ mu hmu).isOpenMap U hUo

theorem precompAnalyticMap_coe {U V : Set ℂ} {ι : ℂ → ℂ} (hι : AnalyticOnNhd ℂ ι V)
    (hmaps : Set.MapsTo ι V U) (a : Bottcher.analyticSubring U) :
    ((Bottcher.precompAnalyticMap hι hmaps a : Bottcher.analyticSubring V) : Germ (𝓟 V) ℂ)
      = (a : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps) := rfl

/-- **The chain rule on analytic germs.**  Precomposition by the scaling twists the germ derivation
by the scaling constant. -/
theorem analyticSubringDeriv_precompAnalytic {U : Set ℂ} (hUo : IsOpen U) {mu : ℂ}
    (hmaps : Set.MapsTo (scaleMap mu) U U) (a : Bottcher.analyticSubring U) :
    analyticSubringDeriv hUo
        (Bottcher.precompAnalyticMap (analyticOnNhd_scaleMap mu U) hmaps a)
      = Bottcher.constToAnalytic U mu *
        Bottcher.precompAnalyticMap (analyticOnNhd_scaleMap mu U) hmaps
          (analyticSubringDeriv hUo a) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  have hcoe : ((Bottcher.precompAnalyticMap (analyticOnNhd_scaleMap mu U) hmaps a
        : Bottcher.analyticSubring U) : Germ (𝓟 U) ℂ)
      = ((f ∘ scaleMap mu : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
    rw [precompAnalyticMap_coe, ← hfa]
    exact Germ.coe_compTendsto f _
  have hderiv : (analyticSubringDeriv hUo a : Germ (𝓟 U) ℂ) = ((deriv f : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
    change analyticGermDeriv hUo (a : Germ (𝓟 U) ℂ) = _
    rw [← hfa]
    rfl
  change analyticGermDeriv hUo
      ((Bottcher.precompAnalyticMap (analyticOnNhd_scaleMap mu U) hmaps a : Bottcher.analyticSubring U)
        : Germ (𝓟 U) ℂ) = _
  rw [hcoe]
  change ((deriv (f ∘ scaleMap mu) : ℂ → ℂ) : Germ (𝓟 U) ℂ) = _
  have hrhs : (((Bottcher.constToAnalytic U mu *
        Bottcher.precompAnalyticMap (analyticOnNhd_scaleMap mu U) hmaps
          (analyticSubringDeriv hUo a) : Bottcher.analyticSubring U)) : Germ (𝓟 U) ℂ)
      = (((fun _ : ℂ => mu) * ((deriv f) ∘ scaleMap mu) : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
    rw [Subring.coe_mul]
    have h1 : ((Bottcher.constToAnalytic U mu : Bottcher.analyticSubring U) : Germ (𝓟 U) ℂ)
        = ((fun _ : ℂ => mu : ℂ → ℂ) : Germ (𝓟 U) ℂ) := rfl
    have h2 : ((Bottcher.precompAnalyticMap (analyticOnNhd_scaleMap mu U) hmaps
          (analyticSubringDeriv hUo a) : Bottcher.analyticSubring U) : Germ (𝓟 U) ℂ)
        = (((deriv f) ∘ scaleMap mu : ℂ → ℂ) : Germ (𝓟 U) ℂ) := by
      rw [precompAnalyticMap_coe, hderiv]
      exact Germ.coe_compTendsto (deriv f) _
    rw [h1, h2, ← Germ.coe_mul]
  rw [hrhs, Germ.coe_eq]
  refine eventually_principal.mpr ?_
  intro w hw
  have hfd : DifferentiableAt ℂ f (scaleMap mu w) :=
    (hf (scaleMap mu w) (hmaps hw)).differentiableAt
  have hgd : DifferentiableAt ℂ (scaleMap mu) w :=
    ((analyticOnNhd_scaleMap mu U) w hw).differentiableAt
  have hchain := deriv_comp w hfd hgd
  simp only [Function.comp_apply, Pi.mul_apply]
  rw [hchain, deriv_scaleMap]
  ring

/-! ## The meromorphic level -/

/-- **The contracting scaling as an endomorphism of the meromorphic germ field.** -/
def scaleMero {U : Set ℂ} {mu : ℂ} (hmu : mu ≠ 0)
    (hmaps : Set.MapsTo (scaleMap mu) U U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    meroField U →+* meroField U :=
  Bottcher.precompMeroMap (analyticOnNhd_scaleMap mu U) hmaps hUc
    (isOpen_image_scaleMap hmu hUo) (hUne.image _) hUo hUne hUo hUc hUne

set_option synthInstance.maxHeartbeats 200000

/-- **The scaling twists the meromorphic derivation by the scaling constant.** -/
theorem scaleMero_deriv {U : Set ℂ} {mu : ℂ} (hmu : mu ≠ 0)
    (hmaps : Set.MapsTo (scaleMap mu) U U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (x : meroField U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroFieldDifferential hUo hUc hUne
    (scaleMero hmu hmaps hUo hUc hUne x)′
      = algebraMap (Bottcher.analyticSubring U) (meroField U) (Bottcher.constToAnalytic U mu)
        * scaleMero hmu hmaps hUo hUc hUne (x′) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℤ (Bottcher.analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI := meroFieldDifferential hUo hUc hUne
  set σ : meroField U →+* meroField U := scaleMero hmu hmaps hUo hUc hUne with hσ
  set P : Bottcher.analyticSubring U →+* Bottcher.analyticSubring U :=
    Bottcher.precompAnalyticMap (analyticOnNhd_scaleMap mu U) hmaps with hP
  have hmap (c : Bottcher.analyticSubring U) :
      σ (algebraMap (Bottcher.analyticSubring U) (meroField U) c)
        = algebraMap (Bottcher.analyticSubring U) (meroField U) (P c) :=
    Bottcher.precompMeroMap_algebraMap _ _ _ _ _ _ _ _ _ _ c
  have hkey (c : Bottcher.analyticSubring U) :
      (σ (algebraMap (Bottcher.analyticSubring U) (meroField U) c))′
        = algebraMap (Bottcher.analyticSubring U) (meroField U) (Bottcher.constToAnalytic U mu)
          * σ ((algebraMap (Bottcher.analyticSubring U) (meroField U) c)′) := by
    rw [hmap, meroFieldDifferential_algebraMap, meroFieldDifferential_algebraMap, hmap, hP,
      analyticSubringDeriv_precompAnalytic hUo hmaps c, map_mul]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (Bottcher.analyticSubring U) x
  rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div]
  simp only [smul_eq_mul, map_mul, map_sub, map_inv₀, map_pow]
  rw [hkey, hkey]
  ring

end

end GaloisForLFunctions.HTGeometry
