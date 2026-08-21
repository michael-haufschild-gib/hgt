import Mathlib

/-!
# Connes' linear Fourier rule and the convolution of two line measures

Formalization of §V (5)-(11) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

To make sense of the product of the two `δ`-distributions `δ(x - y)` and `δ(y - λx)` that appear in
the distributional trace of the scaling action, Connes computes the convolution of their Fourier
transforms.  Both transforms are measures carried by lines in `K²`, and their convolution turns out
to be the *constant* `|1 - λ|⁻¹` — the transverse Jacobian of the fixed point.

* `integral_comp_linearMap_addHaar` - the integral form of the Haar rescaling
  `map f μ = |det f|⁻¹ • μ`, which mathlib owns only at the level of measures.
* `connes_fourier_comp_linearEquiv` - §V (7): `(φ ∘ L)^ = |det L|⁻¹ φ̂ ∘ (L⁻¹)ᵀ`, written with the
  frequency transport spelled out as `⟪L⁻¹ u, w⟫`, which *is* `⟪u, (L⁻¹)ᵀ w⟫`.
* `connesLineMap_det` - the Jacobian `J = 1 - λ` of §V (10).
* `connes_lineMeasure_convolution` - §V (10)/(11): the convolution of the two line measures is the
  constant `|1 - λ|⁻¹`, i.e. `∫∫ f(ξ - λη, -ξ + η) dξ dη = |1 - λ|⁻¹ ∫∫ f`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory

/-- **Linear change of variables in a Bochner integral against a Haar measure.**
`∫ g (f v) dμ(v) = |det f|⁻¹ ∫ g dμ`.  Mathlib owns the measure-level statement
`Measure.map_linearMap_addHaar_eq_smul_addHaar`; this is its integral form. -/
theorem integral_comp_linearMap_addHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) {g : E → G}
    (hg : AEStronglyMeasurable g μ) :
    ∫ v, g (f v) ∂μ = |LinearMap.det f|⁻¹ • ∫ u, g u ∂μ := by
  have hmap : Measure.map (⇑f) μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hf
  have hgmap : AEStronglyMeasurable g (Measure.map (⇑f) μ) := by
    rw [hmap]; exact hg.smul_measure _
  have hmeas : AEMeasurable (⇑f) μ := f.continuous_of_finiteDimensional.measurable.aemeasurable
  have h1 : ∫ v, g (f v) ∂μ = ∫ u, g u ∂(Measure.map (⇑f) μ) := (integral_map hmeas hgmap).symm
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

/-- The standard self-pairing of the plane, used as the additive duality of §V (5). -/
def connesPairing (v w : ℝ × ℝ) : ℝ := v.1 * w.1 + v.2 * w.2

/-- **§V (7).**  Composing with a linear automorphism rescales the Fourier transform by
`|det L|⁻¹` and transports the frequency by the inverse transpose.  Here the transport is written
directly as `⟪L⁻¹ u, w⟫`, which is by definition `⟪u, (L⁻¹)ᵀ w⟫`. -/
theorem connes_fourier_comp_linearEquiv (α : ℝ → ℂ) (φ : ℝ × ℝ → ℂ)
    (L : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ)) (hL : LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0)
    (w : ℝ × ℝ)
    (hmeas : AEStronglyMeasurable
      (fun u : ℝ × ℝ => φ u * α (connesPairing (L.symm u) w)) volume) :
    ∫ v : ℝ × ℝ, φ (L v) * α (connesPairing v w)
      = |LinearMap.det (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))|⁻¹ •
          ∫ u : ℝ × ℝ, φ u * α (connesPairing (L.symm u) w) := by
  have hkey := integral_comp_linearMap_addHaar (volume : Measure (ℝ × ℝ)) hL hmeas
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hkey
  exact hkey

/-- The linear map `(ξ,η) ↦ (ξ - λη, -ξ + η)` of §V (10): the Jacobian of the convolution of the
two line measures `δ(ξ+η)` and `δ(ξ+λη)`. -/
def connesLineMap (lam : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 - lam * p.2, -p.1 + p.2)
  map_add' := by intro p q; simp [Prod.ext_iff]; constructor <;> ring
  map_smul' := by intro c p; simp [Prod.ext_iff]; constructor <;> ring

theorem connesLineMap_det (lam : ℝ) : LinearMap.det (connesLineMap lam) = 1 - lam := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, connesLineMap]

/-- **§V (10)/(11).**  The convolution of the two line measures carried by
`{ξ + η = 0}` and `{ξ + λη = 0}` is the constant `|1 - λ|⁻¹`.  Connes' displayed computation
`∫∫ f((ξ,-ξ) + (-λη,η)) dξ dη = |J|⁻¹ ∫∫ f` with `J = 1 - λ`. -/
theorem connes_lineMeasure_convolution (lam : ℝ) (hlam : lam ≠ 1) (f : ℝ × ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    ∫ p : ℝ × ℝ, f (p.1 - lam * p.2, -p.1 + p.2) = |1 - lam|⁻¹ • ∫ p : ℝ × ℝ, f p := by
  have hdet : LinearMap.det (connesLineMap lam) ≠ 0 := by
    rw [connesLineMap_det]
    intro h
    exact hlam (by linarith [h])
  have := integral_comp_linearMap_addHaar (volume : Measure (ℝ × ℝ)) hdet hf
  rw [connesLineMap_det] at this
  simpa [connesLineMap] using this

end

end GaloisForLFunctions.RHTower
