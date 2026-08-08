import GaloisForLFunctions.HTGeometry.AppellHumbertFactor

/-!
# Boundedness of a periodic normalised modulus

A continuous function invariant under a subgroup takes all its values already on any set that
covers the space modulo that subgroup, so a compact such set bounds it.  mathlib has this for a
full `ZLattice`; the statement below asks only for a compact covering set, which is what a
quasi-Abelian period group provides.

Applied to `thetaNorm`, whose period invariance was proved with the Appell--Humbert normal form,
this bounds the normalised modulus of a theta function.  A bounded normalised modulus is exactly
the hypothesis of the Gaussian vanishing argument, so a theta function that is nonzero somewhere on
a complex line forces the Hermitian form to be non-negative in that direction.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- A periodic function attains all its values on a set covering the space modulo the periods. -/
theorem range_subset_image_of_periodic_of_covers {X Y : Type*} [AddGroup X]
    {f : X → Y} {Γ : AddSubgroup X} {K : Set X}
    (hper : ∀ γ ∈ Γ, ∀ z : X, f (z + γ) = f z)
    (hcov : ∀ z : X, ∃ γ ∈ Γ, z - γ ∈ K) :
    Set.range f ⊆ f '' K := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨γ, hγ, hz⟩ := hcov z
  refine ⟨z - γ, hz, ?_⟩
  have h := hper γ hγ (z - γ)
  rw [sub_add_cancel] at h
  exact h.symm

/-- **A periodic continuous function with a compact covering set is bounded above.** -/
theorem exists_bound_of_periodic_of_compact_cover {X : Type*} [AddGroup X] [TopologicalSpace X]
    {f : X → ℝ} {Γ : AddSubgroup X} {K : Set X} (hK : IsCompact K) (hf : Continuous f)
    (hper : ∀ γ ∈ Γ, ∀ z : X, f (z + γ) = f z)
    (hcov : ∀ z : X, ∃ γ ∈ Γ, z - γ ∈ K) :
    ∃ M : ℝ, ∀ z, f z ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image hf).bddAbove
  refine ⟨M, fun z => ?_⟩
  exact hM (range_subset_image_of_periodic_of_covers hper hcov ⟨z, rfl⟩)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **The normalised modulus of a theta function with a compact covering set is bounded.** -/
theorem exists_bound_thetaNorm_of_compact_cover {H : W → W → ℂ} (hH : IsHermitianForm H)
    {χ : W → ℂ} (hχ : ∀ γ, ‖χ γ‖ = 1) {θ : W → ℂ} (hθc : Continuous θ)
    (hHc : Continuous fun z => (H z z).re)
    (hθ : ∀ γ z : W, θ (z + γ) = appellHumbertFactor H χ γ z * θ z)
    {Γ : AddSubgroup W} {K : Set W} (hK : IsCompact K)
    (hcov : ∀ z : W, ∃ γ ∈ Γ, z - γ ∈ K) :
    ∃ M : ℝ, ∀ z, thetaNorm H θ z ≤ M := by
  have hcont : Continuous (thetaNorm H θ) := by
    have h1 : Continuous fun z : W => ‖θ z‖ := hθc.norm
    have h2 : Continuous fun z : W => Real.exp (-(Real.pi / 2) * (H z z).re) :=
      Real.continuous_exp.comp (continuous_const.mul hHc)
    exact h1.mul h2
  refine exists_bound_of_periodic_of_compact_cover hK hcont ?_ hcov
  intro γ _ z
  exact thetaNorm_add hH hχ hθ γ z

/-- **Semi-definiteness in a direction carrying a nonzero value.**  If the normalised modulus is
bounded and the theta function does not vanish identically on a complex line through the origin,
the Hermitian form is non-negative in that direction. -/
theorem nonneg_re_of_thetaNorm_bounded_of_ne_zero {H : W → W → ℂ} (hH : IsHermitianForm H)
    {θ : W → ℂ} (hdiff : Differentiable ℂ θ) {M : ℝ} (hbdd : ∀ z, thetaNorm H θ z ≤ M)
    {v : W} {t₀ : ℂ} (hne : θ (t₀ • v) ≠ 0) :
    0 ≤ (H v v).re := by
  by_contra hlt
  push Not at hlt
  exact hne (eq_zero_along_line_of_neg_of_thetaNorm_bounded hH hdiff hbdd hlt t₀)

/-- **Semi-definiteness from a compact covering set.**  The two previous results composed. -/
theorem nonneg_re_of_compact_cover_of_ne_zero {H : W → W → ℂ} (hH : IsHermitianForm H)
    {χ : W → ℂ} (hχ : ∀ γ, ‖χ γ‖ = 1) {θ : W → ℂ} (hdiff : Differentiable ℂ θ)
    (hHc : Continuous fun z => (H z z).re)
    (hθ : ∀ γ z : W, θ (z + γ) = appellHumbertFactor H χ γ z * θ z)
    {Γ : AddSubgroup W} {K : Set W} (hK : IsCompact K)
    (hcov : ∀ z : W, ∃ γ ∈ Γ, z - γ ∈ K)
    {v : W} {t₀ : ℂ} (hne : θ (t₀ • v) ≠ 0) :
    0 ≤ (H v v).re := by
  obtain ⟨M, hM⟩ :=
    exists_bound_thetaNorm_of_compact_cover hH hχ hdiff.continuous hHc hθ hK hcov
  exact nonneg_re_of_thetaNorm_bounded_of_ne_zero hH hdiff hM hne

end GaloisForLFunctions.HTGeometry
