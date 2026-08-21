import GaloisForLFunctions.HTGeometry.AppellHumbertAutomorphicFactor

/-!
# The normalised modulus of a lower-automorphic form

The seed hypothesis of the damping datum is a bound on the normalised modulus
`|θ(y)|·exp(−(π/2)·Re H(y,y))`.  That quantity is invariant under the *period group of the form*,
so the hypothesis is a purely local statement: a bound on any set meeting every period orbit is a
bound everywhere.

`thetaNorm_add` in the tree assumes the transformation law for every vector of the ambient space;
a seed only has it for its own period group, so the pointwise version is what is needed here.

* `thetaNorm_add_of` — invariance under one period, from the law at that period alone;
* `thetaNorm_invariant_of_mem_forms` — invariance under the whole period group of the factor;
* `norm_le_of_thetaNorm_le` — the normalised-modulus bound in the shape the decay estimate takes;
* `thetaNorm_le_of_orbitReaching`, `norm_le_of_orbitReaching` — **a bound on a set meeting every
  orbit is a bound everywhere**.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The normalised modulus is invariant under one period**, from the transformation law at that
period alone. -/
theorem thetaNorm_add_of {H : V → V → ℂ} (hH : IsHermitianForm H) {χ : V → ℂ}
    (hχ : ∀ γ, ‖χ γ‖ = 1) {θ : V → ℂ} {γ : V}
    (hθ : ∀ z : V, θ (z + γ) = appellHumbertFactor H χ γ z * θ z) (z : V) :
    thetaNorm H θ (z + γ) = thetaNorm H θ z := by
  have hre : (H (z + γ) (z + γ)).re
      = (H z z).re + 2 * (H z γ).re + (H γ γ).re := by
    rw [hH.add_left, hH.add_right, hH.add_right]
    simp only [Complex.add_re]
    have := hH.re_symm z γ
    linarith
  have hexpid : Real.exp (Real.pi * (H z γ).re + Real.pi / 2 * (H γ γ).re)
      * Real.exp (-(Real.pi / 2) * ((H z z).re + 2 * (H z γ).re + (H γ γ).re))
      = Real.exp (-(Real.pi / 2) * (H z z).re) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [thetaNorm, thetaNorm, hθ, norm_mul, norm_appellHumbertFactor hH hχ, hre]
  linear_combination ‖θ z‖ * hexpid

omit [AddCommGroup V] [Module ℂ V] in
theorem norm_le_of_thetaNorm_le {H : V → V → ℂ} {θ : V → ℂ} {M : ℝ} {y : V}
    (h : thetaNorm H θ y ≤ M) : ‖θ y‖ ≤ M * Real.exp (Real.pi / 2 * (H y y).re) := by
  rw [thetaNorm] at h
  have hpos : (0 : ℝ) < Real.exp (-(Real.pi / 2) * (H y y).re) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos (Real.pi / 2 * (H y y).re)))
  refine le_trans (le_of_eq ?_) hmul
  rw [mul_assoc, ← Real.exp_add]
  have : -(Real.pi / 2) * (H y y).re + Real.pi / 2 * (H y y).re = 0 := by ring
  rw [this, Real.exp_zero, mul_one]

end General

section Lattice

variable {d : ℕ} {H : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χ : (Fin d → ℂ) → ℂ}

/-- **The normalised modulus of a form is invariant under the period group of its factor.** -/
theorem thetaNorm_invariant_of_mem_forms (hH : IsHermitianForm H) (hχ : ∀ γ, ‖χ γ‖ = 1)
    {Γ : AddSubgroup (Fin d → ℂ)} (hsemi : IsSemicharacterOn H χ Γ)
    {f : MultivariateEntire d}
    (hf : f ∈ (appellHumbertAutomorphicFactor hH hχ hsemi).forms) (γ : Γ)
    (z : Fin d → ℂ) : thetaNorm H f.1 (z + γ.1) = thetaNorm H f.1 z := by
  refine thetaNorm_add_of hH hχ (γ := γ.1) (fun x => ?_) z
  exact hf γ x

/-- **A bound on a set meeting every period orbit is a bound everywhere.** -/
theorem thetaNorm_le_of_orbitReaching (hH : IsHermitianForm H) (hχ : ∀ γ, ‖χ γ‖ = 1)
    {Γ : AddSubgroup (Fin d → ℂ)} (hsemi : IsSemicharacterOn H χ Γ)
    {f : MultivariateEntire d}
    (hf : f ∈ (appellHumbertAutomorphicFactor hH hχ hsemi).forms)
    {S : Set (Fin d → ℂ)} (hreach : ∀ y : Fin d → ℂ, ∃ γ : Γ, y - γ.1 ∈ S)
    {M : ℝ} (hbound : ∀ x ∈ S, thetaNorm H f.1 x ≤ M) (y : Fin d → ℂ) :
    thetaNorm H f.1 y ≤ M := by
  obtain ⟨γ, hγ⟩ := hreach y
  have hsplit : y = (y - γ.1) + γ.1 := by ring
  rw [hsplit, thetaNorm_invariant_of_mem_forms hH hχ hsemi hf γ (y - γ.1)]
  exact hbound _ hγ

/-- **The seed hypothesis of the damping datum, from a local bound.** -/
theorem norm_le_of_orbitReaching (hH : IsHermitianForm H) (hχ : ∀ γ, ‖χ γ‖ = 1)
    {Γ : AddSubgroup (Fin d → ℂ)} (hsemi : IsSemicharacterOn H χ Γ)
    {f : MultivariateEntire d}
    (hf : f ∈ (appellHumbertAutomorphicFactor hH hχ hsemi).forms)
    {S : Set (Fin d → ℂ)} (hreach : ∀ y : Fin d → ℂ, ∃ γ : Γ, y - γ.1 ∈ S)
    {M : ℝ} (hbound : ∀ x ∈ S, thetaNorm H f.1 x ≤ M) (y : Fin d → ℂ) :
    ‖f.1 y‖ ≤ M * Real.exp (Real.pi / 2 * (H y y).re) :=
  norm_le_of_thetaNorm_le (thetaNorm_le_of_orbitReaching hH hχ hsemi hf hreach hbound y)

end Lattice

end

end GaloisForLFunctions.HTGeometry
