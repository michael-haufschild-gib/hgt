import Mathlib

/-!
# The observability-deficit allocation law

The card's section 3 is exact finite-dimensional linear algebra, proved here in full.

*Injectivity on the invisible directions.*  If the combined differential `(O_r(B), C)` has trivial
kernel, then `dC` restricted to `ker d(O_r(B))` is injective — equation `(8)`.

*The deficit bound.*  Hence `dim ker d(O_r(B)) ≤ rank dC`, and by rank–nullity
`k − ρ_r(B) ≤ rank dC ≤ q` — equations `(9)`, `(10)`.

*The cofinal consequence.*  With a bounded scalar jet depth `ρ_r ≤ r` this forces
`q ≥ k − r` — equation `(17)`.

The Vandermonde faithfulness `(5)`, the signed-Cauchy index theorem `(13)`, the stratified
residue-birth statement `(15e)`, and the divisor-convergence bound `(18)` are cited parents (the
index theorem itself is `RHTower/CCMRelativeLogDerivCoordinateIndex.lean`) and stay outside the
Lean statement.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {V W₁ W₂ : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

/-! ## Injectivity on the invisible directions -/

/-- **Equation (8).**  Incidence faithfulness makes the relative differential injective on the
directions invisible to the scalar jet. -/
theorem domRestrict_ker_injective (f : V →ₗ[ℂ] W₁) (g : V →ₗ[ℂ] W₂)
    (h : ∀ v : V, f v = 0 → g v = 0 → v = 0) :
    Function.Injective (g.domRestrict (LinearMap.ker f)) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have hgx : g (x : V) = 0 := by
    simpa [LinearMap.domRestrict_apply] using hx
  have hfx : f (x : V) = 0 := x.2
  have hzero : (x : V) = 0 := h _ hfx hgx
  exact Subtype.ext hzero

/-! ## The deficit bound -/

/-- **Equation (9).**  The scalar observability deficit is bounded by the rank of the relative
differential. -/
theorem finrank_ker_le_finrank_range [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] W₁) (g : V →ₗ[ℂ] W₂)
    (h : ∀ v : V, f v = 0 → g v = 0 → v = 0) :
    Module.finrank ℂ (LinearMap.ker f) ≤ Module.finrank ℂ (LinearMap.range g) := by
  have hinj := domRestrict_ker_injective f g h
  have hrange : Module.finrank ℂ (LinearMap.ker f)
      = Module.finrank ℂ (LinearMap.range (g.domRestrict (LinearMap.ker f))) :=
    (LinearMap.finrank_range_of_inj hinj).symm
  rw [hrange]
  refine Submodule.finrank_mono ?_
  rintro y ⟨x, rfl⟩
  exact ⟨(x : V), rfl⟩

/-- **Equation (10).**  Rank–nullity turns the deficit bound into the allocation inequality. -/
theorem observability_allocation [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] W₁) (g : V →ₗ[ℂ] W₂)
    (h : ∀ v : V, f v = 0 → g v = 0 → v = 0) :
    Module.finrank ℂ V
      ≤ Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.range g) := by
  have hrn : Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f)
      = Module.finrank ℂ V := LinearMap.finrank_range_add_finrank_ker f
  have hle := finrank_ker_le_finrank_range f g h
  omega

/-! ## The cofinal consequence -/

/-- **Equation (17).**  A bounded scalar jet depth forces a cofinally growing relative index. -/
theorem index_ge_of_bounded_jet {k rho r q : ℕ} (halloc : k ≤ rho + q) (hjet : rho ≤ r) :
    k - r ≤ q := by omega

/-- **Equation (4).**  The scalar jet can see at most `min(r,k)` directions. -/
theorem jet_rank_le [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] W₁) [FiniteDimensional ℂ W₁] :
    Module.finrank ℂ (LinearMap.range f) ≤ min (Module.finrank ℂ W₁) (Module.finrank ℂ V) := by
  refine le_min (Submodule.finrank_le _) ?_
  have hrn : Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f)
      = Module.finrank ℂ V := LinearMap.finrank_range_add_finrank_ker f
  omega

end GaloisForLFunctions.RHTower

end
