import GaloisForLFunctions.HTGeometry.TranscendentalPowerIndependence

/-!
# Faithful facet separation exists in dimension `#facets`

For a transcendental `τ`, a finite vertex set covered by `m` facets admits a **faithful facet
separation in dimension `m`** (`exists_faithfulFacetSeparation`): assign each vertex `v` a
distinct global power `τ^{g v}`, and in the facet-coordinate `i` place `τ^{g v}` exactly when
`v ∈ facᵢ`, else `0`.  Then

* the vectors `a_v` are `ℚ`-linearly independent (each facet coordinate reads a `ℚ`-combination of
  distinct powers, so all coefficients vanish);
* the coordinate form `ℓ_i` sends `a_v` to zero exactly when `v ∉ facᵢ`;
* the nonzero values `{ℓ_i(a_v) : v ∈ facᵢ}` are `ℚ`-linearly independent.

Hence `ffsDim(Δ) ≤ #Fac(Δ)` — the upper-bound half of the faithful facet-separation dimension.
-/

open Finset

namespace GaloisForLFunctions

/-- **Faithful facet separation in dimension `#facets`.**  A covered finite vertex set admits, for
any transcendental `τ`, a faithful facet separation into `Fin m → ℂ`. -/
theorem exists_faithfulFacetSeparation {V : Type*} [Fintype V] [DecidableEq V] {τ : ℂ}
    (hτ : Transcendental ℚ τ) {m : ℕ} (fac : Fin m → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ fac i) :
    ∃ a : V → (Fin m → ℂ),
      LinearIndependent ℚ a ∧
      (∀ (i : Fin m) (v : V), a v i = 0 ↔ v ∉ fac i) ∧
      (∀ i : Fin m, LinearIndependent ℚ (fun v : fac i => a v i)) := by
  classical
  have hτne : τ ≠ 0 := fun h => hτ (h.symm ▸ isAlgebraic_zero)
  set g : V → ℕ := fun v => ((Fintype.equivFin V) v : ℕ) with hg
  have ginj : Function.Injective g :=
    fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  set a : V → (Fin m → ℂ) := fun v i => if v ∈ fac i then τ ^ (g v) else 0 with ha
  have hcoord3 : ∀ i : Fin m, LinearIndependent ℚ (fun v : fac i => a v.1 i) := by
    intro i
    have hfam : (fun v : fac i => a v.1 i) = fun v : fac i => τ ^ (g v.1) := by
      funext v; rw [ha]; exact if_pos v.2
    rw [hfam]
    exact transcendental_pow_comp_linearIndependent hτ
      (fun x y h => Subtype.ext (ginj h))
  refine ⟨a, ?_, ?_, hcoord3⟩
  · rw [Fintype.linearIndependent_iff]
    intro q hq v
    obtain ⟨i, hvi⟩ := hcover v
    have hqi : ∑ w, q w • (a w i) = 0 := by
      have h := congrArg (fun z : Fin m → ℂ => z i) hq
      simpa using h
    have hterm : ∀ w, q w • (a w i) = if w ∈ fac i then q w • (τ ^ (g w)) else 0 := by
      intro w; rw [ha]; simp only [smul_ite, smul_zero]
    rw [Finset.sum_congr rfl (fun w _ => hterm w), Finset.sum_ite_mem, Finset.univ_inter] at hqi
    have hsub : ∑ w : fac i, (q w.1) • (τ ^ (g w.1)) = 0 := by
      rw [Finset.sum_coe_sort (fac i) (fun w => q w • τ ^ (g w))]; exact hqi
    exact Fintype.linearIndependent_iff.mp
      (transcendental_pow_comp_linearIndependent hτ (fun x y h => Subtype.ext (ginj h)))
      (fun w => q w.1) hsub ⟨v, hvi⟩
  · intro i v
    simp only [ha]
    by_cases hv : v ∈ fac i
    · rw [if_pos hv]
      exact ⟨fun h => (pow_ne_zero _ hτne h).elim, fun h => (h hv).elim⟩
    · rw [if_neg hv]
      exact ⟨fun _ => hv, fun _ => rfl⟩

end GaloisForLFunctions
