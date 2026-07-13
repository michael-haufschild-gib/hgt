import GaloisForLFunctions.HTGeometry.TranscendentalPowerIndependence

/-!
# Vertex-dimension faithful facet separation

The vertex-count half of the universal upper bound on faithful facet-separation dimension.
For any finite simplicial complex on a vertex set `V`, working in the ambient space `V → ℂ`
of dimension `|V|`, the standard basis together with transcendentally-weighted facet forms
realizes a faithful facet separation:

* the standard basis vectors `a v = Pi.single v 1` are `ℚ`-linearly independent (unconditionally —
  no covering hypothesis is needed, unlike the facet-dimension construction);
* the facet form `ℓ A = ∑_{w ∈ A} τ^{g w} · proj_w` (with `g` a global injective vertex index and
  `τ` transcendental) sends the standard basis vector `a v` to `τ^{g v}` when `v ∈ A` and to `0`
  otherwise, so its zero pattern on the basis is exactly the facet complement;
* the nonzero facet values `{ℓ A (a v) : v ∈ A}` are distinct powers of `τ`, hence `ℚ`-linearly
  independent.

This gives `ffsDim(Δ) ≤ |V|`; combined with the facet-dimension construction it yields the
universal bound `ffsDim(Δ) ≤ min(|V|, |Fac(Δ)|)`.
-/

open Finset

namespace GaloisForLFunctions

/-- **Vertex-dimension faithful facet separation.**  For a transcendental `τ` and any finite
family of facets `fac : Fin m → Finset V` on a finite vertex set `V`, the ambient space `V → ℂ`
of dimension `|V|` carries a faithful facet separation: `ℚ`-independent vectors `a v` (the standard
basis), complex-linear facet forms `ℓ i` whose zero set on the basis is exactly the facet
complement, and `ℚ`-independent nonzero facet values.  Hence `ffsDim(Δ) ≤ |V|`. -/
theorem exists_faithfulFacetSeparation_vertexDim {V : Type*} [Fintype V] [DecidableEq V] {τ : ℂ}
    (hτ : Transcendental ℚ τ) {m : ℕ} (fac : Fin m → Finset V) :
    ∃ (a : V → (V → ℂ)) (ℓ : Fin m → ((V → ℂ) →ₗ[ℂ] ℂ)),
      LinearIndependent ℚ a ∧
      (∀ (i : Fin m) (v : V), ℓ i (a v) = 0 ↔ v ∉ fac i) ∧
      (∀ i : Fin m, LinearIndependent ℚ (fun v : fac i => ℓ i (a v))) := by
  classical
  have hτne : τ ≠ 0 := fun h => hτ (h.symm ▸ isAlgebraic_zero)
  set g : V → ℕ := fun v => ((Fintype.equivFin V) v : ℕ) with hg
  have ginj : Function.Injective g :=
    fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  set a : V → (V → ℂ) := fun v => Pi.single v 1 with ha
  set ℓ : Fin m → ((V → ℂ) →ₗ[ℂ] ℂ) :=
    fun i => ∑ w ∈ fac i, (τ ^ (g w)) • (LinearMap.proj w : (V → ℂ) →ₗ[ℂ] ℂ) with hℓ
  have hterm : ∀ (v w : V),
      ((τ ^ (g w)) • (LinearMap.proj w : (V → ℂ) →ₗ[ℂ] ℂ)) (a v)
        = if w = v then τ ^ (g w) else 0 := by
    intro v w
    rw [LinearMap.smul_apply, LinearMap.proj_apply]
    simp only [ha]
    rw [Pi.single_apply]
    by_cases hwv : w = v
    · rw [if_pos hwv, if_pos hwv, smul_eq_mul, mul_one]
    · rw [if_neg hwv, smul_zero, if_neg hwv]
  have heval : ∀ (i : Fin m) (v : V), ℓ i (a v) = if v ∈ fac i then τ ^ (g v) else 0 := by
    intro i v
    simp only [hℓ]
    rw [LinearMap.sum_apply, Finset.sum_congr rfl (fun w _ => hterm v w),
      Finset.sum_ite_eq' (fac i) v (fun w => τ ^ (g w))]
  refine ⟨a, ℓ, ?_, ?_, ?_⟩
  · rw [ha]
    have hℂ : LinearIndependent ℂ (fun v : V => Pi.single v (1 : ℂ)) := by
      have hb := (Pi.basisFun ℂ V).linearIndependent
      have he : ⇑(Pi.basisFun ℂ V) = fun v : V => Pi.single v (1 : ℂ) := by
        funext v; exact Pi.basisFun_apply ℂ V v
      rwa [he] at hb
    refine hℂ.restrict_scalars ?_
    intro p q hpq
    have hpc : (p : ℂ) = (q : ℂ) := by simpa [Rat.smul_one_eq_cast] using hpq
    exact_mod_cast hpc
  · intro i v
    rw [heval i v]
    by_cases hv : v ∈ fac i
    · rw [if_pos hv]
      exact ⟨fun h => (pow_ne_zero _ hτne h).elim, fun h => (h hv).elim⟩
    · rw [if_neg hv]
      exact ⟨fun _ => hv, fun _ => rfl⟩
  · intro i
    have hfam : (fun v : fac i => ℓ i (a v)) = fun v : fac i => τ ^ (g v.1) := by
      funext v; rw [heval i v.1, if_pos v.2]
    rw [hfam]
    exact transcendental_pow_comp_linearIndependent hτ
      (fun x y h => Subtype.ext (ginj h))

end GaloisForLFunctions
