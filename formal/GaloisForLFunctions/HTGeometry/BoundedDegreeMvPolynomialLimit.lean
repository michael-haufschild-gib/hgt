/-
# A pointwise limit of bounded-degree polynomials is a bounded-degree polynomial

The evaluation functions of the polynomials of total degree at most `d` in `m` variables span a
finite-dimensional subspace of the space of all functions, because there are only finitely many
monomials of that degree.  A finite-dimensional subspace of a Hausdorff topological vector space is
closed, and pointwise convergence *is* convergence in the product topology, so the limit of such
evaluations is again one.

Main results:
* `monomialFunSpan`, `finiteDimensional_monomialFunSpan` — the finite-dimensional evaluation space.
* `evalFun_mem_monomialFunSpan` — bounded-degree polynomials evaluate into it.
* `exists_poly_of_mem_monomialFunSpan` — everything in it is such an evaluation.
* `mem_of_tendsto_pointwise` — **a finite-dimensional function space is closed under pointwise
  limits**.
* `exists_mvPolynomial_of_tendsto_pointwise` — **the bounded-degree polynomial limit law, in
  several variables**.
-/
import Mathlib

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Finite-dimensional function spaces are closed under pointwise limits -/

theorem mem_of_tendsto_pointwise {X : Type*} {S : Submodule ℂ (X → ℂ)}
    [FiniteDimensional ℂ S] {f : ℕ → (X → ℂ)} (hf : ∀ n, f n ∈ S) {g : X → ℂ}
    (hg : ∀ x, Tendsto (fun n => f n x) atTop (nhds (g x))) : g ∈ S := by
  have hclosed : IsClosed (S : Set (X → ℂ)) := S.closed_of_finiteDimensional
  have htend : Tendsto f atTop (nhds g) := tendsto_pi_nhds.mpr hg
  exact hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hf)

/-! ## The evaluation space of bounded-degree polynomials -/

variable {m d : ℕ}

/-- The evaluation functions of the monomials of total degree at most `d`. -/
def monomialFunSet (m d : ℕ) : Set ((Fin m → ℂ) → ℂ) :=
  {f | ∃ e : Fin m → ℕ, (∑ i, e i) ≤ d ∧ f = fun v : Fin m → ℂ => ∏ i, (v i) ^ (e i)}

theorem finite_monomialFunSet (m d : ℕ) : (monomialFunSet m d).Finite := by
  refine Set.Finite.subset (Set.finite_range
    (fun e : Fin m → Fin (d + 1) => fun v : Fin m → ℂ => ∏ i, (v i) ^ ((e i : ℕ)))) ?_
  rintro f ⟨e, he, rfl⟩
  refine ⟨fun i => ⟨e i, ?_⟩, rfl⟩
  have hle : e i ≤ ∑ j, e j := Finset.single_le_sum (fun j _ => Nat.zero_le (e j))
    (Finset.mem_univ i)
  omega

/-- The finite-dimensional span of the bounded-degree monomial evaluations. -/
def monomialFunSpan (m d : ℕ) : Submodule ℂ ((Fin m → ℂ) → ℂ) :=
  Submodule.span ℂ (monomialFunSet m d)

instance finiteDimensional_monomialFunSpan (m d : ℕ) :
    FiniteDimensional ℂ (monomialFunSpan m d) :=
  FiniteDimensional.span_of_finite ℂ (finite_monomialFunSet m d)

theorem evalFun_mem_monomialFunSpan {P : MvPolynomial (Fin m) ℂ} (hP : P.totalDegree ≤ d) :
    (fun v : Fin m → ℂ => MvPolynomial.eval v P) ∈ monomialFunSpan m d := by
  classical
  have hexp : (fun v : Fin m → ℂ => MvPolynomial.eval v P)
      = ∑ s ∈ P.support, (MvPolynomial.coeff s P) •
          (fun v : Fin m → ℂ => ∏ i, (v i) ^ (s i)) := by
    funext v
    rw [MvPolynomial.eval_eq']
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hexp]
  refine Submodule.sum_mem _ fun s hs => ?_
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun i => s i, ?_, rfl⟩)
  have hsum : ∑ i, s i = s.sum fun _ e => e := by
    rw [Finsupp.sum_fintype]
    intro i
    rfl
  rw [hsum]
  exact le_trans (MvPolynomial.le_totalDegree hs) hP

theorem exists_poly_of_mem_monomialFunSpan {g : (Fin m → ℂ) → ℂ}
    (hg : g ∈ monomialFunSpan m d) :
    ∃ Q : MvPolynomial (Fin m) ℂ, Q.totalDegree ≤ d ∧
      ∀ v, MvPolynomial.eval v Q = g v := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro f ⟨e, he, rfl⟩
    refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1, ?_, ?_⟩
    · refine le_trans (le_of_eq ?_) he
      rw [MvPolynomial.totalDegree_monomial _ (one_ne_zero)]
      rw [Finsupp.sum_fintype]
      · rfl
      · intro i
        rfl
    · intro v
      rw [MvPolynomial.eval_monomial]
      simp
  · exact ⟨0, by simp, by simp⟩
  · rintro f₁ f₂ - - ⟨Q₁, h₁, h₁'⟩ ⟨Q₂, h₂, h₂'⟩
    refine ⟨Q₁ + Q₂, le_trans (MvPolynomial.totalDegree_add _ _) (max_le h₁ h₂), fun v => ?_⟩
    rw [map_add, h₁', h₂']
    rfl
  · rintro c f - ⟨Q, hQ, hQ'⟩
    refine ⟨c • Q, le_trans (MvPolynomial.totalDegree_smul_le _ _) hQ, fun v => ?_⟩
    rw [MvPolynomial.smul_eval, hQ']
    rfl

/-- **The bounded-degree polynomial limit law, in several variables.** -/
theorem exists_mvPolynomial_of_tendsto_pointwise {P : ℕ → MvPolynomial (Fin m) ℂ}
    (hdeg : ∀ n, (P n).totalDegree ≤ d) {g : (Fin m → ℂ) → ℂ}
    (hg : ∀ v, Tendsto (fun n => MvPolynomial.eval v (P n)) atTop (nhds (g v))) :
    ∃ Q : MvPolynomial (Fin m) ℂ, Q.totalDegree ≤ d ∧
      ∀ v, MvPolynomial.eval v Q = g v :=
  exists_poly_of_mem_monomialFunSpan
    (mem_of_tendsto_pointwise (fun n => evalFun_mem_monomialFunSpan (hdeg n)) hg)

end

end GaloisForLFunctions.HTGeometry
