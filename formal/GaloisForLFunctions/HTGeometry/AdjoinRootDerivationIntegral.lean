import GaloisForLFunctions.HTGeometry.AdjoinRootDerivation

/-!
# The derivative of the defining polynomial bounds the extended derivation

Let `S` be a subring of `K` stable under a derivation `D`, and let `p` be irreducible with all
coefficients in `S`.  The extension of `D` to `K[X]/(p)` does not preserve the order `S[α]`, but it
does after one multiplication: `p'(α)·D'` maps `S[α]` into itself.

The reason is the defining equation.  On the generator, `p'(α)·D'α = −p^D(α)`, and `p^D` again has
coefficients in `S`; on a product the Leibniz rule keeps the single factor `p'(α)` outside.  So the
whole obstruction to integrality of the extended derivation is the one element `p'(α)` — classically
the generator of the different of the order `S[α]`.

For a discrete valuation ring `S` this says exactly that the extended derivation lowers the order at
any place above by at most the order of `p'(α)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [CharZero K]
variable {p : K[X]} [Fact (Irreducible p)]

section

variable (S : Subring K)

theorem algebraMap_subring_eq (p : K[X]) (c : S) :
    algebraMap S (AdjoinRoot p) c = algebraMap K (AdjoinRoot p) (c : K) :=
  IsScalarTower.algebraMap_apply S K (AdjoinRoot p) c

/-- A polynomial with coefficients in `S` evaluates at the root inside the order `S[α]`. -/
theorem aeval_root_mem_adjoin {q : K[X]} (hq : ∀ i, q.coeff i ∈ S) :
    Polynomial.aeval (AdjoinRoot.root p) q
      ∈ Algebra.adjoin S ({AdjoinRoot.root p} : Set (AdjoinRoot p)) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  have hc : (q.coeff i) • (AdjoinRoot.root p) ^ i
      = algebraMap S (AdjoinRoot p) ⟨q.coeff i, hq i⟩ * (AdjoinRoot.root p) ^ i := by
    rw [algebraMap_subring_eq S p, Algebra.smul_def]
  rw [hc]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton S _) i)

end

/-- **The different generator clears the extended derivation.** -/
theorem rootEval_derivative_mul_adjoinRootDeriv_mem (D : Derivation R K K) (S : Subring K)
    (hDS : ∀ a ∈ S, D a ∈ S) (hp : ∀ i, p.coeff i ∈ S)
    {f : AdjoinRoot p}
    (hf : f ∈ Algebra.adjoin S ({AdjoinRoot.root p} : Set (AdjoinRoot p))) :
    rootEval R p (derivative p) * adjoinRootDeriv D p f
      ∈ Algebra.adjoin S ({AdjoinRoot.root p} : Set (AdjoinRoot p)) := by
  have hdercoeff : ∀ i, (derivative p).coeff i ∈ S := by
    intro i
    have hcast : ((i : K) + 1) = ((i + 1 : ℕ) : K) := by push_cast; ring
    rw [Polynomial.coeff_derivative, hcast, mul_comm, ← nsmul_eq_mul]
    exact nsmul_mem (hp (i + 1)) (i + 1)
  have hpD : ∀ i, (polyD D p).coeff i ∈ S := by
    intro i
    rw [coeff_polyD]
    exact hDS _ (hp i)
  have hderMem : rootEval R p (derivative p)
      ∈ Algebra.adjoin S ({AdjoinRoot.root p} : Set (AdjoinRoot p)) :=
    aeval_root_mem_adjoin S hdercoeff
  have hroot : rootEval R p (derivative p) * adjoinRootDeriv D p (AdjoinRoot.root p)
      = -(rootEval R p (polyD D p)) := by
    have hne : rootEval R p (derivative p) ≠ 0 := rootEval_derivative_ne_zero
    rw [adjoinRootDeriv_root, rootShift]
    field_simp
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [hroot]
      exact Subalgebra.neg_mem _ (aeval_root_mem_adjoin S hpD)
  | algebraMap c =>
      rw [algebraMap_subring_eq S p, adjoinRootDeriv_algebraMap]
      refine Subalgebra.mul_mem _ hderMem ?_
      have hc : algebraMap K (AdjoinRoot p) (D (c : K))
          = algebraMap S (AdjoinRoot p) ⟨D (c : K), hDS _ c.2⟩ :=
        (algebraMap_subring_eq S p ⟨D (c : K), hDS _ c.2⟩).symm
      rw [hc]
      exact Subalgebra.algebraMap_mem _ _
  | add x y hx hy ihx ihy =>
      rw [map_add, mul_add]
      exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      have hsplit : rootEval R p (derivative p)
          * (x * adjoinRootDeriv D p y + y * adjoinRootDeriv D p x)
          = x * (rootEval R p (derivative p) * adjoinRootDeriv D p y)
            + y * (rootEval R p (derivative p) * adjoinRootDeriv D p x) := by ring
      rw [hsplit]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx ihy) (Subalgebra.mul_mem _ hy ihx)

end GaloisForLFunctions.HTGeometry
