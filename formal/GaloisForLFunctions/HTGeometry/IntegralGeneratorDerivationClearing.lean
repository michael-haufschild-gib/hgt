import GaloisForLFunctions.HTGeometry.PolyCoeffDerivation

/-!
# The derivative of an annihilator clears the extended derivation at any generator

Let `S` be a subring of a field `K` stable under a derivation `D`, let `L` be a commutative
`K`-algebra carrying a derivation `D'` extending `D`, and let `α : L` be annihilated by a
polynomial `q` with coefficients in `S`.  The extended derivation need not preserve the order
`S[α]`, but it does after one multiplication by `q'(α)`:

`q'(α) · D' f ∈ S[α]`  for every `f ∈ S[α]`.

On the generator this is the chain rule `q'(α)·D'α = −q^D(α)`, where `q^D` acts on the
coefficients and again has coefficients in `S`; on sums and products the Leibniz rule keeps the
single factor `q'(α)` outside.  Classically `q'(α)` generates the different of the order `S[α]`,
so this is the statement that the different clears the extended derivation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R K L : Type*} [CommRing R] [Field K] [CommRing L]
variable [Algebra R K] [Algebra K L] [Algebra R L]

section

variable (S : Subring K)

theorem algebraMap_subring_apply (c : S) :
    algebraMap S L c = algebraMap K L (c : K) :=
  IsScalarTower.algebraMap_apply S K L c

/-- A polynomial with coefficients in `S` evaluates inside the order `S[α]`. -/
theorem aeval_mem_adjoin_singleton {α : L} {q : K[X]} (hq : ∀ i, q.coeff i ∈ S) :
    Polynomial.aeval α q ∈ Algebra.adjoin S ({α} : Set L) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  have hc : (q.coeff i) • α ^ i
      = algebraMap S L ⟨q.coeff i, hq i⟩ * α ^ i := by
    rw [algebraMap_subring_apply S, Algebra.smul_def]
  rw [hc]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton S _) i)

end

/-- **The derivative of the annihilator clears the extended derivation on the order.** -/
theorem aeval_derivative_mul_deriv_mem_adjoin
    (D : Derivation R K K) (D' : Derivation R L L) (S : Subring K)
    (hDS : ∀ a ∈ S, D a ∈ S)
    (hD' : ∀ a : K, D' (algebraMap K L a) = algebraMap K L (D a))
    {α : L} {q : K[X]} (hq : ∀ i, q.coeff i ∈ S) (hqα : Polynomial.aeval α q = 0)
    {f : L} (hf : f ∈ Algebra.adjoin S ({α} : Set L)) :
    Polynomial.aeval α (derivative q) * D' f ∈ Algebra.adjoin S ({α} : Set L) := by
  have hdercoeff : ∀ i, (derivative q).coeff i ∈ S := by
    intro i
    have hcast : ((i : K) + 1) = ((i + 1 : ℕ) : K) := by push_cast; ring
    rw [Polynomial.coeff_derivative, hcast, mul_comm, ← nsmul_eq_mul]
    exact nsmul_mem (hq (i + 1)) (i + 1)
  have hpD : ∀ i, (polyD D q).coeff i ∈ S := by
    intro i
    rw [coeff_polyD]
    exact hDS _ (hq i)
  have hderMem : Polynomial.aeval α (derivative q) ∈ Algebra.adjoin S ({α} : Set L) :=
    aeval_mem_adjoin_singleton S hdercoeff
  have hchain := aeval_polyD D D' α hD' q
  rw [hqα, map_zero] at hchain
  have hroot : Polynomial.aeval α (derivative q) * D' α
      = -(Polynomial.aeval α (polyD D q)) :=
    eq_neg_of_add_eq_zero_right hchain.symm
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [hroot]
      exact Subalgebra.neg_mem _ (aeval_mem_adjoin_singleton S hpD)
  | algebraMap c =>
      rw [algebraMap_subring_apply S, hD']
      refine Subalgebra.mul_mem _ hderMem ?_
      have hc : algebraMap K L (D (c : K))
          = algebraMap S L ⟨D (c : K), hDS _ c.2⟩ :=
        (algebraMap_subring_apply S ⟨D (c : K), hDS _ c.2⟩).symm
      rw [hc]
      exact Subalgebra.algebraMap_mem _ _
  | add x y hx hy ihx ihy =>
      rw [map_add, mul_add]
      exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      have hsplit : Polynomial.aeval α (derivative q) * (x * D' y + y * D' x)
          = x * (Polynomial.aeval α (derivative q) * D' y)
            + y * (Polynomial.aeval α (derivative q) * D' x) := by ring
      rw [hsplit]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx ihy) (Subalgebra.mul_mem _ hy ihx)

end GaloisForLFunctions.HTGeometry
