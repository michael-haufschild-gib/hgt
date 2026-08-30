import GaloisForLFunctions.HTGeometry.RittMinimalCollapse
import GaloisForLFunctions.HTGeometry.RittHomogeneousBaseRelation

/-!
# Ritt's implication, reduced to two base obstructions

Collecting everything: a differentially algebraic linearizer whose first two jets are independent
either satisfies Ritt's order-one relation, or the base carries one of two relations.

The tower descent leaves `ψ(u) = c·u + g` with `c = q^i·ρ^k` and `g` zero or a nonzero multiple of a
Faà di Bruno coefficient.  When `g = 0` and the exponent pair is not `(0,0)` the relation is an
invariant differential, and `exists_rittForm_of_homogeneous_base_relation` converts it into Ritt's
form.  So only two possibilities survive:

* an **affine obstruction** `ψ(u) = q^i·ρ^k·u + z·A_j` with `z ≠ 0` — for `n = 2` this is the
  rational affine-connection equation `a(R)·(R′)² = R′·a − R″`;
* a **degenerate** exponent cancellation, leaving only `ψ(u) = u`, which carries no information.

Ruling out the first for a given map is the obstruction problem that
`RationalAffineConnection.lean` solves for the affine connection; the second is the exponent
bookkeeping the descent does not yet exclude.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Ritt's implication, reduced to the base obstructions.** -/
theorem rittForm_or_affineObstruction_or_degenerate
    [Differential K] [Differential L] [DifferentialAlgebra K L] [CharZero K] [CharZero L]
    (Fr : RittFrame K L) (hd : Fr.d = ⇑(Differential.deriv : Derivation ℤ L L))
    {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (htr0 : Transcendental ↥(Fr.jetPrefixField τ 0) τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    (hjets : ∀ m : ℕ, Fr.d^[m] τ ≠ 0)
    (hDA : DifferentialAlgebraicOver K τ) :
    (∃ (r j : ℤ) (A : K), r ≠ 0 ∧ A ≠ 0 ∧ (Fr.d τ) ^ r = algebraMap K L A * τ ^ j) ∨
      (∃ (n : ℕ) (A : ℕ → K) (u : K) (i k : ℤ) (p : ℕ) (z : K), 2 ≤ n ∧ u ≠ 0 ∧ z ≠ 0 ∧
        (Fr.σ (Fr.d^[n] τ) = algebraMap K L (q / Fr.ρ ^ n) * Fr.d^[n] τ
          + ∑ j ∈ Finset.range n, algebraMap K L (A j) * Fr.d^[j] τ) ∧
        Fr.ψ u = q ^ i * Fr.ρ ^ k * u + z * A p) ∨
      (∃ u : K, u ≠ 0 ∧ Fr.ψ u = u) := by
  rcases rittForm_or_jet_mem_jetPrefixField Fr hd hτ hdτ hq hqconst hshift hDA with h | ⟨N, _, hmem⟩
  · exact Or.inl h
  obtain ⟨n, A, u, c, g, hn2, hu0, hc0, ⟨i, k, hcik⟩, hA, hginv, hrel⟩ :=
    exists_base_relation_of_collapse Fr hτ hdτ hq hqconst hshift htr0 htr1 hjets ⟨N, hmem⟩
  rcases hginv with hg0 | ⟨p, z, hz0, hz⟩
  · -- homogeneous: either Ritt's form or a total cancellation of the exponents
    rw [hg0, add_zero, hcik] at hrel
    by_cases hik : i = 0 ∧ k = 0
    · refine Or.inr (Or.inr ⟨u, hu0, ?_⟩)
      rw [hrel, hik.1, hik.2, zpow_zero, zpow_zero, one_mul, one_mul]
    · refine Or.inl (exists_rittForm_of_homogeneous_base_relation Fr hτ hdτ hq hqconst hshift
        hu0 ?_ hrel)
      by_cases hi : i = 0
      · exact Or.inr (fun hk => hik ⟨hi, hk⟩)
      · exact Or.inl hi
  · exact Or.inr (Or.inl ⟨n, A, u, i, k, p, z, hn2, hu0, hz0, hA, by rw [hrel, hcik, hz]⟩)

end GaloisForLFunctions.HTGeometry
