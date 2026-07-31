import GaloisForLFunctions.HTGeometry.OrbitFreeness

/-!
# No finitely generated period group contains every prime length

The closed-orbit lengths of a compact finite-dimensional dynamical system lie in a finitely
generated additive subgroup of `ℝ` (the period group).  Deninger's arithmetic flow demands
closed orbits of length `log p` for **every** prime `p`.  This file proves the obstruction:

* `exists_primeLog_not_mem_of_fg` — every finitely generated additive subgroup of `ℝ` misses
  the logarithm of some prime;
* `not_forall_primeLog_mem_of_fg` — hence no finitely generated period group realizes every
  prime length.

Mechanism: a finitely generated subgroup lies in the `ℚ`-span of its finitely many generators,
whose dimension is at most the number of generators; but any `n + 1` distinct prime logarithms
are `ℚ`-linearly independent (`linearIndependent_log_primes` — unique factorization in additive
vocabulary), so they cannot all lie in a span of dimension `n`.

This is the formal core of the falsified item 1 of the prime-holonomy-groupoid card: an
ordinary compact three-dimensional dynamical system, whose period group is finitely generated,
cannot realize all prime lengths — the arithmetic lamination must have a non-finitely-generated
period structure.  Unconditional; no zeta, zero, or positivity input.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Every finitely generated additive subgroup of `ℝ` misses some prime logarithm.** -/
theorem exists_primeLog_not_mem_of_fg {G : AddSubgroup ℝ} (hG : G.FG) :
    ∃ p : Nat.Primes, Real.log (p : ℕ) ∉ G := by
  by_contra hall
  push Not at hall
  obtain ⟨S, hS⟩ := hG
  -- the subgroup lies inside the `ℚ`-span of its generators
  have hsub : (G : Set ℝ) ⊆ (Submodule.span ℚ (S : Set ℝ) : Set ℝ) := by
    rw [← hS]
    have hle : AddSubgroup.closure (S : Set ℝ) ≤
        (Submodule.span ℚ (S : Set ℝ)).toAddSubgroup :=
      (AddSubgroup.closure_le _).mpr Submodule.subset_span
    exact fun x hx => hle hx
  -- `S.card + 1` distinct primes
  set n := S.card with hn
  set emb : ℕ ↪ Nat.Primes := Infinite.natEmbedding Nat.Primes with hemb
  set fam : Fin (n + 1) → ℝ :=
    fun i => Real.log ((emb (i : ℕ) : Nat.Primes) : ℕ) with hfam
  have hind : LinearIndependent ℚ fam :=
    linearIndependent_log_primes.comp (fun i : Fin (n + 1) => emb (i : ℕ))
      (emb.injective.comp Fin.val_injective)
  have hmem : ∀ i, fam i ∈ Submodule.span ℚ (S : Set ℝ) :=
    fun i => hsub (hall _)
  set fam' : Fin (n + 1) → Submodule.span ℚ (S : Set ℝ) :=
    fun i => ⟨fam i, hmem i⟩ with hfam'
  have hind' : LinearIndependent ℚ fam' :=
    LinearIndependent.of_comp (Submodule.span ℚ (S : Set ℝ)).subtype hind
  haveI : FiniteDimensional ℚ (Submodule.span ℚ (S : Set ℝ)) :=
    FiniteDimensional.span_finset ℚ S
  have hcard := hind'.fintype_card_le_finrank
  have hrank : Module.finrank ℚ (Submodule.span ℚ (S : Set ℝ)) ≤ n :=
    finrank_span_finset_le_card S
  rw [Fintype.card_fin] at hcard
  omega

/-- **No finitely generated period group realizes every prime length**: the orbit-length
obstruction for compact finite-dimensional realizations of the arithmetic flow. -/
theorem not_forall_primeLog_mem_of_fg {G : AddSubgroup ℝ} (hG : G.FG) :
    ¬ ∀ p : Nat.Primes, Real.log (p : ℕ) ∈ G := by
  intro hall
  obtain ⟨p, hp⟩ := exists_primeLog_not_mem_of_fg hG
  exact hp (hall p)

end

end GaloisForLFunctions
