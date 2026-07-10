import GaloisForLFunctions.RHTower.BakerWeldIndependence

/-!
# Minimal-support relations for the Baker proof

This file packages a hypothetical nontrivial algebraic-coefficient relation among distinct prime
logarithms after deleting its zero coefficients.  The formalized two-prime Gelfond--Schneider
fragment then forces every such reduced relation to have arity at least three.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerProof

/-- A nontrivial algebraic-coefficient relation among logarithms of distinct primes, with its support
already reduced so every coefficient is nonzero. -/
structure Relation where
  n : ℕ
  p : Fin n → ℕ
  coeff : Fin n → ℂ
  p_injective : Function.Injective p
  p_prime : ∀ i, (p i).Prime
  coeff_algebraic : ∀ i, IsAlgebraic ℤ (coeff i)
  coeff_ne_zero : ∀ i, coeff i ≠ 0
  vanishes : ∑ i, coeff i * ((Real.log (p i) : ℝ) : ℂ) = 0

/-- Any counterexample to the Baker interface restricts to a reduced relation of arity at least
three.  Arity zero and one are elementary; arity two is the unconditional complex
Gelfond--Schneider fragment. -/
theorem exists_reduced_relation_of_counterexample
    (n : ℕ) (p : Fin n → ℕ) (β : Fin n → ℂ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hβ : ∀ i, IsAlgebraic ℤ (β i))
    (hrel : ∑ i, β i * ((Real.log (p i) : ℝ) : ℂ) = 0)
    (hnontrivial : ∃ i, β i ≠ 0) : ∃ R : Relation, 3 ≤ R.n := by
  let term : Fin n → ℂ := fun i => β i * ((Real.log (p i) : ℝ) : ℂ)
  let s : Finset (Fin n) := Finset.univ.filter fun i => β i ≠ 0
  let e : Fin s.card ≃ s := (s.orderIsoOfFin rfl).toEquiv
  have hsum_s : ∑ i ∈ s, term i = 0 := by
    calc
      ∑ i ∈ s, term i = ∑ i, term i := by
        apply Finset.sum_subset (by simp [s])
        intro i hi hiS
        have hβi : β i = 0 := by
          by_contra hne
          exact hiS (by simp [s, hne])
        simp [term, hβi]
      _ = 0 := hrel
  have hsum_subtype : ∑ i : s, term i = 0 := by
    calc
      ∑ i : s, term i = ∑ i ∈ s, term i := by
        rw [Finset.univ_eq_attach, Finset.sum_attach]
      _ = 0 := hsum_s
  have hsum_fin : ∑ j : Fin s.card, term (e j) = 0 :=
    (e.sum_comp fun i : s => term i).trans hsum_subtype
  let R : Relation :=
    { n := s.card
      p := fun j => p (e j)
      coeff := fun j => β (e j)
      p_injective := by
        intro i j hij
        apply e.injective
        apply Subtype.ext
        exact hp hij
      p_prime := fun j => hprime (e j)
      coeff_algebraic := fun j => hβ (e j)
      coeff_ne_zero := by
        intro j
        exact (Finset.mem_filter.mp (e j).property).2
      vanishes := by
        simpa [term] using hsum_fin }
  refine ⟨R, ?_⟩
  by_contra hlt
  change ¬3 ≤ s.card at hlt
  have hcard : s.card ≤ 2 := by omega
  have hall := bakerLinearIndependence_of_card_le_two R.n (by simpa [R] using hcard)
    R.p R.coeff R.p_injective R.p_prime R.coeff_algebraic R.vanishes
  obtain ⟨i, hi⟩ := hnontrivial
  have hiS : i ∈ s := by simp [s, hi]
  let j : Fin s.card := e.symm ⟨i, hiS⟩
  exact R.coeff_ne_zero j (hall j)

end GaloisForLFunctions.RHTower.BakerProof
