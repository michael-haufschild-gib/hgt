import Mathlib

/-!
# A rationally independent lattice is pairwise incongruent modulo ℤ

If `1, α, β` are linearly independent over `ℚ` (as for `α = log p`, `β = log q` with distinct
primes), then an integer lattice point `m·α + n·β` is itself an integer only trivially
(`int_lattice_eq_zero_of_linearIndependent`), so distinct lattice points are pairwise
incongruent modulo `ℤ` (`incongruent_of_linearIndependent`).

This is the arithmetic separation underlying the finite-shift Gamma cards: pairwise incongruent
real translates along the lattice give a differential field whose shift orbit has no coincidences.
-/

open Finset

namespace GaloisForLFunctions

/-- An integer combination of a rationally independent pair that lands in `ℤ` is trivial. -/
theorem int_lattice_eq_zero_of_linearIndependent {α β : ℝ}
    (hLI : LinearIndependent ℚ (![1, α, β] : Fin 3 → ℝ)) {m n k : ℤ}
    (h : (m : ℝ) * α + (n : ℝ) * β = (k : ℝ)) : m = 0 ∧ n = 0 ∧ k = 0 := by
  have hcomb : ∑ i, (![(-k : ℚ), (m : ℚ), (n : ℚ)] : Fin 3 → ℚ) i •
      (![1, α, β] : Fin 3 → ℝ) i = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def]
    push_cast
    linarith
  have hz := Fintype.linearIndependent_iff.mp hLI _ hcomb
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hz 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    exact_mod_cast h1
  · have h2 := hz 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
    exact_mod_cast h2
  · have h0 := hz 0
    simp only [Matrix.cons_val_zero] at h0
    have : (k : ℚ) = 0 := by linarith
    exact_mod_cast this

/-- **Pairwise incongruence.**  Distinct integer lattice points of a rationally independent pair
are incongruent modulo `ℤ`. -/
theorem incongruent_of_linearIndependent {α β : ℝ}
    (hLI : LinearIndependent ℚ (![1, α, β] : Fin 3 → ℝ)) {m n m' n' : ℤ}
    (h : ∃ k : ℤ, ((m - m' : ℤ) : ℝ) * α + ((n - n' : ℤ) : ℝ) * β = (k : ℝ)) :
    m = m' ∧ n = n' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨hm, hn, _⟩ := int_lattice_eq_zero_of_linearIndependent hLI hk
  exact ⟨by omega, by omega⟩

end GaloisForLFunctions
