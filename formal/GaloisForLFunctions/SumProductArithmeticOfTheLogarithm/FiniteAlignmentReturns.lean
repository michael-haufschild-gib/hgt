import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Finite alignment has no last height

For any finite set of integers, Dirichlet approximation produces a phase
return in `[L,L(Q+1)^|A|]` at precision `2π/(Q+1)`. Consequently fixed
finite phase data cannot bound all aligned heights. A first-return problem
must retain the dependence of the integer cutoff on height.
-/

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open Finset

/-- A quantitative return interval for any finite set of integer logarithms. -/
theorem exists_alignment_in_scaled_interval (A : Finset ℕ) (Q : ℕ)
    {L : ℝ} (hL : 0 < L) :
    ∃ t : ℝ, L ≤ t ∧ t ≤ L * ((Q + 1 : ℕ) : ℝ) ^ A.card ∧
      ∀ n ∈ A, ∃ m : ℤ, |t * Real.log n - 2 * Real.pi * m| <
        2 * Real.pi / (Q + 1 : ℕ) := by
  classical
  let e := A.equivFin
  obtain ⟨q, hq1, hqQ, hq⟩ := HTGeometry.exists_simultaneous_dirichlet
    (fun i : Fin A.card => L * Real.log ((e.symm i : A) : ℕ) / (2 * Real.pi))
    (Nat.succ_pos Q)
  refine ⟨(q : ℝ) * L, ?_, ?_, ?_⟩
  · have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1' hL.le
  · have hqQ' : (q : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) ^ A.card := by exact_mod_cast hqQ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hqQ' hL.le
  · intro n hn
    obtain ⟨m, hm⟩ := hq (e ⟨n, hn⟩)
    simp only [Equiv.symm_apply_apply] at hm
    refine ⟨m, ?_⟩
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have he : (q : ℝ) * L * Real.log n - 2 * Real.pi * m =
        (2 * Real.pi) * ((q : ℝ) * (L * Real.log n / (2 * Real.pi)) - m) := by
      field_simp
    rw [he, abs_mul, abs_of_pos hpi]
    calc
      _ < (2 * Real.pi) * (1 / ((Q + 1 : ℕ) : ℝ)) := mul_lt_mul_of_pos_left hm hpi
      _ = 2 * Real.pi / (Q + 1 : ℕ) := by ring

/-- The whole finite set aligns again above every height. -/
theorem exists_alignment_above (A : Finset ℕ) (Q : ℕ) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ ∀ n ∈ A, ∃ m : ℤ,
      |t * Real.log n - 2 * Real.pi * m| < 2 * Real.pi / (Q + 1 : ℕ) := by
  obtain ⟨t, ht, _, ha⟩ := exists_alignment_in_scaled_interval A Q
    (L := max T 0 + 1) (by have := le_max_right T 0; linarith)
  exact ⟨t, by have := le_max_left T 0; linarith, ha⟩

/-- No bound depending only on fixed finite data can bound every aligned height. -/
theorem not_exists_last_alignment (A : Finset ℕ) (Q : ℕ) :
    ¬ ∃ T : ℝ, ∀ t : ℝ,
      (∀ n ∈ A, ∃ m : ℤ,
        |t * Real.log n - 2 * Real.pi * m| < 2 * Real.pi / (Q + 1 : ℕ)) → t ≤ T := by
  rintro ⟨T, hT⟩
  obtain ⟨t, ht, ha⟩ := exists_alignment_above A Q T
  exact (not_le_of_gt ht) (hT t ha)

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
