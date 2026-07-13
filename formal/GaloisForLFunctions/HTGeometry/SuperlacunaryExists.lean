import Mathlib

/-!
# Superlacunary exponent sequences exist

The factorial shift `bnat n = (n+1)!` is strictly increasing, positive, and has divergent
successive ratio `bnat(n+1)/bnat(n) = n+2 → ∞` (`exists_superlacunary_sequence`).  So the
hypotheses of the gap-series hypertranscendence machinery are satisfiable: there are concrete
integer exponent sequences with the divergent-ratio (superlacunary) property.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- **Existence of a superlacunary sequence.**  There is a strictly increasing positive integer
sequence whose successive ratio diverges to `+∞`. -/
theorem exists_superlacunary_sequence :
    ∃ bnat : ℕ → ℕ, StrictMono bnat ∧ (∀ n, 0 < bnat n) ∧
      Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop := by
  refine ⟨fun n => Nat.factorial (n + 1), ?_, fun n => Nat.factorial_pos (n + 1), ?_⟩
  · intro a b hab
    exact (Nat.factorial_lt (Nat.succ_pos a)).mpr (by omega)
  · have hratio_eq : ∀ n : ℕ,
        (Nat.factorial (n + 1 + 1) : ℝ) / (Nat.factorial (n + 1) : ℝ) = (n : ℝ) + 2 := by
      intro n
      rw [Nat.factorial_succ (n + 1)]
      have hpos : (Nat.factorial (n + 1) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    refine Filter.Tendsto.congr (fun n => (hratio_eq n).symm) ?_
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop

end GaloisForLFunctions
