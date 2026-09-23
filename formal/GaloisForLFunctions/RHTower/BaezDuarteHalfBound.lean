import GaloisForLFunctions.RHTower.BaezDuartePairingSeries
import GaloisForLFunctions.RHTower.BaezDuarteLeastSquares

/-!
# A closed-form Gram entry, and a concrete bound on a Báez-Duarte distance

The rational series of `BaezDuarteGramDiscrete` and the pairing series of `BaezDuartePairingSeries` coincide
at `m = 2`, because `(n mod 2)² = (n mod 2)`.  That evaluates one Gram entry in closed form:

**`bdGram_half` — `bdGram (1/2) (1/2) = (log 2)/4`.**

Feeding it into the quadratic form `bdDist_sq_le_quadratic` with the single modulus `2` and the optimal
coefficient `c = 2` gives the first concrete unconditional upper bound on a Báez-Duarte distance in this
development:

**`bdDist_sq_le_one_sub_log_two` — `d² ≤ 1 − log 2` for the one-generator family `{1/2}`.**

Both are exact, symbolic and unconditional.  The bound is of course very far from `0`; its point is that the
machinery now produces *numbers* rather than only identities, so any proposed coefficient choice can be
evaluated against it.
-/

open Finset

noncomputable section

namespace RHTower

/-- **A closed-form Gram entry.**  The `m = 2` series is the alternating harmonic pairing. -/
theorem bdGram_half : bdGram (1 / (2 : ℝ)) (1 / (2 : ℝ)) = Real.log 2 / 4 := by
  have hgram := hasSum_bdGram_discrete (m₁ := 2) (m₂ := 2) (by norm_num) (by norm_num)
  have hpair := (hasSum_mod_div_mul_succ (m := 2) (by norm_num)).mul_left (1 / 4 : ℝ)
  have hterm : ∀ n : ℕ,
      (1 / 4 : ℝ) * ((((n + 1) % 2 : ℕ) : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      = (((n + 1) % 2 : ℕ) : ℝ) * (((n + 1) % 2 : ℕ) : ℝ)
        / (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have hsq : (((n + 1) % 2 : ℕ) : ℝ) * (((n + 1) % 2 : ℕ) : ℝ) = (((n + 1) % 2 : ℕ) : ℝ) := by
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> rw [h] <;> norm_num
    rw [hsq]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [(funext hterm : (fun n : ℕ => (1 / 4 : ℝ) * _) = _)] at hpair
  have hval := hgram.unique hpair
  push_cast at hval
  rw [hval]
  ring

/-- **A concrete unconditional bound.**  One generator already gives `d² ≤ 1 − log 2`. -/
theorem bdDist_sq_le_one_sub_log_two :
    bdDist (fun _ : Fin 1 => 1 / (2 : ℝ)) ^ (2 : ℕ) ≤ 1 - Real.log 2 := by
  have hθ : ∀ _i : Fin 1, 0 < (1 / (2 : ℝ)) ∧ (1 / (2 : ℝ)) ≤ 1 := by
    intro _
    norm_num
  have h := bdDist_sq_le_quadratic (fun _ : Fin 1 => 1 / (2 : ℝ)) hθ (fun _ : Fin 1 => (2 : ℝ))
  have hlog : Real.log (1 / (2 : ℝ)) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  refine le_trans h ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  rw [hlog, bdGram_half]
  ring_nf
  linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]

end RHTower

end
