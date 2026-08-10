import GaloisForLFunctions.RHTower.Sieve.FibreLogCharacterisation

/-!
# The endpoint discrepancy costs one term

The fibre is closed at its left end, `log(x/a) ≤ log b`, while the corpus's logarithmic window is
half-open, `u < log n`.  The two therefore differ by the integers `b` with `log b = log(x/a)`, of
which there is at most one — `log` is injective on the positives — so for a unit-bounded weight the
discrepancy is at most `1` per fibre.

Over the `√x` fibres of a block that is `O(√x)`, against a target `o(h²√x)`: negligible once
`h → ∞`, but not zero, and carried here explicitly rather than waved through.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- At most one positive integer has a given logarithm. -/
theorem card_filter_log_eq_le_one {T : Finset ℕ} (hT : ∀ b ∈ T, 1 ≤ b) (c : ℝ) :
    (T.filter (fun b : ℕ => Real.log (b : ℝ) = c)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  rw [Finset.mem_filter] at ha hb
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hT a ha.1
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hT b hb.1
  have hlog : Real.log (a : ℝ) = Real.log (b : ℝ) := by rw [ha.2, hb.2]
  have hexp : (a : ℝ) = (b : ℝ) := by
    rw [← Real.exp_log ha0, ← Real.exp_log hb0, hlog]
  exact_mod_cast hexp

/-- A sum over a set of at most one element is at most one in absolute value. -/
theorem abs_sum_le_one_of_card_le_one {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {S : Finset ℕ}
    (hS : S.card ≤ 1) : |∑ b ∈ S, f b| ≤ 1 := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun b _ => hf b) ?_
  rw [nsmul_eq_mul, mul_one]
  exact_mod_cast hS

/-- **The closed and half-open windows differ by at most one term.** -/
theorem abs_sum_closed_sub_open_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {T : Finset ℕ}
    (hT : ∀ b ∈ T, 1 ≤ b) (c d : ℝ) :
    |(∑ b ∈ T.filter (fun b : ℕ => c ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ d), f b)
        - ∑ b ∈ T.filter (fun b : ℕ => c < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ d), f b| ≤ 1 := by
  classical
  set Sc := T.filter (fun b : ℕ => c ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ d) with hScdef
  set So := T.filter (fun b : ℕ => c < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ d) with hSodef
  have hsub : So ⊆ Sc := by
    intro b hb
    rw [hSodef, Finset.mem_filter] at hb
    rw [hScdef, Finset.mem_filter]
    exact ⟨hb.1, le_of_lt hb.2.1, hb.2.2⟩
  have hdiff : (∑ b ∈ Sc, f b) - ∑ b ∈ So, f b = ∑ b ∈ Sc \ So, f b := by
    have := Finset.sum_sdiff (f := f) hsub
    linarith [this]
  rw [hdiff]
  refine abs_sum_le_one_of_card_le_one hf ?_
  refine le_trans (Finset.card_le_card ?_) (card_filter_log_eq_le_one hT c)
  intro b hb
  rw [Finset.mem_sdiff, hScdef, hSodef, Finset.mem_filter, Finset.mem_filter] at hb
  rw [Finset.mem_filter]
  refine ⟨hb.1.1, ?_⟩
  by_contra hne
  exact hb.2 ⟨hb.1.1, lt_of_le_of_ne hb.1.2.1 (Ne.symm hne), hb.1.2.2⟩

end RHTower.Sieve

end
