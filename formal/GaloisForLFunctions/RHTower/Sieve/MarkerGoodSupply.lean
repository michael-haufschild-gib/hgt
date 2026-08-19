import GaloisForLFunctions.RHTower.Sieve.MarkerLossDevice

/-!
# Most markers survive an exceptional set of starts

The usable form of the device: if the exceptional starts are few enough against the marker count and
the shifted-pair budget, a definite fraction of the markers has a good start.  The threshold is
`#S · (#M + 2·Pi) ≤ (#M)²/4`, i.e. — with `Pi = O(#M)` from the two-dimensional sieve — an
exceptional *density* bounded by an absolute constant, not by `1/log X`.
-/

namespace RHTower.Sieve

open Finset

/-- **A definite fraction of the markers survives.** -/
theorem half_card_le_card_markers_start_notMem {X : ℕ} {M S : Finset ℕ} {K : ℕ} {Pi : ℝ}
    (hsep : ∀ p ∈ M, ∀ q ∈ M, p < q → X / q = X / p → q ≤ p + K)
    (hpair : ∑ d ∈ Finset.Icc 1 K, (((M.filter (fun p => p + d ∈ M)).card : ℕ) : ℝ) ≤ Pi)
    (hthr : (S.card : ℝ) * ((M.card : ℝ) + 2 * Pi) ≤ ((M.card : ℝ)) ^ 2 / 4) :
    ((M.card : ℝ)) / 2 ≤ (((M.filter (fun p => X / p ∉ S)).card : ℕ) : ℝ) := by
  classical
  have hdev := sq_card_markers_start_mem_le (X := X) (M := M) (S := S) (K := K) hsep hpair
  have hle : (((M.filter (fun p => X / p ∈ S)).card : ℕ) : ℝ) ≤ (M.card : ℝ) / 2 := by
    have hsq : (((M.filter (fun p => X / p ∈ S)).card : ℕ) : ℝ) ^ 2
        ≤ ((M.card : ℝ) / 2) ^ 2 := by
      refine hdev.trans (le_trans hthr (le_of_eq ?_))
      ring
    have h0 : (0 : ℝ) ≤ (((M.filter (fun p => X / p ∈ S)).card : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (M.card : ℝ) / 2 := by positivity
    nlinarith [hsq, h0, h1]
  have hsplit : (M.filter (fun p => X / p ∈ S)).card
      + (M.filter (fun p => X / p ∉ S)).card = M.card := by
    classical
    exact Finset.card_filter_add_card_filter_not (p := fun p => X / p ∈ S)
  have hcast : (((M.filter (fun p => X / p ∈ S)).card : ℕ) : ℝ)
      + (((M.filter (fun p => X / p ∉ S)).card : ℕ) : ℝ) = (M.card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsplit
  linarith

end RHTower.Sieve
