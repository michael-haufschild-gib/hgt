import GaloisForLFunctions.RHTower.Sieve.HilbertBilinear

/-!
# Separated points spread linearly

A sequence whose consecutive gaps are at least `δ` separates any two of its terms by at least the
index difference times `δ`:

`λ r + (s - r) δ ≤ λ s`  for `r ≤ s`.

This is the telescoping of the gap hypothesis, and it is what converts a *separation* assumption
into the reciprocal bounds appearing in a Gram row: `|λ r - λ s|^{-1} ≤ ((s-r) δ)^{-1}`, whose sum
over `s ≠ r` is the harmonic series — the source of the logarithmic loss in the weak large sieve,
and the quantity Montgomery–Vaughan's argument avoids by exploiting cancellation instead of
absolute values.
-/

namespace RHTower.Sieve

open Finset

/-- **Separated points spread linearly.** -/
theorem le_of_gap {lam : ℕ → ℝ} {δ : ℝ} (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) :
    ∀ r s : ℕ, r ≤ s → lam r + ((s : ℝ) - r) * δ ≤ lam s := by
  intro r s hrs
  induction s with
  | zero =>
      have hr : r = 0 := by omega
      subst hr
      simp
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hrs with heq | hlt
      · have hr : r = m + 1 := heq
        subst hr
        simp
      · have hrm : r ≤ m := by omega
        have h1 := ih hrm
        have h2 := hgap m
        have hcast : ((m + 1 : ℕ) : ℝ) - r = ((m : ℝ) - r) + 1 := by
          push_cast
          ring
        rw [hcast]
        nlinarith [h1, h2]

/-- The reciprocal separation of two terms is bounded by the index difference. -/
theorem inv_dist_le {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    {r s : ℕ} (hrs : r < s) :
    1 / (lam s - lam r) ≤ 1 / (((s : ℝ) - r) * δ) := by
  have hle := le_of_gap hgap r s (le_of_lt hrs)
  have hrsR : (1 : ℝ) ≤ (s : ℝ) - r := by
    have : (r : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hrs
    linarith
  have hpos : (0 : ℝ) < ((s : ℝ) - r) * δ := by positivity
  exact one_div_le_one_div_of_le hpos (by linarith)

end RHTower.Sieve
