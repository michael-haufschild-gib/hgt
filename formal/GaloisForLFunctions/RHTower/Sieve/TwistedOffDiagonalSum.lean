import GaloisForLFunctions.RHTower.Sieve.DistinctReciprocalSum
import GaloisForLFunctions.HTGeometry.TwistedMeanValueSplit

/-!
# The twisted off-diagonal row sum

For a twist by `(h/k)^{-it}` the frequency of the pair `(m,n)` is `log(nk) − log(mh)`, and the
window integral is at most `2/|log(nk/mh)|`.  Two elementary facts turn that into a usable bound:

* `|log A − log B| ≥ |A−B|/max(A,B)`, so the reciprocal logarithm is at most `max(A,B)/|A−B|`;
* for fixed `m`, the integers `nk − mh` are distinct and nonzero off the diagonal, so their
  reciprocal-absolute-value sum is at most `2(1 + log #s)`.

Together the row sum of `2/|log(nk/mh)|` is `O(max(nk,mh) · log #s)`.
-/

open Finset
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.Sieve

/-- `|A − B| / max A B ≤ |log A − log B|` for positive reals. -/
theorem abs_sub_div_max_le_abs_log_sub_log {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    |A - B| / max A B ≤ |Real.log A - Real.log B| := by
  rcases le_total B A with hle | hle
  · rw [max_eq_left hle, abs_of_nonneg (by linarith), abs_of_nonneg]
    · exact sub_div_le_log_sub_log hB hle
    · have := sub_div_le_log_sub_log hB hle
      have hpos : (0 : ℝ) ≤ (A - B) / A := by positivity
      linarith
  · rw [max_eq_right hle, abs_sub_comm A B, abs_sub_comm (Real.log A) (Real.log B),
      abs_of_nonneg (by linarith), abs_of_nonneg]
    · exact sub_div_le_log_sub_log hA hle
    · have := sub_div_le_log_sub_log hA hle
      have hpos : (0 : ℝ) ≤ (B - A) / B := by positivity
      linarith

/-- The twisted reciprocal logarithm is at most the larger argument over the integer gap. -/
theorem two_div_abs_log_twisted_le {m n h k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hk : 1 ≤ k) (hne : n * k ≠ m * h) {B : ℝ}
    (hB1 : ((n * k : ℕ) : ℝ) ≤ B) (hB2 : ((m * h : ℕ) : ℝ) ≤ B) :
    2 / |Real.log ((n * k : ℕ) : ℝ) - Real.log ((m * h : ℕ) : ℝ)|
      ≤ 2 * B / |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)| := by
  have hnk : (0 : ℝ) < ((n * k : ℕ) : ℝ) := by
    have : 1 ≤ n * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hmh : (0 : ℝ) < ((m * h : ℕ) : ℝ) := by
    have : 1 ≤ m * h := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hgap : (0 : ℝ) < |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)| := by
    rw [abs_pos, sub_ne_zero]
    intro hcon
    exact hne (by exact_mod_cast hcon)
  have hmax : max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ) ≤ B := max_le hB1 hB2
  have hkey := abs_sub_div_max_le_abs_log_sub_log hnk hmh
  have hlogpos : (0 : ℝ) < |Real.log ((n * k : ℕ) : ℝ) - Real.log ((m * h : ℕ) : ℝ)| := by
    refine lt_of_lt_of_le ?_ hkey
    have hmaxpos : (0 : ℝ) < max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ) :=
      lt_of_lt_of_le hnk (le_max_left _ _)
    positivity
  have hmaxpos : (0 : ℝ) < max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ) :=
    lt_of_lt_of_le hnk (le_max_left _ _)
  rw [div_le_div_iff₀ hlogpos hgap]
  have hstep : |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)|
      ≤ max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ)
        * |Real.log ((n * k : ℕ) : ℝ) - Real.log ((m * h : ℕ) : ℝ)| := by
    rw [div_le_iff₀ hmaxpos] at hkey
    linarith
  nlinarith [hstep, hmax, hlogpos, hmaxpos]

/-- **The twisted off-diagonal row sum.**  For fixed `m`, the integers `nk − mh` are distinct and
nonzero, so their reciprocal sum is harmonic. -/
theorem sum_inv_abs_twisted_row_le {s : Finset ℕ} {m h k : ℕ} (hk : 1 ≤ k) :
    ∑ n ∈ s.filter (fun n => ¬ (n * k = m * h)),
        (1 : ℝ) / |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)|
      ≤ 2 * (1 + Real.log s.card) := by
  classical
  set t : Finset ℕ := s.filter (fun n => ¬ (n * k = m * h)) with ht
  set v : ℕ → ℤ := fun n => (n : ℤ) * (k : ℤ) - (m : ℤ) * (h : ℤ) with hv
  have hinj : ∀ i ∈ t, ∀ j ∈ t, v i = v j → i = j := by
    intro i _ j _ heq
    rw [hv] at heq
    simp only [sub_left_inj] at heq
    have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
    have : (i : ℤ) = (j : ℤ) := by
      exact mul_right_cancel₀ (by exact_mod_cast hk0.ne') heq
    exact_mod_cast this
  have hne : ∀ i ∈ t, v i ≠ 0 := by
    intro i hi
    obtain ⟨-, hfilt⟩ := Finset.mem_filter.mp hi
    rw [hv]
    simp only [sub_ne_zero]
    intro hcon
    exact hfilt (by exact_mod_cast hcon)
  have hcast : ∀ n : ℕ, |((v n : ℤ) : ℝ)| = |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)| := by
    intro n
    rw [hv]
    push_cast
    ring_nf
  have hmain := sum_inv_abs_le_of_injOn t v hinj hne
  have hcong : ∑ n ∈ t, (1 : ℝ) / |((v n : ℤ) : ℝ)|
      = ∑ n ∈ t, (1 : ℝ) / |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)| :=
    Finset.sum_congr rfl fun n _ => by rw [hcast n]
  rw [hcong] at hmain
  refine le_trans hmain ?_
  have hcard : t.card ≤ s.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hmono : Real.log t.card ≤ Real.log s.card := by
    rcases Nat.eq_zero_or_pos t.card with h0 | hpos
    · rw [h0]
      simpa using Real.log_natCast_nonneg s.card
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)
  linarith

end RHTower.Sieve

end
