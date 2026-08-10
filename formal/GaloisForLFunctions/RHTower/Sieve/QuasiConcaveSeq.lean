import GaloisForLFunctions.RHTower.Sieve.VariationBimonotone

/-!
# Quasi-concave sequences

A sequence is quasi-concave on `[0, n]` when its superlevel sets are intervals, equivalently when

```text
min (w i) (w k) ≤ w j        for   i ≤ j ≤ k ≤ n .
```

This is the closure-friendly form of "increases then decreases": it is stable under pointwise
`min`, under truncation `max (· ) c`, and it holds for monotone and antitone sequences.  Since an
increasing-then-decreasing sequence has total variation at most twice its range, quasi-concavity
transfers that estimate to any pointwise minimum of monotone pieces — which is exactly the shape of
an interval-count kernel, a minimum of four affine-in-the-endpoints expressions.
-/

namespace RHTower.Sieve

open Finset

/-- A sequence whose superlevel sets on `[0, n]` are intervals. -/
def QuasiConcaveOn (w : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i j k, i ≤ j → j ≤ k → k ≤ n → min (w i) (w k) ≤ w j

/-- Constants are quasi-concave. -/
theorem quasiConcaveOn_const (c : ℝ) (n : ℕ) : QuasiConcaveOn (fun _ => c) n := by
  intro i j k _ _ _
  simp

/-- A nondecreasing sequence is quasi-concave. -/
theorem quasiConcaveOn_of_monotone {w : ℕ → ℝ} {n : ℕ}
    (hmono : ∀ i, i + 1 ≤ n → w i ≤ w (i + 1)) : QuasiConcaveOn w n := by
  have hle : ∀ i j, i ≤ j → j ≤ n → w i ≤ w j := by
    intro i j hij hjn
    induction j with
    | zero =>
        have : i = 0 := Nat.le_zero.1 hij
        rw [this]
    | succ m ih =>
        rcases Nat.lt_or_ge i (m + 1) with hlt | hge
        · have him : i ≤ m := by omega
          exact le_trans (ih him (by omega)) (hmono m (by omega))
        · have : i = m + 1 := by omega
          rw [this]
  intro i j k hij hjk hkn
  exact le_trans (min_le_left _ _) (hle i j hij (by omega))

/-- A nonincreasing sequence is quasi-concave. -/
theorem quasiConcaveOn_of_antitone {w : ℕ → ℝ} {n : ℕ}
    (hanti : ∀ i, i + 1 ≤ n → w (i + 1) ≤ w i) : QuasiConcaveOn w n := by
  have hle : ∀ i j, i ≤ j → j ≤ n → w j ≤ w i := by
    intro i j hij hjn
    induction j with
    | zero =>
        have : i = 0 := Nat.le_zero.1 hij
        rw [this]
    | succ m ih =>
        rcases Nat.lt_or_ge i (m + 1) with hlt | hge
        · have him : i ≤ m := by omega
          exact le_trans (hanti m (by omega)) (ih him (by omega))
        · have : i = m + 1 := by omega
          rw [this]
  intro i j k hij hjk hkn
  exact le_trans (min_le_right _ _) (hle j k hjk hkn)

/-- An increasing-then-decreasing sequence is quasi-concave. -/
theorem quasiConcaveOn_of_bimonotone {w : ℕ → ℝ} {n c : ℕ} (_hc : c ≤ n)
    (h1 : ∀ i, i + 1 ≤ c → w i ≤ w (i + 1))
    (h2 : ∀ i, c ≤ i → i + 1 ≤ n → w (i + 1) ≤ w i) : QuasiConcaveOn w n := by
  -- monotone up to `c`, antitone after
  have hup : ∀ i j, i ≤ j → j ≤ c → w i ≤ w j := by
    intro i j hij hjc
    induction j with
    | zero =>
        have : i = 0 := Nat.le_zero.1 hij
        rw [this]
    | succ m ih =>
        rcases Nat.lt_or_ge i (m + 1) with hlt | hge
        · have him : i ≤ m := by omega
          exact le_trans (ih him (by omega)) (h1 m (by omega))
        · have : i = m + 1 := by omega
          rw [this]
  have hdown : ∀ i j, c ≤ i → i ≤ j → j ≤ n → w j ≤ w i := by
    intro i j hci hij hjn
    induction j with
    | zero =>
        have : i = 0 := Nat.le_zero.1 hij
        rw [this]
    | succ m ih =>
        rcases Nat.lt_or_ge i (m + 1) with hlt | hge
        · have him : i ≤ m := by omega
          exact le_trans (h2 m (by omega) (by omega)) (ih him (by omega))
        · have : i = m + 1 := by omega
          rw [this]
  intro i j k hij hjk hkn
  rcases Nat.lt_or_ge j c with hjc | hjc
  · exact le_trans (min_le_left _ _) (hup i j hij (by omega))
  · exact le_trans (min_le_right _ _) (hdown j k hjc hjk hkn)

/-- Quasi-concavity is stable under pointwise minimum. -/
theorem quasiConcaveOn_min {w v : ℕ → ℝ} {n : ℕ}
    (hw : QuasiConcaveOn w n) (hv : QuasiConcaveOn v n) :
    QuasiConcaveOn (fun i => min (w i) (v i)) n := by
  intro i j k hij hjk hkn
  simp only
  refine le_min ?_ ?_
  · refine le_trans ?_ (hw i j k hij hjk hkn)
    exact min_le_min (min_le_left _ _) (min_le_left _ _)
  · refine le_trans ?_ (hv i j k hij hjk hkn)
    exact min_le_min (min_le_right _ _) (min_le_right _ _)

/-- Quasi-concavity is stable under truncation from below at a constant. -/
theorem quasiConcaveOn_max_const {w : ℕ → ℝ} {n : ℕ} (hw : QuasiConcaveOn w n) (c : ℝ) :
    QuasiConcaveOn (fun i => max (w i) c) n := by
  intro i j k hij hjk hkn
  simp only
  rcases le_or_gt (w i) c with hi | hi
  · calc min (max (w i) c) (max (w k) c) ≤ max (w i) c := min_le_left _ _
      _ = c := max_eq_right hi
      _ ≤ max (w j) c := le_max_right _ _
  · rcases le_or_gt (w k) c with hk | hk
    · calc min (max (w i) c) (max (w k) c) ≤ max (w k) c := min_le_right _ _
        _ = c := max_eq_right hk
        _ ≤ max (w j) c := le_max_right _ _
    · have hi' : max (w i) c = w i := max_eq_left hi.le
      have hk' : max (w k) c = w k := max_eq_left hk.le
      rw [hi', hk']
      exact le_trans (hw i j k hij hjk hkn) (le_max_left _ _)

/-- **A quasi-concave sequence increases and then decreases.** -/
theorem quasiConcaveOn_bimonotone {w : ℕ → ℝ} {n : ℕ} (hw : QuasiConcaveOn w n) :
    ∃ c ≤ n, (∀ i, i + 1 ≤ c → w i ≤ w (i + 1))
      ∧ (∀ i, c ≤ i → i + 1 ≤ n → w (i + 1) ≤ w i) := by
  classical
  obtain ⟨c, hcmem, hcmax⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) w ⟨0, by simp⟩
  rw [Finset.mem_range] at hcmem
  refine ⟨c, by omega, ?_, ?_⟩
  · intro i hi
    have hbase := hw i (i + 1) c (by omega) (by omega) (by omega)
    have hmax : w i ≤ w c := hcmax i (by simp; omega)
    rwa [min_eq_left hmax] at hbase
  · intro i hci hin
    have hbase := hw c i (i + 1) hci (by omega) (by omega)
    have hmax : w (i + 1) ≤ w c := hcmax (i + 1) (by simp; omega)
    rwa [min_eq_right hmax] at hbase

/-- **A quasi-concave sequence has variation at most twice its range.** -/
theorem variation_le_two_range_of_quasiConcave {w : ℕ → ℝ} {n : ℕ} (hw : QuasiConcaveOn w n)
    {L U : ℝ} (hL : ∀ i, i ≤ n → L ≤ w i) (hU : ∀ i, i ≤ n → w i ≤ U) :
    ∑ i ∈ Finset.range n, |w (i + 1) - w i| ≤ 2 * (U - L) := by
  obtain ⟨c, hcn, h1, h2⟩ := quasiConcaveOn_bimonotone hw
  exact variation_le_two_range_of_bimonotone hcn h1 h2 hL hU

end RHTower.Sieve
