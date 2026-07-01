import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GaloisForLFunctions.Bottcher.EvenEntireClassification

/-!
# Growth is automatic for entire solutions of the Böttcher functional equation

This file formalises **§3 of the task02 answer**: an entire function `H` satisfying the functional
equation `H(t²) = H(t)² + c·t²` *automatically* has polynomial growth — no growth hypothesis is
needed as an input.  The mechanism is the sub-multiplicative recursion `M(r²) ≤ M(r)² + ‖c‖·r²`
for `M(r) = sup_{|z|≤r} ‖H z‖`, iterated along the doubling exponents `r = 2^{2ⁿ}` to give
`M(2^{2ⁿ}) ≤ K^{2ⁿ}`, i.e. `log M(r) = O(log r)`.

Combined with `c_mem_of_entire_even_functional_eq`, this removes the polynomial-growth hypothesis
from the entire-level classification: an *even entire* solution with `H 0 = 1` already forces
`c ∈ {0, -2}`.
-/

open Complex Metric Set Real Filter Topology

namespace Bottcher

/-- `supNormBall H r` is the supremum of `‖H‖` over the closed ball of radius `r` about `0`. -/
noncomputable def supNormBall (H : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖H z‖) '' Metric.closedBall 0 r)

variable {H : ℂ → ℂ}

lemma bddAbove_normBall (hH : Continuous H) (r : ℝ) :
    BddAbove ((fun z => ‖H z‖) '' Metric.closedBall 0 r) :=
  (isCompact_closedBall (0 : ℂ) r).bddAbove_image hH.norm.continuousOn

lemma norm_le_supNormBall (hH : Continuous H) {r : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 r) : ‖H z‖ ≤ supNormBall H r :=
  le_csSup (bddAbove_normBall hH r) (mem_image_of_mem _ hz)

lemma supNormBall_le {r B : ℝ} (hr : 0 ≤ r)
    (hB : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖H z‖ ≤ B) : supNormBall H r ≤ B := by
  unfold supNormBall
  refine csSup_le ((Metric.nonempty_closedBall.mpr hr).image _) ?_
  rintro x ⟨z, hz, rfl⟩
  exact hB z hz

lemma supNormBall_nonneg (hH : Continuous H) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ supNormBall H r :=
  le_trans (norm_nonneg _)
    (norm_le_supNormBall hH (z := 0) (Metric.mem_closedBall_self hr))

lemma supNormBall_mono (hH : Continuous H) {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') :
    supNormBall H r ≤ supNormBall H r' := by
  unfold supNormBall
  refine csSup_le_csSup (bddAbove_normBall hH r')
    ((Metric.nonempty_closedBall.mpr hr).image _) ?_
  rintro x ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
  linarith

/-- Every point of the closed ball of radius `r²` is the square of a point of radius `≤ r`. -/
lemma sqrt_surj {w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hw : ‖w‖ ≤ r ^ 2) :
    ∃ t : ℂ, t ^ 2 = w ∧ ‖t‖ ≤ r := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
  refine ⟨t, ht, ?_⟩
  have h1 : ‖t‖ ^ 2 = ‖w‖ := by rw [← ht, norm_pow]
  nlinarith [norm_nonneg t]

/-- The key sub-multiplicative recursion: `M(r²) ≤ M(r)² + ‖c‖·r²`. -/
lemma supNormBall_rec (hH : Continuous H) {c : ℂ}
    (hfe : ∀ t : ℂ, H (t ^ 2) = (H t) ^ 2 + c * t ^ 2) {r : ℝ} (hr : 0 ≤ r) :
    supNormBall H (r ^ 2) ≤ (supNormBall H r) ^ 2 + ‖c‖ * r ^ 2 := by
  apply supNormBall_le (by positivity)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  obtain ⟨t, ht, htr⟩ := sqrt_surj hr hz
  have hHt : ‖H t‖ ≤ supNormBall H r :=
    norm_le_supNormBall hH (by rw [Metric.mem_closedBall, dist_zero_right]; exact htr)
  rw [← ht, hfe t]
  calc ‖(H t) ^ 2 + c * t ^ 2‖ ≤ ‖(H t) ^ 2‖ + ‖c * t ^ 2‖ := norm_add_le _ _
    _ = ‖H t‖ ^ 2 + ‖c‖ * ‖t‖ ^ 2 := by rw [norm_pow, norm_mul, norm_pow]
    _ ≤ (supNormBall H r) ^ 2 + ‖c‖ * r ^ 2 := by gcongr

/-- **task02 §3 — growth is automatic.**  An entire `H` with `H(t²) = H(t)² + c·t²` has polynomial
growth: `‖H z‖ ≤ C·(max 1 ‖z‖)^m` for some `C, m`.  No growth hypothesis is assumed. -/
theorem polyGrowth_of_entire_functional_eq {c : ℂ}
    (hH : Differentiable ℂ H)
    (hfe : ∀ t : ℂ, H (t ^ 2) = (H t) ^ 2 + c * t ^ 2) :
    ∃ (C : ℝ) (m : ℕ), ∀ z, ‖H z‖ ≤ C * (max 1 ‖z‖) ^ m := by
  classical
  have hHc : Continuous H := hH.continuous
  set M : ℝ → ℝ := supNormBall H with hMdef
  -- the doubling radii `rn n = 2^(2ⁿ)`
  set rn : ℕ → ℝ := fun n => (2 : ℝ) ^ (2 ^ n) with hrndef
  have hrn0 : rn 0 = 2 := by simp [hrndef]
  have hrn_pos : ∀ n, 0 < rn n := fun n => by simp only [hrndef]; positivity
  have hrn_succ : ∀ n, rn (n + 1) = (rn n) ^ 2 := by
    intro n; simp only [hrndef]; rw [pow_succ, pow_mul]
  -- recursion on `A n = M (rn n)`
  have hA_rec : ∀ n, M (rn (n + 1)) ≤ (M (rn n)) ^ 2 + ‖c‖ * (rn n) ^ 2 := by
    intro n
    rw [hrn_succ n]
    exact supNormBall_rec hHc hfe (hrn_pos n).le
  -- the barrier sequence `B n`
  set B : ℕ → ℝ := fun n => max (M (rn n)) 1 + (‖c‖ + 1) * rn n with hBdef
  have hB1 : ∀ n, 1 ≤ B n := by
    intro n
    have h1 : (1 : ℝ) ≤ max (M (rn n)) 1 := le_max_right _ _
    have h2 : 0 ≤ (‖c‖ + 1) * rn n := by positivity
    simp only [hBdef]; linarith
  have hB_A : ∀ n, M (rn n) ≤ B n := by
    intro n
    have h2 : 0 ≤ (‖c‖ + 1) * rn n := by positivity
    simp only [hBdef]
    have := le_max_left (M (rn n)) 1
    linarith
  have hB_rn : ∀ n, rn n ≤ B n := by
    intro n
    have h1 : rn n ≤ (‖c‖ + 1) * rn n := by nlinarith [norm_nonneg c, (hrn_pos n).le]
    have h2 : (0 : ℝ) ≤ max (M (rn n)) 1 := le_trans zero_le_one (le_max_right _ _)
    simp only [hBdef]; linarith
  have hB_c : ∀ n, (‖c‖ + 1) * rn n ≤ B n := by
    intro n
    have h2 : (0 : ℝ) ≤ max (M (rn n)) 1 := le_trans zero_le_one (le_max_right _ _)
    simp only [hBdef]; linarith
  -- the step inequality `B (n+1) ≤ 3 (B n)²`
  have hB_step : ∀ n, B (n + 1) ≤ 3 * (B n) ^ 2 := by
    intro n
    have hBpos : (0 : ℝ) ≤ B n := le_trans zero_le_one (hB1 n)
    have hMnn : 0 ≤ M (rn n) := supNormBall_nonneg hHc (hrn_pos n).le
    -- (M rn n)² ≤ (B n)²
    have hsq1 : (M (rn n)) ^ 2 ≤ (B n) ^ 2 := pow_le_pow_left₀ hMnn (hB_A n) 2
    -- (‖c‖+1)(rn n)² ≤ (B n)²
    have hsqc : (‖c‖ + 1) * (rn n) ^ 2 ≤ (B n) ^ 2 := by
      have hmul := mul_le_mul (hB_c n) (hB_rn n) (hrn_pos n).le hBpos
      nlinarith [hmul]
    -- ‖c‖(rn n)² ≤ (B n)²
    have hsqc' : ‖c‖ * (rn n) ^ 2 ≤ (B n) ^ 2 := by
      have : ‖c‖ * (rn n) ^ 2 ≤ (‖c‖ + 1) * (rn n) ^ 2 := by nlinarith [sq_nonneg (rn n)]
      linarith
    -- M (rn (n+1)) ≤ 2 (B n)²
    have hMstep : M (rn (n + 1)) ≤ 2 * (B n) ^ 2 := by
      have := hA_rec n; linarith
    have hmax : max (M (rn (n + 1))) 1 ≤ 2 * (B n) ^ 2 := by
      apply max_le hMstep
      nlinarith [hB1 n, sq_nonneg (B n)]
    have hc2 : (‖c‖ + 1) * rn (n + 1) ≤ (B n) ^ 2 := by rw [hrn_succ n]; exact hsqc
    have hBunfold : B (n + 1) = max (M (rn (n + 1))) 1 + (‖c‖ + 1) * rn (n + 1) := rfl
    rw [hBunfold]; linarith
  -- accumulate: `3 B n ≤ K^(2ⁿ)` with `K = 3 B 0`
  set K : ℝ := 3 * B 0 with hKdef
  have hK1 : 1 ≤ K := by have := hB1 0; simp only [hKdef]; linarith
  have hPind : ∀ n, 3 * B n ≤ K ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp [hKdef]
    | succ n ih =>
        have hBpos : (0 : ℝ) ≤ B n := le_trans zero_le_one (hB1 n)
        have h9 : 3 * B (n + 1) ≤ (3 * B n) ^ 2 := by nlinarith [hB_step n]
        have h10 : (3 * B n) ^ 2 ≤ (K ^ (2 ^ n)) ^ 2 := pow_le_pow_left₀ (by positivity) ih 2
        have h11 : (K ^ (2 ^ n)) ^ 2 = K ^ (2 ^ (n + 1)) := by rw [← pow_mul, ← pow_succ]
        linarith
  have hAK : ∀ n, M (rn n) ≤ K ^ (2 ^ n) := by
    intro n
    have h1 := hB_A n
    have h2 := hPind n
    have h3 := hB1 n
    linarith
  -- the exponent `α = 2 log₂ K` and the identity `(rn i)^α = K^(2^(i+1))`
  set α : ℝ := 2 * Real.logb 2 K with hαdef
  have hlogb : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) hK1
  have hα0 : 0 ≤ α := by rw [hαdef]; linarith
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hid : ∀ i, (rn i) ^ α = K ^ (2 ^ (i + 1)) := by
    intro i
    have hbase : rn i = (2 : ℝ) ^ (2 ^ i) := rfl
    rw [hbase, ← Real.rpow_natCast K (2 ^ (i + 1)), ← Real.rpow_natCast (2 : ℝ) (2 ^ i),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        show K = (2 : ℝ) ^ (Real.logb 2 K) from
          (Real.rpow_logb (by norm_num) (by norm_num) hKpos).symm,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [hαdef]
    push_cast [pow_succ]
    ring
  -- final polynomial bound on `M`
  set C : ℝ := max (M 2) 1 with hCdef
  set m : ℕ := Nat.ceil α + 1 with hmdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCnn : 0 ≤ C := le_trans zero_le_one hC1
  have hαm : α ≤ (m : ℝ) := by
    have h1 : α ≤ (Nat.ceil α : ℝ) := Nat.le_ceil α
    have h2 : (Nat.ceil α : ℝ) ≤ (m : ℝ) := by rw [hmdef]; push_cast; linarith
    linarith
  have hbound : ∀ r : ℝ, 0 ≤ r → M r ≤ C * (max 1 r) ^ m := by
    intro r hr
    by_cases hr2 : r ≤ 2
    · -- small radius
      have hMr : M r ≤ M 2 := supNormBall_mono hHc hr hr2
      have hMC : M 2 ≤ C := le_max_left _ _
      have hb1 : (1 : ℝ) ≤ max 1 r := le_max_left _ _
      have hpow1 : (1 : ℝ) ≤ (max 1 r) ^ m := one_le_pow₀ hb1
      calc M r ≤ M 2 := hMr
        _ ≤ C := hMC
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * (max 1 r) ^ m := by apply mul_le_mul_of_nonneg_left hpow1 hCnn
    · -- large radius: use the doubling ladder
      rw [not_le] at hr2
      have hr1 : (1 : ℝ) ≤ r := by linarith
      have hex : ∃ n : ℕ, r ≤ rn n := by
        obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt r (by norm_num : (1:ℝ) < 2)
        refine ⟨k, ?_⟩
        calc r ≤ 2 ^ k := le_of_lt hk
          _ ≤ 2 ^ (2 ^ k) := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt (Nat.lt_two_pow_self))
          _ = rn k := rfl
      have hjspec : r ≤ rn (Nat.find hex) := Nat.find_spec hex
      have hjne : Nat.find hex ≠ 0 := by
        intro h0
        have := Nat.find_spec hex
        rw [h0, hrn0] at this
        linarith
      obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hjne
      rw [hi] at hjspec
      have hlt : rn i < r := by
        have hmin := Nat.find_min hex (m := i) (by rw [hi]; omega)
        rw [not_le] at hmin
        exact hmin
      -- M r ≤ M (rn (i+1)) ≤ K^(2^(i+1)) = (rn i)^α ≤ r^α
      have hMrle : M r ≤ M (rn (i + 1)) := supNormBall_mono hHc hr hjspec
      have hval : M (rn (i + 1)) ≤ K ^ (2 ^ (i + 1)) := hAK (i + 1)
      have hrpow : (rn i) ^ α ≤ r ^ α := Real.rpow_le_rpow (hrn_pos i).le hlt.le hα0
      have hMα : M r ≤ r ^ α := by
        calc M r ≤ M (rn (i + 1)) := hMrle
          _ ≤ K ^ (2 ^ (i + 1)) := hval
          _ = (rn i) ^ α := (hid i).symm
          _ ≤ r ^ α := hrpow
      -- r^α ≤ r^m
      have hrα : r ^ α ≤ r ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 hαm
      have hrnat : r ^ (m : ℝ) = r ^ m := Real.rpow_natCast r m
      have hmaxr : max 1 r = r := max_eq_right hr1
      have hpownn : (0 : ℝ) ≤ (max 1 r) ^ m := by positivity
      calc M r ≤ r ^ α := hMα
        _ ≤ r ^ (m : ℝ) := hrα
        _ = r ^ m := hrnat
        _ = (max 1 r) ^ m := by rw [hmaxr]
        _ ≤ C * (max 1 r) ^ m := le_mul_of_one_le_left hpownn hC1
  -- conclude
  refine ⟨C, m, fun z => ?_⟩
  calc ‖H z‖ ≤ M ‖z‖ :=
        norm_le_supNormBall hHc (mem_closedBall_zero_iff.mpr le_rfl)
    _ ≤ C * (max 1 ‖z‖) ^ m := hbound ‖z‖ (norm_nonneg z)

/-- **Growth-free entire classification.**  An *even entire* `H` with `H(t²) = H(t)² + c·t²` and
`H 0 = 1` forces `c ∈ {0, -2}` — the polynomial-growth hypothesis of
`c_mem_of_entire_even_functional_eq` is now derived, not assumed. -/
theorem c_mem_of_entire_even_functional_eq' {c : ℂ}
    (hH : Differentiable ℂ H) (heven : ∀ z, H (-z) = H z)
    (hfe : ∀ t : ℂ, H (t ^ 2) = (H t) ^ 2 + c * t ^ 2) (h0 : H 0 = 1) :
    c = 0 ∨ c = -2 := by
  obtain ⟨C, m, hg⟩ := polyGrowth_of_entire_functional_eq hH hfe
  exact c_mem_of_entire_even_functional_eq hH hg heven hfe h0

end Bottcher
