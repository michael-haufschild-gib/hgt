import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalReciprocalRowsCancelAlongTheLongIndex
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsHaveUniformKernelBounds
import GaloisForLFunctions.HTGeometry.IntegerLogGap

/-!
# Long-index cancellation of actual terminal near rows

A nonzero logarithmic shell interaction has integer gap at most the
overlap. Reindexing by that gap exposes a long periodic sum. The
reciprocal kernel and the exact logarithmic kernel differ by a uniform
overlap-over-horizon error on the terminal support.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory

private theorem sum_zero_diagonal_eq_gap_triangles (G : ℕ → ℕ → ℝ) (N : ℕ)
    (hdiag : ∀ n, G n n = 0) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, G n j) =
      ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - d), (G n (n + d) + G (n + d) n) := by
  have hsplit : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, G n j) =
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if n < j then G n j else 0) +
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if j < n then G n j else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rcases lt_trichotomy n j with h | h | h
    · simp only [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
    · subst j
      simp only [hdiag, lt_self_iff_false, if_false, add_zero]
    · simp only [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
  have hdown : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if j < n then G n j else 0) =
      ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - d), G (n + d) n := by
    rw [sum_comm]
    exact sum_sum_ite_lt (fun j n => G n j) N
  rw [hsplit, sum_sum_ite_lt G N, hdown, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => (sum_add_distrib).symm

/-- The larger endpoint pays the integer gap without an exponential strip loss. -/
theorem terminal_gap_le_overlap_of_log_gap {c : ℝ} (hc : 0 ≤ c)
    {N n j : ℕ} (hn : 0 < n) (hnj : n < j) (hjN : j ≤ N)
    (hlog : Real.log j - Real.log n ≤ c / N) : (j : ℝ) - n ≤ c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hn.trans hnj
  have hN0 : (0 : ℝ) < N := hj0.trans_le (by exact_mod_cast hjN)
  have hg := HTGeometry.gap_div_le_log_div hn hnj
  rw [Real.log_div hj0.ne' hn0.ne'] at hg
  have hgap : (j : ℝ) - n ≤ c / N * j := (div_le_iff₀ hj0).mp (hg.trans hlog)
  calc
    _ ≤ c / N * j := hgap
    _ ≤ c / N * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hjN) (div_nonneg hc hN0.le)
    _ = c := by field_simp [hN0.ne']

/-- Both triangles at a fixed positive offset, with the actual logarithmic kernel. -/
def terminalNearOffsetPair (K F : ℝ → ℝ) (c : ℝ) (N : ℕ) (p : ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  (F ((n : ℝ) / N) * p (n + d) + F (((n + d : ℕ) : ℝ) / N) * p n) *
    K ((Real.log (n + d : ℕ) - Real.log n) / (c / N)) /
      (Real.sqrt n * Real.sqrt (n + d : ℕ))

/-- Both triangles with their reciprocal-offset kernel. -/
def terminalLinearOffsetPair (K F : ℝ → ℝ) (c : ℝ) (N : ℕ) (p : ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  (F ((n : ℝ) / N) * p (n + d) + F (((n + d : ℕ) : ℝ) / N) * p n) *
    K ((d : ℝ) * N / (c * n)) / n

/-- A normalized compact shell vanishes beyond the integer overlap strip. -/
theorem terminalNearOffsetPair_eq_zero_of_overlap_lt
    {K : ℝ → ℝ} (hK : ∀ t, 1 ≤ t → K t = 0) (F : ℝ → ℝ) (p : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) {N d n : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnN : n + d ≤ N) (hcd : c < d) : terminalNearOffsetPair K F c N p d n = 0 := by
  have hN0 : (0 : ℝ) < N := by
    have hNpos : 0 < N := by omega
    exact_mod_cast hNpos
  have hw : 0 < c / N := div_pos hc hN0
  have hphase : 1 ≤ (Real.log (n + d : ℕ) - Real.log n) / (c / N) := by
    by_contra h
    have hlog : Real.log (n + d : ℕ) - Real.log n ≤ c / N :=
      ((div_lt_one hw).mp (lt_of_not_ge h)).le
    have hg := terminal_gap_le_overlap_of_log_gap hc.le hn (by omega) hnN hlog
    rw [Nat.cast_add, add_sub_cancel_left] at hg
    exact hcd.not_ge hg
  simp only [terminalNearOffsetPair, hK _ hphase, mul_zero, zero_div]

/-- The actual near pairing is exactly the sum of its two long-index triangles. -/
theorem endpointNearPairSum_eq_terminal_offset_sum
    {K F : ℝ → ℝ} (hK : ∀ t, 1 ≤ t → K t = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (hcN : c ≤ N) (p : ℕ → ℝ) :
    endpointNearPairSum K F 0 2 (c / N) N (fun _ => 1) p =
      ∑ d ∈ Icc 1 ⌊c⌋₊, ∑ n ∈ Icc 1 (N - d), terminalNearOffsetPair K F c N p d n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  let G := fun n j : ℕ => if n = j then (0 : ℝ) else
    F ((n : ℝ) / N) * p j * K (|Real.log j - Real.log n| / (c / N)) /
      (Real.sqrt n * Real.sqrt j)
  have hpunct : endpointNearPairSum K F 0 2 (c / N) N (fun _ => 1) p =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, G n j := by
    unfold endpointNearPairSum
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro j hj
    simp only [G, zero_mul, mul_one]
    by_cases hnj : n = j
    · subst j
      simp only [sub_self, abs_zero, lt_self_iff_false, false_and, if_false, if_true]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      have hpos : 0 < |Real.log j - Real.log n| := by
        apply abs_pos.mpr
        apply sub_ne_zero.mpr
        rcases lt_or_gt_of_ne hnj with h | h
        · exact (Real.log_lt_log hn0 (by exact_mod_cast h)).ne'
        · exact (Real.log_lt_log hj0 (by exact_mod_cast h)).ne
      rw [if_neg hnj]
      by_cases hgap : |Real.log j - Real.log n| ≤ 2 * (c / N)
      · rw [if_pos ⟨hpos, hgap⟩]
      · have hphase : 1 ≤ |Real.log j - Real.log n| / (c / N) := by
          apply (le_div_iff₀ hw).mpr
          linarith only [lt_of_not_ge hgap, hw]
        rw [if_neg (fun hh => hgap hh.2), hK _ hphase, mul_zero, zero_div]
  have hdiag : ∀ n, G n n = 0 := fun n => by simp only [G, if_true]
  have htri : (∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - d), (G n (n + d) + G (n + d) n)) =
      ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - d), terminalNearOffsetPair K F c N p d n := by
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnj : n < n + d := by have := (mem_Icc.mp hd).1; omega
    have hlog : 0 < Real.log (n + d : ℕ) - Real.log n :=
      sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hnj))
    simp only [G, if_neg hnj.ne, if_neg hnj.ne',
      abs_sub_comm (Real.log n) (Real.log (n + d : ℕ)), abs_of_pos hlog,
      terminalNearOffsetPair, mul_comm (Real.sqrt (n + d : ℕ)) (Real.sqrt n)]
    ring
  rw [hpunct, sum_zero_diagonal_eq_gap_triangles G N hdiag, htri]
  have hfloorN : ⌊c⌋₊ ≤ N := by
    exact_mod_cast (Nat.floor_le hc.le).trans hcN
  symm
  apply sum_subset
  · intro d hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans hfloorN⟩
  · intro d hd hdout
    have hcd : c < d := by
      by_contra h
      exact hdout (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, Nat.le_floor (le_of_not_gt h)⟩)
    apply sum_eq_zero
    intro n hn
    exact terminalNearOffsetPair_eq_zero_of_overlap_lt hK F p hc (mem_Icc.mp hn).1
      (mem_Icc.mp hd).1 (by have := (mem_Icc.mp hn).2; omega) hcd

/-- On terminal support the actual pair and its reciprocal model differ by `O(c/N²)`. -/
theorem abs_terminalNearOffsetPair_sub_linear_le
    {K F : ℝ → ℝ} {KL : NNReal} (hKL : LipschitzWith KL K)
    {BF BK B : ℝ} (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {p : ℕ → ℝ} (hB : ∀ n, |p n| ≤ B)
    {c : ℝ} (hc : 1 ≤ c) {N n d : ℕ} (hsmall : 8 * c ≤ N)
    (hn : 0 < n) (hd : 0 < d) (hdc : (d : ℝ) ≤ c) (hnN : n + d ≤ N) :
    |terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n| ≤
      8 * BF * B * (64 * (KL : ℝ) + 4 * BK) * c / (N : ℝ) ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by linarith only [hc0, hsmall]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < (n + d : ℕ) := by
    have hj : 0 < n + d := by omega
    exact_mod_cast hj
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let A := F ((n : ℝ) / N) * p (n + d) + F (((n + d : ℕ) : ℝ) / N) * p n
  change |A * K ((Real.log (n + d : ℕ) - Real.log n) / (c / N)) /
      (Real.sqrt n * Real.sqrt (n + d : ℕ)) - A * K ((d : ℝ) * N / (c * n)) / n| ≤ _
  by_cases hAzero : A = 0
  · rw [hAzero, zero_mul, zero_mul, zero_div, zero_div, sub_self, abs_zero]
    positivity
  have hnmac : (N : ℝ) ≤ 4 * n := by
    by_contra h
    have hlt : (4 : ℝ) * n < N := lt_of_not_ge h
    have hfn : F ((n : ℝ) / N) = 0 := hlow _ ((div_le_iff₀ hN0).mpr (by
      linarith only [hlt, hn0]))
    have hfj : F (((n + d : ℕ) : ℝ) / N) = 0 := hlow _ ((div_le_iff₀ hN0).mpr (by
      rw [Nat.cast_add]
      linarith only [hlt, hdc, hsmall, hn0]))
    exact hAzero (by dsimp only [A]; rw [hfn, hfj, zero_mul, zero_mul, zero_add])
  have hjmac : (N : ℝ) ≤ 4 * (n + d : ℕ) := by
    rw [Nat.cast_add]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith only [hnmac, hd0]
  have hgap : |((n + d : ℕ) : ℝ) - n| ≤ c := by
    simpa only [Nat.cast_add, add_sub_cancel_left, Nat.abs_cast] using hdc
  have hk := abs_sqrt_log_kernel_sub_linear_le hKL hK hc0 hN0
    (by norm_num : (0 : ℝ) ≤ 4) hc0.le hn0 hj0 hgap hnmac hjmac
    (by linarith only [hsmall] : 2 * (4 : ℝ) * c ≤ N)
  have hslog : (N : ℝ) / c * (Real.log (n + d : ℕ) - Real.log n) =
      (Real.log (n + d : ℕ) - Real.log n) / (c / N) := by
    field_simp [hc0.ne', hN0.ne']
    <;> ring
  have hslin : (N : ℝ) / c * ((((n + d : ℕ) : ℝ) - n) / n) =
      (d : ℝ) * N / (c * n) := by
    rw [Nat.cast_add, add_sub_cancel_left]
    ring
  rw [hslog, hslin] at hk
  have hkernel : |Real.sqrt n / Real.sqrt (n + d : ℕ) *
        K ((Real.log (n + d : ℕ) - Real.log n) / (c / N)) -
      K ((d : ℝ) * N / (c * n))| ≤ (64 * (KL : ℝ) + 4 * BK) * c / N := by
    exact hk.trans_eq (by field_simp [hc0.ne'] <;> ring)
  have hAabs : |A| ≤ 2 * BF * B := by
    dsimp only [A]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact (add_le_add (mul_le_mul (hF _) (hB _) (abs_nonneg _) hBF)
      (mul_le_mul (hF _) (hB _) (abs_nonneg _) hBF)).trans_eq (by ring)
  have hAdiv : |A / n| ≤ 8 * BF * B / N := by
    rw [abs_div, abs_of_pos hn0]
    apply (div_le_div_of_nonneg_right hAabs hn0.le).trans
    apply (div_le_div_iff₀ hn0 hN0).mpr
    have hm := mul_le_mul_of_nonneg_left hnmac (show 0 ≤ 2 * BF * B by positivity)
    nlinarith only [hm]
  have heq : A * K ((Real.log (n + d : ℕ) - Real.log n) / (c / N)) /
        (Real.sqrt n * Real.sqrt (n + d : ℕ)) - A * K ((d : ℝ) * N / (c * n)) / n =
      (A / n) * (Real.sqrt n / Real.sqrt (n + d : ℕ) *
        K ((Real.log (n + d : ℕ) - Real.log n) / (c / N)) - K ((d : ℝ) * N / (c * n))) := by
    have hsn := Real.sqrt_pos.mpr hn0
    have hsj := Real.sqrt_pos.mpr hj0
    have hden : A / (Real.sqrt n * Real.sqrt (n + d : ℕ)) =
        A / n * (Real.sqrt n / Real.sqrt (n + d : ℕ)) := by
      calc
        _ = A / (Real.sqrt n) ^ 2 * (Real.sqrt n / Real.sqrt (n + d : ℕ)) := by
          field_simp [hsn.ne', hsj.ne']
          <;> ring
        _ = _ := by rw [Real.sq_sqrt hn0.le]
    calc
      _ = (A / (Real.sqrt n * Real.sqrt (n + d : ℕ))) *
          K ((Real.log (n + d : ℕ) - Real.log n) / (c / N)) -
          (A / n) * K ((d : ℝ) * N / (c * n)) := by ring
      _ = _ := by rw [hden]; ring
  rw [heq, abs_mul]
  exact (mul_le_mul hAdiv hkernel (abs_nonneg _) (by positivity)).trans_eq (by ring)

/-- A mean-zero terminal source cancels along the long index even when its period exceeds overlap. -/
theorem abs_terminal_near_pair_div_overlap_le_long_index
    {K F : ℝ → ℝ} {KL : NNReal} (hKL : LipschitzWith KL K)
    (hKzero : ∀ t, 1 ≤ t → K t = 0)
    {BF BK LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hLF : 0 ≤ LF) (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    (hz : periodicMean p q = 0) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hsmall : 8 * c ≤ N) :
    |endpointNearPairSum K F 0 2 (c / N) N (fun _ => 1) p / c| ≤
      (4 * q * B * (20 * BF * BK + 64 * BF * (KL : ℝ) + 4 * BK * LF) +
        8 * BF * B * (64 * (KL : ℝ) + 4 * BK) * c) / N := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by linarith only [hc0, hsmall]
  have hN : 1 ≤ N := by exact_mod_cast hN0
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hKLp : ∀ x y, |K x - K y| ≤ (KL : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hKL.dist_le_mul x y
  let CW := 20 * BF * BK + 64 * BF * (KL : ℝ) + 4 * BK * LF
  let CK := 64 * (KL : ℝ) + 4 * BK
  let P := 4 * q * B * CW / N + 8 * BF * B * CK * c / N
  have hCW : 0 ≤ CW := by dsimp only [CW]; positivity
  have hCK : 0 ≤ CK := by dsimp only [CK]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hrows : ∀ d ∈ Icc 1 ⌊c⌋₊,
      |∑ n ∈ Icc 1 (N - d), terminalNearOffsetPair K F c N p d n| ≤ P := by
    intro d hd
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdc : (d : ℝ) ≤ c :=
      (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans (Nat.floor_le hc0.le)
    have hshift : 4 * d ≤ N := by
      have hh : (4 : ℝ) * d ≤ N := by linarith only [hdc, hsmall, hc0]
      exact_mod_cast hh
    have hθ : |(d : ℝ) / c| ≤ (1 : ℝ) := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hc0.le), div_le_one hc0]
      exact hdc
    have h₁ := abs_terminal_reciprocal_gap_row_le hF hK hLF KL.2 hFL hKLp hθ hlow
      hq hp hz hB hN (Nat.sub_le N d) (by omega : 4 * (0 : ℕ) ≤ N) d
    have h₂ := abs_terminal_reciprocal_gap_row_le hF hK hLF KL.2 hFL hKLp hθ hlow
      hq hp hz hB hN (Nat.sub_le N d) hshift 0
    have hphase (n : ℕ) : (d : ℝ) / c * N / n = (d : ℝ) * N / (c * n) := by ring
    simp only [Nat.add_zero, hphase, mul_one] at h₁ h₂
    have hlin : |∑ n ∈ Icc 1 (N - d), terminalLinearOffsetPair K F c N p d n| ≤
        4 * q * B * CW / N := by
      have he : (∑ n ∈ Icc 1 (N - d), terminalLinearOffsetPair K F c N p d n) =
          (∑ n ∈ Icc 1 (N - d), F ((n : ℝ) / N) * p (n + d) *
            K ((d : ℝ) * N / (c * n)) / n) +
          ∑ n ∈ Icc 1 (N - d), F (((n + d : ℕ) : ℝ) / N) * p n *
            K ((d : ℝ) * N / (c * n)) / n := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun _ _ => by unfold terminalLinearOffsetPair; ring
      rw [he]
      exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by dsimp only [CW]; ring)
    have herr : |∑ n ∈ Icc 1 (N - d),
        (terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n)| ≤
        8 * BF * B * CK * c / N := by
      calc
        _ ≤ ∑ n ∈ Icc 1 (N - d),
            |terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Icc 1 (N - d), 8 * BF * B * CK * c / (N : ℝ) ^ 2 := by
          apply sum_le_sum
          intro n hn
          exact abs_terminalNearOffsetPair_sub_linear_le hKL hF hK hlow hB hc hsmall
            (mem_Icc.mp hn).1 hd0 hdc (by have := (mem_Icc.mp hn).2; omega)
        _ = (N - d : ℕ) * (8 * BF * B * CK * c / (N : ℝ) ^ 2) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ (N : ℝ) * (8 * BF * B * CK * c / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N d) (by positivity)
        _ = _ := by field_simp [hN0.ne'] <;> ring
    calc
      _ = |(∑ n ∈ Icc 1 (N - d),
            (terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n)) +
          ∑ n ∈ Icc 1 (N - d), terminalLinearOffsetPair K F c N p d n| := by
        rw [sum_sub_distrib, sub_add_cancel]
      _ ≤ _ := ((abs_add_le _ _).trans (add_le_add herr hlin)).trans_eq (by dsimp only [P]; ring)
  rw [endpointNearPairSum_eq_terminal_offset_sum hKzero hc0 hN
    (by linarith only [hc0, hsmall] : c ≤ N) p, abs_div, abs_of_pos hc0]
  calc
    _ ≤ (∑ _d ∈ Icc 1 ⌊c⌋₊, P) / c :=
      div_le_div_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hrows)) hc0.le
    _ = ((⌊c⌋₊ : ℝ) * P) / c := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ (c * P) / c :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le hc0.le) hP) hc0.le
    _ = _ := by dsimp only [P, CW, CK]; field_simp [hc0.ne'] <;> ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminal_gap_le_overlap_of_log_gap
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.endpointNearPairSum_eq_terminal_offset_sum
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminalNearOffsetPair_sub_linear_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_near_pair_div_overlap_le_long_index
