import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalNearRowsCancelAlongTheLongIndex
import Mathlib.Data.Finset.Max

/-!
# Long-index cancellation on logarithmic annuli

For a fixed integer gap the logarithmic selector is an interval in the
long index. Periodic interval cancellation therefore survives sharp
annular cutoffs. Rescaling the actual near-kernel estimate retains an
explicit polynomial dependence on the outer scaled gap.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory

/-- At a fixed positive offset the logarithmic gap decreases with its lower endpoint. -/
theorem terminal_logarithmic_gap_antitone (d : ℕ) {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) :
    Real.log (n + d : ℕ) - Real.log n ≤ Real.log (m + d : ℕ) - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := hm0.trans_le (by exact_mod_cast hmn)
  have hmd0 : (0 : ℝ) < (m + d : ℕ) := by positivity
  have hnd0 : (0 : ℝ) < (n + d : ℕ) := by positivity
  rw [← Real.log_div hnd0.ne' hn0.ne', ← Real.log_div hmd0.ne' hm0.ne']
  apply Real.log_le_log (div_pos hnd0 hn0)
  simp only [Nat.cast_add, add_div, div_self hm0.ne', div_self hn0.ne']
  exact add_le_add_left (div_le_div_of_nonneg_left (Nat.cast_nonneg d) hm0
    (by exact_mod_cast hmn)) 1

/-- The long-index interval selected by a logarithmic annulus. -/
def terminalLogarithmicGapInterval (α β w : ℝ) (N d : ℕ) : Finset ℕ :=
  (Icc 1 (N - d)).filter fun n =>
    α * w < Real.log (n + d : ℕ) - Real.log n ∧
      Real.log (n + d : ℕ) - Real.log n ≤ β * w

/-- Every nonempty logarithmic selector is the interval between its two extreme indices. -/
theorem terminalLogarithmicGapInterval_eq_Icc (α β w : ℝ) (N d : ℕ)
    (hS : (terminalLogarithmicGapInterval α β w N d).Nonempty) :
    terminalLogarithmicGapInterval α β w N d =
      Icc ((terminalLogarithmicGapInterval α β w N d).min' hS)
        ((terminalLogarithmicGapInterval α β w N d).max' hS) := by
  let S := terminalLogarithmicGapInterval α β w N d
  have ha := mem_filter.mp (S.min'_mem hS)
  have hb := mem_filter.mp (S.max'_mem hS)
  ext n
  constructor
  · intro hn
    exact mem_Icc.mpr ⟨S.min'_le n hn, S.le_max' n hn⟩
  · intro hn
    obtain ⟨han, hnb⟩ := mem_Icc.mp hn
    have hn1 : 1 ≤ n := (mem_Icc.mp ha.1).1.trans han
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hn1, hnb.trans (mem_Icc.mp hb.1).2⟩, ?_⟩
    exact ⟨hb.2.1.trans_le (terminal_logarithmic_gap_antitone d hn1 hnb),
      (terminal_logarithmic_gap_antitone d (mem_Icc.mp ha.1).1 han).trans ha.2.2⟩

/-- A sharp logarithmic selector costs the same two prefix bounds as any moving interval. -/
theorem abs_terminal_reciprocal_gap_selected_le
    {F K : ℝ → ℝ} {BF BK LF LK T θ : ℝ}
    (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hLF : 0 ≤ LF) (hLK : 0 ≤ LK)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    (hKL : ∀ x y, |K x - K y| ≤ LK * |x - y|) (hθ : |θ| ≤ T)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    (hz : periodicMean p q = 0) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {N s : ℕ} (hN : 1 ≤ N) (hs : 4 * s ≤ N) (t d : ℕ) (α β w : ℝ) :
    |∑ n ∈ terminalLogarithmicGapInterval α β w N d,
      F (((n + s : ℕ) : ℝ) / N) * p (n + t) * K (θ * N / n) / n| ≤
      4 * q * B * (20 * BF * BK + 64 * BF * LK * T + 4 * BK * LF) / N := by
  classical
  let S := terminalLogarithmicGapInterval α β w N d
  by_cases hS : S.Nonempty
  · have ha := mem_filter.mp (S.min'_mem hS)
    have hb := mem_filter.mp (S.max'_mem hS)
    rw [terminalLogarithmicGapInterval_eq_Icc α β w N d hS]
    exact abs_terminal_reciprocal_gap_interval_le hF hK hLF hLK hFL hKL hθ hlow
      hq hp hz hB (mem_Icc.mp ha.1).1 hN ((mem_Icc.mp hb.1).2.trans (Nat.sub_le N d)) hs t
  · have he : terminalLogarithmicGapInterval α β w N d = ∅ :=
      not_nonempty_iff_eq_empty.mp hS
    rw [he, sum_empty, abs_zero]
    have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
    have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    have hT : 0 ≤ T := (abs_nonneg _).trans hθ
    positivity

/-- Reindexing a sharp annulus retains its exact long-index selector and only `Tc` gaps. -/
theorem endpointNearPairSum_eq_annular_offset_sum (K F : ℝ → ℝ) (p : ℕ → ℝ)
    {α β T c : ℝ} (hα : 0 ≤ α) (hβT : β ≤ T) (hT : 0 < T) (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (hTcN : T * c ≤ N) :
    endpointNearPairSum K F α β (c / N) N (fun _ => 1) p =
      ∑ d ∈ Icc 1 ⌊T * c⌋₊,
        ∑ n ∈ terminalLogarithmicGapInterval α β (c / N) N d,
          terminalNearOffsetPair K F c N p d n := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  let G := fun n j : ℕ =>
    if α * (c / N) < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ β * (c / N) then
      F ((n : ℝ) / N) * p j * K (|Real.log j - Real.log n| / (c / N)) /
        (Real.sqrt n * Real.sqrt j) else 0
  have hdiag : ∀ n, G n n = 0 := by
    intro n
    have hnot : ¬α * (c / N) < (0 : ℝ) := not_lt.mpr (mul_nonneg hα hw.le)
    simp only [G, sub_self, abs_zero, hnot, false_and, if_false]
  have htri : (∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - d), (G n (n + d) + G (n + d) n)) =
      ∑ d ∈ Icc 1 N, ∑ n ∈ terminalLogarithmicGapInterval α β (c / N) N d,
        terminalNearOffsetPair K F c N p d n := by
    apply sum_congr rfl
    intro d hd
    rw [terminalLogarithmicGapInterval, sum_filter]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnj : n < n + d := by have := (mem_Icc.mp hd).1; omega
    have hlog : 0 < Real.log (n + d : ℕ) - Real.log n :=
      sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hnj))
    simp only [G, abs_sub_comm (Real.log n) (Real.log (n + d : ℕ)), abs_of_pos hlog,
      terminalNearOffsetPair, mul_comm (Real.sqrt (n + d : ℕ)) (Real.sqrt n)]
    split_ifs <;> ring
  change (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    if _ then F ((n : ℝ) / N) * 1 * p j * K _ / _ else 0) = _
  simp only [mul_one]
  change (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, G n j) = _
  rw [sum_zero_diagonal_eq_gap_triangles G N hdiag, htri]
  have hfloorN : ⌊T * c⌋₊ ≤ N := by
    exact_mod_cast (Nat.floor_le (mul_pos hT hc).le).trans hTcN
  symm
  apply sum_subset
  · intro d hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans hfloorN⟩
  · intro d hd hout
    apply sum_eq_zero
    intro n hn
    obtain ⟨hn, hgap⟩ := mem_filter.mp hn
    have hnN : n + d ≤ N := by have := (mem_Icc.mp hn).2; omega
    have hlog : Real.log (n + d : ℕ) - Real.log n ≤ (T * c) / N := by
      exact hgap.2.trans ((mul_le_mul_of_nonneg_right hβT hw.le).trans_eq (by ring))
    have hg := terminal_gap_le_overlap_of_log_gap (mul_pos hT hc).le
      (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hd).1; omega) hnN hlog
    rw [Nat.cast_add, add_sub_cancel_left] at hg
    exact (hout (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, Nat.le_floor hg⟩)).elim

/-- Rescaling the near-kernel comparison gives a uniform error through an arbitrary outer gap. -/
theorem abs_terminal_annular_offset_sub_linear_le
    {K F : ℝ → ℝ} {KL : NNReal} (hKL : LipschitzWith KL K)
    {BF BK B : ℝ} (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {p : ℕ → ℝ} (hB : ∀ n, |p n| ≤ B)
    {T c : ℝ} (hT : 1 ≤ T) (hc : 1 ≤ c) {N n d : ℕ} (hsmall : 8 * (T * c) ≤ N)
    (hn : 0 < n) (hd : 0 < d) (hdc : (d : ℝ) ≤ T * c) (hnN : n + d ≤ N) :
    |terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n| ≤
      8 * BF * B * (64 * (KL : ℝ) * T + 4 * BK) * T * c / (N : ℝ) ^ 2 := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by nlinarith only [hsmall, mul_pos hT0 hc0]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let Kt := fun s : ℝ => K (T * s)
  let KLt : NNReal := ⟨T * (KL : ℝ), mul_nonneg hT0.le KL.2⟩
  have hKLt : LipschitzWith KLt Kt := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := hKL.dist_le_mul (T * x) (T * y)
    rw [Real.dist_eq, Real.dist_eq] at hh ⊢
    exact hh.trans_eq (by
      rw [← mul_sub, abs_mul, abs_of_pos hT0]
      dsimp only [KLt]
      ring)
  have hTc1 : 1 ≤ T * c := by
    simpa only [one_mul] using mul_le_mul hT hc zero_le_one hT0.le
  have ht := abs_terminalNearOffsetPair_sub_linear_le hKLt hF (fun x => hK (T * x))
    hlow hB hTc1 hsmall hn hd hdc hnN
  have hlog (u : ℝ) : T * (u / ((T * c) / N)) = u / (c / N) := by
    field_simp [hT0.ne', hc0.ne', hN0.ne'] <;> ring
  have hlin : T * ((d : ℝ) * N / ((T * c) * n)) = (d : ℝ) * N / (c * n) := by
    field_simp [hT0.ne', hc0.ne', hn0.ne'] <;> ring
  dsimp only [terminalNearOffsetPair, terminalLinearOffsetPair, Kt] at ht
  rw [hlog, hlin] at ht
  exact ht.trans_eq (by dsimp only [KLt]; ring)

/-- Periodic cancellation on a sharp annulus retains explicit quadratic and cubic outer-gap costs. -/
theorem abs_terminal_annular_pair_div_overlap_le_long_index
    {K F : ℝ → ℝ} {KL : NNReal} (hKL : LipschitzWith KL K)
    {BF BK LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hLF : 0 ≤ LF) (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    (hz : periodicMean p q = 0) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {α β T c : ℝ} (hα : 0 ≤ α) (hβT : β ≤ T) (hT : 1 ≤ T) (hc : 1 ≤ c)
    {N : ℕ} (hsmall : 8 * (T * c) ≤ N) :
    |endpointNearPairSum K F α β (c / N) N (fun _ => 1) p / c| ≤
      (8 * q * B * T * (20 * BF * BK + 64 * BF * (KL : ℝ) * T + 4 * BK * LF) +
        8 * BF * B * (64 * (KL : ℝ) * T + 4 * BK) * T ^ 2 * c) / N := by
  classical
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hTc0 : 0 < T * c := mul_pos hT0 hc0
  have hN0 : (0 : ℝ) < N := by linarith only [hTc0, hsmall]
  have hN : 1 ≤ N := by exact_mod_cast hN0
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hKLp : ∀ x y, |K x - K y| ≤ (KL : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hKL.dist_le_mul x y
  let CW := 20 * BF * BK + 64 * BF * (KL : ℝ) * T + 4 * BK * LF
  let CK := 64 * (KL : ℝ) * T + 4 * BK
  let P := 8 * q * B * CW / N + 8 * BF * B * CK * T * c / N
  have hCW : 0 ≤ CW := by dsimp only [CW]; positivity
  have hCK : 0 ≤ CK := by dsimp only [CK]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hrows : ∀ d ∈ Icc 1 ⌊T * c⌋₊,
      |∑ n ∈ terminalLogarithmicGapInterval α β (c / N) N d,
        terminalNearOffsetPair K F c N p d n| ≤ P := by
    intro d hd
    let S := terminalLogarithmicGapInterval α β (c / N) N d
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdc : (d : ℝ) ≤ T * c :=
      (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans (Nat.floor_le hTc0.le)
    have hshift : 4 * d ≤ N := by
      have hh : (4 : ℝ) * d ≤ N := by linarith only [hdc, hsmall, hTc0]
      exact_mod_cast hh
    have hθ : |(d : ℝ) / c| ≤ T := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hc0.le)]
      exact (div_le_iff₀ hc0).mpr hdc
    have h₁ := abs_terminal_reciprocal_gap_selected_le hF hK hLF KL.2 hFL hKLp hθ hlow
      hq hp hz hB hN (by omega : 4 * (0 : ℕ) ≤ N) d d α β (c / N)
    have h₂ := abs_terminal_reciprocal_gap_selected_le hF hK hLF KL.2 hFL hKLp hθ hlow
      hq hp hz hB hN hshift 0 d α β (c / N)
    have hphase (n : ℕ) : (d : ℝ) / c * N / n = (d : ℝ) * N / (c * n) := by ring
    simp only [Nat.add_zero, hphase] at h₁ h₂
    have hlin : |∑ n ∈ S, terminalLinearOffsetPair K F c N p d n| ≤ 8 * q * B * CW / N := by
      have he : (∑ n ∈ S, terminalLinearOffsetPair K F c N p d n) =
          (∑ n ∈ S, F ((n : ℝ) / N) * p (n + d) * K ((d : ℝ) * N / (c * n)) / n) +
          ∑ n ∈ S, F (((n + d : ℕ) : ℝ) / N) * p n * K ((d : ℝ) * N / (c * n)) / n := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun _ _ => by unfold terminalLinearOffsetPair; ring
      rw [he]
      exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by dsimp only [CW]; ring)
    have hcard : (S.card : ℝ) ≤ N := by
      have hh : S.card ≤ N := by
        calc
          _ ≤ (Icc 1 (N - d)).card := card_le_card (filter_subset _ _)
          _ = N - d := by rw [Nat.card_Icc, Nat.add_sub_cancel]
          _ ≤ N := Nat.sub_le N d
      exact_mod_cast hh
    have herr : |∑ n ∈ S,
        (terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n)| ≤
        8 * BF * B * CK * T * c / N := by
      calc
        _ ≤ ∑ n ∈ S,
            |terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ S, 8 * BF * B * CK * T * c / (N : ℝ) ^ 2 := by
          apply sum_le_sum
          intro n hn
          have hni := (mem_filter.mp hn).1
          exact abs_terminal_annular_offset_sub_linear_le hKL hF hK hlow hB hT hc hsmall
            (mem_Icc.mp hni).1 hd0 hdc (by have := (mem_Icc.mp hni).2; omega)
        _ = (S.card : ℝ) * (8 * BF * B * CK * T * c / (N : ℝ) ^ 2) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * (8 * BF * B * CK * T * c / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by field_simp [hN0.ne'] <;> ring
    calc
      _ = |(∑ n ∈ S,
            (terminalNearOffsetPair K F c N p d n - terminalLinearOffsetPair K F c N p d n)) +
          ∑ n ∈ S, terminalLinearOffsetPair K F c N p d n| := by
        rw [sum_sub_distrib, sub_add_cancel]
      _ ≤ _ := ((abs_add_le _ _).trans (add_le_add herr hlin)).trans_eq (by dsimp only [P]; ring)
  rw [endpointNearPairSum_eq_annular_offset_sum K F p hα hβT hT0 hc0 hN
    (by linarith only [hTc0, hsmall] : T * c ≤ N), abs_div, abs_of_pos hc0]
  calc
    _ ≤ (∑ _d ∈ Icc 1 ⌊T * c⌋₊, P) / c :=
      div_le_div_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hrows)) hc0.le
    _ = ((⌊T * c⌋₊ : ℝ) * P) / c := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ (T * c * P) / c :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le hTc0.le) hP) hc0.le
    _ = _ := by dsimp only [P, CW, CK]; field_simp [hc0.ne'] <;> ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminalLogarithmicGapInterval_eq_Icc
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_reciprocal_gap_selected_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.endpointNearPairSum_eq_annular_offset_sum
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_annular_offset_sub_linear_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_annular_pair_div_overlap_le_long_index
