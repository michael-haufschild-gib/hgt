import GaloisForLFunctions.HTGeometry.BinaryParityDriftExactLaws

/-!
# Correlation transfer for the binary parity drift

Write `εₘ(x) = 2 b_{m+1}(x) − 1 ∈ {±1}` for the signed binary digits and
`c_M(d) = Σ_{m<M} εₘ ε_{m+d}` for their correlation at lag `d`.

* `vanDerCorput_nat` : a van der Corput inequality for real sequences bounded by one, with
  overlapping windows of the infinite sequence instead of a zero extension.
* `tendsto_drift_div_of_digitCorr` : if `c_M(d)/M → 0` for every lag `d ≥ 1`, then
  `D_x(N)/N → 0`.  The parity drift is the spectral mass of the signed digits at frequency `1/2`,
  and vanishing correlations leave no room for an atom there.
* `twoPointUncorrelated_of_binaryNormal` : normality in base `2` forces vanishing correlations.
* `not_binaryNormal_pi_of_parityDriftHypothesis` : the Parity-Drift Hypothesis for `π` refutes
  normality of `π` in base `2`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.BinaryParityDrift

/-! ### A van der Corput inequality on `ℕ` -/

/-- Shifting a window of length `M` by `j` changes the sum of a sequence bounded by one by at
most `2j`. -/
theorem abs_sum_range_shift_sub_le (g : ℕ → ℝ) (hg : ∀ m, |g m| ≤ 1) (M j : ℕ) :
    |∑ k ∈ range M, g (k + j) - ∑ k ∈ range M, g k| ≤ 2 * j := by
  have hbound : ∀ f : ℕ → ℝ, (∀ i, |f i| ≤ 1) → |∑ i ∈ range j, f i| ≤ j := fun f hf => by
    calc |∑ i ∈ range j, f i| ≤ ∑ i ∈ range j, |f i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range j, (1 : ℝ) := sum_le_sum fun i _ => hf i
      _ = j := by simp
  have h1 := sum_range_add g j M
  have h2 := sum_range_add g M j
  have h3 : ∑ k ∈ range M, g (k + j) = ∑ k ∈ range M, g (j + k) :=
    sum_congr rfl fun k _ => by rw [add_comm]
  have hb1 := hbound g hg
  have hb2 := hbound (fun i => g (M + i)) fun i => hg _
  rw [add_comm j M] at h1
  have key : ∑ k ∈ range M, g (k + j) - ∑ k ∈ range M, g k =
      ∑ i ∈ range j, g (M + i) - ∑ i ∈ range j, g i := by linarith
  rw [key]
  calc _ ≤ |∑ i ∈ range j, g (M + i)| + |∑ i ∈ range j, g i| := abs_sub _ _
    _ ≤ 2 * j := by linarith

/-- The lag `|j₁ − j₂|` of two offsets. -/
def lag (j₁ j₂ : ℕ) : ℕ := j₁ - j₂ + (j₂ - j₁)

/-- The correlation sum `Σ_{k<M} aₖ a_{k+d}`. -/
def corrSum (a : ℕ → ℝ) (M d : ℕ) : ℝ := ∑ k ∈ range M, a k * a (k + d)

theorem abs_sum_shifted_products_le (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 1) (M j₁ j₂ : ℕ) :
    |∑ k ∈ range M, a (k + j₁) * a (k + j₂)| ≤ |corrSum a M (lag j₁ j₂)| + 2 * (j₁ + j₂) := by
  have hprod : ∀ d m, |a m * a (m + d)| ≤ 1 := fun d m => by
    rw [abs_mul]; exact mul_le_one₀ (ha m) (abs_nonneg _) (ha _)
  have hgen : ∀ X Y : ℝ, |X - Y| ≤ 2 * (j₁ + j₂) → |X| ≤ |Y| + 2 * (j₁ + j₂) := fun X Y h => by
    have := abs_sub_abs_le_abs_sub X Y
    linarith
  rcases le_total j₁ j₂ with h | h
  · have hl : lag j₁ j₂ = j₂ - j₁ := by unfold lag; omega
    have hs := abs_sum_range_shift_sub_le (fun m => a m * a (m + (j₂ - j₁))) (hprod _) M j₁
    have he : ∑ k ∈ range M, a (k + j₁) * a (k + j₂) =
        ∑ k ∈ range M, a (k + j₁) * a (k + j₁ + (j₂ - j₁)) :=
      sum_congr rfl fun k _ => by rw [show k + j₁ + (j₂ - j₁) = k + j₂ by omega]
    rw [he, hl]
    refine hgen _ _ (hs.trans ?_)
    have : (0 : ℝ) ≤ j₂ := Nat.cast_nonneg _
    linarith
  · have hl : lag j₁ j₂ = j₁ - j₂ := by unfold lag; omega
    have hs := abs_sum_range_shift_sub_le (fun m => a m * a (m + (j₁ - j₂))) (hprod _) M j₂
    have he : ∑ k ∈ range M, a (k + j₁) * a (k + j₂) =
        ∑ k ∈ range M, a (k + j₂) * a (k + j₂ + (j₁ - j₂)) :=
      sum_congr rfl fun k _ => by rw [show k + j₂ + (j₁ - j₂) = k + j₁ by omega, mul_comm]
    rw [he, hl]
    refine hgen _ _ (hs.trans ?_)
    have : (0 : ℝ) ≤ j₁ := Nat.cast_nonneg _
    linarith

/-- **Van der Corput on `ℕ`.**  For a real sequence bounded by one and window lengths `M`, `H`,
`H² (Σ_{m<M} aₘ)² ≤ 2M Σ_{j₁,j₂<H} (|c_M(|j₁−j₂|)| + 4H) + 8H⁴`. -/
theorem vanDerCorput_nat (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 1) (M H : ℕ) :
    (H : ℝ) ^ 2 * (∑ m ∈ range M, a m) ^ 2 ≤
      2 * M * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, (|corrSum a M (lag j₁ j₂)| + 4 * H) +
        8 * (H : ℝ) ^ 4 := by
  set S := ∑ m ∈ range M, a m with hS
  set T := ∑ k ∈ range M, ∑ j ∈ range H, a (k + j) with hTdef
  have hT : T = ∑ j ∈ range H, ∑ k ∈ range M, a (k + j) := sum_comm
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have h1 : |(H : ℝ) * S - T| ≤ 2 * (H : ℝ) ^ 2 := by
    rw [hT, show (H : ℝ) * S = ∑ _j ∈ range H, S by simp, ← sum_sub_distrib]
    calc |∑ j ∈ range H, (S - ∑ k ∈ range M, a (k + j))|
        ≤ ∑ j ∈ range H, |S - ∑ k ∈ range M, a (k + j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range H, 2 * (H : ℝ) := sum_le_sum fun j hj => by
          rw [abs_sub_comm]
          have := abs_sum_range_shift_sub_le a ha M j
          have hj' : (j : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hj).le
          linarith
      _ = 2 * (H : ℝ) ^ 2 := by simp; ring
  have hCS : T ^ 2 ≤ M * ∑ k ∈ range M, (∑ j ∈ range H, a (k + j)) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range M) (f := fun k => ∑ j ∈ range H, a (k + j))
    simpa using this
  have hexp : ∑ k ∈ range M, (∑ j ∈ range H, a (k + j)) ^ 2 =
      ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ∑ k ∈ range M, a (k + j₁) * a (k + j₂) := by
    simp_rw [sq, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j₁ _ => ?_
    rw [sum_comm]
  have hE : ∑ k ∈ range M, (∑ j ∈ range H, a (k + j)) ^ 2 ≤
      ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, (|corrSum a M (lag j₁ j₂)| + 4 * H) := by
    rw [hexp]
    refine sum_le_sum fun j₁ hj₁ => sum_le_sum fun j₂ hj₂ => ?_
    have h := abs_sum_shifted_products_le a ha M j₁ j₂
    have hj₁' : (j₁ : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hj₁).le
    have hj₂' : (j₂ : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hj₂).le
    have := le_abs_self (∑ k ∈ range M, a (k + j₁) * a (k + j₂))
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hHS : ((H : ℝ) * S) ^ 2 ≤ 2 * T ^ 2 + 8 * (H : ℝ) ^ 4 := by
    have habs := abs_le.mp h1
    have he2 : ((H : ℝ) * S - T) ^ 2 ≤ (2 * (H : ℝ) ^ 2) ^ 2 := by
      nlinarith [habs.1, habs.2]
    nlinarith [sq_nonneg (T - ((H : ℝ) * S - T))]
  calc (H : ℝ) ^ 2 * S ^ 2 = ((H : ℝ) * S) ^ 2 := by ring
    _ ≤ 2 * T ^ 2 + 8 * (H : ℝ) ^ 4 := hHS
    _ ≤ 2 * (M * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, (|corrSum a M (lag j₁ j₂)| + 4 * H)) +
          8 * (H : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_left hE hM0
        linarith
    _ = _ := by ring

/-! ### Signed digits and their correlations -/

/-- The signed binary digit `εₘ = 2 b_{m+1} − 1 ∈ {±1}`. -/
noncomputable def signedDigit (x : ℝ) (m : ℕ) : ℝ := 2 * (binDigit x (m + 1) : ℝ) - 1

/-- The digit correlation `c_M(d) = Σ_{m<M} εₘ ε_{m+d}`. -/
noncomputable def digitCorr (x : ℝ) (M d : ℕ) : ℝ := corrSum (signedDigit x) M d

theorem signedDigit_sq (x : ℝ) (m : ℕ) : signedDigit x m ^ 2 = 1 := by
  have h0 := binDigit_nonneg x (m + 1)
  have h1 := binDigit_le_one x (m + 1)
  unfold signedDigit
  rcases (show binDigit x (m + 1) = 0 ∨ binDigit x (m + 1) = 1 by omega) with h | h <;>
    · rw [h]; norm_num

theorem abs_signedDigit (x : ℝ) (m : ℕ) : |signedDigit x m| = 1 := by
  have h0 := binDigit_nonneg x (m + 1)
  have h1 := binDigit_le_one x (m + 1)
  unfold signedDigit
  rcases (show binDigit x (m + 1) = 0 ∨ binDigit x (m + 1) = 1 by omega) with h | h <;>
    · rw [h]; norm_num

theorem digitCorr_zero (x : ℝ) (M : ℕ) : digitCorr x M 0 = M := by
  unfold digitCorr corrSum
  simp_rw [add_zero, ← sq, signedDigit_sq]
  simp

theorem sum_range_two_mul_neg_one_pow (N : ℕ) : ∑ m ∈ range (2 * N), (-1 : ℝ) ^ m = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, pow_succ,
      pow_mul]
    norm_num

/-- The alternating signed sequence `(−1)ᵐ εₘ`. -/
noncomputable def altSigned (x : ℝ) (m : ℕ) : ℝ := (-1) ^ m * signedDigit x m

theorem abs_altSigned (x : ℝ) (m : ℕ) : |altSigned x m| = 1 := by
  rw [altSigned, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_signedDigit]

/-- The alternating signed digit sum over `2N` digits is `2 D_x(N)`. -/
theorem sum_altSigned (x : ℝ) (N : ℕ) :
    ∑ m ∈ range (2 * N), altSigned x m = 2 * (drift x N : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (drift_eq_alternating_sum x N)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  rw [h, mul_sum]
  unfold altSigned signedDigit
  simp_rw [mul_sub, mul_one, sum_sub_distrib, sum_range_two_mul_neg_one_pow, sub_zero]
  refine sum_congr rfl fun m _ => by ring

theorem abs_corrSum_altSigned (x : ℝ) (M d : ℕ) :
    |corrSum (altSigned x) M d| = |digitCorr x M d| := by
  have h : corrSum (altSigned x) M d = (-1) ^ d * digitCorr x M d := by
    unfold corrSum digitCorr corrSum altSigned
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [pow_add]
    have : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    linear_combination (signedDigit x k * signedDigit x (k + d) * (-1) ^ d) * this
  rw [h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- **Correlation transfer.**  If the signed binary digits of `x` have vanishing correlation at
every positive lag, the parity drift of `x` is `o(N)`. -/
theorem tendsto_drift_div_of_digitCorr (x : ℝ)
    (hC : ∀ d : ℕ, 1 ≤ d → Tendsto (fun M : ℕ => digitCorr x M d / M) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨H, hH⟩ := exists_nat_gt (3 / ε ^ 2)
  have hε2 : 0 < ε ^ 2 := by positivity
  have hHpos : (0 : ℝ) < H := lt_trans (by positivity) hH
  have hHnat : 0 < H := by exact_mod_cast hHpos
  -- the normalized correlation of each offset pair converges
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hpair : ∀ j₁ j₂ : ℕ, Tendsto (fun N : ℕ => |digitCorr x (2 * N) (lag j₁ j₂)| / (2 * N : ℕ))
      atTop (𝓝 (if j₁ = j₂ then 1 else 0)) := by
    intro j₁ j₂
    split_ifs with hj
    · have hl : lag j₁ j₂ = 0 := by unfold lag; omega
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [hl, digitCorr_zero, abs_of_nonneg (Nat.cast_nonneg _), div_self]
      exact_mod_cast (by omega : 2 * N ≠ 0)
    · have hl : 1 ≤ lag j₁ j₂ := by unfold lag; omega
      have h := ((hC _ hl).comp hdouble).abs
      rw [abs_zero] at h
      refine h.congr fun N => ?_
      simp only [Function.comp, abs_div, Nat.abs_cast]
  have hsum : Tendsto (fun N : ℕ => ∑ j₁ ∈ range H, ∑ j₂ ∈ range H,
      |digitCorr x (2 * N) (lag j₁ j₂)| / (2 * N : ℕ)) atTop (𝓝 (H : ℝ)) := by
    have h := tendsto_finsetSum (range H) fun j₁ _ =>
      tendsto_finsetSum (range H) fun j₂ _ => hpair j₁ j₂
    have hval : ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, (if j₁ = j₂ then (1 : ℝ) else 0) = H := by
      rw [sum_congr rfl fun j₁ hj₁ => by rw [sum_ite_eq, if_pos hj₁]]
      simp
    rwa [hval] at h
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  -- the van der Corput majorant converges to `2/H`
  set R : ℕ → ℝ := fun N => 2 / (H : ℝ) ^ 2 * (∑ j₁ ∈ range H, ∑ j₂ ∈ range H,
      |digitCorr x (2 * N) (lag j₁ j₂)| / (2 * N : ℕ)) + 16 * H * (1 / N) +
        2 * (H : ℝ) ^ 2 * (1 / N) ^ 2 with hR
  have hRlim : Tendsto R atTop (𝓝 (2 / (H : ℝ) ^ 2 * H + 16 * H * 0 + 2 * (H : ℝ) ^ 2 * 0 ^ 2)) :=
    ((hsum.const_mul _).add (hinv.const_mul _)).add ((hinv.pow 2).const_mul _)
  have hlimval : 2 / (H : ℝ) ^ 2 * H + 16 * H * 0 + 2 * (H : ℝ) ^ 2 * 0 ^ 2 = 2 / H := by
    field_simp
    ring
  rw [hlimval] at hRlim
  have hlt : 2 / (H : ℝ) < ε ^ 2 := by
    rw [div_lt_iff₀ hHpos]
    rw [div_lt_iff₀ hε2] at hH
    linarith
  filter_upwards [hRlim.eventually (gt_mem_nhds hlt), eventually_gt_atTop 0] with N hRN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hvdc := vanDerCorput_nat (altSigned x) (fun m => (abs_altSigned x m).le) (2 * N) H
  rw [sum_altSigned] at hvdc
  simp_rw [abs_corrSum_altSigned] at hvdc
  -- normalize the van der Corput bound
  have hbound : ((drift x N : ℝ) / N) ^ 2 ≤ R N := by
    have hsplit : ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, (|digitCorr x (2 * N) (lag j₁ j₂)| + 4 * H) =
        (2 * N : ℕ) * (∑ j₁ ∈ range H, ∑ j₂ ∈ range H,
          |digitCorr x (2 * N) (lag j₁ j₂)| / (2 * N : ℕ)) + 4 * (H : ℝ) ^ 3 := by
      simp_rw [sum_add_distrib, mul_sum]
      simp only [sum_const, card_range, nsmul_eq_mul]
      have h2N : ((2 * N : ℕ) : ℝ) ≠ 0 := by positivity
      rw [show ∑ i ∈ range H, ∑ i_1 ∈ range H,
            ((2 * N : ℕ) : ℝ) * (|digitCorr x (2 * N) (lag i i_1)| / ((2 * N : ℕ) : ℝ)) =
          ∑ i ∈ range H, ∑ i_1 ∈ range H, |digitCorr x (2 * N) (lag i i_1)| from
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_div_cancel₀ _ h2N]
      ring
    rw [hsplit] at hvdc
    simp only [hR]
    rw [div_pow, div_le_iff₀ (by positivity)]
    push_cast at hvdc ⊢
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    set sc := ∑ j₁ ∈ range H, ∑ j₂ ∈ range H,
      |digitCorr x (2 * N) (lag j₁ j₂)| / (2 * (N : ℝ)) with hsc
    have hscnn : 0 ≤ sc := sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      div_nonneg (abs_nonneg _) (by positivity)
    have key : (H : ℝ) ^ 2 * (drift x N : ℝ) ^ 2 ≤
        (N : ℝ) ^ 2 * (2 * sc) + 4 * (H : ℝ) ^ 3 * N + 2 * (H : ℝ) ^ 4 := by
      nlinarith [hvdc]
    have hgoal : (drift x N : ℝ) ^ 2 * (H : ℝ) ^ 2 ≤
        (2 / (H : ℝ) ^ 2 * sc + 16 * H * (1 / N) + 2 * (H : ℝ) ^ 2 * (1 / N) ^ 2) *
          (N : ℝ) ^ 2 * (H : ℝ) ^ 2 := by
      have e : (2 / (H : ℝ) ^ 2 * sc + 16 * H * (1 / N) + 2 * (H : ℝ) ^ 2 * (1 / N) ^ 2) *
          (N : ℝ) ^ 2 * (H : ℝ) ^ 2 =
          2 * sc * (N : ℝ) ^ 2 + 16 * (H : ℝ) ^ 3 * N + 2 * (H : ℝ) ^ 4 := by
        field_simp
      rw [e]
      have hpos3 : 0 ≤ (H : ℝ) ^ 3 * N := by positivity
      linarith [key, hpos3]
    exact le_of_mul_le_mul_right (by linarith) hH2
  have hsq : ((drift x N : ℝ) / N) ^ 2 < ε ^ 2 := lt_of_le_of_lt hbound hRN
  rw [Real.dist_eq, sub_zero]
  exact abs_lt.mpr (abs_lt_of_sq_lt_sq' hsq hε.le)

/-- The signed binary digits of `x` are uncorrelated at every positive lag. -/
def TwoPointUncorrelated (x : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → Tendsto (fun M : ℕ => digitCorr x M d / M) atTop (𝓝 0)

theorem not_parityDriftHypothesis_of_twoPointUncorrelated {x : ℝ}
    (hx : TwoPointUncorrelated x) : ¬ ParityDriftHypothesis x :=
  fun h => h (tendsto_drift_div_of_digitCorr x hx)

/-! ### Normality in base two -/

/-- The word of `k` binary digits read at positions `m+1, …, m+k`. -/
noncomputable def digitWord (x : ℝ) (k m : ℕ) : Fin k → Bool :=
  fun i => decide (binDigit x (m + 1 + i) = 1)

/-- Normality in base `2`: every word of length `k` occurs with frequency `2⁻ᵏ`. -/
def BinaryNormal (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Bool),
    Tendsto (fun M : ℕ => (#{m ∈ range M | digitWord x k m = w} : ℝ) / M) atTop (𝓝 ((1 / 2) ^ k))

/-- The sign `±1` recording whether the first and last letters of a word agree. -/
def endSign {d : ℕ} (w : Fin (d + 1) → Bool) : ℝ := if w 0 = w (Fin.last d) then 1 else -1

theorem signedDigit_mul_eq_endSign (x : ℝ) (d m : ℕ) :
    signedDigit x m * signedDigit x (m + d) = endSign (digitWord x (d + 1) m) := by
  have h0 := binDigit_nonneg x (m + 1)
  have h1 := binDigit_le_one x (m + 1)
  have h2 := binDigit_nonneg x (m + d + 1)
  have h3 := binDigit_le_one x (m + d + 1)
  unfold signedDigit endSign digitWord
  simp only [Fin.val_zero, add_zero, Fin.val_last]
  simp only [show m + 1 + d = m + d + 1 by ring]
  rcases (show binDigit x (m + 1) = 0 ∨ binDigit x (m + 1) = 1 by omega) with ha | ha <;>
  rcases (show binDigit x (m + d + 1) = 0 ∨ binDigit x (m + d + 1) = 1 by omega) with hb | hb <;>
  · rw [ha, hb]; norm_num

theorem sum_endSign_eq_zero {d : ℕ} (hd : 1 ≤ d) : ∑ w : Fin (d + 1) → Bool, endSign w = 0 := by
  set flip : (Fin (d + 1) → Bool) → (Fin (d + 1) → Bool) :=
    fun w => Function.update w (Fin.last d) (!w (Fin.last d)) with hflip
  have hne : (0 : Fin (d + 1)) ≠ Fin.last d := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hinv : Function.Involutive flip := fun w => by
    funext i
    by_cases hi : i = Fin.last d
    · subst hi; simp [hflip]
    · simp [hflip, Function.update_of_ne hi]
  have hsign : ∀ w, endSign (flip w) = -endSign w := fun w => by
    unfold endSign
    simp only [hflip, Function.update_self, Function.update_of_ne hne]
    by_cases h : w 0 = w (Fin.last d)
    · rw [if_pos h, if_neg (by rw [h]; cases w (Fin.last d) <;> simp)]
    · rw [if_neg h, if_pos (by cases h0 : w 0 <;> cases hl : w (Fin.last d) <;> simp_all)]
      ring
  have hperm := Equiv.sum_comp (hinv.toPerm flip) endSign
  simp only [Function.Involutive.coe_toPerm, hsign, sum_neg_distrib] at hperm
  linarith

theorem digitCorr_eq_sum_endSign (x : ℝ) (M d : ℕ) :
    digitCorr x M d =
      ∑ w : Fin (d + 1) → Bool, (#{m ∈ range M | digitWord x (d + 1) m = w} : ℝ) * endSign w := by
  unfold digitCorr corrSum
  simp_rw [signedDigit_mul_eq_endSign]
  rw [← sum_fiberwise (range M) (digitWord x (d + 1)) (fun m => endSign (digitWord x (d + 1) m))]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_congr rfl fun m hm => by rw [(mem_filter.mp hm).2], sum_const, nsmul_eq_mul]

/-- **Normality kills all correlations.** -/
theorem twoPointUncorrelated_of_binaryNormal {x : ℝ} (hx : BinaryNormal x) :
    TwoPointUncorrelated x := by
  intro d hd
  have h := tendsto_finsetSum (univ : Finset (Fin (d + 1) → Bool)) fun w _ =>
    (hx (d + 1) w).mul_const (endSign w)
  have hzero : ∑ w : Fin (d + 1) → Bool, (1 / 2 : ℝ) ^ (d + 1) * endSign w = 0 := by
    rw [← mul_sum, sum_endSign_eq_zero hd, mul_zero]
  rw [hzero] at h
  refine h.congr fun M => ?_
  rw [digitCorr_eq_sum_endSign, sum_div]
  refine sum_congr rfl fun w _ => by ring

theorem not_parityDriftHypothesis_of_binaryNormal {x : ℝ} (hx : BinaryNormal x) :
    ¬ ParityDriftHypothesis x :=
  not_parityDriftHypothesis_of_twoPointUncorrelated (twoPointUncorrelated_of_binaryNormal hx)

/-- **The hypothesis refutes normality of `π` in base `2`.** -/
theorem not_binaryNormal_pi_of_parityDriftHypothesis
    (h : ParityDriftHypothesis Real.pi) : ¬ BinaryNormal Real.pi :=
  fun hn => not_parityDriftHypothesis_of_binaryNormal hn h

end GaloisForLFunctions.HTGeometry.BinaryParityDrift
