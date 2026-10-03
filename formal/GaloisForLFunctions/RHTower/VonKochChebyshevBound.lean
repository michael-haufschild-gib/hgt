import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound
import GaloisForLFunctions.RHTower.LittlewoodOmega

/-!
# Von Koch's theorem: `ψ(x) - x = O(√x log²x)` under the Riemann hypothesis

The window statistic `J(a, b) = Σ_{a<n≤b} Λ(n)(1/n - 1/b) + ψ(a)(1/a - 1/b)` squeezes `ψ`:
`ψ(a) ≤ J(a,b)/w ≤ ψ(b)`, `w = 1/a - 1/b`, and the genus-kernel explicit formula evaluates it,
`J/w = log(b/a)/w + Re Σ_ρ T(ρ; a, b) - log 2π + O(1/(a(b-a)))`, with the logarithmic mean
`log(b/a)/w ∈ [a, b]`.  Under the Riemann hypothesis each zero term satisfies

* `|T(ρ; a, a+h)| ≤ √a/|γ| + h/√a` (the term is `-a^ρ/ρ` up to `|ρ|h a^{-1/2}`), and
* `|T(ρ; a, a+h)| ≤ 4a^{3/2}/(h(¼ + γ²))` (the crude bound through `1/w ≤ 2a²/h`).

Unit shells of ordinates hold at most `20(A + log(k+5))` zeros, so with the split at `S`,
`Σ_ρ |T| ≤ 20√a (A + log(S+5))(1 + log S) + 20(h/√a)(S+1)(A + log(S+6))
+ (4a^{3/2}/h)·40(A + 1 + log(S+4))/S`.  The choice `h = S = √a` gives `O(√a log²a)` on both
sides of `ψ(x) - x`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Counting zeros in unit shells -/

/-- `Σ_{k=1}^n 1/k ≤ 1 + log n`. -/
theorem sum_Icc_one_div_le_one_add_log_max (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ 1 + Real.log (max n 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hmax : max (n : ℝ) 1 = n := max_eq_left hn1
      have hmax' : max ((n + 1 : ℕ) : ℝ) 1 = (n : ℝ) + 1 := by
        push_cast; exact max_eq_left (by linarith)
      rw [hmax] at ih
      rw [hmax']
      have hlog : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        rw [← Real.log_div (by linarith) (by linarith)]
        have h := Real.one_sub_inv_le_log_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
        have : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
        linarith
      push_cast
      linarith

/-- Zeros with `|γ| ≤ S` number at most `20(S + 1)(A + log(S + 6))`. -/
theorem card_xiCopiesBelow_le_log {S : ℝ} (hS : 0 ≤ S) :
    ((xiCopiesBelow S).card : ℝ)
      ≤ 20 * (S + 1) * (xiLineTwoLogDerivConstant + Real.log (S + 6)) := by
  classical
  set A := xiLineTwoLogDerivConstant with hA
  set F := xiCopiesBelow S with hF
  set N : ℕ := ⌊S⌋₊ with hN
  have hmaps : ∀ q ∈ F, ⌊|zeroOrdinate q|⌋₊ ∈ Finset.range (N + 1) := by
    intro q hq
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor ((mem_xiCopiesBelow).mp hq)
  have hsplit := Finset.card_eq_sum_card_fiberwise hmaps
  have hlogk : ∀ k ∈ Finset.range (N + 1), Real.log ((k : ℝ) + 5) ≤ Real.log (S + 6) := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hNS : (N : ℝ) ≤ S := Nat.floor_le hS
    exact Real.log_le_log (by positivity) (by linarith)
  have hA0 : 0 ≤ A + Real.log 5 := by
    have := xiLineTwoLogDerivConstant_nonneg
    have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith
  calc (F.card : ℝ) = ∑ k ∈ Finset.range (N + 1),
        ((F.filter (fun q => ⌊|zeroOrdinate q|⌋₊ = k)).card : ℝ) := by
          rw [hsplit]; push_cast; rfl
    _ ≤ ∑ k ∈ Finset.range (N + 1), 20 * (A + Real.log (S + 6)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine (card_filter_floor_abs_zeroOrdinate_le F k).trans ?_
        have := hlogk k hk
        linarith
    _ = (N + 1) * (20 * (A + Real.log (S + 6))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ 20 * (S + 1) * (A + Real.log (S + 6)) := by
        have hNS : (N : ℝ) ≤ S := Nat.floor_le hS
        have h6 : 0 ≤ A + Real.log (S + 6) := by
          have := xiLineTwoLogDerivConstant_nonneg
          have : 0 ≤ Real.log (S + 6) := Real.log_nonneg (by linarith)
          linarith
        nlinarith

/-- `Σ_{|γ| ≤ S} 1/|γ| ≤ 20(A + log(S + 6))(1 + log(S + 1))`. -/
theorem sum_xiCopiesBelow_inv_abs_le {S : ℝ} (hS : 0 ≤ S) :
    ∑ q ∈ xiCopiesBelow S, 1 / |zeroOrdinate q|
      ≤ 20 * (xiLineTwoLogDerivConstant + Real.log (S + 6)) * (1 + Real.log (S + 1)) := by
  classical
  set A := xiLineTwoLogDerivConstant with hA
  set F := xiCopiesBelow S with hF
  set N : ℕ := ⌊S⌋₊ with hN
  have hNS : (N : ℝ) ≤ S := Nat.floor_le hS
  have hmaps : ∀ q ∈ F, ⌊|zeroOrdinate q|⌋₊ ∈ Finset.Icc 1 N := by
    intro q hq
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.floor_le_floor ((mem_xiCopiesBelow).mp hq)⟩
    have h4 := four_lt_abs_zeroOrdinate q
    exact Nat.le_floor (by norm_num; linarith)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hA6 : 0 ≤ A + Real.log (S + 6) := by
    have := xiLineTwoLogDerivConstant_nonneg
    have : 0 ≤ Real.log (S + 6) := Real.log_nonneg (by linarith)
    linarith
  calc ∑ k ∈ Finset.Icc 1 N, ∑ q ∈ F with ⌊|zeroOrdinate q|⌋₊ = k, 1 / |zeroOrdinate q|
      ≤ ∑ k ∈ Finset.Icc 1 N, 20 * (A + Real.log (S + 6)) * (1 / k) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
        have hterm : ∀ q ∈ F.filter (fun q => ⌊|zeroOrdinate q|⌋₊ = k),
            1 / |zeroOrdinate q| ≤ 1 / (k : ℝ) := by
          intro q hq
          have hqk := (Finset.mem_filter.mp hq).2
          have hle : (k : ℝ) ≤ |zeroOrdinate q| := by
            rw [← hqk]; exact Nat.floor_le (abs_nonneg _)
          exact one_div_le_one_div_of_le (by linarith) hle
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc := card_filter_floor_abs_zeroOrdinate_le F k
        have hlog : Real.log ((k : ℝ) + 5) ≤ Real.log (S + 6) :=
          Real.log_le_log (by positivity) (by linarith)
        have hk0 : 0 ≤ 1 / (k : ℝ) := by positivity
        calc ((F.filter (fun q => ⌊|zeroOrdinate q|⌋₊ = k)).card : ℝ) * (1 / k)
            ≤ (20 * (A + Real.log ((k : ℝ) + 5))) * (1 / k) :=
              mul_le_mul_of_nonneg_right hc hk0
          _ ≤ 20 * (A + Real.log (S + 6)) * (1 / k) := by
              refine mul_le_mul_of_nonneg_right ?_ hk0; linarith
    _ = 20 * (A + Real.log (S + 6)) * ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k := by
        rw [Finset.mul_sum]
    _ ≤ 20 * (A + Real.log (S + 6)) * (1 + Real.log (S + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (sum_Icc_one_div_le_one_add_log_max N).trans ?_
        have : Real.log (max (N : ℝ) 1) ≤ Real.log (S + 1) := by
          refine Real.log_le_log (lt_max_of_lt_right one_pos) (max_le (by linarith) (by linarith))
        linarith


/-! ## The zero terms under the Riemann hypothesis -/

theorem norm_mul_one_sub_eq_inv_cosWeight (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ = 1 / cosWeight q := by
  rw [← norm_mul, xiZeroCopy_eq_of_riemannHypothesis hRH q, half_add_mul_I_mul_one_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), cosWeight, one_div_one_div]

theorem abs_zeroOrdinate_le_norm (q : XiZeroCopy) : |zeroOrdinate q| ≤ ‖(q.1 : ℂ)‖ :=
  Complex.abs_im_le_norm _

/-- **Head bound.**  `|T(ρ; a, a+h)| ≤ √a/|γ| + h/√a`. -/
theorem norm_lagWindowZeroTerm_le_head (hRH : RiemannHypothesis) {a h : ℝ} (ha : 1 ≤ a)
    (hh : 0 < h) (q : XiZeroCopy) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖ ≤ Real.sqrt a / |zeroOrdinate q| + h / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have hre : (q.1 : ℂ).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have h1 := norm_mul_lagWindowZeroTerm_add_cpow_le ha0 le_rfl (by linarith : a < a + h)
    (ρ := (q.1 : ℂ)) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rw [hre, add_sub_cancel_left] at h1
  have hγ := four_lt_abs_zeroOrdinate q
  have hρn : |zeroOrdinate q| ≤ ‖(q.1 : ℂ)‖ := abs_zeroOrdinate_le_norm q
  have hρ0 : 0 < ‖(q.1 : ℂ)‖ := by linarith
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hpow : a ^ (1 / 2 - 1 : ℝ) = 1 / Real.sqrt a := by
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ha0.le, Real.sqrt_eq_rpow,
      inv_eq_one_div]
  have hcpow : ‖(a : ℂ) ^ (q.1 : ℂ)‖ = Real.sqrt a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha0, hre, Real.sqrt_eq_rpow]
  rw [hpow] at h1
  have h2 : ‖(q.1 : ℂ)‖ * ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖
      ≤ ‖(q.1 : ℂ)‖ * h * (1 / Real.sqrt a) + Real.sqrt a := by
    rw [← norm_mul]
    have := norm_sub_le ((q.1 : ℂ) * lagWindowZeroTerm (q.1 : ℂ) a (a + h) + (a : ℂ) ^ (q.1 : ℂ))
      ((a : ℂ) ^ (q.1 : ℂ))
    rw [add_sub_cancel_right, hcpow] at this
    linarith
  have h3 : ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖
      ≤ h / Real.sqrt a + Real.sqrt a / ‖(q.1 : ℂ)‖ := by
    rw [← mul_le_mul_iff_of_pos_left hρ0]
    have e : ‖(q.1 : ℂ)‖ * (h / Real.sqrt a + Real.sqrt a / ‖(q.1 : ℂ)‖)
        = ‖(q.1 : ℂ)‖ * h * (1 / Real.sqrt a) + Real.sqrt a := by field_simp
    rw [e]; exact h2
  have h4 : Real.sqrt a / ‖(q.1 : ℂ)‖ ≤ Real.sqrt a / |zeroOrdinate q| :=
    div_le_div_of_nonneg_left hsa.le (by linarith) hρn
  linarith

/-- **Tail bound.**  `|T(ρ; a, a+h)| ≤ 4a√a/(h(¼ + γ²))` for `h ≤ a`. -/
theorem norm_lagWindowZeroTerm_le_tail (hRH : RiemannHypothesis) {a h : ℝ} (ha : 1 ≤ a)
    (hh : 0 < h) (hha : h ≤ a) (q : XiZeroCopy) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖ ≤ 4 * a * Real.sqrt a * cosWeight q / h := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < a + h := by linarith
  have hre : (q.1 : ℂ).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have h1 := norm_lagWindowZeroTerm_le ha0 (by linarith : a < a + h) (q.1 : ℂ)
  rw [hre, norm_mul_one_sub_eq_inv_cosWeight hRH q] at h1
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hpa : a ^ (1 / 2 - 1 : ℝ) = 1 / Real.sqrt a := by
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ha0.le, Real.sqrt_eq_rpow,
      inv_eq_one_div]
  have hpb : (a + h) ^ (1 / 2 - 1 : ℝ) ≤ 1 / Real.sqrt a := by
    rw [← hpa]
    exact Real.rpow_le_rpow_of_nonpos ha0 (by linarith) (by norm_num)
  have hw : 1 / a - 1 / (a + h) = h / (a * (a + h)) := by field_simp; ring
  rw [hw] at h1
  have hc := cosWeight_pos q
  refine h1.trans ?_
  rw [hpa]
  have hden : 0 < 1 / cosWeight q * (h / (a * (a + h))) := by positivity
  rw [div_le_iff₀ hden]
  have e : 4 * a * Real.sqrt a * cosWeight q / h * (1 / cosWeight q * (h / (a * (a + h))))
      = 4 * Real.sqrt a / (a + h) := by
    field_simp
  rw [e, le_div_iff₀ hb0]
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have : (1 / Real.sqrt a + (a + h) ^ (1 / 2 - 1 : ℝ)) * (a + h) ≤ 2 / Real.sqrt a * (2 * a) := by
    have h2 : 1 / Real.sqrt a + (a + h) ^ (1 / 2 - 1 : ℝ) ≤ 2 / Real.sqrt a := by
      have : 2 / Real.sqrt a = 1 / Real.sqrt a + 1 / Real.sqrt a := by ring
      linarith
    have h3 : 0 ≤ 1 / Real.sqrt a + (a + h) ^ (1 / 2 - 1 : ℝ) := by
      have := Real.rpow_nonneg hb0.le (1 / 2 - 1 : ℝ); positivity
    calc (1 / Real.sqrt a + (a + h) ^ (1 / 2 - 1 : ℝ)) * (a + h)
        ≤ (2 / Real.sqrt a) * (a + h) := mul_le_mul_of_nonneg_right h2 hb0.le
      _ ≤ 2 / Real.sqrt a * (2 * a) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : 2 / Real.sqrt a * (2 * a) = 4 * Real.sqrt a := by
    calc 2 / Real.sqrt a * (2 * a) = 2 / Real.sqrt a * (2 * (Real.sqrt a * Real.sqrt a)) := by
          rw [hsq]
      _ = 4 * Real.sqrt a := by field_simp; ring
  linarith

/-- **The zero sum of one window.** -/
theorem tsum_norm_lagWindowZeroTerm_le (hRH : RiemannHypothesis) {a h S : ℝ} (ha : 1 ≤ a)
    (hh : 0 < h) (hha : h ≤ a) (hS : 4 ≤ S) :
    ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖
      ≤ Real.sqrt a * (20 * (xiLineTwoLogDerivConstant + Real.log (S + 6))
          * (1 + Real.log (S + 1)))
        + h / Real.sqrt a * (20 * (S + 1) * (xiLineTwoLogDerivConstant + Real.log (S + 6)))
        + 4 * a * Real.sqrt a / h * lagTailBound S := by
  classical
  set f : XiZeroCopy → ℝ := fun q => ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖ with hf
  have hfs : Summable f := summable_norm_lagWindowZeroTerm ha (by linarith)
  have hf0 : ∀ q, 0 ≤ f q := fun q => norm_nonneg _
  set F := xiCopiesBelow S with hF
  have hsplit : ∀ q, f q = (if |zeroOrdinate q| ≤ S then f q else 0)
      + (if S < |zeroOrdinate q| then f q else 0) := by
    intro q
    by_cases hq : |zeroOrdinate q| ≤ S
    · rw [if_pos hq, if_neg (not_lt.mpr hq), add_zero]
    · rw [if_neg hq, if_pos (not_le.mp hq), zero_add]
  have hs1 : Summable (fun q => if |zeroOrdinate q| ≤ S then f q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hf0 q])
      (fun q => by split_ifs <;> simp [hf0 q]) hfs
  have hs2 : Summable (fun q => if S < |zeroOrdinate q| then f q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hf0 q])
      (fun q => by split_ifs <;> simp [hf0 q]) hfs
  have htsum : ∑' q, f q = ∑' q, (if |zeroOrdinate q| ≤ S then f q else 0)
      + ∑' q, (if S < |zeroOrdinate q| then f q else 0) := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr hsplit
  -- the head
  have hhead : ∑' q, (if |zeroOrdinate q| ≤ S then f q else 0) = ∑ q ∈ F, f q := by
    rw [tsum_eq_sum (s := F) (fun q hq => by
      rw [if_neg]; intro h; exact hq ((mem_xiCopiesBelow).mpr h))]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [if_pos ((mem_xiCopiesBelow).mp hq)]
  have hheadle : ∑ q ∈ F, f q
      ≤ Real.sqrt a * ∑ q ∈ F, 1 / |zeroOrdinate q| + (F.card : ℝ) * (h / Real.sqrt a) := by
    calc ∑ q ∈ F, f q ≤ ∑ q ∈ F, (Real.sqrt a / |zeroOrdinate q| + h / Real.sqrt a) :=
          Finset.sum_le_sum fun q _ => norm_lagWindowZeroTerm_le_head hRH ha hh q
      _ = Real.sqrt a * ∑ q ∈ F, 1 / |zeroOrdinate q| + (F.card : ℝ) * (h / Real.sqrt a) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [mul_one_div]
  have hS0 : 0 ≤ S := by linarith
  have hinv := sum_xiCopiesBelow_inv_abs_le hS0
  have hcard := card_xiCopiesBelow_le_log hS0
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  -- the tail
  have hw := summable_cosWeight hRH
  have hwt : Summable (fun q => if S < |zeroOrdinate q| then cosWeight q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [(cosWeight_pos q).le])
      (fun q => by split_ifs <;> simp [(cosWeight_pos q).le]) hw
  have htail : ∑' q, (if S < |zeroOrdinate q| then f q else 0)
      ≤ 4 * a * Real.sqrt a / h * lagTailBound S := by
    calc ∑' q, (if S < |zeroOrdinate q| then f q else 0)
        ≤ ∑' q, (4 * a * Real.sqrt a / h) * (if S < |zeroOrdinate q| then cosWeight q else 0) := by
          refine hs2.tsum_le_tsum (fun q => ?_) (hwt.mul_left _)
          by_cases hq : S < |zeroOrdinate q|
          · rw [if_pos hq, if_pos hq]
            have := norm_lagWindowZeroTerm_le_tail hRH ha hh hha q
            rw [hf]
            calc ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖ ≤ 4 * a * Real.sqrt a * cosWeight q / h :=
                  this
              _ = 4 * a * Real.sqrt a / h * cosWeight q := by ring
          · rw [if_neg hq, if_neg hq, mul_zero]
      _ = 4 * a * Real.sqrt a / h * ∑' q, (if S < |zeroOrdinate q| then cosWeight q else 0) :=
          tsum_mul_left
      _ ≤ 4 * a * Real.sqrt a / h * lagTailBound S := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [lagTailBound]
          exact tsum_cosWeight_tail_le hS
  rw [htsum, hhead]
  have h1 : Real.sqrt a * ∑ q ∈ F, 1 / |zeroOrdinate q|
      ≤ Real.sqrt a * (20 * (xiLineTwoLogDerivConstant + Real.log (S + 6))
          * (1 + Real.log (S + 1))) := mul_le_mul_of_nonneg_left hinv hsa
  have h2 : (F.card : ℝ) * (h / Real.sqrt a)
      ≤ h / Real.sqrt a * (20 * (S + 1) * (xiLineTwoLogDerivConstant + Real.log (S + 6))) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hcard (by positivity)
  linarith


/-! ## Von Koch's bound -/

theorem vonKoch_arith {u L A : ℝ} (hu : 4 ≤ u) (hL : 2 ≤ L) (hA : 0 ≤ A) :
    u + 2 + u * (20 * (A + L) * (1 + L) + 80 * (A + L) + 160 * (A + 1 + L))
      ≤ 200 * (A + 2) * u * L ^ 2 := by
  have hu0 : 0 < u := by linarith
  have key : 1 + 2 / u + (20 * (A + L) * (1 + L) + 80 * (A + L) + 160 * (A + 1 + L))
      ≤ 200 * (A + 2) * L ^ 2 := by
    have h2u : 2 / u ≤ 1 / 2 := by rw [div_le_iff₀ hu0]; linarith
    have hAL : 0 ≤ A * L := by positivity
    have hAL2 : 0 ≤ A * (L - 2) := mul_nonneg hA (by linarith)
    have hLL : 0 ≤ (L - 2) * L := mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg hAL2 (by linarith : (0:ℝ) ≤ L)]
  have e : u + 2 + u * (20 * (A + L) * (1 + L) + 80 * (A + L) + 160 * (A + 1 + L))
      = u * (1 + 2 / u + (20 * (A + L) * (1 + L) + 80 * (A + L) + 160 * (A + 1 + L))) := by
    field_simp
  rw [e, show 200 * (A + 2) * u * L ^ 2 = u * (200 * (A + 2) * L ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left key hu0.le

theorem log_two_mul_pi_lt_two : Real.log (2 * Real.pi) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hπ := Real.pi_lt_d2
  have he := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith

/-- The logarithms at `S = √x` are at most `log x` for `x ≥ 16`. -/
theorem log_sqrt_add_le_log {x c : ℝ} (hx : 16 ≤ x) (hc : 0 < c) (hc6 : c ≤ 6) :
    Real.log (Real.sqrt x + c) ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have hs : Real.sqrt x ≤ x / 4 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  exact Real.log_le_log (by positivity) (by linarith)

theorem four_le_sqrt_of_sixteen_le {x : ℝ} (hx : 16 ≤ x) : 4 ≤ Real.sqrt x := by
  rw [show (4 : ℝ) = Real.sqrt 16 by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hx

theorem two_le_log_of_sixteen_le {x : ℝ} (hx : 16 ≤ x) : 2 ≤ Real.log x := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) hx
  linarith

/-- The zero sum at `S = √x` with `a ∈ [x/2, x]`, `h = √x`. -/
theorem tsum_norm_lagWindowZeroTerm_le_sqrt (hRH : RiemannHypothesis) {x a : ℝ} (hx : 16 ≤ x)
    (hxa : x / 2 ≤ a) (hax : a ≤ x) (hha : Real.sqrt x ≤ a) :
    ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) a (a + Real.sqrt x)‖
      ≤ Real.sqrt x * (20 * (xiLineTwoLogDerivConstant + Real.log x) * (1 + Real.log x)
        + 80 * (xiLineTwoLogDerivConstant + Real.log x)
        + 160 * (xiLineTwoLogDerivConstant + 1 + Real.log x)) := by
  set A := xiLineTwoLogDerivConstant with hA
  have hA0 : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  have hx0 : 0 < x := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hs4 := four_le_sqrt_of_sixteen_le hx
  set u := Real.sqrt x with hu
  have hh := tsum_norm_lagWindowZeroTerm_le hRH ha1 (by linarith) hha hs4
  have hL := two_le_log_of_sixteen_le hx
  have l6 := log_sqrt_add_le_log hx (c := 6) (by norm_num) le_rfl
  have l1 := log_sqrt_add_le_log hx (c := 1) (by norm_num) (by norm_num)
  have l4 := log_sqrt_add_le_log hx (c := 4) (by norm_num) (by norm_num)
  rw [← hu] at l6 l1 l4
  have hsa : Real.sqrt a ≤ u := Real.sqrt_le_sqrt hax
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have huu : u * u = x := Real.mul_self_sqrt hx0.le
  have hsaa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  -- `u/√a ≤ 2` since `x ≤ 4a`
  have hr : u / Real.sqrt a ≤ 2 := by
    rw [div_le_iff₀ hsa0]
    nlinarith
  -- `4a√a/u ≤ 4u` since `a√a ≤ x = u²`
  have hq : 4 * a * Real.sqrt a / u ≤ 4 * x := by
    rw [div_le_iff₀ (by linarith)]
    have : a * Real.sqrt a ≤ x * u :=
      mul_le_mul hax hsa hsa0.le hx0.le
    nlinarith
  have hT : lagTailBound u ≤ 40 * (A + 1 + Real.log x) / u := by
    unfold lagTailBound
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hT0 : 0 ≤ lagTailBound u := by
    unfold lagTailBound
    have := Real.log_nonneg (show (1 : ℝ) ≤ u + 4 by linarith)
    exact div_nonneg (by nlinarith) (by linarith)
  have h1 : Real.sqrt a * (20 * (A + Real.log (u + 6)) * (1 + Real.log (u + 1)))
      ≤ u * (20 * (A + Real.log x) * (1 + Real.log x)) := by
    have hl6 : 0 ≤ A + Real.log (u + 6) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ u + 6 by linarith); linarith
    have hl1 : 0 ≤ 1 + Real.log (u + 1) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ u + 1 by linarith); linarith
    calc Real.sqrt a * (20 * (A + Real.log (u + 6)) * (1 + Real.log (u + 1)))
        ≤ u * (20 * (A + Real.log (u + 6)) * (1 + Real.log (u + 1))) :=
          mul_le_mul_of_nonneg_right hsa (by positivity)
      _ ≤ u * (20 * (A + Real.log x) * (1 + Real.log x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          have := mul_le_mul (show A + Real.log (u + 6) ≤ A + Real.log x by linarith)
            (show 1 + Real.log (u + 1) ≤ 1 + Real.log x by linarith) hl1 (by linarith)
          linarith
  have h2 : u / Real.sqrt a * (20 * (u + 1) * (A + Real.log (u + 6)))
      ≤ u * (80 * (A + Real.log x)) := by
    have hl6 : 0 ≤ A + Real.log (u + 6) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ u + 6 by linarith); linarith
    calc u / Real.sqrt a * (20 * (u + 1) * (A + Real.log (u + 6)))
        ≤ 2 * (20 * (u + 1) * (A + Real.log (u + 6))) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ ≤ 2 * (20 * (2 * u) * (A + Real.log x)) := by
          have : 20 * (u + 1) * (A + Real.log (u + 6)) ≤ 20 * (2 * u) * (A + Real.log x) :=
            mul_le_mul (by linarith) (by linarith) hl6 (by linarith)
          linarith
      _ = u * (80 * (A + Real.log x)) := by ring
  have h3 : 4 * a * Real.sqrt a / u * lagTailBound u ≤ u * (160 * (A + 1 + Real.log x)) := by
    calc 4 * a * Real.sqrt a / u * lagTailBound u ≤ 4 * x * lagTailBound u :=
          mul_le_mul_of_nonneg_right hq hT0
      _ ≤ 4 * x * (40 * (A + 1 + Real.log x) / u) :=
          mul_le_mul_of_nonneg_left hT (by linarith)
      _ = u * (160 * (A + 1 + Real.log x)) := by
          rw [← huu]; field_simp; ring
  linarith

/-- **Von Koch, upper half.**  Under RH, `ψ(x) - x ≤ 200(A+2)√x log²x` for `x ≥ 16`. -/
theorem chebyshevPsi_sub_le_of_riemannHypothesis (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 16 ≤ x) :
    Chebyshev.psi x - x
      ≤ 200 * (xiLineTwoLogDerivConstant + 2) * Real.sqrt x * Real.log x ^ 2 := by
  set A := xiLineTwoLogDerivConstant with hA
  have hA0 : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  have hx0 : 0 < x := by linarith
  have hs4 := four_le_sqrt_of_sixteen_le hx
  set h := Real.sqrt x with hhdef
  have hhx : h ≤ x := by
    rw [hhdef, Real.sqrt_le_left hx0.le]; nlinarith
  have hb : x < x + h := by linarith
  have hw : 0 < 1 / x - 1 / (x + h) := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt hx0 hb
  have hψ : Chebyshev.psi x ≤ chebyshevLagWindow x (x + h) / (1 / x - 1 / (x + h)) := by
    rw [le_div_iff₀ hw]
    exact (chebyshevLagWindow_bounds hx0 hb.le).1
  rw [chebyshevLagWindow_div_eq (by linarith) hb] at hψ
  have hL : Real.log ((x + h) / x) / (1 / x - 1 / (x + h)) ≤ x + h := by
    rw [div_le_iff₀ hw]
    exact (log_div_le_mul_inv_sub hx0 hb.le).2
  have hS := summable_norm_lagWindowZeroTerm (a := x) (b := x + h) (by linarith) hb
  have hre : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (x + h)).re
      ≤ ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) x (x + h)‖ :=
    (Complex.re_le_norm _).trans (norm_tsum_le_tsum_norm hS)
  have hzero := tsum_norm_lagWindowZeroTerm_le_sqrt hRH hx (a := x) (by linarith) le_rfl hhx
  have hE : (trivialZeroSeriesReal x / x - trivialZeroSeriesReal (x + h) / (x + h))
      / (1 / x - 1 / (x + h)) ≤ 1 := by
    have hEb := trivialZeroSeriesReal_nonneg (show (1 : ℝ) ≤ x + h by linarith)
    have hEx := trivialZeroSeriesReal_le_two_div_sq (show (2 : ℝ) ≤ x by linarith)
    have hb0 : 0 < x + h := by linarith
    rw [div_le_iff₀ hw, one_mul]
    have h1 : trivialZeroSeriesReal x / x ≤ 2 / x ^ 2 / x :=
      div_le_div_of_nonneg_right hEx hx0.le
    have h2 : 0 ≤ trivialZeroSeriesReal (x + h) / (x + h) := div_nonneg hEb hb0.le
    have h3 : 2 / x ^ 2 / x ≤ 1 / x - 1 / (x + h) := by
      have e : 1 / x - 1 / (x + h) = h / (x * (x + h)) := by field_simp; ring
      rw [e, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h5 : 2 * (x + h) ≤ h * x ^ 2 := by
        have : 4 * x ^ 2 ≤ h * x ^ 2 := mul_le_mul_of_nonneg_right hs4 (sq_nonneg x)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h5 hx0.le]
    linarith
  have hlog := log_two_mul_pi_lt_two
  have hlog0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  have harith := vonKoch_arith hs4 (two_le_log_of_sixteen_le hx) hA0 (L := Real.log x)
  linarith

/-- **Von Koch, lower half.**  Under RH, `x - ψ(x) ≤ 200(A+2)√x log²x` for `x ≥ 16`. -/
theorem sub_chebyshevPsi_le_of_riemannHypothesis (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 16 ≤ x) :
    x - Chebyshev.psi x
      ≤ 200 * (xiLineTwoLogDerivConstant + 2) * Real.sqrt x * Real.log x ^ 2 := by
  set A := xiLineTwoLogDerivConstant with hA
  have hA0 : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  have hx0 : 0 < x := by linarith
  have hs4 := four_le_sqrt_of_sixteen_le hx
  set h := Real.sqrt x with hhdef
  have hsx : h * h = x := Real.mul_self_sqrt hx0.le
  have hh4 : h ≤ x / 4 := by nlinarith
  set a := x - h with hadef
  have ha8 : x / 2 ≤ a := by rw [hadef]; linarith
  have hax : a ≤ x := by rw [hadef]; linarith
  have hha : h ≤ a := by rw [hadef]; linarith
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hab : a < a + h := by linarith
  have hb : a + h = x := by rw [hadef]; ring
  have hw : 0 < 1 / a - 1 / (a + h) := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt ha0 hab
  have hψ : chebyshevLagWindow a (a + h) / (1 / a - 1 / (a + h)) ≤ Chebyshev.psi (a + h) := by
    rw [div_le_iff₀ hw]
    exact (chebyshevLagWindow_bounds ha0 hab.le).2
  rw [chebyshevLagWindow_div_eq ha1 hab] at hψ
  have hL : a ≤ Real.log ((a + h) / a) / (1 / a - 1 / (a + h)) := by
    rw [le_div_iff₀ hw]
    exact (log_div_le_mul_inv_sub ha0 hab.le).1
  have hS := summable_norm_lagWindowZeroTerm (a := a) (b := a + h) ha1.le hab
  have hre : -(∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖)
      ≤ (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a (a + h)).re := by
    have h1 := (norm_tsum_le_tsum_norm hS)
    have h2 := Complex.abs_re_le_norm (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a (a + h))
    have h3 := neg_abs_le (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a (a + h)).re
    linarith
  have hzero := tsum_norm_lagWindowZeroTerm_le_sqrt hRH hx ha8 hax hha
  have hE : 0 ≤ (trivialZeroSeriesReal a / a - trivialZeroSeriesReal (a + h) / (a + h))
      / (1 / a - 1 / (a + h)) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti ha1.le hab.le)) hw.le
  have hlog := log_two_mul_pi_lt_two
  have harith := vonKoch_arith hs4 (two_le_log_of_sixteen_le hx) hA0 (L := Real.log x)
  have hψx : Chebyshev.psi (a + h) = Chebyshev.psi x := by rw [hb]
  linarith

/-- **Von Koch's theorem.**  Under the Riemann hypothesis,
`|ψ(x) - x| ≤ 200(A+2)√x log²x` for every `x ≥ 16`. -/
theorem abs_chebyshevPsi_sub_le_of_riemannHypothesis (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 16 ≤ x) :
    |Chebyshev.psi x - x|
      ≤ 200 * (xiLineTwoLogDerivConstant + 2) * Real.sqrt x * Real.log x ^ 2 :=
  abs_le.mpr ⟨by linarith [sub_chebyshevPsi_le_of_riemannHypothesis hRH hx],
    chebyshevPsi_sub_le_of_riemannHypothesis hRH hx⟩


/-! ## The converse -/

/-- **A power bound on the Chebyshev error moves every zero to the left of `½ + a`.**  If
`ψ(t) - t ≤ C t^{1/2+a}` for `t ≥ x₁`, `0 < a < ½`, then every zero has real part at most
`½ + a`. -/
theorem re_le_half_add_of_chebyshevError_le_rpow {C a x₁ : ℝ} (hC : 0 ≤ C) (ha0 : 0 < a)
    (ha : a < 1 / 2) (hx₁1 : 1 < x₁)
    (hpow : ∀ t, x₁ ≤ t → chebyshevError t ≤ C * t ^ (1 / 2 + a)) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  have htail : ∀ x, x₁ ≤ x →
      ∫ t in Ioi x, chebyshevError t / t ^ 2 ≤ C * (x ^ (a - 1 / 2) / (1 / 2 - a)) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi x) :=
      integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi (by linarith))
    have hint2 : IntegrableOn (fun t : ℝ => C * t ^ (a - 3 / 2)) (Ioi x) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul _
    have hmono := setIntegral_mono_on hint hint2 measurableSet_Ioi (fun t ht => by
      have ht0 : 0 < t := lt_trans hx0 ht
      have h1 := hpow t (le_trans hx (le_of_lt ht))
      have h2 : C * t ^ (a - 3 / 2) = C * t ^ (1 / 2 + a) / t ^ 2 := by
        rw [show a - 3 / 2 = (1 / 2 + a) - 2 by ring, Real.rpow_sub ht0, Real.rpow_two]
        ring
      rw [h2]
      exact div_le_div_of_nonneg_right h1 (by positivity))
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
      show a - 3 / 2 + 1 = a - 1 / 2 by ring] at hmono
    have hd : -x ^ (a - 1 / 2) / (a - 1 / 2) = x ^ (a - 1 / 2) / (1 / 2 - a) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [hd] at hmono
    exact hmono
  set K := C / (1 / 2 - a) + 3 with hK
  have hlarge : ∀ L, Real.log x₁ ≤ L → -(K * Real.exp (a * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    have hx1L : x₁ ≤ Real.exp L := by
      rw [← Real.exp_log (show 0 < x₁ by linarith)]; exact Real.exp_le_exp.mpr hL
    set x := Real.exp L with hxdef
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hlogx : Real.log x = L := by rw [hxdef, Real.log_exp]
    have hid := weilLagFunctionReal_log_mul_sqrt hx1
    rw [hlogx] at hid
    have ht := htail x hx1L
    have hS := trivialZeroSeriesReal_nonneg hx1.le
    have hl : Real.log (2 * Real.pi) ≤ 3 := by
      have h := abs_trivialZeroSeriesReal_sub_log_two_pi_le hx1.le
      have h1 := trivialZeroSeriesReal_le_one hx1.le
      rw [abs_le] at h; linarith [h.1]
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxa : x ^ a = Real.exp (a * L) := by
      rw [hxdef, ← Real.exp_mul]; ring_nf
    have hxa' : x * x ^ (a - 1 / 2) = Real.sqrt x * x ^ a := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith), ← Real.rpow_add hx0]
      ring_nf
    have h1 : -(C * (x * x ^ (a - 1 / 2)) / (1 / 2 - a)) - 3
        ≤ weilLagFunctionReal L * Real.sqrt x := by
      have hxI := mul_le_mul_of_nonneg_left ht hx0.le
      have : x * (C * (x ^ (a - 1 / 2) / (1 / 2 - a)))
          = C * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) := by ring
      linarith
    rw [hxa'] at h1
    have h2 : -(C / (1 / 2 - a) * x ^ a) - 3 / Real.sqrt x ≤ weilLagFunctionReal L := by
      rw [← mul_le_mul_iff_of_pos_right hsx]
      have : (-(C / (1 / 2 - a) * x ^ a) - 3 / Real.sqrt x) * Real.sqrt x
          = -(C * (Real.sqrt x * x ^ a) / (1 / 2 - a)) - 3 := by
        field_simp
      rw [this]; exact h1
    have h3 : 3 / Real.sqrt x ≤ 3 * x ^ a := by
      have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx1.le ha0.le
      have hsx1 : 1 ≤ Real.sqrt x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
      have : 3 / Real.sqrt x ≤ 3 := by rw [div_le_iff₀ hsx]; linarith
      linarith
    rw [← hxa]
    nlinarith
  obtain ⟨L₀, hL₀mem, hL₀min⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.log x₁)).exists_isMinOn
    ⟨0, ⟨le_refl 0, (Real.log_pos hx₁1).le⟩⟩
    (Complex.continuous_re.comp continuous_weilLagFunction_unconditional).continuousOn
  set B := weilLagFunctionReal L₀ with hB
  have hK0 : 0 ≤ K := by
    have : 0 ≤ C / (1 / 2 - a) := div_nonneg hC (by linarith)
    linarith
  have hM : ∀ L, 0 ≤ L → -(max K |B| * Real.exp (a * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    have hexp1 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (by positivity)
    rcases le_or_gt (Real.log x₁) L with hbig | hsmall
    · have := hlarge L hbig
      have : K * Real.exp (a * L) ≤ max K |B| * Real.exp (a * L) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      linarith
    · have h1 : B ≤ weilLagFunctionReal L := hL₀min ⟨hL, hsmall.le⟩
      have h2 : -|B| ≤ B := neg_abs_le B
      have h3 : |B| ≤ max K |B| := le_max_right _ _
      have h4 : max K |B| ≤ max K |B| * Real.exp (a * L) := by
        have : 0 ≤ max K |B| := le_trans (abs_nonneg B) h3
        nlinarith
      linarith
  exact re_le_half_add_of_neg_exp_le_weilLagFunctionReal ha0.le ha hM q


/-- **A one-sided `C√x log²x` bound for `ψ - x` implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x - x ≤ C * Real.sqrt x * Real.log x ^ 2) :
    RiemannHypothesis := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h
  set x₁ := max x₀ 2 with hx₁
  have hx₁1 : 1 < x₁ := by rw [hx₁]; linarith [le_max_right x₀ 2]
  have hre : ∀ a : ℝ, 0 < a → a < 1 / 2 → ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + a := by
    intro a ha0 ha q
    refine re_le_half_add_of_chebyshevError_le_rpow (C := C * (2 / a) ^ 2) (by positivity) ha0 ha
      hx₁1 (fun t ht => ?_) q
    have ht0 : 0 < t := by linarith [le_max_right x₀ 2]
    have hψ := hx₀ t (le_trans (le_max_left _ _) ht)
    have hlog := Real.log_le_rpow_div ht0.le (show 0 < a / 2 by linarith)
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith [le_max_right x₀ 2])
    have hsq : Real.log t ^ 2 ≤ (2 / a) ^ 2 * t ^ a := by
      have h1 : Real.log t ≤ 2 / a * t ^ (a / 2) := by
        rw [show 2 / a * t ^ (a / 2) = t ^ (a / 2) / (a / 2) by field_simp]; exact hlog
      have h2 : (2 / a * t ^ (a / 2)) ^ 2 = (2 / a) ^ 2 * t ^ a := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ (a / 2)) 2, ← Real.rpow_mul ht0.le]; norm_num
      calc Real.log t ^ 2 ≤ (2 / a * t ^ (a / 2)) ^ 2 := pow_le_pow_left₀ hlog0 h1 2
        _ = (2 / a) ^ 2 * t ^ a := h2
    have hpow : Real.sqrt t * t ^ a = t ^ (1 / 2 + a) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
    unfold chebyshevError
    calc Chebyshev.psi t - t ≤ C * Real.sqrt t * Real.log t ^ 2 := hψ
      _ ≤ C * Real.sqrt t * ((2 / a) ^ 2 * t ^ a) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = C * (2 / a) ^ 2 * t ^ (1 / 2 + a) := by rw [← hpow]; ring
  have hle : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 := by
    intro q
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := hre (min (ε / 2) (1 / 4)) (lt_min (by linarith) (by norm_num))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) q
    have h2 := min_le_left (ε / 2) (1 / 4)
    linarith
  have hρ : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ 1 / 2 := by
    intro ρ
    exact hle ⟨ρ, ⟨0, xiSupportMultiplicity_pos ρ⟩⟩
  refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
  have h1 := hρ ρ
  have h2 := hρ (supportPartner ρ)
  rw [supportPartner_re] at h2
  linarith

/-- **Von Koch's equivalence.**  RH holds iff `ψ(x) - x = O(√x log²x)`. -/
theorem riemannHypothesis_iff_chebyshevPsi_sub_isBigO :
    RiemannHypothesis ↔ (fun x : ℝ => Chebyshev.psi x - x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) := by
  constructor
  · intro hRH
    refine Asymptotics.IsBigO.of_bound (200 * (xiLineTwoLogDerivConstant + 2)) ?_
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log x))), ← mul_assoc]
    exact abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hx
  · intro hO
    obtain ⟨C, hC⟩ := hO.bound
    refine riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq (C := |C|) (abs_nonneg C) ?_
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log x)))] at hx
    calc Chebyshev.psi x - x ≤ |Chebyshev.psi x - x| := le_abs_self _
      _ ≤ C * (Real.sqrt x * Real.log x ^ 2) := hx
      _ ≤ |C| * (Real.sqrt x * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = |C| * Real.sqrt x * Real.log x ^ 2 := by ring

end

end RHTower
