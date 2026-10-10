import GaloisForLFunctions.RHTower.VonKochChebyshevBound

/-!
# Von Koch's law with finitely many off-line zeros

Let `S` be a finite set of zero copies of `ξ` (zeros counted with multiplicity) containing every
copy off the critical line, and let `W_S(x) = Σ_{q ∈ S} x^q/q`. Then

`|ψ(x) − x + Re W_S(x)| ≤ (200(A + 2) + 4|S|) √x log²x`   for `x ≥ 16`

(`abs_chebyshevPsi_sub_add_offLineWave_le`), with `A = xiLineTwoLogDerivConstant`. For `S = ∅` this
is von Koch's theorem under the Riemann hypothesis.

**Proof.** The window squeeze `ψ(a) ≤ J(a,b)/w ≤ ψ(b)` and the explicit formula
`J/w = log(b/a)/w + Re Σ_q T(q; a, b) − log 2π + O(1)` are those of von Koch's proof. Split the zero
sum at `S`.
* A copy outside `S` lies on the critical line, so the head bound `|T| ≤ √a/|γ| + h/√a` and the tail
  bound `|T| ≤ 4a√a/(h(¼ + γ²))` hold for it as under the Riemann hypothesis. With `h = √x` the
  copies outside `S` contribute `O(√x log²x)`.
* For a copy in `S`, `−qT(q; a, a+h)` is the `t^{−2}`-weighted mean of `t^q` over the window, so it is
  within `2|q|h a^{β−1} ≤ 2|q|h` of `x^q` for `x ∈ {a, a + h}`. Hence `T(q; ·)` is `−x^q/q` up to
  `2h = 2√x`.
-/

namespace RHTower

noncomputable section

open Complex Finset

/-- The off-line wave `W_S(x) = Σ_{q ∈ S} x^q/q`. -/
def offLineWave (S : Finset XiZeroCopy) (x : ℝ) : ℂ :=
  ∑ q ∈ S, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)

/-! ## Critical copies -/

theorem xiZeroCopy_eq_of_re_eq_half {q : XiZeroCopy} (hre : (q.1 : ℂ).re = 1 / 2) :
    (q.1 : ℂ) = 1 / 2 + (zeroOrdinate q : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [zeroOrdinate, hre]
  · simp [zeroOrdinate]

theorem norm_mul_one_sub_eq_inv_cosWeight_of_re {q : XiZeroCopy}
    (hre : (q.1 : ℂ).re = 1 / 2) :
    ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ = 1 / cosWeight q := by
  rw [← norm_mul, xiZeroCopy_eq_of_re_eq_half hre, half_add_mul_I_mul_one_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), cosWeight, one_div_one_div]

/-- `1/(¼ + γ²) ≤ 2/(|q||1 − q|)` for every copy, so the weights are summable. -/
theorem cosWeight_le_two_mul_norm_inv (q : XiZeroCopy) :
    cosWeight q ≤ 2 * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [norm_inv_mul_one_sub_eq]
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  set β := (q.1 : ℂ).re with hβ
  set γ := zeroOrdinate q with hγ
  have hn : ‖(q.1 : ℂ)‖ ^ 2 = β ^ 2 + γ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hβ, hγ, zeroOrdinate]; ring
  have hm : ‖1 - (q.1 : ℂ)‖ ^ 2 = (1 - β) ^ 2 + γ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hβ, hγ, zeroOrdinate, Complex.sub_re, Complex.sub_im]; ring
  have hq0 : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (fun h => by
    rw [h, Complex.zero_re] at hβ; linarith)
  have hq1 : 0 < ‖1 - (q.1 : ℂ)‖ := norm_pos_iff.mpr (fun h => by
    have := congrArg Complex.re h; simp at this; linarith)
  have hprod : ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ ≤ 2 * (1 / 4 + γ ^ 2) := by
    nlinarith [sq_nonneg (‖(q.1 : ℂ)‖ - ‖1 - (q.1 : ℂ)‖)]
  rw [cosWeight, ← hγ, div_le_iff₀ (by positivity)]
  rw [show 2 * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) * (1 / 4 + γ ^ (2 : ℕ))
      = 2 * (1 / 4 + γ ^ 2) / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖) by ring]
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem summable_cosWeight_unconditional : Summable cosWeight :=
  Summable.of_nonneg_of_le (fun q => (cosWeight_pos q).le) cosWeight_le_two_mul_norm_inv
    (summable_norm_inv_mul_one_sub.mul_left 2)

/-- **Head bound** for a critical copy: `|T(q; a, a+h)| ≤ √a/|γ| + h/√a`. -/
theorem norm_lagWindowZeroTerm_le_head_of_re {a h : ℝ} (ha : 1 ≤ a) (hh : 0 < h)
    {q : XiZeroCopy} (hre : (q.1 : ℂ).re = 1 / 2) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖ ≤ Real.sqrt a / |zeroOrdinate q| + h / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
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

/-- **Tail bound** for a critical copy: `|T(q; a, a+h)| ≤ 4a√a/(h(¼ + γ²))` for `h ≤ a`. -/
theorem norm_lagWindowZeroTerm_le_tail_of_re {a h : ℝ} (ha : 1 ≤ a) (hh : 0 < h) (hha : h ≤ a)
    {q : XiZeroCopy} (hre : (q.1 : ℂ).re = 1 / 2) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖ ≤ 4 * a * Real.sqrt a * cosWeight q / h := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < a + h := by linarith
  have h1 := norm_lagWindowZeroTerm_le ha0 (by linarith : a < a + h) (q.1 : ℂ)
  rw [hre, norm_mul_one_sub_eq_inv_cosWeight_of_re hre] at h1
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

/-! ## The critical part of the zero sum -/

/-- **The critical copies of one window.** If every copy outside `S` is critical, the copies
outside `S` contribute at most von Koch's head-plus-tail bound. -/
theorem tsum_compl_norm_lagWindowZeroTerm_le {S : Finset XiZeroCopy}
    (hS : ∀ q : XiZeroCopy, q ∉ S → (q.1 : ℂ).re = 1 / 2) {a h H : ℝ} (ha : 1 ≤ a)
    (hh : 0 < h) (hha : h ≤ a) (hH : 4 ≤ H) :
    ∑' q : XiZeroCopy, (if q ∈ S then 0 else ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖)
      ≤ Real.sqrt a * (20 * (xiLineTwoLogDerivConstant + Real.log (H + 6))
          * (1 + Real.log (H + 1)))
        + h / Real.sqrt a * (20 * (H + 1) * (xiLineTwoLogDerivConstant + Real.log (H + 6)))
        + 4 * a * Real.sqrt a / h * lagTailBound H := by
  classical
  set f : XiZeroCopy → ℝ :=
    fun q => if q ∈ S then 0 else ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖ with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => by simp only [hf]; split_ifs <;> simp
  have hfs : Summable f :=
    Summable.of_nonneg_of_le hf0 (fun q => by simp only [hf]; split_ifs <;> simp)
      (summable_norm_lagWindowZeroTerm (b := a + h) ha (by linarith))
  set F := xiCopiesBelow H with hF
  have hsplit : ∀ q, f q = (if |zeroOrdinate q| ≤ H then f q else 0)
      + (if H < |zeroOrdinate q| then f q else 0) := by
    intro q
    by_cases hq : |zeroOrdinate q| ≤ H
    · rw [if_pos hq, if_neg (not_lt.mpr hq), add_zero]
    · rw [if_neg hq, if_pos (not_le.mp hq), zero_add]
  have hs1 : Summable (fun q => if |zeroOrdinate q| ≤ H then f q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hf0 q])
      (fun q => by split_ifs <;> simp [hf0 q]) hfs
  have hs2 : Summable (fun q => if H < |zeroOrdinate q| then f q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hf0 q])
      (fun q => by split_ifs <;> simp [hf0 q]) hfs
  have htsum : ∑' q, f q = ∑' q, (if |zeroOrdinate q| ≤ H then f q else 0)
      + ∑' q, (if H < |zeroOrdinate q| then f q else 0) := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr hsplit
  have hhead : ∑' q, (if |zeroOrdinate q| ≤ H then f q else 0) = ∑ q ∈ F, f q := by
    rw [tsum_eq_sum (s := F) (fun q hq => by
      rw [if_neg]; intro h; exact hq ((mem_xiCopiesBelow).mpr h))]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [if_pos ((mem_xiCopiesBelow).mp hq)]
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hheadle : ∑ q ∈ F, f q
      ≤ Real.sqrt a * ∑ q ∈ F, 1 / |zeroOrdinate q| + (F.card : ℝ) * (h / Real.sqrt a) := by
    calc ∑ q ∈ F, f q ≤ ∑ q ∈ F, (Real.sqrt a / |zeroOrdinate q| + h / Real.sqrt a) := by
          refine Finset.sum_le_sum fun q _ => ?_
          simp only [hf]
          split_ifs with hqS
          · have := abs_nonneg (zeroOrdinate q)
            positivity
          · exact norm_lagWindowZeroTerm_le_head_of_re ha hh (hS q hqS)
      _ = Real.sqrt a * ∑ q ∈ F, 1 / |zeroOrdinate q| + (F.card : ℝ) * (h / Real.sqrt a) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [mul_one_div]
  have hH0 : 0 ≤ H := by linarith
  have hinv := sum_xiCopiesBelow_inv_abs_le hH0
  have hcard := card_xiCopiesBelow_le_log hH0
  have hw := summable_cosWeight_unconditional
  have hwt : Summable (fun q => if H < |zeroOrdinate q| then cosWeight q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [(cosWeight_pos q).le])
      (fun q => by split_ifs <;> simp [(cosWeight_pos q).le]) hw
  have htail : ∑' q, (if H < |zeroOrdinate q| then f q else 0)
      ≤ 4 * a * Real.sqrt a / h * lagTailBound H := by
    calc ∑' q, (if H < |zeroOrdinate q| then f q else 0)
        ≤ ∑' q, (4 * a * Real.sqrt a / h) * (if H < |zeroOrdinate q| then cosWeight q else 0) := by
          refine hs2.tsum_le_tsum (fun q => ?_) (hwt.mul_left _)
          by_cases hq : H < |zeroOrdinate q|
          · rw [if_pos hq, if_pos hq]
            simp only [hf]
            split_ifs with hqS
            · have := cosWeight_pos q
              have : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
              positivity
            · have := norm_lagWindowZeroTerm_le_tail_of_re ha hh hha (hS q hqS)
              calc ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)‖
                  ≤ 4 * a * Real.sqrt a * cosWeight q / h := this
                _ = 4 * a * Real.sqrt a / h * cosWeight q := by ring
          · rw [if_neg hq, if_neg hq, mul_zero]
      _ = 4 * a * Real.sqrt a / h * ∑' q, (if H < |zeroOrdinate q| then cosWeight q else 0) :=
          tsum_mul_left
      _ ≤ 4 * a * Real.sqrt a / h * lagTailBound H := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [lagTailBound]
          exact tsum_cosWeight_tail_le hH
  rw [htsum, hhead]
  have h1 : Real.sqrt a * ∑ q ∈ F, 1 / |zeroOrdinate q|
      ≤ Real.sqrt a * (20 * (xiLineTwoLogDerivConstant + Real.log (H + 6))
          * (1 + Real.log (H + 1))) := mul_le_mul_of_nonneg_left hinv hsa
  have h2 : (F.card : ℝ) * (h / Real.sqrt a)
      ≤ h / Real.sqrt a * (20 * (H + 1) * (xiLineTwoLogDerivConstant + Real.log (H + 6))) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hcard (by positivity)
  linarith

/-- The critical part at `H = √x`, `a ∈ [x/2, x]`, `h = √x`. -/
theorem tsum_compl_norm_lagWindowZeroTerm_le_sqrt {S : Finset XiZeroCopy}
    (hS : ∀ q : XiZeroCopy, q ∉ S → (q.1 : ℂ).re = 1 / 2) {x a : ℝ} (hx : 16 ≤ x)
    (hxa : x / 2 ≤ a) (hax : a ≤ x) (hha : Real.sqrt x ≤ a) :
    ∑' q : XiZeroCopy,
        (if q ∈ S then 0 else ‖lagWindowZeroTerm (q.1 : ℂ) a (a + Real.sqrt x)‖)
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
  have hh := tsum_compl_norm_lagWindowZeroTerm_le hS ha1 (by linarith) hha hs4
  have hL := two_le_log_of_sixteen_le hx
  have l6 := log_sqrt_add_le_log hx (c := 6) (by norm_num) le_rfl
  have l1 := log_sqrt_add_le_log hx (c := 1) (by norm_num) (by norm_num)
  have l4 := log_sqrt_add_le_log hx (c := 4) (by norm_num) (by norm_num)
  rw [← hu] at l6 l1 l4
  have hsa : Real.sqrt a ≤ u := Real.sqrt_le_sqrt hax
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have huu : u * u = x := Real.mul_self_sqrt hx0.le
  have hsaa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have hr : u / Real.sqrt a ≤ 2 := by
    rw [div_le_iff₀ hsa0]
    nlinarith
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

/-! ## The copies in `S` -/

/-- The left endpoint: `|T(q; a, a+h) + a^q/q| ≤ h` for `a ≥ 1`. -/
theorem norm_lagWindowZeroTerm_add_cpow_div_le_left (q : XiZeroCopy) {a h : ℝ} (ha : 1 ≤ a)
    (hh : 0 < h) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h) + (a : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖ ≤ h := by
  have ha0 : 0 < a := by linarith
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hq0 : (q.1 : ℂ) ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hqn : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr hq0
  have hmain := norm_mul_lagWindowZeroTerm_add_cpow_le ha0 le_rfl (by linarith : a < a + h)
    (ρ := (q.1 : ℂ)) h0 h1
  have hpow : a ^ ((q.1 : ℂ).re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  have he : (q.1 : ℂ) * lagWindowZeroTerm (q.1 : ℂ) a (a + h) + (a : ℂ) ^ (q.1 : ℂ)
      = (q.1 : ℂ) * (lagWindowZeroTerm (q.1 : ℂ) a (a + h)
        + (a : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)) := by
    field_simp
  rw [he, norm_mul, add_sub_cancel_left] at hmain
  have : ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h) + (a : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖
      ≤ h * a ^ ((q.1 : ℂ).re - 1) := by
    rw [← mul_le_mul_iff_of_pos_left hqn]; linarith
  calc _ ≤ h * a ^ ((q.1 : ℂ).re - 1) := this
    _ ≤ h * 1 := mul_le_mul_of_nonneg_left hpow hh.le
    _ = h := mul_one h

/-- The right endpoint: `|T(q; a, a+h) + (a+h)^q/q| ≤ 2h` for `a ≥ 1`. -/
theorem norm_lagWindowZeroTerm_add_cpow_div_le_right (q : XiZeroCopy) {a h : ℝ} (ha : 1 ≤ a)
    (hh : 0 < h) :
    ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)
        + ((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖ ≤ 2 * h := by
  have ha0 : 0 < a := by linarith
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hq0 : (q.1 : ℂ) ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hqn : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr hq0
  have hleft := norm_lagWindowZeroTerm_add_cpow_div_le_left q ha hh
  have hmv := norm_ofReal_cpow_sub_cpow_le ha0 (by linarith : a ≤ a + h) h0 h1.le
  have hpow : a ^ ((q.1 : ℂ).re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  have hd : ‖((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) - (a : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖ ≤ h := by
    rw [← sub_div, norm_div, div_le_iff₀ hqn]
    calc ‖((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) - (a : ℂ) ^ (q.1 : ℂ)‖
        ≤ ‖(q.1 : ℂ)‖ * (a + h - a) * a ^ ((q.1 : ℂ).re - 1) := hmv
      _ ≤ ‖(q.1 : ℂ)‖ * h * 1 := by
          rw [add_sub_cancel_left]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = h * ‖(q.1 : ℂ)‖ := by ring
  calc _ = ‖(lagWindowZeroTerm (q.1 : ℂ) a (a + h) + (a : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ))
        + (((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) - (a : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ))‖ := by
          congr 1; ring
    _ ≤ h + h := (norm_add_le _ _).trans (add_le_add hleft hd)
    _ = 2 * h := by ring

/-- **Splitting a window's zero sum at `S`.** -/
theorem tsum_lagWindowZeroTerm_eq_sum_add_compl (S : Finset XiZeroCopy) {a b : ℝ} (ha : 1 ≤ a)
    (hab : a < b) :
    ∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b
      = ∑ q ∈ S, lagWindowZeroTerm (q.1 : ℂ) a b
        + ∑' q : XiZeroCopy, (if q ∈ S then 0 else lagWindowZeroTerm (q.1 : ℂ) a b) := by
  classical
  have hn := summable_norm_lagWindowZeroTerm ha hab
  have hs1 : Summable (fun q : XiZeroCopy => if q ∈ S then lagWindowZeroTerm (q.1 : ℂ) a b else 0) :=
    Summable.of_norm_bounded hn (fun q => by split_ifs <;> simp)
  have hs2 : Summable (fun q : XiZeroCopy => if q ∈ S then 0 else lagWindowZeroTerm (q.1 : ℂ) a b) :=
    Summable.of_norm_bounded hn (fun q => by split_ifs <;> simp)
  have hfirst : ∑' q : XiZeroCopy, (if q ∈ S then lagWindowZeroTerm (q.1 : ℂ) a b else 0)
      = ∑ q ∈ S, lagWindowZeroTerm (q.1 : ℂ) a b := by
    rw [tsum_eq_sum (s := S) (fun q hq => by rw [if_neg hq])]
    exact Finset.sum_congr rfl fun q hq => by rw [if_pos hq]
  rw [← hfirst, ← hs1.tsum_add hs2]
  exact tsum_congr fun q => by split_ifs <;> simp

/-- The real part of the complement sum is bounded by the complement sum of norms. -/
theorem abs_re_tsum_compl_le (S : Finset XiZeroCopy) {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    |(∑' q : XiZeroCopy, (if q ∈ S then 0 else lagWindowZeroTerm (q.1 : ℂ) a b)).re|
      ≤ ∑' q : XiZeroCopy, (if q ∈ S then 0 else ‖lagWindowZeroTerm (q.1 : ℂ) a b‖) := by
  classical
  have hn := summable_norm_lagWindowZeroTerm ha hab
  have hs : Summable (fun q : XiZeroCopy => ‖if q ∈ S then 0 else lagWindowZeroTerm (q.1 : ℂ) a b‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => by split_ifs <;> simp) hn
  calc _ ≤ ‖∑' q : XiZeroCopy, (if q ∈ S then 0 else lagWindowZeroTerm (q.1 : ℂ) a b)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑' q : XiZeroCopy, ‖if q ∈ S then 0 else lagWindowZeroTerm (q.1 : ℂ) a b‖ :=
        norm_tsum_le_tsum_norm hs
    _ = _ := tsum_congr fun q => by split_ifs <;> simp

/-! ## Von Koch's law with a finite off-line set -/

/-- The `S`-part of a window at its left endpoint `x`. -/
theorem re_sum_lagWindowZeroTerm_le_left (S : Finset XiZeroCopy) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) :
    (∑ q ∈ S, lagWindowZeroTerm (q.1 : ℂ) x (x + h)).re ≤ -(offLineWave S x).re + S.card * h := by
  have he : ∑ q ∈ S, lagWindowZeroTerm (q.1 : ℂ) x (x + h)
      = ∑ q ∈ S, (lagWindowZeroTerm (q.1 : ℂ) x (x + h) + (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ))
        - offLineWave S x := by
    unfold offLineWave; rw [← Finset.sum_sub_distrib]; simp
  have hb : ‖∑ q ∈ S, (lagWindowZeroTerm (q.1 : ℂ) x (x + h) + (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ))‖
      ≤ S.card * h := by
    calc _ ≤ ∑ q ∈ S, ‖lagWindowZeroTerm (q.1 : ℂ) x (x + h)
            + (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _q ∈ S, h :=
          Finset.sum_le_sum fun q _ => norm_lagWindowZeroTerm_add_cpow_div_le_left q hx hh
      _ = S.card * h := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [he, Complex.sub_re]
  have := Complex.re_le_norm
    (∑ q ∈ S, (lagWindowZeroTerm (q.1 : ℂ) x (x + h) + (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)))
  linarith

/-- The `S`-part of a window at its right endpoint `x = a + h`. -/
theorem re_sum_lagWindowZeroTerm_ge_right (S : Finset XiZeroCopy) {a h x : ℝ} (ha : 1 ≤ a)
    (hh : 0 < h) (hx : a + h = x) :
    -(offLineWave S x).re - 2 * S.card * h ≤ (∑ q ∈ S, lagWindowZeroTerm (q.1 : ℂ) a (a + h)).re := by
  have he : ∑ q ∈ S, lagWindowZeroTerm (q.1 : ℂ) a (a + h)
      = ∑ q ∈ S, (lagWindowZeroTerm (q.1 : ℂ) a (a + h)
          + ((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)) - offLineWave S x := by
    unfold offLineWave; rw [← Finset.sum_sub_distrib, ← hx]; simp
  have hb : ‖∑ q ∈ S, (lagWindowZeroTerm (q.1 : ℂ) a (a + h)
      + ((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ))‖ ≤ 2 * S.card * h := by
    calc _ ≤ ∑ q ∈ S, ‖lagWindowZeroTerm (q.1 : ℂ) a (a + h)
            + ((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _q ∈ S, 2 * h :=
          Finset.sum_le_sum fun q _ => norm_lagWindowZeroTerm_add_cpow_div_le_right q ha hh
      _ = 2 * S.card * h := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [he, Complex.sub_re]
  have := Complex.abs_re_le_norm (∑ q ∈ S, (lagWindowZeroTerm (q.1 : ℂ) a (a + h)
      + ((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)))
  have := neg_abs_le (∑ q ∈ S, (lagWindowZeroTerm (q.1 : ℂ) a (a + h)
      + ((a + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ))).re
  linarith

/-- **Upper half.** If every copy outside `S` is critical, then
`ψ(x) − x + Re W_S(x) ≤ (200(A+2) + 4|S|)√x log²x` for `x ≥ 16`. -/
theorem chebyshevPsi_sub_add_offLineWave_le {S : Finset XiZeroCopy}
    (hS : ∀ q : XiZeroCopy, q ∉ S → (q.1 : ℂ).re = 1 / 2) {x : ℝ} (hx : 16 ≤ x) :
    Chebyshev.psi x - x + (offLineWave S x).re
      ≤ (200 * (xiLineTwoLogDerivConstant + 2) + 4 * S.card) * Real.sqrt x * Real.log x ^ 2 := by
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
  rw [tsum_lagWindowZeroTerm_eq_sum_add_compl S (by linarith) hb, Complex.add_re] at hψ
  have hcompl := abs_re_tsum_compl_le S (a := x) (b := x + h) (by linarith) hb
  have hzero := tsum_compl_norm_lagWindowZeroTerm_le_sqrt hS hx (a := x) (by linarith) le_rfl hhx
  have hSpart := re_sum_lagWindowZeroTerm_le_left S (x := x) (h := h) (by linarith) (by linarith)
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
  have hlog0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  have hLx := two_le_log_of_sixteen_le hx
  have harith := vonKoch_arith hs4 hLx hA0 (L := Real.log x)
  have hcard : (S.card : ℝ) * h ≤ 4 * S.card * h * Real.log x ^ 2 := by
    have : (1 : ℝ) ≤ 4 * Real.log x ^ 2 := by nlinarith
    have hc : 0 ≤ (S.card : ℝ) * h := by positivity
    nlinarith
  have hre := (abs_le.mp hcompl).2
  have e : (200 * (A + 2) + 4 * S.card) * h * Real.log x ^ 2
      = 200 * (A + 2) * h * Real.log x ^ 2 + 4 * S.card * h * Real.log x ^ 2 := by ring
  rw [e]
  linarith

/-- **Lower half.** If every copy outside `S` is critical, then
`x − ψ(x) − Re W_S(x) ≤ (200(A+2) + 4|S|)√x log²x` for `x ≥ 16`. -/
theorem sub_chebyshevPsi_sub_offLineWave_le {S : Finset XiZeroCopy}
    (hS : ∀ q : XiZeroCopy, q ∉ S → (q.1 : ℂ).re = 1 / 2) {x : ℝ} (hx : 16 ≤ x) :
    x - Chebyshev.psi x - (offLineWave S x).re
      ≤ (200 * (xiLineTwoLogDerivConstant + 2) + 4 * S.card) * Real.sqrt x * Real.log x ^ 2 := by
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
  rw [tsum_lagWindowZeroTerm_eq_sum_add_compl S ha1.le hab, Complex.add_re] at hψ
  have hcompl := abs_re_tsum_compl_le S (a := a) (b := a + h) ha1.le hab
  have hzero := tsum_compl_norm_lagWindowZeroTerm_le_sqrt hS hx ha8 hax hha
  have hSpart := re_sum_lagWindowZeroTerm_ge_right S ha1.le (by linarith : 0 < h) hb
  have hE : 0 ≤ (trivialZeroSeriesReal a / a - trivialZeroSeriesReal (a + h) / (a + h))
      / (1 / a - 1 / (a + h)) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti ha1.le hab.le)) hw.le
  have hlog := log_two_mul_pi_lt_two
  have hLx := two_le_log_of_sixteen_le hx
  have harith := vonKoch_arith hs4 hLx hA0 (L := Real.log x)
  have hψx : Chebyshev.psi (a + h) = Chebyshev.psi x := by rw [hb]
  have hcard : 2 * (S.card : ℝ) * h ≤ 4 * S.card * h * Real.log x ^ 2 := by
    have : (1 : ℝ) ≤ 2 * Real.log x ^ 2 := by nlinarith
    have hc : 0 ≤ 2 * (S.card : ℝ) * h := by positivity
    nlinarith
  have hre := (abs_le.mp hcompl).1
  have e : (200 * (A + 2) + 4 * S.card) * h * Real.log x ^ 2
      = 200 * (A + 2) * h * Real.log x ^ 2 + 4 * S.card * h * Real.log x ^ 2 := by ring
  rw [e]
  linarith

/-- **Von Koch's law with finitely many off-line zeros.** Let `S` be a finite set of zero copies
containing every copy off the critical line. Then for every `x ≥ 16`,
`|ψ(x) − x + Re Σ_{q ∈ S} x^q/q| ≤ (200(A+2) + 4|S|) √x log²x`. -/
theorem abs_chebyshevPsi_sub_add_offLineWave_le {S : Finset XiZeroCopy}
    (hS : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → q ∈ S) {x : ℝ} (hx : 16 ≤ x) :
    |Chebyshev.psi x - x + (offLineWave S x).re|
      ≤ (200 * (xiLineTwoLogDerivConstant + 2) + 4 * S.card) * Real.sqrt x * Real.log x ^ 2 := by
  have hS' : ∀ q : XiZeroCopy, q ∉ S → (q.1 : ℂ).re = 1 / 2 := fun q hq => by
    by_contra h; exact hq (hS q h)
  refine abs_le.mpr ⟨?_, chebyshevPsi_sub_add_offLineWave_le hS' hx⟩
  have := sub_chebyshevPsi_sub_offLineWave_le hS' hx
  linarith

/-- **Finitely many off-line zeros: the explicit wave.** If the off-line zero copies form a finite
set, then `ψ(x) = x − Re Σ_{q off-line} x^q/q + O(√x log²x)`. -/
theorem exists_abs_chebyshevPsi_sub_add_offLineWave_le_of_finite
    (hfin : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 16 ≤ x →
      |Chebyshev.psi x - x + (offLineWave hfin.toFinset x).re|
        ≤ K * Real.sqrt x * Real.log x ^ 2 := by
  refine ⟨200 * (xiLineTwoLogDerivConstant + 2) + 4 * hfin.toFinset.card, ?_, fun x hx => ?_⟩
  · have := xiLineTwoLogDerivConstant_nonneg; positivity
  · exact abs_chebyshevPsi_sub_add_offLineWave_le
      (fun q hq => hfin.mem_toFinset.mpr hq) hx

end

end RHTower
