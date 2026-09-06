import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega
import GaloisForLFunctions.RHTower.WeilLagFunctionInteger
import GaloisForLFunctions.PNTPlus.ZetaConj
import GaloisForLFunctions.RHTower.XiRealAnchorPositive

/-!
# Weights, windows, and the two-sided logarithmic-derivative bound

Preparations for the Landau assembly of the prime-lag criterion: the lag weights are bounded by
`1/γ²`; the zero copies with `|γ| ∈ [k, k+1)` number at most `80 log(180(k+2)) + K₀`; the
weighted logarithms `Σ_q ‖w_q‖ log(2 + |γ_q|)` converge; and the bound `‖ζ'/ζ(σ+it)‖ ≤ C log|t|/δ`
holds for `|t| ≥ 4` of either sign, by conjugation.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Zeros are non-real -/

/-- No zero copy is real: `ξ` is positive on the real segment `(0,1)`. -/
theorem zeroOrdinate_ne_zero' (q : XiZeroCopy) : zeroOrdinate q ≠ 0 := by
  intro h0
  have hre := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  have hreal : (q.1 : ℂ) = (((q.1 : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]; exact h0
  have hpos := xi_pos_on_real_anchor hre hre1
  rw [← hreal, xi_xiZeroCopy_eq_zero] at hpos
  simp at hpos

/-! ## The weight bound -/

theorem norm_lagWeight_le_inv_sq (q : XiZeroCopy) :
    ‖lagWeight q‖ ≤ 1 / zeroOrdinate q ^ 2 := by
  have hγ : zeroOrdinate q ≠ 0 := zeroOrdinate_ne_zero' q
  have hγ2 : 0 < zeroOrdinate q ^ 2 := by positivity
  have hre := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  have hprod : zeroOrdinate q ^ 2 ≤ ‖(q.1 : ℂ) * (1 - (q.1 : ℂ))‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, mul_neg, sub_neg_eq_add, zeroOrdinate]
    nlinarith
  unfold lagWeight
  rw [norm_div, norm_one, div_le_div_iff₀ (lt_of_lt_of_le hγ2 hprod) hγ2]
  linarith

/-! ## The two-sided logarithmic-derivative bound -/

/-- The conjugate of a zero copy value is the value of a copy. -/
theorem exists_xiZeroCopy_conj (q : XiZeroCopy) :
    ∃ q' : XiZeroCopy, (q'.1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) := by
  apply exists_xiZeroCopy_of_xi_eq_zero
  rw [xi_conj, xi_xiZeroCopy_eq_zero]
  simp

/-- `‖ζ'/ζ(σ+it)‖ ≤ C log|t|/δ` for `|t| ≥ 4`, both signs. -/
theorem norm_logDeriv_zeta_le_abs {σ t δ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ |t|)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hall : ∀ q : XiZeroCopy, δ ≤ ‖(σ + t * I : ℂ) - (q.1 : ℂ)‖) :
    ‖logDeriv riemannZeta (σ + t * I)‖ ≤ logDerivZetaConstant * Real.log |t| / δ := by
  rcases le_or_gt 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at ht ⊢
    exact norm_logDeriv_zeta_le hσ hσ2 ht hδ hδ1 hall
  · obtain ⟨t', rfl⟩ : ∃ t' : ℝ, t = -t' := ⟨-t, by ring⟩
    have ht' : 4 ≤ t' := by rw [abs_of_neg ht0] at ht; linarith
    rw [abs_of_neg ht0, neg_neg]
    have hconj : ((starRingEnd ℂ) (σ + t' * I) : ℂ) = σ + (-t' : ℝ) * I := by
      apply Complex.ext <;> simp
    have hall' : ∀ q : XiZeroCopy, δ ≤ ‖(σ + t' * I : ℂ) - (q.1 : ℂ)‖ := by
      intro q
      obtain ⟨q', hq'⟩ := exists_xiZeroCopy_conj q
      have h1 := hall q'
      have e : (σ + (-t' : ℝ) * I : ℂ) - (q'.1 : ℂ)
          = (starRingEnd ℂ) ((σ + t' * I : ℂ) - (q.1 : ℂ)) := by
        rw [map_sub, hconj, hq']
      rw [e, Complex.norm_conj] at h1
      exact h1
    have e2 := logDerivZeta_conj' (σ + t' * I)
    rw [hconj] at e2
    rw [e2, Complex.norm_conj]
    exact norm_logDeriv_zeta_le hσ hσ2 ht' hδ hδ1 hall'

/-! ## Windows around the real axis -/

/-- The number of copies with `|γ| ∈ [k, k+1)` is at most `80 log(180(k+2)) + K₀`. -/
theorem card_absWindow_le (k : ℕ) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, (k : ℝ) ≤ |zeroOrdinate q| ∧ |zeroOrdinate q| < k + 1) :
    (F.card : ℝ) ≤ 80 * Real.log (180 * (k + 2)) + smallHeightCount := by
  classical
  have hlog0 : 0 ≤ Real.log (180 * (k + 2)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith)
  have hK0 : (0 : ℝ) ≤ smallHeightCount := Nat.cast_nonneg _
  rcases Nat.lt_or_ge k 4 with hk | hk
  · -- all copies have height at most `5 ≤ 6`
    have : (F.card : ℝ) ≤ smallHeightCount := by
      have := card_le_smallHeightCount F fun q hq => by
        have h := (hF q hq).2
        have hk' : (k : ℝ) ≤ 3 := by exact_mod_cast (by omega : k ≤ 3)
        unfold zeroOrdinate at h
        linarith
      exact_mod_cast this
    linarith
  · have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    set Fp := F.filter (fun q : XiZeroCopy => 0 ≤ zeroOrdinate q) with hFpdef
    set Fm := F.filter (fun q : XiZeroCopy => ¬ (0 ≤ zeroOrdinate q)) with hFmdef
    have hcard : F.card = Fp.card + Fm.card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have hlogmono : Real.log (180 * ((k : ℝ) + 1 / 2)) ≤ Real.log (180 * (k + 2)) :=
      Real.log_le_log (by positivity) (by linarith)
    have hp : (Fp.card : ℝ) ≤ 40 * Real.log (180 * (k + 2)) := by
      have hc : 4 ≤ |(k : ℝ) + 1 / 2| := by rw [abs_of_pos (by positivity)]; linarith
      refine (card_le_of_ordinates_in_window hc Fp fun q hq => ?_).trans ?_
      · rw [hFpdef, Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        have hw := hF q hq1
        rw [abs_of_nonneg hq2] at hw
        unfold zeroOrdinate at hw hq2
        rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
      · rw [abs_of_pos (by positivity)]; linarith
    have hm : (Fm.card : ℝ) ≤ 40 * Real.log (180 * (k + 2)) := by
      have hc : 4 ≤ |-((k : ℝ) + 1 / 2)| := by rw [abs_neg, abs_of_pos (by positivity)]; linarith
      refine (card_le_of_ordinates_in_window hc Fm fun q hq => ?_).trans ?_
      · rw [hFmdef, Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        push Not at hq2
        have hw := hF q hq1
        rw [abs_of_neg hq2] at hw
        unfold zeroOrdinate at hw hq2
        rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
      · rw [abs_neg, abs_of_pos (by positivity)]; linarith
    have : (F.card : ℝ) = Fp.card + Fm.card := by rw [hcard]; push_cast; ring
    linarith

/-! ## Summability of the weighted logarithms -/

/-- `(log(k+3) + 2)² ≤ 72 √k` for `k ≥ 1`. -/
theorem sq_log_add_three_le {k : ℕ} (hk : 1 ≤ k) :
    (Real.log ((k : ℝ) + 3) + 2) ^ 2 ≤ 72 * Real.sqrt k := by
  have h := sq_log_add_two_le (n := k + 3) (by omega)
  push_cast at h
  have hs : Real.sqrt ((k : ℝ) + 3) ≤ 2 * Real.sqrt k := by
    have h4 : (k : ℝ) + 3 ≤ 4 * k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    calc Real.sqrt ((k : ℝ) + 3) ≤ Real.sqrt (4 * k) := Real.sqrt_le_sqrt h4
      _ = 2 * Real.sqrt k := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

/-- The weighted logarithm on the window `k ≥ 1` is at most `(log(k+3)+2)²/k²`. -/
theorem weight_log_le_window {k : ℕ} (hk : 1 ≤ k) {q : XiZeroCopy}
    (hq : (k : ℝ) ≤ |zeroOrdinate q|) (hq' : |zeroOrdinate q| < k + 1) :
    ‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)
      ≤ (Real.log ((k : ℝ) + 3) + 2) ^ 2 / (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : ‖lagWeight q‖ ≤ 1 / (k : ℝ) ^ 2 := by
    refine (norm_lagWeight_le_inv_sq q).trans ?_
    have : (k : ℝ) ^ 2 ≤ zeroOrdinate q ^ 2 := by
      rw [← sq_abs (zeroOrdinate q)]
      exact pow_le_pow_left₀ hk0.le hq 2
    exact one_div_le_one_div_of_le (by positivity) this
  have h2 : Real.log (2 + |zeroOrdinate q|) ≤ Real.log ((k : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have h2' : 0 ≤ Real.log (2 + |zeroOrdinate q|) := Real.log_nonneg (by linarith [abs_nonneg (zeroOrdinate q)])
  have h3 : Real.log ((k : ℝ) + 3) ≤ (Real.log ((k : ℝ) + 3) + 2) ^ 2 := by
    have : 0 ≤ Real.log ((k : ℝ) + 3) := Real.log_nonneg (by linarith)
    nlinarith
  calc ‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|)
      ≤ (1 / (k : ℝ) ^ 2) * (Real.log ((k : ℝ) + 3) + 2) ^ 2 :=
        mul_le_mul h1 (h2.trans h3) h2' (by positivity)
    _ = (Real.log ((k : ℝ) + 3) + 2) ^ 2 / (k : ℝ) ^ 2 := by ring

/-- `Σ_{k ∈ Ico 1 K} √k/k² ≤ 3`. -/
theorem sum_sqrt_div_sq_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 1 K, Real.sqrt k / (k : ℝ) ^ 2 ≤ 3 := by
  have hterm : ∀ k ∈ Finset.Ico 1 K, Real.sqrt k / (k : ℝ) ^ 2 = 1 / ((k : ℝ) * Real.sqrt k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hs : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    have hs0 : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    field_simp
    nlinarith [hs]
  rw [Finset.sum_congr rfl hterm]
  rcases Nat.lt_or_ge K 2 with hK | hK
  · interval_cases K <;> simp
  · rw [← Finset.sum_Ico_consecutive (fun k : ℕ => (1 : ℝ) / ((k : ℝ) * Real.sqrt k))
      (by norm_num : 1 ≤ 2) hK]
    have h1 : ∑ k ∈ Finset.Ico (1 : ℕ) 2, (1 : ℝ) / ((k : ℝ) * Real.sqrt k) = 1 := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp
    have h2 := sum_inv_mul_sqrt_Ico_le K
    linarith

/-- The window logarithm `L_k = log(k+3) + 2`. -/
def winLog (k : ℕ) : ℝ := Real.log ((k : ℝ) + 3) + 2

theorem winLog_ge_two (k : ℕ) : 2 ≤ winLog k := by
  unfold winLog
  have : 0 ≤ Real.log ((k : ℝ) + 3) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  linarith

/-- `L_k³ ≤ 2000 √k` for `k ≥ 1`. -/
theorem winLog_cube_le {k : ℕ} (hk : 1 ≤ k) : winLog k ^ 3 ≤ 2000 * Real.sqrt k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : (1 : ℝ) ≤ (k : ℝ) + 3 := by linarith
  have hlog : Real.log ((k : ℝ) + 3) ≤ 8 * ((k : ℝ) + 3) ^ (1 / 8 : ℝ) := by
    have := Real.log_le_rpow_div (x := (k : ℝ) + 3) (by linarith) (by norm_num : (0:ℝ) < 1 / 8)
    rw [div_div_eq_mul_div, div_one] at this
    linarith
  have hr1 : (1 : ℝ) ≤ ((k : ℝ) + 3) ^ (1 / 8 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hL : winLog k ≤ 10 * ((k : ℝ) + 3) ^ (1 / 8 : ℝ) := by unfold winLog; linarith
  have hL0 : 0 ≤ winLog k := by linarith [winLog_ge_two k]
  have hcube : (10 * ((k : ℝ) + 3) ^ (1 / 8 : ℝ)) ^ 3 = 1000 * ((k : ℝ) + 3) ^ (3 / 8 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (((k : ℝ) + 3) ^ (1 / 8 : ℝ)) 3, ← Real.rpow_mul (by linarith)]
    norm_num
  have h38 : ((k : ℝ) + 3) ^ (3 / 8 : ℝ) ≤ ((k : ℝ) + 3) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hsq : ((k : ℝ) + 3) ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt k := by
    rw [← Real.sqrt_eq_rpow]
    have h4 : (k : ℝ) + 3 ≤ 4 * k := by linarith
    calc Real.sqrt ((k : ℝ) + 3) ≤ Real.sqrt (4 * k) := Real.sqrt_le_sqrt h4
      _ = 2 * Real.sqrt k := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  calc winLog k ^ 3 ≤ (10 * ((k : ℝ) + 3) ^ (1 / 8 : ℝ)) ^ 3 := pow_le_pow_left₀ hL0 hL 3
    _ = 1000 * ((k : ℝ) + 3) ^ (3 / 8 : ℝ) := hcube
    _ ≤ 1000 * (2 * Real.sqrt k) := by gcongr; exact h38.trans hsq
    _ = 2000 * Real.sqrt k := by ring

/-- The window count in terms of `L_k`: at most `(240 + K₀) L_k` copies with `|γ| ∈ [k, k+1)`. -/
theorem card_absWindow_le' (k : ℕ) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, (k : ℝ) ≤ |zeroOrdinate q| ∧ |zeroOrdinate q| < k + 1) :
    (F.card : ℝ) ≤ (240 + smallHeightCount) * winLog k := by
  have h := card_absWindow_le k F hF
  have hK0 : (0 : ℝ) ≤ smallHeightCount := Nat.cast_nonneg _
  have hL2 := winLog_ge_two k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : Real.log (180 * ((k : ℝ) + 2)) ≤ 3 * winLog k := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h180 : Real.log 180 ≤ 8 * Real.log 2 := by
      have e : Real.log ((2 : ℝ) ^ 8) = 8 * Real.log 2 := by
        rw [Real.log_pow]; norm_num
      rw [← e]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have h2 := Real.log_two_lt_d9
    have hmono : Real.log ((k : ℝ) + 2) ≤ Real.log ((k : ℝ) + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hl0 : 0 ≤ Real.log ((k : ℝ) + 3) := Real.log_nonneg (by linarith)
    unfold winLog
    linarith
  have hK : (smallHeightCount : ℝ) ≤ smallHeightCount * winLog k := by
    exact le_mul_of_one_le_right hK0 (by linarith)
  nlinarith

/-- The weighted logarithm on the window `k ≥ 1` is at most `L_k²/k²`. -/
theorem weight_log_le_window' {k : ℕ} (hk : 1 ≤ k) {q : XiZeroCopy}
    (hq : (k : ℝ) ≤ |zeroOrdinate q|) (hq' : |zeroOrdinate q| < k + 1) :
    ‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|) ≤ winLog k ^ 2 / (k : ℝ) ^ 2 :=
  weight_log_le_window hk hq hq'

/-- **Summability of the weighted logarithms.** -/
theorem summable_lagWeight_mul_log :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|) := by
  classical
  set W := ∑' q : XiZeroCopy, ‖lagWeight q‖ with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun q => norm_nonneg _
  set K₀ : ℝ := (smallHeightCount : ℝ) with hK₀
  have hK₀0 : 0 ≤ K₀ := Nat.cast_nonneg _
  refine summable_of_sum_le (c := 2 * W + (240 + K₀) * 2000 * 3)
    (fun q => mul_nonneg (norm_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg (zeroOrdinate q)])))
    fun F => ?_
  -- window index `⌊|γ|⌋₊`
  set idx : XiZeroCopy → ℕ := fun q => ⌊|zeroOrdinate q|⌋₊ with hidx
  set f : XiZeroCopy → ℝ := fun q => ‖lagWeight q‖ * Real.log (2 + |zeroOrdinate q|) with hfdef
  have hf0 : ∀ q, 0 ≤ f q := fun q =>
    mul_nonneg (norm_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg (zeroOrdinate q)]))
  set K := F.sup idx + 1 with hKdef
  have hmaps : ∀ q ∈ F, idx q ∈ Finset.range K := fun q hq =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := idx) hq))
  -- the window `0`
  have hwin0 : ∑ q ∈ F with idx q = 0, f q ≤ 2 * W := by
    have h1 : ∀ q ∈ F.filter (fun q => idx q = 0), f q ≤ 2 * ‖lagWeight q‖ := by
      intro q hq
      have hq0 : idx q = 0 := (Finset.mem_filter.mp hq).2
      have hlt : |zeroOrdinate q| < 1 := by
        have := Nat.lt_floor_add_one |zeroOrdinate q|
        rw [show ⌊|zeroOrdinate q|⌋₊ = idx q from rfl, hq0] at this
        simpa using this
      have hlog : Real.log (2 + |zeroOrdinate q|) ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 + |zeroOrdinate q| by positivity)
        linarith
      simp only [hfdef]
      have := mul_le_mul_of_nonneg_left hlog (norm_nonneg (lagWeight q))
      linarith
    calc ∑ q ∈ F with idx q = 0, f q ≤ ∑ q ∈ F with idx q = 0, 2 * ‖lagWeight q‖ :=
          Finset.sum_le_sum h1
      _ = 2 * ∑ q ∈ F with idx q = 0, ‖lagWeight q‖ := by rw [Finset.mul_sum]
      _ ≤ 2 * W := by
          have hle : ∑ q ∈ F with idx q = 0, ‖lagWeight q‖ ≤ W := by
            rw [hWdef]
            exact summable_norm_lagWeight.sum_le_tsum (F.filter fun q => idx q = 0)
              (fun q _ => norm_nonneg (lagWeight q))
          linarith
  -- the windows `k ≥ 1`
  have hwin : ∀ k ∈ Finset.Ico 1 K, ∑ q ∈ F with idx q = k, f q
      ≤ (240 + K₀) * 2000 * (Real.sqrt k / (k : ℝ) ^ 2) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hmem : ∀ q ∈ F.filter (fun q => idx q = k),
        (k : ℝ) ≤ |zeroOrdinate q| ∧ |zeroOrdinate q| < k + 1 := by
      intro q hq
      have hqk : idx q = k := (Finset.mem_filter.mp hq).2
      have := (Nat.floor_eq_iff (abs_nonneg _)).mp hqk
      exact this
    have hcount := card_absWindow_le' k (F.filter (fun q => idx q = k)) hmem
    have hterm : ∀ q ∈ F.filter (fun q => idx q = k), f q ≤ winLog k ^ 2 / (k : ℝ) ^ 2 :=
      fun q hq => weight_log_le_window' hk1 (hmem q hq).1 (hmem q hq).2
    have hcube := winLog_cube_le hk1
    have hL0 : 0 ≤ winLog k := by linarith [winLog_ge_two k]
    calc ∑ q ∈ F with idx q = k, f q
        ≤ ((F.filter (fun q => idx q = k)).card : ℝ) * (winLog k ^ 2 / (k : ℝ) ^ 2) := by
          rw [← nsmul_eq_mul]
          exact Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ (240 + K₀) * winLog k * (winLog k ^ 2 / (k : ℝ) ^ 2) := by gcongr
      _ = (240 + K₀) * (winLog k ^ 3 / (k : ℝ) ^ 2) := by ring
      _ ≤ (240 + K₀) * (2000 * Real.sqrt k / (k : ℝ) ^ 2) := by gcongr
      _ = (240 + K₀) * 2000 * (Real.sqrt k / (k : ℝ) ^ 2) := by ring
  have hsplit : ∑ q ∈ F, f q = ∑ k ∈ Finset.range K, ∑ q ∈ F with idx q = k, f q :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hrange : ∑ k ∈ Finset.range K, ∑ q ∈ F with idx q = k, f q
      = ∑ q ∈ F with idx q = 0, f q + ∑ k ∈ Finset.Ico 1 K, ∑ q ∈ F with idx q = k, f q := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ K)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  have hsum := sum_sqrt_div_sq_le K
  calc ∑ q ∈ F, f q = _ := hsplit
    _ = _ := hrange
    _ ≤ 2 * W + ∑ k ∈ Finset.Ico 1 K, (240 + K₀) * 2000 * (Real.sqrt k / (k : ℝ) ^ 2) :=
        add_le_add hwin0 (Finset.sum_le_sum hwin)
    _ = 2 * W + (240 + K₀) * 2000 * ∑ k ∈ Finset.Ico 1 K, Real.sqrt k / (k : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 2 * W + (240 + K₀) * 2000 * 3 := by gcongr

end

end RHTower
