import GaloisForLFunctions.RHTower.SmoothDyadicZetaReflection
import GaloisForLFunctions.RHTower.Sieve.HuxleyFinsetLargeValues
import GaloisForLFunctions.RHTower.Sieve.HuxleyDirichletLargeValues

/-!
# The smooth dyadic weight and the Halász–Montgomery inequality

`b(n) = V(n/2N) − V(n/N)` for the Gaussian cutoff `V` of the smooth AFE: `0 ≤ b`, `b ≥ 1/20` on
`[N, 2N]`, `b(n) ≤ (e/2√π) min(n/N, 2N/n)`, hence `∑ b(n)/n ≤ 4`.  The Gram entries
`H(τ) = ∑ b(n) n^{-1-iτ}` are the smooth dyadic sums of `SmoothDyadicZetaReflection`, and duality
gives, for points `x ∈ S` where `|∑_{N ≤ n < 2N} c_n n^{-1-ix}| ≥ V`,
`(|S| V)² ≤ 20 (∑ |c_n|²/n) ∑_{x,y ∈ S} |H(x − y)|`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology Set

noncomputable section

/-- The smooth dyadic weight `V(n/2N) − V(n/N)`. -/
def dyadicSmoothWeight (N : ℝ) (y : ℝ) : ℝ :=
  (RHTower.smoothAFECutoff (y / (2 * N))).re - (RHTower.smoothAFECutoff (y / N)).re

theorem dyadicSmoothWeight_nonneg {N y : ℝ} (hN : 0 < N) (hy : 0 < y) :
    0 ≤ dyadicSmoothWeight N y := by
  unfold dyadicSmoothWeight
  have h1 : y / (2 * N) ≤ y / N := div_le_div_of_nonneg_left hy.le hN (by linarith)
  have := RHTower.smoothAFECutoff_re_antitoneOn (by positivity : (0 : ℝ) < y / (2 * N))
    (by positivity : (0 : ℝ) < y / N) h1
  linarith

/-- The mean value form: `b(y) = e^{-(log ξ)²/4}/(2√π ξ) · y/(2N)` for some `ξ ∈ (y/2N, y/N)`. -/
theorem exists_dyadicSmoothWeight_eq {N y : ℝ} (hN : 0 < N) (hy : 0 < y) :
    ∃ ξ ∈ Set.Ioo (y / (2 * N)) (y / N), dyadicSmoothWeight N y =
      Real.exp (-(Real.log ξ) ^ 2 / 4) / (2 * Real.sqrt Real.pi * ξ) * (y / (2 * N)) := by
  have hlt : y / (2 * N) < y / N := div_lt_div_of_pos_left hy hN (by linarith)
  have hpos : 0 < y / (2 * N) := by positivity
  obtain ⟨ξ, hξ, hderiv⟩ := exists_hasDerivAt_eq_slope
    (fun u : ℝ => (RHTower.smoothAFECutoff u).re) (RHTower.smoothAFECutoffDeriv) hlt
    (fun u hu => (RHTower.hasDerivAt_smoothAFECutoff_re (by linarith [hu.1])).continuousAt
      |>.continuousWithinAt)
    (fun u hu => RHTower.hasDerivAt_smoothAFECutoff_re (by linarith [hu.1]))
  refine ⟨ξ, hξ, ?_⟩
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  unfold dyadicSmoothWeight
  unfold RHTower.smoothAFECutoffDeriv at hderiv
  have hdiff : y / N - y / (2 * N) = y / (2 * N) := by field_simp; ring
  rw [hdiff] at hderiv
  rw [eq_div_iff (by positivity)] at hderiv
  linarith

/-- `b ≥ 1/20` on `[N, 2N]`. -/
theorem dyadicSmoothWeight_ge {N y : ℝ} (hN : 0 < N) (hy1 : N ≤ y) (hy2 : y ≤ 2 * N) :
    1 / 20 ≤ dyadicSmoothWeight N y := by
  have hy : 0 < y := by linarith
  obtain ⟨ξ, hξ, heq⟩ := exists_dyadicSmoothWeight_eq hN hy
  rw [heq]
  have hξ1 : 1 / 2 ≤ ξ := by
    have : 1 / 2 ≤ y / (2 * N) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith [hξ.1]
  have hξ2 : ξ ≤ 2 := by
    have : y / N ≤ 2 := by rw [div_le_iff₀ hN]; linarith
    linarith [hξ.2]
  have hlog : (Real.log ξ) ^ 2 ≤ 1 / 2 := by
    have hl1 : Real.log ξ ≤ Real.log 2 := Real.log_le_log (by linarith) hξ2
    have hl2 : -Real.log 2 ≤ Real.log ξ := by
      rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by linarith)
    have hl2' : Real.log 2 < 0.7 := by
      have := Real.log_two_lt_d9; linarith
    nlinarith
  have hexp : Real.exp (-1 / 8) ≤ Real.exp (-(Real.log ξ) ^ 2 / 4) :=
    Real.exp_le_exp.2 (by linarith)
  have he8 : (7 : ℝ) / 8 ≤ Real.exp (-1 / 8) := by
    have := Real.add_one_le_exp (-1 / 8); linarith
  have hsq : Real.sqrt Real.pi ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
  have hy2N : 1 / 2 ≤ y / (2 * N) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hden : 2 * Real.sqrt Real.pi * ξ ≤ 8 := by
    have := Real.sqrt_nonneg Real.pi; nlinarith
  have hden0 : 0 < 2 * Real.sqrt Real.pi * ξ := by
    have := Real.sqrt_pos.2 Real.pi_pos; positivity
  calc (1 : ℝ) / 20 ≤ (7 / 8) / 8 * (1 / 2) := by norm_num
    _ ≤ Real.exp (-(Real.log ξ) ^ 2 / 4) / (2 * Real.sqrt Real.pi * ξ) * (y / (2 * N)) := by
        gcongr
        · exact he8.trans hexp

/-- `b(y) ≤ (e/2√π) min(y/2N, 2N/y)`. -/
theorem dyadicSmoothWeight_le {N y : ℝ} (hN : 0 < N) (hy : 0 < y) :
    dyadicSmoothWeight N y ≤ Real.exp 1 / (2 * Real.sqrt Real.pi) * min (y / (2 * N)) (2 * N / y) := by
  obtain ⟨ξ, hξ, heq⟩ := exists_dyadicSmoothWeight_eq hN hy
  rw [heq]
  have hξ0 : 0 < ξ := by linarith [hξ.1, (by positivity : (0 : ℝ) < y / (2 * N))]
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  set a : ℝ := y / (2 * N) with ha
  have ha0 : 0 < a := by positivity
  have haξ : a ≤ ξ := hξ.1.le
  -- `e^{-(log ξ)²/4} ≤ e · min(ξ, 1/ξ)`
  have hgauss : Real.exp (-(Real.log ξ) ^ 2 / 4) ≤ Real.exp 1 * min ξ (1 / ξ) := by
    have hkey : Real.exp (-(Real.log ξ) ^ 2 / 4) ≤ Real.exp (1 - |Real.log ξ|) :=
      Real.exp_le_exp.2 (by nlinarith [sq_abs (Real.log ξ), sq_nonneg (|Real.log ξ| / 2 - 1)])
    refine hkey.trans (le_of_eq ?_)
    rcases le_total ξ 1 with h1 | h1
    · rw [abs_of_nonpos (Real.log_nonpos hξ0.le h1), sub_neg_eq_add, Real.exp_add,
        Real.exp_log hξ0, min_eq_left (by rw [le_div_iff₀ hξ0]; nlinarith)]
    · rw [abs_of_nonneg (Real.log_nonneg h1), Real.exp_sub, Real.exp_log hξ0,
        min_eq_right (by rw [div_le_iff₀ hξ0]; nlinarith)]
      ring
  have hmin_le : min ξ (1 / ξ) * a / ξ ≤ min a (1 / a) := by
    rcases le_total ξ 1 with h1 | h1
    · rw [min_eq_left (by rw [le_div_iff₀ hξ0]; nlinarith), mul_div_assoc,
        mul_div_cancel₀ _ hξ0.ne']
      refine le_min le_rfl ?_
      rw [le_div_iff₀ ha0]; nlinarith
    · rw [min_eq_right (by rw [div_le_iff₀ hξ0]; nlinarith)]
      have heq2 : 1 / ξ * a / ξ = a / (ξ * ξ) := by field_simp
      rw [heq2]
      have hξξ : 1 ≤ ξ * ξ := by nlinarith
      refine le_min (div_le_self ha0.le hξξ) ?_
      rw [div_le_div_iff₀ (by positivity) ha0]
      nlinarith
  have h2N : 1 / a = 2 * N / y := by rw [ha]; field_simp
  rw [← h2N]
  calc Real.exp (-(Real.log ξ) ^ 2 / 4) / (2 * Real.sqrt Real.pi * ξ) * a
      = Real.exp (-(Real.log ξ) ^ 2 / 4) * a / ξ / (2 * Real.sqrt Real.pi) := by
        field_simp
    _ ≤ Real.exp 1 * min ξ (1 / ξ) * a / ξ / (2 * Real.sqrt Real.pi) := by gcongr
    _ = Real.exp 1 / (2 * Real.sqrt Real.pi) * (min ξ (1 / ξ) * a / ξ) := by ring
    _ ≤ Real.exp 1 / (2 * Real.sqrt Real.pi) * min a (1 / a) := by gcongr

/-- The Gram coefficient `b(n+1)/(n+1)`. -/
def dyadicGramCoeff (N : ℝ) (n : ℕ) : ℝ := dyadicSmoothWeight N ((n : ℝ) + 1) / ((n : ℝ) + 1)

theorem dyadicGramCoeff_nonneg {N : ℝ} (hN : 0 < N) (n : ℕ) : 0 ≤ dyadicGramCoeff N n :=
  div_nonneg (dyadicSmoothWeight_nonneg hN (by positivity)) (by positivity)

theorem dyadicGramCoeff_le {N : ℝ} (hN : 0 < N) (n : ℕ) :
    dyadicGramCoeff N n ≤ 6 / 5 * min (1 / (2 * N)) (2 * N / ((n : ℝ) + 1) ^ 2) := by
  have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hw := dyadicSmoothWeight_le hN hy
  have hc : Real.exp 1 / (2 * Real.sqrt Real.pi) ≤ 6 / 5 := by
    have he := Real.exp_one_lt_d9
    have hsq : (17 / 10 : ℝ) ≤ Real.sqrt Real.pi := by
      rw [show (17 / 10 : ℝ) = Real.sqrt ((17 / 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  unfold dyadicGramCoeff
  rw [div_le_iff₀ hy]
  have hmin : min ((n + 1 : ℝ) / (2 * N)) (2 * N / (n + 1 : ℝ)) =
      min (1 / (2 * N)) (2 * N / ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1) := by
    rw [min_mul_of_nonneg _ _ hy.le]
    congr 1
    · field_simp
    · field_simp
  calc dyadicSmoothWeight N ((n : ℝ) + 1)
      ≤ Real.exp 1 / (2 * Real.sqrt Real.pi) *
          min (((n : ℝ) + 1) / (2 * N)) (2 * N / ((n : ℝ) + 1)) := hw
    _ ≤ 6 / 5 * min (((n : ℝ) + 1) / (2 * N)) (2 * N / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hc (le_min (by positivity) (by positivity))
    _ = 6 / 5 * min (1 / (2 * N)) (2 * N / ((n : ℝ) + 1) ^ 2) * ((n : ℝ) + 1) := by
        rw [hmin]; ring

theorem summable_dyadicGramCoeff {N : ℝ} (hN : 0 < N) : Summable (dyadicGramCoeff N) := by
  have hmaj : Summable fun n : ℕ => 6 / 5 * (2 * N) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
    refine Summable.mul_left _ ?_
    have h1 := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    refine h1.congr fun n => ?_
    rw [Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity)]
  refine hmaj.of_nonneg_of_le (dyadicGramCoeff_nonneg hN) fun n => ?_
  refine (dyadicGramCoeff_le hN n).trans ?_
  have : min (1 / (2 * N)) (2 * N / ((n : ℝ) + 1) ^ 2) ≤ 2 * N * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [Real.rpow_neg (by positivity), Real.rpow_two]; ring
  calc 6 / 5 * min (1 / (2 * N)) (2 * N / ((n : ℝ) + 1) ^ 2)
      ≤ 6 / 5 * (2 * N * ((n : ℝ) + 1) ^ (-(2 : ℝ))) := by gcongr
    _ = 6 / 5 * (2 * N) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by ring

/-- **The total Gram mass**: `∑ b(n)/n ≤ 3` for `N ≥ 1`. -/
theorem tsum_dyadicGramCoeff_le {N : ℝ} (hN : 1 ≤ N) : ∑' n, dyadicGramCoeff N n ≤ 3 := by
  have hN0 : 0 < N := by linarith
  set L : ℕ := ⌈2 * N⌉₊ with hL
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (by
    rw [hL]; exact Nat.ceil_pos.2 (by positivity) |>.ne')
  have hLle : (L : ℝ) ≤ 2 * N + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hLge : 2 * N ≤ (L : ℝ) := Nat.le_ceil _
  have hs := summable_dyadicGramCoeff hN0
  rw [← hs.sum_add_tsum_nat_add L]
  have hhead : ∑ n ∈ Finset.range L, dyadicGramCoeff N n ≤ 6 / 5 * ((2 * N + 1) / (2 * N)) := by
    calc ∑ n ∈ Finset.range L, dyadicGramCoeff N n ≤ ∑ n ∈ Finset.range L, 6 / 5 * (1 / (2 * N)) :=
          Finset.sum_le_sum fun n _ => (dyadicGramCoeff_le hN0 n).trans
            (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
      _ = 6 / 5 * (1 / (2 * N)) * L := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 6 / 5 * (1 / (2 * N)) * (2 * N + 1) := by gcongr
      _ = 6 / 5 * ((2 * N + 1) / (2 * N)) := by ring
  have htail : ∑' i, dyadicGramCoeff N (i + L) ≤ 6 / 5 * (2 * N) * (1 / (L : ℝ)) := by
    have hbound : ∀ i : ℕ, dyadicGramCoeff N (i + L) ≤
        6 / 5 * (2 * N) * (((i + L + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ)) := by
      intro i
      refine (dyadicGramCoeff_le hN0 (i + L)).trans ?_
      have : min (1 / (2 * N)) (2 * N / (((i + L : ℕ) : ℝ) + 1) ^ 2) ≤
          2 * N * (((i + L + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ)) := by
        refine (min_le_right _ _).trans (le_of_eq ?_)
        rw [Real.rpow_neg (by positivity), Real.rpow_two]; push_cast; ring
      calc 6 / 5 * min (1 / (2 * N)) (2 * N / (((i + L : ℕ) : ℝ) + 1) ^ 2)
          ≤ 6 / 5 * (2 * N * (((i + L + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ))) := by gcongr
        _ = _ := by ring
    have hmaj : Summable fun i : ℕ => 6 / 5 * (2 * N) * (((i + L + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ)) := by
      refine Summable.mul_left _ ?_
      have h1 := (Real.summable_one_div_nat_add_rpow ((L : ℝ) + 1) 2).2 (by norm_num)
      refine h1.congr fun i => ?_
      rw [Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity)]
      push_cast; ring_nf
    calc ∑' i, dyadicGramCoeff N (i + L)
        ≤ ∑' i : ℕ, 6 / 5 * (2 * N) * (((i + L + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ)) :=
          ((summable_nat_add_iff L).2 hs).tsum_le_tsum hbound hmaj
      _ = 6 / 5 * (2 * N) * ∑' i : ℕ, (((i + L + 1 : ℕ) : ℝ)) ^ (-(2 : ℝ)) := tsum_mul_left
      _ ≤ 6 / 5 * (2 * N) * ((L : ℝ) ^ (1 - (2 : ℝ)) / ((2 : ℝ) - 1)) := by
          gcongr
          exact RHTower.Sieve.tsum_tail_rpow_neg_le (by norm_num) hL1
      _ = 6 / 5 * (2 * N) * (1 / (L : ℝ)) := by
          rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]; ring
  have h1 : (2 * N + 1) / (2 * N) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h2 : 2 * N * (1 / (L : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]; exact hLge
  nlinarith

/-- The Gram entries as a Dirichlet series with the nonnegative coefficients `b(n)/n`. -/
theorem dyadicSmoothGram_eq_tsum_gramCoeff {N : ℝ} (hN : 0 < N) (τ : ℝ) :
    RHTower.dyadicSmoothGram N τ =
      ∑' n : ℕ, (dyadicGramCoeff N n : ℂ) * ((n : ℂ) + 1) ^ (-((τ : ℂ) * I)) := by
  set s : ℂ := (1 : ℂ) + (τ : ℂ) * I with hs
  have hsc : 1 < s.re + 1 := by simp [hs]
  obtain ⟨K, hK0, hK⟩ := RHTower.exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  have hsum : ∀ x : ℝ, 0 < x → Summable fun n : ℕ =>
      (n + 1 : ℂ) ^ (-s) * RHTower.smoothAFECutoff ((n + 1 : ℝ) / x) := by
    intro x hx
    have hmaj : Summable fun n : ℕ => (K * x) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
      refine Summable.mul_left _ ?_
      have h1 := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
      refine h1.congr fun n => ?_
      rw [Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity)]
    refine Summable.of_norm (hmaj.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_)
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_mul, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    have hV := hK (x := ((n : ℝ) + 1) / x) (by positivity)
    rw [Real.rpow_neg_one] at hV
    have hre : (-s).re = -1 := by simp [hs]
    rw [hre]
    calc ((n : ℝ) + 1) ^ (-1 : ℝ) * ‖RHTower.smoothAFECutoff (((n : ℝ) + 1) / x)‖
        ≤ ((n : ℝ) + 1) ^ (-1 : ℝ) * (K * (((n : ℝ) + 1) / x)⁻¹) := by
          gcongr
      _ = (K * x) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
          rw [Real.rpow_neg_one, Real.rpow_neg hn.le, Real.rpow_two]; field_simp
  unfold RHTower.dyadicSmoothGram
  rw [RHTower.smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff (by positivity) one_pos hsc,
    RHTower.smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff hN one_pos hsc,
    ← (hsum _ (by positivity)).tsum_sub (hsum _ hN)]
  refine tsum_congr fun n => ?_
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hkey : RHTower.smoothAFECutoff (((n : ℝ) + 1) / (2 * N)) -
      RHTower.smoothAFECutoff (((n : ℝ) + 1) / N) =
      (((RHTower.smoothAFECutoff (((n : ℝ) + 1) / (2 * N))).re -
        (RHTower.smoothAFECutoff (((n : ℝ) + 1) / N)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [RHTower.smoothAFECutoff_im_eq_zero (by positivity : (0 : ℝ) < ((n : ℝ) + 1) / (2 * N)),
        RHTower.smoothAFECutoff_im_eq_zero (by positivity : (0 : ℝ) < ((n : ℝ) + 1) / N)]
  rw [← mul_sub]
  push_cast at hkey ⊢
  rw [hkey]
  unfold dyadicGramCoeff dyadicSmoothWeight
  have hsplit : ((n : ℂ) + 1) ^ (-s) = ((n : ℂ) + 1) ^ (-(1 : ℂ)) * ((n : ℂ) + 1) ^ (-((τ : ℂ) * I)) := by
    rw [← Complex.cpow_add _ _ hn, hs]; ring_nf
  rw [hsplit, Complex.cpow_neg_one]
  push_cast
  field_simp

/-- `exp(−i t log n) = n^{−it}` for `n ≥ 1`. -/
theorem exp_neg_mul_log_natCast_eq_cpow {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * I) = (n : ℂ) ^ (-((t : ℂ) * I)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
    ← Complex.ofReal_log (by positivity)]
  congr 1
  push_cast; ring

/-- `conj((m+1)^{-iy}) = (m+1)^{iy}`. -/
theorem conj_natSucc_cpow_neg_mul_I (m : ℕ) (y : ℝ) :
    (starRingEnd ℂ) (((m : ℂ) + 1) ^ (-((y : ℂ) * I))) = ((m : ℂ) + 1) ^ ((y : ℂ) * I) := by
  have hne : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_conj]
  congr 1
  have hlog : Complex.log ((m : ℂ) + 1) = ((Real.log ((m : ℝ) + 1) : ℝ) : ℂ) := by
    rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  rw [hlog, map_mul, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **The smooth Halász–Montgomery inequality.** -/
theorem sq_sum_norm_blockPoly_le_gram {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ) (S : Finset ℝ) :
    (∑ x ∈ S, ‖blockPoly N c 1 x‖) ^ 2 ≤
      20 * (∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ)) *
        ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ → ℂ := fun x => blockPoly N c 1 x with hP
  set η : ℝ → ℂ := fun x => if P x = 0 then 0 else (starRingEnd ℂ) (P x) / (‖P x‖ : ℂ) with hη
  have hηP : ∀ x, η x * P x = (‖P x‖ : ℂ) := by
    intro x
    simp only [hη]
    split_ifs with h0
    · simp [h0]
    · have hn : (‖P x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h0)
      rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
      ring
  have hηn : ∀ x, ‖η x‖ ≤ 1 := by
    intro x
    simp only [hη]
    split_ifs with h0
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.2 h0)]
  set X : ℕ → ℂ := fun n => ∑ x ∈ S, η x * (n : ℂ) ^ (-((x : ℂ) * I)) with hX
  set w : ℕ → ℝ := fun n => dyadicSmoothWeight N n with hw
  -- the duality identity
  have hdual : ((∑ x ∈ S, ‖P x‖ : ℝ) : ℂ) =
      ∑ n ∈ Finset.Ico N (2 * N), c n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ) * X n := by
    push_cast
    rw [← Finset.sum_congr rfl fun x _ => hηP x]
    simp only [hP, blockPoly, hX, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun x _ => ?_
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Ico.1 hn).1; omega
    rw [exp_neg_mul_log_natCast_eq_cpow hn1]
    ring
  have hnorm : ∑ x ∈ S, ‖P x‖ ≤
      ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ * (n : ℝ) ^ (-(1 : ℝ)) * ‖X n‖ := by
    have h := congrArg norm hdual
    rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun x _ => norm_nonneg _)] at h
    rw [h]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  -- weights on the block
  have hwlow : ∀ n ∈ Finset.Ico N (2 * N), 1 / 20 ≤ w n := by
    intro n hn
    have h1 : (N : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.1 hn).1
    have h2 : (n : ℝ) ≤ 2 * N := by
      have := (Finset.mem_Ico.1 hn).2; exact_mod_cast this.le
    exact dyadicSmoothWeight_ge hN0 h1 h2
  have hnpos : ∀ n ∈ Finset.Ico N (2 * N), (0 : ℝ) < n := by
    intro n hn; exact_mod_cast (by have := (Finset.mem_Ico.1 hn).1; omega : 0 < n)
  -- Cauchy–Schwarz with the weights
  have hCS : (∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ * (n : ℝ) ^ (-(1 : ℝ)) * ‖X n‖) ^ 2 ≤
      (∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / ((n : ℝ) * w n)) *
        ∑ n ∈ Finset.Ico N (2 * N), w n / n * ‖X n‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico N (2 * N))
      (fun n => ‖c n‖ / Real.sqrt ((n : ℝ) * w n))
      (fun n => Real.sqrt (w n / n) * ‖X n‖)
    have e1 : ∀ n ∈ Finset.Ico N (2 * N),
        ‖c n‖ / Real.sqrt ((n : ℝ) * w n) * (Real.sqrt (w n / n) * ‖X n‖) =
          ‖c n‖ * (n : ℝ) ^ (-(1 : ℝ)) * ‖X n‖ := by
      intro n hn
      have hn0 := hnpos n hn
      have hw0 : 0 < w n := lt_of_lt_of_le (by norm_num) (hwlow n hn)
      rw [Real.rpow_neg_one, Real.sqrt_div' _ hn0.le, Real.sqrt_mul hn0.le]
      have hs1 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
      have hs2 : 0 < Real.sqrt (w n) := Real.sqrt_pos.2 hw0
      field_simp
      rw [Real.sq_sqrt hn0.le]; ring
    have e2 : ∀ n ∈ Finset.Ico N (2 * N),
        (‖c n‖ / Real.sqrt ((n : ℝ) * w n)) ^ 2 = ‖c n‖ ^ 2 / ((n : ℝ) * w n) := by
      intro n hn
      have hw0 : 0 < w n := lt_of_lt_of_le (by norm_num) (hwlow n hn)
      rw [div_pow, Real.sq_sqrt (by positivity [hnpos n hn])]
    have e3 : ∀ n ∈ Finset.Ico N (2 * N),
        (Real.sqrt (w n / n) * ‖X n‖) ^ 2 = w n / n * ‖X n‖ ^ 2 := by
      intro n hn
      have hw0 : 0 < w n := lt_of_lt_of_le (by norm_num) (hwlow n hn)
      rw [mul_pow, Real.sq_sqrt (by positivity [hnpos n hn])]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
    exact h
  -- the coefficient side
  have hA : ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / ((n : ℝ) * w n) ≤
      20 * ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 := hnpos n hn
    have hw := hwlow n hn
    have hw0 : 0 < w n := lt_of_lt_of_le (by norm_num) hw
    calc ‖c n‖ ^ 2 / ((n : ℝ) * w n) = (‖c n‖ ^ 2 / (n : ℝ)) * (1 / w n) := by
          field_simp
      _ ≤ (‖c n‖ ^ 2 / (n : ℝ)) * 20 :=
          mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ hw0]; linarith) (by positivity)
      _ = 20 * (‖c n‖ ^ 2 / (n : ℝ)) := by ring
  -- the Gram side
  have hB : ∑ n ∈ Finset.Ico N (2 * N), w n / n * ‖X n‖ ^ 2 ≤
      ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ := by
    set Y : ℕ → ℝ := fun m => dyadicGramCoeff N m * ‖X (m + 1)‖ ^ 2 with hY
    have hY0 : ∀ m, 0 ≤ Y m := fun m => mul_nonneg (dyadicGramCoeff_nonneg hN0 m) (by positivity)
    have hXb : ∀ n, ‖X n‖ ≤ S.card := by
      intro n
      refine (norm_sum_le _ _).trans ?_
      calc ∑ x ∈ S, ‖η x * (n : ℂ) ^ (-((x : ℂ) * I))‖ ≤ ∑ x ∈ S, (1 : ℝ) := by
            refine Finset.sum_le_sum fun x _ => ?_
            rw [norm_mul]
            have h1 : ‖(n : ℂ) ^ (-((x : ℂ) * I))‖ ≤ 1 := by
              rcases eq_or_ne n 0 with h | h
              · subst h
                by_cases hx : x = 0
                · subst hx; simp
                · rw [Nat.cast_zero, Complex.zero_cpow (by simpa using hx)]; simp
              · rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
                  Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h)]
                simp
            nlinarith [hηn x, norm_nonneg (η x), norm_nonneg ((n : ℂ) ^ (-((x : ℂ) * I)))]
        _ = S.card := by simp
    have hYs : Summable Y := by
      refine ((summable_dyadicGramCoeff hN0).mul_right ((S.card : ℝ) ^ 2)).of_nonneg_of_le hY0
        fun m => ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hXb _) 2)
        (dyadicGramCoeff_nonneg hN0 m)
    -- the block sum is part of the full series
    have hpart : ∑ n ∈ Finset.Ico N (2 * N), w n / n * ‖X n‖ ^ 2 ≤ ∑' m, Y m := by
      have hre : ∑ n ∈ Finset.Ico N (2 * N), w n / n * ‖X n‖ ^ 2 =
          ∑ m ∈ Finset.Ico (N - 1) (2 * N - 1), Y m := by
        refine Finset.sum_nbij' (fun n => n - 1) (fun m => m + 1) ?_ ?_ ?_ ?_ ?_
        · intro n hn; simp only [Finset.mem_Ico] at hn ⊢; omega
        · intro m hm; simp only [Finset.mem_Ico] at hm ⊢; omega
        · intro n hn; simp only [Finset.mem_Ico] at hn; omega
        · intro m _; simp
        · intro n hn
          simp only [Finset.mem_Ico] at hn
          have hn1 : n - 1 + 1 = n := by omega
          simp only [hY, dyadicGramCoeff, hw, hn1]
          have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
          rw [hcast]
      rw [hre]
      exact hYs.sum_le_tsum _ fun m _ => hY0 m
    -- the full series is the Gram form
    have hgram : ((∑' m, Y m : ℝ) : ℂ) =
        ∑ x ∈ S, ∑ y ∈ S, η x * (starRingEnd ℂ) (η y) * RHTower.dyadicSmoothGram N (x - y) := by
      rw [Complex.ofReal_tsum]
      have hterm : ∀ m : ℕ, ((Y m : ℝ) : ℂ) = ∑ x ∈ S, ∑ y ∈ S,
          η x * (starRingEnd ℂ) (η y) *
            ((dyadicGramCoeff N m : ℂ) * ((m : ℂ) + 1) ^ (-(((x - y : ℝ) : ℂ) * I))) := by
        intro m
        simp only [hY]
        push_cast
        have hXX : ((‖X (m + 1)‖ : ℂ)) ^ 2 = X (m + 1) * (starRingEnd ℂ) (X (m + 1)) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
        rw [hXX]
        have hbase : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
        simp only [hX, hbase, map_sum, map_mul, conj_natSucc_cpow_neg_mul_I]
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hne : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have hsplit : ((m : ℂ) + 1) ^ (-(((x - y : ℝ) : ℂ) * I)) =
            ((m : ℂ) + 1) ^ (-((x : ℂ) * I)) * ((m : ℂ) + 1) ^ ((y : ℂ) * I) := by
          rw [← Complex.cpow_add _ _ hne]; push_cast; ring_nf
        push_cast at hsplit ⊢
        rw [hsplit]
        ring
      rw [tsum_congr hterm]
      rw [Summable.tsum_finsetSum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [Summable.tsum_finsetSum]
        · refine Finset.sum_congr rfl fun y _ => ?_
          rw [tsum_mul_left, ← dyadicSmoothGram_eq_tsum_gramCoeff hN0]
        · intro y _
          refine Summable.mul_left _ ?_
          refine Summable.of_norm ?_
          refine (summable_dyadicGramCoeff hN0).of_nonneg_of_le (fun m => norm_nonneg _) fun m => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (dyadicGramCoeff_nonneg hN0 m),
            show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
          simp
      · intro x _
        refine summable_sum fun y _ => ?_
        refine Summable.mul_left _ ?_
        refine Summable.of_norm ?_
        refine (summable_dyadicGramCoeff hN0).of_nonneg_of_le (fun m => norm_nonneg _) fun m => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (dyadicGramCoeff_nonneg hN0 m),
          show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
        simp
    have hle : ∑' m, Y m ≤ ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ := by
      have h := congrArg norm hgram
      rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg hY0)] at h
      rw [h]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have h1 := hηn x
      have h2 := hηn y
      have h3 := norm_nonneg (RHTower.dyadicSmoothGram (N : ℝ) (x - y))
      have h4 : ‖η x‖ * ‖η y‖ ≤ 1 := by nlinarith [norm_nonneg (η x), norm_nonneg (η y)]
      nlinarith [norm_nonneg (η x), norm_nonneg (η y)]
    exact hpart.trans hle
  have hS0 : 0 ≤ ∑ x ∈ S, ‖P x‖ := Finset.sum_nonneg fun x _ => norm_nonneg _
  have hsq : (∑ x ∈ S, ‖P x‖) ^ 2 ≤
      (∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ * (n : ℝ) ^ (-(1 : ℝ)) * ‖X n‖) ^ 2 :=
    pow_le_pow_left₀ hS0 hnorm 2
  have hB0 : 0 ≤ ∑ n ∈ Finset.Ico N (2 * N), w n / n * ‖X n‖ ^ 2 :=
    Finset.sum_nonneg fun n hn => mul_nonneg (div_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1 / 20).trans (hwlow n hn)) (hnpos n hn).le) (by positivity)
  have hA0 : 0 ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ) :=
    Finset.sum_nonneg fun n hn => div_nonneg (by positivity) (hnpos n hn).le
  calc (∑ x ∈ S, ‖blockPoly N c 1 x‖) ^ 2 ≤ _ := hsq
    _ ≤ _ := hCS
    _ ≤ (20 * ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ)) *
          ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ :=
        mul_le_mul hA hB hB0 (by positivity)
    _ = _ := by ring

end

end RHTower.Sieve

