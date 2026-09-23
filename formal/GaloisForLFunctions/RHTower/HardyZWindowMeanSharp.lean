import GaloisForLFunctions.RHTower.HardyZWindowMean
import GaloisForLFunctions.RHTower.ShortWindowNoGo

/-!
# A sharp window mean for Hardy's `Z`: the resonance-graded bound

The trivial window mean is `O(T^{3/4})`: every below-conductor term of the direct edge is
second-derivative tested at `O(√T)`.  But on a window `[a,b] ⊆ [T,2T]` the phase rate of
the `m`-th direct term is `log(√(τ/2π)/m) + O(1/T)`, so only the `m` inside a narrow band
around the moving resonance `√(τ/2π)` lack a usable first-derivative test.  Grading the
first-derivative test by the logarithmic distance to the resonance band and summing with a
harmonic telescope — no dyadic shells — bounds the window mean by
`C·(T^{1/4}(1+log T) + (b-a)·T^{-1/4} + √x + (b-a)·T/x)` for every cutoff `x`.
-/

open Set MeasureTheory Complex Finset

namespace RHTower

noncomputable section

/-! ## The phase-rate window bounds -/

private theorem hardy_rate_err_le {T τ : ℝ} (hT : 16 ≤ T) (hτT : T ≤ τ) :
    33 / (16 * τ ^ (2 : ℕ)) + Real.pi / (2 * τ) ≤ 2 / T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hτ0 : (0 : ℝ) < τ := by linarith
  have h1 : 33 / (16 * τ ^ (2 : ℕ)) ≤ 33 / 256 / T := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hτT (by linarith : (0 : ℝ) ≤ 16 * τ)]
  have h2 : Real.pi / (2 * τ) ≤ 1.575 / T := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h3 : 33 / 256 / T + 1.575 / T ≤ 2 / T := by
    have he : 33 / 256 / T + 1.575 / T = (33 / 256 + 1.575) / T := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (by norm_num) hT0.le
  linarith

theorem gammaHardyPhaseRate_window_lower {T a τ : ℝ} (hT : 16 ≤ T) (ha : T ≤ a)
    (hτa : a ≤ τ) (_hτ2T : τ ≤ 2 * T) :
    Real.log (a / (2 * Real.pi)) / 2 - 2 / T ≤ gammaHardyPhaseRate τ := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hbound := gammaHardyPhaseRate_sub_log_conductor_bound hτ0
  have hlow := (abs_le.mp hbound).1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmono : Real.log (a / (2 * Real.pi)) ≤ Real.log (τ / (2 * Real.pi)) :=
    Real.log_le_log (div_pos (by linarith) (by positivity))
      (div_le_div_of_nonneg_right hτa (by positivity))
  have herr := hardy_rate_err_le hT (le_trans ha hτa)
  linarith

theorem gammaHardyPhaseRate_window_upper {T b τ : ℝ} (hT : 16 ≤ T) (hτT : T ≤ τ)
    (hτb : τ ≤ b) (_hb : b ≤ 2 * T) :
    gammaHardyPhaseRate τ ≤ Real.log (b / (2 * Real.pi)) / 2 + 2 / T := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hbound := gammaHardyPhaseRate_sub_log_conductor_bound hτ0
  have hup := (abs_le.mp hbound).2
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmono : Real.log (τ / (2 * Real.pi)) ≤ Real.log (b / (2 * Real.pi)) :=
    Real.log_le_log (div_pos (by linarith) (by positivity))
      (div_le_div_of_nonneg_right hτb (by positivity))
  have herr := hardy_rate_err_le hT hτT
  linarith

/-! ## The graded first-derivative window bounds -/

theorem norm_integral_twist_first_le_window_graded {T a b L lam : ℝ} (hT : 16 ≤ T)
    (ha : T ≤ a) (hb : b ≤ 2 * T) (hab : a ≤ b) (hlam : 0 < lam)
    (hrate : ∀ τ ∈ Set.Icc a b, lam ≤ |gammaHardyPhaseRate τ - L|) (c : ℂ) :
    ‖∫ τ in a..b, c * Complex.exp (Complex.I * (hardyTwistPhase L τ : ℂ))‖
      ≤ 8 * ‖c‖ / lam := by
  have hT4 : (4 : ℝ) ≤ T := by linarith
  have hsub : Set.Icc a b ⊆ Set.Icc T (2 * T) := Set.Icc_subset_Icc ha hb
  have h := firstDerivTestOn (a := a) (b := b) (lam := lam) hab hlam
    (φ := hardyTwistPhase L) (φ' := fun τ => gammaHardyPhaseRate τ - L)
    (φ'' := deriv gammaHardyPhaseRate) (A := fun _ => c) (A' := fun _ => 0)
    (fun τ _ => hasDerivAt_hardyTwistPhase L τ)
    (fun τ _ => hasDerivAt_hardyTwistRate L τ)
    continuous_deriv_gammaHardyPhaseRate.continuousOn
    (fun τ _ => hasDerivAt_const τ c)
    continuousOn_const
    (fun τ hτ => le_trans (by positivity) (curvature_lower_dyadic hT4 (hsub hτ)))
    hrate
  have hzero : (∫ _ : ℝ in a..b, ‖(0 : ℂ)‖) = 0 := by simp
  rw [hzero] at h
  refine le_trans h (le_of_eq ?_)
  ring

theorem abs_integral_hardyDirectTerm_le_first_window_graded {T a b lam : ℝ} (hT : 16 ≤ T)
    (ha : T ≤ a) (hb : b ≤ 2 * T) (hab : a ≤ b) (x : ℝ) (n : ℕ) (hlam : 0 < lam)
    (hrate : ∀ τ ∈ Set.Icc a b, lam ≤ |gammaHardyPhaseRate τ - Real.log ((n : ℝ) + 1)|) :
    |∫ τ in a..b, hardyDirectTerm x n τ| ≤ 8 * cutoffWeight x n / lam := by
  have hs : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by positivity
  rw [integral_hardyDirectTerm_eq, abs_mul, abs_of_nonneg hs]
  have hre := Complex.abs_re_le_norm (∫ τ in a..b,
    smoothAFECutoff (((n : ℝ) + 1) / x) *
      Complex.exp (Complex.I *
        ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ)))
  have hosc := norm_integral_twist_first_le_window_graded hT ha hb hab hlam hrate
    (smoothAFECutoff (((n : ℝ) + 1) / x))
  have hchain := le_trans hre hosc
  calc (Real.sqrt ((n : ℝ) + 1))⁻¹ * |(∫ τ in a..b,
        smoothAFECutoff (((n : ℝ) + 1) / x) *
          Complex.exp (Complex.I *
            ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))).re|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (8 * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖ / lam) :=
        mul_le_mul_of_nonneg_left hchain hs
    _ = 8 * cutoffWeight x n / lam := by
        unfold cutoffWeight; ring

/-! ## Band rate bounds -/

theorem rate_abs_lower_low {T a b L lam : ℝ} (hT : 16 ≤ T) (ha : T ≤ a)
    (hb : b ≤ 2 * T) (hlam4 : 4 / T ≤ lam)
    (hL : L ≤ Real.log (a / (2 * Real.pi)) / 2 - lam) :
    ∀ τ ∈ Set.Icc a b, lam / 2 ≤ |gammaHardyPhaseRate τ - L| := by
  intro τ hτ
  have h1 := gammaHardyPhaseRate_window_lower hT ha hτ.1 (le_trans hτ.2 hb)
  have hT0 : (0 : ℝ) < T := by linarith
  have h4 := (div_le_iff₀ hT0).mp hlam4
  have h3 : 2 / T ≤ lam / 2 := by
    rw [div_le_div_iff₀ hT0 (by norm_num)]
    linarith
  have h2 : lam / 2 ≤ gammaHardyPhaseRate τ - L := by linarith
  exact le_trans h2 (le_abs_self _)

theorem rate_abs_lower_high {T a b L lam : ℝ} (hT : 16 ≤ T) (ha : T ≤ a)
    (hb : b ≤ 2 * T) (hlam4 : 4 / T ≤ lam)
    (hL : Real.log (b / (2 * Real.pi)) / 2 + lam ≤ L) :
    ∀ τ ∈ Set.Icc a b, lam / 2 ≤ |gammaHardyPhaseRate τ - L| := by
  intro τ hτ
  have h1 := gammaHardyPhaseRate_window_upper hT (le_trans ha hτ.1) hτ.2 hb
  have hT0 : (0 : ℝ) < T := by linarith
  have h4 := (div_le_iff₀ hT0).mp hlam4
  have h3 : 2 / T ≤ lam / 2 := by
    rw [div_le_div_iff₀ hT0 (by norm_num)]
    linarith
  calc lam / 2 ≤ -(gammaHardyPhaseRate τ - L) := by linarith
    _ ≤ |gammaHardyPhaseRate τ - L| := neg_le_abs _

/-! ## Harmonic sum devices -/

private theorem sum_range_inv_add_one_le (cnt : ℕ) :
    ∑ j ∈ Finset.range cnt, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log cnt := by
  induction cnt with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    by_cases h0 : N = 0
    · subst h0
      norm_num
    · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have hstep : 1 / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by
        have hrat : Real.log ((N : ℝ) / ((N : ℝ) + 1)) ≤ (N : ℝ) / ((N : ℝ) + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hsplit : Real.log ((N : ℝ) / ((N : ℝ) + 1))
            = Real.log (N : ℝ) - Real.log ((N : ℝ) + 1) :=
          Real.log_div (by linarith) (by linarith)
        have hval : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by
          field_simp
          ring
        rw [hsplit, hval] at hrat
        linarith
      linarith [ih]

private theorem sum_Ico_inv_sub_le {P : ℝ} (lo hi : ℕ) (hhi : (hi : ℝ) ≤ P - 1) :
    ∑ n ∈ Finset.Ico lo hi, 1 / (P - ((n : ℝ) + 1)) ≤ 1 + Real.log hi := by
  by_cases hle : hi ≤ lo
  · rw [Finset.Ico_eq_empty (Nat.not_lt.mpr hle)]
    rcases Nat.eq_zero_or_pos hi with h0 | h1
    · subst h0; simp
    · have : (0 : ℝ) ≤ Real.log hi :=
        Real.log_nonneg (by exact_mod_cast h1)
      simp only [Finset.sum_empty]
      linarith
  · have hlt : lo < hi := Nat.lt_of_not_le hle
    have hterm : ∀ n ∈ Finset.Ico lo hi,
        1 / (P - ((n : ℝ) + 1)) ≤ 1 / ((hi : ℝ) - (n : ℝ)) := by
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hnh : (n : ℝ) < (hi : ℝ) := by exact_mod_cast hn'.2
      have hpos : (0 : ℝ) < (hi : ℝ) - (n : ℝ) := by linarith
      refine one_div_le_one_div_of_le hpos ?_
      linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have hcnt : ∀ j ∈ Finset.range (hi - lo),
        1 / ((hi : ℝ) - ((lo + j : ℕ) : ℝ)) = 1 / (((hi - lo - 1 - j : ℕ) : ℝ) + 1) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hjlt : lo + j < hi := by omega
      have h2 : ((hi - lo - 1 - j : ℕ) : ℝ) = (hi : ℝ) - (lo : ℝ) - 1 - (j : ℝ) := by
        have h3 : hi - lo - 1 - j = hi - (lo + 1 + j) := by omega
        rw [h3, Nat.cast_sub (by omega : lo + 1 + j ≤ hi)]
        push_cast
        ring
      congr 1
      rw [h2]
      push_cast
      ring
    rw [Finset.sum_congr rfl hcnt,
      Finset.sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) (hi - lo)]
    refine le_trans (sum_range_inv_add_one_le (hi - lo)) ?_
    have hmono : Real.log ((hi - lo : ℕ) : ℝ) ≤ Real.log hi := by
      have h1 : 0 < hi - lo := by omega
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast h1
      · exact_mod_cast Nat.sub_le hi lo
    linarith

private theorem sum_Ico_inv_sub_le' {Q : ℝ} (lo hi : ℕ) (hlo : Q ≤ (lo : ℝ)) :
    ∑ n ∈ Finset.Ico lo hi, 1 / (((n : ℝ) + 1) - Q) ≤ 1 + Real.log hi := by
  by_cases hle : hi ≤ lo
  · rw [Finset.Ico_eq_empty (Nat.not_lt.mpr hle)]
    rcases Nat.eq_zero_or_pos hi with h0 | h1
    · subst h0; simp
    · have : (0 : ℝ) ≤ Real.log hi :=
        Real.log_nonneg (by exact_mod_cast h1)
      simp only [Finset.sum_empty]
      linarith
  · have hlt : lo < hi := Nat.lt_of_not_le hle
    have hterm : ∀ n ∈ Finset.Ico lo hi,
        1 / (((n : ℝ) + 1) - Q) ≤ 1 / (((n - lo : ℕ) : ℝ) + 1) := by
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hcast : ((n - lo : ℕ) : ℝ) = (n : ℝ) - (lo : ℝ) := by
        have := Nat.cast_sub hn'.1 (R := ℝ)
        rw [this]
      have hpos : (0 : ℝ) < ((n - lo : ℕ) : ℝ) + 1 := by positivity
      refine one_div_le_one_div_of_le hpos ?_
      rw [hcast]
      linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have hcnt : ∀ j ∈ Finset.range (hi - lo),
        1 / (((lo + j - lo : ℕ) : ℝ) + 1) = 1 / ((j : ℝ) + 1) := by
      intro j _
      have h1 : lo + j - lo = j := by omega
      rw [h1]
    rw [Finset.sum_congr rfl hcnt]
    refine le_trans (sum_range_inv_add_one_le (hi - lo)) ?_
    have hmono : Real.log ((hi - lo : ℕ) : ℝ) ≤ Real.log hi := by
      have h1 : 0 < hi - lo := by omega
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast h1
      · exact_mod_cast Nat.sub_le hi lo
    linarith

/-! ## Shared window geometry -/

private theorem sqrtT_le_self {T : ℝ} (hT : 16 ≤ T) : Real.sqrt T ≤ T := by
  have hT0 : (0 : ℝ) < T := by linarith
  nlinarith [Real.sq_sqrt hT0.le, Real.sqrt_nonneg T,
    Real.sqrt_le_sqrt (show (16 : ℝ) ≤ T from hT)]

private theorem sixteen_le_sqrtT {T : ℝ} (hT : 256 ≤ T) : 16 ≤ Real.sqrt T := by
  rw [show (16 : ℝ) = Real.sqrt 256 by
    rw [show (256 : ℝ) = 16 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hT

private theorem conductor_lower {T c : ℝ} (hT : 256 ≤ T) (hc : T ≤ c) (_hc2 : c ≤ 2 * T) :
    Real.sqrt T / 3 ≤ Real.sqrt (c / (2 * Real.pi)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have h2 : Real.sqrt (T / 9) = Real.sqrt T / 3 := by
    rw [Real.sqrt_div hT0.le, show Real.sqrt 9 = 3 by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
  have h1 : Real.sqrt (T / 9) ≤ Real.sqrt (c / (2 * Real.pi)) := by
    refine Real.sqrt_le_sqrt ?_
    have h3 : (2 : ℝ) * Real.pi ≤ 7 := by nlinarith [Real.pi_lt_d2]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith [h2 ▸ h1]

private theorem conductor_upper {T c : ℝ} (hT : 256 ≤ T) (hc : c ≤ 2 * T) (hc0 : T ≤ c) :
    Real.sqrt (c / (2 * Real.pi)) ≤ 3 / 5 * Real.sqrt T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hs2 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have h1 : c / (2 * Real.pi) ≤ (3 / 5 * Real.sqrt T) ^ (2 : ℕ) := by
    have h3 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h4 : c / (2 * Real.pi) ≤ c / 6 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) h3
    have h5 : (3 / 5 * Real.sqrt T) ^ (2 : ℕ) = 9 / 25 * T := by
      rw [mul_pow, sq (Real.sqrt T), hs2]
      ring
    rw [h5]
    nlinarith
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity)] at h2

private theorem cutoffWeight_le_of_uniform {x C₁ : ℝ} (hx0 : 0 < x)
    (hC₁ : ∀ {v : ℝ}, 0 < v → ‖smoothAFECutoff v‖ ≤ C₁) (n : ℕ) :
    cutoffWeight x n ≤ C₁ * (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
  unfold cutoffWeight
  rw [mul_comm C₁ _]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hC₁ (by positivity)

private theorem exp_taylor_upper {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    Real.exp δ ≤ 1 + 2 * δ := by
  have h1 : 1 - δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ)
    linarith
  have h2 : Real.exp δ * (1 - δ) ≤ 1 := by
    have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos δ))
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
  nlinarith [Real.exp_pos δ]

private theorem exp_neg_taylor_lower {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    Real.exp (-δ) ≤ 1 - δ / 2 := by
  have hkey : Real.exp (-δ) * (1 + δ) ≤ 1 := by
    have h2 := Real.add_one_le_exp δ
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos (-δ)))
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero, add_comm δ 1] at h3
  nlinarith [Real.exp_pos (-δ)]

/-! ## The three resonance classes -/

/-- **Low near-resonant class.**  Terms with `P/3 < m ≤ P·e^{-δ}` carry a first-derivative
test graded by the logarithmic distance to the resonance `P`; the harmonic telescope sums
them to `O(√√T·(1+log T))`. -/
private theorem sum_class_low_near {T a b x P δ C₁ : ℝ} {S : Finset ℕ} (hT : 256 ≤ T)
    (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T) (hx0 : 0 < x)
    (hC₁ : ∀ {v : ℝ}, 0 < v → ‖smoothAFECutoff v‖ ≤ C₁)
    (hP : P = Real.sqrt (a / (2 * Real.pi))) (hδ : δ = 8 / Real.sqrt T)
    (hmem : ∀ n ∈ S, P / 3 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 ≤ P * Real.exp (-δ)) :
    ∑ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 32 * C₁ * Real.sqrt (Real.sqrt T) * (1 + Real.log (Real.sqrt T)) := by
  classical
  have hT16 : (16 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hs16 : (16 : ℝ) ≤ Real.sqrt T := sixteen_le_sqrtT hT
  have hs0 : (0 : ℝ) < Real.sqrt T := by linarith
  have hδpos : (0 : ℝ) < δ := by rw [hδ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hs0 (by norm_num)]
    linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hP0 : (0 : ℝ) < P := by
    rw [hP]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hPle : P ≤ Real.sqrt T := by
    rw [hP]
    calc Real.sqrt (a / (2 * Real.pi)) ≤ 3 / 5 * Real.sqrt T :=
        conductor_upper hT (by linarith) ha
      _ ≤ Real.sqrt T := by nlinarith [Real.sqrt_nonneg T]
  have hPs3 : Real.sqrt T / 3 ≤ P := by
    rw [hP]; exact conductor_lower hT ha (by linarith)
  have hC₁0 : (0 : ℝ) ≤ C₁ := le_trans (norm_nonneg _) (hC₁ one_pos)
  have hlogPa : Real.log P = Real.log (a / (2 * Real.pi)) / 2 := by
    rw [hP]
    exact Real.log_sqrt (le_of_lt (div_pos (by linarith) (by positivity)))
  -- the resonance gap
  have hgap : P * Real.exp (-δ) ≤ P - 4 / 3 := by
    have h5 := exp_neg_taylor_lower hδpos hδhalf
    have h8 : 4 / 3 ≤ P * (δ / 2) := by
      have h9 : P * (δ / 2) = 4 * P / Real.sqrt T := by
        rw [hδ]; field_simp; ring
      rw [h9, le_div_iff₀ hs0]
      nlinarith [hPs3]
    nlinarith [hP0]
  set hi : ℕ := ⌊P * Real.exp (-δ)⌋₊ with hhidef
  have hhicast : (hi : ℝ) ≤ P * Real.exp (-δ) := Nat.floor_le (by positivity)
  have hhi1 : (hi : ℝ) ≤ P - 1 := by linarith [hgap]
  have hSsub : S ⊆ Finset.Ico 0 hi := by
    intro n hn
    rw [Finset.mem_Ico]
    refine ⟨Nat.zero_le n, ?_⟩
    have h1 := (hmem n hn).2
    have h2 : n + 1 ≤ hi := Nat.le_floor (by push_cast; linarith)
    omega
  -- the per-term graded bound
  have hterm : ∀ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 32 * C₁ * Real.sqrt P * (1 / (P - ((n : ℝ) + 1))) := by
    intro n hn
    obtain ⟨hlo, hhi'⟩ := hmem n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hlogm : Real.log ((n : ℝ) + 1) ≤ Real.log P - δ := by
      have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log (P * Real.exp (-δ)) :=
        Real.log_le_log hm0 hhi'
      rwa [Real.log_mul hP0.ne' (Real.exp_ne_zero _), Real.log_exp] at h1
    have hlamδ : δ ≤ Real.log P - Real.log ((n : ℝ) + 1) := by linarith
    have hlam0 : (0 : ℝ) < Real.log P - Real.log ((n : ℝ) + 1) :=
      lt_of_lt_of_le hδpos hlamδ
    have hlam4 : 4 / T ≤ Real.log P - Real.log ((n : ℝ) + 1) := by
      have h1 : 4 / T ≤ 8 / Real.sqrt T := by
        rw [div_le_div_iff₀ hT0 hs0]
        nlinarith [sqrtT_le_self hT16]
      rw [← hδ] at h1
      linarith
    have hL : Real.log ((n : ℝ) + 1) ≤ Real.log (a / (2 * Real.pi)) / 2
        - (Real.log P - Real.log ((n : ℝ) + 1)) := by
      rw [← hlogPa]
      linarith
    have hrate := rate_abs_lower_low hT16 ha hb hlam4 hL
    have hper := abs_integral_hardyDirectTerm_le_first_window_graded hT16 ha hb hab x n
      (by linarith : (0 : ℝ) < (Real.log P - Real.log ((n : ℝ) + 1)) / 2) hrate
    have hwn := cutoffWeight_le_of_uniform hx0 hC₁ n
    -- the amplitude bound
    have hsq3 : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 2 / Real.sqrt P := by
      have h1 : Real.sqrt (P / 3) ≤ Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_le_sqrt (le_of_lt hlo)
      have h2 : (0 : ℝ) < Real.sqrt (P / 3) := Real.sqrt_pos.mpr (by positivity)
      have h3 : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ (Real.sqrt (P / 3))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le h2 h1
      have h4 : (Real.sqrt (P / 3))⁻¹ = Real.sqrt 3 / Real.sqrt P := by
        rw [Real.sqrt_div hP0.le, inv_div]
      have h5 : Real.sqrt 3 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have h6 : Real.sqrt 3 / Real.sqrt P ≤ 2 / Real.sqrt P :=
        div_le_div_of_nonneg_right h5 (Real.sqrt_pos.mpr hP0).le
      linarith [h3, h4.le, h4.ge]
    -- the rate lower bound in linear form
    have hPm : (0 : ℝ) < P - ((n : ℝ) + 1) := by linarith [hgap, hhi']
    have hlamlow : (P - ((n : ℝ) + 1)) / P ≤ Real.log P - Real.log ((n : ℝ) + 1) := by
      have h1 : Real.log (((n : ℝ) + 1) / P) ≤ ((n : ℝ) + 1) / P - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (((n : ℝ) + 1) / P) = Real.log ((n : ℝ) + 1) - Real.log P :=
        Real.log_div hm0.ne' hP0.ne'
      rw [h2] at h1
      have h3 : (P - ((n : ℝ) + 1)) / P = 1 - ((n : ℝ) + 1) / P := by
        field_simp
      rw [h3]
      linarith
    have hinvlam : 1 / (Real.log P - Real.log ((n : ℝ) + 1)) ≤ P / (P - ((n : ℝ) + 1)) := by
      have h2 : (0 : ℝ) < (P - ((n : ℝ) + 1)) / P := by positivity
      have h3 := one_div_le_one_div_of_le h2 hlamlow
      rwa [one_div_div] at h3
    have hsP0 : (0 : ℝ) < Real.sqrt P := Real.sqrt_pos.mpr hP0
    calc |∫ τ in a..b, hardyDirectTerm x n τ|
        ≤ 8 * cutoffWeight x n / ((Real.log P - Real.log ((n : ℝ) + 1)) / 2) := hper
      _ = 16 * cutoffWeight x n * (1 / (Real.log P - Real.log ((n : ℝ) + 1))) := by
          field_simp
          ring
      _ ≤ 16 * (C₁ * (2 / Real.sqrt P)) * (P / (P - ((n : ℝ) + 1))) := by
          refine mul_le_mul ?_ hinvlam (by positivity) ?_
          · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            calc cutoffWeight x n ≤ C₁ * (Real.sqrt ((n : ℝ) + 1))⁻¹ := hwn
              _ ≤ C₁ * (2 / Real.sqrt P) := mul_le_mul_of_nonneg_left hsq3 hC₁0
          · positivity
      _ = 32 * C₁ * (P / Real.sqrt P) * (1 / (P - ((n : ℝ) + 1))) := by
          field_simp
          ring
      _ = 32 * C₁ * Real.sqrt P * (1 / (P - ((n : ℝ) + 1))) := by
          rw [Real.div_sqrt]
  -- sum it with the harmonic telescope
  have hnn : ∀ n ∈ Finset.Ico 0 hi, n ∉ S →
      (0 : ℝ) ≤ 32 * C₁ * Real.sqrt P * (1 / (P - ((n : ℝ) + 1))) := by
    intro n hn _
    have h1 := (Finset.mem_Ico.mp hn).2
    have h2 : ((n : ℝ) + 1) ≤ (hi : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) < P - ((n : ℝ) + 1) := by linarith [hhi1]
    positivity
  have hsum := sum_Ico_inv_sub_le (P := P) 0 hi hhi1
  have hlogs : Real.log (hi : ℝ) ≤ Real.log (Real.sqrt T) := by
    by_cases h0 : hi = 0
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · refine Real.log_le_log ?_ ?_
      · exact_mod_cast Nat.pos_of_ne_zero h0
      · calc (hi : ℝ) ≤ P - 1 := hhi1
          _ ≤ Real.sqrt T := by linarith [hPle]
  have hsP0 : (0 : ℝ) ≤ Real.sqrt P := Real.sqrt_nonneg P
  have hsPle : Real.sqrt P ≤ Real.sqrt (Real.sqrt T) := Real.sqrt_le_sqrt hPle
  have hlog1 : (0 : ℝ) ≤ 1 + Real.log (Real.sqrt T) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Real.sqrt T)
    linarith
  calc ∑ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ ∑ n ∈ S, 32 * C₁ * Real.sqrt P * (1 / (P - ((n : ℝ) + 1))) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Ico 0 hi, 32 * C₁ * Real.sqrt P * (1 / (P - ((n : ℝ) + 1))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub hnn
    _ = 32 * C₁ * Real.sqrt P * ∑ n ∈ Finset.Ico 0 hi, 1 / (P - ((n : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ 32 * C₁ * Real.sqrt P * (1 + Real.log (hi : ℝ)) := by
        refine mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 32 * C₁ * Real.sqrt (Real.sqrt T) * (1 + Real.log (Real.sqrt T)) := by
        have h1 : 32 * C₁ * Real.sqrt P ≤ 32 * C₁ * Real.sqrt (Real.sqrt T) := by
          refine mul_le_mul_of_nonneg_left hsPle (by positivity)
        have h2 : (1 : ℝ) + Real.log (hi : ℝ) ≤ 1 + Real.log (Real.sqrt T) := by
          linarith
        have h3 : (0 : ℝ) ≤ 1 + Real.log (hi : ℝ) := by
          by_cases h0 : hi = 0
          · rw [h0]; simp
          · have h4 : (1 : ℝ) ≤ (hi : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero h0
            have := Real.log_nonneg h4
            linarith
        have h5 : (0 : ℝ) ≤ 32 * C₁ * Real.sqrt (Real.sqrt T) :=
          mul_nonneg (mul_nonneg (by norm_num) hC₁0) (Real.sqrt_nonneg _)
        exact mul_le_mul h1 h2 h3 h5

/-- **High near-resonant class.**  Terms with `Q·e^{δ} ≤ m < 3Q` are graded by the distance
above the resonance `Q` and sum by the harmonic telescope to `O(√√T·(1+log T))`. -/
private theorem sum_class_high_near {T a b x Q δ C₁ : ℝ} {M : ℕ} {S : Finset ℕ}
    (hT : 256 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T) (hx0 : 0 < x)
    (hC₁ : ∀ {v : ℝ}, 0 < v → ‖smoothAFECutoff v‖ ≤ C₁)
    (hQ : Q = Real.sqrt (b / (2 * Real.pi))) (hδ : δ = 8 / Real.sqrt T)
    (hM : (M : ℝ) ≤ 6 * Real.sqrt T)
    (hmem : ∀ n ∈ S, Q * Real.exp δ ≤ (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * Q)
    (hmemM : ∀ n ∈ S, n < M) :
    ∑ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 48 * C₁ * Real.sqrt (Real.sqrt T) * (3 + Real.log (Real.sqrt T)) := by
  classical
  have hT16 : (16 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hs16 : (16 : ℝ) ≤ Real.sqrt T := sixteen_le_sqrtT hT
  have hs0 : (0 : ℝ) < Real.sqrt T := by linarith
  have hδpos : (0 : ℝ) < δ := by rw [hδ]; positivity
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQ]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hQle : Q ≤ Real.sqrt T := by
    rw [hQ]
    calc Real.sqrt (b / (2 * Real.pi)) ≤ 3 / 5 * Real.sqrt T :=
        conductor_upper hT hb (by linarith)
      _ ≤ Real.sqrt T := by nlinarith [Real.sqrt_nonneg T]
  have hQs3 : Real.sqrt T / 3 ≤ Q := by
    rw [hQ]; exact conductor_lower hT (by linarith) hb
  have hC₁0 : (0 : ℝ) ≤ C₁ := le_trans (norm_nonneg _) (hC₁ one_pos)
  have hlogQb : Real.log Q = Real.log (b / (2 * Real.pi)) / 2 := by
    rw [hQ]
    exact Real.log_sqrt (le_of_lt (div_pos (by linarith) (by positivity)))
  -- the resonance gap on the high side
  have hgap : Q + 2 ≤ Q * Real.exp δ := by
    have h1 : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
    have h2 : Q * (1 + δ) ≤ Q * Real.exp δ := mul_le_mul_of_nonneg_left h1 hQ0.le
    have h3 : (2 : ℝ) ≤ Q * δ := by
      have h4 : Q * δ = 8 * Q / Real.sqrt T := by rw [hδ]; field_simp
      rw [h4, le_div_iff₀ hs0]
      nlinarith [hQs3]
    nlinarith [hQ0]
  set lo : ℕ := ⌈Q * Real.exp δ⌉₊ - 1 with hlodef
  have hceil1 : 1 ≤ ⌈Q * Real.exp δ⌉₊ := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
    positivity
  have hlocast : Q + 1 ≤ (lo : ℝ) := by
    have h1 : Q * Real.exp δ ≤ (⌈Q * Real.exp δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((lo : ℕ) : ℝ) = (⌈Q * Real.exp δ⌉₊ : ℝ) - 1 := by
      rw [hlodef, Nat.cast_sub hceil1, Nat.cast_one]
    rw [h2]
    linarith [hgap]
  have hSsub : S ⊆ Finset.Ico lo M := by
    intro n hn
    rw [Finset.mem_Ico]
    refine ⟨?_, hmemM n hn⟩
    have h1 := (hmem n hn).1
    have h2 : ⌈Q * Real.exp δ⌉₊ ≤ n + 1 := Nat.ceil_le.mpr (by push_cast; linarith)
    omega
  -- per-term bound
  have hterm : ∀ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 48 * C₁ * Real.sqrt Q * (1 / (((n : ℝ) + 1) - Q)) := by
    intro n hn
    obtain ⟨hlo', hhi'⟩ := hmem n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hmQ : Q ≤ (n : ℝ) + 1 := by
      have h1 : Q ≤ Q * Real.exp δ := by
        nlinarith [Real.add_one_le_exp δ, hQ0]
      linarith
    have hlogm : Real.log Q + δ ≤ Real.log ((n : ℝ) + 1) := by
      have h1 : Real.log (Q * Real.exp δ) ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by positivity) hlo'
      rwa [Real.log_mul hQ0.ne' (Real.exp_ne_zero _), Real.log_exp] at h1
    have hlamδ : δ ≤ Real.log ((n : ℝ) + 1) - Real.log Q := by linarith
    have hlam0 : (0 : ℝ) < Real.log ((n : ℝ) + 1) - Real.log Q :=
      lt_of_lt_of_le hδpos hlamδ
    have hlam4 : 4 / T ≤ Real.log ((n : ℝ) + 1) - Real.log Q := by
      have h1 : 4 / T ≤ 8 / Real.sqrt T := by
        rw [div_le_div_iff₀ hT0 hs0]
        nlinarith [sqrtT_le_self hT16]
      rw [← hδ] at h1
      linarith
    have hL : Real.log (b / (2 * Real.pi)) / 2
        + (Real.log ((n : ℝ) + 1) - Real.log Q) ≤ Real.log ((n : ℝ) + 1) := by
      rw [← hlogQb]
      linarith
    have hrate := rate_abs_lower_high hT16 ha hb hlam4 hL
    have hper := abs_integral_hardyDirectTerm_le_first_window_graded hT16 ha hb hab x n
      (by linarith : (0 : ℝ) < (Real.log ((n : ℝ) + 1) - Real.log Q) / 2) hrate
    have hwn := cutoffWeight_le_of_uniform hx0 hC₁ n
    have hsqm : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 1 / Real.sqrt Q := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hQ0)
        (Real.sqrt_le_sqrt hmQ)
    -- linear lower bound for the log gap
    have hmQ0 : (0 : ℝ) < ((n : ℝ) + 1) - Q := by linarith [hlocast, hgap, hlo']
    have hlamlow : (((n : ℝ) + 1) - Q) / (3 * Q)
        ≤ Real.log ((n : ℝ) + 1) - Real.log Q := by
      have h1 : Real.log (Q / ((n : ℝ) + 1)) ≤ Q / ((n : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (Q / ((n : ℝ) + 1)) = Real.log Q - Real.log ((n : ℝ) + 1) :=
        Real.log_div hQ0.ne' hm0.ne'
      rw [h2] at h1
      have h3 : 1 - Q / ((n : ℝ) + 1) = (((n : ℝ) + 1) - Q) / ((n : ℝ) + 1) := by
        field_simp
      have h4 : (((n : ℝ) + 1) - Q) / (3 * Q) ≤ (((n : ℝ) + 1) - Q) / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_left (le_of_lt hmQ0) hm0 (le_of_lt hhi')
      linarith [h3.le, h3.ge]
    have hinvlam : 1 / (Real.log ((n : ℝ) + 1) - Real.log Q)
        ≤ 3 * Q / (((n : ℝ) + 1) - Q) := by
      have h2 : (0 : ℝ) < (((n : ℝ) + 1) - Q) / (3 * Q) := by positivity
      have h3 := one_div_le_one_div_of_le h2 hlamlow
      rwa [one_div_div] at h3
    calc |∫ τ in a..b, hardyDirectTerm x n τ|
        ≤ 8 * cutoffWeight x n / ((Real.log ((n : ℝ) + 1) - Real.log Q) / 2) := hper
      _ = 16 * cutoffWeight x n * (1 / (Real.log ((n : ℝ) + 1) - Real.log Q)) := by
          field_simp
          ring
      _ ≤ 16 * (C₁ * (1 / Real.sqrt Q)) * (3 * Q / (((n : ℝ) + 1) - Q)) := by
          refine mul_le_mul ?_ hinvlam (by positivity) ?_
          · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            calc cutoffWeight x n ≤ C₁ * (Real.sqrt ((n : ℝ) + 1))⁻¹ := hwn
              _ ≤ C₁ * (1 / Real.sqrt Q) := mul_le_mul_of_nonneg_left hsqm hC₁0
          · have : (0 : ℝ) < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
            positivity
      _ = 48 * C₁ * (Q / Real.sqrt Q) * (1 / (((n : ℝ) + 1) - Q)) := by
          field_simp
          ring
      _ = 48 * C₁ * Real.sqrt Q * (1 / (((n : ℝ) + 1) - Q)) := by
          rw [Real.div_sqrt]
  -- sum with the harmonic telescope
  have hnn : ∀ n ∈ Finset.Ico lo M, n ∉ S →
      (0 : ℝ) ≤ 48 * C₁ * Real.sqrt Q * (1 / (((n : ℝ) + 1) - Q)) := by
    intro n hn _
    have h1 := (Finset.mem_Ico.mp hn).1
    have h2 : (lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) < ((n : ℝ) + 1) - Q := by linarith [hlocast]
    have h4 : (0 : ℝ) ≤ Real.sqrt Q := Real.sqrt_nonneg Q
    positivity
  have hsum := sum_Ico_inv_sub_le' (Q := Q) lo M (by linarith [hlocast])
  have hlogM : Real.log (M : ℝ) ≤ 2 + Real.log (Real.sqrt T) := by
    by_cases h0 : M = 0
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Real.sqrt T)
      linarith
    · have h1 : Real.log (M : ℝ) ≤ Real.log (6 * Real.sqrt T) := by
        refine Real.log_le_log ?_ hM
        exact_mod_cast Nat.pos_of_ne_zero h0
      have h2 : Real.log (6 * Real.sqrt T) = Real.log 6 + Real.log (Real.sqrt T) :=
        Real.log_mul (by norm_num) (by linarith)
      have h3 : Real.log 6 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h4 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_gt_d9]
      linarith
  have hsQle : Real.sqrt Q ≤ Real.sqrt (Real.sqrt T) := Real.sqrt_le_sqrt hQle
  calc ∑ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ ∑ n ∈ S, 48 * C₁ * Real.sqrt Q * (1 / (((n : ℝ) + 1) - Q)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Ico lo M, 48 * C₁ * Real.sqrt Q * (1 / (((n : ℝ) + 1) - Q)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub hnn
    _ = 48 * C₁ * Real.sqrt Q * ∑ n ∈ Finset.Ico lo M, 1 / (((n : ℝ) + 1) - Q) := by
        rw [Finset.mul_sum]
    _ ≤ 48 * C₁ * Real.sqrt Q * (1 + Real.log (M : ℝ)) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        exact mul_nonneg (mul_nonneg (by norm_num) hC₁0) (Real.sqrt_nonneg Q)
    _ ≤ 48 * C₁ * Real.sqrt (Real.sqrt T) * (3 + Real.log (Real.sqrt T)) := by
        have h1 : 48 * C₁ * Real.sqrt Q ≤ 48 * C₁ * Real.sqrt (Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hsQle (mul_nonneg (by norm_num) hC₁0)
        have h2 : (1 : ℝ) + Real.log (M : ℝ) ≤ 3 + Real.log (Real.sqrt T) := by
          linarith [hlogM]
        have h3 : (0 : ℝ) ≤ 1 + Real.log (M : ℝ) := by
          by_cases h0 : M = 0
          · rw [h0]; simp
          · have h4 : (1 : ℝ) ≤ (M : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero h0
            linarith [Real.log_nonneg h4]
        have h5 : (0 : ℝ) ≤ 48 * C₁ * Real.sqrt (Real.sqrt T) :=
          mul_nonneg (mul_nonneg (by norm_num) hC₁0) (Real.sqrt_nonneg _)
        exact mul_le_mul h1 h2 h3 h5

private theorem cross_band_card_le {T a b P Q δ : ℝ} {S : Finset ℕ}
    (hT : 256 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T)
    (hP : P = Real.sqrt (a / (2 * Real.pi))) (hQ : Q = Real.sqrt (b / (2 * Real.pi)))
    (hδ : δ = 8 / Real.sqrt T)
    (hmem : ∀ n ∈ S, P * Real.exp (-δ) < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < Q * Real.exp δ) :
    (S.card : ℝ) ≤ (b - a) / (4 * Real.sqrt T) + 18 := by
  classical
  have hT0 : (0 : ℝ) < T := by linarith
  have hs16 : (16 : ℝ) ≤ Real.sqrt T := sixteen_le_sqrtT hT
  have hs0 : (0 : ℝ) < Real.sqrt T := by linarith
  have hδpos : (0 : ℝ) < δ := by rw [hδ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hs0 (by norm_num)]
    linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hP0 : (0 : ℝ) < P := by
    rw [hP]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQ]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hPQ : P ≤ Q := by
    rw [hP, hQ]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hab (by positivity))
  have hPs3 : Real.sqrt T / 3 ≤ P := by
    rw [hP]; exact conductor_lower hT ha (by linarith)
  have hQ35 : Q ≤ 3 / 5 * Real.sqrt T := by
    rw [hQ]; exact conductor_upper hT hb (by linarith)
  set lo : ℕ := ⌊P * Real.exp (-δ)⌋₊ with hlodef
  set hi : ℕ := ⌈Q * Real.exp δ⌉₊ with hhidef
  have hSsub : S ⊆ Finset.Ico lo hi := by
    intro n hn
    obtain ⟨h1, h2⟩ := hmem n hn
    rw [Finset.mem_Ico]
    constructor
    · have h3 : lo < n + 1 := by
        rw [hlodef]
        rw [Nat.floor_lt (by positivity)]
        push_cast
        linarith
      omega
    · have h4 : n + 1 < hi := by
        rw [hhidef]
        rw [Nat.lt_ceil]
        push_cast
        linarith
      omega
  have h5 : S.card ≤ hi - lo := by
    calc S.card ≤ (Finset.Ico lo hi).card := Finset.card_le_card hSsub
      _ = hi - lo := Nat.card_Ico lo hi
  -- real bound for hi − lo
  have hQP : Q - P ≤ (b - a) / (4 * Real.sqrt T) := by
    have h6 : (Q - P) * (2 * Real.pi * (Q + P)) = b - a := by
      have h7 : Q * Q = b / (2 * Real.pi) := by
        rw [hQ]; exact Real.mul_self_sqrt (le_of_lt (div_pos (by linarith) (by positivity)))
      have h8 : P * P = a / (2 * Real.pi) := by
        rw [hP]; exact Real.mul_self_sqrt (le_of_lt (div_pos (by linarith) (by positivity)))
      have h9 : (Q - P) * (Q + P) = Q * Q - P * P := by ring
      have h10 : Q * Q - P * P = (b - a) / (2 * Real.pi) := by
        rw [h7, h8]; ring
      calc (Q - P) * (2 * Real.pi * (Q + P))
          = 2 * Real.pi * ((Q - P) * (Q + P)) := by ring
        _ = 2 * Real.pi * ((b - a) / (2 * Real.pi)) := by rw [h9, h10]
        _ = b - a := by field_simp
    have h11 : 4 * Real.sqrt T ≤ 2 * Real.pi * (Q + P) := by
      have h12 : Real.sqrt T / 3 + Real.sqrt T / 3 ≤ Q + P := by
        have h13 : Real.sqrt T / 3 ≤ Q := le_trans hPs3 hPQ
        linarith [hPs3]
      nlinarith [Real.pi_gt_three, hs0]
    have h14 : (0 : ℝ) ≤ Q - P := by linarith
    have h15 := mul_le_mul_of_nonneg_left h11 h14
    rw [h6] at h15
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h16 : (hi : ℝ) ≤ Q * Real.exp δ + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Q * Real.exp δ)
    rw [hhidef]
    linarith
  have h17 : P * Real.exp (-δ) - 1 ≤ (lo : ℝ) := by
    have := Nat.lt_floor_add_one (P * Real.exp (-δ))
    rw [hlodef]
    linarith
  have h18 : Q * Real.exp δ ≤ Q + 2 * (Q * δ) := by
    have h19 := mul_le_mul_of_nonneg_left (exp_taylor_upper hδpos hδhalf) hQ0.le
    calc Q * Real.exp δ ≤ Q * (1 + 2 * δ) := h19
      _ = Q + 2 * (Q * δ) := by ring
  have h20 : P - P * δ ≤ P * Real.exp (-δ) := by
    have h21 : (1 : ℝ) - δ ≤ Real.exp (-δ) := by
      linarith only [Real.add_one_le_exp (-δ)]
    have h22' := mul_le_mul_of_nonneg_left h21 hP0.le
    calc P - P * δ = P * (1 - δ) := by ring
      _ ≤ P * Real.exp (-δ) := h22'
  have h22 : Q * δ ≤ 24 / 5 := by
    have h23 : Q * δ = 8 * Q / Real.sqrt T := by rw [hδ]; field_simp
    rw [h23, div_le_iff₀ hs0]
    have h26' := mul_le_mul_of_nonneg_left hQ35 (by norm_num : (0:ℝ) ≤ 8)
    calc 8 * Q ≤ 8 * (3 / 5 * Real.sqrt T) := h26'
      _ = 24 / 5 * Real.sqrt T := by ring
  have h24 : P * δ ≤ 24 / 5 := by
    have h25 : P * δ = 8 * P / Real.sqrt T := by rw [hδ]; field_simp
    rw [h25, div_le_iff₀ hs0]
    have h27' := mul_le_mul_of_nonneg_left (le_trans hPQ hQ35)
      (by norm_num : (0:ℝ) ≤ 8)
    calc 8 * P ≤ 8 * (3 / 5 * Real.sqrt T) := h27'
      _ = 24 / 5 * Real.sqrt T := by ring
  -- assemble the cast bound
  by_cases hcase : hi ≤ lo
  · have h26 : S.card = 0 := by
      have h27 : Finset.Ico lo hi = ∅ := Finset.Ico_eq_empty (Nat.not_lt.mpr hcase)
      have h28 := Finset.card_le_card hSsub
      rw [h27] at h28
      simpa using h28
    rw [h26]
    have h29 : (0 : ℝ) ≤ (b - a) / (4 * Real.sqrt T) := by positivity
    push_cast
    linarith
  · have h30 : ((hi - lo : ℕ) : ℝ) = (hi : ℝ) - (lo : ℝ) :=
      Nat.cast_sub (le_of_lt (Nat.lt_of_not_le hcase))
    have h31 : (S.card : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := by exact_mod_cast h5
    rw [h30] at h31
    have h32 : (hi : ℝ) - (lo : ℝ)
        ≤ (Q - P) + 2 * (Q * δ) + P * δ + 2 := by linarith [h16, h17, h18, h20]
    linarith [hQP, h22, h24]

/-- **Crossing class.**  The `O((b-a)/√T + 1)` terms whose resonance crosses the window are
second-derivative tested at `O(T^{1/4})` each. -/
private theorem sum_class_cross {T a b x P Q δ C₁ : ℝ} {S : Finset ℕ}
    (hT : 256 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T) (hx0 : 0 < x)
    (hC₁ : ∀ {v : ℝ}, 0 < v → ‖smoothAFECutoff v‖ ≤ C₁)
    (hP : P = Real.sqrt (a / (2 * Real.pi))) (hQ : Q = Real.sqrt (b / (2 * Real.pi)))
    (hδ : δ = 8 / Real.sqrt T)
    (hmem : ∀ n ∈ S, P * Real.exp (-δ) < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < Q * Real.exp δ) :
    ∑ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 384 * Real.sqrt 200 * C₁
        * ((b - a) / Real.sqrt (Real.sqrt T) + 18 * Real.sqrt (Real.sqrt T)) := by
  classical
  have hT16 : (16 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hs16 : (16 : ℝ) ≤ Real.sqrt T := sixteen_le_sqrtT hT
  have hs0 : (0 : ℝ) < Real.sqrt T := by linarith
  have hs2 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have hδpos : (0 : ℝ) < δ := by rw [hδ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hs0 (by norm_num)]
    linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hP0 : (0 : ℝ) < P := by
    rw [hP]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQ]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hPQ : P ≤ Q := by
    rw [hP, hQ]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hab (by positivity))
  have hPs3 : Real.sqrt T / 3 ≤ P := by
    rw [hP]; exact conductor_lower hT ha (by linarith)
  have hQ35 : Q ≤ 3 / 5 * Real.sqrt T := by
    rw [hQ]; exact conductor_upper hT hb (by linarith)
  have hC₁0 : (0 : ℝ) ≤ C₁ := le_trans (norm_nonneg _) (hC₁ one_pos)
  have hs200 : (0 : ℝ) ≤ Real.sqrt 200 := Real.sqrt_nonneg _
  -- per-term second-derivative bound with amplitude control
  have hterm : ∀ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 192 * Real.sqrt 200 * C₁ * Real.sqrt (Real.sqrt T) := by
    intro n hn
    obtain ⟨hlo', _⟩ := hmem n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 := abs_integral_hardyDirectTerm_le_second_window (by linarith) ha hb hab x n
    -- amplitude: m > P e^{-δ} ≥ P/2 ≥ √T/6
    have hm6 : Real.sqrt T / 6 ≤ (n : ℝ) + 1 := by
      have h2 : P / 2 ≤ P * Real.exp (-δ) := by
        have h3 : (1 : ℝ) / 2 ≤ Real.exp (-δ) := by
          have h4 : Real.exp (-δ) ≥ 1 - δ := by linarith [Real.add_one_le_exp (-δ)]
          linarith
        nlinarith [hP0]
      linarith [hlo', hPs3]
    have hwn := cutoffWeight_le_of_uniform hx0 hC₁ n
    have hsqm : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 3 / Real.sqrt (Real.sqrt T) := by
      have h2 : Real.sqrt (Real.sqrt T / 6) ≤ Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_le_sqrt hm6
      have h3 : (0 : ℝ) < Real.sqrt (Real.sqrt T / 6) :=
        Real.sqrt_pos.mpr (by positivity)
      have h4 : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ (Real.sqrt (Real.sqrt T / 6))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le h3 h2
      have h5 : (Real.sqrt (Real.sqrt T / 6))⁻¹ = Real.sqrt 6 / Real.sqrt (Real.sqrt T) := by
        rw [Real.sqrt_div (Real.sqrt_nonneg T), inv_div]
      have h6 : Real.sqrt 6 ≤ 3 := by
        rw [show (3 : ℝ) = Real.sqrt 9 by
          rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have h7 : Real.sqrt 6 / Real.sqrt (Real.sqrt T) ≤ 3 / Real.sqrt (Real.sqrt T) :=
        div_le_div_of_nonneg_right h6 (Real.sqrt_pos.mpr hs0).le
      linarith [h4, h5.le, h5.ge]
    -- √(200T) = √200·√T and √T/√√T = √√T
    have hsqrt200T : Real.sqrt (200 * T) = Real.sqrt 200 * Real.sqrt T :=
      Real.sqrt_mul (by norm_num) T
    have hssT : Real.sqrt T / Real.sqrt (Real.sqrt T) = Real.sqrt (Real.sqrt T) :=
      Real.div_sqrt
    calc |∫ τ in a..b, hardyDirectTerm x n τ|
        ≤ 64 * Real.sqrt (200 * T) * cutoffWeight x n := h1
      _ ≤ 64 * Real.sqrt (200 * T) * (C₁ * (3 / Real.sqrt (Real.sqrt T))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc cutoffWeight x n ≤ C₁ * (Real.sqrt ((n : ℝ) + 1))⁻¹ := hwn
            _ ≤ C₁ * (3 / Real.sqrt (Real.sqrt T)) :=
                mul_le_mul_of_nonneg_left hsqm hC₁0
      _ = 192 * Real.sqrt 200 * C₁ * (Real.sqrt T / Real.sqrt (Real.sqrt T)) := by
          rw [hsqrt200T]
          ring
      _ = 192 * Real.sqrt 200 * C₁ * Real.sqrt (Real.sqrt T) := by
          rw [hssT]
  -- the crossing count
  have hcard : (S.card : ℝ) ≤ (b - a) / (4 * Real.sqrt T) + 18 :=
    cross_band_card_le hT ha hab hb hP hQ hδ hmem
  -- combine
  have hB0 : (0 : ℝ) ≤ 192 * Real.sqrt 200 * C₁ * Real.sqrt (Real.sqrt T) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 192) hs200) hC₁0)
      (Real.sqrt_nonneg (Real.sqrt T))
    linarith
  have hsum := Finset.sum_le_card_nsmul S _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hss4 : Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt T) = Real.sqrt T :=
    Real.mul_self_sqrt hs0.le
  calc ∑ n ∈ S, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ (S.card : ℝ) * (192 * Real.sqrt 200 * C₁ * Real.sqrt (Real.sqrt T)) := hsum
    _ ≤ ((b - a) / (4 * Real.sqrt T) + 18)
          * (192 * Real.sqrt 200 * C₁ * Real.sqrt (Real.sqrt T)) :=
        mul_le_mul_of_nonneg_right hcard hB0
    _ ≤ 384 * Real.sqrt 200 * C₁
          * ((b - a) / Real.sqrt (Real.sqrt T) + 18 * Real.sqrt (Real.sqrt T)) := by
        have hba : (0 : ℝ) ≤ b - a := by linarith
        have hs40 : (0 : ℝ) < Real.sqrt (Real.sqrt T) := Real.sqrt_pos.mpr hs0
        have hkey : (b - a) / (4 * Real.sqrt T) * Real.sqrt (Real.sqrt T)
            ≤ (b - a) / Real.sqrt (Real.sqrt T) := by
          have h1 : (b - a) / (4 * Real.sqrt T) * Real.sqrt (Real.sqrt T)
              = (b - a) * (Real.sqrt (Real.sqrt T) / (4 * Real.sqrt T)) := by ring
          have h2 : (b - a) / Real.sqrt (Real.sqrt T)
              = (b - a) * (1 / Real.sqrt (Real.sqrt T)) := by ring
          rw [h1, h2]
          refine mul_le_mul_of_nonneg_left ?_ hba
          rw [div_le_div_iff₀ (by positivity) hs40, hss4]
          linarith [hs0]
        have hexp : ((b - a) / (4 * Real.sqrt T) + 18)
              * (192 * Real.sqrt 200 * C₁ * Real.sqrt (Real.sqrt T))
            = 192 * Real.sqrt 200 * C₁
              * ((b - a) / (4 * Real.sqrt T) * Real.sqrt (Real.sqrt T)
                + 18 * Real.sqrt (Real.sqrt T)) := by ring
        rw [hexp]
        have hc0 : (0 : ℝ) ≤ 192 * Real.sqrt 200 * C₁ :=
          mul_nonneg (mul_nonneg (by norm_num) hs200) hC₁0
        have hinner : (b - a) / (4 * Real.sqrt T) * Real.sqrt (Real.sqrt T)
              + 18 * Real.sqrt (Real.sqrt T)
            ≤ (b - a) / Real.sqrt (Real.sqrt T) + 18 * Real.sqrt (Real.sqrt T) := by
          linarith [hkey]
        calc 192 * Real.sqrt 200 * C₁
              * ((b - a) / (4 * Real.sqrt T) * Real.sqrt (Real.sqrt T)
                + 18 * Real.sqrt (Real.sqrt T))
            ≤ 192 * Real.sqrt 200 * C₁
              * ((b - a) / Real.sqrt (Real.sqrt T) + 18 * Real.sqrt (Real.sqrt T)) :=
              mul_le_mul_of_nonneg_left hinner hc0
          _ ≤ 384 * Real.sqrt 200 * C₁
              * ((b - a) / Real.sqrt (Real.sqrt T) + 18 * Real.sqrt (Real.sqrt T)) := by
              have hpos : (0 : ℝ) ≤ (b - a) / Real.sqrt (Real.sqrt T)
                  + 18 * Real.sqrt (Real.sqrt T) := by positivity
              nlinarith [hc0, hpos, hs200, hC₁0]

/-! ## The far classes -/

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  exact Real.log_le_log (Real.exp_pos 1) (by nlinarith [Real.exp_one_lt_d9])

private theorem term_low_far {T a b x P : ℝ} (hT : 256 ≤ T) (ha : T ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * T) (hP : P = Real.sqrt (a / (2 * Real.pi))) (n : ℕ)
    (hn : (n : ℝ) + 1 ≤ P / 3) :
    |∫ τ in a..b, hardyDirectTerm x n τ| ≤ 16 * cutoffWeight x n := by
  have hT16 : (16 : ℝ) ≤ T := by linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hP0 : (0 : ℝ) < P := by
    rw [hP]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hlogPa : Real.log P = Real.log (a / (2 * Real.pi)) / 2 := by
    rw [hP]
    exact Real.log_sqrt (le_of_lt (div_pos (by linarith) (by positivity)))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hL : Real.log ((n : ℝ) + 1) ≤ Real.log (a / (2 * Real.pi)) / 2 - 1 := by
    have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log (P / 3) := Real.log_le_log hm0 hn
    have h2 : Real.log (P / 3) = Real.log P - Real.log 3 :=
      Real.log_div hP0.ne' (by norm_num)
    rw [← hlogPa]
    linarith [one_le_log_three]
  have hrate := rate_abs_lower_low hT16 ha hb
    (by rw [div_le_one (by linarith : (0:ℝ) < T)]; linarith : 4 / T ≤ 1) hL
  have hper := abs_integral_hardyDirectTerm_le_first_window_graded hT16 ha hb hab x n
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hrate
  calc |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 8 * cutoffWeight x n / ((1 : ℝ) / 2) := hper
    _ = 16 * cutoffWeight x n := by ring

private theorem term_high_far {T a b x Q : ℝ} (hT : 256 ≤ T) (ha : T ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * T) (hQ : Q = Real.sqrt (b / (2 * Real.pi))) (n : ℕ)
    (hn : 3 * Q ≤ (n : ℝ) + 1) :
    |∫ τ in a..b, hardyDirectTerm x n τ| ≤ 16 * cutoffWeight x n := by
  have hT16 : (16 : ℝ) ≤ T := by linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQ]
    exact Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hlogQb : Real.log Q = Real.log (b / (2 * Real.pi)) / 2 := by
    rw [hQ]
    exact Real.log_sqrt (le_of_lt (div_pos (by linarith) (by positivity)))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hL : Real.log (b / (2 * Real.pi)) / 2 + 1 ≤ Real.log ((n : ℝ) + 1) := by
    have h1 : Real.log (3 * Q) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) hn
    have h2 : Real.log (3 * Q) = Real.log 3 + Real.log Q :=
      Real.log_mul (by norm_num) hQ0.ne'
    rw [← hlogQb]
    linarith [one_le_log_three]
  have hrate := rate_abs_lower_high hT16 ha hb
    (by rw [div_le_one (by linarith : (0:ℝ) < T)]; linarith : 4 / T ≤ 1) hL
  have hper := abs_integral_hardyDirectTerm_le_first_window_graded hT16 ha hb hab x n
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hrate
  calc |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 8 * cutoffWeight x n / ((1 : ℝ) / 2) := hper
    _ = 16 * cutoffWeight x n := by ring

/-! ## The sharp direct-series window bound -/

/-- **The direct edge over a subwindow, resonance-graded.**  For every cutoff `x ≥ 1` and
window `[a,b] ⊆ [T,2T]`, `|∫_a^b Σ_direct| ≤ C(√√T(1+log T) + (b-a)/√√T + √x)`. -/
theorem exists_abs_integral_hardyDirectSeries_window_sharp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T a b x : ℝ}, 256 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T → 1 ≤ x →
      |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
        ≤ C * (Real.sqrt (Real.sqrt T) * (1 + Real.log T)
            + (b - a) / Real.sqrt (Real.sqrt T) + Real.sqrt x) := by
  classical
  obtain ⟨Ct, hCt, hmain⟩ := exists_summable_tsum_cutoffWeight_le
  obtain ⟨Ch, hCh, hhead⟩ := exists_sum_range_cutoffWeight_le
  obtain ⟨C₁, hC₁0', hC₁⟩ := exists_norm_smoothAFECutoff_le
  refine ⟨96 * Ch + 176 * C₁ + 7300 * Real.sqrt 200 * C₁ + 8 * Ct, by positivity, ?_⟩
  intro T a b x hT ha hab hb hx
  have hT16 : (16 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨hsumm, hle⟩ := hmain hx
  have hs16 : (16 : ℝ) ≤ Real.sqrt T := sixteen_le_sqrtT hT
  have hs0 : (0 : ℝ) < Real.sqrt T := by linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := 8 / Real.sqrt T with hδdef
  set P : ℝ := Real.sqrt (a / (2 * Real.pi)) with hPdef
  set Q : ℝ := Real.sqrt (b / (2 * Real.pi)) with hQdef
  set M : ℕ := ⌈5 * Real.sqrt T⌉₊ with hMdef
  have hMge : 5 * Real.sqrt T ≤ (M : ℝ) := Nat.le_ceil _
  have hMlt : (M : ℝ) < 5 * Real.sqrt T + 1 := Nat.ceil_lt_add_one (by positivity)
  have hM6 : (M : ℝ) ≤ 6 * Real.sqrt T := by linarith
  -- summability and per-term second bound
  have hsecond : ∀ n : ℕ, |∫ τ in a..b, hardyDirectTerm x n τ|
      ≤ 64 * Real.sqrt (200 * T) * cutoffWeight x n :=
    fun n => abs_integral_hardyDirectTerm_le_second_window (by linarith) ha hb hab x n
  have habs : Summable (fun n : ℕ => |∫ τ in a..b, hardyDirectTerm x n τ|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) hsecond ?_
    exact hsumm.mul_left (64 * Real.sqrt (200 * T))
  -- the far tail beyond the conductor cutoff
  have hfirst : ∀ n : ℕ, |∫ τ in a..b, hardyDirectTerm x (n + M) τ|
      ≤ 8 * cutoffWeight x (n + M) := by
    intro n
    refine abs_integral_hardyDirectTerm_le_first_window hT16 ha hb hab x (n + M) ?_
    refine Real.log_le_log (by positivity) ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : ((n + M : ℕ) : ℝ) + 1 = (n : ℝ) + (M : ℝ) + 1 := by push_cast; ring
    rw [h1]
    linarith
  have hshift : Summable (fun n : ℕ => |∫ τ in a..b, hardyDirectTerm x (n + M) τ|) :=
    (summable_nat_add_iff M).mpr habs
  have hsplit := habs.sum_add_tsum_nat_add M
  have htailbd : ∑' n : ℕ, |∫ τ in a..b, hardyDirectTerm x (n + M) τ|
      ≤ 8 * (Ct * Real.sqrt x) := by
    refine le_trans (hshift.tsum_le_tsum hfirst
      (((summable_nat_add_iff M).mpr hsumm).mul_left 8)) ?_
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact le_trans (tsum_cutoffWeight_shift_le hx M) hle
  -- head class split
  set F : ℕ → ℝ := fun n => |∫ τ in a..b, hardyDirectTerm x n τ| with hFdef
  set S1 : Finset ℕ := (Finset.range M).filter (fun n => ((n : ℝ) + 1) ≤ P / 3)
    with hS1def
  set R1 : Finset ℕ := (Finset.range M).filter (fun n => ¬ ((n : ℝ) + 1) ≤ P / 3)
    with hR1def
  set S2 : Finset ℕ := R1.filter (fun n => ((n : ℝ) + 1) ≤ P * Real.exp (-δ)) with hS2def
  set R2 : Finset ℕ := R1.filter (fun n => ¬ ((n : ℝ) + 1) ≤ P * Real.exp (-δ))
    with hR2def
  set S3 : Finset ℕ := R2.filter (fun n => ((n : ℝ) + 1) < Q * Real.exp δ) with hS3def
  set R3 : Finset ℕ := R2.filter (fun n => ¬ ((n : ℝ) + 1) < Q * Real.exp δ) with hR3def
  set S4 : Finset ℕ := R3.filter (fun n => ((n : ℝ) + 1) < 3 * Q) with hS4def
  set S5 : Finset ℕ := R3.filter (fun n => ¬ ((n : ℝ) + 1) < 3 * Q) with hS5def
  have hhead1 : ∑ n ∈ Finset.range M, F n = ∑ n ∈ S1, F n + ∑ n ∈ R1, F n :=
    (Finset.sum_filter_add_sum_filter_not _ _ F).symm
  have hhead2 : ∑ n ∈ R1, F n = ∑ n ∈ S2, F n + ∑ n ∈ R2, F n :=
    (Finset.sum_filter_add_sum_filter_not _ _ F).symm
  have hhead3 : ∑ n ∈ R2, F n = ∑ n ∈ S3, F n + ∑ n ∈ R3, F n :=
    (Finset.sum_filter_add_sum_filter_not _ _ F).symm
  have hhead4 : ∑ n ∈ R3, F n = ∑ n ∈ S4, F n + ∑ n ∈ S5, F n :=
    (Finset.sum_filter_add_sum_filter_not _ _ F).symm
  -- class bounds
  have hB1 : ∑ n ∈ S1, F n ≤ 16 * (Ch * Real.sqrt (M : ℝ)) := by
    have h1 : ∀ n ∈ S1, F n ≤ 16 * cutoffWeight x n := by
      intro n hn
      have h2 := (Finset.mem_filter.mp hn).2
      exact term_low_far hT ha hab hb hPdef n h2
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun i _ _ => cutoffWeight_nonneg x i)) ?_
    exact hhead hx0 M
  have hR1sub : R1 ⊆ Finset.range M := Finset.filter_subset _ _
  have hR2sub : R2 ⊆ Finset.range M :=
    Finset.Subset.trans (Finset.filter_subset _ _) hR1sub
  have hR3sub : R3 ⊆ Finset.range M :=
    Finset.Subset.trans (Finset.filter_subset _ _) hR2sub
  have hB5 : ∑ n ∈ S5, F n ≤ 16 * (Ch * Real.sqrt (M : ℝ)) := by
    have h1 : ∀ n ∈ S5, F n ≤ 16 * cutoffWeight x n := by
      intro n hn
      have h2 := (Finset.mem_filter.mp hn).2
      exact term_high_far hT ha hab hb hQdef n (not_lt.mp h2)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Subset.trans (Finset.filter_subset _ _) hR3sub)
      (fun i _ _ => cutoffWeight_nonneg x i)) ?_
    exact hhead hx0 M
  have hB2 : ∑ n ∈ S2, F n
      ≤ 32 * C₁ * Real.sqrt (Real.sqrt T) * (1 + Real.log (Real.sqrt T)) := by
    refine sum_class_low_near hT ha hab hb hx0 hC₁ hPdef hδdef ?_
    intro n hn
    have h1 := Finset.mem_filter.mp hn
    have h2 := Finset.mem_filter.mp h1.1
    exact ⟨not_le.mp h2.2, h1.2⟩
  have hB3 : ∑ n ∈ S3, F n
      ≤ 384 * Real.sqrt 200 * C₁
        * ((b - a) / Real.sqrt (Real.sqrt T) + 18 * Real.sqrt (Real.sqrt T)) := by
    refine sum_class_cross hT ha hab hb hx0 hC₁ hPdef hQdef hδdef ?_
    intro n hn
    have h1 := Finset.mem_filter.mp hn
    have h2 := Finset.mem_filter.mp h1.1
    exact ⟨not_le.mp h2.2, h1.2⟩
  have hB4 : ∑ n ∈ S4, F n
      ≤ 48 * C₁ * Real.sqrt (Real.sqrt T) * (3 + Real.log (Real.sqrt T)) := by
    refine sum_class_high_near hT ha hab hb hx0 hC₁ hQdef hδdef hM6 ?_ ?_
    · intro n hn
      have h1 := Finset.mem_filter.mp hn
      have h2 := Finset.mem_filter.mp h1.1
      exact ⟨not_lt.mp h2.2, h1.2⟩
    · intro n hn
      have h1 := Finset.mem_filter.mp hn
      exact Finset.mem_range.mp (hR3sub h1.1)
  -- fold the pieces
  have hfinal : |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
      ≤ ∑' n : ℕ, F n := by
    rw [integral_hardyDirectSeries_eq_window hab hx]
    have h := norm_tsum_le_tsum_norm
      (f := fun n : ℕ => ∫ τ in a..b, hardyDirectTerm x n τ)
      (by simpa [Real.norm_eq_abs] using habs)
    simpa [Real.norm_eq_abs] using h
  set s4 : ℝ := Real.sqrt (Real.sqrt T) with hs4def
  have hs40 : (0 : ℝ) < s4 := Real.sqrt_pos.mpr hs0
  have hsqM : Real.sqrt (M : ℝ) ≤ 3 * s4 := by
    have h1 : (M : ℝ) ≤ 9 * Real.sqrt T := by linarith
    calc Real.sqrt (M : ℝ) ≤ Real.sqrt (9 * Real.sqrt T) := Real.sqrt_le_sqrt h1
      _ = 3 * s4 := by
          rw [hs4def, Real.sqrt_mul (by norm_num) _, show Real.sqrt 9 = 3 by
            rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
  have hlogs : Real.log (Real.sqrt T) ≤ Real.log T := by
    rw [Real.log_sqrt hT0.le]
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]
  have hlogs0 : (0 : ℝ) ≤ Real.log (Real.sqrt T) := Real.log_nonneg (by linarith)
  have hlogT0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  -- grouped estimates
  have hA0 : (0 : ℝ) ≤ s4 * (1 + Real.log T) := by positivity
  have hBq0 : (0 : ℝ) ≤ (b - a) / s4 := by
    have : (0 : ℝ) ≤ b - a := by linarith
    positivity
  have hX0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hg15 : ∑ n ∈ S1, F n + ∑ n ∈ S5, F n ≤ 96 * Ch * (s4 * (1 + Real.log T)) := by
    have h1 : 16 * (Ch * Real.sqrt (M : ℝ)) ≤ 48 * Ch * s4 := by
      have h2 := mul_le_mul_of_nonneg_left hsqM hCh
      linarith only [h2]
    have h3 : 48 * Ch * s4 ≤ 48 * Ch * (s4 * (1 + Real.log T)) := by
      have h4 : s4 * 1 ≤ s4 * (1 + Real.log T) :=
        mul_le_mul_of_nonneg_left (by linarith only [hlogT0]) hs40.le
      rw [mul_one] at h4
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith only [hB1, hB5, h1, h3]
  have hg2 : ∑ n ∈ S2, F n ≤ 32 * C₁ * (s4 * (1 + Real.log T)) := by
    refine le_trans hB2 ?_
    have h1 : (1 : ℝ) + Real.log (Real.sqrt T) ≤ 1 + Real.log T := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Real.log (Real.sqrt T) := by linarith
    calc 32 * C₁ * s4 * (1 + Real.log (Real.sqrt T))
        ≤ 32 * C₁ * s4 * (1 + Real.log T) := by
          refine mul_le_mul_of_nonneg_left h1 ?_
          positivity
      _ = 32 * C₁ * (s4 * (1 + Real.log T)) := by ring
  have hg4 : ∑ n ∈ S4, F n ≤ 144 * C₁ * (s4 * (1 + Real.log T)) := by
    refine le_trans hB4 ?_
    have h1 : (3 : ℝ) + Real.log (Real.sqrt T) ≤ 3 * (1 + Real.log T) := by linarith
    have h2 : (0 : ℝ) ≤ 3 + Real.log (Real.sqrt T) := by linarith
    calc 48 * C₁ * s4 * (3 + Real.log (Real.sqrt T))
        ≤ 48 * C₁ * s4 * (3 * (1 + Real.log T)) := by
          refine mul_le_mul_of_nonneg_left h1 ?_
          positivity
      _ = 144 * C₁ * (s4 * (1 + Real.log T)) := by ring
  have hg3 : ∑ n ∈ S3, F n
      ≤ 384 * Real.sqrt 200 * C₁ * ((b - a) / s4)
        + 6912 * Real.sqrt 200 * C₁ * (s4 * (1 + Real.log T)) := by
    refine le_trans hB3 ?_
    have h1 : (18 : ℝ) * s4 ≤ 18 * (s4 * (1 + Real.log T)) := by
      have h4 : s4 * 1 ≤ s4 * (1 + Real.log T) :=
        mul_le_mul_of_nonneg_left (by linarith only [hlogT0]) hs40.le
      rw [mul_one] at h4
      linarith only [h4]
    have h2 : (0 : ℝ) ≤ 384 * Real.sqrt 200 * C₁ := by positivity
    calc 384 * Real.sqrt 200 * C₁ * ((b - a) / s4 + 18 * s4)
        = 384 * Real.sqrt 200 * C₁ * ((b - a) / s4)
          + 384 * Real.sqrt 200 * C₁ * (18 * s4) := by ring
      _ ≤ 384 * Real.sqrt 200 * C₁ * ((b - a) / s4)
          + 384 * Real.sqrt 200 * C₁ * (18 * (s4 * (1 + Real.log T))) := by
          have := mul_le_mul_of_nonneg_left h1 h2
          linarith
      _ = 384 * Real.sqrt 200 * C₁ * ((b - a) / s4)
          + 6912 * Real.sqrt 200 * C₁ * (s4 * (1 + Real.log T)) := by ring
  -- assemble
  have hsum200 : (0 : ℝ) ≤ Real.sqrt 200 := Real.sqrt_nonneg _
  have htotal : |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
      ≤ (96 * Ch + 176 * C₁ + 6912 * Real.sqrt 200 * C₁) * (s4 * (1 + Real.log T))
        + 384 * Real.sqrt 200 * C₁ * ((b - a) / s4) + 8 * Ct * Real.sqrt x := by
    calc |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
        ≤ ∑' n : ℕ, F n := hfinal
      _ = ∑ n ∈ Finset.range M, F n
            + ∑' n : ℕ, F (n + M) := hsplit.symm
      _ ≤ (∑ n ∈ S1, F n + ∑ n ∈ S2, F n + ∑ n ∈ S3, F n + ∑ n ∈ S4, F n
            + ∑ n ∈ S5, F n) + 8 * (Ct * Real.sqrt x) := by
          rw [hhead1, hhead2, hhead3, hhead4]
          linarith only [htailbd]
      _ ≤ (96 * Ch + 176 * C₁ + 6912 * Real.sqrt 200 * C₁) * (s4 * (1 + Real.log T))
            + 384 * Real.sqrt 200 * C₁ * ((b - a) / s4) + 8 * Ct * Real.sqrt x := by
          linarith only [hg15, hg2, hg3, hg4]
  refine le_trans htotal ?_
  have hprod : (0 : ℝ) ≤ Real.sqrt 200 * C₁ := mul_nonneg hsum200 hC₁0'
  have hc1 : 96 * Ch + 176 * C₁ + 6912 * Real.sqrt 200 * C₁
      ≤ 96 * Ch + 176 * C₁ + 7300 * Real.sqrt 200 * C₁ + 8 * Ct := by
    linarith only [hprod, hCt]
  have hc2 : 384 * Real.sqrt 200 * C₁
      ≤ 96 * Ch + 176 * C₁ + 7300 * Real.sqrt 200 * C₁ + 8 * Ct := by
    linarith only [hprod, hCt, hCh, hC₁0']
  have hc3 : 8 * Ct ≤ 96 * Ch + 176 * C₁ + 7300 * Real.sqrt 200 * C₁ + 8 * Ct := by
    linarith only [hprod, hCh, hC₁0']
  set CC : ℝ := 96 * Ch + 176 * C₁ + 7300 * Real.sqrt 200 * C₁ + 8 * Ct with hCCdef
  calc (96 * Ch + 176 * C₁ + 6912 * Real.sqrt 200 * C₁) * (s4 * (1 + Real.log T))
        + 384 * Real.sqrt 200 * C₁ * ((b - a) / s4) + 8 * Ct * Real.sqrt x
      ≤ CC * (s4 * (1 + Real.log T)) + CC * ((b - a) / s4) + CC * Real.sqrt x := by
        have h1 := mul_le_mul_of_nonneg_right hc1 hA0
        have h2 := mul_le_mul_of_nonneg_right hc2 hBq0
        have h3 := mul_le_mul_of_nonneg_right hc3 hX0
        linarith
    _ = CC * (s4 * (1 + Real.log T) + (b - a) / s4 + Real.sqrt x) := by ring

private theorem combine_window_bounds {CD K u v A B X D : ℝ} (hCD : 0 ≤ CD)
    (hK : 0 ≤ K) (hA : 1 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X) (hD : 0 ≤ D)
    (hu : u ≤ CD * (A + B + X)) (hv : v ≤ 9 * K * D + 1) :
    u + v ≤ (CD + 9 * K + 1) * (A + B + X + D) := by
  have h1 : CD * (A + B + X) ≤ CD * (A + B + X + D) :=
    mul_le_mul_of_nonneg_left (by linarith) hCD
  have h2 : 9 * K * D ≤ 9 * K * (A + B + X + D) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : (1 : ℝ) ≤ A + B + X + D := by linarith
  nlinarith [h1, h2, h3]

/-! ## The sharp window mean of Hardy's `Z` -/

/-- **The sharp window mean of Hardy's `Z`.**  For every window `[a,b] ⊆ [T,2T]` and every
cutoff `1 ≤ x ≤ e^T`, the window mean is bounded by
`C·(√√T(1+log T) + (b-a)/√√T + √x + (b-a)·T/x)`: the resonance-graded direct edge plus the
cutoff tail.  At `x ≈ ((b-a)T)^{2/3}` this is far below the trivial `T^{3/4}` for short
windows. -/
theorem exists_abs_integral_hardyZ_window_sharp_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T a b x : ℝ}, 256 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
      1 ≤ x → x ≤ Real.exp T →
      |∫ τ in a..b, hardyZ τ|
        ≤ C * (Real.sqrt (Real.sqrt T) * (1 + Real.log T)
            + (b - a) / Real.sqrt (Real.sqrt T) + Real.sqrt x + (b - a) * T / x) := by
  obtain ⟨CD, hCD, hdirect⟩ := exists_abs_integral_hardyDirectSeries_window_sharp
  obtain ⟨K, hK, htail⟩ := exists_abs_hardyZ_sub_direct_le
  refine ⟨CD + 9 * K + 1, by positivity, ?_⟩
  intro T a b x hT ha hab hb hx hxe
  have hT0 : (0 : ℝ) < T := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hba0 : (0 : ℝ) ≤ b - a := by linarith
  have hbaT : b - a ≤ T := by linarith
  have hZint : IntervalIntegrable hardyZ volume a b :=
    continuous_hardyZ.intervalIntegrable _ _
  have hDint : IntervalIntegrable (fun τ : ℝ => ∑' n : ℕ, hardyDirectTerm x n τ)
      volume a b := (continuous_hardyDirectSeries hx).intervalIntegrable _ _
  have hdecomp : (∫ τ in a..b, hardyZ τ)
      = (∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ))
        + ∫ τ in a..b, (hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ) := by
    rw [intervalIntegral.integral_sub hZint hDint]
    ring
  -- pointwise tail bound on the window
  have hconst : ∀ τ ∈ Set.uIoc a b,
      ‖hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ‖
        ≤ 9 * K * T / x + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) := by
    intro τ hτ
    rw [Set.uIoc_of_le hab] at hτ
    have hτ1 : (1 : ℝ) ≤ τ := by linarith [hτ.1]
    have hτ2T : τ ≤ 2 * T := le_trans hτ.2 hb
    have hτT : T ≤ τ := le_trans ha hτ.1.le
    have hbnd := htail hx0 hτ1
    rw [Real.norm_eq_abs]
    refine le_trans hbnd (add_le_add ?_ ?_)
    · have hnum : 3 * K * (1 + τ) ≤ 9 * K * T := by nlinarith [hK]
      exact div_le_div_of_nonneg_right hnum hx0.le
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hτT])) ?_
      positivity
  have htailint := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  rw [abs_of_nonneg hba0] at htailint
  -- the Gaussian remainder is below one
  have hexpbd : Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * (b - a) ≤ 1 := by
    have h1 : Real.sqrt x ≤ Real.exp (T / 2) := by
      have h2 : Real.sqrt x ≤ Real.sqrt (Real.exp T) := Real.sqrt_le_sqrt hxe
      have h3 : Real.sqrt (Real.exp T) = Real.exp (T / 2) := by
        rw [show Real.exp T = Real.exp (T / 2) * Real.exp (T / 2) by
            rw [← Real.exp_add]; ring_nf,
          Real.sqrt_mul_self (le_of_lt (Real.exp_pos _))]
      linarith [h3 ▸ h2]
    have h2 : Real.exp ((1 : ℝ) / 4) ≤ 2 := by
      have h3 : Real.exp ((1 : ℝ) / 4) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
      rwa [Real.exp_log (by norm_num)] at h3
    have h5 : Real.sqrt x * Real.exp (1 / 4) ≤ 2 * Real.exp (T / 2) := by
      calc Real.sqrt x * Real.exp (1 / 4)
          ≤ Real.exp (T / 2) * 2 :=
            mul_le_mul h1 h2 (by positivity) (le_of_lt (Real.exp_pos _))
        _ = 2 * Real.exp (T / 2) := by ring
    have h6 : Real.exp (T / 2) * Real.exp (-(T ^ (2 : ℕ))) = (Real.exp (T ^ (2 : ℕ) - T / 2))⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_neg]
      ring_nf
    have h7 : 2 * T ≤ Real.exp (T ^ (2 : ℕ) - T / 2) := by
      have h8 := Real.add_one_le_exp (T ^ (2 : ℕ) - T / 2)
      nlinarith
    have h9 : (0 : ℝ) < Real.exp (T ^ (2 : ℕ) - T / 2) := Real.exp_pos _
    calc Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * (b - a)
        ≤ 2 * Real.exp (T / 2) * Real.exp (-(T ^ (2 : ℕ))) * T := by
          have hp : (0 : ℝ) ≤ Real.exp (-(T ^ (2 : ℕ))) := le_of_lt (Real.exp_pos _)
          have hq : (0 : ℝ) ≤ Real.sqrt x * Real.exp (1 / 4) := by positivity
          have hr := mul_le_mul h5 hbaT hba0 (by positivity :
            (0 : ℝ) ≤ 2 * Real.exp (T / 2))
          calc Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * (b - a)
              = Real.sqrt x * Real.exp (1 / 4) * (b - a) * Real.exp (-(T ^ (2 : ℕ))) := by ring
            _ ≤ 2 * Real.exp (T / 2) * T * Real.exp (-(T ^ (2 : ℕ))) :=
                mul_le_mul_of_nonneg_right hr hp
            _ = 2 * Real.exp (T / 2) * Real.exp (-(T ^ (2 : ℕ))) * T := by ring
      _ = 2 * T * (Real.exp (T ^ (2 : ℕ) - T / 2))⁻¹ := by rw [mul_assoc 2 _ _, h6]; ring
      _ ≤ 1 := by
          rw [mul_inv_le_iff₀ h9]
          linarith
  -- combine
  have hdir := hdirect hT ha hab hb hx
  have htailfinal : ‖∫ τ in a..b, (hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ)‖
      ≤ 9 * K * ((b - a) * T / x) + 1 := by
    refine le_trans htailint ?_
    have h1 : (9 * K * T / x + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))))
          * (b - a)
        = 9 * K * ((b - a) * T / x)
          + Real.sqrt x * Real.exp (1 / 4) * Real.exp (-(T ^ (2 : ℕ))) * (b - a) := by
      ring
    rw [h1]
    linarith [hexpbd]
  have hs4ge : (4 : ℝ) ≤ Real.sqrt (Real.sqrt T) := by
    have h1 : Real.sqrt 16 ≤ Real.sqrt (Real.sqrt T) :=
      Real.sqrt_le_sqrt (sixteen_le_sqrtT hT)
    have h2 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num]
      exact Real.sqrt_sq (by norm_num)
    linarith
  have hlogT0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  have hA1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt T) * (1 + Real.log T) := by
    nlinarith [hs4ge, hlogT0]
  have hB0 : (0 : ℝ) ≤ (b - a) / Real.sqrt (Real.sqrt T) := by positivity
  have hX0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hD0 : (0 : ℝ) ≤ (b - a) * T / x := by positivity
  have hsplit : |∫ τ in a..b, hardyZ τ|
      ≤ |∫ τ in a..b, (∑' n : ℕ, hardyDirectTerm x n τ)|
        + ‖∫ τ in a..b, (hardyZ τ - ∑' n : ℕ, hardyDirectTerm x n τ)‖ := by
    rw [hdecomp, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact norm_add_le _ _
  refine le_trans hsplit ?_
  exact combine_window_bounds hCD hK hA1 hB0 hX0 hD0 hdir htailfinal
