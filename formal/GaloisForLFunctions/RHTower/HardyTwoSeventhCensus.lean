import GaloisForLFunctions.RHTower.HardySixthRootCensus
import GaloisForLFunctions.RHTower.HardyZWindowMeanSharp

/-!
# The two-sevenths critical-line census

The resonance-graded window mean `|∫_a^b Z| ≤ C(T^{1/4}(1+log T) + (b-a)T^{-1/4} + √x
+ (b-a)T/x)` replaces the trivial `T^{3/4}` mean in the window pigeonhole.  At cutoff
`x = T^{8/7}` and `K = ⌊T^{2/7}/(D(1+log T)^5)⌋` windows the per-window mean is
`O(T^{4/7}·polylog)`, the sign-change gap `ME²·M4 < (T/8K)³` closes, and the
Cauchy–Schwarz count gives `K/polylog` distinct critical-line ordinates per dyadic block:
`N₀(T) ≥ c·T^{2/7}/(1+log T)^9`, unconditionally.
-/

open Set MeasureTheory Complex Finset

namespace RHTower

noncomputable section

/-! ## Real-power utilities -/

private theorem rpow_pow {T : ℝ} (hT : 0 ≤ T) (q : ℝ) (n : ℕ) :
    (T ^ q) ^ n = T ^ (q * (n : ℝ)) := by
  rw [← Real.rpow_natCast (T ^ q) n, ← Real.rpow_mul hT]

private theorem rpow_add_eq {T : ℝ} (hT : 0 < T) {p q r : ℝ} (h : p + q = r) :
    T ^ p * T ^ q = T ^ r := by
  rw [← Real.rpow_add hT, h]

/-- `T^{8/7} ≤ e^T` for `T ≥ 256`: the cutoff obeys the Gaussian-tail constraint. -/
private theorem rpow_le_exp {T : ℝ} (hT : 256 ≤ T) : T ^ ((8 : ℝ) / 7) ≤ Real.exp T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 : T ^ ((8 : ℝ) / 7) = Real.exp ((8 : ℝ) / 7 * Real.log T) := by
    rw [Real.rpow_def_of_pos hT0, mul_comm]
  rw [h1]
  refine Real.exp_le_exp.mpr ?_
  have hs : (16 : ℝ) ≤ Real.sqrt T := by
    rw [show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  have h2 : Real.log (Real.sqrt T) ≤ Real.sqrt T - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h3 : Real.log (Real.sqrt T) = Real.log T / 2 := Real.log_sqrt hT0.le
  have hprod : 16 * Real.sqrt T ≤ T := by
    have h4 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
    nlinarith [Real.sqrt_nonneg T]
  linarith only [h2, h3, hprod, hT0.le]

/-! ## The abstract moment gap -/

/-- The sign-change gap `ME²·M4 < (T/8K)³` follows from
`512·K³·ME²·(CF+1)(1+log T)⁴ < T²`. -/
private theorem gap_of_bound {T CF ME : ℝ} {K : ℕ} (hT0 : 0 < T) (hK1 : 1 ≤ K)
    (hkey : 512 * (K : ℝ) ^ 3 * ME ^ 2 * ((CF + 1) * (1 + Real.log T) ^ 4) < T ^ 2) :
    ME ^ 2 * ((CF + 1) * T * (1 + Real.log T) ^ 4) < (T / (8 * (K : ℝ))) ^ 3 := by
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hΘcube : (T / (8 * (K : ℝ))) ^ 3 = T ^ 3 / (512 * (K : ℝ) ^ 3) := by
    rw [div_pow]
    congr 1
    ring
  rw [hΘcube, lt_div_iff₀ (by positivity : (0 : ℝ) < 512 * (K : ℝ) ^ 3)]
  have hlhs : ME ^ 2 * ((CF + 1) * T * (1 + Real.log T) ^ 4) * (512 * (K : ℝ) ^ 3)
      = (512 * (K : ℝ) ^ 3 * ME ^ 2 * ((CF + 1) * (1 + Real.log T) ^ 4)) * T := by
    ring
  have hT3 : T ^ 3 = T ^ 2 * T := by ring
  rw [hlhs, hT3]
  exact mul_lt_mul_of_pos_right hkey hT0

/-! ## Exponent comparisons -/

private theorem rpow_exp_mono {T p q : ℝ} (hT1 : 1 ≤ T) (hpq : p ≤ q) :
    T ^ p ≤ T ^ q :=
  Real.rpow_le_rpow_of_exponent_le hT1 hpq

private theorem one_le_rpow {T q : ℝ} (hT1 : 1 ≤ T) (hq : 0 ≤ q) : 1 ≤ T ^ q := by
  have h := Real.rpow_le_rpow (by norm_num) hT1 hq
  rwa [Real.one_rpow] at h

/-! ## Two-sevenths many distinct critical-line ordinates -/

private theorem window_mean_le {T CS D2 : ℝ} {K : ℕ} (hT256 : 256 ≤ T) (hCS0 : 0 ≤ CS)
    (hD22 : 2 ≤ D2) (hK1 : 1 ≤ K)
    (hsharp : ∀ {a b x : ℝ}, 256 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T → 1 ≤ x →
      x ≤ Real.exp T →
      |∫ τ in a..b, hardyZ τ|
        ≤ CS * (Real.sqrt (Real.sqrt T) * (1 + Real.log T)
            + (b - a) / Real.sqrt (Real.sqrt T) + Real.sqrt x + (b - a) * T / x))
    (hTKle : T / (K : ℝ) ≤ 2 * (D2 * (1 + Real.log T) ^ 5) * T ^ ((5 : ℝ) / 7)) :
    ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ|
        ≤ 6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) := by
  have hT0 : (0 : ℝ) < T := by linarith only [hT256]
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT256]
  have hL1 : (1 : ℝ) ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1
    linarith only [this]
  have hL0 : (0 : ℝ) < 1 + Real.log T := by linarith only [hL1]
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hTK0 : (0 : ℝ) < T / K := div_pos hT0 hKR0
  intro k hkK
  have hk1K : ((k : ℝ) + 1) ≤ (K : ℝ) := by exact_mod_cast hkK
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha' : T ≤ T + k * (T / K) := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) * (T / K) := mul_nonneg hk0 hTK0.le
    linarith only [h0]
  have hab' : T + k * (T / K) ≤ T + ((k + 1 : ℕ) : ℝ) * (T / K) := by
    push_cast
    have := mul_le_mul_of_nonneg_right
      (by linarith only [] : (k : ℝ) ≤ (k : ℝ) + 1) hTK0.le
    linarith only [this]
  have hb' : T + ((k + 1 : ℕ) : ℝ) * (T / K) ≤ 2 * T := by
    push_cast
    have h1 : ((k : ℝ) + 1) * (T / K) ≤ (K : ℝ) * (T / K) :=
      mul_le_mul_of_nonneg_right hk1K hTK0.le
    have h2 : (K : ℝ) * (T / K) = T := by field_simp
    linarith only [h1, h2.le, h2.ge]
  have hdiff : T + ((k + 1 : ℕ) : ℝ) * (T / K) - (T + k * (T / K)) = T / K := by
    push_cast
    ring
  have hx1 : (1 : ℝ) ≤ T ^ ((8 : ℝ) / 7) := one_le_rpow hT1 (by norm_num)
  have hxe := rpow_le_exp hT256
  have h := hsharp hT256 ha' hab' hb' hx1 hxe
  rw [hdiff] at h
  refine le_trans h ?_
  -- bound the four terms by E
  have hs4T : Real.sqrt (Real.sqrt T) = T ^ ((1 : ℝ) / 4) := by
    rw [show Real.sqrt T = T ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow T,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
    congr 1
    norm_num
  have hsqx : Real.sqrt (T ^ ((8 : ℝ) / 7)) = T ^ ((4 : ℝ) / 7) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
    congr 1
    norm_num
  have hTdivx : T / T ^ ((8 : ℝ) / 7) = (T ^ ((1 : ℝ) / 7))⁻¹ := by
    have h1 : T ^ ((1 : ℝ)) * T ^ ((1 : ℝ) / 7) = T ^ ((8 : ℝ) / 7) :=
      rpow_add_eq hT0 (by norm_num : (1 : ℝ) + 1 / 7 = 8 / 7)
    rw [Real.rpow_one] at h1
    rw [← h1, div_mul_eq_div_div, div_self (ne_of_gt hT0), one_div]
  -- term 1
  have ht1 : Real.sqrt (Real.sqrt T) * (1 + Real.log T)
      ≤ (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) := by
    rw [hs4T]
    have h1 : T ^ ((1 : ℝ) / 4) ≤ T ^ ((4 : ℝ) / 7) :=
      rpow_exp_mono hT1 (by norm_num)
    have h2 : (1 + Real.log T) ≤ (1 + Real.log T) ^ 5 :=
      le_self_pow₀ hL1 (by norm_num)
    have h3 := mul_le_mul h1 h2 hL0.le
      (le_of_lt (Real.rpow_pos_of_pos hT0 _))
    calc T ^ ((1 : ℝ) / 4) * (1 + Real.log T)
        ≤ T ^ ((4 : ℝ) / 7) * (1 + Real.log T) ^ 5 := h3
      _ = (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) := by ring
  -- terms 2 and 4 merge through T^{-1/7} ≥ T^{-1/4}
  have ht17pos : (0 : ℝ) < T ^ ((1 : ℝ) / 7) := Real.rpow_pos_of_pos hT0 _
  have ht2 : (T / K) / Real.sqrt (Real.sqrt T) ≤ (T / K) / T ^ ((1 : ℝ) / 7) := by
    rw [hs4T]
    exact div_le_div_of_nonneg_left hTK0.le ht17pos
      (rpow_exp_mono hT1 (by norm_num))
  have ht4 : (T / K) * T / T ^ ((8 : ℝ) / 7) = (T / K) / T ^ ((1 : ℝ) / 7) := by
    rw [mul_div_assoc, hTdivx]
    exact (div_eq_mul_inv _ _).symm
  have htK7 : (T / K) / T ^ ((1 : ℝ) / 7)
      ≤ 2 * (D2 * (1 + Real.log T) ^ 5) * T ^ ((4 : ℝ) / 7) := by
    rw [div_le_iff₀ ht17pos]
    have h1 : T ^ ((4 : ℝ) / 7) * T ^ ((1 : ℝ) / 7) = T ^ ((5 : ℝ) / 7) :=
      rpow_add_eq hT0 (by norm_num)
    calc T / K ≤ 2 * (D2 * (1 + Real.log T) ^ 5) * T ^ ((5 : ℝ) / 7) := hTKle
      _ = 2 * (D2 * (1 + Real.log T) ^ 5)
          * (T ^ ((4 : ℝ) / 7) * T ^ ((1 : ℝ) / 7)) := by rw [h1]
      _ = 2 * (D2 * (1 + Real.log T) ^ 5) * T ^ ((4 : ℝ) / 7)
          * T ^ ((1 : ℝ) / 7) := by ring
  -- term 3
  have ht3 : Real.sqrt (T ^ ((8 : ℝ) / 7))
      ≤ (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) := by
    rw [hsqx]
    have h1 : (1 : ℝ) ≤ (1 + Real.log T) ^ 5 := one_le_pow₀ hL1
    have h2 := mul_le_mul_of_nonneg_right h1
      (le_of_lt (Real.rpow_pos_of_pos hT0 ((4 : ℝ) / 7)))
    calc T ^ ((4 : ℝ) / 7) = 1 * T ^ ((4 : ℝ) / 7) := (one_mul _).symm
      _ ≤ (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) := h2
  -- combine into E
  have hsum : Real.sqrt (Real.sqrt T) * (1 + Real.log T)
        + (T / K) / Real.sqrt (Real.sqrt T) + Real.sqrt (T ^ ((8 : ℝ) / 7))
        + (T / K) * T / T ^ ((8 : ℝ) / 7)
      ≤ (2 + 4 * D2) * ((1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)) := by
    have h24 : (T / K) / Real.sqrt (Real.sqrt T) + (T / K) * T / T ^ ((8 : ℝ) / 7)
        ≤ 4 * D2 * ((1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)) := by
      rw [ht4]
      have := le_trans ht2 htK7
      have h5 : 2 * (D2 * (1 + Real.log T) ^ 5) * T ^ ((4 : ℝ) / 7)
          = 2 * D2 * ((1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)) := by ring
      linarith only [this, htK7, h5.le, h5.ge]
    linarith only [ht1, ht3, h24]
  have hE' : CS * ((2 + 4 * D2) * ((1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)))
      ≤ 6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) := by
    have h1 : (2 : ℝ) + 4 * D2 ≤ 6 * D2 := by linarith only [hD22]
    have h2 : (0 : ℝ) ≤ (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) :=
      mul_nonneg (le_of_lt (pow_pos hL0 5))
        (le_of_lt (Real.rpow_pos_of_pos hT0 _))
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have h4 := mul_le_mul_of_nonneg_left h3 hCS0
    calc CS * ((2 + 4 * D2) * ((1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)))
        ≤ CS * (6 * D2 * ((1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7))) := h4
      _ = 6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left hsum hCS0) hE'

private theorem key_lt {T CS D2 CF : ℝ} {K : ℕ} (hT256 : 256 ≤ T)
    (hCF : 0 ≤ CF) (hK1 : 1 ≤ K)
    (hD2big : 18432 * CS ^ 2 * (CF + 1) + 2 ≤ D2)
    (hKD : (K : ℝ) * (D2 * (1 + Real.log T) ^ 5) ≤ T ^ ((2 : ℝ) / 7)) :
    512 * (K : ℝ) ^ 3
        * (6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)) ^ 2
        * ((CF + 1) * (1 + Real.log T) ^ 4) < T ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith only [hT256]
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT256]
  have hL1 : (1 : ℝ) ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1
    linarith only [this]
  have hL0 : (0 : ℝ) < 1 + Real.log T := by linarith only [hL1]
  have hsq : (0 : ℝ) ≤ 18432 * CS ^ 2 * (CF + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg CS)) (by linarith only [hCF])
  have hD2pos : (0 : ℝ) < D2 := by linarith only [hD2big, hsq]
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hDL5pos : (0 : ℝ) < D2 * (1 + Real.log T) ^ 5 := mul_pos hD2pos (pow_pos hL0 5)
  have hcube : ((K : ℝ) * (D2 * (1 + Real.log T) ^ 5)) ^ 3 ≤ T ^ ((6 : ℝ) / 7) := by
    have h1 : ((K : ℝ) * (D2 * (1 + Real.log T) ^ 5)) ^ 3
        ≤ (T ^ ((2 : ℝ) / 7)) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt (mul_pos hKR0 hDL5pos)) hKD 3
    have h2 : (T ^ ((2 : ℝ) / 7)) ^ 3 = T ^ ((6 : ℝ) / 7) := by
      rw [rpow_pow hT0.le]
      congr 1
      norm_num
    linarith only [h1, h2.le, h2.ge]
  have hE2 : (6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)) ^ 2
      = 36 * CS ^ 2 * D2 ^ 2 * (1 + Real.log T) ^ 10 * T ^ ((8 : ℝ) / 7) := by
    have h1 : (T ^ ((4 : ℝ) / 7)) ^ 2 = T ^ ((8 : ℝ) / 7) := by
      rw [rpow_pow hT0.le]
      congr 1
      norm_num
    calc (6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)) ^ 2
        = 36 * CS ^ 2 * D2 ^ 2 * (1 + Real.log T) ^ 10
          * (T ^ ((4 : ℝ) / 7)) ^ 2 := by ring
      _ = 36 * CS ^ 2 * D2 ^ 2 * (1 + Real.log T) ^ 10 * T ^ ((8 : ℝ) / 7) := by
          rw [h1]
  have hstep1 : 512 * (K : ℝ) ^ 3
      * (6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7)) ^ 2
      * ((CF + 1) * (1 + Real.log T) ^ 4)
      = 18432 * CS ^ 2 * (CF + 1) * D2 ^ 2 * (1 + Real.log T) ^ 14
        * ((K : ℝ) ^ 3 * T ^ ((8 : ℝ) / 7)) := by
    rw [hE2]
    ring
  have hcoef : 18432 * CS ^ 2 * (CF + 1) * D2 ^ 2 * (1 + Real.log T) ^ 14
      < D2 ^ 3 * (1 + Real.log T) ^ 15 := by
    have h2 : 18432 * CS ^ 2 * (CF + 1) < D2 * (1 + Real.log T) := by
      have h3 : D2 * 1 ≤ D2 * (1 + Real.log T) :=
        mul_le_mul_of_nonneg_left hL1 (le_of_lt hD2pos)
      rw [mul_one] at h3
      linarith only [hD2big, h3]
    have h4 : (0 : ℝ) < D2 ^ 2 * (1 + Real.log T) ^ 14 :=
      mul_pos (pow_pos hD2pos 2) (pow_pos hL0 14)
    have h5 := mul_lt_mul_of_pos_right h2 h4
    calc 18432 * CS ^ 2 * (CF + 1) * D2 ^ 2 * (1 + Real.log T) ^ 14
        = 18432 * CS ^ 2 * (CF + 1) * (D2 ^ 2 * (1 + Real.log T) ^ 14) := by ring
      _ < D2 * (1 + Real.log T) * (D2 ^ 2 * (1 + Real.log T) ^ 14) := h5
      _ = D2 ^ 3 * (1 + Real.log T) ^ 15 := by ring
  have hKT0 : (0 : ℝ) < (K : ℝ) ^ 3 * T ^ ((8 : ℝ) / 7) :=
    mul_pos (pow_pos hKR0 3) (Real.rpow_pos_of_pos hT0 _)
  have hstep2 := mul_lt_mul_of_pos_right hcoef hKT0
  have hstep3 : D2 ^ 3 * (1 + Real.log T) ^ 15 * ((K : ℝ) ^ 3 * T ^ ((8 : ℝ) / 7))
      ≤ T ^ 2 := by
    have h1 : D2 ^ 3 * (1 + Real.log T) ^ 15 * ((K : ℝ) ^ 3 * T ^ ((8 : ℝ) / 7))
        = ((K : ℝ) * (D2 * (1 + Real.log T) ^ 5)) ^ 3 * T ^ ((8 : ℝ) / 7) := by
      ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_right hcube
      (le_of_lt (Real.rpow_pos_of_pos hT0 ((8 : ℝ) / 7)))
    have h3 : T ^ ((6 : ℝ) / 7) * T ^ ((8 : ℝ) / 7) = T ^ ((2 : ℝ)) :=
      rpow_add_eq hT0 (by norm_num)
    have h4 : T ^ ((2 : ℝ)) = T ^ 2 := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc ((K : ℝ) * (D2 * (1 + Real.log T) ^ 5)) ^ 3 * T ^ ((8 : ℝ) / 7)
        ≤ T ^ ((6 : ℝ) / 7) * T ^ ((8 : ℝ) / 7) := h2
      _ = T ^ ((2 : ℝ)) := h3
      _ = T ^ 2 := h4
  rw [hstep1]
  linarith only [hstep2, hstep3]

private theorem no_small_x2 {T D2 CF Y : ℝ} (hT256 : 256 ≤ T) (hCF : 0 ≤ CF)
    (hD2pos : 0 < D2) (_hY2 : 2 ≤ Y) (hY18 : Y ≤ T ^ ((1 : ℝ) / 8))
    (hYbig : 128 * D2 * (CF + 1) * 4624 ^ 5 + 2 ≤ Y)
    (hT27 : T ^ ((2 : ℝ) / 7) ≤ 128 * D2 * (CF + 1) * (1 + Real.log T) ^ 9) :
    False := by
  have hT0 : (0 : ℝ) < T := by linarith only [hT256]
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT256]
  have hL1 : (1 : ℝ) ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1
    linarith only [this]
  have hL0 : (0 : ℝ) < 1 + Real.log T := by linarith only [hL1]
  have hLsq : (1 + Real.log T) ^ 2 ≤ 4624 * T ^ ((1 : ℝ) / 32) := log_sq_le_rpow hT1
  have hDCF : (0 : ℝ) ≤ D2 * (CF + 1) :=
    mul_nonneg (le_of_lt hD2pos) (by linarith only [hCF])
  have hL9 : (1 + Real.log T) ^ 9 ≤ 4624 ^ 5 * T ^ ((5 : ℝ) / 32) := by
    have h1 : (1 + Real.log T) ^ 9 ≤ (1 + Real.log T) ^ 10 :=
      pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : ((1 + Real.log T) ^ 2) ^ 5 ≤ (4624 * T ^ ((1 : ℝ) / 32)) ^ 5 :=
      pow_le_pow_left₀ (by positivity) hLsq 5
    have h3 : ((1 + Real.log T) ^ 2) ^ 5 = (1 + Real.log T) ^ 10 := by ring
    have h4 : (4624 * T ^ ((1 : ℝ) / 32)) ^ 5
        = 4624 ^ 5 * T ^ ((5 : ℝ) / 32) := by
      rw [mul_pow, rpow_pow hT0.le]
      congr 2
      norm_num
    rw [h3, h4] at h2
    linarith only [h1, h2]
  have hcomb : T ^ ((2 : ℝ) / 7)
      ≤ (128 * D2 * (CF + 1) * 4624 ^ 5) * T ^ ((5 : ℝ) / 32) := by
    have hpos : (0 : ℝ) ≤ 128 * D2 * (CF + 1) := by
      have := hDCF
      linarith only [mul_nonneg hDCF (by norm_num : (0:ℝ) ≤ (128:ℝ))]
    calc T ^ ((2 : ℝ) / 7)
        ≤ 128 * D2 * (CF + 1) * (1 + Real.log T) ^ 9 := hT27
      _ ≤ 128 * D2 * (CF + 1) * (4624 ^ 5 * T ^ ((5 : ℝ) / 32)) :=
          mul_le_mul_of_nonneg_left hL9 hpos
      _ = (128 * D2 * (CF + 1) * 4624 ^ 5) * T ^ ((5 : ℝ) / 32) := by ring
  have hsplit2 : T ^ ((29 : ℝ) / 224) * T ^ ((5 : ℝ) / 32) = T ^ ((2 : ℝ) / 7) :=
    rpow_add_eq hT0 (by norm_num)
  have h7 : T ^ ((29 : ℝ) / 224) ≤ 128 * D2 * (CF + 1) * 4624 ^ 5 := by
    have h8 := hcomb
    rw [← hsplit2] at h8
    exact le_of_mul_le_mul_right h8 (Real.rpow_pos_of_pos hT0 _)
  have h9 : Y ≤ T ^ ((29 : ℝ) / 224) := by
    refine le_trans hY18 (rpow_exp_mono hT1 (by norm_num))
  have h10 : 128 * D2 * (CF + 1) * 4624 ^ 5 + 2 ≤ Y := hYbig
  linarith only [h7, h9, h10]

/-- **Two-sevenths many distinct ordinates.**  Unconditionally, at least
`c · T^{2/7} / (1 + log T)⁹` distinct ordinates in `(T, 2T]` carry critical-line zeros,
for all large `T`. -/
theorem exists_many_distinct_line_zeros_dyadic_twoSeventh :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      ∃ τS : Finset ℝ, (∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T ∧ riemannZeta (linePt τ) = 0) ∧
        c * T ^ ((2 : ℝ) / 7) / (1 + Real.log T) ^ 9 ≤ (τS.card : ℝ) := by
  classical
  obtain ⟨TC, hTC0, hC⟩ := exists_le_integral_hardyZ_sq
  obtain ⟨CF, hCF, hF⟩ := exists_integral_hardyZ_pow_four_dyadic_real_le
  obtain ⟨CS, hCS0, hsharp⟩ := exists_abs_integral_hardyZ_window_sharp_le
  set D2 : ℝ := 18432 * (CS ^ 2 + 1) * (CF + 1) + 2 with hD2def
  have hD22 : (2 : ℝ) ≤ D2 := by
    rw [hD2def]
    nlinarith [sq_nonneg CS, hCF]
  have hD2pos : (0 : ℝ) < D2 := by linarith only [hD22]
  set Y : ℝ := 2 * D2 * 4624 ^ 3 + 128 * D2 * (CF + 1) * 4624 ^ 5 + 2 with hYdef
  have hDCF : (0 : ℝ) ≤ D2 * (CF + 1) :=
    mul_nonneg (le_of_lt hD2pos) (by linarith only [hCF])
  have hY2 : (2 : ℝ) ≤ Y := by
    rw [hYdef]
    have h1 : (0 : ℝ) ≤ 2 * D2 * 4624 ^ 3 :=
      mul_nonneg (by linarith only [hD2pos]) (by norm_num)
    have h2 : (0 : ℝ) ≤ 128 * D2 * (CF + 1) * 4624 ^ 5 := by
      have := mul_nonneg hDCF (by norm_num : (0 : ℝ) ≤ 4624 ^ 5)
      linarith only [this]
    linarith only [h1, h2]
  have hYbig : 128 * D2 * (CF + 1) * 4624 ^ 5 + 2 ≤ Y := by
    rw [hYdef]
    have h11 : (0 : ℝ) ≤ 2 * D2 * 4624 ^ 3 :=
      mul_nonneg (by linarith only [hD2pos]) (by norm_num)
    linarith only [h11]
  have hD2big : 18432 * CS ^ 2 * (CF + 1) + 2 ≤ D2 := by
    rw [hD2def]
    linarith only [hCF]
  clear_value D2 Y
  refine ⟨1 / (384 * D2 * (CF + 1) + 1), one_div_pos.mpr (by
      linarith only [mul_nonneg hDCF (by norm_num : (0:ℝ) ≤ (384:ℝ)),
        mul_nonneg (le_of_lt hD2pos) hCF]),
    max (max TC 256) (Y ^ 24), ?_, fun T hT => ?_⟩
  · refine le_trans ?_ (le_max_right _ _)
    exact one_le_pow₀ (by linarith only [hY2])
  have hT256 : (256 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTC : TC ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTY : Y ^ 24 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith only [hT256]
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT256]
  have hL1 : (1 : ℝ) ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1
    linarith only [this]
  have hL0 : (0 : ℝ) < 1 + Real.log T := by linarith only [hL1]
  -- the 24th-root device
  have hroot : Y ≤ T ^ ((1 : ℝ) / 24) := by
    have h1 : ((Y ^ 24 : ℝ)) ^ ((1 : ℝ) / 24) ≤ T ^ ((1 : ℝ) / 24) :=
      Real.rpow_le_rpow (by positivity) hTY (by norm_num)
    have h2 : ((Y ^ 24 : ℝ)) ^ ((1 : ℝ) / 24) = Y := by
      rw [← Real.rpow_natCast Y 24,
        ← Real.rpow_mul (by linarith only [hY2] : (0 : ℝ) ≤ Y),
        show ((24 : ℕ) : ℝ) * ((1 : ℝ) / 24) = 1 by norm_num, Real.rpow_one]
    linarith only [h1, h2.symm.le, h2.le]
  have hY16 : Y ≤ T ^ ((1 : ℝ) / 6) := by
    have ha' : Y ^ 1 ≤ Y ^ 4 := pow_le_pow_right₀ (by linarith only [hY2]) (by norm_num)
    have hb' : Y ^ 4 ≤ (T ^ ((1 : ℝ) / 24)) ^ 4 :=
      pow_le_pow_left₀ (by linarith only [hY2]) hroot 4
    have hc' : (T ^ ((1 : ℝ) / 24)) ^ 4 = T ^ ((4 : ℝ) / 24) := by
      rw [rpow_pow hT0.le]
      congr 1
      norm_num
    rw [pow_one] at ha'
    have hd' : T ^ ((4 : ℝ) / 24) = T ^ ((1 : ℝ) / 6) := by
      congr 1
      norm_num
    linarith only [ha', hb', hc'.le, hc'.ge, hd'.le, hd'.ge]
  have hY18 : Y ≤ T ^ ((1 : ℝ) / 8) := by
    have ha' : Y ^ 1 ≤ Y ^ 3 := pow_le_pow_right₀ (by linarith only [hY2]) (by norm_num)
    have hb' : Y ^ 3 ≤ (T ^ ((1 : ℝ) / 24)) ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hY2]) hroot 3
    have hc' : (T ^ ((1 : ℝ) / 24)) ^ 3 = T ^ ((3 : ℝ) / 24) := by
      rw [rpow_pow hT0.le]
      congr 1
      norm_num
    rw [pow_one] at ha'
    have hd' : T ^ ((3 : ℝ) / 24) = T ^ ((1 : ℝ) / 8) := by
      congr 1
      norm_num
    linarith only [ha', hb', hc'.le, hc'.ge, hd'.le, hd'.ge]
  have hLsq : (1 + Real.log T) ^ 2 ≤ 4624 * T ^ ((1 : ℝ) / 32) := log_sq_le_rpow hT1
  have hL5T : (1 + Real.log T) ^ 5 ≤ 4624 ^ 3 * T ^ ((3 : ℝ) / 32) := by
    have h1 : (1 + Real.log T) ^ 5 ≤ (1 + Real.log T) ^ 6 :=
      pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : ((1 + Real.log T) ^ 2) ^ 3 ≤ (4624 * T ^ ((1 : ℝ) / 32)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hLsq 3
    have h3 : ((1 + Real.log T) ^ 2) ^ 3 = (1 + Real.log T) ^ 6 := by ring
    have h4 : (4624 * T ^ ((1 : ℝ) / 32)) ^ 3
        = 4624 ^ 3 * T ^ ((3 : ℝ) / 32) := by
      rw [mul_pow, rpow_pow hT0.le]
      congr 2
      norm_num
    rw [h3, h4] at h2
    linarith only [h1, h2]
  -- the window count
  set x2 : ℝ := T ^ ((2 : ℝ) / 7) / (D2 * (1 + Real.log T) ^ 5) with hx2def
  have hDL5pos : (0 : ℝ) < D2 * (1 + Real.log T) ^ 5 := mul_pos hD2pos (pow_pos hL0 5)
  have hx20 : 0 < x2 := div_pos (Real.rpow_pos_of_pos hT0 _) hDL5pos
  have hx22 : (2 : ℝ) ≤ x2 := by
    rw [hx2def, le_div_iff₀ hDL5pos]
    have h1 : 2 * (D2 * (1 + Real.log T) ^ 5)
        ≤ 2 * D2 * (4624 ^ 3 * T ^ ((3 : ℝ) / 32)) := by
      have h2 := mul_le_mul_of_nonneg_left hL5T
        (by linarith only [hD2pos] : (0 : ℝ) ≤ 2 * D2)
      calc 2 * (D2 * (1 + Real.log T) ^ 5)
          = 2 * D2 * (1 + Real.log T) ^ 5 := by ring
        _ ≤ 2 * D2 * (4624 ^ 3 * T ^ ((3 : ℝ) / 32)) := h2
    have h3 : 2 * D2 * (4624 ^ 3 * T ^ ((3 : ℝ) / 32))
        ≤ T ^ ((1 : ℝ) / 6) * T ^ ((3 : ℝ) / 32) := by
      have h4 : 2 * D2 * 4624 ^ 3 ≤ Y := by
        rw [hYdef]
        have := mul_nonneg hDCF (by norm_num : (0 : ℝ) ≤ 4624 ^ 5)
        linarith only [this]
      have h5 : 2 * D2 * 4624 ^ 3 ≤ T ^ ((1 : ℝ) / 6) := le_trans h4 hY16
      have h6 := mul_le_mul_of_nonneg_right h5
        (le_of_lt (Real.rpow_pos_of_pos hT0 ((3 : ℝ) / 32)))
      calc 2 * D2 * (4624 ^ 3 * T ^ ((3 : ℝ) / 32))
          = 2 * D2 * 4624 ^ 3 * T ^ ((3 : ℝ) / 32) := by ring
        _ ≤ T ^ ((1 : ℝ) / 6) * T ^ ((3 : ℝ) / 32) := h6
    have h7 : T ^ ((1 : ℝ) / 6) * T ^ ((3 : ℝ) / 32) = T ^ ((25 : ℝ) / 96) :=
      rpow_add_eq hT0 (by norm_num)
    have h8 : T ^ ((25 : ℝ) / 96) ≤ T ^ ((2 : ℝ) / 7) :=
      rpow_exp_mono hT1 (by norm_num)
    linarith only [h1, h3, h7.le, h7.ge, h8]
  set K : ℕ := ⌊x2⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by
    exact_mod_cast (by linarith only [hx22] : (1 : ℝ) ≤ x2))
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR0
  have hKle : (K : ℝ) ≤ x2 := Nat.floor_le hx20.le
  have hKge : x2 / 2 ≤ (K : ℝ) := by
    have h1 : x2 < (K : ℝ) + 1 := Nat.lt_floor_add_one x2
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith only [h1, h2, hx22]
  have hTK0 : (0 : ℝ) < T / K := div_pos hT0 hKR0
  have hxK : x2 ≤ 2 * (K : ℝ) := by linarith only [hKge]
  have hxval : T ^ ((2 : ℝ) / 7) = x2 * (D2 * (1 + Real.log T) ^ 5) := by
    rw [hx2def, div_mul_cancel₀ _ (ne_of_gt hDL5pos)]
  have hKD : (K : ℝ) * (D2 * (1 + Real.log T) ^ 5) ≤ T ^ ((2 : ℝ) / 7) := by
    rw [hxval]
    exact mul_le_mul_of_nonneg_right hKle (le_of_lt hDL5pos)
  -- the uniform window mean
  have hTKle : T / (K : ℝ) ≤ 2 * (D2 * (1 + Real.log T) ^ 5) * T ^ ((5 : ℝ) / 7) := by
    rw [div_le_iff₀ hKR0]
    have h1 : T = T ^ ((5 : ℝ) / 7) * T ^ ((2 : ℝ) / 7) :=
      ((rpow_add_eq hT0 (by norm_num : (5 : ℝ) / 7 + 2 / 7 = 1)).trans
        (Real.rpow_one T)).symm
    have h2 : T ^ ((2 : ℝ) / 7) ≤ 2 * (K : ℝ) * (D2 * (1 + Real.log T) ^ 5) := by
      rw [hxval]
      exact mul_le_mul_of_nonneg_right hxK (le_of_lt hDL5pos)
    have h4 := mul_le_mul_of_nonneg_left h2
      (le_of_lt (Real.rpow_pos_of_pos hT0 ((5 : ℝ) / 7)))
    calc T = T ^ ((5 : ℝ) / 7) * T ^ ((2 : ℝ) / 7) := h1
      _ ≤ T ^ ((5 : ℝ) / 7) * (2 * (K : ℝ) * (D2 * (1 + Real.log T) ^ 5)) := h4
      _ = 2 * (D2 * (1 + Real.log T) ^ 5) * T ^ ((5 : ℝ) / 7) * (K : ℝ) := by ring
  set E : ℝ := 6 * CS * D2 * (1 + Real.log T) ^ 5 * T ^ ((4 : ℝ) / 7) with hEdef
  have hEwin : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ| ≤ E :=
    window_mean_le hT256 hCS0 hD22 hK1 (fun {a b x} => hsharp) hTKle
  -- the moment gap
  have hE0 : (0 : ℝ) ≤ E := by
    rw [hEdef]
    have := mul_nonneg (mul_nonneg (mul_nonneg
      (by linarith only [hCS0] : (0 : ℝ) ≤ 6 * CS) (le_of_lt hD2pos))
      (le_of_lt (pow_pos hL0 5))) (le_of_lt (Real.rpow_pos_of_pos hT0 ((4 : ℝ) / 7)))
    linarith only [this]
  have hkey : 512 * (K : ℝ) ^ 3 * E ^ 2 * ((CF + 1) * (1 + Real.log T) ^ 4)
      < T ^ 2 := by
    rw [hEdef]
    exact key_lt hT256 hCF hK1 hD2big hKD
  have hgap := gap_of_bound hT0 hK1 hkey
  set M4 : ℝ := (CF + 1) * T * (1 + Real.log T) ^ 4 with hM4def
  have hM40 : 0 < M4 := by
    rw [hM4def]
    exact mul_pos (mul_pos (by linarith only [hCF] : (0 : ℝ) < CF + 1) hT0)
      (pow_pos hL0 4)
  have hCdyadic := hC T hTTC
  have hM4dyadic : (∫ τ in T..(2 * T), (hardyZ τ) ^ 4) ≤ M4 := by
    refine le_trans (hF (by linarith only [hT256])) ?_
    rw [hM4def]
    have h1 : (0 : ℝ) ≤ T * (1 + Real.log T) ^ 4 :=
      mul_nonneg hT0.le (le_of_lt (pow_pos hL0 4))
    linarith only [h1]
  have hgap' : E ^ 2 * M4 < (T / (8 * (K : ℝ))) ^ 3 := by
    rw [hM4def]
    have h1 : E ^ 2 * ((CF + 1) * T * (1 + Real.log T) ^ 4)
        = E ^ 2 * ((CF + 1) * (1 + Real.log T) ^ 4) * T := by ring
    have h2 : E ^ 2 * ((CF + 1) * (1 + Real.log T) ^ 4) * T
        = E ^ 2 * ((CF + 1) * T * (1 + Real.log T) ^ 4) := by ring
    exact hgap
  obtain ⟨S, hSzero, hScount⟩ :=
    exists_heavyFinset_sq hK1 hT0 hM40 hCdyadic hM4dyadic hEwin hgap'
  obtain ⟨τS, hτSmem, hτScard⟩ := exists_distinct_ordinates hT0 hK1 S hSzero
  refine ⟨τS, hτSmem, ?_⟩
  -- counting
  have hcard : (K : ℝ) ≤ 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := by
    have h1 : (T / 8) ^ 2 * (K : ℝ) ≤ (S.card : ℝ) * ((T / K) * M4) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hScount hKR0.le
    have h2 : (S.card : ℝ) * ((T / K) * M4) * (K : ℝ) = (S.card : ℝ) * (T * M4) := by
      have hTK : T / K * (K : ℝ) = T := div_mul_cancel₀ T hKne
      calc (S.card : ℝ) * ((T / K) * M4) * (K : ℝ)
          = (S.card : ℝ) * M4 * (T / K * (K : ℝ)) := by ring
        _ = (S.card : ℝ) * M4 * T := by rw [hTK]
        _ = (S.card : ℝ) * (T * M4) := by ring
    have h3 : (T / 8) ^ 2 * (K : ℝ) = T ^ 2 * ((K : ℝ) / 64) := by ring
    rw [h2, h3] at h1
    have h4 : (S.card : ℝ) * (T * M4)
        = T ^ 2 * ((S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4) := by
      rw [hM4def]
      ring
    rw [h4] at h1
    have h5 := le_of_mul_le_mul_left h1 (pow_pos hT0 2)
    linarith only [h5]
  have himg1 : (1 : ℝ) ≤ (τS.card : ℝ) := by
    by_contra h0
    have h0lt : (τS.card : ℝ) < 1 := not_le.mp h0
    have h0' : τS.card = 0 := by
      by_contra h1
      have h2 : 1 ≤ τS.card := Nat.one_le_iff_ne_zero.mpr h1
      have h3 : (1 : ℝ) ≤ (τS.card : ℝ) := by exact_mod_cast h2
      linarith only [h0lt, h3]
    have h1 : (S.card : ℝ) ≤ 2 * (τS.card : ℝ) + 1 := by exact_mod_cast hτScard
    have h1' : ((τS.card : ℕ) : ℝ) = 0 := by exact_mod_cast h0'
    rw [h1'] at h1
    have hS1 : (S.card : ℝ) ≤ 1 := by linarith only [h1]
    have hK64 : (K : ℝ) ≤ 64 * (CF + 1) * (1 + Real.log T) ^ 4 := by
      have hpos : (0 : ℝ) ≤ 64 * ((CF + 1) * (1 + Real.log T) ^ 4) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (by linarith only [hCF]) (le_of_lt (pow_pos hL0 4)))
      have h4 := mul_le_mul_of_nonneg_right hS1 hpos
      calc (K : ℝ) ≤ 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := hcard
        _ = (S.card : ℝ) * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := by ring
        _ ≤ 1 * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := h4
        _ = 64 * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
    have hxb : x2 ≤ 128 * (CF + 1) * (1 + Real.log T) ^ 4 := by
      calc x2 ≤ 2 * (K : ℝ) := hxK
        _ ≤ 2 * (64 * (CF + 1) * (1 + Real.log T) ^ 4) := by linarith only [hK64]
        _ = 128 * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
    have hT27 : T ^ ((2 : ℝ) / 7)
        ≤ 128 * D2 * (CF + 1) * (1 + Real.log T) ^ 9 := by
      have h2 := mul_le_mul_of_nonneg_right hxb (le_of_lt hDL5pos)
      calc T ^ ((2 : ℝ) / 7) = x2 * (D2 * (1 + Real.log T) ^ 5) := hxval
        _ ≤ 128 * (CF + 1) * (1 + Real.log T) ^ 4
            * (D2 * (1 + Real.log T) ^ 5) := h2
        _ = 128 * D2 * (CF + 1) * (1 + Real.log T) ^ 9 := by ring
    exact no_small_x2 hT256 hCF hD2pos hY2 hY18 hYbig hT27

  have hcard3 : (S.card : ℝ) ≤ 3 * (τS.card : ℝ) := by
    have h1 : (S.card : ℝ) ≤ 2 * (τS.card : ℝ) + 1 := by exact_mod_cast hτScard
    linarith only [h1, himg1]
  have hxbound : x2 ≤ 384 * (τS.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := by
    have hpos : (0 : ℝ) ≤ 64 * ((CF + 1) * (1 + Real.log T) ^ 4) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (by linarith only [hCF]) (le_of_lt (pow_pos hL0 4)))
    have h3 := mul_le_mul_of_nonneg_right hcard3 hpos
    have h2 : 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4
        ≤ 64 * (3 * (τS.card : ℝ)) * (CF + 1) * (1 + Real.log T) ^ 4 := by
      calc 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4
          = (S.card : ℝ) * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := by ring
        _ ≤ 3 * (τS.card : ℝ) * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := h3
        _ = 64 * (3 * (τS.card : ℝ)) * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
    calc x2 ≤ 2 * (K : ℝ) := hxK
      _ ≤ 2 * (64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4) := by
          linarith only [hcard]
      _ ≤ 2 * (64 * (3 * (τS.card : ℝ)) * (CF + 1) * (1 + Real.log T) ^ 4) := by
          linarith only [h2]
      _ = 384 * (τS.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
  have hfinal2 : T ^ ((2 : ℝ) / 7)
      ≤ 384 * D2 * (CF + 1) * (τS.card : ℝ) * (1 + Real.log T) ^ 9 := by
    have h2 := mul_le_mul_of_nonneg_right hxbound (le_of_lt hDL5pos)
    calc T ^ ((2 : ℝ) / 7) = x2 * (D2 * (1 + Real.log T) ^ 5) := hxval
      _ ≤ 384 * (τS.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4
          * (D2 * (1 + Real.log T) ^ 5) := h2
      _ = 384 * D2 * (CF + 1) * (τS.card : ℝ) * (1 + Real.log T) ^ 9 := by ring
  rw [div_le_iff₀ (pow_pos hL0 9), div_mul_eq_mul_div, one_mul,
    div_le_iff₀ (by
      linarith only [mul_nonneg hDCF (by norm_num : (0:ℝ) ≤ (384:ℝ)),
        mul_nonneg (le_of_lt hD2pos) hCF] :
      (0 : ℝ) < 384 * D2 * (CF + 1) + 1)]
  have hcl : (0 : ℝ) ≤ (τS.card : ℝ) * (1 + Real.log T) ^ 9 :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos hL0 9))
  calc T ^ ((2 : ℝ) / 7)
      ≤ 384 * D2 * (CF + 1) * (τS.card : ℝ) * (1 + Real.log T) ^ 9 := hfinal2
    _ ≤ (τS.card : ℝ) * (1 + Real.log T) ^ 9 * (384 * D2 * (CF + 1) + 1) := by
        linarith only [hcl]

/-- **Two-sevenths census difference.**  Unconditionally, the number of critical-line zeros
of `xi` with ordinate in `(T, 2T]`, counted with multiplicity, is at least
`c · T^{2/7} / (1 + log T)⁹` for all large `T`. -/
theorem exists_twoSeventhRoot_le_xiPosCriticalZeroCount_sub :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * T ^ ((2 : ℝ) / 7) / (1 + Real.log T) ^ 9
        ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) - (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_many_distinct_line_zeros_dyadic_twoSeventh
  refine ⟨c, hc, T₁, hT₁, fun T hT => ?_⟩
  obtain ⟨τS, hmemS, hcard⟩ := h T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hinj := xiPosCriticalZeroCount_add_card_le hT0 τS hmemS
  have hcast : (xiPosCriticalZeroCount T : ℝ) + (τS.card : ℝ)
      ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) := by exact_mod_cast hinj
  linarith only [hcard, hcast]

/-- **The two-sevenths critical-line census.**  Unconditionally, the number of critical-line
zeros of `xi` with ordinate in `(0, T]`, counted with multiplicity, is at least
`c · T^{2/7} / (1 + log T)⁹` for all large `T` — the window-pigeonhole census at the
resonance-graded window mean. -/
theorem exists_twoSeventhRoot_le_xiPosCriticalZeroCount :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * T ^ ((2 : ℝ) / 7) / (1 + Real.log T) ^ 9
        ≤ (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_twoSeventhRoot_le_xiPosCriticalZeroCount_sub
  refine ⟨c / 2, by positivity, max (2 * T₁) 2, ?_, fun T hT => ?_⟩
  · have h1 := le_max_right (2 * T₁) 2
    linarith
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT20 : (0 : ℝ) < T / 2 := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hhalf : T₁ ≤ T / 2 := by
    have h1 := le_trans (le_max_left (2 * T₁) 2) hT
    linarith
  have hspec := h (T / 2) hhalf
  rw [show 2 * (T / 2) = T by ring] at hspec
  have hl1 : (0 : ℝ) ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (T / 2) ≤ Real.log T := Real.log_le_log hT20 (by linarith)
  have hp1 : (0 : ℝ) < 1 + Real.log (T / 2) := by linarith
  have hp2 : (0 : ℝ) < 1 + Real.log T := by linarith
  have hlogc : (1 + Real.log (T / 2)) ^ 9 ≤ (1 + Real.log T) ^ 9 :=
    pow_le_pow_left₀ hp1.le (by linarith) 9
  have hchain : T ^ ((2 : ℝ) / 7) ≤ 2 * (T / 2) ^ ((2 : ℝ) / 7) := by
    have h1 : T = 2 * (T / 2) := by ring
    have h2 : T ^ ((2 : ℝ) / 7) = 2 ^ ((2 : ℝ) / 7) * (T / 2) ^ ((2 : ℝ) / 7) := by
      calc T ^ ((2 : ℝ) / 7) = (2 * (T / 2)) ^ ((2 : ℝ) / 7) := by rw [← h1]
        _ = 2 ^ ((2 : ℝ) / 7) * (T / 2) ^ ((2 : ℝ) / 7) :=
            Real.mul_rpow (by norm_num) hT20.le
    have h3 : (2 : ℝ) ^ ((2 : ℝ) / 7) ≤ 2 := by
      have h4 : (2 : ℝ) ^ ((2 : ℝ) / 7) ≤ 2 ^ ((1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rwa [Real.rpow_one] at h4
    have h5 : (0 : ℝ) ≤ (T / 2) ^ ((2 : ℝ) / 7) := Real.rpow_nonneg hT20.le _
    calc T ^ ((2 : ℝ) / 7) = 2 ^ ((2 : ℝ) / 7) * (T / 2) ^ ((2 : ℝ) / 7) := h2
      _ ≤ 2 * (T / 2) ^ ((2 : ℝ) / 7) := mul_le_mul_of_nonneg_right h3 h5
  have hfinal : c / 2 * T ^ ((2 : ℝ) / 7) / (1 + Real.log T) ^ 9
      ≤ c * (T / 2) ^ ((2 : ℝ) / 7) / (1 + Real.log (T / 2)) ^ 9 := by
    have hq1 : (0 : ℝ) < (1 + Real.log T) ^ 9 := pow_pos hp2 9
    have hq2 : (0 : ℝ) < (1 + Real.log (T / 2)) ^ 9 := pow_pos hp1 9
    rw [div_le_div_iff₀ hq1 hq2]
    have hprod : T ^ ((2 : ℝ) / 7) * (1 + Real.log (T / 2)) ^ 9
        ≤ (2 * (T / 2) ^ ((2 : ℝ) / 7)) * (1 + Real.log T) ^ 9 :=
      mul_le_mul hchain hlogc hq2.le (by positivity)
    have hscale := mul_le_mul_of_nonneg_left hprod
      (by positivity : (0 : ℝ) ≤ c / 2)
    calc c / 2 * T ^ ((2 : ℝ) / 7) * (1 + Real.log (T / 2)) ^ 9
        = c / 2 * (T ^ ((2 : ℝ) / 7) * (1 + Real.log (T / 2)) ^ 9) := by ring
      _ ≤ c / 2 * ((2 * (T / 2) ^ ((2 : ℝ) / 7)) * (1 + Real.log T) ^ 9) := hscale
      _ = c * (T / 2) ^ ((2 : ℝ) / 7) * (1 + Real.log T) ^ 9 := by ring
  have hcnn : (0 : ℝ) ≤ (xiPosCriticalZeroCount (T / 2) : ℝ) := Nat.cast_nonneg _
  calc c / 2 * T ^ ((2 : ℝ) / 7) / (1 + Real.log T) ^ 9
      ≤ c * (T / 2) ^ ((2 : ℝ) / 7) / (1 + Real.log (T / 2)) ^ 9 := hfinal
    _ ≤ (xiPosCriticalZeroCount T : ℝ) - (xiPosCriticalZeroCount (T / 2) : ℝ) := hspec
    _ ≤ (xiPosCriticalZeroCount T : ℝ) := by linarith only [hcnn]

end

end RHTower
