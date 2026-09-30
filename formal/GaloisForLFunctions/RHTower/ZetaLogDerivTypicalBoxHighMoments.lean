import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxDensity
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments

/-!
# Typical `ζ'/ζ` box bound at one scale, through high moments of the prime part

The large values of `D_x` near the box `1/2 + 3R/4 ≤ Re ≤ 1/2 + 6R`, `|Im − t| ≤ 6R` are large values
of its prime part `P_x` once `96/R ≤ M`, because the proper prime powers contribute at most `48/R`
there (`largeNearBox_selbergVonMangoldtPoly_subset_prime`). The `m`-th moment of `P_x`, for
`1 ≤ m ≤ 7500` and `x = T^{1/30000}` (so that `N_x^m ≤ T^{1/2}`), then bounds the exceptional
heights of the box bound at level `ε log T` by

`C T (e^{−κ/120000}/ε + m! (1280/(ε²κ²))^m) + C T^{1/2}`,   `κ = R log T ≥ max(30000, 384/ε)`

(`exists_volume_not_zetaLogDerivScaleData_le_pow`), in place of the rate `1/(ε²κ²)` of the mean
square.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- **Large values of `D_x` near the box are large values of the prime part.** -/
theorem largeNearBox_selbergVonMangoldtPoly_subset_prime {T x R M : ℝ} (hx : 1 < x) (hR : 0 < R)
    (hR16 : R ≤ 1 / 16) (hM : 96 / R ≤ M) :
    largeNearBox (selbergVonMangoldtPoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R M ⊆
      largeNearBox (selbergPrimePoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R (M / 2) := by
  rintro t ⟨ht, z, h1, h2, h3, hz⟩
  refine ⟨ht, z, h1, h2, h3, ?_⟩
  have hH := norm_selbergPrimePowerPoly_le hx (δ := 3 * R / 4) (by positivity) (by linarith) h1
  have e : 36 / (3 * R / 4) = 48 / R := by field_simp; ring
  rw [e] at hH
  rw [selbergVonMangoldtPoly_eq_prime_add hx] at hz
  have htri := norm_add_le (selbergPrimePoly x z) (selbergPrimePowerPoly x z)
  have h48 : 48 / R = 96 / R / 2 := by ring
  linarith

/-- The length term of the `m`-th moment: `8N^m(1 + log N^m) ≤ T` for `x = T^{1/30000}`,
`N = ⌈x²⌉` and `m ≤ 7500`. -/
theorem polyLength_pow_term_le {T : ℝ} {m : ℕ} (hT : 1 < T) (hm : m ≤ 7500)
    (h : 8 * 2 ^ m * (1 + (m : ℝ)) * (Real.log T + 3) ^ 1 ≤ Real.exp (1 / 2 * Real.log T)) :
    8 * ((selbergPolyLength (Real.exp (Real.log T / 30000)) ^ m : ℕ) : ℝ) *
      (1 + Real.log ((selbergPolyLength (Real.exp (Real.log T / 30000)) ^ m : ℕ) : ℝ)) ≤ T := by
  set L := Real.log T with hL
  have hL0 : 0 < L := Real.log_pos hT
  set x := Real.exp (L / 30000) with hx
  set N := selbergPolyLength x with hN
  have hx2 : x ^ 2 = Real.exp (L / 15000) := by
    rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hNle : (N : ℝ) ≤ 2 * Real.exp (L / 15000) := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x ^ 2 by positivity)
    have hx21 : 1 ≤ x ^ 2 := by rw [hx2]; exact Real.one_le_exp (by positivity)
    rw [hN, selbergPolyLength, ← hx2]
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN, selbergPolyLength]
    have hx21 : 1 ≤ x ^ 2 := by rw [hx2]; exact Real.one_le_exp (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      rw [Nat.ceil_eq_zero] at h0
      linarith)
  have hlogN : Real.log N ≤ 1 + L / 15000 := by
    have h1 : Real.log N ≤ Real.log (2 * Real.exp (L / 15000)) :=
      Real.log_le_log (by linarith) hNle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at h1
    have := Real.log_two_lt_d9
    linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmL : (m : ℝ) ≤ 7500 := by exact_mod_cast hm
  rw [Nat.cast_pow, Real.log_pow]
  have hNm : (N : ℝ) ^ m ≤ 2 ^ m * Real.exp (1 / 2 * L) := by
    calc (N : ℝ) ^ m ≤ (2 * Real.exp (L / 15000)) ^ m :=
          pow_le_pow_left₀ (by linarith) hNle m
      _ = 2 ^ m * Real.exp (m * (L / 15000)) := by rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ 2 ^ m * Real.exp (1 / 2 * L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have : (m : ℝ) * (L / 15000) ≤ 7500 * (L / 15000) :=
            mul_le_mul_of_nonneg_right hmL (by positivity)
          linarith
  have hlog : 1 + (m : ℝ) * Real.log N ≤ (1 + m) * (L + 3) := by
    have : (m : ℝ) * Real.log N ≤ m * (1 + L / 15000) := mul_le_mul_of_nonneg_left hlogN hm0
    nlinarith
  have hT' : T = Real.exp (1 / 2 * L) * Real.exp (1 / 2 * L) := by
    rw [← Real.exp_add, show 1 / 2 * L + 1 / 2 * L = L by ring, hL, Real.exp_log (by linarith)]
  rw [pow_one] at h
  have hNm0 : 0 ≤ (N : ℝ) ^ m := by positivity
  calc 8 * (N : ℝ) ^ m * (1 + (m : ℝ) * Real.log N)
      ≤ 8 * (2 ^ m * Real.exp (1 / 2 * L)) * ((1 + m) * (L + 3)) :=
        mul_le_mul (by linarith) hlog (by positivity) (by positivity)
    _ = 8 * 2 ^ m * (1 + (m : ℝ)) * (L + 3) * Real.exp (1 / 2 * L) := by ring
    _ ≤ Real.exp (1 / 2 * L) * Real.exp (1 / 2 * L) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = T := hT'.symm

/-- The prime-part term at level `εL/8`. -/
theorem primePoly_term_le {T L R ε Nm : ℝ} {m : ℕ} (hT : 64 ≤ T) (hL0 : 0 < L) (hR : 0 < R)
    (hR16 : R ≤ 1 / 16) (hε : 0 < ε) (hN : Nm ≤ T) :
    1380 * (m.factorial * (20 / R ^ 2) ^ m * (T + 17 * R + Nm)) /
        (Real.pi * ((ε * L / 4 / 2) ^ m) ^ 2) ≤
      4140 / Real.pi * T * (m.factorial * (1280 / (ε ^ 2 * (R * L) ^ 2)) ^ m) := by
  have hsum : T + 17 * R + Nm ≤ 3 * T := by linarith
  have hB : 0 < ((ε * L / 4 / 2) ^ 2) ^ m := by positivity
  have e1 : ((ε * L / 4 / 2) ^ m) ^ 2 = ((ε * L / 4 / 2) ^ 2) ^ m := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have e2 : (20 / R ^ 2) ^ m / ((ε * L / 4 / 2) ^ 2) ^ m = (1280 / (ε ^ 2 * (R * L) ^ 2)) ^ m := by
    rw [← div_pow]; congr 1; field_simp; ring
  rw [e1, ← e2]
  set A := (20 / R ^ 2) ^ m with hA
  set B := ((ε * L / 4 / 2) ^ 2) ^ m with hBdef
  have hA0 : 0 ≤ A := by positivity
  have e3 : 1380 * (m.factorial * A * (T + 17 * R + Nm)) / (Real.pi * B) =
      1380 / Real.pi * (m.factorial * (A / B)) * (T + 17 * R + Nm) := by
    field_simp
  have e4 : 4140 / Real.pi * T * (m.factorial * (A / B)) =
      1380 / Real.pi * (m.factorial * (A / B)) * (3 * T) := by ring
  rw [e3, e4]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Combination of the four terms. -/
theorem four_terms_combine_pow {a b c d A Cb Cc T E ε P s : ℝ} (hA : 0 ≤ A) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (hT : 0 ≤ T) (hE : 0 ≤ E) (hε : 0 < ε) (hs : 0 ≤ s) (hP : 0 ≤ P)
    (ha : a ≤ 336 * A / Real.pi * T * (E / ε) + s) (hb : b ≤ Cb * T * (E / ε))
    (hc : c ≤ Cc * T * (E / ε)) (hd : d ≤ 4140 / Real.pi * T * P) :
    a + b + c + d ≤ (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * T * (E / ε + P) +
      (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * s := by
  have hp : 0 ≤ 336 * A / Real.pi := by positivity
  have hq : 0 ≤ 4140 / Real.pi := by positivity
  have hTE : 0 ≤ T * (E / ε) := by positivity
  have hTP : 0 ≤ T * P := by positivity
  have k1 : (336 * A / Real.pi + Cb + Cc) * (T * (E / ε)) ≤
      (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * (T * (E / ε)) :=
    mul_le_mul_of_nonneg_right (by linarith) hTE
  have k2 : 4140 / Real.pi * (T * P) ≤
      (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * (T * P) :=
    mul_le_mul_of_nonneg_right (by linarith) hTP
  have k3 : 1 * s ≤ (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * s :=
    mul_le_mul_of_nonneg_right (by linarith) hs
  have e1 : 336 * A / Real.pi * T * (E / ε) + Cb * T * (E / ε) + Cc * T * (E / ε) =
      (336 * A / Real.pi + Cb + Cc) * (T * (E / ε)) := by ring
  have e2 : 4140 / Real.pi * T * P = 4140 / Real.pi * (T * P) := by ring
  have e3 : (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * T * (E / ε + P) =
      (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * (T * (E / ε)) +
      (336 * A / Real.pi + Cb + Cc + 4140 / Real.pi + 1) * (T * P) := by ring
  rw [e3]
  linarith

/-- The four exceptional measures at one scale, with the prime part at the `m`-th moment. -/
theorem scale_terms_pow_le {T L R ε A Kw C₀ x S : ℝ} {m : ℕ} (hT64 : 64 ≤ T) (hL : Real.log T = L)
    (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hκ : 30000 ≤ R * L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : 0 < A) (hC₀ : 0 < C₀) (hx : x = Real.exp (L / 30000)) (hm : m ≤ 7500)
    (hE5 : 144 * Kw / Real.pi * (L + 3) ^ 2 ≤ Real.exp ((1 / 2 - 1 / 10000) * L))
    (hE6 : 8 * 2 ^ m * (1 + (m : ℝ)) * (Real.log T + 3) ^ 1 ≤ Real.exp (1 / 2 * Real.log T))
    (hS0 : 0 ≤ S)
    (hS : S ≤ 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) +
      144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi) :
    ENNReal.ofReal S +
        ENNReal.ofReal (4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
          (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153))) +
        ENNReal.ofReal (4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
          (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4)) +
        ENNReal.ofReal (1380 * (m.factorial * (20 / R ^ 2) ^ m *
          (T + 17 * R + 8 * (selbergPolyLength x ^ m : ℕ) *
            (1 + Real.log (selbergPolyLength x ^ m : ℕ)))) /
          (Real.pi * ((ε * L / 4 / 2) ^ m) ^ 2)) ≤
      ENNReal.ofReal ((336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ +
          1600000 * Real.pi * C₀ + 4140 / Real.pi + 1) * T *
          (Real.exp (-(R * L / 120000)) / ε +
            m.factorial * (1280 / (ε ^ 2 * (R * L) ^ 2)) ^ m) +
        (336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ + 1600000 * Real.pi * C₀ +
          4140 / Real.pi + 1) * T ^ ((1 : ℝ) / 2)) := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by rw [← hL]; exact Real.log_pos (by linarith)
  have hlx : Real.log x = L / 30000 := by rw [hx, Real.log_exp]
  have hx1 : 1 < x := by rw [hx]; exact Real.one_lt_exp_iff.mpr (by positivity)
  have hlx0 := Real.log_pos hx1
  have hκ1 : 1 ≤ R * L := by linarith
  have hΦ0 : 0 ≤ Real.log (4 * T + 5) := Real.log_nonneg (by linarith)
  have hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L := by
    have h1 : Real.log (4 * T + 5) ≤ 2 * L := by
      have : Real.log (4 * T + 5) ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow, hL] at this
      push_cast at this
      linarith
    have h3 : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ C₀ * (5 * T) * (2 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₀.le) h1 hΦ0 (by positivity)
    linarith
  have ha := window_term_le hT0 hL hκ hε hε1 hA hlx hE5 hS
  have hb := lorentz_term_le (x := x) hT0 hL0 hR hε hC₀ hκ1 hlx hΦ
  have hc := far_term_le (x := x) hT0 hL0 hR hε hC₀ hκ1 hlx hΦ hΦ0
  have hN := polyLength_pow_term_le (by linarith) hm hE6
  rw [hL, ← hx] at hN
  have hd := primePoly_term_le (m := m) hT64 hL0 hR hR16 hε hN
  have hN0 : 0 ≤ ((selbergPolyLength x ^ m : ℕ) : ℝ) *
      (1 + Real.log (selbergPolyLength x ^ m : ℕ)) := by
    rcases Nat.eq_zero_or_pos (selbergPolyLength x ^ m) with h0 | hpos
    · rw [h0]; simp
    · have := Real.log_nonneg (show (1 : ℝ) ≤ (selbergPolyLength x ^ m : ℕ) by
        exact_mod_cast hpos)
      positivity
  have hnb : 0 ≤ 4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
      (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153)) := by positivity
  have hnc : 0 ≤ 4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
      (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4) := by positivity
  have hnd0 : 0 ≤ T + 17 * R + 8 * ((selbergPolyLength x ^ m : ℕ) : ℝ) *
      (1 + Real.log (selbergPolyLength x ^ m : ℕ)) := by
    have : 0 ≤ 8 * (((selbergPolyLength x ^ m : ℕ) : ℝ) *
        (1 + Real.log (selbergPolyLength x ^ m : ℕ))) := by positivity
    rw [← mul_assoc] at this
    linarith
  have hnd : 0 ≤ 1380 * (m.factorial * (20 / R ^ 2) ^ m *
      (T + 17 * R + 8 * ((selbergPolyLength x ^ m : ℕ) : ℝ) *
        (1 + Real.log (selbergPolyLength x ^ m : ℕ)))) / (Real.pi * ((ε * L / 4 / 2) ^ m) ^ 2) := by
    positivity
  rw [← ENNReal.ofReal_add hS0 hnb, ← ENNReal.ofReal_add (by positivity) hnc,
    ← ENNReal.ofReal_add (by positivity) hnd]
  exact ENNReal.ofReal_le_ofReal (four_terms_combine_pow hA.le (by positivity) (by positivity)
    hT0.le (Real.exp_pos _).le hε (by positivity) (by positivity) ha hb hc hd)

/-- **Typical `ζ'/ζ` box bound at one scale, at the `m`-th moment.** For `0 < ε ≤ 1` and
`1 ≤ m ≤ 7500` there is `C` such that for all large `T` and every scale `0 < R ≤ 1/16` with
`κ = R log T ≥ max(30000, 384/ε)`, the heights `t ∈ [T, 2T]` without log-derivative scale data at
level `ε log T` have measure `≤ C T (e^{−κ/120000}/ε + m! (1280/(ε²κ²))^m) + C T^{1/2}`. -/
theorem exists_volume_not_zetaLogDerivScaleData_le_pow {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 7500) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → 30000 ≤ R * Real.log T →
      384 / ε ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / ε +
          m.factorial * (1280 / (ε ^ 2 * (R * Real.log T) ^ 2)) ^ m) + C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨KE, hKE, hEFall⟩ := exists_selberg_explicit_formula_at_height
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (eventually_selbergHeightError_le_one hKE)
  obtain ⟨A, Kw, hA, hKw, hwin⟩ := exists_sum_selbergRightWindow_le
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_sum_mult_selbergMidZeros_le
  refine ⟨336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ + 1600000 * Real.pi * C₀ +
    4140 / Real.pi + 1, by positivity, ?_⟩
  have hE2 := eventually_mul_log_add_pow_le_exp 40 1 (show (0 : ℝ) < 1 / 30000 by norm_num)
  have hE3 := Real.tendsto_log_atTop.eventually_ge_atTop (4 / ε)
  have hE5 := eventually_mul_log_add_pow_le_exp 2 (144 * Kw / Real.pi)
    (show (0 : ℝ) < 1 / 2 - 1 / 10000 by norm_num)
  have hE6 := eventually_mul_log_add_pow_le_exp 1 (8 * 2 ^ m * (1 + (m : ℝ)))
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hwin, eventually_ge_atTop (max t₀ 64), hE2, hE3, hE5, hE6] with T hTwin hTt
    hE2 hE3 hE5 hE6
  intro R hR hR16 hκ hκε
  have hT64 : 64 ≤ T := le_of_max_le_right hTt
  set L := Real.log T with hLdef
  have hL4 : 4 ≤ L := le_trans (by rw [le_div_iff₀ hε]; linarith) hE3
  have hL0 : 0 < L := by linarith
  set x := Real.exp (L / 30000) with hxdef
  have hlx : Real.log x = L / 30000 := Real.log_exp _
  have hx : 1 < x := Real.one_lt_exp_iff.mpr (by positivity)
  have hRx : 1 ≤ 36 * R * Real.log x := by
    rw [hlx]
    have : 36 * R * (L / 30000) = 36 * (R * L) / 30000 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    linarith
  have hEF := selberg_explicit_formula_block hEFall ht₀ hT64 (le_of_max_le_left hTt) hx
    (by rw [hxdef, show L / 30000 = 1 / 30000 * L by ring]; linarith)
    (by rw [hlx]; linarith)
  have hcL0 : 0 < 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 := by
    have := Real.log_pos hx; positivity
  have hεL : 0 < ε * L / 4 := by positivity
  have hε4 : 4 ≤ ε * L := by
    have := (div_le_iff₀ hε).mp hE3
    linarith
  have h96 : 96 / R ≤ ε * L / 4 := by
    rw [div_le_iff₀ hR]
    have := (div_le_iff₀ hε).mp hκε
    nlinarith
  refine (volume_not_zetaLogDerivScaleData_le_of_largeNearBox (B := ε * L) (C₀ := C₀)
    (M_D := ε * L / 4) (M_L := ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) /
      Real.log x * 1153)) (M_F := ε * L / 4) hT64 hx hR hR16 hRx hEF (hC₀ T (by linarith))
    (div_pos hεL hcL0) hεL (by rw [mul_div_cancel₀ _ hcL0.ne']; linarith)).trans ?_
  have hD := (measure_mono (largeNearBox_selbergVonMangoldtPoly_subset_prime (T := T) hx hR hR16
    h96)).trans (volume_largeNearBox_selbergPrimePoly_le (by linarith) hx hR hR16
      (by positivity : 0 < ε * L / 4 / 2) hm1)
  refine le_trans (by gcongr) (scale_terms_pow_le hT64 hLdef.symm hR hR16 hκ hε hε1 hA hC₀pos
    hxdef hm hE5 hE6
    (Finset.sum_nonneg fun w _ => by have := selbergRightWindow_pos (x := x) hR w; positivity)
    (hTwin x R hx hR (by linarith) (by linarith) (by
      rw [hlx, show 6 * (L / 30000) / L = 1 / 5000 by field_simp; ring]; norm_num)))

end RHTower
