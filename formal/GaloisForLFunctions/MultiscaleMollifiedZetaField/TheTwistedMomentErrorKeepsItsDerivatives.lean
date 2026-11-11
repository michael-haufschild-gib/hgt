import GaloisForLFunctions.MultiscaleMollifiedZetaField.RealParameterErrorsKeepTheirDerivatives
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTwistedMomentHasPolynomialDerivatives
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTwistedMainTermsHavePolynomialDerivatives

/-!
# Derivatives of the actual twisted-moment error

The error is a difference of two holomorphic displacement families. Their
Cauchy bounds control its curvature and third derivative. Two short real
steps then transfer the proved undifferentiated remainder to both derivatives.
-/

open Complex Filter Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Successive real displacement derivatives of the literal moment remainder. -/
def twistedMomentErrorJet (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  realTwistedMomentJet p q η N w n d - realTwistedMomentMainJet p q η N w n d

/-- The sum of the two explicit Cauchy bounds at the left displacement endpoint. -/
def twistedErrorJetBound (C p q η d : ℝ) (N n : ℕ) : ℝ :=
  (n.factorial : ℝ) * ((q - p + 2 * η) * ((2 + 8 * (q + η + 1)) * N) ^ 2) /
      (1 / 8) ^ n +
    (n.factorial : ℝ) * (C * twistedMainSize p q η N / d) / (d / 2) ^ n

theorem twistedMomentErrorJet_zero {d : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) :
    twistedMomentErrorJet p q η N w 0 d =
      ((twistedMoment d p q η N w : ℂ) - twistedMomentMain d p q η N w).re := by
  rw [twistedMomentErrorJet, realTwistedMomentJet_zero hd hd20,
    realTwistedMomentMainJet_zero, Complex.sub_re, Complex.ofReal_re]

theorem hasDerivAt_twistedMomentErrorJet {p q η : ℝ} (hη : 0 < η)
    (hp : 4 ≤ p - η) {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ k ∈ Finset.Icc 1 N, |w k| ≤ 1)
    {d : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20) (n : ℕ) :
    HasDerivAt (twistedMomentErrorJet p q η N w n)
      (twistedMomentErrorJet p q η N w (n + 1) d) d := by
  have hd4 : |d| < 1 / 4 := by rw [abs_of_pos hd]; linarith only [hd20]
  exact (hasDerivAt_realTwistedMomentJet hη hp hw hd4 n).sub
    (hasDerivAt_realTwistedMomentMainJet hη hp N w hd hd20 n)

/-- A single constant bounds all error jets uniformly on each right displacement interval. -/
theorem exists_abs_twistedMomentErrorJet_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p q η d y : ℝ) (N : ℕ) (w : ℕ → ℝ) (n : ℕ),
      0 < η → p ≤ q → 4 ≤ p - η → (∀ k ∈ Finset.Icc 1 N, |w k| ≤ 1) →
      0 < d → d ≤ y → y ≤ 1 / 20 →
      |twistedMomentErrorJet p q η N w n y| ≤ twistedErrorJetBound C p q η d N n := by
  obtain ⟨C, hC, hmain⟩ := exists_norm_iteratedDeriv_holomorphicTwistedMomentMain_le
  refine ⟨C, hC, fun p q η d y N w n hη hpq hp hw hd hdy hy20 => ?_⟩
  have hy : 0 < y := hd.trans_le hdy
  have hsize : 0 ≤ twistedMainSize p q η N := by
    have hlen : 0 ≤ q - p + 2 * η := by linarith only [hpq, hη]
    unfold twistedMainSize
    positivity
  have hCd : 0 ≤ C * twistedMainSize p q η N :=
    mul_nonneg (by linarith only [hC]) hsize
  have hden : (d / 2) ^ n ≤ (y / 2) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hdy]) n
  have hm : |realTwistedMomentMainJet p q η N w n y| ≤
      (n.factorial : ℝ) * (C * twistedMainSize p q η N / d) / (d / 2) ^ n := by
    refine (Complex.abs_re_le_norm _).trans
      ((hmain p q η N w y n hη hpq hp hw hy hy20).trans ?_)
    apply div_le_div₀ (by positivity) ?_ (by positivity) hden
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hCd hd hdy) (Nat.cast_nonneg _)
  exact (abs_sub _ _).trans (add_le_add
    (abs_realTwistedMomentJet_le hη hpq hp hw hy.le hy20 n) hm)

/-- The actual power-saving remainder controls both derivatives through explicit
step costs. No differentiated asymptotic formula is assumed. -/
theorem exists_twistedMoment_derivative_error_bounds {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (B : ℝ) :
    ∃ a C D : ℝ, 0 < a ∧ a < 1 ∧ 0 ≤ C ∧ 1 ≤ D ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (d q h k : ℝ) (N : ℕ) (w : ℕ → ℝ),
        T ≤ q → q ≤ 2 * T → 0 < d → 0 < h → 0 < k → d + h + k ≤ 1 / 20 →
        (N : ℝ) ≤ T ^ θ → (∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) →
        |twistedMomentErrorJet T q (T ^ a) N w 1 d| ≤
            2 * ((q - T + 2 * T ^ a) * C * T ^ (-B)) / k +
              twistedErrorJetBound D T q (T ^ a) d N 2 * k / 2 ∧
        |twistedMomentErrorJet T q (T ^ a) N w 2 d| ≤
            4 * ((q - T + 2 * T ^ a) * C * T ^ (-B)) / (h * k) +
              twistedErrorJetBound D T q (T ^ a) d N 2 * k / h +
              twistedErrorJetBound D T q (T ^ a) d N 3 * h / 2 := by
  obtain ⟨a, C, ha, ha1, hC, herror⟩ := exists_twistedMoment_power_saving hθ0 hθ B
  obtain ⟨D, hD, hjet⟩ := exists_abs_twistedMomentErrorJet_le
  refine ⟨a, C, D, ha, ha1, hC, hD, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_rpow_le_quarter ha1, herror]
    with T hT hηT he
  intro d q h k N w hq hq2 hd hh hk hsum hN hw
  have hT0 : 0 < T := by linarith only [hT]
  have hη : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hp : 4 ≤ T - T ^ a := by linarith only [hT, hηT]
  have hparts {y : ℝ} (hy : y ∈ Icc d (d + h + k)) : 0 < y ∧ y ≤ 1 / 20 :=
    ⟨hd.trans_le hy.1, hy.2.trans hsum⟩
  have hder (n : ℕ) (y : ℝ) (hy : y ∈ Icc d (d + h + k)) :=
    hasDerivAt_twistedMomentErrorJet (q := q) hη hp hw (hparts hy).1 (hparts hy).2 n
  have hc (n : ℕ) : ContinuousOn (twistedMomentErrorJet T q (T ^ a) N w n)
      (Icc d (d + h + k)) := fun y hy => (hder n y hy).continuousAt.continuousWithinAt
  have hval (y : ℝ) (hy : y ∈ Icc d (d + h + k)) :
      |twistedMomentErrorJet T q (T ^ a) N w 0 y| ≤
        (q - T + 2 * T ^ a) * C * T ^ (-B) := by
    rw [twistedMomentErrorJet_zero (hparts hy).1 (hparts hy).2]
    exact (Complex.abs_re_le_norm _).trans
      (he y q N w hq hq2 (hparts hy).1 (hparts hy).2 hN hw)
  have hb (n : ℕ) (y : ℝ) (hy : y ∈ Icc d (d + h + k)) :=
    hjet T q (T ^ a) d y N w n hη hq hp hw hd hy.1 (hparts hy).2
  have hsub : Icc d (d + k) ⊆ Icc d (d + h + k) :=
    Icc_subset_Icc_right (by linarith only [hh])
  constructor
  · exact abs_deriv_le_of_short_interval hk
      (fun y hy => hder 0 y (hsub hy)) (fun y hy => hder 1 y (hsub hy))
      ((hc 2).mono hsub) (fun y hy => hval y (hsub hy)) (fun y hy => hb 2 y (hsub hy))
  · exact abs_second_deriv_le_of_two_steps hh hk
      (hder 0) (hder 1) (hder 2) (hc 2) (hc 3) hval (hb 2) (hb 3)

private theorem twistedErrorJetBound_polynomial {C T q η d : ℝ} {N : ℕ}
    (hC : 1 ≤ C) (hT : 8 ≤ T) (hq : T ≤ q) (hq2 : q ≤ 2 * T)
    (hη : 0 < η) (hηT : η ≤ T) (hN : (N : ℝ) ≤ T) (hd : 0 < d) (hdT : 1 ≤ d * T) :
    twistedErrorJetBound C T q η d N 2 ≤
        16000000 * (C + 1) * (1 + (Real.exp 1) ^ 2) * T ^ 10 ∧
    twistedErrorJetBound C T q η d N 3 ≤
        16000000 * (C + 1) * (1 + (Real.exp 1) ^ 2) * T ^ 10 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hlen0 : 0 ≤ q - T + 2 * η := by linarith only [hq, hη]
  have hlen : q - T + 2 * η ≤ 3 * T := by linarith only [hq2, hηT]
  have hb0 : 0 ≤ 2 + 8 * (q + η + 1) := by linarith only [hT, hq, hη]
  have hb : 2 + 8 * (q + η + 1) ≤ 34 * T := by linarith only [hT, hq2, hηT]
  have hA : (q - T + 2 * η) * ((2 + 8 * (q + η + 1)) * N) ^ 2 ≤ 3468 * T ^ 5 := by
    have hbN := mul_le_mul hb hN (Nat.cast_nonneg _) (by positivity : 0 ≤ 34 * T)
    have hs := pow_le_pow_left₀ (mul_nonneg hb0 (Nat.cast_nonneg _)) hbN 2
    calc
      _ ≤ (3 * T) * ((34 * T) * T) ^ 2 :=
        mul_le_mul hlen hs (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hN2 := pow_le_pow_left₀ (Nat.cast_nonneg N) hN 2
  have hχ : (Real.exp 1 * (q + η + 2)) ^ 2 ≤ 16 * (Real.exp 1) ^ 2 * T ^ 2 := by
    have hl : 0 ≤ q + η + 2 := by linarith only [hq, hT, hη]
    have hu : q + η + 2 ≤ 4 * T := by linarith only [hq2, hT, hηT]
    calc
      _ ≤ (Real.exp 1 * (4 * T)) ^ 2 :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le) 2
      _ = _ := by ring
  have hT2 : 1 ≤ T ^ 2 := by nlinarith only [hT1]
  have hS : twistedMainSize T q η N ≤ (3 + 48 * (Real.exp 1) ^ 2) * T ^ 5 := by
    have hlast : 1 + (Real.exp 1 * (q + η + 2)) ^ 2 ≤
        (1 + 16 * (Real.exp 1) ^ 2) * T ^ 2 := by nlinarith only [hχ, hT2]
    unfold twistedMainSize
    calc
      _ ≤ (T ^ 2 * (3 * T)) * ((1 + 16 * (Real.exp 1) ^ 2) * T ^ 2) :=
        mul_le_mul (mul_le_mul hN2 hlen hlen0 (sq_nonneg _)) hlast
          (by positivity) (by positivity)
      _ = _ := by ring
  let A : ℝ := 4000 * (1 + (Real.exp 1) ^ 2)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hA' : (q - T + 2 * η) * ((2 + 8 * (q + η + 1)) * N) ^ 2 ≤ A * T ^ 5 :=
    hA.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [A]; nlinarith only [sq_nonneg (Real.exp 1)]) (by positivity))
  have hS' : twistedMainSize T q η N ≤ A * T ^ 5 :=
    hS.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [A]; nlinarith only [sq_nonneg (Real.exp 1)]) (by positivity))
  have hS0 : 0 ≤ twistedMainSize T q η N := by unfold twistedMainSize; positivity
  have hinv : 1 / d ≤ T := (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hdT)
  have hinv3 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / d) hinv 3
  have hinv4 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / d) hinv 4
  have hT5 : T ^ 5 ≤ T ^ 10 := pow_le_pow_right₀ hT1 (by decide)
  have hT8 : T ^ 8 ≤ T ^ 10 := pow_le_pow_right₀ hT1 (by decide)
  have hT9 : T ^ 9 ≤ T ^ 10 := pow_le_pow_right₀ hT1 (by decide)
  have hC0 : 0 ≤ C := by linarith only [hC]
  have htwo : twistedErrorJetBound C T q η d N 2 ≤
      128 * A * T ^ 5 + 8 * C * A * T ^ 8 := by
    have he : twistedErrorJetBound C T q η d N 2 =
        128 * ((q - T + 2 * η) * ((2 + 8 * (q + η + 1)) * N) ^ 2) +
          8 * C * twistedMainSize T q η N * (1 / d) ^ 3 := by
      unfold twistedErrorJetBound
      norm_num
      ring
    rw [he]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hS' (by positivity : 0 ≤ 8 * C))
      hinv3 (by positivity) (by positivity : 0 ≤ 8 * C * (A * T ^ 5))
    calc
      _ ≤ 128 * (A * T ^ 5) + (8 * C * (A * T ^ 5)) * T ^ 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hA' (by norm_num)) hh
      _ = _ := by ring
  have hthree : twistedErrorJetBound C T q η d N 3 ≤
      3072 * A * T ^ 5 + 48 * C * A * T ^ 9 := by
    have he : twistedErrorJetBound C T q η d N 3 =
        3072 * ((q - T + 2 * η) * ((2 + 8 * (q + η + 1)) * N) ^ 2) +
          48 * C * twistedMainSize T q η N * (1 / d) ^ 4 := by
      unfold twistedErrorJetBound
      norm_num
      ring
    rw [he]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hS' (by positivity : 0 ≤ 48 * C))
      hinv4 (by positivity) (by positivity : 0 ≤ 48 * C * (A * T ^ 5))
    calc
      _ ≤ 3072 * (A * T ^ 5) + (48 * C * (A * T ^ 5)) * T ^ 4 :=
        add_le_add (mul_le_mul_of_nonneg_left hA' (by norm_num)) hh
      _ = _ := by ring
  have hfinish (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y * C ≤ 4000 * (C + 1))
      (m : ℕ) (hm : T ^ m ≤ T ^ 10) :
      x * A * T ^ 5 + y * C * A * T ^ m ≤
        16000000 * (C + 1) * (1 + (Real.exp 1) ^ 2) * T ^ 10 := by
    calc
      _ ≤ x * A * T ^ 10 + y * C * A * T ^ 10 :=
        add_le_add (mul_le_mul_of_nonneg_left hT5 (by positivity))
          (mul_le_mul_of_nonneg_left hm (by positivity))
      _ = (x + y * C) * (A * T ^ 10) := by ring
      _ ≤ (4000 * (C + 1)) * (A * T ^ 10) :=
        mul_le_mul_of_nonneg_right hxy (by positivity)
      _ = _ := by dsimp only [A]; ring
  exact ⟨htwo.trans (hfinish 128 8 (by norm_num) (by norm_num)
      (by linarith only [hC]) 8 hT8),
    hthree.trans (hfinish 3072 48 (by norm_num) (by norm_num)
      (by linarith only [hC]) 9 hT9)⟩

/-- The first two displacement derivatives retain arbitrary power saving,
uniformly down to displacement `1/T` and for every length below square root. -/
theorem exists_twistedMoment_first_two_derivative_power_saving {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (B : ℝ) (hB : 0 ≤ B) :
    ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (d q : ℝ) (N : ℕ) (w : ℕ → ℝ),
        T ≤ q → q ≤ 2 * T → 1 / T ≤ d → d ≤ 1 / 40 → (N : ℝ) ≤ T ^ θ →
        (∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) →
        |twistedMomentErrorJet T q (T ^ a) N w 1 d| ≤ C * T ^ (-B) ∧
        |twistedMomentErrorJet T q (T ^ a) N w 2 d| ≤ C * T ^ (-B) := by
  obtain ⟨a, C, D, ha, ha1, hC, hD, herr⟩ :=
    exists_twistedMoment_derivative_error_bounds hθ0 hθ (4 * B + 40)
  let K : ℝ := 16000000 * (D + 1) * (1 + (Real.exp 1) ^ 2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨a, 12 * C + 2 * K, ha, ha1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (80 : ℝ), eventually_rpow_le_quarter ha1, herr]
    with T hT hηT he
  intro d q N w hq hq2 hdT hd40 hN hw
  have hT0 : 0 < T := by linarith only [hT]
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hη : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hηle : T ^ a ≤ T := hηT.trans (by linarith only [hT])
  have hd : 0 < d := (one_div_pos.mpr hT0).trans_le hdT
  have hdT' : 1 ≤ d * T := (div_le_iff₀ hT0).mp hdT
  have hN' : (N : ℝ) ≤ T := hN.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
      (show θ ≤ 1 by linarith only [hθ]))
  obtain ⟨hM₂, hM₃⟩ := twistedErrorJetBound_polynomial hD
    (by linarith only [hT]) hq hq2 hη hηle hN' hd hdT'
  change twistedErrorJetBound D T q (T ^ a) d N 2 ≤ K * T ^ 10 at hM₂
  change twistedErrorJetBound D T q (T ^ a) d N 3 ≤ K * T ^ 10 at hM₃
  let h : ℝ := T ^ (-(B + 12))
  let k : ℝ := T ^ (-(2 * B + 24))
  have hh : 0 < h := Real.rpow_pos_of_pos hT0 _
  have hk : 0 < k := Real.rpow_pos_of_pos hT0 _
  have hsmall (v : ℝ) (hv : v ≤ -1) : T ^ v ≤ 1 / 80 := by
    calc
      _ ≤ T ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hv
      _ = 1 / T := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := div_le_div_of_nonneg_left zero_le_one (by norm_num) hT
  have hhsmall : h ≤ 1 / 80 := hsmall _ (by linarith only [hB])
  have hksmall : k ≤ 1 / 80 := hsmall _ (by linarith only [hB])
  have hsum : d + h + k ≤ 1 / 20 := by linarith only [hd40, hhsmall, hksmall]
  obtain ⟨he₁, he₂⟩ := he d q h k N w hq hq2 hd hh hk hsum hN hw
  have hlen : q - T + 2 * T ^ a ≤ 3 * T := by linarith only [hq2, hηle]
  have hE₁ : T * T ^ (-(4 * B + 40)) / k = T ^ (-2 * B - 15) := by
    calc
      _ = (T ^ (1 : ℝ) * T ^ (-(4 * B + 40))) / T ^ (-(2 * B + 24)) := by
        simp only [k, Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hT0, ← Real.rpow_sub hT0]; congr 1; ring
  have hE₂ : T * T ^ (-(4 * B + 40)) / (h * k) = T ^ (-B - 3) := by
    calc
      _ = (T ^ (1 : ℝ) * T ^ (-(4 * B + 40))) /
          (T ^ (-(B + 12)) * T ^ (-(2 * B + 24))) := by simp only [h, k, Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hT0, ← Real.rpow_add hT0,
          ← Real.rpow_sub hT0]; congr 1; ring
  have hP₁ : T ^ (10 : ℕ) * k = T ^ (-2 * B - 14) := by
    dsimp only [k]
    rw [← Real.rpow_natCast, ← Real.rpow_add hT0]
    congr 1
    norm_num
    ring
  have hP₂ : T ^ (10 : ℕ) * k / h = T ^ (-B - 2) := by
    rw [hP₁]
    dsimp only [h]
    rw [← Real.rpow_sub hT0]
    congr 1
    ring
  have hP₃ : T ^ (10 : ℕ) * h = T ^ (-B - 2) := by
    dsimp only [h]
    rw [← Real.rpow_natCast, ← Real.rpow_add hT0]
    congr 1
    norm_num
    ring
  have hp₁ : T ^ (-2 * B - 15) ≤ T ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hB])
  have hp₂ : T ^ (-B - 3) ≤ T ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hp₃ : T ^ (-2 * B - 14) ≤ T ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hB])
  have hp₄ : T ^ (-B - 2) ≤ T ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hvalue₁ : 2 * ((q - T + 2 * T ^ a) * C * T ^ (-(4 * B + 40))) / k ≤
      6 * C * T ^ (-B) := by
    calc
      _ ≤ 2 * ((3 * T) * C * T ^ (-(4 * B + 40))) / k := by gcongr
      _ = 6 * C * (T * T ^ (-(4 * B + 40)) / k) := by ring
      _ = 6 * C * T ^ (-2 * B - 15) := by rw [hE₁]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₁ (by positivity)
  have hvalue₂ : 4 * ((q - T + 2 * T ^ a) * C * T ^ (-(4 * B + 40))) / (h * k) ≤
      12 * C * T ^ (-B) := by
    calc
      _ ≤ 4 * ((3 * T) * C * T ^ (-(4 * B + 40))) / (h * k) := by gcongr
      _ = 12 * C * (T * T ^ (-(4 * B + 40)) / (h * k)) := by ring
      _ = 12 * C * T ^ (-B - 3) := by rw [hE₂]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₂ (by positivity)
  have hcurvature₁ : twistedErrorJetBound D T q (T ^ a) d N 2 * k / 2 ≤
      K / 2 * T ^ (-B) := by
    calc
      _ ≤ (K * T ^ 10) * k / 2 := by gcongr
      _ = K / 2 * (T ^ 10 * k) := by ring
      _ = K / 2 * T ^ (-2 * B - 14) := by rw [hP₁]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₃ (by positivity)
  have hcurvature₂ : twistedErrorJetBound D T q (T ^ a) d N 2 * k / h ≤
      K * T ^ (-B) := by
    calc
      _ ≤ (K * T ^ 10) * k / h := by gcongr
      _ = K * (T ^ 10 * k / h) := by ring
      _ = K * T ^ (-B - 2) := by rw [hP₂]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₄ hK
  have hthird : twistedErrorJetBound D T q (T ^ a) d N 3 * h / 2 ≤
      K / 2 * T ^ (-B) := by
    calc
      _ ≤ (K * T ^ 10) * h / 2 := by gcongr
      _ = K / 2 * (T ^ 10 * h) := by ring
      _ = K / 2 * T ^ (-B - 2) := by rw [hP₃]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₄ (by positivity)
  have hr0 : 0 ≤ T ^ (-B) := Real.rpow_nonneg hT0.le _
  constructor
  · refine (he₁.trans (add_le_add hvalue₁ hcurvature₁)).trans ?_
    calc
      _ = (6 * C + K / 2) * T ^ (-B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hC, hK]) hr0
  · refine (he₂.trans (add_le_add (add_le_add hvalue₂ hcurvature₂) hthird)).trans ?_
    calc
      _ = (12 * C + 3 * K / 2) * T ^ (-B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hK]) hr0

end GaloisForLFunctions.MultiscaleMollifiedZetaField
