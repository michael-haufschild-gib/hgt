import GaloisForLFunctions.RHTower.ZetaZeroDensityEdgeRanges

/-!
# Class-count arithmetic for powers `ℓ ≤ M`

The class-count arithmetic of `ZetaZeroDensityEdgeRanges` and `ZetaZeroClassExponentBookkeeping`
fixes the largest power at `34`.  Here the bound is a free natural number `M`:

* `classPowerMass_le_of_le`: in the window `(2^j)^ℓ ≤ T²`,
  `classPowerMass j ℓ σ ≤ 2^M X^{1-2σ} ((M+3)(1 + log T))^{2^{4M}}`;
* `class_count_mvt_arith_of_le`, `class_huxley_threshold_arith_of_le`,
  `class_count_huxley_arith_of_le`: the mean value range, the Huxley threshold and the Huxley range
  with `L ≤ 2^M X`, `G ≤ 2^M X^{1-2σ} P`, `U ≤ M Q^M`.
-/

noncomputable section

namespace RHTower

open Finset

/-- The logarithm of the raised length is at most `(M+3)(1 + log T)` when `(2^j)^ℓ ≤ T²`. -/
theorem one_add_log_raised_le_of_le {T : ℝ} (hT : 1 ≤ T) {j ℓ M : ℕ} (hℓ : ℓ ≤ M)
    (hX : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (2 : ℝ)) :
    1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ (M + 3) * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * (((2 ^ j : ℕ) : ℝ)) ^ ℓ := by
    push_cast
    ring
  have hXpos : 0 < (((2 ^ j : ℕ) : ℝ)) ^ ℓ := by positivity
  rw [hcast, Real.log_mul (by positivity) hXpos.ne', Real.log_pow]
  have hM : (ℓ : ℝ) ≤ M := by exact_mod_cast hℓ
  have h1 : (ℓ : ℝ) * Real.log 2 ≤ M := by
    have : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  have h2 : Real.log ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ≤ 2 * Real.log T := by
    have := Real.log_le_log hXpos hX
    rwa [Real.log_rpow hT0] at this
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

/-- **The mass of a raised class polynomial, powers `ℓ ≤ M`.** -/
theorem classPowerMass_le_of_le {T : ℝ} (hT : 1 ≤ T) {j ℓ M : ℕ} (hℓ : ℓ ≤ M) {σ : ℝ}
    (hX : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (2 : ℝ)) :
    classPowerMass j ℓ σ ≤ 2 ^ M * ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ^ (1 - 2 * σ)
        * ((M + 3) * (1 + Real.log T)) ^ (2 ^ (4 * M)) := by
  have hlog := one_add_log_raised_le_of_le hT hℓ hX
  set X := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hX0 : 0 < X := by linarith
  have hΛ1 : 1 ≤ ((M : ℝ) + 3) * (1 + Real.log T) := by
    have := Real.log_nonneg hT
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hlogL0 : 1 ≤ 1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    have : 0 ≤ Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_pow _ _ (by positivity))
    linarith
  have hcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
    rw [hXdef]
    push_cast
    ring
  have h2l : (2 : ℝ) ^ ℓ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hℓ
  have hexp : 2 ^ (4 * ℓ) - 1 ≤ 2 ^ (4 * M) := by
    have : 2 ^ (4 * ℓ) ≤ 2 ^ (4 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans (Nat.sub_le _ _) this
  have hpolylog : (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) ^ (2 ^ (4 * ℓ) - 1)
      ≤ (((M : ℝ) + 3) * (1 + Real.log T)) ^ (2 ^ (4 * M)) :=
    le_trans (pow_le_pow_left₀ (by linarith) hlog _) (pow_le_pow_right₀ hΛ1 hexp)
  unfold classPowerMass
  rw [← hXdef, hcast]
  have hXpow : X ^ (-2 * σ) * (2 ^ ℓ * X) = 2 ^ ℓ * X ^ (1 - 2 * σ) := by
    rw [show (1 - 2 * σ) = (-2 * σ) + 1 by ring, Real.rpow_add hX0, Real.rpow_one]
    ring
  rw [hXpow]
  have hXnn : 0 ≤ X ^ (1 - 2 * σ) := Real.rpow_nonneg hX0.le _
  calc 2 ^ ℓ * X ^ (1 - 2 * σ) * (1 + Real.log (2 ^ ℓ * X)) ^ (2 ^ (4 * ℓ) - 1)
      ≤ 2 ^ M * X ^ (1 - 2 * σ) * (((M : ℝ) + 3) * (1 + Real.log T)) ^ (2 ^ (4 * M)) := by
        rw [← hcast]
        gcongr

/-- **The mean value range, powers `ℓ ≤ M`.**  If `T X^{1-2σ} ≤ T^E` and `X^{2-2σ} ≤ T^E`, a mean
value count gives `c ≤ 2^{M+1}(2 + 2^{M+2}) Q^{2M}·Q·Q·P·T^E`. -/
theorem class_count_mvt_arith_of_le {T X σ E Q P L G V c : ℝ} {ℓ M : ℕ}
    (hT : 1 ≤ T) (hXge : 1 ≤ X) (hTa : T * X ^ (1 - 2 * σ) ≤ T ^ E)
    (hXb : X ^ (2 - 2 * σ) ≤ T ^ E)
    (hQ : 1 ≤ Q) (hP : 0 ≤ P) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ M * X)
    (hlogL : 1 + Real.log L ≤ Q) (hG0 : 0 ≤ G) (hG : G ≤ 2 ^ M * X ^ (1 - 2 * σ) * P)
    (hV : 1 / Q ^ M ≤ V ^ ℓ) (hc0 : 0 ≤ c)
    (hcount : c * (V ^ ℓ) ^ 2 ≤ (T + 1 + 4 * L * (1 + Real.log L)) * (1 + 2 * Real.log L) * G) :
    c ≤ 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) * (Q ^ (2 * M) * Q * Q * P) * T ^ E := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  set a := 1 - 2 * σ with ha
  have hXa0 : 0 ≤ X ^ a := Real.rpow_nonneg hX0.le _
  have hXb' : X * X ^ a ≤ T ^ E := by
    have h1 : X * X ^ a = X ^ (2 - 2 * σ) := by
      rw [show (2 - 2 * σ) = 1 + a by rw [ha]; ring, Real.rpow_add hX0, Real.rpow_one]
    rw [h1]
    exact hXb
  have hmain : (2 * T + 2 ^ (M + 2) * X) * X ^ a ≤ (2 + 2 ^ (M + 2)) * T ^ E := by
    calc (2 * T + 2 ^ (M + 2) * X) * X ^ a = 2 * (T * X ^ a) + 2 ^ (M + 2) * (X * X ^ a) := by
          ring
      _ ≤ 2 * T ^ E + 2 ^ (M + 2) * T ^ E :=
          add_le_add (mul_le_mul_of_nonneg_left hTa (by norm_num))
            (mul_le_mul_of_nonneg_left hXb' (by positivity))
      _ = (2 + 2 ^ (M + 2)) * T ^ E := by ring
  have hF1 : T + 1 + 4 * L * (1 + Real.log L) ≤ (2 * T + 2 ^ (M + 2) * X) * Q := by
    have h4 : 4 * L * (1 + Real.log L) ≤ 4 * (2 ^ M * X) * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num)) hlogL (by linarith) (by positivity)
    have hTQ : 2 * T ≤ 2 * T * Q := le_mul_of_one_le_right (by linarith) hQ
    have hexp : (2 * T + 2 ^ (M + 2) * X) * Q = 2 * T * Q + 4 * (2 ^ M * X) * Q := by ring
    rw [hexp]
    linarith
  have hF2 : 1 + 2 * Real.log L ≤ 2 * Q := by linarith
  have hprod : (T + 1 + 4 * L * (1 + Real.log L)) * (1 + 2 * Real.log L) * G
      ≤ ((2 * T + 2 ^ (M + 2) * X) * Q) * (2 * Q) * (2 ^ M * X ^ a * P) :=
    mul_le_mul (mul_le_mul hF1 hF2 (by linarith) (by positivity)) hG hG0 (by positivity)
  have hVsq : 1 / Q ^ (2 * M) ≤ (V ^ ℓ) ^ 2 := by
    calc 1 / Q ^ (2 * M) = (1 / Q ^ M) ^ 2 := by rw [div_pow, one_pow, ← pow_mul, mul_comm]
      _ ≤ (V ^ ℓ) ^ 2 := pow_le_pow_left₀ (by positivity) hV 2
  have hc : c ≤ Q ^ (2 * M) *
      (((2 * T + 2 ^ (M + 2) * X) * Q) * (2 * Q) * (2 ^ M * X ^ a * P)) := by
    have h1 : c * (1 / Q ^ (2 * M)) ≤ c * (V ^ ℓ) ^ 2 := mul_le_mul_of_nonneg_left hVsq hc0
    have h2 := le_trans (le_trans h1 hcount) hprod
    rw [mul_one_div, div_le_iff₀ (pow_pos hQ0 _)] at h2
    linarith
  refine le_trans hc ?_
  have hQP : 0 ≤ Q ^ (2 * M) * Q * Q * P :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hQ0.le _) hQ0.le) hQ0.le) hP
  calc Q ^ (2 * M) * (((2 * T + 2 ^ (M + 2) * X) * Q) * (2 * Q) * (2 ^ M * X ^ a * P))
      = 2 ^ (M + 1) * (Q ^ (2 * M) * Q * Q * P) * ((2 * T + 2 ^ (M + 2) * X) * X ^ a) := by
        ring
    _ ≤ 2 ^ (M + 1) * (Q ^ (2 * M) * Q * Q * P) * ((2 + 2 ^ (M + 2)) * T ^ E) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg (by positivity) hQP)
    _ = 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) * (Q ^ (2 * M) * Q * Q * P) * T ^ E := by ring

/-- **The Huxley threshold, powers `ℓ ≤ M`.**  If `X^{3/2-2σ} ≤ T^{-δ}`, `U ≤ M Q^M` and
`3 M² · 1537 · 2^{2M} · Q^{2M} P ≤ T^δ`, then `G(1 + 1536√(3L/4π)) ≤ (1/U)²/3`. -/
theorem class_huxley_threshold_arith_of_le {T X σ δ Q P L G U : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hXge : 1 ≤ X) (hXd : X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ T ^ (-δ))
    (hQ : 1 ≤ Q) (hP : 0 ≤ P) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ M * X)
    (hG : G ≤ 2 ^ M * X ^ (1 - 2 * σ) * P) (hU0 : 0 < U) (hU : U ≤ M * Q ^ M)
    (hbig : 3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M) * (Q ^ (2 * M) * P) ≤ T ^ δ) :
    G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi))) ≤ (1 / U) ^ 2 / 3 := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  have h2M : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  have h22 : (2 : ℝ) ^ (2 * M) = 2 ^ M * 2 ^ M := by rw [two_mul, pow_add]
  have hsq1 : Real.sqrt (3 * L / (4 * Real.pi)) ≤ Real.sqrt L := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hsq2 : Real.sqrt L ≤ 2 ^ M * X ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt L ≤ Real.sqrt ((2 ^ M) ^ 2 * X) := by
          apply Real.sqrt_le_sqrt
          calc L ≤ 2 ^ M * X := hL
            _ ≤ (2 ^ M) ^ 2 * X := by
                apply mul_le_mul_of_nonneg_right _ hX0.le
                nlinarith
      _ = 2 ^ M * Real.sqrt X := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hone : (1 : ℝ) ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hsqrtL :
      1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)) ≤ 1537 * 2 ^ M * X ^ ((1 : ℝ) / 2) := by
    linarith
  have hXs : X ^ (1 - 2 * σ) * X ^ ((1 : ℝ) / 2) = X ^ ((3 : ℝ) / 2 - 2 * σ) := by
    rw [← Real.rpow_add hX0]
    ring_nf
  have hstep : G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)))
      ≤ 1537 * 2 ^ (2 * M) * P * T ^ (-δ) := by
    calc G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)))
        ≤ (2 ^ M * X ^ (1 - 2 * σ) * P) * (1537 * 2 ^ M * X ^ ((1 : ℝ) / 2)) :=
          mul_le_mul hG hsqrtL (by positivity) (by positivity)
      _ = 1537 * 2 ^ (2 * M) * P * (X ^ (1 - 2 * σ) * X ^ ((1 : ℝ) / 2)) := by
          rw [h22]; ring
      _ = 1537 * 2 ^ (2 * M) * P * X ^ ((3 : ℝ) / 2 - 2 * σ) := by rw [hXs]
      _ ≤ 1537 * 2 ^ (2 * M) * P * T ^ (-δ) := mul_le_mul_of_nonneg_left hXd (by positivity)
  refine le_trans hstep ?_
  have hTe0 : 0 < T ^ δ := Real.rpow_pos_of_pos hT0 _
  have hTeps : T ^ (-δ) = 1 / T ^ δ := by rw [Real.rpow_neg hT0.le, one_div]
  have hU2 : U ^ 2 ≤ (M : ℝ) ^ 2 * Q ^ (2 * M) := by
    calc U ^ 2 ≤ ((M : ℝ) * Q ^ M) ^ 2 := pow_le_pow_left₀ hU0.le hU 2
      _ = (M : ℝ) ^ 2 * Q ^ (2 * M) := by rw [mul_pow, ← pow_mul, mul_comm M 2]
  rw [hTeps, one_div_pow, div_div, le_div_iff₀ (by positivity)]
  calc 1537 * 2 ^ (2 * M) * P * (1 / T ^ δ) * (U ^ 2 * 3)
      = 3 * 1537 * 2 ^ (2 * M) * P * U ^ 2 / T ^ δ := by ring
    _ ≤ 3 * 1537 * 2 ^ (2 * M) * P * ((M : ℝ) ^ 2 * Q ^ (2 * M)) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hTe0.le
        exact mul_le_mul_of_nonneg_left hU2 (by positivity)
    _ = (3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M) * (Q ^ (2 * M) * P)) / T ^ δ := by ring
    _ ≤ 1 := by
        rw [div_le_one hTe0]
        exact hbig

/-- The Huxley constant for powers `ℓ ≤ M`. -/
def classHuxleyConstantOf (M : ℕ) : ℝ :=
  (M : ℝ) ^ 3 * 6 * (1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M) + 2 ^ (2 * M))

theorem classHuxleyConstantOf_nonneg (M : ℕ) : 0 ≤ classHuxleyConstantOf M := by
  unfold classHuxleyConstantOf
  positivity

/-- **The Huxley range, powers `ℓ ≤ M`.**  If `T X^{4-6σ} ≤ T^E` and `X^{2-2σ} ≤ T^E`, a Huxley
count gives `c ≤ classHuxleyConstantOf M · (Q^{2M}·R·Q)·T^E`. -/
theorem class_count_huxley_arith_of_le {T X σ E Q P R L G U c : ℝ} {ℓ M : ℕ}
    (hT : 1 ≤ T) (hXge : 1 ≤ X) (hX46 : T * X ^ (4 - 6 * σ) ≤ T ^ E)
    (hX22 : X ^ (2 - 2 * σ) ≤ T ^ E)
    (hQ : 1 ≤ Q) (hQlow : 36 * (1 + Real.log T) ≤ Q) (hP : 0 ≤ P)
    (hcube : Q ^ (4 * M) * P ^ 3 ≤ R)
    (hsingle : P ≤ R) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ M * X) (hG0 : 0 ≤ G)
    (hG : G ≤ 2 ^ M * X ^ (1 - 2 * σ) * P) (hU0 : 0 < U) (hU : U ≤ M * Q ^ M)
    (hℓ : (ℓ : ℝ) ≤ M)
    (hcount : c * (1 / U) ^ 2 ≤ ℓ * ((T * (1284 * G) ^ 2 / (1 / U) ^ 4 + 1) *
      (2 * G * (L + 12 * Real.pi * L * (1 + Real.log (T + 1)))))) :
    c ≤ classHuxleyConstantOf M * (Q ^ (2 * M) * R * Q) * T ^ E := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  have hTA0 : 0 ≤ T ^ E := Real.rpow_nonneg hT0.le _
  have hR0 : 0 ≤ R := le_trans hP hsingle
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h22 : (2 : ℝ) ^ (2 * M) = 2 ^ M * 2 ^ M := by rw [two_mul, pow_add]
  have h44 : (2 : ℝ) ^ (4 * M) = 2 ^ (2 * M) * 2 ^ (2 * M) := by
    rw [← pow_add]; congr 1; ring
  have hc : c ≤ U ^ 2 * (ℓ * ((T * (1284 * G) ^ 2 / (1 / U) ^ 4 + 1) *
      (2 * G * (L + 12 * Real.pi * L * (1 + Real.log (T + 1)))))) := by
    rw [one_div_pow, mul_one_div, div_le_iff₀ (pow_pos hU0 2)] at hcount
    linarith
  refine le_trans hc ?_
  have hsimp : (T * (1284 * G) ^ 2 / (1 / U) ^ 4 + 1)
      * (2 * G * (L + 12 * Real.pi * L * (1 + Real.log (T + 1))))
      = 2 * (1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L)
        * (1 + 12 * Real.pi * (1 + Real.log (T + 1))) := by
    field_simp
  rw [hsimp]
  have hlogT1 : 1 + 12 * Real.pi * (1 + Real.log (T + 1)) ≤ 3 * Q := by
    have h1 : Real.log (T + 1) ≤ 1 + Real.log T := by
      have := Real.log_le_log (by linarith) (show T + 1 ≤ 2 * T by linarith)
      rw [Real.log_mul (by norm_num) hT0.ne'] at this
      have hl2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
      linarith
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
    have hπ : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have hlog1 : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
    have hprod : 12 * Real.pi * (1 + Real.log (T + 1)) ≤ 12 * 3.15 * (2 + Real.log T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hπ (by norm_num)) (by linarith) (by positivity)
        (by norm_num)
    linarith
  have hGL : G * L ≤ 2 ^ (2 * M) * X ^ (2 - 2 * σ) * P := by
    have h1 : X ^ (1 - 2 * σ) * X = X ^ (2 - 2 * σ) := by
      rw [show (2 - 2 * σ) = (1 - 2 * σ) + 1 by ring, Real.rpow_add hX0, Real.rpow_one]
    calc G * L ≤ (2 ^ M * X ^ (1 - 2 * σ) * P) * (2 ^ M * X) :=
          mul_le_mul hG hL (by linarith) (by positivity)
      _ = 2 ^ (2 * M) * (X ^ (1 - 2 * σ) * X) * P := by rw [h22]; ring
      _ = 2 ^ (2 * M) * X ^ (2 - 2 * σ) * P := by rw [h1]
  have hG3L : G ^ 2 * (G * L) ≤ 2 ^ (4 * M) * X ^ (4 - 6 * σ) * P ^ 3 := by
    have h1 : (X ^ (1 - 2 * σ)) ^ 2 * X ^ (2 - 2 * σ) = X ^ (4 - 6 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
      ring_nf
    have hGL0 : 0 ≤ G * L := mul_nonneg hG0 (by linarith)
    calc G ^ 2 * (G * L)
        ≤ (2 ^ M * X ^ (1 - 2 * σ) * P) ^ 2 * (2 ^ (2 * M) * X ^ (2 - 2 * σ) * P) :=
          mul_le_mul (pow_le_pow_left₀ hG0 hG 2) hGL hGL0 (by positivity)
      _ = 2 ^ (4 * M) * ((X ^ (1 - 2 * σ)) ^ 2 * X ^ (2 - 2 * σ)) * P ^ 3 := by
          rw [h44, h22]; ring
      _ = 2 ^ (4 * M) * X ^ (4 - 6 * σ) * P ^ 3 := by rw [h1]
  have hU4 : U ^ 4 ≤ (M : ℝ) ^ 4 * Q ^ (4 * M) := by
    calc U ^ 4 ≤ ((M : ℝ) * Q ^ M) ^ 4 := pow_le_pow_left₀ hU0.le hU 4
      _ = (M : ℝ) ^ 4 * Q ^ (4 * M) := by rw [mul_pow, ← pow_mul, mul_comm M 4]
  have hU2 : U ^ 2 ≤ (M : ℝ) ^ 2 * Q ^ (2 * M) := by
    calc U ^ 2 ≤ ((M : ℝ) * Q ^ M) ^ 2 := pow_le_pow_left₀ hU0.le hU 2
      _ = (M : ℝ) ^ 2 * Q ^ (2 * M) := by rw [mul_pow, ← pow_mul, mul_comm M 2]
  have hQ4 : 0 ≤ Q ^ (4 * M) := pow_nonneg hQ0.le _
  have hinner : 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L
      ≤ (1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M) + 2 ^ (2 * M)) * R * T ^ E := by
    have h1 : T * (G ^ 2 * (G * L)) ≤ 2 ^ (4 * M) * P ^ 3 * T ^ E := by
      calc T * (G ^ 2 * (G * L)) ≤ T * (2 ^ (4 * M) * X ^ (4 - 6 * σ) * P ^ 3) :=
            mul_le_mul_of_nonneg_left hG3L hT0.le
        _ = 2 ^ (4 * M) * P ^ 3 * (T * X ^ (4 - 6 * σ)) := by ring
        _ ≤ 2 ^ (4 * M) * P ^ 3 * T ^ E :=
            mul_le_mul_of_nonneg_left hX46 (mul_nonneg (by positivity) (pow_nonneg hP _))
    have h2 : G * L ≤ 2 ^ (2 * M) * P * T ^ E := by
      calc G * L ≤ 2 ^ (2 * M) * X ^ (2 - 2 * σ) * P := hGL
        _ = 2 ^ (2 * M) * P * X ^ (2 - 2 * σ) := by ring
        _ ≤ 2 ^ (2 * M) * P * T ^ E :=
            mul_le_mul_of_nonneg_left hX22 (mul_nonneg (by positivity) hP)
    have h3 : 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L)))
        ≤ 1284 ^ 2 * ((M : ℝ) ^ 4 * Q ^ (4 * M)) * (2 ^ (4 * M) * P ^ 3 * T ^ E) := by
      have hTG : 0 ≤ T * (G ^ 2 * (G * L)) := by
        have : 0 ≤ G * L := mul_nonneg hG0 (by linarith)
        positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hU4 (by norm_num)) h1 hTG
        (mul_nonneg (by norm_num) (mul_nonneg (by positivity) hQ4))
    have h5 : 1284 ^ 2 * ((M : ℝ) ^ 4 * Q ^ (4 * M)) * (2 ^ (4 * M) * P ^ 3 * T ^ E)
        ≤ 1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M) * R * T ^ E := by
      have e : 1284 ^ 2 * ((M : ℝ) ^ 4 * Q ^ (4 * M)) * (2 ^ (4 * M) * P ^ 3 * T ^ E)
          = 1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M) * (Q ^ (4 * M) * P ^ 3) * T ^ E := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by positivity)) hTA0
    have h6 : 2 ^ (2 * M) * P * T ^ E ≤ 2 ^ (2 * M) * R * T ^ E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsingle (by positivity)) hTA0
    have h7 : (1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M) + 2 ^ (2 * M)) * R * T ^ E
        = 1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M) * R * T ^ E + 2 ^ (2 * M) * R * T ^ E := by ring
    rw [h7]
    linarith
  have hinner0 : 0 ≤ 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L := by
    have : 0 ≤ G * L := mul_nonneg hG0 (by linarith)
    positivity
  have hlog0 : 0 ≤ 1 + 12 * Real.pi * (1 + Real.log (T + 1)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 1 by linarith)
    positivity
  have hQ2 : 0 ≤ Q ^ (2 * M) := pow_nonneg hQ0.le _
  calc U ^ 2 * (ℓ * (2 * (1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L)
        * (1 + 12 * Real.pi * (1 + Real.log (T + 1)))))
      ≤ ((M : ℝ) ^ 2 * Q ^ (2 * M)) * ((M : ℝ) * (2 * ((1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M)
          + 2 ^ (2 * M)) * R * T ^ E) * (3 * Q))) := by
        have hin2 : 0 ≤ 2 * (1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L)
            * (1 + 12 * Real.pi * (1 + Real.log (T + 1))) :=
          mul_nonneg (mul_nonneg (by norm_num) hinner0) hlog0
        have hKR : 0 ≤ (1284 ^ 2 * (M : ℝ) ^ 4 * 2 ^ (4 * M) + 2 ^ (2 * M)) * R * T ^ E :=
          mul_nonneg (mul_nonneg (by positivity) hR0) hTA0
        apply mul_le_mul hU2 _ (mul_nonneg (Nat.cast_nonneg _) hin2) (by positivity)
        apply mul_le_mul hℓ _ hin2 hM0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hinner (by norm_num)) hlogT1 hlog0
          (mul_nonneg (by norm_num) hKR)
    _ = classHuxleyConstantOf M * (Q ^ (2 * M) * R * Q) * T ^ E := by
        unfold classHuxleyConstantOf
        ring

end RHTower

end
