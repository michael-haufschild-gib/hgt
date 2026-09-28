import GaloisForLFunctions.RHTower.ZetaZeroDensityExponentLemmas

/-!
# Pure inequalities behind the class count

Each lemma turns one large-value count, stated with abstract nonnegative quantities, into a power of
`T`.  Here `X ∈ [T^{2/3}, T^{4/3}]`, `L ≤ 2^{34} X`, `1 + log L ≤ Q`, the mass `G ≤ 2^{34} X^{1-2σ} P`,
and the threshold `V^ℓ ≥ Q^{-34}`.  Keeping them separate from the Dirichlet-polynomial objects keeps
each elaboration small.
-/

namespace RHTower

noncomputable section

theorem rpow_window_lower {T X a : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (2 / 3 : ℝ) ≤ X) (ha : a ≤ 0) :
    X ^ a ≤ T ^ ((2 / 3) * a) := by
  have hT0 : 0 < T := by linarith
  calc X ^ a ≤ (T ^ (2 / 3 : ℝ)) ^ a :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 ha
    _ = T ^ ((2 / 3) * a) := by rw [← Real.rpow_mul hT0.le]

theorem rpow_window_upper {T X a : ℝ} (hT : 1 ≤ T) (hX0 : 0 ≤ X) (hX2 : X ≤ T ^ (4 / 3 : ℝ))
    (ha : 0 ≤ a) : X ^ a ≤ T ^ ((4 / 3) * a) := by
  have hT0 : 0 < T := by linarith
  calc X ^ a ≤ (T ^ (4 / 3 : ℝ)) ^ a := Real.rpow_le_rpow hX0 hX2 ha
    _ = T ^ ((4 / 3) * a) := by rw [← Real.rpow_mul hT0.le]

/-- `X^{2-2σ} ≤ T^{(8/3+ε)(1-σ)}` in the window. -/
theorem window_diagonal_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX0 : 0 ≤ X)
    (hX2 : X ≤ T ^ (4 / 3 : ℝ)) (hσ : σ ≤ 1) (hε : 0 ≤ ε) :
    X ^ (2 - 2 * σ) ≤ T ^ ((8 / 3 + ε) * (1 - σ)) := by
  refine le_trans (rpow_window_upper hT hX0 hX2 (by linarith)) ?_
  apply Real.rpow_le_rpow_of_exponent_le hT
  nlinarith

/-- **The mean value range.**  If `c·(V^ℓ)² ≤ (T + 1 + 4L(1 + log L))(1 + 2 log L)·G` with the
window data, then `c ≤ 2^{35}(2 + 2^{36}) Q^{68}·Q·Q·P·T^{(8/3+ε)(1-σ)}`. -/
theorem class_count_mvt_arith {T X σ ε Q P L G V c : ℝ} {ℓ : ℕ}
    (hT : 1 ≤ T) (hX1 : T ^ (2 / 3 : ℝ) ≤ X) (hX2 : X ≤ T ^ (4 / 3 : ℝ)) (hXge : 1 ≤ X)
    (hσ0 : 1 / 2 ≤ σ) (hσ : σ ≤ 3 / 4 + ε / 32) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hQ : 1 ≤ Q) (hP : 0 ≤ P) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ 34 * X)
    (hlogL : 1 + Real.log L ≤ Q) (hG0 : 0 ≤ G) (hG : G ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * P)
    (hV : 1 / Q ^ 34 ≤ V ^ ℓ) (hc0 : 0 ≤ c)
    (hcount : c * (V ^ ℓ) ^ 2 ≤ (T + 1 + 4 * L * (1 + Real.log L)) * (1 + 2 * Real.log L) * G) :
    c ≤ 2 ^ 35 * (2 + 2 ^ 36) * (Q ^ 68 * Q * Q * P) * T ^ ((8 / 3 + ε) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  set A := (8 / 3 + ε) * (1 - σ) with hA
  set a := 1 - 2 * σ with ha
  have hXa0 : 0 ≤ X ^ a := Real.rpow_nonneg hX0.le _
  have hTa : T * X ^ a ≤ T ^ A := by
    calc T * X ^ a ≤ T * T ^ ((2 / 3) * a) :=
          mul_le_mul_of_nonneg_left (rpow_window_lower hT hX1 (by rw [ha]; linarith)) hT0.le
      _ = T ^ (1 + (2 / 3) * a) := by rw [Real.rpow_add hT0, Real.rpow_one]
      _ ≤ T ^ A := Real.rpow_le_rpow_of_exponent_le hT (mvt_exponent_le hε hε1 hσ)
  have hXb : X * X ^ a ≤ T ^ A := by
    have h1 : X * X ^ a = X ^ (2 - 2 * σ) := by
      rw [show (2 - 2 * σ) = 1 + a by rw [ha]; ring, Real.rpow_add hX0, Real.rpow_one]
    rw [h1]
    exact window_diagonal_le hT hX0.le hX2 (by linarith) hε.le
  have hmain : (2 * T + 2 ^ 36 * X) * X ^ a ≤ (2 + 2 ^ 36) * T ^ A := by
    calc (2 * T + 2 ^ 36 * X) * X ^ a = 2 * (T * X ^ a) + 2 ^ 36 * (X * X ^ a) := by ring
      _ ≤ 2 * T ^ A + 2 ^ 36 * T ^ A :=
          add_le_add (mul_le_mul_of_nonneg_left hTa (by norm_num))
            (mul_le_mul_of_nonneg_left hXb (by norm_num))
      _ = (2 + 2 ^ 36) * T ^ A := by ring
  have hF1 : T + 1 + 4 * L * (1 + Real.log L) ≤ (2 * T + 2 ^ 36 * X) * Q := by
    have h4 : 4 * L * (1 + Real.log L) ≤ 4 * (2 ^ 34 * X) * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num)) hlogL (by linarith) (by positivity)
    have hTQ : 2 * T ≤ 2 * T * Q := le_mul_of_one_le_right (by linarith) hQ
    have hexp : (2 * T + 2 ^ 36 * X) * Q = 2 * T * Q + 4 * (2 ^ 34 * X) * Q := by ring
    rw [hexp]
    linarith
  have hF2 : 1 + 2 * Real.log L ≤ 2 * Q := by linarith
  have hprod : (T + 1 + 4 * L * (1 + Real.log L)) * (1 + 2 * Real.log L) * G
      ≤ ((2 * T + 2 ^ 36 * X) * Q) * (2 * Q) * (2 ^ 34 * X ^ a * P) :=
    mul_le_mul (mul_le_mul hF1 hF2 (by linarith) (by positivity)) hG hG0 (by positivity)
  have hVsq : 1 / Q ^ 68 ≤ (V ^ ℓ) ^ 2 := by
    calc 1 / Q ^ 68 = (1 / Q ^ 34) ^ 2 := by rw [div_pow, one_pow, ← pow_mul]
      _ ≤ (V ^ ℓ) ^ 2 := pow_le_pow_left₀ (by positivity) hV 2
  have hc : c ≤ Q ^ 68 * (((2 * T + 2 ^ 36 * X) * Q) * (2 * Q) * (2 ^ 34 * X ^ a * P)) := by
    have h1 : c * (1 / Q ^ 68) ≤ c * (V ^ ℓ) ^ 2 := mul_le_mul_of_nonneg_left hVsq hc0
    have h2 := le_trans (le_trans h1 hcount) hprod
    rw [mul_one_div, div_le_iff₀ (pow_pos hQ0 _)] at h2
    linarith
  refine le_trans hc ?_
  have hQP : 0 ≤ Q ^ 68 * Q * Q * P :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hQ0.le _) hQ0.le) hQ0.le) hP
  calc Q ^ 68 * (((2 * T + 2 ^ 36 * X) * Q) * (2 * Q) * (2 ^ 34 * X ^ a * P))
      = 2 ^ 35 * (Q ^ 68 * Q * Q * P) * ((2 * T + 2 ^ 36 * X) * X ^ a) := by ring
    _ ≤ 2 ^ 35 * (Q ^ 68 * Q * Q * P) * ((2 + 2 ^ 36) * T ^ A) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num) hQP)
    _ = 2 ^ 35 * (2 + 2 ^ 36) * (Q ^ 68 * Q * Q * P) * T ^ A := by ring

/-- **The Huxley threshold.**  In the range `σ ≥ 3/4 + ε/32`, with `U = ℓ/V^ℓ ≤ 34 Q^{34}` and
`3·34²·1537·2^{51}·Q^{68}P ≤ T^{ε/24}`, the mass satisfies
`G(1 + 1536√(3L/4π)) ≤ (1/U)²/3`. -/
theorem class_huxley_threshold_arith {T X σ ε Q P L G U : ℝ}
    (hT : 1 ≤ T) (hX1 : T ^ (2 / 3 : ℝ) ≤ X) (hXge : 1 ≤ X) (hσ : 3 / 4 + ε / 32 ≤ σ)
    (hε : 0 < ε) (hQ : 1 ≤ Q) (hP : 0 ≤ P) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ 34 * X)
    (hG : G ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * P) (hU0 : 0 < U) (hU : U ≤ 34 * Q ^ 34)
    (hbig : 3 * 34 ^ 2 * 1537 * 2 ^ 51 * (Q ^ 68 * P) ≤ T ^ (ε / 24)) :
    G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi))) ≤ (1 / U) ^ 2 / 3 := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  -- the square root
  have hsq1 : Real.sqrt (3 * L / (4 * Real.pi)) ≤ Real.sqrt L := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hsq2 : Real.sqrt L ≤ 2 ^ 17 * X ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt L ≤ Real.sqrt ((2 ^ 17) ^ 2 * X) := by
          apply Real.sqrt_le_sqrt
          calc L ≤ 2 ^ 34 * X := hL
            _ = (2 ^ 17) ^ 2 * X := by norm_num
      _ = 2 ^ 17 * Real.sqrt X := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hone : (1 : ℝ) ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hsqrtL : 1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)) ≤ 1537 * 2 ^ 17 * X ^ ((1 : ℝ) / 2) := by
    linarith
  -- the power of `X`
  have hXs : X ^ (1 - 2 * σ) * X ^ ((1 : ℝ) / 2) = X ^ ((3 : ℝ) / 2 - 2 * σ) := by
    rw [← Real.rpow_add hX0]
    ring_nf
  have hXd : X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ T ^ (-(ε / 24)) := by
    calc X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ X ^ (-(ε / 16)) :=
          Real.rpow_le_rpow_of_exponent_le hXge (by linarith)
      _ ≤ T ^ ((2 / 3) * (-(ε / 16))) := rpow_window_lower hT hX1 (by linarith)
      _ = T ^ (-(ε / 24)) := by ring_nf
  have hstep : G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)))
      ≤ 1537 * 2 ^ 51 * P * T ^ (-(ε / 24)) := by
    calc G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)))
        ≤ (2 ^ 34 * X ^ (1 - 2 * σ) * P) * (1537 * 2 ^ 17 * X ^ ((1 : ℝ) / 2)) :=
          mul_le_mul hG hsqrtL (by positivity) (by positivity)
      _ = 1537 * 2 ^ 51 * P * (X ^ (1 - 2 * σ) * X ^ ((1 : ℝ) / 2)) := by ring
      _ = 1537 * 2 ^ 51 * P * X ^ ((3 : ℝ) / 2 - 2 * σ) := by rw [hXs]
      _ ≤ 1537 * 2 ^ 51 * P * T ^ (-(ε / 24)) :=
          mul_le_mul_of_nonneg_left hXd (by positivity)
  refine le_trans hstep ?_
  have hTe0 : 0 < T ^ (ε / 24) := Real.rpow_pos_of_pos hT0 _
  have hTeps : T ^ (-(ε / 24)) = 1 / T ^ (ε / 24) := by rw [Real.rpow_neg hT0.le, one_div]
  have hU2 : U ^ 2 ≤ 34 ^ 2 * Q ^ 68 := by
    calc U ^ 2 ≤ (34 * Q ^ 34) ^ 2 := pow_le_pow_left₀ hU0.le hU 2
      _ = 34 ^ 2 * Q ^ 68 := by ring
  rw [hTeps, one_div_pow, div_div, le_div_iff₀ (by positivity)]
  have hQ68 : 0 ≤ Q ^ 68 := pow_nonneg hQ0.le _
  calc 1537 * 2 ^ 51 * P * (1 / T ^ (ε / 24)) * (U ^ 2 * 3)
      = 3 * 1537 * 2 ^ 51 * P * U ^ 2 / T ^ (ε / 24) := by ring
    _ ≤ 3 * 1537 * 2 ^ 51 * P * (34 ^ 2 * Q ^ 68) / T ^ (ε / 24) := by
        apply div_le_div_of_nonneg_right _ hTe0.le
        exact mul_le_mul_of_nonneg_left hU2 (by positivity)
    _ = (3 * 34 ^ 2 * 1537 * 2 ^ 51 * (Q ^ 68 * P)) / T ^ (ε / 24) := by ring
    _ ≤ 1 := by
        rw [div_le_one hTe0]
        exact hbig

/-- The constant of the Huxley range. -/
def classHuxleyConstant : ℝ := 34 ^ 3 * 6 * (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68)

/-- **The Huxley range.**  With `R ≥ Q^{136}P³` and `R ≥ P`, a Huxley count
`c(1/U)² ≤ ℓ((T(1284G)²/(1/U)⁴ + 1)·2G(L + 12πL(1 + log(T+1))))` gives
`c ≤ classHuxleyConstant·(Q^{68}·R·Q)·T^{(8/3+ε)(1-σ)}`. -/
theorem class_count_huxley_arith {T X σ ε Q P R L G U c : ℝ} {ℓ : ℕ}
    (hT : 1 ≤ T) (hX1 : T ^ (2 / 3 : ℝ) ≤ X) (hX2 : X ≤ T ^ (4 / 3 : ℝ)) (hXge : 1 ≤ X)
    (hσ34 : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hQ : 1 ≤ Q) (hQlow : 36 * (1 + Real.log T) ≤ Q) (hP : 0 ≤ P) (hcube : Q ^ 136 * P ^ 3 ≤ R)
    (hsingle : P ≤ R) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ 34 * X) (hG0 : 0 ≤ G)
    (hG : G ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * P) (hU0 : 0 < U) (hU : U ≤ 34 * Q ^ 34)
    (hℓ : (ℓ : ℝ) ≤ 34)
    (hcount : c * (1 / U) ^ 2 ≤ ℓ * ((T * (1284 * G) ^ 2 / (1 / U) ^ 4 + 1) *
      (2 * G * (L + 12 * Real.pi * L * (1 + Real.log (T + 1)))))) :
    c ≤ classHuxleyConstant * (Q ^ 68 * R * Q) * T ^ ((8 / 3 + ε) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  set A := (8 / 3 + ε) * (1 - σ) with hA
  have hTA0 : 0 ≤ T ^ A := Real.rpow_nonneg hT0.le _
  have hR0 : 0 ≤ R := le_trans hP hsingle
  -- solve for `c`
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
  -- the pieces
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
  have hGL : G * L ≤ 2 ^ 68 * X ^ (2 - 2 * σ) * P := by
    have h1 : X ^ (1 - 2 * σ) * X = X ^ (2 - 2 * σ) := by
      rw [show (2 - 2 * σ) = (1 - 2 * σ) + 1 by ring, Real.rpow_add hX0, Real.rpow_one]
    calc G * L ≤ (2 ^ 34 * X ^ (1 - 2 * σ) * P) * (2 ^ 34 * X) :=
          mul_le_mul hG hL (by linarith) (by positivity)
      _ = 2 ^ 68 * (X ^ (1 - 2 * σ) * X) * P := by ring
      _ = 2 ^ 68 * X ^ (2 - 2 * σ) * P := by rw [h1]
  have hG3L : G ^ 2 * (G * L) ≤ 2 ^ 136 * X ^ (4 - 6 * σ) * P ^ 3 := by
    have h1 : (X ^ (1 - 2 * σ)) ^ 2 * X ^ (2 - 2 * σ) = X ^ (4 - 6 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
      ring_nf
    have hGL0 : 0 ≤ G * L := mul_nonneg hG0 (by linarith)
    calc G ^ 2 * (G * L) ≤ (2 ^ 34 * X ^ (1 - 2 * σ) * P) ^ 2 * (2 ^ 68 * X ^ (2 - 2 * σ) * P) :=
          mul_le_mul (pow_le_pow_left₀ hG0 hG 2) hGL hGL0 (by positivity)
      _ = 2 ^ 136 * ((X ^ (1 - 2 * σ)) ^ 2 * X ^ (2 - 2 * σ)) * P ^ 3 := by ring
      _ = 2 ^ 136 * X ^ (4 - 6 * σ) * P ^ 3 := by rw [h1]
  have hX46 : T * X ^ (4 - 6 * σ) ≤ T ^ A := by
    calc T * X ^ (4 - 6 * σ) ≤ T * T ^ ((2 / 3) * (4 - 6 * σ)) :=
          mul_le_mul_of_nonneg_left (rpow_window_lower hT hX1 (by linarith)) hT0.le
      _ = T ^ (1 + (2 / 3) * (4 - 6 * σ)) := by rw [Real.rpow_add hT0, Real.rpow_one]
      _ ≤ T ^ A := by
          apply Real.rpow_le_rpow_of_exponent_le hT
          have := huxley_exponent_le hσ34
          nlinarith
  have hX22 : X ^ (2 - 2 * σ) ≤ T ^ A := window_diagonal_le hT hX0.le hX2 hσ1 hε.le
  have hU4 : U ^ 4 ≤ 34 ^ 4 * Q ^ 136 := by
    calc U ^ 4 ≤ (34 * Q ^ 34) ^ 4 := pow_le_pow_left₀ hU0.le hU 4
      _ = 34 ^ 4 * Q ^ 136 := by ring
  have hU2 : U ^ 2 ≤ 34 ^ 2 * Q ^ 68 := by
    calc U ^ 2 ≤ (34 * Q ^ 34) ^ 2 := pow_le_pow_left₀ hU0.le hU 2
      _ = 34 ^ 2 * Q ^ 68 := by ring
  have hQ136 : 0 ≤ Q ^ 136 := pow_nonneg hQ0.le _
  have hinner : 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L
      ≤ (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ A := by
    have h1 : T * (G ^ 2 * (G * L)) ≤ 2 ^ 136 * P ^ 3 * T ^ A := by
      calc T * (G ^ 2 * (G * L)) ≤ T * (2 ^ 136 * X ^ (4 - 6 * σ) * P ^ 3) :=
            mul_le_mul_of_nonneg_left hG3L hT0.le
        _ = 2 ^ 136 * P ^ 3 * (T * X ^ (4 - 6 * σ)) := by ring
        _ ≤ 2 ^ 136 * P ^ 3 * T ^ A :=
            mul_le_mul_of_nonneg_left hX46 (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hP _))
    have h2 : G * L ≤ 2 ^ 68 * P * T ^ A := by
      calc G * L ≤ 2 ^ 68 * X ^ (2 - 2 * σ) * P := hGL
        _ = 2 ^ 68 * P * X ^ (2 - 2 * σ) := by ring
        _ ≤ 2 ^ 68 * P * T ^ A :=
            mul_le_mul_of_nonneg_left hX22 (mul_nonneg (pow_nonneg (by norm_num) _) hP)
    have h3 : 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L)))
        ≤ 1284 ^ 2 * (34 ^ 4 * Q ^ 136) * (2 ^ 136 * P ^ 3 * T ^ A) := by
      have hTG : 0 ≤ T * (G ^ 2 * (G * L)) := by
        have : 0 ≤ G * L := mul_nonneg hG0 (by linarith)
        positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hU4 (by norm_num)) h1 hTG
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hQ136))
    have h4 : 1284 ^ 2 * (34 ^ 4 * Q ^ 136) * (2 ^ 136 * P ^ 3 * T ^ A)
        = 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * (Q ^ 136 * P ^ 3) * T ^ A := by ring
    have h5 : 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * (Q ^ 136 * P ^ 3) * T ^ A
        ≤ 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * R * T ^ A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by norm_num)) hTA0
    have h6 : 2 ^ 68 * P * T ^ A ≤ 2 ^ 68 * R * T ^ A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsingle (by norm_num)) hTA0
    have h7 : (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ A
        = 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * R * T ^ A + 2 ^ 68 * R * T ^ A := by ring
    rw [h7]
    linarith
  have hinner0 : 0 ≤ 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L := by
    have : 0 ≤ G * L := mul_nonneg hG0 (by linarith)
    positivity
  have hlog0 : 0 ≤ 1 + 12 * Real.pi * (1 + Real.log (T + 1)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 1 by linarith)
    positivity
  have hQ68 : 0 ≤ Q ^ 68 := pow_nonneg hQ0.le _
  calc U ^ 2 * (ℓ * (2 * (1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L)
        * (1 + 12 * Real.pi * (1 + Real.log (T + 1)))))
      ≤ (34 ^ 2 * Q ^ 68) * (34 * (2 * ((1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ A)
          * (3 * Q))) := by
        have hin2 : 0 ≤ 2 * (1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L)
            * (1 + 12 * Real.pi * (1 + Real.log (T + 1))) :=
          mul_nonneg (mul_nonneg (by norm_num) hinner0) hlog0
        have hKR : 0 ≤ (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ A :=
          mul_nonneg (mul_nonneg (by norm_num) hR0) hTA0
        apply mul_le_mul hU2 _ (mul_nonneg (Nat.cast_nonneg _) hin2)
          (mul_nonneg (by norm_num) hQ68)
        apply mul_le_mul hℓ _ hin2 (by norm_num)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hinner (by norm_num)) hlogT1 hlog0
          (mul_nonneg (by norm_num) hKR)
    _ = classHuxleyConstant * (Q ^ 68 * R * Q) * T ^ A := by
        unfold classHuxleyConstant
        ring

end

end RHTower
