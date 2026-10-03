import GaloisForLFunctions.RHTower.ZetaZeroDensityEightThirds

/-!
# Zero density with exponent `33/13` on the edge ranges `σ ≤ 7/10` and `σ ≥ 26/33`

The class count of `exists_class_card_le` raises a block polynomial into the window
`[T^{2/3}, T^{4/3}]`.  The window may be moved to `[T^{33/52}, T^{33/26}]`: it still has ratio two,
and it still contains every block length, because the support ends at `2T^{249/200} ≤ T^{33/26}`.
With `X` in the new window:

* for `σ ≤ 7/10` the mean value count gives `T X^{1-2σ} + X^{2-2σ} ≤ 2T^{(33/13)(1-σ)}`, because
  `1 + (33/52)(1 - 2σ) ≤ (33/13)(1 - σ)` exactly when `σ ≤ 47/66`;
* for `σ ≥ 26/33` Huxley's threshold holds, because `X^{3/2-2σ} ≤ T^{-5/104}`, and the Huxley count
  gives `T X^{4-6σ} + X^{2-2σ} ≤ 2T^{(33/13)(1-σ)}`, because `1 + (33/52)(4 - 6σ) ≤ (33/13)(1 - σ)`
  exactly when `σ ≥ 26/33`.

The arithmetic lemmas are stated for an abstract exponent `E`, with the two power comparisons as
hypotheses, so that each range only supplies its own exponent inequalities.
-/

namespace RHTower

noncomputable section

open Complex Finset Filter RHTower.Sieve

/-! ## The window -/

/-- **A block with a large value ends below `T^{33/26}`.** -/
theorem block_le_edge_of_large {T : ℝ} (hT : (2 : ℝ) ^ (400 : ℕ) ≤ T) {j i : ℕ} {σ' t V : ℝ}
    (hV : 0 < V)
    (hbig : V ≤ ‖dpoly (classCoeff (densityBlockLength T) (densityMollifierLength T)
      (Real.log (densityBlockLength T * densityMollifierLength T : ℕ)) i σ')
      (detDyadicBlock (densityBlockLength T) (densityMollifierLength T) j) t‖) :
    ((2 ^ j : ℕ) : ℝ) ≤ T ^ (33 / 26 : ℝ) := by
  have hT120 : (2 : ℝ) ^ (120 : ℕ) ≤ T :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hup := densityParameters_upper hT120
  set N := densityBlockLength T
  set y := densityMollifierLength T
  have hne : ∃ k ∈ detDyadicBlock N y j,
      classCoeff N y (Real.log (N * y : ℕ)) i σ' k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero :
        dpoly (classCoeff N y (Real.log (N * y : ℕ)) i σ') (detDyadicBlock N y j) t = 0 := by
      unfold dpoly
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [cterm, hcon k hk]
      simp
    rw [hzero, norm_zero] at hbig
    linarith
  obtain ⟨k, hk, -⟩ := hne
  have hks := mem_detSupport_le (Finset.mem_filter.mp hk).1
  have hkb := mem_detDyadicBlock_bounds hk
  have hkNy : ((2 ^ j : ℕ) : ℝ) ≤ ((N * y : ℕ) : ℝ) := by
    exact_mod_cast le_trans hkb.1 hks.2
  refine le_trans hkNy (le_trans hup ?_)
  have hsplit : T ^ (33 / 26 : ℝ) = T ^ (63 / 2600 : ℝ) * T ^ (249 / 200 : ℝ) := by
    rw [← Real.rpow_add hT0]
    norm_num
  have h2 : (2 : ℝ) ≤ T ^ (63 / 2600 : ℝ) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (400 : ℕ)) ^ (1 / 400 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ T ^ (1 / 400 : ℝ) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
      _ ≤ T ^ (63 / 2600 : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (le_trans (one_le_pow₀ (by norm_num)) hT) (by norm_num)
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)

/-- If `T^{1/50} ≤ K ≤ T^{33/26}` then some power `K^ℓ`, `1 ≤ ℓ ≤ 34`, lies in
`[T^{33/52}, T^{33/26}]`. -/
theorem exists_pow_mem_edge_window {T : ℝ} (hT : 1 < T) {K : ℕ}
    (hK1 : T ^ (1 / 50 : ℝ) ≤ K) (hK2 : (K : ℝ) ≤ T ^ (33 / 26 : ℝ)) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ 34 ∧ T ^ (33 / 52 : ℝ) ≤ (K : ℝ) ^ ℓ ∧
      (K : ℝ) ^ ℓ ≤ T ^ (33 / 26 : ℝ) := by
  classical
  have hT0 : 0 < T := by linarith
  have hK0 : 0 < (K : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hK1
  have h34 : T ^ (33 / 52 : ℝ) ≤ (K : ℝ) ^ (34 : ℕ) := by
    calc T ^ (33 / 52 : ℝ) ≤ T ^ ((1 / 50 : ℝ) * 34) :=
          Real.rpow_le_rpow_of_exponent_le hT.le (by norm_num)
      _ = (T ^ (1 / 50 : ℝ)) ^ (34 : ℕ) := by
          rw [Real.rpow_mul hT0.le]
          norm_cast
      _ ≤ (K : ℝ) ^ (34 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hK1 _
  have hex : ∃ ℓ, T ^ (33 / 52 : ℝ) ≤ (K : ℝ) ^ ℓ := ⟨34, h34⟩
  set ℓ := Nat.find hex with hℓ
  have hspec : T ^ (33 / 52 : ℝ) ≤ (K : ℝ) ^ ℓ := Nat.find_spec hex
  have hle34 : ℓ ≤ 34 := Nat.find_min' hex h34
  have hone : 1 < T ^ (33 / 52 : ℝ) := Real.one_lt_rpow hT (by norm_num)
  have hℓ1 : 1 ≤ ℓ := by
    by_contra h
    have h0 : ℓ = 0 := by omega
    rw [h0, pow_zero] at hspec
    linarith
  refine ⟨ℓ, hℓ1, hle34, hspec, ?_⟩
  rcases eq_or_lt_of_le hℓ1 with h | h
  · rw [← h, pow_one]
    exact hK2
  · have hmin1 : ¬ T ^ (33 / 52 : ℝ) ≤ (K : ℝ) ^ (ℓ - 1) := Nat.find_min hex (by omega)
    have hminK : ¬ T ^ (33 / 52 : ℝ) ≤ (K : ℝ) ^ (1 : ℕ) := Nat.find_min hex h
    push Not at hmin1 hminK
    rw [pow_one] at hminK
    have hsplit : (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hsplit]
    calc (K : ℝ) ^ (ℓ - 1) * K ≤ T ^ (33 / 52 : ℝ) * T ^ (33 / 52 : ℝ) :=
          mul_le_mul hmin1.le hminK.le hK0.le (Real.rpow_nonneg hT0.le _)
      _ = T ^ (33 / 26 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num

/-! ## Exponent comparisons in the window -/

theorem edge_rpow_window_lower {T X a : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (33 / 52 : ℝ) ≤ X)
    (ha : a ≤ 0) : X ^ a ≤ T ^ ((33 / 52) * a) := by
  have hT0 : 0 < T := by linarith
  calc X ^ a ≤ (T ^ (33 / 52 : ℝ)) ^ a :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 ha
    _ = T ^ ((33 / 52) * a) := by rw [← Real.rpow_mul hT0.le]

/-- `X^{2-2σ} ≤ T^{(33/13)(1-σ)}` for `X ≤ T^{33/26}`. -/
theorem edge_window_diagonal_le {T X σ : ℝ} (hT : 1 ≤ T) (hX0 : 0 ≤ X)
    (hX2 : X ≤ T ^ (33 / 26 : ℝ)) (hσ : σ ≤ 1) :
    X ^ (2 - 2 * σ) ≤ T ^ ((33 / 13) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  calc X ^ (2 - 2 * σ) ≤ (T ^ (33 / 26 : ℝ)) ^ (2 - 2 * σ) :=
        Real.rpow_le_rpow hX0 hX2 (by linarith)
    _ = T ^ ((33 / 13) * (1 - σ)) := by
        rw [← Real.rpow_mul hT0.le]
        ring_nf

/-- The mean value term `T X^{1-2σ} ≤ T^{(33/13)(1-σ)}` for `1/2 ≤ σ ≤ 7/10`. -/
theorem edge_mvt_term_le {T X σ : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (33 / 52 : ℝ) ≤ X)
    (hσ0 : 1 / 2 ≤ σ) (hσ : σ ≤ 7 / 10) :
    T * X ^ (1 - 2 * σ) ≤ T ^ ((33 / 13) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  calc T * X ^ (1 - 2 * σ) ≤ T * T ^ ((33 / 52) * (1 - 2 * σ)) :=
        mul_le_mul_of_nonneg_left (edge_rpow_window_lower hT hX1 (by linarith)) hT0.le
    _ = T ^ (1 + (33 / 52) * (1 - 2 * σ)) := by rw [Real.rpow_add hT0, Real.rpow_one]
    _ ≤ T ^ ((33 / 13) * (1 - σ)) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)

/-- The Huxley term `T X^{4-6σ} ≤ T^{(33/13)(1-σ)}` for `σ ≥ 26/33`. -/
theorem edge_huxley_term_le {T X σ : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (33 / 52 : ℝ) ≤ X)
    (hσ : 26 / 33 ≤ σ) :
    T * X ^ (4 - 6 * σ) ≤ T ^ ((33 / 13) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  calc T * X ^ (4 - 6 * σ) ≤ T * T ^ ((33 / 52) * (4 - 6 * σ)) :=
        mul_le_mul_of_nonneg_left (edge_rpow_window_lower hT hX1 (by linarith)) hT0.le
    _ = T ^ (1 + (33 / 52) * (4 - 6 * σ)) := by rw [Real.rpow_add hT0, Real.rpow_one]
    _ ≤ T ^ ((33 / 13) * (1 - σ)) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)

/-- Huxley's threshold decay `X^{3/2-2σ} ≤ T^{-5/104}` for `σ ≥ 26/33`. -/
theorem edge_huxley_decay_le {T X σ : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (33 / 52 : ℝ) ≤ X)
    (hXge : 1 ≤ X) (hσ : 26 / 33 ≤ σ) :
    X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ T ^ (-(5 / 104 : ℝ)) := by
  calc X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ X ^ (-(5 / 66 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hXge (by linarith)
    _ ≤ T ^ ((33 / 52) * (-(5 / 66 : ℝ))) := edge_rpow_window_lower hT hX1 (by norm_num)
    _ = T ^ (-(5 / 104 : ℝ)) := by norm_num

/-! ## The large-value arithmetic with an abstract exponent -/

/-- **The mean value range, abstract exponent.**  If `T X^{1-2σ} ≤ T^E` and `X^{2-2σ} ≤ T^E`, a mean
value count `c·(V^ℓ)² ≤ (T + 1 + 4L(1 + log L))(1 + 2 log L)·G` with the window data gives
`c ≤ 2^{35}(2 + 2^{36}) Q^{68}·Q·Q·P·T^E`. -/
theorem class_count_mvt_arith_of_exponent {T X σ E Q P L G V c : ℝ} {ℓ : ℕ}
    (hT : 1 ≤ T) (hXge : 1 ≤ X) (hTa : T * X ^ (1 - 2 * σ) ≤ T ^ E)
    (hXb : X ^ (2 - 2 * σ) ≤ T ^ E)
    (hQ : 1 ≤ Q) (hP : 0 ≤ P) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ 34 * X)
    (hlogL : 1 + Real.log L ≤ Q) (hG0 : 0 ≤ G) (hG : G ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * P)
    (hV : 1 / Q ^ 34 ≤ V ^ ℓ) (hc0 : 0 ≤ c)
    (hcount : c * (V ^ ℓ) ^ 2 ≤ (T + 1 + 4 * L * (1 + Real.log L)) * (1 + 2 * Real.log L) * G) :
    c ≤ 2 ^ 35 * (2 + 2 ^ 36) * (Q ^ 68 * Q * Q * P) * T ^ E := by
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
  have hmain : (2 * T + 2 ^ 36 * X) * X ^ a ≤ (2 + 2 ^ 36) * T ^ E := by
    calc (2 * T + 2 ^ 36 * X) * X ^ a = 2 * (T * X ^ a) + 2 ^ 36 * (X * X ^ a) := by ring
      _ ≤ 2 * T ^ E + 2 ^ 36 * T ^ E :=
          add_le_add (mul_le_mul_of_nonneg_left hTa (by norm_num))
            (mul_le_mul_of_nonneg_left hXb' (by norm_num))
      _ = (2 + 2 ^ 36) * T ^ E := by ring
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
    _ ≤ 2 ^ 35 * (Q ^ 68 * Q * Q * P) * ((2 + 2 ^ 36) * T ^ E) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num) hQP)
    _ = 2 ^ 35 * (2 + 2 ^ 36) * (Q ^ 68 * Q * Q * P) * T ^ E := by ring

/-- **The Huxley threshold, abstract decay.**  If `X^{3/2-2σ} ≤ T^{-δ}`, `U ≤ 34 Q^{34}` and
`3·34²·1537·2^{51}·Q^{68}P ≤ T^δ`, then `G(1 + 1536√(3L/4π)) ≤ (1/U)²/3`. -/
theorem class_huxley_threshold_arith_of_decay {T X σ δ Q P L G U : ℝ}
    (hT : 1 ≤ T) (hXge : 1 ≤ X) (hXd : X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ T ^ (-δ))
    (hQ : 1 ≤ Q) (hP : 0 ≤ P) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ 34 * X)
    (hG : G ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * P) (hU0 : 0 < U) (hU : U ≤ 34 * Q ^ 34)
    (hbig : 3 * 34 ^ 2 * 1537 * 2 ^ 51 * (Q ^ 68 * P) ≤ T ^ δ) :
    G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi))) ≤ (1 / U) ^ 2 / 3 := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
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
  have hsqrtL :
      1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)) ≤ 1537 * 2 ^ 17 * X ^ ((1 : ℝ) / 2) := by
    linarith
  have hXs : X ^ (1 - 2 * σ) * X ^ ((1 : ℝ) / 2) = X ^ ((3 : ℝ) / 2 - 2 * σ) := by
    rw [← Real.rpow_add hX0]
    ring_nf
  have hstep : G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)))
      ≤ 1537 * 2 ^ 51 * P * T ^ (-δ) := by
    calc G * (1 + 1536 * Real.sqrt (3 * L / (4 * Real.pi)))
        ≤ (2 ^ 34 * X ^ (1 - 2 * σ) * P) * (1537 * 2 ^ 17 * X ^ ((1 : ℝ) / 2)) :=
          mul_le_mul hG hsqrtL (by positivity) (by positivity)
      _ = 1537 * 2 ^ 51 * P * (X ^ (1 - 2 * σ) * X ^ ((1 : ℝ) / 2)) := by ring
      _ = 1537 * 2 ^ 51 * P * X ^ ((3 : ℝ) / 2 - 2 * σ) := by rw [hXs]
      _ ≤ 1537 * 2 ^ 51 * P * T ^ (-δ) := mul_le_mul_of_nonneg_left hXd (by positivity)
  refine le_trans hstep ?_
  have hTe0 : 0 < T ^ δ := Real.rpow_pos_of_pos hT0 _
  have hTeps : T ^ (-δ) = 1 / T ^ δ := by rw [Real.rpow_neg hT0.le, one_div]
  have hU2 : U ^ 2 ≤ 34 ^ 2 * Q ^ 68 := by
    calc U ^ 2 ≤ (34 * Q ^ 34) ^ 2 := pow_le_pow_left₀ hU0.le hU 2
      _ = 34 ^ 2 * Q ^ 68 := by ring
  rw [hTeps, one_div_pow, div_div, le_div_iff₀ (by positivity)]
  calc 1537 * 2 ^ 51 * P * (1 / T ^ δ) * (U ^ 2 * 3)
      = 3 * 1537 * 2 ^ 51 * P * U ^ 2 / T ^ δ := by ring
    _ ≤ 3 * 1537 * 2 ^ 51 * P * (34 ^ 2 * Q ^ 68) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hTe0.le
        exact mul_le_mul_of_nonneg_left hU2 (by positivity)
    _ = (3 * 34 ^ 2 * 1537 * 2 ^ 51 * (Q ^ 68 * P)) / T ^ δ := by ring
    _ ≤ 1 := by
        rw [div_le_one hTe0]
        exact hbig

/-- **The Huxley range, abstract exponent.**  If `T X^{4-6σ} ≤ T^E` and `X^{2-2σ} ≤ T^E`, a Huxley
count gives `c ≤ classHuxleyConstant·(Q^{68}·R·Q)·T^E`. -/
theorem class_count_huxley_arith_of_exponent {T X σ E Q P R L G U c : ℝ} {ℓ : ℕ}
    (hT : 1 ≤ T) (hXge : 1 ≤ X) (hX46 : T * X ^ (4 - 6 * σ) ≤ T ^ E)
    (hX22 : X ^ (2 - 2 * σ) ≤ T ^ E)
    (hQ : 1 ≤ Q) (hQlow : 36 * (1 + Real.log T) ≤ Q) (hP : 0 ≤ P) (hcube : Q ^ 136 * P ^ 3 ≤ R)
    (hsingle : P ≤ R) (hL1 : 1 ≤ L) (hL : L ≤ 2 ^ 34 * X) (hG0 : 0 ≤ G)
    (hG : G ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * P) (hU0 : 0 < U) (hU : U ≤ 34 * Q ^ 34)
    (hℓ : (ℓ : ℝ) ≤ 34)
    (hcount : c * (1 / U) ^ 2 ≤ ℓ * ((T * (1284 * G) ^ 2 / (1 / U) ^ 4 + 1) *
      (2 * G * (L + 12 * Real.pi * L * (1 + Real.log (T + 1)))))) :
    c ≤ classHuxleyConstant * (Q ^ 68 * R * Q) * T ^ E := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 < Q := by linarith
  have hTA0 : 0 ≤ T ^ E := Real.rpow_nonneg hT0.le _
  have hR0 : 0 ≤ R := le_trans hP hsingle
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
    calc G ^ 2 * (G * L)
        ≤ (2 ^ 34 * X ^ (1 - 2 * σ) * P) ^ 2 * (2 ^ 68 * X ^ (2 - 2 * σ) * P) :=
          mul_le_mul (pow_le_pow_left₀ hG0 hG 2) hGL hGL0 (by positivity)
      _ = 2 ^ 136 * ((X ^ (1 - 2 * σ)) ^ 2 * X ^ (2 - 2 * σ)) * P ^ 3 := by ring
      _ = 2 ^ 136 * X ^ (4 - 6 * σ) * P ^ 3 := by rw [h1]
  have hU4 : U ^ 4 ≤ 34 ^ 4 * Q ^ 136 := by
    calc U ^ 4 ≤ (34 * Q ^ 34) ^ 4 := pow_le_pow_left₀ hU0.le hU 4
      _ = 34 ^ 4 * Q ^ 136 := by ring
  have hU2 : U ^ 2 ≤ 34 ^ 2 * Q ^ 68 := by
    calc U ^ 2 ≤ (34 * Q ^ 34) ^ 2 := pow_le_pow_left₀ hU0.le hU 2
      _ = 34 ^ 2 * Q ^ 68 := by ring
  have hQ136 : 0 ≤ Q ^ 136 := pow_nonneg hQ0.le _
  have hinner : 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L
      ≤ (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ E := by
    have h1 : T * (G ^ 2 * (G * L)) ≤ 2 ^ 136 * P ^ 3 * T ^ E := by
      calc T * (G ^ 2 * (G * L)) ≤ T * (2 ^ 136 * X ^ (4 - 6 * σ) * P ^ 3) :=
            mul_le_mul_of_nonneg_left hG3L hT0.le
        _ = 2 ^ 136 * P ^ 3 * (T * X ^ (4 - 6 * σ)) := by ring
        _ ≤ 2 ^ 136 * P ^ 3 * T ^ E :=
            mul_le_mul_of_nonneg_left hX46
              (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hP _))
    have h2 : G * L ≤ 2 ^ 68 * P * T ^ E := by
      calc G * L ≤ 2 ^ 68 * X ^ (2 - 2 * σ) * P := hGL
        _ = 2 ^ 68 * P * X ^ (2 - 2 * σ) := by ring
        _ ≤ 2 ^ 68 * P * T ^ E :=
            mul_le_mul_of_nonneg_left hX22 (mul_nonneg (pow_nonneg (by norm_num) _) hP)
    have h3 : 1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L)))
        ≤ 1284 ^ 2 * (34 ^ 4 * Q ^ 136) * (2 ^ 136 * P ^ 3 * T ^ E) := by
      have hTG : 0 ≤ T * (G ^ 2 * (G * L)) := by
        have : 0 ≤ G * L := mul_nonneg hG0 (by linarith)
        positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hU4 (by norm_num)) h1 hTG
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hQ136))
    have h4 : 1284 ^ 2 * (34 ^ 4 * Q ^ 136) * (2 ^ 136 * P ^ 3 * T ^ E)
        = 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * (Q ^ 136 * P ^ 3) * T ^ E := by ring
    have h5 : 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * (Q ^ 136 * P ^ 3) * T ^ E
        ≤ 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * R * T ^ E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by norm_num)) hTA0
    have h6 : 2 ^ 68 * P * T ^ E ≤ 2 ^ 68 * R * T ^ E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsingle (by norm_num)) hTA0
    have h7 : (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ E
        = 1284 ^ 2 * 34 ^ 4 * 2 ^ 136 * R * T ^ E + 2 ^ 68 * R * T ^ E := by ring
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
      ≤ (34 ^ 2 * Q ^ 68) * (34 * (2 * ((1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ E)
          * (3 * Q))) := by
        have hin2 : 0 ≤ 2 * (1284 ^ 2 * U ^ 4 * (T * (G ^ 2 * (G * L))) + G * L)
            * (1 + 12 * Real.pi * (1 + Real.log (T + 1))) :=
          mul_nonneg (mul_nonneg (by norm_num) hinner0) hlog0
        have hKR : 0 ≤ (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) * R * T ^ E :=
          mul_nonneg (mul_nonneg (by norm_num) hR0) hTA0
        apply mul_le_mul hU2 _ (mul_nonneg (Nat.cast_nonneg _) hin2)
          (mul_nonneg (by norm_num) hQ68)
        apply mul_le_mul hℓ _ hin2 (by norm_num)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hinner (by norm_num)) hlogT1 hlog0
          (mul_nonneg (by norm_num) hKR)
    _ = classHuxleyConstant * (Q ^ 68 * R * Q) * T ^ E := by
        unfold classHuxleyConstant
        ring

/-! ## The class count on the edge ranges -/

/-- The mean-value constant is below `2^{300}`. -/
theorem classMvtConstant_le : (2 : ℝ) ^ 35 * (2 + 2 ^ 36) ≤ 2 ^ 300 := by
  calc (2 : ℝ) ^ 35 * (2 + 2 ^ 36) ≤ 2 ^ 35 * 2 ^ 37 :=
        mul_le_mul_of_nonneg_left (by norm_num) (by norm_num)
    _ = 2 ^ 72 := by rw [← pow_add]
    _ ≤ 2 ^ 300 := pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- The Huxley constant is below `2^{300}`. -/
theorem classHuxleyConstant_le : classHuxleyConstant ≤ 2 ^ 300 := by
  have h34 : (34 : ℝ) ≤ 2 ^ 6 := by norm_num
  have h1284 : (1284 : ℝ) ≤ 2 ^ 11 := by norm_num
  have h6 : (6 : ℝ) ≤ 2 ^ 3 := by norm_num
  have h68 : (2 : ℝ) ^ 68 ≤ 2 ^ 182 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hin : (1284 : ℝ) ^ 2 * 34 ^ 4 * 2 ^ 136 ≤ 2 ^ 182 := by
    calc (1284 : ℝ) ^ 2 * 34 ^ 4 * 2 ^ 136 ≤ (2 ^ 11) ^ 2 * (2 ^ 6) ^ 4 * 2 ^ 136 := by
          gcongr
      _ = 2 ^ 182 := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  calc classHuxleyConstant
      = 34 ^ 3 * 6 * (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) := rfl
    _ ≤ (2 ^ 6) ^ 3 * 2 ^ 3 * (2 ^ 182 + 2 ^ 182) := by gcongr
    _ = 2 ^ 204 := by
        rw [← two_mul, ← pow_succ', ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2 ^ 300 := pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- **The class count with exponent `33/13` on the edge ranges.**  For all large `T`, every
`σ ∈ [1/2, 7/10] ∪ [26/33, 1]` and every class `(j, i, σ')` with `σ ≤ σ'`, a `1`-separated set
`W ⊆ [T, 2T]` on which the class polynomial is at least `1/(12J)` has
`#W ≤ C (1 + log T)^E T^{(33/13)(1 - σ)}`, with the constants of `exists_class_card_le`. -/
theorem exists_class_card_le_edge :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → (σ ≤ 7 / 10 ∨ 26 / 33 ≤ σ) →
      ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (12 * (detBlockCount (densityBlockLength T) (densityMollifierLength T) : ℝ))
          ≤ ‖abscissaTaylorPoly (detDyadicBlock (densityBlockLength T) (densityMollifierLength T) j)
              (detCoeffC (densityBlockLength T) (densityMollifierLength T))
              (Real.log (densityBlockLength T * densityMollifierLength T : ℕ)) i σ' t‖) →
        (W.card : ℝ) ≤ classCountConstant * (1 + Real.log T) ^ classCountLogExponent
          * T ^ ((33 / 13) * (1 - σ)) := by
  obtain ⟨TH, hTH⟩ := exists_classBigFacts (show (0 : ℝ) < 15 / 13 by norm_num)
  refine ⟨max ((2 : ℝ) ^ (400 : ℕ)) TH, ?_⟩
  intro T hT σ hσ1 hσ2 hrange j i σ' hσσ' W hW hsep hbig
  have hT400 : (2 : ℝ) ^ (400 : ℕ) ≤ T := le_trans (le_max_left _ _) hT
  have hT120 : (2 : ℝ) ^ (120 : ℕ) ≤ T :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hT400
  have hT1 : (1 : ℝ) ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT400
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hBig := hTH T (le_trans (le_max_right _ _) hT) hT1
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 36 * (1 + Real.log T) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Q ^ (2 ^ 136) := ⟨_, rfl⟩
  rw [← hQdef, ← hPdef] at hBig
  have hthr : 3 * 34 ^ 2 * 1537 * 2 ^ 51 * (Q ^ 68 * P) ≤ T ^ (5 / 104 : ℝ) := by
    have h := hBig.threshold
    rwa [show (15 / 13 : ℝ) / 24 = 5 / 104 by norm_num] at h
  have hQlow : 36 * (1 + Real.log T) ≤ Q := hQdef.symm.le
  have hQ1 : 1 ≤ Q := by
    have := Real.log_nonneg hT1
    linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hP0 : 0 ≤ P := by rw [hPdef]; exact pow_nonneg hQ0.le _
  set N := densityBlockLength T with hNdef
  set y := densityMollifierLength T with hydef
  set J := detBlockCount N y with hJdef
  have hJpos : (0 : ℝ) < J := by
    rw [hJdef, detBlockCount]
    positivity
  have hJQ : 12 * (J : ℝ) ≤ Q := by
    have := detBlockCount_le_log hT120
    linarith
  set V : ℝ := 1 / (12 * (J : ℝ)) with hVdef
  have hV0 : 0 < V := by positivity
  have hVQ : 1 / Q ≤ V := by
    rw [hVdef]
    exact one_div_le_one_div_of_le (by positivity) hJQ
  rcases W.eq_empty_or_nonempty with hWe | ⟨t₀, ht₀⟩
  · rw [hWe, card_empty, Nat.cast_zero]
    unfold classCountConstant
    have hl : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
      (pow_nonneg hl _)) (Real.rpow_nonneg hT0.le _)
  have hbig' : ∀ t ∈ W, V ≤ ‖dpoly (classCoeff N y (Real.log (N * y : ℕ)) i σ')
      (detDyadicBlock N y j) t‖ := by
    intro t ht
    rw [← abscissaTaylorPoly_eq_dpoly]
    exact hbig t ht
  obtain ⟨hK1, -⟩ := block_bounds_of_large hT400 hV0 (hbig' t₀ ht₀)
  have hK2 := block_le_edge_of_large hT400 hV0 (hbig' t₀ ht₀)
  obtain ⟨ℓ, hℓ1, hℓ34, hX1, hX2⟩ := exists_pow_mem_edge_window
      (lt_of_lt_of_le (one_lt_pow₀ one_lt_two (by norm_num)) hT400) hK1 hK2
  have hX2' : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (4 / 3 : ℝ) :=
    le_trans hX2 (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num))
  obtain ⟨hy1, _, _, _, hNy⟩ := densityParameters hT120
  replace hy1 : 1 ≤ y := hy1
  have hN1 : 1 ≤ N := by
    by_contra h
    have h0 : N = 0 := by omega
    rw [hNdef] at h0
    rw [h0] at hNy
    simp at hNy
  set X : ℝ := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hXge1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hσ0 : (0 : ℝ) ≤ σ := le_trans (by norm_num) hσ1
  have hmass := classPowerMass_le (σ := σ) hT1 hℓ1 hℓ34 hX2'
  rw [← hXdef, ← hQdef, ← hPdef] at hmass
  have hLcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
    rw [hXdef]
    push_cast
    ring
  have hL34 : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ 2 ^ 34 * X := by
    rw [hLcast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hℓ34) (by linarith)
  have hL1 : (1 : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hlogL := one_add_log_raised_le hT1 hℓ34 hX2'
  rw [← hQdef] at hlogL
  have hVl : 1 / Q ^ 34 ≤ V ^ ℓ := by
    calc 1 / Q ^ 34 ≤ 1 / Q ^ ℓ := one_div_le_one_div_of_le (pow_pos hQ0 _)
          (pow_le_pow_right₀ hQ1 hℓ34)
      _ = (1 / Q) ^ ℓ := by rw [one_div_pow]
      _ ≤ V ^ ℓ := pow_le_pow_left₀ (by positivity) hVQ ℓ
  have hG0 : 0 ≤ classPowerMass j ℓ σ := by unfold classPowerMass; positivity
  have hdiag := edge_window_diagonal_le hT1 (by linarith) hX2 hσ2
  clear_value N y J V X
  clear hQdef hPdef
  have hl : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hfinal : ∀ K : ℝ, 0 ≤ K → K ≤ 2 ^ 300 →
      K * Q ^ classCountLogExponent * T ^ ((33 / 13) * (1 - σ))
        ≤ classCountConstant * (1 + Real.log T) ^ classCountLogExponent
          * T ^ ((33 / 13) * (1 - σ)) := by
    intro K hK0 hK
    rw [hBig.split]
    unfold classCountConstant
    have e : K * (36 ^ classCountLogExponent * (1 + Real.log T) ^ classCountLogExponent)
        * T ^ ((33 / 13) * (1 - σ)) = K * 36 ^ classCountLogExponent
          * (1 + Real.log T) ^ classCountLogExponent * T ^ ((33 / 13) * (1 - σ)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (pow_nonneg (by norm_num) _)) (pow_nonneg hl _))
      (Real.rpow_nonneg hT0.le _)
  rcases hrange with hlow | hhigh
  · have hmvt := card_mul_pow_le_class_mvt (N := N) (y := y) (j := j) (i := i) (ℓ := ℓ)
      (σ := σ) (σ' := σ') (T := T) (V := V) (W := W) hN1 hy1 hℓ1 hσ0 hσσ' hT0.le hV0.le hW hsep
      hbig'
    have hc := class_count_mvt_arith_of_exponent hT1 hXge1 (edge_mvt_term_le hT1 hX1 hσ1 hlow)
      hdiag hQ1 hP0 hL1 hL34 hlogL hG0 hmass hVl (Nat.cast_nonneg _) hmvt
    refine le_trans hc (le_trans ?_ (hfinal _ (by norm_num) classMvtConstant_le))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
    exact mul_le_mul_of_nonneg_left hBig.meanValue (by norm_num)
  · have hVlpos : 0 < V ^ ℓ := pow_pos hV0 ℓ
    have hℓR34 : (ℓ : ℝ) ≤ 34 := by exact_mod_cast hℓ34
    obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = ℓ / V ^ ℓ := ⟨_, rfl⟩
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    have hU0 : 0 < U := by rw [hUdef]; positivity
    have hU : U ≤ 34 * Q ^ 34 := by
      rw [hUdef, div_le_iff₀ hVlpos]
      have h1 : 1 ≤ Q ^ 34 * V ^ ℓ := by
        have := mul_le_mul_of_nonneg_left hVl (pow_nonneg hQ0.le 34)
        rwa [mul_one_div_cancel (pow_pos hQ0 _).ne'] at this
      nlinarith [pow_pos hQ0 34]
    have hVU : V ^ ℓ / ℓ = 1 / U := by rw [hUdef, one_div_div]
    have hthr' := class_huxley_threshold_arith_of_decay hT1 hXge1
      (edge_huxley_decay_le hT1 hX1 hXge1 hhigh) hQ1 hP0 hL1 hL34 hmass hU0 hU hthr
    rw [← hVU] at hthr'
    have hhux := card_mul_pow_le_class_huxley (N := N) (y := y) (j := j) (i := i) (ℓ := ℓ)
      (σ := σ) (σ' := σ') (T := T) (V := V) (W := W) hN1 hy1 hℓ1 hσ0 hσσ' hT0.le hV0 hW hsep
      hbig' hthr'
    rw [hVU] at hhux
    have hc := class_count_huxley_arith_of_exponent hT1 hXge1
      (edge_huxley_term_le hT1 hX1 hhigh) hdiag hQ1 hQlow hP0 hBig.cube hBig.single hL1 hL34
      hG0 hmass hU0 hU hℓR34 hhux
    have hHC0 : 0 ≤ classHuxleyConstant := by unfold classHuxleyConstant; norm_num
    refine le_trans hc (le_trans ?_ (hfinal _ hHC0 classHuxleyConstant_le))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
    exact mul_le_mul_of_nonneg_left hBig.huxley hHC0

/-! ## The box count -/

/-- **A class count bound gives a box count bound.**  If every separated large-value class at height
`T ≥ 2^{400}` has at most `C (1 + log T)^E T^e` points, then the box `σ ≤ Re ρ`, `T ≤ Im ρ ≤ 2T`
has at most `zeroDensityConstant (1 + log T)^{E+4} T^e` zero copies. -/
theorem zeroHeightBox_ncard_le_of_classCount {T σ e : ℝ} (hT400 : (2 : ℝ) ^ (400 : ℕ) ≤ T)
    (hσ1 : 1 / 2 ≤ σ)
    (hclass : ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (12 * (detBlockCount (densityBlockLength T) (densityMollifierLength T) : ℝ))
          ≤ ‖abscissaTaylorPoly (detDyadicBlock (densityBlockLength T) (densityMollifierLength T) j)
              (detCoeffC (densityBlockLength T) (densityMollifierLength T))
              (Real.log (densityBlockLength T * densityMollifierLength T : ℕ)) i σ' t‖) →
        (W.card : ℝ) ≤ classCountConstant * (1 + Real.log T) ^ classCountLogExponent * T ^ e) :
    ((zeroHeightBox σ T).ncard : ℝ)
      ≤ zeroDensityConstant * (1 + Real.log T) ^ (classCountLogExponent + 4) * T ^ e := by
  have hT120 : (2 : ℝ) ^ (120 : ℕ) ≤ T :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hT400
  have hT1 : (1 : ℝ) ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT400
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  set LT : ℝ := 1 + Real.log T with hLT
  have hLT1 : 1 ≤ LT := by rw [hLT]; linarith [Real.log_nonneg hT1]
  have hJ := detBlockCount_le_log hT120
  have hJ8 : (detBlockCount (densityBlockLength T) (densityMollifierLength T) : ℝ) + 8
      ≤ 11 * LT := by linarith
  have hM := floor_log_add_one_le hT120
  have hCap := densityWindowCapacity_le hT1
  have hCap00 : 0 ≤ densityWindowCapacity T := by
    unfold densityWindowCapacity
    have := abs_nonneg xiLineTwoLogDerivConstant
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T + 5 from
      le_add_of_nonneg_of_le (by positivity) (by norm_num))
    positivity
  obtain ⟨j, hj, i, hi, m, hm, W, hWT, hWsep, hWbig, hcount⟩ :=
    exists_separated_class_of_zeroHeightBox hT120 hσ1
  have hΛ0 : 0 ≤ Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ) :=
    Real.log_nonneg (by
      obtain ⟨_, _, _, _, hNy⟩ := densityParameters hT120
      exact_mod_cast (by omega : 1 ≤ densityBlockLength T * densityMollifierLength T))
  have hσσ' : σ ≤ σ + m / Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ) :=
    le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hΛ0)
  have hW := hclass j i _ hσσ' W hWT hWsep hWbig
  set E : ℕ := classCountLogExponent with hE
  set J : ℕ := detBlockCount (densityBlockLength T) (densityMollifierLength T) with hJdef
  set M : ℕ := ⌊Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ)⌋₊ + 1
    with hMdef
  have hcountR : ((zeroHeightBox σ T).ncard : ℝ)
      ≤ ((J : ℝ) * ((J : ℝ) + 8) * (M : ℝ)) * densityWindowCapacity T * W.card := by
    have h := hcount
    push_cast at h
    exact h
  have hfac : (J : ℝ) * ((J : ℝ) + 8) * (M : ℝ) ≤ (3 * LT) * (11 * LT) * (3 * LT) :=
    mul_le_mul (mul_le_mul hJ hJ8 (by positivity) (by positivity)) hM (Nat.cast_nonneg _)
      (by positivity)
  have hCapT : densityWindowCapacity T ≤ 16 * (|xiLineTwoLogDerivConstant| + 3) * LT := hCap
  have hWc0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hTA : 0 ≤ T ^ e := Real.rpow_nonneg hT0.le _
  have hLTE : 0 ≤ LT ^ E := pow_nonneg (by linarith) _
  have hcc : 0 ≤ classCountConstant := by
    unfold classCountConstant
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
  calc ((zeroHeightBox σ T).ncard : ℝ)
      ≤ ((J : ℝ) * ((J : ℝ) + 8) * (M : ℝ)) * densityWindowCapacity T * W.card := hcountR
    _ ≤ ((3 * LT) * (11 * LT) * (3 * LT)) * (16 * (|xiLineTwoLogDerivConstant| + 3) * LT)
          * (classCountConstant * LT ^ E * T ^ e) :=
        mul_le_mul (mul_le_mul hfac hCapT hCap00 (by positivity)) hW hWc0 (by positivity)
    _ = zeroDensityConstant * (LT ^ 4 * LT ^ E) * T ^ e := by
        unfold zeroDensityConstant
        ring
    _ = zeroDensityConstant * LT ^ (E + 4) * T ^ e := by
        rw [← pow_add, add_comm 4 E]

/-- **Zero density with exponent `33/13` on the edge ranges.**  For all large `T` and every
`σ ∈ [1/2, 7/10] ∪ [26/33, 1]`,
`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ C (1 + log T)^{E+4} T^{(33/13)(1 - σ)}`. -/
theorem exists_zeroHeightBox_ncard_le_edge :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → (σ ≤ 7 / 10 ∨ 26 / 33 ≤ σ) →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ zeroDensityConstant * (1 + Real.log T) ^ (classCountLogExponent + 4)
          * T ^ ((33 / 13) * (1 - σ)) := by
  obtain ⟨T₁, hT₁⟩ := exists_class_card_le_edge
  refine ⟨max T₁ ((2 : ℝ) ^ (400 : ℕ)), fun T hT σ hσ1 hσ2 hrange => ?_⟩
  exact zeroHeightBox_ncard_le_of_classCount (le_trans (le_max_right _ _) hT) hσ1
    (hT₁ T (le_trans (le_max_left _ _) hT) σ hσ1 hσ2 hrange)

end

end RHTower
