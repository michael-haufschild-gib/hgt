import GaloisForLFunctions.HTGeometry.UniformShapeBounds

/-!
# The dominance order of equation (26), uniformly on a vertical tube

A subordinate shape vanishes against the dominant one uniformly in the abscissa.  Each of the three
cases of the order rests on an abscissa-free estimate built in the previous steps: `Γ` decaying faster
than every power, the argument power `s^a` with `a < 0`, and the logarithm power `L^b` with `b < 0`.

Since quotients of shapes are shapes, this gives the tube form of the ratio limits the residue
assembly consumes.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A negative integer power is antitone in the base above `1`. -/
theorem zpow_le_zpow_of_le_of_neg {x y : ℝ} {b : ℤ} (hx : 1 ≤ x) (hxy : x ≤ y) (hb : b < 0) :
    y ^ b ≤ x ^ b := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = -((n : ℤ) + 1) := ⟨(-b - 1).toNat, by omega⟩
  have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  rw [hn, zpow_neg, zpow_neg, hcast, zpow_natCast, zpow_natCast]
  have hpow : x ^ (n + 1) ≤ y ^ (n + 1) := pow_le_pow_left₀ (le_of_lt hxpos) hxy _
  have hxn : (0 : ℝ) < x ^ (n + 1) := by positivity
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hxn hpow

/-- The logarithm power with a negative exponent vanishes. -/
theorem tendsto_log_zpow_neg {b : ℤ} (hb : b < 0) :
    Tendsto (fun t : ℝ => (Real.log t) ^ b) atTop (nhds 0) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = -((n : ℤ) + 1) := ⟨(-b - 1).toNat, by omega⟩
  have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have hpow : Tendsto (fun t : ℝ => (Real.log t) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero n)).comp Real.tendsto_log_atTop
  have hinv := hpow.inv_tendsto_atTop
  refine hinv.congr fun t => ?_
  rw [Pi.inv_apply, hn, zpow_neg, hcast, zpow_natCast]

/-- **The logarithmic case of the dominance order, uniformly.** -/
theorem tubeLimit_gammaShapeZ_zero_of_log_neg {M : ℝ} {b : ℤ} (hb : b < 0) :
    TubeLimit M (fun σ t => gammaShapeZ σ 0 0 b t) 0 := by
  refine tubeLimit_of_squeeze (T₀ := 3) (g := fun t => (Real.log t) ^ b) ?_
    (tendsto_log_zpow_neg hb)
  intro σ t hσ hσM ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hre : (vertLog t).re = Real.log t := by
    rw [vertLog]
    simp
  have hlow : Real.log t ≤ ‖vertLog t‖ := by
    calc Real.log t = (vertLog t).re := hre.symm
      _ ≤ ‖vertLog t‖ := Complex.re_le_norm _
  have hshape : gammaShapeZ σ 0 0 b t = vertLog t ^ b := by
    rw [gammaShapeZ, zpow_zero, zpow_zero, one_mul, one_mul]
  rw [hshape, norm_zpow]
  exact zpow_le_zpow_of_le_of_neg hlog1 hlow hb

/-- **The argument case of the dominance order, uniformly.** -/
theorem tubeLimit_gammaShapeZ_zero_of_arg_neg {M : ℝ} {a : ℤ} (ha : a < 0) (b : ℤ) :
    TubeLimit M (fun σ t => gammaShapeZ σ 0 a b t) 0 := by
  classical
  refine tubeLimit_of_squeeze (T₀ := 8)
    (g := fun t => (2 * Real.log t) ^ b.toNat / t) ?_ ?_
  · intro σ t hσ hσM ht
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have htpos : (0 : ℝ) < t := by linarith
    have hlogpi : Real.log t + Real.pi / 2 ≤ 2 * Real.log t := by
      have hexp : Real.exp 2 ≤ t := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      have hlog2 : (2 : ℝ) ≤ Real.log t := by
        have := Real.log_le_log (Real.exp_pos 2) hexp
        rwa [Real.log_exp] at this
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      linarith
    have hshape : gammaShapeZ σ 0 a b t
        = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ a * vertLog t ^ b := by
      rw [gammaShapeZ, zpow_zero, one_mul]
    rw [hshape, norm_mul]
    have h1 : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ ≤ t ^ a := by
      have := norm_zpow_vertical_le (M := M) hσ hσM ht1 a
      have htoNat : a.toNat = 0 := by omega
      rwa [htoNat, pow_zero, one_mul] at this
    have h2 : ‖vertLog t ^ b‖ ≤ (2 * Real.log t) ^ b.toNat := by
      refine le_trans (norm_vertLog_zpow_le (by linarith) b) ?_
      refine pow_le_pow_left₀ ?_ hlogpi _
      have hlog0 : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht1
      have hpi0 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
      linarith
    have hta : t ^ a ≤ 1 / t := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, a = -((n : ℤ) + 1) := ⟨(-a - 1).toNat, by omega⟩
      have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hn, zpow_neg, hcast, zpow_natCast, inv_eq_one_div]
      refine one_div_le_one_div_of_le htpos ?_
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ (n + 1) := pow_le_pow_right₀ ht1 (by omega)
    calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ * ‖vertLog t ^ b‖
        ≤ (1 / t) * (2 * Real.log t) ^ b.toNat := by
          refine mul_le_mul (le_trans h1 hta) h2 (norm_nonneg _) (by positivity)
      _ = (2 * Real.log t) ^ b.toNat / t := by
          rw [one_div, inv_mul_eq_div]
  · -- the logarithm power over the ordinate vanishes
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 b.toNat one_ne_zero
    have hconst := h.const_mul ((2 : ℝ) ^ b.toNat)
    rw [mul_zero] at hconst
    refine hconst.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [one_mul, add_zero, mul_pow, mul_div_assoc]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The Gamma case of the dominance order, uniformly.**  A positive Gamma exponent beats every
algebraic-logarithmic factor, with one constant for the whole tube. -/
theorem tubeLimit_gammaShapeZ_zero_of_gamma_pos {M : ℝ} (hM : 0 < M) {k : ℤ} (hk : 0 < k)
    (a b : ℤ) : TubeLimit M (fun σ t => gammaShapeZ σ k a b t) 0 := by
  classical
  set A : ℕ := a.toNat with hA
  set B : ℕ := b.toNat with hB
  obtain ⟨C, hC, hΓ⟩ := exists_uniform_bound_norm_Gamma_vertical hM (A + B + 2)
  obtain ⟨D, hD, hΓ0⟩ := exists_uniform_bound_norm_Gamma_vertical hM 0
  obtain ⟨K, hK⟩ : ∃ K : ℕ, k = (K : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  refine tubeLimit_of_squeeze (T₀ := 3)
    (g := fun t => (D ^ K * C * (1 + M) ^ A * 2 ^ B) / t) ?_ ?_
  case refine_2 =>
    have hlim : Tendsto (fun t : ℝ => (D ^ K * C * (1 + M) ^ A * 2 ^ B) / t) atTop (nhds 0) :=
      (tendsto_const_nhds (x := D ^ K * C * (1 + M) ^ A * 2 ^ B)).div_atTop tendsto_id
    exact hlim
  intro σ t hσ hσM ht3
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith
  rw [gammaShapeZ, norm_mul, norm_mul]
  -- the three factors
  have hΓbound : ‖gammaLine σ t‖ ≤ C / t ^ (A + B + 2) := hΓ σ t hσ hσM ht1
  have hΓ0bound : ‖gammaLine σ t‖ ≤ D := by
    have := hΓ0 σ t hσ hσM ht1
    rwa [pow_zero, div_one] at this
  have hpowΓ : ‖gammaLine σ t ^ k‖ ≤ D ^ K * (C / t ^ (A + B + 2)) := by
    rw [hK, zpow_add₀ (gammaLine_ne_zero hσ t), zpow_natCast, zpow_one, norm_mul, norm_pow]
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hΓ0bound K) hΓbound (norm_nonneg _)
      (by positivity)
  have hpows : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ ≤ (1 + M) ^ A * t ^ A := by
    refine le_trans (norm_zpow_vertical_le hσ hσM ht1 a) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hle : a ≤ (A : ℤ) := Int.self_le_toNat a
    calc t ^ a ≤ t ^ (A : ℤ) := zpow_le_zpow_right₀ ht1 hle
      _ = t ^ A := zpow_natCast t A
  have hpowL : ‖vertLog t ^ b‖ ≤ 2 ^ B * t ^ B := by
    refine le_trans (norm_vertLog_zpow_le ht3 b) ?_
    · have hlog : Real.log t + Real.pi / 2 ≤ 2 * t := by
        have h1 : Real.log t ≤ t := by
          have := Real.log_le_sub_one_of_pos htpos
          linarith
        have h2 : Real.pi ≤ 4 := Real.pi_le_four
        linarith
      calc (Real.log t + Real.pi / 2) ^ B ≤ (2 * t) ^ B := by
            refine pow_le_pow_left₀ ?_ hlog _
            have := Real.log_nonneg ht1
            have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
            linarith
        _ = 2 ^ B * t ^ B := by rw [mul_pow]
  -- multiply the three bounds
  have hfinal : (D ^ K * (C / t ^ (A + B + 2))) * ((1 + M) ^ A * t ^ A * (2 ^ B * t ^ B))
      = (D ^ K * C * (1 + M) ^ A * 2 ^ B) / t ^ 2 := by
    have htne : (t : ℝ) ≠ 0 := ne_of_gt htpos
    field_simp
    ring
  calc ‖gammaLine σ t ^ k‖ * (‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ * ‖vertLog t ^ b‖)
      ≤ (D ^ K * (C / t ^ (A + B + 2))) * ((1 + M) ^ A * t ^ A * (2 ^ B * t ^ B)) := by
        refine mul_le_mul hpowΓ ?_ (by positivity) (by positivity)
        exact mul_le_mul hpows hpowL (norm_nonneg _) (by positivity)
    _ = (D ^ K * C * (1 + M) ^ A * 2 ^ B) / t ^ 2 := hfinal
    _ ≤ (D ^ K * C * (1 + M) ^ A * 2 ^ B) / t := by
        refine div_le_div_of_nonneg_left (by positivity) htpos ?_
        calc t = t ^ 1 := (pow_one t).symm
          _ ≤ t ^ 2 := pow_le_pow_right₀ ht1 (by omega)

/-- The quotient of two shapes is the shape at the difference, beyond a fixed height. -/
theorem gammaShapeZ_div_of_le {σ t : ℝ} (hσ : 0 < σ) (ht : 3 ≤ t) (k a b k' a' b' : ℤ) :
    gammaShapeZ σ k a b t / gammaShapeZ σ k' a' b' t
      = gammaShapeZ σ (k - k') (a - a') (b - b') t := by
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h0] at him
    simp only [Complex.zero_im] at him
    linarith
  have hL : vertLog t ≠ 0 := by
    intro h0
    have hre : (vertLog t).re = Real.log t := by
      rw [vertLog]
      simp
    rw [h0] at hre
    simp only [Complex.zero_re] at hre
    have hlog1 : (1 : ℝ) ≤ Real.log t := by
      have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      have := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  rw [gammaShapeZ, gammaShapeZ, gammaShapeZ, zpow_sub₀ hΓ, zpow_sub₀ hs, zpow_sub₀ hL]
  field_simp

/-- **The dominance order of eq. (26), uniformly on a tube.**  A strictly subordinate shape vanishes
against the dominant one, simultaneously for every abscissa. -/
theorem tubeLimit_gammaShapeZ_ratio_zero {M : ℝ} (hM : 0 < M) {k a b k' a' b' : ℤ}
    (h : k' < k ∨ (k = k' ∧ a < a') ∨ (k = k' ∧ a = a' ∧ b < b')) :
    TubeLimit M (fun σ t => gammaShapeZ σ k a b t / gammaShapeZ σ k' a' b' t) 0 := by
  have hzero : TubeLimit M (fun σ t => gammaShapeZ σ (k - k') (a - a') (b - b') t) 0 := by
    rcases h with hk | ⟨hk, ha⟩ | ⟨hk, ha, hb⟩
    · exact tubeLimit_gammaShapeZ_zero_of_gamma_pos hM (by omega) _ _
    · rw [show k - k' = 0 by omega]
      exact tubeLimit_gammaShapeZ_zero_of_arg_neg (by omega) _
    · rw [show k - k' = 0 by omega, show a - a' = 0 by omega]
      exact tubeLimit_gammaShapeZ_zero_of_log_neg (by omega)
  refine hzero.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  exact (gammaShapeZ_div_of_le hσ ht k a b k' a' b').symm

end

end GaloisForLFunctions.HTGeometry
