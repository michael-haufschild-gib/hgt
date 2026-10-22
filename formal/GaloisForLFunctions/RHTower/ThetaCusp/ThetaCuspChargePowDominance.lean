import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargePowLinearity

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

section Relative

variable {t : ℝ}

theorem chR0m_gap {n n' : ℕ} (hnn : n' < n) (ht : 0 < t) (ht4 : t ^ 4 ≤ 3 / 4) :
    chR0m (chM n') t + 1 / t ^ 2 ≤ chR0m (chM n) t := by
  unfold chR0m
  rw [chM_eq, chM_eq]
  have hb := half_le_chB (t := t) ht4
  have hπ := Real.pi_gt_three
  have hd : (1 : ℝ) ≤ (n : ℝ) - n' := by
    have : (n' : ℝ) + 1 ≤ n := by exact_mod_cast hnn
    linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have e : (8 * (n : ℝ) + 7) * π * chB t / (8 * t ^ 2) - (8 * (n' : ℝ) + 7) * π * chB t / (8 * t ^ 2) =
      ((n : ℝ) - n') * π * chB t / t ^ 2 := by field_simp; ring
  have h1 : 1 / t ^ 2 ≤ ((n : ℝ) - n') * π * chB t / t ^ 2 := by
    apply div_le_div_of_nonneg_right _ ht2.le
    have h2 : (3 / 2 : ℝ) ≤ π * chB t := by nlinarith
    nlinarith
  linarith

theorem lower_rel_bound {n n' : ℕ} (hnn : n' < n) (ht : chSmall n t) {M : ℝ} (hM0 : 0 ≤ M) :
    2 * (2 * chP0 t * Real.exp (chR0m (chM n') t) + chBfarP n' t M) ≤
      (2 * (2 + 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) + M)) * 2 ^ (8 * (n + 1)) *
        (Nat.factorial 9 : ℝ) * t ^ 12 * chG0p n t := by
  have ht0 := ht.1
  have htle := ht.le
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht0.le ht1 (by norm_num : (4:ℕ) ≠ 0); linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_of_le_one ht0.le ht1 (by norm_num : (2:ℕ) ≠ 0); linarith
  have ht2p : 0 < t ^ 2 := by positivity
  have hκ := chKap_ge ht4
  have hκ0 : 0 < chKap t := lt_of_lt_of_le ht2p hκ
  have hp := one_le_chP0 ht0 ht2
  have hp0 := chP0_pos (t := t)
  set R := chR0m (chM n) t with hR
  set R' := chR0m (chM n') t with hR'
  have hR'0 : 0 ≤ R' := by
    rw [hR']; unfold chR0m; have := chB_nonneg (t := t); have := chM_ge n'; positivity
  have hgap := chR0m_gap hnn ht0 ht4
  rw [← hR, ← hR'] at hgap
  have hE : Real.exp R' ≤ Real.exp R * ((Nat.factorial 9 : ℝ) * t ^ 18) := by
    have h1 : Real.exp R' ≤ Real.exp R * Real.exp (-(1 / t ^ 2)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h2 := exp_neg_inv_sq_le 9 ht0
    calc Real.exp R' ≤ Real.exp R * Real.exp (-(1 / t ^ 2)) := h1
      _ ≤ Real.exp R * ((Nat.factorial 9 : ℝ) * t ^ (2 * 9)) := by gcongr
      _ = _ := by norm_num
  have hinv6 : 1 ≤ (1 / t) ^ 6 := one_le_pow₀ (by rw [le_div_iff₀ ht0]; linarith)
  have hB : chBfarP n' t M ≤ (3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) + M) * (1 / t) ^ 6 *
      Real.exp R' := by
    have hER : 1 ≤ Real.exp R' := Real.one_le_exp hR'0
    have hkinv : (chKap t)⁻¹ ≤ 1 / t ^ 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le ht2p hκ
    have hk3 : (chKap t)⁻¹ ^ 3 ≤ (1 / t) ^ 6 := by
      calc (chKap t)⁻¹ ^ 3 ≤ (1 / t ^ 2) ^ 3 := pow_le_pow_left₀ (inv_nonneg.mpr hκ0.le) hkinv 3
        _ = (1 / t) ^ 6 := by field_simp
    have hC : (0 : ℝ) ≤ 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) := by positivity
    unfold chBfarP
    apply max_le
    · have h1 : Real.exp (R' / 3) ≤ Real.exp R' := Real.exp_le_exp.mpr (by linarith)
      rw [← hR']
      calc 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) * (chKap t)⁻¹ ^ 3 * Real.exp (R' / 3) / 2
          ≤ 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) * (1 / t) ^ 6 * Real.exp R' := by
            have : 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) * (chKap t)⁻¹ ^ 3 * Real.exp (R' / 3) ≤
                3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) * (1 / t) ^ 6 * Real.exp R' := by gcongr
            have h0 : 0 ≤ 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) * (chKap t)⁻¹ ^ 3 *
                Real.exp (R' / 3) := by positivity
            linarith
        _ ≤ _ := by
            have : 0 ≤ M * (1 / t) ^ 6 * Real.exp R' := by positivity
            nlinarith
    · have hpik : 1 / (π * chKap t) ≤ (1 / t) ^ 6 := by
        have h1 : 1 / (π * chKap t) ≤ 1 / chKap t := by
          apply one_div_le_one_div_of_le hκ0
          have : 1 ≤ π := by linarith [Real.pi_gt_three]
          nlinarith
        have h2 : 1 / chKap t ≤ 1 / t ^ 2 := one_div_le_one_div_of_le ht2p hκ
        have h3 : 1 / t ^ 2 ≤ (1 / t) ^ 6 := by
          rw [show 1 / t ^ 2 = (1 / t) ^ 2 by field_simp]
          exact pow_le_pow_right₀ (by rw [le_div_iff₀ ht0]; linarith) (by norm_num)
        linarith
      calc M / 2 * (1 / (π * chKap t)) ≤ M * (1 / t) ^ 6 := by
            have : M / 2 ≤ M := by linarith
            calc M / 2 * (1 / (π * chKap t)) ≤ M * (1 / (π * chKap t)) := by gcongr
              _ ≤ M * (1 / t) ^ 6 := by gcongr
        _ ≤ M * (1 / t) ^ 6 * Real.exp R' := le_mul_of_one_le_right (by positivity) hER
        _ ≤ _ := by
            have : 0 ≤ 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) * (1 / t) ^ 6 * Real.exp R' := by
              positivity
            nlinarith
  have hG : chP0 t * Real.exp R = 2 ^ (8 * (n + 1)) * chG0p n t := by
    unfold chG0p; rw [← hR]; field_simp
  have ht18 : (1 / t) ^ 6 * t ^ 18 = t ^ 12 := by field_simp
  set C : ℝ := 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  calc 2 * (2 * chP0 t * Real.exp R' + chBfarP n' t M)
      ≤ 2 * (2 * chP0 t * Real.exp R' * (1 / t) ^ 6 + (C + M) * (1 / t) ^ 6 * Real.exp R' * chP0 t) := by
        have h1 : 2 * chP0 t * Real.exp R' ≤ 2 * chP0 t * Real.exp R' * (1 / t) ^ 6 :=
          le_mul_of_one_le_right (by positivity) hinv6
        have h2 : (C + M) * (1 / t) ^ 6 * Real.exp R' ≤
            (C + M) * (1 / t) ^ 6 * Real.exp R' * chP0 t :=
          le_mul_of_one_le_right (by positivity) hp
        linarith
    _ = 2 * (2 + C + M) * (1 / t) ^ 6 * (chP0 t * Real.exp R') := by ring
    _ ≤ 2 * (2 + C + M) * (1 / t) ^ 6 * (chP0 t * (Real.exp R * ((Nat.factorial 9 : ℝ) * t ^ 18))) := by
        gcongr
    _ = 2 * (2 + C + M) * (Nat.factorial 9 : ℝ) * ((1 / t) ^ 6 * t ^ 18) * (chP0 t * Real.exp R) := by
        ring
    _ = 2 * (2 + C + M) * 2 ^ (8 * (n + 1)) * (Nat.factorial 9 : ℝ) * t ^ 12 * chG0p n t := by
        rw [ht18, hG]; ring
    _ = _ := by ring

theorem xi_rel_bound {n : ℕ} (ht : chSmall n t) :
    8 * xiStripConst (chBeta t) ≤
      24000000 * 2 ^ (8 * (n + 1)) * (Nat.factorial 20 : ℝ) * t ^ 24 * chG0p n t := by
  have ht0 := ht.1
  have htle := ht.le
  have ht1 : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht0.le ht1 (by norm_num : (4:ℕ) ≠ 0); linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_of_le_one ht0.le ht1 (by norm_num : (2:ℕ) ≠ 0); linarith
  have hxi := xiStripConst_chBeta_le ht0 (by linarith)
  have hR := chR0m_ge n ht0 ht4
  have hp := one_le_chP0 ht0 ht2
  set R := chR0m (chM n) t with hRdef
  have hE : 1 ≤ Real.exp R * ((Nat.factorial 20 : ℝ) * t ^ 40) := by
    have h1 := exp_neg_inv_sq_le 20 ht0
    have h2 : Real.exp (-(1 / t ^ 2)) * Real.exp R ≥ 1 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have h3 : Real.exp (-(1 / t ^ 2)) ≤ (Nat.factorial 20 : ℝ) * t ^ 40 := by
      have := h1; norm_num at this ⊢; exact this
    have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos R).le
    rw [mul_comm]; exact le_trans h2 h4
  have hG : Real.exp R ≤ 2 ^ (8 * (n + 1)) * chG0p n t := by
    unfold chG0p; rw [← hRdef]
    have h2 : (2 : ℝ) ^ (8 * (n + 1)) * ((2 ^ (8 * (n + 1)))⁻¹ * chP0 t * Real.exp R) =
        chP0 t * Real.exp R := by field_simp
    rw [h2]; nlinarith [Real.exp_pos R]
  have h16 : 1 / t ^ 16 ≤ (Nat.factorial 20 : ℝ) * t ^ 24 * Real.exp R := by
    rw [div_le_iff₀ (by positivity)]
    have e : (Nat.factorial 20 : ℝ) * t ^ 24 * Real.exp R * t ^ 16 =
        Real.exp R * ((Nat.factorial 20 : ℝ) * t ^ 40) := by ring
    rw [e]; exact hE
  calc 8 * xiStripConst (chBeta t) ≤ 8 * (3000000 / t ^ 16) := by gcongr
    _ = 24000000 * (1 / t ^ 16) := by ring
    _ ≤ 24000000 * ((Nat.factorial 20 : ℝ) * t ^ 24 * Real.exp R) := by gcongr
    _ ≤ 24000000 * ((Nat.factorial 20 : ℝ) * t ^ 24 * (2 ^ (8 * (n + 1)) * chG0p n t)) := by gcongr
    _ = _ := by ring

end Relative

/-! ### Dominance of the top pole order -/

/-- The saddle parameter of a frequency for pole order `8n+7`. -/
def chTm (n : ℕ) (u : ℝ) : ℝ := Real.sqrt (Real.sqrt (chM n * π / (8 * u)))

theorem chTm_pos (n : ℕ) {u : ℝ} (hu : 0 < u) : 0 < chTm n u := by
  unfold chTm; have := chM_ge n
  apply Real.sqrt_pos.mpr; apply Real.sqrt_pos.mpr; positivity

theorem chTm_pow_four (n : ℕ) {u : ℝ} (hu : 0 < u) : chTm n u ^ 4 = chM n * π / (8 * u) := by
  unfold chTm; have := chM_ge n
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]

theorem chUm_chTm (n : ℕ) {u : ℝ} (hu : 0 < u) : chUm (chM n) (chTm n u) = u := by
  unfold chUm; rw [chTm_pow_four n hu]; have := chM_ge n; field_simp

theorem chTm_le (n : ℕ) {u t₁ : ℝ} (hu : 0 < u) (ht₁ : 0 < t₁)
    (hU : chM n * π / (8 * t₁ ^ 4) ≤ u) : chTm n u ≤ t₁ := by
  have hm := chM_ge n
  have h4 : chTm n u ^ 4 ≤ t₁ ^ 4 := by
    rw [chTm_pow_four n hu, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hU
    nlinarith [pow_pos ht₁ 4]
  exact le_of_pow_le_pow_left₀ (by norm_num) ht₁.le h4

/-- **Top-order dominance.**  If `P` has degree `n+1`, the transform of `θ₃P(h)` has no zero
at large real frequency. -/
theorem thetaGroupForm_eventually_ne_zero (P : Polynomial ℝ) {n : ℕ} (hP : P.natDegree = n + 1) :
    ∃ U : ℝ, 0 < U ∧ ∀ u : ℝ, U ≤ u →
      modXi (thetaGroupForm (P.map (algebraMap ℝ ℂ))) (u : ℂ) ≠ 0 := by
  have hc : P.coeff (n + 1) ≠ 0 := by
    rw [← hP]; exact Polynomial.leadingCoeff_ne_zero.mpr (by
      intro h; rw [h] at hP; simp at hP)
  -- cusp constants of the lower basis forms
  have hMex : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℂ, 1 ≤ τ.im →
      ‖thetaGroupBasis (j + 1) τ‖ ≤ M * Real.exp (-π * τ.im) := by
    intro j
    obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay (j + 1)
    have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis (j + 1) τ‖ ≤ M * Real.exp (-π * τ.im) := by
      intro τ hτ; have := hM τ hτ; simpa [thetaGroupBasisCusp] using this
    refine ⟨M, ?_, hM'⟩
    have h := hM' Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  choose Mf hMf0 hMf using hMex
  obtain ⟨t₁, ht₁, hpos⟩ := exists_re_chLinePInt_pos n
  set cN : ℝ := |P.coeff (n + 1)| with hcN
  have hcNpos : 0 < cN := abs_pos.mpr hc
  set Klow : ℝ := ∑ n' ∈ Finset.range n, |P.coeff (n' + 1)| *
    ((2 * (2 + 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) + Mf n')) * 2 ^ (8 * (n + 1)) *
      (Nat.factorial 9 : ℝ)) with hKlow
  set Kxi : ℝ := |P.coeff 0| * (24000000 * 2 ^ (8 * (n + 1)) * (Nat.factorial 20 : ℝ)) with hKxi
  have hKlow0 : 0 ≤ Klow := Finset.sum_nonneg (fun n' _ => by
    have := hMf0 n'; positivity)
  have hKxi0 : 0 ≤ Kxi := by positivity
  set W : ℝ := 64 * ((n : ℝ) + 1) * (Klow + Kxi + 1) / cN with hW
  have hWpos : 0 < W := by positivity
  set t₂ : ℝ := min t₁ (min (1 / W) 1) with ht₂
  have ht₂pos : 0 < t₂ := lt_min ht₁ (lt_min (by positivity) one_pos)
  refine ⟨chM n * π / (8 * t₂ ^ 4), by have := chM_ge n; positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le (by have := chM_ge n; positivity) hu
  set t := chTm n u with htdef
  have ht0 : 0 < t := chTm_pos n hu0
  have htt₂ : t ≤ t₂ := chTm_le n hu0 ht₂pos hu
  have htt₁ : t ≤ t₁ := le_trans htt₂ (min_le_left _ _)
  have htW : t * W ≤ 1 := by
    have := le_trans htt₂ (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ hWpos] at this; linarith
  have ht1 : t ≤ 1 := le_trans htt₂ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hsm, hRe⟩ := hpos t ht0 htt₁
  have ht2 : t ^ 2 ≤ 1 / 2 := by have := hsm.le; nlinarith
  have hU : chUm (chM n) t = u := chUm_chTm n hu0
  -- expansion
  rw [modXi_thetaGroupForm_map, hP, Finset.sum_range_succ]
  set β := chBeta t with hβ
  have hβ0 : 0 ≤ β := chBeta_nonneg ht2
  have hβ4 : 2 * β < π / 2 := by have := chBeta_lt ht0 (by linarith); linarith
  set E : ℝ := Real.exp (-(u * β)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set A : ℝ := (u ^ 2 + 1 / 4) * E with hA
  have hApos : 0 < A := by positivity
  have hpref : ∀ z : ℂ, -((u : ℂ) ^ 2 + 1 / 4) * (Complex.exp (-(u * β : ℝ)) * z) = -((A : ℝ) : ℂ) * z := by
    intro z; rw [hA, hE]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  -- the top term
  have htop : thetaGroupXi (n + 1) (u : ℂ) = -((A : ℝ) : ℂ) * chLinePInt n t := by
    rw [thetaGroupXi_succ_chU n ht0 ht2 u, hpref]
    congr 1
    unfold chLinePInt
    congr 1; funext s; rw [chLineP_eq_chLineJ, hU]
  set G : ℝ := chG0p n t * t ^ 3 / (32 * ((n : ℝ) + 1)) with hG
  have hGpos : 0 < G := by
    rw [hG]; unfold chG0p; have := chP0_pos (t := t); positivity
  have hG0 : 0 ≤ chG0p n t := by unfold chG0p; have := chP0_pos (t := t); positivity
  have htopn : cN * A * G ≤ ‖(P.coeff (n + 1) : ℂ) * thetaGroupXi (n + 1) (u : ℂ)‖ := by
    rw [htop, norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hApos]
    have h1 : G ≤ ‖chLinePInt n t‖ := le_trans hRe (Complex.re_le_norm _)
    rw [← hcN]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hcNpos.le hApos.le)
    linarith [this]
  -- the lower terms
  have hlow : ‖∑ j ∈ Finset.range (n + 1), (P.coeff j : ℂ) * thetaGroupXi j (u : ℂ)‖ ≤
      A * (32 * ((n : ℝ) + 1) * (Klow + Kxi) * t ^ 9 * G) := by
    rw [Finset.sum_range_succ']
    refine le_trans (norm_add_le _ _) ?_
    have hterm : ∀ n' ∈ Finset.range n,
        ‖(P.coeff (n' + 1) : ℂ) * thetaGroupXi (n' + 1) (u : ℂ)‖ ≤
          A * (|P.coeff (n' + 1)| * ((2 * (2 + 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) + Mf n')) *
            2 ^ (8 * (n + 1)) * (Nat.factorial 9 : ℝ)) * (32 * ((n : ℝ) + 1)) * t ^ 9 * G) := by
      intro n' hn'
      have hnn : n' < n := Finset.mem_range.mp hn'
      have hsm' := chSmall_mono hnn.le hsm
      rw [thetaGroupXi_succ_chU n' ht0 ht2 u, hpref, norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hApos]
      have hI := norm_integral_chLineJ_le n' hsm' (hMf n') u
      have hrel := lower_rel_bound hnn hsm (hMf0 n')
      have hGe : t ^ 12 * chG0p n t = 32 * ((n : ℝ) + 1) * t ^ 9 * G := by
        rw [hG]; field_simp; try ring
      set Kp : ℝ := (2 * (2 + 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) + Mf n')) *
        2 ^ (8 * (n + 1)) * (Nat.factorial 9 : ℝ)
      have hI2 : ‖∫ s : ℝ, chLineJ (n' + 1) u t s‖ ≤ Kp * (32 * ((n : ℝ) + 1) * t ^ 9 * G) := by
        calc _ ≤ _ := hI
          _ ≤ _ := hrel
          _ = Kp * (t ^ 12 * chG0p n t) := by ring
          _ = _ := by rw [hGe]
      calc |P.coeff (n' + 1)| * (A * ‖∫ s : ℝ, chLineJ (n' + 1) u t s‖)
          ≤ |P.coeff (n' + 1)| * (A * (Kp * (32 * ((n : ℝ) + 1) * t ^ 9 * G))) := by gcongr
        _ = _ := by ring
    have hsum := norm_sum_le_of_le (Finset.range n) hterm
    have hxi : ‖(P.coeff 0 : ℂ) * thetaGroupXi 0 (u : ℂ)‖ ≤
        A * (Kxi * (32 * ((n : ℝ) + 1)) * t ^ 9 * G) := by
      rw [thetaGroupXi_zero_eq_XiC, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hX := norm_XiC_ofReal_le_strip hβ0 hβ4 u
      have hxr := xi_rel_bound hsm
      have hEA : E ≤ 4 * A := by rw [hA]; nlinarith [sq_nonneg u]
      have hGe : t ^ 24 * chG0p n t ≤ 32 * ((n : ℝ) + 1) * t ^ 9 * G := by
        rw [hG]
        have ht15 : t ^ 15 ≤ 1 := pow_le_one₀ ht0.le ht1
        have e : 32 * ((n : ℝ) + 1) * t ^ 9 * (chG0p n t * t ^ 3 / (32 * ((n : ℝ) + 1))) =
            t ^ 12 * chG0p n t := by field_simp; try ring
        rw [e]
        have e2 : t ^ 24 * chG0p n t = t ^ 12 * chG0p n t * t ^ 12 := by ring
        rw [e2]
        have ht12 : t ^ 12 ≤ 1 := pow_le_one₀ ht0.le ht1
        exact mul_le_of_le_one_right (by positivity) ht12
      have hxi0 := xiStripConst_nonneg hβ0 hβ4
      calc |P.coeff 0| * ‖XiC (u : ℂ)‖ ≤ |P.coeff 0| * (E * (2 * xiStripConst β)) := by gcongr
        _ ≤ |P.coeff 0| * (4 * A * (2 * xiStripConst β)) := by gcongr
        _ = A * (|P.coeff 0| * (8 * xiStripConst β)) := by ring
        _ ≤ A * (|P.coeff 0| * (24000000 * 2 ^ (8 * (n + 1)) * (Nat.factorial 20 : ℝ) *
              t ^ 24 * chG0p n t)) := by gcongr
        _ = A * (Kxi * (t ^ 24 * chG0p n t)) := by rw [hKxi]; ring
        _ ≤ A * (Kxi * (32 * ((n : ℝ) + 1) * t ^ 9 * G)) := by gcongr
        _ = _ := by ring
    have hsumval : ∑ n' ∈ Finset.range n, A * (|P.coeff (n' + 1)| *
        ((2 * (2 + 3 ^ (8 * (n' + 1)) * 2 ^ (8 * (n' + 1)) + Mf n')) * 2 ^ (8 * (n + 1)) *
          (Nat.factorial 9 : ℝ)) * (32 * ((n : ℝ) + 1)) * t ^ 9 * G) =
        A * (Klow * (32 * ((n : ℝ) + 1)) * t ^ 9 * G) := by
      rw [hKlow, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      try exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hsumval] at hsum
    have e : A * (Klow * (32 * ((n : ℝ) + 1)) * t ^ 9 * G) + A * (Kxi * (32 * ((n : ℝ) + 1)) * t ^ 9 * G) =
        A * (32 * ((n : ℝ) + 1) * (Klow + Kxi) * t ^ 9 * G) := by ring
    linarith
  -- comparison
  have ht9 : t ^ 9 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
  have hsmall : 32 * ((n : ℝ) + 1) * (Klow + Kxi) * t ^ 9 ≤ cN / 2 := by
    have hK0 : 0 ≤ 32 * ((n : ℝ) + 1) * (Klow + Kxi) := by positivity
    have h1 : 32 * ((n : ℝ) + 1) * (Klow + Kxi) * t ^ 9 ≤
        32 * ((n : ℝ) + 1) * (Klow + Kxi + 1) * t := by
      calc 32 * ((n : ℝ) + 1) * (Klow + Kxi) * t ^ 9 ≤ 32 * ((n : ℝ) + 1) * (Klow + Kxi) * t :=
            mul_le_mul_of_nonneg_left ht9 hK0
        _ ≤ 32 * ((n : ℝ) + 1) * (Klow + Kxi + 1) * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
              ht0.le
    have h2 : 32 * ((n : ℝ) + 1) * (Klow + Kxi + 1) * t ≤ cN / 2 := by
      have e : t * W = 64 * ((n : ℝ) + 1) * (Klow + Kxi + 1) * t / cN := by rw [hW]; ring
      rw [e, div_le_iff₀ hcNpos] at htW
      linarith
    exact le_trans h1 h2
  intro hzero
  rw [add_comm] at hzero
  have hkey : ‖(P.coeff (n + 1) : ℂ) * thetaGroupXi (n + 1) (u : ℂ)‖ =
      ‖∑ j ∈ Finset.range (n + 1), (P.coeff j : ℂ) * thetaGroupXi j (u : ℂ)‖ := by
    rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]
  have h3 : cN * A * G ≤ A * (32 * ((n : ℝ) + 1) * (Klow + Kxi) * t ^ 9 * G) :=
    le_trans htopn (hkey ▸ hlow)
  have h4 : A * (32 * ((n : ℝ) + 1) * (Klow + Kxi) * t ^ 9 * G) ≤ A * (cN / 2 * G) := by
    apply mul_le_mul_of_nonneg_left _ hApos.le
    exact mul_le_mul_of_nonneg_right hsmall hGpos.le
  have h5 : cN * A * G ≤ cN * A * G / 2 := by
    have e : A * (cN / 2 * G) = cN * A * G / 2 := by ring
    linarith
  have h6 : 0 < cN * A * G := mul_pos (mul_pos hcNpos hApos) hGpos
  linarith

end RHTower
