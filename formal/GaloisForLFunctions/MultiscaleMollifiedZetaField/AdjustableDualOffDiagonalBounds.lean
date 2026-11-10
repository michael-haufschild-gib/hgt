import GaloisForLFunctions.MultiscaleMollifiedZetaField.AdjustableOffDiagonalBounds

/-!
# The dual off-diagonal below square-root length

A power-sized frequency split makes its Gaussian tail smaller than any power.
The surviving carrier jets retain the taper saving at arbitrary order.
-/

noncomputable section
open Finset Filter Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The Gaussian frequency tail is smaller than any prescribed power,
for every positive power in the splitting frequency. -/
theorem eventually_gaussian_split_le_rpow {b : ℝ} (hb : 0 < b) (M : ℝ) :
    ∀ᶠ T : ℝ in atTop, Real.exp (-((T ^ b) ^ 2) / 2) ≤ T ^ (-M) := by
  have h2b : 0 < 2 * b := by linarith only [hb]
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (M / (2 * b)) (1 / 2) (by norm_num)).comp (tendsto_rpow_atTop h2b)
  have heq : (fun T : ℝ => (T ^ (2 * b)) ^ (M / (2 * b)) *
      Real.exp (-(1 / 2) * T ^ (2 * b))) =ᶠ[atTop]
      (fun T : ℝ => T ^ M * Real.exp (-((T ^ b) ^ 2) / 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← Real.rpow_mul hT.le]
    have hM : (2 * b) * (M / (2 * b)) = M := by field_simp
    rw [hM]
    have he : T ^ (2 * b) = (T ^ b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
      congr 1
      ring
    rw [he]
    congr 2
    ring
  have hlim' : Tendsto (fun T : ℝ => T ^ M * Real.exp (-((T ^ b) ^ 2) / 2))
      atTop (𝓝 0) := hlim.congr' heq
  filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_order.1 hlim').2 1 zero_lt_one]
    with T hT hsmall
  rw [Real.rpow_neg hT.le, ← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT M)).mpr
  simpa only [mul_comm] using hsmall.le

/-- The constant of the oscillating dual term, independent of all scales. -/
def dualOscillationConstant (K : ℕ) (C : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.exp 1 *
    (jetStarK K * Real.exp 8 * 625 * Real.sqrt Real.pi * 2 ^ K +
      C * 256 * Real.exp 16 * Real.sqrt (4 * Real.pi))

theorem dualOscillationConstant_nonneg (K : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ dualOscillationConstant K C := by
  unfold dualOscillationConstant
  have hj := jetStarK_nonneg K
  positivity

/-- The oscillation constant has the full `T^(-aK)` saving. The Gaussian
bound required here holds eventually at every positive splitting exponent. -/
theorem dualOffDiagOscConstV_le_rpow (K : ℕ) {C T a b q : ℝ}
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : a + b ≤ 1) (hη : T ^ a ≤ T / 2) (hq : T ≤ q) (hq2 : q ≤ 2 * T)
    (hg : Real.exp (-((T ^ b) ^ 2) / 2) ≤ T ^ (-a * K)) :
    dualOffDiagOscConstV K C T T q (T ^ a) (T ^ b) ≤
      (q - T + 2 * T ^ a) * dualOscillationConstant K C * T ^ (3 - a * K) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hη0 : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hV0 : 0 < T ^ b := Real.rpow_pos_of_pos hT0 _
  have hV : T ^ b ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hb1
  have hlen : 0 ≤ q - T + 2 * T ^ a := by linarith only [hq, hη0]
  have hjet := windowCarrierJetConst_le_rpow K hT hb hab
    (show T / 2 ≤ T - T ^ a by linarith only [hη])
  have hpoly : (1 + (q + T ^ a) + T ^ b) ^ 4 ≤ 625 * T ^ 4 := by
    calc
      _ ≤ (5 * T) ^ 4 := pow_le_pow_left₀ (by linarith only [hT0, hq, hη0, hV0])
        (by linarith only [hT, hq2, hη, hV]) 4
      _ = _ := by ring
  have hpoly' : (1 + (q + T ^ a)) ^ 4 ≤ 256 * T ^ 4 := by
    calc
      _ ≤ (4 * T) ^ 4 := pow_le_pow_left₀ (by linarith only [hT0, hq, hη0])
        (by linarith only [hT, hq2, hη]) 4
      _ = _ := by ring
  have hj0 := jetStarK_nonneg K
  have hp0 : 0 ≤ T ^ (-a * K) := Real.rpow_nonneg hT0.le _
  have hfactor : 0 ≤ (1 / (2 * Real.pi)) * ((T⁻¹ * Real.exp 1) * (q - T + 2 * T ^ a)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hlen)
  have hfirst : windowCarrierJetConst K (T ^ a) (T - T ^ a) (T ^ b) *
      (Real.exp 8 * (1 + (q + T ^ a) + T ^ b) ^ 4) * Real.sqrt Real.pi * 2 ^ K ≤
      (jetStarK K * T ^ (-a * K)) * (Real.exp 8 * (625 * T ^ 4)) * Real.sqrt Real.pi * 2 ^ K := by
    gcongr
  have hsecond : C * (1 + (q + T ^ a)) ^ 4 *
      (Real.exp 16 * Real.exp (-((T ^ b) ^ 2) / 2) * Real.sqrt (4 * Real.pi)) ≤
      C * (256 * T ^ 4) * (Real.exp 16 * T ^ (-a * K) * Real.sqrt (4 * Real.pi)) := by
    gcongr
  have halg : T⁻¹ * T ^ 4 * T ^ (-a * K) = T ^ (3 - a * K) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    congr 1
    ring
  unfold dualOffDiagOscConstV
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((T⁻¹ * Real.exp 1) * (q - T + 2 * T ^ a)) *
        ((jetStarK K * T ^ (-a * K)) * (Real.exp 8 * (625 * T ^ 4)) * Real.sqrt Real.pi * 2 ^ K +
          C * (256 * T ^ 4) * (Real.exp 16 * T ^ (-a * K) * Real.sqrt (4 * Real.pi))) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hfactor
    _ = (q - T + 2 * T ^ a) * dualOscillationConstant K C *
        (T⁻¹ * T ^ 4 * T ^ (-a * K)) := by
      unfold dualOscillationConstant
      ring
    _ = _ := by rw [halg]

/-- Shifting the dual contour trades one power of the scale for each
integration order; the split beyond the scale then supplies decay. -/
theorem dualOffDiagShiftConst_le_rpow (J : ℕ) {C T a d q : ℝ}
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hd : d ≤ 1 / 2)
    (hη : T ^ a ≤ T) (hq : T ≤ q) (hq2 : q ≤ 2 * T) :
    dualOffDiagShiftConst J C d T T q (T ^ a) ≤
      (q - T + 2 * T ^ a) * (C * 4 ^ (2 * (J : ℝ) + 1)) * T ^ ((J : ℝ) + 1) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hη0 : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hlen : 0 ≤ q - T + 2 * T ^ a := by linarith only [hq, hη0]
  have hpoly : (1 + (q + T ^ a)) ^ (2 * ((J : ℝ) + 1 / 2)) ≤
      (4 * T) ^ (2 * ((J : ℝ) + 1 / 2)) :=
    Real.rpow_le_rpow (by linarith only [hT0, hq, hη0])
      (by linarith only [hT, hq2, hη]) (by positivity)
  have hdecay : T ^ (-(1 / 2 - d + J)) ≤ T ^ (-(J : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hd])
  unfold dualOffDiagShiftConst
  calc
    _ ≤ (q - T + 2 * T ^ a) *
        (C * (4 * T) ^ (2 * ((J : ℝ) + 1 / 2)) * T ^ (-(J : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hlen
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly hC) hdecay
        (Real.rpow_nonneg hT0.le _) (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) hT0.le]
      have he : 2 * ((J : ℝ) + 1 / 2) = 2 * J + 1 := by ring
      rw [he]
      have hp : T ^ (2 * (J : ℝ) + 1) * T ^ (-(J : ℝ)) = T ^ ((J : ℝ) + 1) := by
        rw [← Real.rpow_add hT0]
        congr 1
        ring
      calc
        _ = (q - T + 2 * T ^ a) * (C * 4 ^ (2 * (J : ℝ) + 1)) *
            (T ^ (2 * (J : ℝ) + 1) * T ^ (-(J : ℝ))) := by ring
        _ = _ := by rw [hp]

/-- The free split exposes both dual exponents without fixing any contour
or differentiation order. All constants come from the actual dual carrier. -/
theorem exists_dualOffDiag_rpow_bound (K J : ℕ) (hJ : 1 ≤ J) :
    ∃ Co Cs : ℝ, 0 ≤ Co ∧ 0 ≤ Cs ∧
      ∀ (T θ a b d q : ℝ) (h k : ℕ),
        1 ≤ T → 0 ≤ b → b ≤ 1 → a + b ≤ 1 → T ^ a ≤ T / 2 →
        4 ≤ T - T ^ a → 2 * T ^ b ≤ T - T ^ a →
        T ≤ q → q ≤ 2 * T → 0 < d → d ≤ 1 / 8 → 0 < h → 0 < k →
        (h : ℝ) ≤ T ^ θ → (k : ℝ) ≤ T ^ θ →
        Real.exp (-((T ^ b) ^ 2) / 2) ≤ T ^ (-a * K) →
        (∑' P : ℕ × ℕ, dualOffDiagTerm d T T q (T ^ a) h k P) ≤
          (q - T + 2 * T ^ a) *
            (Co * T ^ (4 + b + (K : ℝ) * (1 / 2 + θ + b / 2 - a)) +
              Cs * T ^ (2 + b - b * J)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ := exists_tsum_dualOffDiagTerm_le_split K hJ
  let Z₁ : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))
  let Z₂ : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))
  refine ⟨dualOscillationConstant K C₁ * Z₁ ^ 2,
    C₂ * 4 ^ (2 * (J : ℝ) + 1) * Z₂ ^ 2,
    mul_nonneg (dualOscillationConstant_nonneg K hC₁) (sq_nonneg _),
    mul_nonneg (mul_nonneg hC₂ (by positivity)) (sq_nonneg _), ?_⟩
  intro T θ a b d q h k hT hb hb1 hab hη hL hV hq hq2 hd hd8 hh hk hhT hkT hg
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hη0 : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hlen : 0 ≤ q - T + 2 * T ^ a := by linarith only [hq, hη0]
  have hco := dualOscillationConstant_nonneg K hC₁
  have hcs : 0 ≤ C₂ * 4 ^ (2 * (J : ℝ) + 1) := by positivity
  have ho := dualOffDiagOscConstV_le_rpow K hC₁ hT hb hb1 hab hη hq hq2 hg
  have hs := dualOffDiagShiftConst_le_rpow J hC₂ hT
    (show d ≤ 1 / 2 by linarith only [hd8]) (hη.trans (by linarith only [hT0])) hq hq2
  have hpair : ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) ≤ T ^ (θ * K) := by
    convert pair_rpow_le_length hT (show 0 ≤ 1 / 2 - d by linarith only [hd8]) hh hk hhT hkT (K := K) using 1 <;> ring
  have hpair' : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hhkp : (1 : ℝ) ≤ (h : ℝ) * k := by nlinarith only [hh1, hk1]
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hhkp
      (show -(1 / 2 - d) ≤ 0 by linarith only [hd8])
  have hz : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2 ≤ Z₁ ^ 2 :=
    pow_le_pow_left₀ (tsum_succ_rpow_neg_nonneg _)
      (tsum_succ_rpow_neg_le (by norm_num) (by linarith only [hd])) 2
  have hbound := hsplit d T T q (T ^ a) (T ^ (1 + b)) (T ^ b) h k hd
    (by linarith only [hd8]) hT0 hη0 hL hq (Real.rpow_pos_of_pos hT0 _)
    (Real.rpow_nonneg hT0.le _) hV hh hk
  have ho' : dualOffDiagOscConstV K C₁ T T q (T ^ a) (T ^ b) *
      ((h : ℝ) * k) ^ ((K : ℝ) / 2 - 1 / 2 + d) *
      (T ^ (1 + b)) ^ ((K : ℝ) / 2 + 1) *
      (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2 ≤
      (q - T + 2 * T ^ a) * (dualOscillationConstant K C₁ * Z₁ ^ 2) *
        T ^ (4 + b + (K : ℝ) * (1 / 2 + θ + b / 2 - a)) := by
    calc
      _ ≤ ((q - T + 2 * T ^ a) * dualOscillationConstant K C₁ * T ^ (3 - a * K)) *
          T ^ (θ * K) * (T ^ (1 + b)) ^ ((K : ℝ) / 2 + 1) * Z₁ ^ 2 := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_mul hT0.le]
        have he : T ^ (3 - a * K) * T ^ (θ * K) *
            T ^ ((1 + b) * ((K : ℝ) / 2 + 1)) =
            T ^ (4 + b + (K : ℝ) * (1 / 2 + θ + b / 2 - a)) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
          congr 1
          ring
        calc
          _ = (q - T + 2 * T ^ a) * (dualOscillationConstant K C₁ * Z₁ ^ 2) *
              (T ^ (3 - a * K) * T ^ (θ * K) * T ^ ((1 + b) * ((K : ℝ) / 2 + 1))) := by ring
          _ = _ := by rw [he]
  have hs' : dualOffDiagShiftConst J C₂ d T T q (T ^ a) *
      ((h : ℝ) * k) ^ (-(1 / 2 - d)) *
      (T ^ (1 + b)) ^ (-((J : ℝ) - 1)) * Z₂ ^ 2 ≤
      (q - T + 2 * T ^ a) * (C₂ * 4 ^ (2 * (J : ℝ) + 1) * Z₂ ^ 2) *
        T ^ (2 + b - b * J) := by
    calc
      _ ≤ ((q - T + 2 * T ^ a) * (C₂ * 4 ^ (2 * (J : ℝ) + 1)) * T ^ ((J : ℝ) + 1)) *
          1 * (T ^ (1 + b)) ^ (-((J : ℝ) - 1)) * Z₂ ^ 2 := by
        gcongr
      _ = _ := by
        rw [mul_one, ← Real.rpow_mul hT0.le]
        have he : T ^ ((J : ℝ) + 1) * T ^ ((1 + b) * (-((J : ℝ) - 1))) =
            T ^ (2 + b - b * J) := by
          rw [← Real.rpow_add hT0]
          congr 1
          ring
        calc
          _ = (q - T + 2 * T ^ a) * (C₂ * 4 ^ (2 * (J : ℝ) + 1) * Z₂ ^ 2) *
              (T ^ ((J : ℝ) + 1) * T ^ ((1 + b) * (-((J : ℝ) - 1)))) := by ring
          _ = _ := by rw [he]
  exact hbound.trans ((add_le_add ho' hs').trans_eq (by ring))

private theorem eventually_rpow_le_quarter {a : ℝ} (ha : a < 1) :
    ∀ᶠ T : ℝ in atTop, T ^ a ≤ T / 4 := by
  have hg := tendsto_rpow_atTop (show 0 < 1 - a by linarith only [ha])
  filter_upwards [eventually_gt_atTop (0 : ℝ), hg.eventually_ge_atTop 4] with T hT hgT
  have he : T ^ a * T ^ (1 - a) = T := by
    rw [← Real.rpow_add hT]
    convert Real.rpow_one T using 2 <;> ring
  have hm := mul_le_mul_of_nonneg_left hgT (Real.rpow_nonneg hT.le a)
  rw [he] at hm
  linarith only [hm]

/-- A positive gap in the oscillating exponent and a split beyond the scale
supply arbitrary power saving for the complete dual off-diagonal. -/
theorem exists_dualOffDiag_power_saving {θ a b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ha1 : a < 1) (hab : a + b ≤ 1)
    (hgap : 1 / 2 + θ + b / 2 < a) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (d q : ℝ) (h k : ℕ), T ≤ q → q ≤ 2 * T →
        0 < d → d ≤ 1 / 8 → 0 < h → 0 < k →
        (h : ℝ) ≤ T ^ θ → (k : ℝ) ≤ T ^ θ →
        (∑' P : ℕ × ℕ, dualOffDiagTerm d T T q (T ^ a) h k P) ≤
          (q - T + 2 * T ^ a) * C * T ^ (-B) := by
  have hg : 0 < a - (1 / 2 + θ + b / 2) := sub_pos.mpr hgap
  obtain ⟨K, hK⟩ := exists_nat_gt ((B + 4 + b) / (a - (1 / 2 + θ + b / 2)))
  obtain ⟨J, hJ⟩ := exists_nat_gt (max ((B + 2 + b) / b) 1)
  have hJ1 : 1 ≤ J := by
    have hh : (1 : ℝ) < J := (le_max_right _ _).trans_lt hJ
    have hh' : (1 : ℕ) < J := by exact_mod_cast hh
    omega
  have hKo : 4 + b + (K : ℝ) * (1 / 2 + θ + b / 2 - a) ≤ -B := by
    have hh := (div_lt_iff₀ hg).mp hK
    nlinarith only [hh]
  have hJs : 2 + b - b * J ≤ -B := by
    have hh := (div_lt_iff₀ hb).mp ((le_max_left _ _).trans_lt hJ)
    nlinarith only [hh]
  obtain ⟨Co, Cs, hCo, hCs, hbound⟩ := exists_dualOffDiag_rpow_bound K J hJ1
  refine ⟨Co + Cs, add_nonneg hCo hCs, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_rpow_le_quarter ha1,
    eventually_rpow_le_quarter hb1, eventually_gaussian_split_le_rpow hb (a * K)]
    with T hT hη hV hgT
  intro d q h k hq hq2 hd hd8 hh hk hhT hkT
  have hT0 : 0 < T := by linarith only [hT]
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hη0 : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hlen : 0 ≤ q - T + 2 * T ^ a := by linarith only [hq, hη0]
  have hhbound := hbound T θ a b d q h k hT1 hb.le hb1.le hab
    (by linarith only [hη, hT0]) (by linarith only [hη, hT])
    (by linarith only [hη, hV, hT0]) hq hq2 hd hd8 hh hk hhT hkT
    (by simpa only [neg_mul] using hgT)
  refine hhbound.trans ?_
  calc
    _ ≤ (q - T + 2 * T ^ a) * (Co * T ^ (-B) + Cs * T ^ (-B)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hKo) hCo)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hJs) hCs)) hlen
    _ = _ := by ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField

#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.eventually_gaussian_split_le_rpow
#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.exists_dualOffDiag_rpow_bound

#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.exists_dualOffDiag_power_saving
