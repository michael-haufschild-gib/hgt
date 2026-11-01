import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheLogarithmicProfileHasCoerciveConductorBands

/-!
# Horizon bounds for the logarithmic conductor split

A power-of-logarithm envelope bounds actual overlap and reciprocal Fourier
floor. The exponent bound `α ≤ 1/128` also makes the high-conductor cross error
bounded independently of actual overlap.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

theorem eventually_log_nat_le_rpow_36 :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
  exact (le_abs_self _).trans habs

theorem eventually_floor_log_rpow_bounds {q : ℝ} (hq : 0 < q) (hqmax : q ≤ 1 / 5) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      2 ≤ Q₁ ∧
      (Q₁ : ℝ) ≤ L ^ q ∧
      (1 / 4 : ℝ) * L ^ q ≤ (Q₁ : ℝ) ∧
      q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) ∧
      Q₁ ^ 4 ≤ N := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp hLlim
  filter_upwards [hQlim.eventually_ge_atTop 4,
    hLlim.eventually_ge_atTop 1, eventually_ge_atTop 2] with N hX4 hL1 hN2
  dsimp only
  let L := Real.log (N : ℝ)
  let Xq := L ^ q
  let Q₁ := ⌊Xq⌋₊
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ2 : 2 ≤ Q₁ := Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ Xq by linarith only [hX4]))
  have hQ_le : (Q₁ : ℝ) ≤ Xq := Nat.floor_le (by linarith only [hX4])
  have hQ_gt : Xq - 1 < (Q₁ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one Xq)
  have hQ_quarter : (1 / 4 : ℝ) * Xq ≤ (Q₁ : ℝ) := by linarith only [hX4, hQ_gt]
  have hQ_half : (1 / 2 : ℝ) * Xq ≤ (Q₁ : ℝ) := by linarith only [hX4, hQ_gt]
  have hlogQ_lb : q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hXq_pos : 0 < Xq := by linarith only [hX4]
    have h1 := Real.log_le_log (by positivity) hQ_half
    rw [Real.log_mul (by norm_num) hXq_pos.ne', one_div, Real.log_inv,
      show Xq = L ^ q from rfl, Real.log_rpow hL0] at h1
    linarith only [h1, hlog2]
  have hQ4_N : Q₁ ^ 4 ≤ N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 4
    have he : Xq ^ (4 : ℕ) = L ^ (4 * q) := by
      dsimp only [Xq]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    have hL_le : L ^ (4 * q) ≤ L := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hqmax] : 4 * q ≤ 1)
    have hLN : L ≤ (N : ℝ) :=
      (Real.log_le_sub_one_of_pos hN0).trans (by linarith only)
    exact_mod_cast ((hp.trans_eq he).trans hL_le).trans hLN
  exact ⟨hQ2, hQ_le, hQ_quarter, hlogQ_lb, hQ4_N⟩

theorem rpow_horizon_N_bounds {N R' : ℕ} {c H_res : ℝ}
    (hN1 : 1 ≤ N) (hR'2 : 2 ≤ R') (hc1 : 1 ≤ c) (_hH0 : 0 < H_res)
    (hL2000 : 2000 ≤ Real.log (N : ℝ)) (hHL : H_res ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ))
    (hlog36 : 36 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ)) :
    H_res * c ^ 8 ≤ (N : ℝ) ∧
    4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
    c / (N : ℝ) ≤ 1 / 3 ∧
    4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
    R' ^ 6 ≤ N ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
    (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 5 * Real.log (N : ℝ) / (N : ℝ) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) := by
  let L := Real.log (N : ℝ)
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL2000]
  have hX2000 : 2000 ≤ X := hL2000.trans hLX
  have hX1 : 1 ≤ X := by linarith only [hX2000]
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcX : c ≤ X := hcL.trans hLX
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpowX : ∀ k : ℕ, k ≤ 36 → X ^ k ≤ (N : ℝ) := fun k hk =>
    (pow_le_pow_right₀ hX1 hk).trans_eq hX36
  have hR'X : (R' : ℝ) ≤ X := by
    have hR'0 : (0 : ℝ) < R' := by exact_mod_cast (show 0 < R' by omega)
    have hlog_le : Real.log (R' : ℝ) ≤ Real.log X := by
      have h1 : Real.log X = (1 / 36 : ℝ) * Real.log (N : ℝ) := Real.log_rpow hN0 (1 / 36 : ℝ)
      linarith only [hlog36, h1]
    exact (Real.exp_log hR'0).symm.trans_le ((Real.exp_le_exp.mpr hlog_le).trans_eq (Real.exp_log hX0))
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 ≤ 9 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [he1, h2, Real.exp_pos 1]
  have hlin_le : linearNearRowRadius c + 1 ≤ 19 * X := by
    unfold linearNearRowRadius
    nlinarith only [hc1, hcX, he2]
  have hup_le : c * Real.exp 1 + 1 ≤ 4 * X := by nlinarith only [hc0, hc1, hcX, he1]
  have hRR1_le : ((R' * R' : ℕ) + 1 : ℝ) ≤ 2 * X ^ 2 := by
    have hR1 : (1 : ℝ) ≤ R' := by exact_mod_cast (show 1 ≤ R' by omega)
    push_cast
    have hsq : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hR'X 2
    have h1sq : (1 : ℝ) ≤ (R' : ℝ) ^ 2 := one_le_pow₀ hR1
    linarith only [hsq, h1sq]
  have h1 : H_res * c ^ 8 ≤ (N : ℝ) := by
    have hHX : H_res ≤ X := hHL.trans hLX
    have hc8 : c ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hc0.le hcX 8
    calc
      H_res * c ^ 8 ≤ X * X ^ 8 := mul_le_mul hHX hc8 (by positivity) hX0.le
      _ = X ^ 9 := by ring
      _ ≤ (N : ℝ) := hpowX 9 (by norm_num)
  have h2 : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le hcX 2
    have hconst : 4 * (Real.exp 1 + 3) ^ 2 ≤ X := by
      have : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
      linarith only [this, hX2000]
    calc
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ X * X ^ 2 :=
        mul_le_mul hconst hc2 (by positivity) hX0.le
      _ = X ^ 3 := by ring
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h3 : c / (N : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]
    have h3X : 3 * c ≤ X ^ 2 := by nlinarith only [hcX, hX2000]
    exact (by linarith only [h3X] : c * 3 ≤ X ^ 2).trans (by simpa only [ one_mul] using hpowX 2 (by norm_num))
  have h4 : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) := by
    have hsq : (linearNearRowRadius c + 1) ^ 2 ≤ (19 * X) ^ 2 :=
      pow_le_pow_left₀ (by unfold linearNearRowRadius; positivity) hlin_le 2
    have h1444 : 1444 * X ^ 2 ≤ X ^ 3 := by nlinarith only [hX2000, sq_nonneg X]
    calc
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ 4 * (19 * X) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 1444 * X ^ 2 := by ring
      _ ≤ X ^ 3 := h1444
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h5 : R' ^ 6 ≤ N := by
    have hR6 : (R' : ℝ) ^ 6 ≤ (N : ℝ) :=
      (pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 6).trans (hpowX 6 (by norm_num))
    exact_mod_cast hR6
  have h6 : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) := by
    have h38 : 38 * X ^ 3 ≤ X ^ 4 := by
      calc
        38 * X ^ 3 ≤ X * X ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith only [hX2000]) (by positivity)
        _ = X ^ 4 := by ring
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (2 * X ^ 2) * (19 * X) :=
        mul_le_mul hRR1_le hlin_le (by unfold linearNearRowRadius; positivity) (by positivity)
      _ = 38 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h38
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h7 : ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) := by
    have h8 : 8 * X ^ 3 ≤ X ^ 4 := by nlinarith only [hX2000, pow_nonneg hX0.le 3]
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (2 * X ^ 2) * (4 * X) :=
        mul_le_mul hRR1_le hup_le (by positivity) (by positivity)
      _ = 8 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h8
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h8 : (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 1 / L := by
    have hprod : (R' : ℝ) ^ 2 * L ^ 3 ≤ (N : ℝ) := by
      have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
      have hL3 : L ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hL0.le hLX 3
      calc
        (R' : ℝ) ^ 2 * L ^ 3 ≤ X ^ 2 * X ^ 3 := mul_le_mul hR2 hL3 (by positivity) (by positivity)
        _ = X ^ 5 := by ring
        _ ≤ (N : ℝ) := hpowX 5 (by norm_num)
    have hsq : ((R' : ℝ) * Real.sqrt (L / (N : ℝ))) ^ 2 ≤ (1 / L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), one_div, inv_pow, ← one_div]
      rw [← mul_div_assoc, div_le_div_iff₀ hN0 (sq_pos_of_pos hL0)]
      calc
        (R' : ℝ) ^ 2 * L * L ^ 2 = (R' : ℝ) ^ 2 * L ^ 3 := by ring
        _ ≤ 1 * (N : ℝ) := by rw [one_mul]; exact hprod
    have hlhs0 : 0 ≤ (R' : ℝ) * Real.sqrt (L / (N : ℝ)) := by positivity
    have hrhs0 : 0 ≤ 1 / L := by positivity
    nlinarith only [hsq, hlhs0, hrhs0]
  have h9 : c ^ 5 * L / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc5 : c ^ 5 ≤ X ^ 5 := pow_le_pow_left₀ hc0.le hcX 5
    have hL2 : L ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hL0.le hLX 2
    calc
      c ^ 5 * L * L = c ^ 5 * L ^ 2 := by ring
      _ ≤ X ^ 5 * X ^ 2 := mul_le_mul hc5 hL2 (by positivity) (by positivity)
      _ = X ^ 7 := by ring
      _ ≤ (N : ℝ) := hpowX 7 (by norm_num)
  have h10 : c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc3 : c ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hc0.le hcX 3
    have hR4 : (R' : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 4
    calc
      c ^ 3 * (R' : ℝ) ^ 4 * L ≤ (X ^ 3 * X ^ 4) * X :=
        mul_le_mul (mul_le_mul hc3 hR4 (by positivity) (by positivity)) hLX hL0.le (by positivity)
      _ = X ^ 8 := by ring
      _ ≤ (N : ℝ) := hpowX 8 (by norm_num)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem rpow_horizon_L_smallness_bounds {Q₁ R' N : ℕ} {c C_R C_small H_res α q ν : ℝ}
    (hα128 : α ≤ 1 / 128) (hqmax : q ≤ 1 / 5)
    (hν : 0 < ν) (hν1000 : ν ≤ 1 / 1000) (hsep : 4 * α - q / 2 ≤ -ν)
    (hN1 : 1 ≤ N) (hQ₁2 : 2 ≤ Q₁) (hQR' : Q₁ ≤ R')
    (hc1 : 1 ≤ c) (hCR0 : 0 < C_R) (hCsmall0 : 0 < C_small) (hH0 : 0 < H_res)
    (hL2000 : 2000 ≤ Real.log (N : ℝ))
    (hHL : H_res ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hL45 : 36 ≤ Real.log (N : ℝ) ^ (7 / 10 : ℝ))
    (hCR_L : 2 * C_R + 2 ≤ Real.log (N : ℝ) ^ (1 / 400 : ℝ))
    (hCs_L : 20 * C_small + 3 ≤ Real.log (N : ℝ) ^ ν)
    (hQ_le : (Q₁ : ℝ) ≤ Real.log (N : ℝ) ^ q)
    (hQ_quarter : (1 / 4 : ℝ) * Real.log (N : ℝ) ^ q ≤ (Q₁ : ℝ))
    (hcα : c ≤ Real.log (N : ℝ) ^ α)
    (hR'_log : Real.log (R' : ℝ) ≤ C_R * c ^ 16 + Real.log (Q₁ : ℝ)) :
    c ≤ Real.log (N : ℝ) ∧
    36 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ) ∧
    R' ^ 6 ≤ N ∧
    18 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
    (1 + Real.log (R' : ℝ)) / Real.sqrt (Real.log (N : ℝ)) ≤ 1 ∧
    (1 + Real.log (R' : ℝ)) ^ 2 / Real.sqrt (Real.log (N : ℝ)) ≤ 1 ∧
    (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 ∧
    C_small * (c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / Real.log (N : ℝ) +
      ((1 + Real.log (R' : ℝ)) ^ 2 / Real.log (N : ℝ) + (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt (Real.log (N : ℝ))) +
      c * (1 + Real.log (R' : ℝ)) / Real.sqrt (Real.log (N : ℝ)) +
      c ^ 2 / Real.log (N : ℝ) +
      c ^ 2 * (1 + Real.log (R' : ℝ)) * Real.sqrt ((1 + Real.log c) / Real.log (N : ℝ)) +
      c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) +
      c ^ 5 * Real.log (N : ℝ) / (N : ℝ) +
      c ^ 4 / Real.sqrt (Q₁ : ℝ) +
      c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) +
      c ^ 2 * (1 + Real.log c) / Real.log (N : ℝ)) ≤ 1 := by
  have hα59 : α ≤ 1 / 59 := hα128.trans (by norm_num)
  let L := Real.log (N : ℝ)
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hR'2 : 2 ≤ R' := hQ₁2.trans hQR'
  have hc_59 : c ≤ L ^ (1 / 59 : ℝ) :=
    hcα.trans (Real.rpow_le_rpow_of_exponent_le hL1 hα59)
  have hcpow : ∀ k : ℕ, c ^ k ≤ L ^ ((k : ℝ) / 59) := fun k => by
    have hp := pow_le_pow_left₀ hc0.le hc_59 k
    have he : (L ^ (1 / 59 : ℝ)) ^ k = L ^ ((k : ℝ) / 59) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1; ring
    exact hp.trans_eq he
  have hcL : c ≤ L :=
    hc_59.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 59 : ℝ) ≤ 1))
  have h1R_le : 1 + Real.log (R' : ℝ) ≤ L ^ (3 / 10 : ℝ) := by
    have hc16 : c ^ 16 ≤ L ^ (119 / 400 : ℝ) :=
      (hcpow 16).trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (16 : ℝ) / 59 ≤ 119 / 400))
    have hQ0 : (0 : ℝ) < Q₁ := by exact_mod_cast (show 0 < Q₁ by omega)
    have hlogQ : Real.log (Q₁ : ℝ) ≤ L ^ (119 / 400 : ℝ) :=
      ((Real.log_le_sub_one_of_pos hQ0).trans (by linarith only)).trans
        (hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hqmax] : q ≤ 119 / 400)))
    have h1_10 : 1 ≤ L ^ (119 / 400 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hlin : 1 + Real.log (R' : ℝ) ≤ (C_R + 2) * L ^ (119 / 400 : ℝ) := by
      have hCRc : C_R * c ^ 16 ≤ C_R * L ^ (119 / 400 : ℝ) :=
        mul_le_mul_of_nonneg_left hc16 hCR0.le
      linarith only [hR'_log, hCRc, hlogQ, h1_10]
    have hmul : L ^ (1 / 400 : ℝ) * L ^ (119 / 400 : ℝ) = L ^ (3 / 10 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    exact hlin.trans ((mul_le_mul_of_nonneg_right (by linarith only [hCR_L, hCR0] : C_R + 2 ≤ L ^ (1 / 400 : ℝ)) (by positivity)).trans_eq hmul)
  have hlog36 : 36 * (1 + Real.log (R' : ℝ)) ≤ L := by
    have hmul : L ^ (7 / 10 : ℝ) * L ^ (3 / 10 : ℝ) = L := by
      rw [← Real.rpow_add hL0, show (7 / 10 : ℝ) + 3 / 10 = 1 by norm_num, Real.rpow_one]
    calc
      36 * (1 + Real.log (R' : ℝ)) ≤ 36 * L ^ (3 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left h1R_le (by norm_num)
      _ ≤ L ^ (7 / 10 : ℝ) * L ^ (3 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hL45 (by positivity)
      _ = L := hmul
  have hlog18 : 18 * (1 + Real.log (R' : ℝ)) ≤ L := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  obtain ⟨_, _, _, _, hR6N, hRNT_lin, hRNT_up, hR_sqrtL, hc5_N, hc3R4_N⟩ :=
    rpow_horizon_N_bounds hN1 hR'2 hc1 hH0 hL2000 hHL hLX hcL hlog36
  have h1L_le1 : 1 / L ≤ 1 := div_le_one_of_le₀ hL1 hL0.le
  have hR_sqrt1 : (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 1 := hR_sqrtL.trans h1L_le1
  let δ := L ^ (-ν)
  have hδ_le1 : δ ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν] : -ν ≤ 0)
  have hsqrtL : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
  have h1lc : 1 + Real.log c ≤ 2 * c := by
    have := Real.log_le_sub_one_of_pos hc0; linarith only [this, hc1]
  have h1R0 : 0 ≤ 1 + Real.log (R' : ℝ) := by
    have := Real.log_natCast_nonneg R'; positivity
  have h1R_sq : (1 + Real.log (R' : ℝ)) ^ 2 ≤ L ^ (3 / 5 : ℝ) := by
    have hp := pow_le_pow_left₀ h1R0 h1R_le 2
    have he : (L ^ (3 / 10 : ℝ)) ^ (2 : ℕ) = L ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    exact hp.trans_eq he
  have hs2_R : (1 + Real.log (R' : ℝ)) ^ 2 / L ≤ δ := by
    calc
      _ ≤ L ^ (3 / 5 : ℝ) / L := div_le_div_of_nonneg_right h1R_sq hL0.le
      _ = L ^ (-(2 / 5 : ℝ)) := by
        rw [show (-(2 / 5) : ℝ) = 3 / 5 - 1 by norm_num,
          Real.rpow_sub hL0, Real.rpow_one]
      _ ≤ δ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
  have hQ0 : (0 : ℝ) < Q₁ := by exact_mod_cast (show 0 < Q₁ by omega)
  have h1Q_le : 1 + Real.log (Q₁ : ℝ) ≤ L ^ (1 / 5 : ℝ) :=
    (by linarith only [Real.log_le_sub_one_of_pos hQ0] : 1 + Real.log (Q₁ : ℝ) ≤ Q₁).trans
      (hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 hqmax))
  have hs2_Q : (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L ≤ δ := by
    have hQsq := pow_le_pow_left₀
      (by have h := Real.log_natCast_nonneg Q₁; positivity : 0 ≤ 1 + Real.log (Q₁ : ℝ)) h1Q_le 2
    have heq : (L ^ (1 / 5 : ℝ)) ^ (2 : ℕ) = L ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
    rw [heq] at hQsq
    rw [hsqrtL]
    calc
      _ ≤ L ^ (2 / 5 : ℝ) / L ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hQsq (by positivity)
      _ = L ^ (-(1 / 10 : ℝ)) := by rw [← Real.rpow_sub hL0]; norm_num
      _ ≤ δ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
  have hdiv1_le1 : (1 + Real.log (R' : ℝ)) / Real.sqrt L ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.mpr hL0)).mpr
    rw [hsqrtL]
    exact h1R_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  -- The stronger envelope exponent makes the prime cross error uniformly bounded.
  have hdiv2_le_one : (1 + Real.log (R' : ℝ)) ^ 2 / Real.sqrt L ≤ 1 := by
    have hc16 : c ^ 16 ≤ L ^ (99 / 400 : ℝ) := by
      calc
        c ^ 16 ≤ (L ^ α) ^ 16 := pow_le_pow_left₀ hc0.le hcα 16
        _ = L ^ (16 * α) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα128])
    have hlogQ : Real.log (Q₁ : ℝ) ≤ L ^ (99 / 400 : ℝ) :=
      ((Real.log_le_sub_one_of_pos hQ0).trans (by linarith only)).trans
        (hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hqmax])))
    have h1 : 1 ≤ L ^ (99 / 400 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hlin : 1 + Real.log (R' : ℝ) ≤ (C_R + 2) * L ^ (99 / 400 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hc16 hCR0.le
      linarith only [hR'_log, h, hlogQ, h1]
    have hsharp : 1 + Real.log (R' : ℝ) ≤ L ^ (1 / 4 : ℝ) := by
      calc
        _ ≤ (C_R + 2) * L ^ (99 / 400 : ℝ) := hlin
        _ ≤ L ^ (1 / 400 : ℝ) * L ^ (99 / 400 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCR_L, hCR0]) (by positivity)
        _ = _ := by rw [← Real.rpow_add hL0]; norm_num
    apply (div_le_one (Real.sqrt_pos.mpr hL0)).mpr
    calc
      (1 + Real.log (R' : ℝ)) ^ 2 ≤ (L ^ (1 / 4 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ h1R0 hsharp 2
      _ = Real.sqrt L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, hsqrtL]
        norm_num
  have hδ0 : 0 ≤ δ := by dsimp only [δ]; positivity
  have hL_div1 : ∀ a : ℝ, L ^ a / L = L ^ (a - 1) := fun a => by
    rw [Real.rpow_sub hL0, Real.rpow_one]
  have hL_mul_div1 : ∀ a b : ℝ, L ^ a * L ^ b / L = L ^ (a + b - 1) := fun a b => by
    rw [Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_one]
  have hL_mul_div : ∀ a b d : ℝ, L ^ a * L ^ b / L ^ d = L ^ (a + b - d) := fun a b d => by
    rw [Real.rpow_sub hL0, Real.rpow_add hL0]
  have h1L_δ : 1 / L ≤ δ := by
    have heq : 1 / L = L ^ (-1 : ℝ) := by rw [one_div, ← Real.rpow_neg_one]
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
  -- Bound each of the 10 summands by 2 * δ
  have hs1 : c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L ≤ 2 * δ := by
    have hc2 := hcpow 2
    have h1 : c * (1 + Real.log c) ≤ 2 * c ^ 2 := by nlinarith only [hc0, h1lc]
    have hnum : c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) ≤
        2 * (L ^ ((2 : ℝ) / 59) * L ^ (3 / 10 : ℝ)) := by
      calc
        c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) ≤ (2 * c ^ 2) * L ^ (3 / 10 : ℝ) :=
          mul_le_mul h1 h1R_le h1R0 (by positivity)
        _ ≤ 2 * (L ^ ((2 : ℝ) / 59) * L ^ (3 / 10 : ℝ)) := by
          have := mul_le_mul_of_nonneg_right hc2 (by positivity : 0 ≤ L ^ (3 / 10 : ℝ))
          linarith only [this]
    have hexp : L ^ ((2 : ℝ) / 59 + 3 / 10 - 1) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L ≤
          (2 * (L ^ ((2 : ℝ) / 59) * L ^ (3 / 10 : ℝ))) / L :=
        div_le_div_of_nonneg_right hnum hL0.le
      _ = 2 * (L ^ ((2 : ℝ) / 59) * L ^ (3 / 10 : ℝ) / L) := by ring
      _ = 2 * L ^ ((2 : ℝ) / 59 + 3 / 10 - 1) := by rw [hL_mul_div1]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hs2 : ((1 + Real.log (R' : ℝ)) ^ 2 / L +
      (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L) ≤ 2 * δ := by
    linarith only [hs2_R, hs2_Q]
  have hs3 : c * (1 + Real.log (R' : ℝ)) / Real.sqrt L ≤ 2 * δ := by
    have hexp : L ^ ((1 / 59 : ℝ) + 3 / 10 - 1 / 2) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    rw [hsqrtL]
    calc
      c * (1 + Real.log (R' : ℝ)) / L ^ (1 / 2 : ℝ) ≤
          L ^ (1 / 59 : ℝ) * L ^ (3 / 10 : ℝ) / L ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul hc_59 h1R_le h1R0 (by positivity)) (by positivity)
      _ = L ^ ((1 / 59 : ℝ) + 3 / 10 - 1 / 2) := hL_mul_div _ _ _
      _ ≤ δ := hexp
      _ ≤ 2 * δ := by linarith only [hδ0]
  have hs4_δ : c ^ 2 / L ≤ δ := by
    have hexp : L ^ ((2 : ℝ) / 59 - 1) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c ^ 2 / L ≤ L ^ ((2 : ℝ) / 59) / L := div_le_div_of_nonneg_right (hcpow 2) hL0.le
      _ = L ^ ((2 : ℝ) / 59 - 1) := hL_div1 _
      _ ≤ δ := hexp
  have hs4 : c ^ 2 / L ≤ 2 * δ := by linarith only [hs4_δ, hδ0]
  have hs5 : c ^ 2 * (1 + Real.log (R' : ℝ)) * Real.sqrt ((1 + Real.log c) / L) ≤ 2 * δ := by
    have hsqrt_c : Real.sqrt ((1 + Real.log c) / L) ≤ 2 * c / Real.sqrt L := by
      rw [Real.sqrt_div (by have := Real.log_nonneg hc1; positivity)]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg L)
      exact (Real.sqrt_le_sqrt (h1lc.trans (by nlinarith only [hc1]))).trans_eq
        (Real.sqrt_sq (by positivity))
    have hc3 := hcpow 3
    have hexp : L ^ ((3 : ℝ) / 59 + 3 / 10 - 1 / 2) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c ^ 2 * (1 + Real.log (R' : ℝ)) * Real.sqrt ((1 + Real.log c) / L) ≤
          c ^ 2 * (1 + Real.log (R' : ℝ)) * (2 * c / Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hsqrt_c (by positivity)
      _ = 2 * (c ^ 3 * (1 + Real.log (R' : ℝ)) / Real.sqrt L) := by ring
      _ ≤ 2 * (L ^ ((3 : ℝ) / 59) * L ^ (3 / 10 : ℝ) / L ^ (1 / 2 : ℝ)) := by
        rw [hsqrtL]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul hc3 h1R_le h1R0 (by positivity)) (by positivity))
          zero_le_two
      _ = 2 * L ^ ((3 : ℝ) / 59 + 3 / 10 - 1 / 2) := by rw [hL_mul_div]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hs6 : c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 2 * δ := by
    calc
      c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) =
          c ^ 2 * ((R' : ℝ) * Real.sqrt (L / (N : ℝ))) := by ring
      _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR_sqrtL (by positivity)
      _ = c ^ 2 / L := by ring
      _ ≤ 2 * δ := hs4
  have hs7 : c ^ 5 * L / (N : ℝ) ≤ 2 * δ := (hc5_N.trans h1L_δ).trans (by linarith only [hδ0])
  have hs8 : c ^ 4 / Real.sqrt (Q₁ : ℝ) ≤ 2 * δ := by
    have hsqrtQ : (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt (Q₁ : ℝ) := by
      have hsq : ((1 / 2 : ℝ) * L ^ (q / 2)) ^ 2 = (1 / 4 : ℝ) * L ^ q := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (q / 2)) 2, ← Real.rpow_mul hL0.le]
        norm_num
      have hpos : 0 ≤ (1 / 2 : ℝ) * L ^ (q / 2) := by positivity
      exact (Real.sqrt_sq hpos).symm.trans_le (Real.sqrt_le_sqrt (hsq.trans_le hQ_quarter))
    have hc4 : c ^ 4 ≤ L ^ (4 * α) := by
      have hp := pow_le_pow_left₀ hc0.le hcα 4
      have heq : (L ^ α) ^ (4 : ℕ) = L ^ (4 * α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        congr 1
        ring
      exact hp.trans_eq heq
    have hexp : L ^ (4 * α - q / 2) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 hsep
    calc
      c ^ 4 / Real.sqrt (Q₁ : ℝ) ≤ L ^ (4 * α) / ((1 / 2 : ℝ) * L ^ (q / 2)) :=
        (div_le_div_of_nonneg_right hc4 (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrtQ)
      _ = 2 * (L ^ (4 * α) / L ^ (q / 2)) := by ring
      _ = 2 * L ^ (4 * α - q / 2) := by rw [← Real.rpow_sub hL0]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hs9 : c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 2 * δ :=
    (hc3R4_N.trans h1L_δ).trans (by linarith only [hδ0])
  have hs10 : c ^ 2 * (1 + Real.log c) / L ≤ 2 * δ := by
    have hc3 := hcpow 3
    have h1 : c ^ 2 * (1 + Real.log c) ≤ 2 * c ^ 3 := by nlinarith only [sq_nonneg c, hc0, h1lc]
    have hexp : L ^ ((3 : ℝ) / 59 - 1) ≤ δ :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν1000])
    calc
      c ^ 2 * (1 + Real.log c) / L ≤ (2 * c ^ 3) / L := div_le_div_of_nonneg_right h1 hL0.le
      _ ≤ (2 * L ^ ((3 : ℝ) / 59)) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc3 zero_le_two) hL0.le
      _ = 2 * (L ^ ((3 : ℝ) / 59) / L) := by ring
      _ = 2 * L ^ ((3 : ℝ) / 59 - 1) := by rw [hL_div1]
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hexp zero_le_two
  have hsum_small : C_small * (c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L +
      ((1 + Real.log (R' : ℝ)) ^ 2 / L + (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L) +
      c * (1 + Real.log (R' : ℝ)) / Real.sqrt L +
      c ^ 2 / L +
      c ^ 2 * (1 + Real.log (R' : ℝ)) * Real.sqrt ((1 + Real.log c) / L) +
      c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) +
      c ^ 5 * L / (N : ℝ) +
      c ^ 4 / Real.sqrt (Q₁ : ℝ) +
      c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) +
      c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have h10 : c * (1 + Real.log c) * (1 + Real.log (R' : ℝ)) / L +
        ((1 + Real.log (R' : ℝ)) ^ 2 / L + (1 + Real.log (Q₁ : ℝ)) ^ 2 / Real.sqrt L) +
        c * (1 + Real.log (R' : ℝ)) / Real.sqrt L +
        c ^ 2 / L +
        c ^ 2 * (1 + Real.log (R' : ℝ)) * Real.sqrt ((1 + Real.log c) / L) +
        c ^ 2 * (R' : ℝ) * Real.sqrt (L / (N : ℝ)) +
        c ^ 5 * L / (N : ℝ) +
        c ^ 4 / Real.sqrt (Q₁ : ℝ) +
        c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) +
        c ^ 2 * (1 + Real.log c) / L ≤ 20 * δ := by
      linarith only [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10]
    have hmul : L ^ ν * δ = 1 := by
      dsimp only [δ]
      rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
    calc
      _ ≤ C_small * (20 * δ) := mul_le_mul_of_nonneg_left h10 hCsmall0.le
      _ = (20 * C_small) * δ := by ring
      _ ≤ L ^ ν * δ := mul_le_mul_of_nonneg_right (by linarith only [hCs_L] : 20 * C_small ≤ L ^ ν) hδ0
      _ = 1 := hmul
  exact ⟨hcL, hlog36, hR6N, hlog18, hRNT_lin, hRNT_up, hdiv1_le1, hdiv2_le_one, hR_sqrt1, hsum_small⟩

theorem eventually_powerLog_low_band_and_coercivity_gap
    {K_res C_coerc α q ν : ℝ} {k : ℕ} (hK : 0 < K_res) (_hC_coerc : 0 < C_coerc)
    (_hα : 0 < α) (hα_lt : α < (1 / 59 : ℝ))
    (hq : 0 < q) (hqmax : q ≤ 1 / 5) (hν : 0 < ν) (hk : 1 ≤ k)
    (hbudget_exp : 5 * q + 19 * α + 1 / (k : ℝ) - 1 ≤ -ν)
    (hgap_pos : 0 < q / 4 - α) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      ∀ c : ℝ, 1 ≤ c → c ≤ L ^ α →
        c ≤ L ^ (1 / 59 : ℝ) ∧
        9 * (1 + Real.log (Q₁ : ℝ)) / L *
          (|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
            2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4) ≤ 1 / 16 ∧
        K_res * (Q₁ : ℝ) ^ 5 * (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
          c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 128 ∧
        K_res * (Q₁ : ℝ) ^ 5 * (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
          c ^ 3 * L ^ (1 / (k : ℝ)) / L) /
          ((2 : ℝ) / (2 * c ^ 7)) ^ 2 ≤ 1 / 36 ∧
        2 * (2 : ℝ) + 4 + C_coerc ≤
          (1 / 4) * Real.log (Q₁ : ℝ) - Real.log c := by
  have hα_59 : α < 1 / 59 := hα_lt
  have hκ : 0 < (2 : ℝ) := by norm_num
  let M_self := |completeWeilSelfFinitePart zeroFreeLogProfile 1| + 5
  let M_rate := max (384 * K_res) (432 * K_res / (2 : ℝ) ^ 2)
  let M_coerc := (2 * (2 : ℝ) + 4 + C_coerc +
    1 / 4) / (q / 4 - α)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [eventually_floor_log_rpow_bounds hq hqmax,
    eventually_log_nat_le_rpow_36,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp hLlim).eventually_ge_atTop
      (144 * M_self),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop M_rate,
    hllim.eventually_ge_atTop M_coerc,
    hLlim.eventually_ge_atTop 1, eventually_ge_atTop 2] with
    N hQ_all hLX hL35 hL50 hll hL1 hN2
  dsimp only [Function.comp_def] at hL35 hL50 hll
  obtain ⟨hQ2, hQ_le, _, hlogQ_lb, _⟩ := hQ_all
  dsimp only
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  intro c hc1 hcup
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc_59 : c ≤ L ^ (1 / 59 : ℝ) :=
    hcup.trans (Real.rpow_le_rpow_of_exponent_le hL1 hα_59.le)
  have hcpow : ∀ j : ℕ, c ^ j ≤ L ^ ((j : ℝ) * α) := fun j => by
    have hp := pow_le_pow_left₀ hc0.le hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  -- 1. Gram error bound
  have hgram : 9 * (1 + Real.log (Q₁ : ℝ)) / L *
      (|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
        2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4) ≤ 1 / 16 := by
    have hQ2' : 2 ≤ Q₁ := hQ2
    have hQ0 : (0 : ℝ) < Q₁ := Nat.cast_pos.mpr (zero_lt_two.trans_le hQ2')
    have hQ_15 : (Q₁ : ℝ) ≤ L ^ (1 / 5 : ℝ) :=
      hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 hqmax)
    have h1logQ : 1 + Real.log (Q₁ : ℝ) ≤ L ^ (1 / 5 : ℝ) :=
      (by linarith only [Real.log_le_sub_one_of_pos hQ0] : 1 + Real.log (Q₁ : ℝ) ≤ Q₁).trans hQ_15
    have hlogQ_15 : Real.log (Q₁ : ℝ) ≤ L ^ (1 / 5 : ℝ) := by linarith only [h1logQ]
    have hc4_15 : c ^ 4 ≤ L ^ (1 / 5 : ℝ) :=
      (hcpow 4).trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα_59] : (4 : ℝ) * α ≤ 1 / 5))
    have h1_15 : 1 ≤ L ^ (1 / 5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hbrack : |completeWeilSelfFinitePart zeroFreeLogProfile 1| +
        2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4 ≤ M_self * L ^ (1 / 5 : ℝ) := by
      have ha : |completeWeilSelfFinitePart zeroFreeLogProfile 1| ≤
          |completeWeilSelfFinitePart zeroFreeLogProfile 1| * L ^ (1 / 5 : ℝ) := by
        nlinarith only [abs_nonneg (completeWeilSelfFinitePart zeroFreeLogProfile 1), h1_15]
      dsimp only [M_self]
      linarith only [ha, hlogQ_15, hc4_15]
    have hexp : L ^ (1 / 5 : ℝ) * L ^ (1 / 5 : ℝ) / L = L ^ (-3 / 5 : ℝ) := by
      rw [show (-3 / 5 : ℝ) = 1 / 5 + 1 / 5 - 1 by norm_num,
        Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_one]
    have hmul1 : L ^ (3 / 5 : ℝ) * L ^ (-3 / 5 : ℝ) = 1 := by
      rw [← Real.rpow_add hL0, show (3 / 5 : ℝ) + (-3 / 5) = 0 by norm_num, Real.rpow_zero]
    calc
      9 * (1 + Real.log (Q₁ : ℝ)) / L *
          (|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
            2 * Real.log (Q₁ : ℝ) + 3 * c ^ 4) ≤
          (9 * L ^ (1 / 5 : ℝ) / L) * (M_self * L ^ (1 / 5 : ℝ)) :=
        mul_le_mul (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1logQ (by norm_num)) hL0.le)
          hbrack (by have := Real.log_natCast_nonneg Q₁; positivity) (by positivity)
      _ = (9 * M_self) * (L ^ (1 / 5 : ℝ) * L ^ (1 / 5 : ℝ) / L) := by ring
      _ = (1 / 16 : ℝ) * ((144 * M_self) * L ^ (-3 / 5 : ℝ)) := by rw [hexp]; ring
      _ ≤ (1 / 16 : ℝ) * (L ^ (3 / 5 : ℝ) * L ^ (-3 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL35 (by positivity)) (by norm_num)
      _ = 1 / 16 := by rw [hmul1, mul_one]
  -- 2 & 3. Residual sum and budget bounds
  have hsL : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hcL : c ≤ L := hc_59.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 59 : ℝ) ≤ 1))
  have hrate_le : c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
      c ^ 3 * L ^ (1 / (k : ℝ)) / L ≤ 3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L := by
    have hLN : c ^ 5 * (L / (N : ℝ)) ^ 2 ≤ 1 / L := by
      rw [div_pow, ← mul_div_assoc,
        div_le_div_iff₀ (sq_pos_of_pos hN0) hL0, one_mul]
      let X := (N : ℝ) ^ (1 / 36 : ℝ)
      have hX1 : 1 ≤ X := hL1.trans hLX
      have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
        dsimp only [X]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        norm_num
      have hL8 : L ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hL0.le hLX 8
      have hX8 : X ^ 8 ≤ (N : ℝ) :=
        (pow_le_pow_right₀ hX1 (by norm_num : 8 ≤ 36)).trans_eq hX36
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      calc
        c ^ 5 * L ^ 2 * L = c ^ 5 * L ^ 3 := by ring
        _ ≤ L ^ 5 * L ^ 3 := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hc0.le hcL 5) (by positivity)
        _ = L ^ 8 := by ring
        _ ≤ (N : ℝ) := hL8.trans hX8
        _ ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1R]
    have ht1 : c ^ 5 / L ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L :=
      div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hsL) hL0.le
    have ht2 : c ^ 10 * (L / (N : ℝ)) ^ 2 ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L := by
      calc
        _ = c ^ 5 * (c ^ 5 * (L / (N : ℝ)) ^ 2) := by ring
        _ ≤ c ^ 5 * (1 / L) := mul_le_mul_of_nonneg_left hLN (by positivity)
        _ = c ^ 5 / L := by ring
        _ ≤ _ := ht1
    have ht3 : c ^ 3 * L ^ (1 / (k : ℝ)) / L ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 5)) (by positivity)) hL0.le
    calc
      _ ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L + c ^ 5 * L ^ (1 / (k : ℝ)) / L +
          c ^ 5 * L ^ (1 / (k : ℝ)) / L := add_le_add (add_le_add ht1 ht2) ht3
      _ = 3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L := by ring
  have hQ5 : (Q₁ : ℝ) ^ 5 ≤ L ^ (5 * q) := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 5
    have he : (L ^ q) ^ (5 : ℕ) = L ^ (5 * q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    exact hp.trans_eq he
  have hmul50 : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hQ5_c19 : (Q₁ : ℝ) ^ 5 * c ^ 19 * L ^ (1 / (k : ℝ)) / L ≤
      L ^ (-ν) := by
    calc
      _ ≤ L ^ (5 * q) * L ^ ((19 : ℝ) * α) * L ^ (1 / (k : ℝ)) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hQ5 (hcpow 19) (by positivity) (by positivity))
          (by positivity)) hL0.le
      _ = L ^ ((5 * q) + (19 : ℝ) * α + 1 / (k : ℝ) - 1) := by
        rw [Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hbudget_exp
  have hQ5_c5 : (Q₁ : ℝ) ^ 5 * c ^ 5 * L ^ (1 / (k : ℝ)) / L ≤
      L ^ (-ν) := by
    apply le_trans ?_ hQ5_c19
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (by norm_num : 5 ≤ 19))
        (by positivity)) (by positivity)) hL0.le
  have hres_sum : K_res * (Q₁ : ℝ) ^ 5 * (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
      c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 128 := by
    have hM1 : 384 * K_res ≤ L ^ ν := (le_max_left _ _).trans hL50
    calc
      _ ≤ K_res * (Q₁ : ℝ) ^ 5 * (3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L) :=
        mul_le_mul_of_nonneg_left hrate_le (by positivity)
      _ = (1 / 128 : ℝ) * ((384 * K_res) *
          ((Q₁ : ℝ) ^ 5 * c ^ 5 * L ^ (1 / (k : ℝ)) / L)) := by ring
      _ ≤ (1 / 128 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hM1 hQ5_c5 (by positivity) (by positivity))
          (by norm_num)
      _ = 1 / 128 := by rw [hmul50, mul_one]
  have hbudget : K_res * (Q₁ : ℝ) ^ 5 * (c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
      c ^ 3 * L ^ (1 / (k : ℝ)) / L) /
      ((2 : ℝ) / (2 * c ^ 7)) ^ 2 ≤ 1 / 36 := by
    have hM2 : 432 * K_res / (2 : ℝ) ^ 2 ≤ L ^ ν :=
      (le_max_right _ _).trans hL50
    calc
      _ ≤ K_res * (Q₁ : ℝ) ^ 5 * (3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L) /
          ((2 : ℝ) / (2 * c ^ 7)) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrate_le (by positivity)) (sq_nonneg _)
      _ = (1 / 36 : ℝ) * ((432 * K_res / (2 : ℝ) ^ 2) *
          ((Q₁ : ℝ) ^ 5 * c ^ 19 * L ^ (1 / (k : ℝ)) / L)) := by
        field_simp [hκ.ne', hc0.ne', hL0.ne']
        ring
      _ ≤ (1 / 36 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hM2 hQ5_c19 (by positivity) (by positivity))
          (by norm_num)
      _ = 1 / 36 := by rw [hmul50, mul_one]

  -- 4. Coercivity gap
  have hcoerc_gap : 2 * (2 : ℝ) + 4 + C_coerc ≤
      (1 / 4) * Real.log (Q₁ : ℝ) - Real.log c := by
    have hlogc : Real.log c ≤ α * Real.log L :=
      (Real.log_le_log hc0 hcup).trans_eq (Real.log_rpow hL0 α)
    have hq_scaled : (q / 4) * Real.log L -
        1 / 4 ≤
        (1 / 4) * Real.log (Q₁ : ℝ) := by
      have hpos : (0 : ℝ) ≤ 1 / 4 := by positivity
      have hm := mul_le_mul_of_nonneg_left hlogQ_lb hpos
      have heq : (1 / 4) * (q * Real.log L - 1) =
          (q / 4) * Real.log L -
            1 / 4 := by ring
      linarith only [hm, heq]
    have hll_scaled : 2 * (2 : ℝ) + 4 + C_coerc +
        1 / 4 ≤
        (q / 4 - α) * Real.log L :=
      ((div_le_iff₀ hgap_pos).mp (show M_coerc ≤ Real.log L from hll)).trans_eq (mul_comm _ _)
    linarith only [hlogc, hq_scaled, hll_scaled]
  exact ⟨hc_59, hgram, hres_sum, hbudget, hcoerc_gap⟩

end GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit.rpow_horizon_L_smallness_bounds
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit.eventually_powerLog_low_band_and_coercivity_gap
