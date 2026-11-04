import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSignedCriticalResidualIsCompactBelowOverlap

/-!
# Decay of the critical conductor residual above overlap

On the logarithmic conductor packet, pairs with at least one conductor
above overlap have vanishing total energy-normalized squared residual.
A logarithmic exponent slightly above one eighth accommodates every fixed
positive critical ratio. The polar subtraction vanishes on these pairs.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis

private lemma one_add_log_le_rpow_256 {L : ℝ} (hL1 : 1 ≤ L) :
    1 + Real.log L ≤ 256 * L ^ (1 / 256 : ℝ) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht0 : 0 < L ^ (1 / 256 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hlog : Real.log (L ^ (1 / 256 : ℝ)) = (1 / 256 : ℝ) * Real.log L := Real.log_rpow hL0 _
  have h1 := Real.log_le_sub_one_of_pos ht0
  linarith only [hlog, h1]

private lemma rate_vb_unrestricted_critical_le {N : ℕ} {c : ℝ}
    (hc1 : 1 ≤ c) (hL1 : 1 ≤ Real.log (N : ℝ))
    (hc_log : c ≤ Real.log (N : ℝ) ^ (129 / 1024 : ℝ))
    (hL8N : Real.log (N : ℝ) ^ (8 : ℕ) ≤ N) :
    c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (128 : ℕ) : ℝ) / Real.log N +
        c ^ 5 * Real.log N / (N : ℝ) ≤
      65537 * Real.log (N : ℝ) ^ (-879 / 1024 : ℝ) := by
  let L := Real.log (N : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc_le_L : c ≤ L :=
    hc_log.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hN0 : (0 : ℝ) < N := (pow_pos hL0 8).trans_le hL8N
  have hlogc_sq : (1 + Real.log c) ^ 2 ≤ 65536 * L ^ (1 / 128 : ℝ) := by
    have h1 : 1 + Real.log c ≤ 256 * L ^ (1 / 256 : ℝ) :=
      (by linarith [Real.log_le_log hc0 hc_le_L] : 1 + Real.log c ≤ 1 + Real.log L).trans
        (one_add_log_le_rpow_256 hL1)
    calc
      (1 + Real.log c) ^ 2 ≤ (256 * L ^ (1 / 256 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) h1 2
      _ = 65536 * L ^ (1 / 128 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 2, ← Real.rpow_mul hL0.le]
        norm_num
  have ht1 : c * (1 + Real.log c) ^ 2 * L ^ (1 / (128 : ℕ) : ℝ) / L ≤
      65536 * L ^ (-879 / 1024 : ℝ) := by
    have hm1 : c * (1 + Real.log c) ^ 2 ≤ L ^ (129 / 1024 : ℝ) * (65536 * L ^ (1 / 128 : ℝ)) :=
      mul_le_mul hc_log hlogc_sq (sq_nonneg _) (by positivity)
    rw [show ((128 : ℕ) : ℝ) = 128 by norm_num]
    calc
      c * (1 + Real.log c) ^ 2 * L ^ (1 / 128 : ℝ) / L ≤
          L ^ (129 / 1024 : ℝ) * (65536 * L ^ (1 / 128 : ℝ)) * L ^ (1 / 128 : ℝ) / L :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hm1 (by positivity)) hL0.le
      _ = 65536 * (L ^ (129 / 1024 : ℝ) * L ^ (1 / 128 : ℝ) * L ^ (1 / 128 : ℝ) * L ^ (-1 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one L]; ring
      _ = 65536 * L ^ (-879 / 1024 : ℝ) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
  have ht2 : c ^ 5 * L / (N : ℝ) ≤ L ^ (-879 / 1024 : ℝ) := by
    have hc5 : c ^ 5 * L * L ≤ N := by
      calc
        c ^ 5 * L * L ≤ L ^ 5 * L * L := by
          gcongr
        _ = L ^ 7 := by ring
        _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
        _ ≤ N := hL8N
    have hinv : c ^ 5 * L / (N : ℝ) ≤ L ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← one_div, div_le_div_iff₀ hN0 hL0]
      linarith only [hc5]
    exact hinv.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  linarith only [ht1, ht2]

private noncomputable def rawCriticalRelativeSquare (c : ℝ) (N m l : ℕ) : ℝ :=
  |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy tiltedUnitSpline c m •
        normalizedRamanujanHorizonVector m N,
    normalizedRamanujanHorizonVector l N⟫| ^ 2 /
    (completedConductorEnergy tiltedUnitSpline c m *
      completedConductorEnergy tiltedUnitSpline c l)

private lemma rawCriticalRelativeSquare_high_sum_le {N Q₁ : ℕ} {c K_vb L r_vb : ℝ}
    (_hKvb : 0 < K_vb) (hL1 : 1 ≤ L) (hc1 : 1 ≤ c)
    (hr_vb0 : 0 ≤ r_vb) (hr_vb : r_vb ≤ 65537 * L ^ (-879 / 1024 : ℝ))
    (hc7_le : c ^ 7 ≤ L ^ (903 / 1024 : ℝ))
    (hQ₁_le : (Q₁ : ℝ) ≤ L ^ (13 / 32 : ℝ))
    (h1Q_le : 1 + Real.log (Q₁ : ℝ) ≤ 1 + Real.log L)
    (hQ₁_sq : (Q₁ : ℝ) ^ 2 ≤ L ^ (13 / 16 : ℝ))
    (hQ₁_sq_common : (Q₁ : ℝ) ^ 2 ≤ L ^ (903 / 1024 : ℝ))
    (hQ_logL_sq : (Q₁ : ℝ) ^ 2 * (1 + Real.log L) ^ 2 ≤ 65536 * L ^ (105 / 128 : ℝ))
    (hQ_logQ_sq : (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 ≤ 65536 * L ^ (903 / 1024 : ℝ))
    (hbi_pt : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ L ^ (13 / 32 : ℝ) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ L ^ (13 / 32 : ℝ) →
      |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫| ≤
        K_vb * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) * r_vb) :
    (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if c < (m : ℝ) then rawCriticalRelativeSquare c N m l else 0) +
      (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if c < (l : ℝ) then rawCriticalRelativeSquare c N m l else 0) ≤
        ((K_vb ^ 2 / tiltedSplineSpectralFloorConstant ^ 2) * 65537 ^ 2 * 262152) /
          L ^ (15 / 1024 : ℝ) := by
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = tiltedSplineSpectralFloorConstant := ⟨_, rfl⟩
  have hκ : 0 < κ := hκ_def ▸ tiltedSplineSpectralFloorConstant_pos
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hE_nn : ∀ m : ℕ, 0 < m → 0 ≤ completedConductorEnergy tiltedUnitSpline c m := fun m hm =>
    completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc0 hm
  have hr_vb_sq : r_vb ^ 2 ≤ 65537 ^ 2 * L ^ (-879 / 512 : ℝ) := by
    calc
      r_vb ^ 2 ≤ (65537 * L ^ (-879 / 1024 : ℝ)) ^ 2 := pow_le_pow_left₀ hr_vb0 hr_vb 2
      _ = 65537 ^ 2 * L ^ (-879 / 512 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (-879 / 1024 : ℝ)) 2, ← Real.rpow_mul hL0.le]; norm_num
  have hpt_vb : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁,
      rawCriticalRelativeSquare c N m l ≤ (K_vb ^ 2 * r_vb ^ 2) *
        (((m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m) *
          ((l : ℝ) / completedConductorEnergy tiltedUnitSpline c l)) := by
    intro m hm l hl
    obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
    obtain ⟨hl1, hlQ⟩ := mem_Icc.mp hl
    have hb := hbi_pt m hm1 ((by exact_mod_cast hmQ : (m : ℝ) ≤ Q₁).trans hQ₁_le)
      l hl1 ((by exact_mod_cast hlQ : (l : ℝ) ≤ Q₁).trans hQ₁_le)
    unfold rawCriticalRelativeSquare
    refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hb 2)
      (mul_nonneg (hE_nn m hm1) (hE_nn l hl1))).trans_eq ?_
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have h_hiL : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁,
      (if c < (m : ℝ) then rawCriticalRelativeSquare c N m l else 0) ≤
        (K_vb ^ 2 * r_vb ^ 2) *
          (((Q₁ : ℝ) * (1 + Real.log L) ^ 2 / κ) *
            ((l : ℝ) / completedConductorEnergy tiltedUnitSpline c l)) := by
    intro m hm l hl
    obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
    obtain ⟨hl1, _⟩ := mem_Icc.mp hl
    split_ifs with hmc
    · have hEm : κ ≤ completedConductorEnergy tiltedUnitSpline c m := by
        rw [hκ_def]
        exact tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm1 hmc.le
      have hmQ' : (m : ℝ) ≤ Q₁ := by exact_mod_cast hmQ
      have hm_num : (m : ℝ) * (1 + Real.log m) ^ 2 ≤ (Q₁ : ℝ) * (1 + Real.log L) ^ 2 := by
        have hlog : 1 + Real.log (m : ℝ) ≤ 1 + Real.log L := by
          have := Real.log_le_log (by exact_mod_cast hm1 : (0 : ℝ) < m) hmQ'
          linarith only [this, h1Q_le]
        exact mul_le_mul hmQ'
          (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg m]) hlog 2)
          (sq_nonneg _) (Nat.cast_nonneg _)
      have hdiv : (m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m ≤
          (Q₁ : ℝ) * (1 + Real.log L) ^ 2 / κ :=
        (div_le_div_of_nonneg_right hm_num (hE_nn m hm1)).trans
          (div_le_div_of_nonneg_left
            (mul_nonneg (Nat.cast_nonneg Q₁) (sq_nonneg _)) hκ hEm)
      exact (hpt_vb m hm l hl).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdiv (div_nonneg (Nat.cast_nonneg l) (hE_nn l hl1)))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg Q₁) (sq_nonneg _)) hκ.le)
          (div_nonneg (Nat.cast_nonneg l) (hE_nn l hl1)))
  have h_hiR : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁,
      (if c < (l : ℝ) then rawCriticalRelativeSquare c N m l else 0) ≤
        (K_vb ^ 2 * r_vb ^ 2) *
          (((m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m) *
            ((Q₁ : ℝ) / κ)) := by
    intro m hm l hl
    obtain ⟨hm1, _⟩ := mem_Icc.mp hm
    obtain ⟨hl1, hlQ⟩ := mem_Icc.mp hl
    split_ifs with hlc
    · have hEl : κ ≤ completedConductorEnergy tiltedUnitSpline c l := by
        rw [hκ_def]
        exact tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hl1 hlc.le
      have hdiv : (l : ℝ) / completedConductorEnergy tiltedUnitSpline c l ≤ (Q₁ : ℝ) / κ :=
        (div_le_div_of_nonneg_right (by exact_mod_cast hlQ) (hE_nn l hl1)).trans
          (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hκ hEl)
      exact (hpt_vb m hm l hl).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdiv
          (div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _)) (hE_nn m hm1)))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _)) (hE_nn m hm1))
          (div_nonneg (Nat.cast_nonneg Q₁) hκ.le))
  have hsl : (∑ l ∈ Icc 1 Q₁, (l : ℝ) / completedConductorEnergy tiltedUnitSpline c l) ≤
      3 * L ^ (903 / 1024 : ℝ) / κ := by
    have h0 := sum_conductor_inv_energy_le hc1 Q₁
    rw [← hκ_def] at h0
    exact h0.trans (div_le_div_of_nonneg_right (by linarith only [hc7_le, hQ₁_sq_common]) hκ.le)
  have hsm : (∑ m ∈ Icc 1 Q₁, (m : ℝ) * (1 + Real.log m) ^ 2 /
      completedConductorEnergy tiltedUnitSpline c m) ≤ 65544 * L ^ (903 / 1024 : ℝ) / κ := by
    have h0 := sum_conductor_log_sq_inv_energy_le hc1 Q₁
    rw [← hκ_def] at h0
    exact h0.trans (div_le_div_of_nonneg_right (by linarith only [hc7_le, hQ_logQ_sq]) hκ.le)
  have hsum_hiL :
      (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if c < (m : ℝ) then rawCriticalRelativeSquare c N m l else 0) ≤
        (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 / L ^ (15 / 1024 : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁,
            (K_vb ^ 2 * r_vb ^ 2) *
              (((Q₁ : ℝ) * (1 + Real.log L) ^ 2 / κ) *
                ((l : ℝ) / completedConductorEnergy tiltedUnitSpline c l)) :=
        sum_le_sum fun m hm => sum_le_sum fun l hl => h_hiL m hm l hl
      _ = (K_vb ^ 2 * r_vb ^ 2) *
            (((Q₁ : ℝ) ^ 2 * (1 + Real.log L) ^ 2 / κ) *
              (∑ l ∈ Icc 1 Q₁, (l : ℝ) / completedConductorEnergy tiltedUnitSpline c l)) := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_sum, ← mul_sum]
        ring
      _ ≤ (K_vb ^ 2 * (65537 ^ 2 * L ^ (-879 / 512 : ℝ))) *
            ((65536 * L ^ (105 / 128 : ℝ) / κ) * (3 * L ^ (903 / 1024 : ℝ) / κ)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hr_vb_sq (sq_nonneg _))
          (mul_le_mul (div_le_div_of_nonneg_right hQ_logL_sq hκ.le) hsl
            (sum_nonneg fun l hl => div_nonneg (Nat.cast_nonneg l) (hE_nn l (mem_Icc.mp hl).1))
            (by positivity))
          (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hκ.le)
            (sum_nonneg fun l hl => div_nonneg (Nat.cast_nonneg l) (hE_nn l (mem_Icc.mp hl).1)))
          (by positivity)
      _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 *
            (L ^ (-879 / 512 : ℝ) * L ^ (105 / 128 : ℝ) * L ^ (903 / 1024 : ℝ)) := by ring
      _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 * L ^ (-15 / 1024 : ℝ) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
      _ ≤ (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 * L ^ (-(15 / 1024 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
          (by positivity)
      _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 / L ^ (15 / 1024 : ℝ) := by
        rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  have hsum_hiR :
      (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if c < (l : ℝ) then rawCriticalRelativeSquare c N m l else 0) ≤
        (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 / L ^ (15 / 1024 : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁,
            (K_vb ^ 2 * r_vb ^ 2) *
              (((m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m) *
                ((Q₁ : ℝ) / κ)) :=
        sum_le_sum fun m hm => sum_le_sum fun l hl => h_hiR m hm l hl
      _ = (K_vb ^ 2 * r_vb ^ 2) *
            ((∑ m ∈ Icc 1 Q₁, (m : ℝ) * (1 + Real.log m) ^ 2 /
                completedConductorEnergy tiltedUnitSpline c m) * ((Q₁ : ℝ) ^ 2 / κ)) := by
        simp_rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        rw [← mul_sum, ← mul_sum, ← sum_mul]
        ring
      _ ≤ (K_vb ^ 2 * (65537 ^ 2 * L ^ (-879 / 512 : ℝ))) *
            ((65544 * L ^ (903 / 1024 : ℝ) / κ) * (L ^ (13 / 16 : ℝ) / κ)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hr_vb_sq (sq_nonneg _))
          (mul_le_mul hsm (div_le_div_of_nonneg_right hQ₁_sq hκ.le)
            (div_nonneg (sq_nonneg _) hκ.le) (by positivity))
          (mul_nonneg (sum_nonneg fun m hm => div_nonneg
            (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _)) (hE_nn m (mem_Icc.mp hm).1))
            (div_nonneg (sq_nonneg _) hκ.le))
          (by positivity)
      _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 *
            (L ^ (-879 / 512 : ℝ) * L ^ (903 / 1024 : ℝ) * L ^ (13 / 16 : ℝ)) := by ring
      _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 * L ^ (-23 / 1024 : ℝ) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
      _ ≤ (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 * L ^ (-(15 / 1024 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
          (by positivity)
      _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 / L ^ (15 / 1024 : ℝ) := by
        rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  calc
    _ ≤ (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 / L ^ (15 / 1024 : ℝ) +
          (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 / L ^ (15 / 1024 : ℝ) :=
      add_le_add hsum_hiL hsum_hiR
    _ = _ := by rw [hκ_def]; ring


private theorem rawCriticalRelativeSquare_eq_signed {c : ℝ} (hc : 1 ≤ c)
    {N m l : ℕ} (hhigh : c < (m : ℝ) ∨ c < (l : ℝ)) :
    rawCriticalRelativeSquare c N m l = signedCriticalRelativeSquare c N m l := by
  have hpolar : ¬(m = 1 ∧ l = 1) := by
    rintro ⟨rfl, rfl⟩
    norm_num only [Nat.cast_one] at hhigh
    exact hhigh.elim (not_lt_of_ge hc) (not_lt_of_ge hc)
  simp only [rawCriticalRelativeSquare, signedCriticalRelativeSquare,
    signedCriticalConductorResidual, if_neg hpolar, sub_zero, sq_abs]

/-- Pairs above overlap in the logarithmic packet have vanishing total relative square,
for every positive critical ratio. -/
theorem tendsto_sum_signedCriticalRelativeSquare_above_overlap {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      (∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
        ∑ l ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
          if c N < (m : ℝ) then signedCriticalRelativeSquare (c N) N m l else 0) +
      (∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
        ∑ l ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
          if c N < (l : ℝ) then signedCriticalRelativeSquare (c N) N m l else 0))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := exists_tiltedUnitSpline_bilinear_conductor_residual_variable_rate
  let C : ℝ := (K ^ 2 / tiltedSplineSpectralFloorConstant ^ 2) * 65537 ^ 2 * 262152
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => C / Real.log N ^ (15 / 1024 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 15 / 1024)).comp hlog)
  have h8 := criticalCurve_pow_log_div_natCast hc hR hcrit 0 8
  simp only [pow_zero, one_mul] at h8
  let P : ℝ := 4 * (Real.exp 1 + 3) ^ 2
  have hwidth := (criticalCurve_pow_log_div_natCast hc hR hcrit 2 0).const_mul P
  simp only [pow_zero, mul_one, mul_zero] at hwidth
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun N => add_nonneg
      (sum_nonneg fun m hm => sum_nonneg fun l hl => by
        split_ifs
        · exact signedCriticalRelativeSquare_nonneg (zero_lt_one.trans_le (hc N)) N
            (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
        · exact le_rfl)
      (sum_nonneg fun m hm => sum_nonneg fun l hl => by
        split_ifs
        · exact signedCriticalRelativeSquare_nonneg (zero_lt_one.trans_le (hc N)) N
            (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
        · exact le_rfl)
  filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop 1,
    eventually_criticalCurve_le_log_rpow hc hcrit (by norm_num : (1 / 8 : ℝ) < 129 / 1024),
    h8.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hwidth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hbound (13 / 32) (by norm_num) 128 (by norm_num)]
    with N hL1 hN hcL h8N hw hb
  change 1 ≤ Real.log (N : ℝ) at hL1
  let L : ℝ := Real.log N
  let Q : ℕ := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let r : ℝ := c N * (1 + Real.log (c N)) ^ 2 * L ^ (1 / (128 : ℕ) : ℝ) / L +
    c N ^ 5 * L / N
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL8N : L ^ 8 ≤ N := (div_le_one hN0).mp h8N.le
  have hwN : P * c N ^ 2 ≤ N := (div_le_one hN0).mp (by simpa only [← mul_div_assoc] using hw.le)
  have hQle : (Q : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (by positivity)
  have hQ1 : 1 ≤ Q := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow hL1 (by norm_num : (0 : ℝ) ≤ 13 / 32))
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hQleL : (Q : ℝ) ≤ L := hQle.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have h1Q : 1 + Real.log Q ≤ 1 + Real.log L :=
    add_le_add le_rfl (Real.log_le_log hQ0 hQleL)
  have hQsq : (Q : ℝ) ^ 2 ≤ L ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ (L ^ (13 / 32 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQle 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hQsq' : (Q : ℝ) ^ 2 ≤ L ^ (903 / 1024 : ℝ) :=
    hQsq.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hc7 : c N ^ 7 ≤ L ^ (903 / 1024 : ℝ) := by
    calc
      _ ≤ (L ^ (129 / 1024 : ℝ)) ^ 7 := pow_le_pow_left₀ (zero_le_one.trans (hc N)) hcL 7
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hlogLsq : (1 + Real.log L) ^ 2 ≤ 65536 * L ^ (1 / 128 : ℝ) := by
    calc
      _ ≤ (256 * L ^ (1 / 256 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hL1]) (one_add_log_le_rpow_256 hL1) 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 2, ← Real.rpow_mul hL0.le]
        norm_num
  have hQlogL : (Q : ℝ) ^ 2 * (1 + Real.log L) ^ 2 ≤ 65536 * L ^ (105 / 128 : ℝ) := by
    calc
      _ ≤ L ^ (13 / 16 : ℝ) * (65536 * L ^ (1 / 128 : ℝ)) :=
        mul_le_mul hQsq hlogLsq (sq_nonneg _) (by positivity)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hL0]
        norm_num
  have hQlogQ : (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤ 65536 * L ^ (903 / 1024 : ℝ) := by
    calc
      _ ≤ (Q : ℝ) ^ 2 * (1 + Real.log L) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (by linarith [Real.log_natCast_nonneg Q]) h1Q 2) (sq_nonneg _)
      _ ≤ 65536 * L ^ (105 / 128 : ℝ) := hQlogL
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) (by norm_num)
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr : r ≤ 65537 * L ^ (-879 / 1024 : ℝ) :=
    rate_vb_unrestricted_critical_le (hc N) hL1 hcL hL8N
  have hpt : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ L ^ (13 / 32 : ℝ) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ L ^ (13 / 32 : ℝ) →
      |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫| ≤
        K * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) * r := by
    intro m hm hmL l hl hlL
    exact hb m hm hmL l hl hlL (c N) (hc N) hwN
  have htotal := rawCriticalRelativeSquare_high_sum_le hK hL1 (hc N) hr0 hr hc7
    hQle h1Q hQsq hQsq' hQlogL hQlogQ hpt
  change _ ≤ C / L ^ (15 / 1024 : ℝ) at htotal
  convert htotal using 1
  congr 1
  · apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro l hl
    split_ifs with hhigh
    · exact (rawCriticalRelativeSquare_eq_signed (hc N) (Or.inl hhigh)).symm
    · rfl
  · apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro l hl
    split_ifs with hhigh
    · exact (rawCriticalRelativeSquare_eq_signed (hc N) (Or.inr hhigh)).symm
    · rfl

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_sum_signedCriticalRelativeSquare_above_overlap
