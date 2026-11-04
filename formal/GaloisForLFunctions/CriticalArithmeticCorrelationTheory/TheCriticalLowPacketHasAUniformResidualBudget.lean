import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSignedCriticalResidualIsCompactBelowOverlap

/-!
# A residual norm budget at every critical ratio

The first-power inverse-energy estimate leaves a strict logarithmic
exponent gap on the low packet. Every fixed positive critical ratio
therefore has the same eventual quarter-power norm budget.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticHodgeTheoryOfDegenerations
  SpacingScaleHarmonicAnalysis

/-- The low-packet inverse-energy residual mass is at most a quarter power of the horizon
logarithm at every fixed positive critical ratio. -/
theorem eventually_critical_low_packet_residual_budget {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (c N) m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 /
          completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        Real.log N ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK, hbudget⟩ := exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwidth := (criticalCurve_pow_log_div_natCast hc hR hcrit 2 0).const_mul
    (4 * (Real.exp 1 + 3) ^ 2)
  simp only [pow_zero, mul_one, mul_zero] at hwidth
  have hLN := criticalCurve_pow_log_div_natCast hc hR hcrit 0 8
  simp only [pow_zero, one_mul] at hLN
  filter_upwards [hbudget (13 / 32) (by norm_num) 128 (by norm_num),
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1,
    eventually_criticalCurve_le_log_rpow hc hcrit (by norm_num : (1 / 8 : ℝ) < 2 / 15),
    hwidth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hLN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlog.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (133 / 640 : ℝ) < 1 / 4) 5 (4 * K)),
    hlog.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (-46 / 15 : ℝ) < 1 / 4) 2 (4 * K))]
    with N hbudgetN hL1 hN hcα hwidthN hL8N hpoly₁ hpoly₂
  let L : ℝ := Real.log N
  let Q : ℕ := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let U : ℝ := 1 + Real.log L
  change 1 ≤ L at hL1
  change c N ≤ L ^ (2 / 15 : ℝ) at hcα
  change 4 * K * L ^ (133 / 640 : ℝ) * U ^ 5 ≤ L ^ (1 / 4 : ℝ) at hpoly₁
  change 4 * K * L ^ (-46 / 15 : ℝ) * U ^ 2 ≤ L ^ (1 / 4 : ℝ) at hpoly₂
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hU1 : 1 ≤ U := by dsimp only [U]; linarith [Real.log_nonneg hL1]
  have hU0 : 0 ≤ U := zero_le_one.trans hU1
  have hlarge : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N := by
    apply (div_le_one hN0).mp
    simpa only [mul_div_assoc] using hwidthN.le
  have hL8 : L ^ 8 ≤ N := (div_le_one hN0).mp hL8N.le
  have hcL : c N ≤ L := hcα.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (2 / 15 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hc2 : c N ^ 2 ≤ L ^ (4 / 15 : ℝ) := by
    calc
      _ ≤ (L ^ (2 / 15 : ℝ)) ^ 2 := pow_le_pow_left₀ hc0.le hcα 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hc7 : c N ^ 7 ≤ L ^ (14 / 15 : ℝ) := by
    calc
      _ ≤ (L ^ (2 / 15 : ℝ)) ^ 7 := pow_le_pow_left₀ hc0.le hcα 7
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hQpow : (Q : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
  have hQ1 : 1 ≤ Q := Nat.le_floor (by
    exact_mod_cast (Real.one_le_rpow hL1 (by norm_num : (0 : ℝ) ≤ 13 / 32)))
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hQL : (Q : ℝ) ≤ L := hQpow.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hQ2 : (Q : ℝ) ^ 2 ≤ L ^ (14 / 15 : ℝ) := by
    calc
      _ ≤ (L ^ (13 / 32 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQpow 2
      _ = L ^ (13 / 16 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hlogQ : (1 + Real.log Q) ^ 2 ≤ U ^ 2 :=
    pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg Q])
      (add_le_add le_rfl (Real.log_le_log hQ0 hQL)) 2
  have hlogc : (1 + Real.log (c N)) ^ 3 ≤ U ^ 3 :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg (hc N)])
      (add_le_add le_rfl (Real.log_le_log hc0 hcL)) 3
  have hW : c N ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤
      2 * L ^ (14 / 15 : ℝ) * U ^ 2 := by
    have ha : c N ^ 7 ≤ L ^ (14 / 15 : ℝ) * U ^ 2 := hc7.trans
      (le_mul_of_one_le_right (Real.rpow_nonneg hL0.le _) (one_le_pow₀ hU1))
    have hb := mul_le_mul hQ2 hlogQ (sq_nonneg _) (Real.rpow_nonneg hL0.le _)
    linarith only [ha, hb]
  have hratio : L / (N : ℝ) ≤ 1 / L ^ 7 := by
    rw [div_le_div_iff₀ hN0 (pow_pos hL0 7), one_mul]
    calc
      L * L ^ 7 = L ^ 8 := by ring
      _ ≤ _ := hL8
  have hr₂ : c N ^ 10 * (L / N) ^ 2 ≤ 1 / L ^ 4 := by
    calc
      _ ≤ L ^ 10 * (1 / L ^ 7) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hc0.le hcL 10)
          (pow_le_pow_left₀ (div_nonneg hL0.le hN0.le) hratio 2)
          (sq_nonneg _) (pow_nonneg hL0.le _)
      _ = _ := by field_simp [hL0.ne']
  have hr₁ : c N ^ 2 * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 128 : ℝ) / L ≤
      L ^ (4 / 15 : ℝ) * U ^ 3 * L ^ (1 / 128 : ℝ) / L :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hc2 hlogc (pow_nonneg (by linarith [Real.log_nonneg (hc N)]) 3)
          (Real.rpow_nonneg hL0.le _))
        (Real.rpow_nonneg hL0.le _)) hL0.le
  have hfirst : K * (c N ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) *
      (c N ^ 2 * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 128 : ℝ) / L) ≤
        (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ K * (2 * L ^ (14 / 15 : ℝ) * U ^ 2) *
          (L ^ (4 / 15 : ℝ) * U ^ 3 * L ^ (1 / 128 : ℝ) / L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hW hK.le) hr₁
          (by have := Real.log_nonneg (hc N); positivity) (by positivity)
      _ = 2 * K * (L ^ (14 / 15 : ℝ) * L ^ (4 / 15 : ℝ) *
          L ^ (1 / 128 : ℝ) * L⁻¹) * U ^ 5 := by ring
      _ = 2 * K * L ^ (133 / 640 : ℝ) * U ^ 5 := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
          ← Real.rpow_add hL0]
        norm_num
      _ ≤ _ := by linarith only [hpoly₁]
  have hsecond : K * (c N ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) *
      (c N ^ 10 * (L / N) ^ 2) ≤ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ K * (2 * L ^ (14 / 15 : ℝ) * U ^ 2) * (1 / L ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hW hK.le) hr₂ (by positivity) (by positivity)
      _ = 2 * K * (L ^ (14 / 15 : ℝ) / L ^ (4 : ℝ)) * U ^ 2 := by
        have hfour : L ^ (4 : ℝ) = L ^ (4 : ℕ) := by
          simpa only [Nat.cast_ofNat] using Real.rpow_natCast L 4
        rw [hfour]
        ring
      _ = 2 * K * L ^ (-46 / 15 : ℝ) * U ^ 2 := by
        rw [← Real.rpow_sub hL0]
        norm_num
      _ ≤ _ := by linarith only [hpoly₂]
  have hb := hbudgetN (c N) (hc N) hlarge Q hQpow
  change (∑ m ∈ Icc 1 Q, _) ≤ L ^ (1 / 4 : ℝ)
  calc
    _ ≤ K * (c N ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) *
        (c N ^ 2 * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 128 : ℝ) / L +
          c N ^ 10 * (L / N) ^ 2) := hb
    _ ≤ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) + (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
      rw [mul_add]
      exact add_le_add hfirst hsecond
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_critical_low_packet_residual_budget
