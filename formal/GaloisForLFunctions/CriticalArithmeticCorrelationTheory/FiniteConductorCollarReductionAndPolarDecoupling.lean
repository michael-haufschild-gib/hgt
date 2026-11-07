import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrefixCollarSchurObstructionAndFarDecoupling
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLowPacketPaymentAtEveryRatioIsTheRiemannHypothesis

/-!
# Finite-Conductor Collar Reduction and Complete Prefix–Collar Resolution

At any bounded critical ratio `1 ≤ c`, `c⁸ ≤ R_max log N` (`R_max > 0`), the low-conductor
operator residual
`r_m = B_{c,N} v_m - E_m(c) v_m`
satisfies `topCollarDualSeventhMass M N r_m / E_m(c) = O((c⁹ / log N) m⁻⁵)` for `m ≤ c` and decays in
`N` for `c < m`. Consequently, cutting off a finite conductor prefix `1 ≤ m ≤ m₀` (depending only on
`(R_max, ε)`, not on `N` or `c`) makes the remaining low-packet operator-residual coupling against
every collar vector `y` arbitrarily small (`exists_finite_conductor_cutoff_collar_dualSeventh_below_ratio`,
`exists_above_cutoff_subquarter_packet_collar_schur_below_ratio`).

Combined with the `4 / 13` physical-tearing obstruction on `(conductorSubspace Q₁ N)ᗮ`, the
conductor-adapted `o(1)` Schur decoupling on `(conductorSubspace R₁ N)ᗮ`
(`PrefixCollarSchurObstructionAndFarDecoupling`), and the sharp `m = 1` polar capacity law
(`tendsto_optimized_terminal_window_energy`, `polarPaymentAt_of_eventually_nonneg`),
`complete_prefix_and_low_packet_collar_resolution` gives the complete two-sided resolution at any
fixed critical ratio `c_N⁸ / log N → R > 0`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CompletedArithmeticForms
  ArithmeticElectrostatics ArithmeticHodgeTheoryOfDegenerations CohomologyOfWindowsOfSpecZ
  WindowTowerOfSpecZ

/-- The operator residual `B_{c,N} v_m - E_m(c) v_m` of the `m`-th normalized Ramanujan horizon
mode under `completeWeilMatrix tiltedUnitSpline c N`. -/
def conductorResidualVector (c : ℝ) (m N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N

/-- Strict positivity `0 < completedConductorEnergy tiltedUnitSpline c m` for all `c > 0`, `m ≥ 1`. -/
theorem completedConductorEnergy_tilted_pos {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m) :
    0 < completedConductorEnergy tiltedUnitSpline c m := by
  have hκ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hmc : (m : ℝ) ≤ c
  · exact (mul_pos hκ (pow_pos (div_pos hm0 hc) 7)).trans_le
      (completedConductorEnergy_tilted_ge_low hc hm hmc)
  · exact hκ.trans_le
      (tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc hm (le_of_not_ge hmc))

private theorem critical_collar_side_bounds {N : ℕ} {c R₀ L : ℝ}
    (hL_def : L = Real.log (N : ℝ)) (hR₀1 : 1 ≤ R₀) (hc1 : 1 ≤ c)
    (hc_R₀ : c ≤ R₀ * L ^ (1 / 8 : ℝ)) (hR₀_L : R₀ ≤ L ^ (1 / 8 : ℝ))
    (hL2048 : 2048 ≤ L) (hL8N : L ^ (8 : ℕ) ≤ N) :
    c ≤ L ∧
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ N ∧
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N ∧
      c ^ 4 ≤ N ∧
      2 * linearPrimeStrip c ≤ N / linearDefectCutoff c ∧
      c ^ 2 / Real.log (N : ℝ) + c ^ 3 * Real.log (N : ℝ) / N +
        c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤ 3 * c ^ 2 / L := by
  have hL1 : 1 ≤ L := by linarith only [hL2048]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := (one_le_pow₀ hL1).trans hL8N
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc_L4 : c ≤ L ^ (1 / 4 : ℝ) := by
    calc c ≤ R₀ * L ^ (1 / 8 : ℝ) := hc_R₀
      _ ≤ L ^ (1 / 8 : ℝ) * L ^ (1 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_right hR₀_L (Real.rpow_nonneg hL0.le _)
      _ = L ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have hc_le_L : c ≤ L :=
    hc_L4.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hc2_L : c ^ 2 ≤ L := by
    calc c ^ 2 ≤ (L ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hc0.le hc_L4 2
      _ = L ^ (1 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
      _ ≤ L := (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L)
  have hc4_L : c ^ 4 ≤ L := by
    calc c ^ 4 ≤ (L ^ (1 / 4 : ℝ)) ^ 4 := pow_le_pow_left₀ hc0.le hc_L4 4
      _ = L := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num [Real.rpow_one]
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 1 ≤ 2.8 := by have := Real.exp_one_lt_d9; linarith
    have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h1, hp, Real.exp_pos 1]
  have hL6 : (2048 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL2048 6
  have hL8_split : L ^ 2 * L ^ 6 = L ^ (8 : ℕ) := by ring
  have hlarge : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ N := by
    have h1 : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
    have h2 : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ 144 * L :=
      (mul_le_mul h1 hc2_L (sq_nonneg _) (by norm_num)).trans_eq (by ring)
    have h3 : (144 : ℝ) * L ≤ L ^ 2 * L ^ 6 := by
      have : (144 : ℝ) ≤ L * L ^ 6 := by nlinarith only [hL6, hL1]
      nlinarith only [this, hL0]
    exact h2.trans ((h3.trans_eq hL8_split).trans hL8N)
  have hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N := by
    have hR : linearNearRowRadius c + 1 ≤ 17 * c := by
      unfold linearNearRowRadius; nlinarith only [hc1, he2]
    have hsq := pow_le_pow_left₀ (by unfold linearNearRowRadius; positivity) hR 2
    have h1 : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ 1156 * L := by
      nlinarith only [hsq, hc2_L, (by ring : 4 * (17 * c) ^ 2 = 1156 * c ^ 2)]
    have h2 : (1156 : ℝ) * L ≤ L ^ 2 * L ^ 6 := by
      have : (1156 : ℝ) ≤ L * L ^ 6 := by nlinarith only [hL6, hL1]
      nlinarith only [this, hL0]
    exact h1.trans ((h2.trans_eq hL8_split).trans hL8N)
  have hc4N : c ^ 4 ≤ N :=
    hc4_L.trans ((pow_one L).symm.trans_le ((pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 8)).trans hL8N))
  have h2BM : 2 * linearPrimeStrip c ≤ N / linearDefectCutoff c := by
    obtain ⟨hLc3, _, -, hLcup⟩ := linearDefectCutoff_bounds hc1
    refine (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr ?_
    have hB : (linearPrimeStrip c : ℝ) ≤ 4 * L := by
      have hb := linearPrimeStrip_le hc1
      nlinarith only [hb, he1, hc_le_L]
    have hLc : (linearDefectCutoff c : ℝ) ≤ 2052 * L := by
      nlinarith only [hLcup, he2, hc_le_L]
    have hprod : ((2 * linearPrimeStrip c * linearDefectCutoff c : ℕ) : ℝ) ≤ N := by
      push_cast
      have hp : (2 * (linearPrimeStrip c : ℝ)) * linearDefectCutoff c ≤ (8 * L) * (2052 * L) :=
        mul_le_mul (by linarith only [hB]) hLc (Nat.cast_nonneg _) (by positivity)
      have hhi : (8 * L) * (2052 * L) ≤ L ^ 2 * L ^ 6 := by
        have : (16416 : ℝ) ≤ L ^ 6 := by linarith only [hL6]
        nlinarith only [this, sq_nonneg L]
      exact hp.trans ((hhi.trans_eq hL8_split).trans hL8N)
    exact_mod_cast hprod
  have hrate : c ^ 2 / Real.log (N : ℝ) + c ^ 3 * Real.log (N : ℝ) / N +
      c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤ 3 * c ^ 2 / L := by
    rw [← hL_def]
    have ht1 : c ^ 3 * L / N ≤ c ^ 2 / L := by
      rw [div_le_div_iff₀ hN0 hL0]
      have hcLN : c * L ^ 2 ≤ N := by
        calc c * L ^ 2 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hc_le_L (sq_nonneg _)
          _ ≤ L ^ (8 : ℕ) := (by ring : L * L ^ 2 = L ^ 3).trans_le (pow_le_pow_right₀ hL1 (by norm_num))
          _ ≤ N := hL8N
      have hm := mul_le_mul_of_nonneg_left hcLN (sq_nonneg c)
      linarith only [hm, (by ring : c ^ 3 * L * L = c ^ 2 * (c * L ^ 2))]
    have ht2 : c ^ 10 * (L / N) ^ 2 ≤ c ^ 2 / L := by
      rw [div_pow, mul_div_assoc', div_le_div_iff₀ (sq_pos_of_pos hN0) hL0]
      have hc8N : c ^ 8 * L ^ 3 ≤ (N : ℝ) ^ 2 := by
        have hc8 : c ^ 8 ≤ L ^ 2 := (pow_le_pow_left₀ hc0.le hc4_L 2).trans_eq' (by ring)
        calc c ^ 8 * L ^ 3 ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_right hc8 (by positivity)
          _ ≤ L ^ (8 : ℕ) := (by ring : L ^ 2 * L ^ 3 = L ^ 5).trans_le (pow_le_pow_right₀ hL1 (by norm_num))
          _ ≤ N := hL8N
          _ ≤ (N : ℝ) ^ 2 := le_self_pow₀ (by exact_mod_cast hN1) (by decide)
      have hm := mul_le_mul_of_nonneg_left hc8N (sq_nonneg c)
      linarith only [hm, (by ring : c ^ 10 * L ^ 2 * L = c ^ 2 * (c ^ 8 * L ^ 3))]
    linarith only [ht1, ht2, (by ring : 3 * c ^ 2 / L = 3 * (c ^ 2 / L))]
  exact ⟨hc_le_L, hlarge, hradN, hc4N, h2BM, hrate⟩

private theorem above_cutoff_low_range_dualSeventh_sum_le {m₀ Q M N : ℕ} {c R_max K_d7 L : ℝ}
    (hm₀ : 1 ≤ m₀) (hc1 : 1 ≤ c) (hL1 : 1 ≤ L) (hR : 0 < R_max) (hKd7 : 0 < K_d7)
    (hc8 : c ^ 8 ≤ R_max * L)
    (hd7 : ∀ m ∈ Ioc m₀ Q, (m : ℝ) ≤ c →
      topCollarDualSeventhMass M N (conductorResidualVector c m N) ≤
        K_d7 * (m : ℝ) ^ 2 * (3 * c ^ 2 / L)) :
    (1 / c) * (∑ m ∈ Ioc m₀ Q,
      if (m : ℝ) ≤ c then
        topCollarDualSeventhMass M N (conductorResidualVector c m N) /
          completedConductorEnergy tiltedUnitSpline c m
      else 0) ≤
      (3 * K_d7 * R_max / tiltedSplineSpectralFloorConstant) / (m₀ : ℝ) ^ 4 := by
  set κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hm₀0 : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  have hc8_div : c ^ 8 / L ≤ R_max := (div_le_iff₀ hL0).mpr hc8
  have hterm : ∀ m ∈ Ioc m₀ Q,
      (if (m : ℝ) ≤ c then
        topCollarDualSeventhMass M N (conductorResidualVector c m N) /
          completedConductorEnergy tiltedUnitSpline c m
      else 0) ≤
        (3 * K_d7 * R_max / κ) * c / (m₀ : ℝ) ^ 3 * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    split_ifs with hmc
    · have hm_gt : m₀ < m := (mem_Ioc.mp hm).1
      have hm1 : 1 ≤ m := by omega
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hm₀_le : (m₀ : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 :=
        pow_le_pow_left₀ hm₀0.le (by exact_mod_cast hm_gt.le) 3
      have hEm : κ * ((m : ℝ) / c) ^ 7 ≤ completedConductorEnergy tiltedUnitSpline c m :=
        completedConductorEnergy_tilted_ge_low hc0 hm1 hmc
      have hEpos := completedConductorEnergy_tilted_pos hc0 hm1
      calc topCollarDualSeventhMass M N (conductorResidualVector c m N) /
              completedConductorEnergy tiltedUnitSpline c m
          ≤ (K_d7 * (m : ℝ) ^ 2 * (3 * c ^ 2 / L)) / (κ * ((m : ℝ) / c) ^ 7) :=
            (div_le_div_of_nonneg_right (hd7 m hm hmc) hEpos.le).trans
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hEm)
        _ = (3 * K_d7 / κ) * (c ^ 8 / L) * c * (1 / (m : ℝ) ^ 3) * (1 / (m : ℝ) ^ 2) := by
            field_simp [hκ.ne', hc0.ne', hL0.ne', hm0.ne']; ring
        _ ≤ (3 * K_d7 / κ) * R_max * c * (1 / (m₀ : ℝ) ^ 3) * (1 / (m : ℝ) ^ 2) := by
            have h1 : (3 * K_d7 / κ) * (c ^ 8 / L) ≤ (3 * K_d7 / κ) * R_max :=
              mul_le_mul_of_nonneg_left hc8_div (by positivity)
            have h2 : 1 / (m : ℝ) ^ 3 ≤ 1 / (m₀ : ℝ) ^ 3 :=
              one_div_le_one_div_of_le (by positivity) hm₀_le
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul (mul_le_mul_of_nonneg_right h1 hc0.le) h2 (by positivity) (by positivity))
              (by positivity)
        _ = (3 * K_d7 * R_max / κ) * c / (m₀ : ℝ) ^ 3 * (1 / (m : ℝ) ^ 2) := by ring
    · positivity
  calc (1 / c) * (∑ m ∈ Ioc m₀ Q, _)
      ≤ (1 / c) * ∑ m ∈ Ioc m₀ Q,
          (3 * K_d7 * R_max / κ) * c / (m₀ : ℝ) ^ 3 * (1 / (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = ((3 * K_d7 * R_max / κ) / (m₀ : ℝ) ^ 3) * ∑ m ∈ Ioc m₀ Q, 1 / (m : ℝ) ^ 2 := by
        rw [← mul_sum]; field_simp [hc0.ne', hm₀0.ne']
    _ ≤ ((3 * K_d7 * R_max / κ) / (m₀ : ℝ) ^ 3) * (1 / (m₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le hm₀) (by positivity)
    _ = (3 * K_d7 * R_max / κ) / (m₀ : ℝ) ^ 4 := by field_simp [hm₀0.ne']; ring

/-- **Finite-conductor reduction of dual seventh-power collar residuals at any critical ratio.**
For every `R_max > 0` and `ε > 0`, there exists a finite conductor cutoff `m₀ ≥ 1` (independent of
`N` and `c`) such that eventually in `N`, across all `1 ≤ c` with `c⁸ ≤ R_max log N` and all collar
boundaries `M` with `2 · linearPrimeStrip c ≤ M` (including `M = N / linearDefectCutoff c`):
1. `(c⁷ / log N) · ∑_{m ∈ Ioc m₀ (lowPacketCutoff N)} D₇(r_m) / E_m(c) ≤ ε`;
2. `(1 / c) · ∑_{m ∈ Ioc m₀ ⌊(log N)^{1/4}⌋₊} D₇(r_m) / E_m(c) ≤ ε`. -/
theorem exists_finite_conductor_cutoff_collar_dualSeventh_below_ratio
    {R_max : ℝ} (hR : 0 < R_max) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
        2 * linearPrimeStrip c ≤ N / linearDefectCutoff c ∧
          ∀ {M : ℕ}, 2 * linearPrimeStrip c ≤ M →
            (c ^ 7 / Real.log (N : ℝ)) *
                (∑ m ∈ Ioc m₀ (lowPacketCutoff N),
                  topCollarDualSeventhMass M N (conductorResidualVector c m N) /
                    completedConductorEnergy tiltedUnitSpline c m) ≤ ε ∧
              (1 / c) *
                (∑ m ∈ Ioc m₀ ⌊Real.log (N : ℝ) ^ (1 / 4 : ℝ)⌋₊,
                  topCollarDualSeventhMass M N (conductorResidualVector c m N) /
                    completedConductorEnergy tiltedUnitSpline c m) ≤ ε := by
  set κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  obtain ⟨K_d7, hKd7, hd7_lf⟩ := exists_completeWeil_dualSeventh_conductor_residual_log_free
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨K_vq, hKvq, hq_var⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  set R₀ : ℝ := max 1 R_max
  have hR₀1 : 1 ≤ R₀ := le_max_left _ _
  have hR₀0 : 0 < R₀ := zero_lt_one.trans_le hR₀1
  have hR_le : R_max ≤ R₀ := le_max_right _ _
  set m₀ : ℕ := max 1 ⌈(6 * K_d7 * R₀ ^ 2 / κ + 1) / ε⌉₊
  have hm₀1 : 1 ≤ m₀ := le_max_left _ _
  have hm₀_ge : (6 * K_d7 * R₀ ^ 2 / κ + 1) / ε ≤ m₀ :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  refine ⟨m₀, hm₀1, ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL_sub_N : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ (8 : ℕ) ≤ N := by
    have hsm := tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound zero_lt_one)
    filter_upwards [hsm, eventually_ge_atTop 3] with N hN hN3
    have hN0 : (0 : ℝ) < N := by positivity
    have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have h1 : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) :=
      (le_abs_self _).trans (by
        simpa only [Function.comp_def, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] using hN)
    exact (pow_le_pow_left₀ hL0 h1 8).trans_eq
      (by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num)
  set C_hi1 : ℝ := (K_vq / κ) * R₀ ^ 9 * 66049 * (257 ^ 3 + 1)
  set C_hi2 : ℝ := 3 * K_d7 * R₀ / κ
  filter_upwards [hq_var (13 / 32) (by norm_num) 128 (by norm_num),
    hL_sub_N, hloglim.eventually_ge_atTop 2048,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hloglim).eventually_ge_atTop
      (R₀ + 2 * C_hi2 / ε + 1),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp hloglim).eventually_ge_atTop
      (2 * C_hi1 / ε + 1)]
    with N hqN hL8N hL2048 hL_18 hL_32 c hc1 hc8
  dsimp only [Function.comp_def] at hL_18 hL_32
  set L := Real.log (N : ℝ)
  have hL1 : 1 ≤ L := by linarith only [hL2048]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hChi1_0 : 0 ≤ C_hi1 := by dsimp only [C_hi1]; positivity
  have hChi2_0 : 0 ≤ C_hi2 := by dsimp only [C_hi2]; positivity
  have hR₀_L : R₀ ≤ L ^ (1 / 8 : ℝ) := by
    have : 0 ≤ 2 * C_hi2 / ε := by positivity
    linarith only [hL_18, this]
  have hc_R₀ : c ≤ R₀ * L ^ (1 / 8 : ℝ) := by
    have hc8' : c ^ 8 ≤ R₀ ^ 8 * L :=
      hc8.trans (mul_le_mul_of_nonneg_right (hR_le.trans (le_self_pow₀ hR₀1 (by norm_num))) hL0.le)
    have hr := Real.rpow_le_rpow (pow_nonneg hc0.le 8) hc8' (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hlhs : (c ^ 8) ^ (1 / 8 : ℝ) = c := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_one]
    have hrhs : (R₀ ^ 8 * L) ^ (1 / 8 : ℝ) = R₀ * L ^ (1 / 8 : ℝ) := by
      rw [Real.mul_rpow (by positivity) hL0.le, ← Real.rpow_natCast R₀ 8,
        ← Real.rpow_mul hR₀0.le]
      norm_num [Real.rpow_one]
    rwa [hlhs, hrhs] at hr
  obtain ⟨hc_le_L, hlarge, hradN, hc4N, h2BM_def, hrate_d7⟩ :=
    critical_collar_side_bounds rfl hR₀1 hc1 hc_R₀ hR₀_L hL2048 hL8N
  refine ⟨h2BM_def, fun {M} h2BM => ?_⟩
  have hd7_pt : ∀ m : ℕ, 0 < m →
      topCollarDualSeventhMass M N (conductorResidualVector c m N) ≤
        K_d7 * (m : ℝ) ^ 2 * (3 * c ^ 2 / L) := fun m hm0 =>
    (hd7_lf hm0 hc1 hL1 hlarge hradN hc4N h2BM).trans
      (mul_le_mul_of_nonneg_left hrate_d7 (by positivity))
  have hm₀4_ge : (6 * K_d7 * R₀ ^ 2 / κ + 1) / ε ≤ (m₀ : ℝ) ^ 4 :=
    hm₀_ge.trans (le_self_pow₀ (by exact_mod_cast hm₀1) (by norm_num))
  have hlow_eps : (3 * K_d7 * R₀ ^ 2 / κ) / (m₀ : ℝ) ^ 4 ≤ ε / 2 := by
    have hm₀4_pos : 0 < (m₀ : ℝ) ^ 4 := by positivity
    rw [div_le_iff₀ hm₀4_pos]
    have hm := mul_le_mul_of_nonneg_left hm₀4_ge hε.le
    have heq : ε * ((6 * K_d7 * R₀ ^ 2 / κ + 1) / ε) = 6 * K_d7 * R₀ ^ 2 / κ + 1 :=
      mul_div_cancel₀ _ hε.ne'
    linarith only [hm, heq, hε]
  refine ⟨?_, ?_⟩
  · -- Part 1: Full low packet `Ioc m₀ (lowPacketCutoff N)` with `(c^7 / L)` weight
    set Q₁ := lowPacketCutoff N
    have hlow1 : (c ^ 7 / L) * (∑ m ∈ Ioc m₀ Q₁,
        if (m : ℝ) ≤ c then
          topCollarDualSeventhMass M N (conductorResidualVector c m N) /
            completedConductorEnergy tiltedUnitSpline c m
        else 0) ≤ ε / 2 := by
      have hbase := above_cutoff_low_range_dualSeventh_sum_le hm₀1 hc1 hL1 hR₀0 hKd7
        (hc8.trans (mul_le_mul_of_nonneg_right hR_le hL0.le))
        (fun m hm _ => hd7_pt m (lt_of_le_of_lt hm₀1 (mem_Ioc.mp hm).1))
      have hc8_R₀ : c ^ 8 / L ≤ R₀ := ((div_le_iff₀ hL0).mpr hc8).trans hR_le
      have hid : (c ^ 7 / L) = (c ^ 8 / L) * (1 / c) := by field_simp [hc0.ne', hL0.ne']
      rw [hid, mul_assoc]
      calc (c ^ 8 / L) * ((1 / c) * ∑ m ∈ Ioc m₀ Q₁, _)
          ≤ R₀ * ((3 * K_d7 * R₀ / κ) / (m₀ : ℝ) ^ 4) :=
            mul_le_mul hc8_R₀ hbase (mul_nonneg (by positivity)
              (sum_nonneg fun m _ => by
                split_ifs with h
                · exact div_nonneg (topCollarDualSeventhMass_nonneg _ _ _)
                    (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
                      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0
                      (by omega))
                · exact le_rfl)) hR₀0.le
        _ = (3 * K_d7 * R₀ ^ 2 / κ) / (m₀ : ℝ) ^ 4 := by ring
        _ ≤ ε / 2 := hlow_eps
    have h1_logL_256 : 1 + Real.log L ≤ 257 * L ^ (1 / 256 : ℝ) := by
      have hlg := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hL0 (1 / 256 : ℝ))
      rw [Real.log_rpow hL0] at hlg
      have h1 : 1 ≤ L ^ (1 / 256 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith only [hlg, h1]
    have hQ₁_le : (Q₁ : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have hr_q : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (128 : ℕ) : ℝ) / L +
        c ^ 10 * (L / N) ^ 2 ≤ (257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ) := by
      have hc2 : c ^ 2 ≤ R₀ ^ 2 * L ^ (1 / 4 : ℝ) := by
        calc c ^ 2 ≤ (R₀ * L ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hc0.le hc_R₀ 2
          _ = R₀ ^ 2 * L ^ (1 / 4 : ℝ) := by
              rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hL0.le]
              norm_num
      have hlogc3 : (1 + Real.log c) ^ 3 ≤ 257 ^ 3 * L ^ (3 / 256 : ℝ) := by
        have hlc : 1 + Real.log c ≤ 257 * L ^ (1 / 256 : ℝ) :=
          (add_le_add_right (Real.log_le_log hc0 hc_le_L) 1).trans h1_logL_256
        calc (1 + Real.log c) ^ 3 ≤ (257 * L ^ (1 / 256 : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) hlc 3
          _ = 257 ^ 3 * L ^ (3 / 256 : ℝ) := by
              rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 3, ← Real.rpow_mul hL0.le]
              norm_num
      have ht1 : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (128 : ℕ) : ℝ) / L ≤
          257 ^ 3 * R₀ ^ 2 * L ^ (-187 / 256 : ℝ) := by
        calc c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (128 : ℕ) : ℝ) / L
            ≤ (R₀ ^ 2 * L ^ (1 / 4 : ℝ)) * (257 ^ 3 * L ^ (3 / 256 : ℝ)) *
                L ^ (1 / 128 : ℝ) * L ^ (-1 : ℝ) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg_one L, show (1 / (128 : ℕ) : ℝ) = 1 / 128 by norm_num]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul hc2 hlogc3 (by positivity) (by positivity)) (by positivity))
                (by positivity)
          _ = 257 ^ 3 * R₀ ^ 2 *
                (L ^ (1 / 4 : ℝ) * L ^ (3 / 256 : ℝ) * L ^ (1 / 128 : ℝ) * L ^ (-1 : ℝ)) := by ring
          _ = 257 ^ 3 * R₀ ^ 2 * L ^ (-187 / 256 : ℝ) := by
              rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
      have ht2 : c ^ 10 * (L / N) ^ 2 ≤ R₀ ^ 2 * L ^ (-187 / 256 : ℝ) := by
        have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (pow_pos hL0 8) hL8N
        have hc10 : c ^ 10 * L ^ 2 ≤ L ^ 12 := by
          have : c ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ hc0.le hc_le_L 10
          exact (mul_le_mul_of_nonneg_right this (sq_nonneg L)).trans_eq (by ring)
        have hN2 : L ^ 16 ≤ (N : ℝ) ^ 2 :=
          (pow_le_pow_left₀ (by positivity) hL8N 2).trans_eq' (by ring)
        have hdiv : c ^ 10 * (L / N) ^ 2 ≤ L ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, inv_eq_one_div, div_pow, mul_div_assoc',
            div_le_div_iff₀ (sq_pos_of_pos hN0) hL0]
          have h13_16 : L ^ 13 ≤ L ^ 16 := pow_le_pow_right₀ hL1 (by norm_num)
          nlinarith only [hc10, hN2, h13_16, hL0, (by ring : L ^ 12 * L = L ^ 13)]
        calc c ^ 10 * (L / N) ^ 2 ≤ L ^ (-1 : ℝ) := hdiv
          _ ≤ L ^ (-187 / 256 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          _ ≤ R₀ ^ 2 * L ^ (-187 / 256 : ℝ) :=
              le_mul_of_one_le_left (by positivity) (one_le_pow₀ hR₀1)
      linarith only [ht1, ht2, (by ring : (257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ) =
        257 ^ 3 * R₀ ^ 2 * L ^ (-187 / 256 : ℝ) + R₀ ^ 2 * L ^ (-187 / 256 : ℝ))]
    have hhi1 : (c ^ 7 / L) * (∑ m ∈ Ioc m₀ Q₁,
        if c < (m : ℝ) then
          topCollarDualSeventhMass M N (conductorResidualVector c m N) /
            completedConductorEnergy tiltedUnitSpline c m
        else 0) ≤ ε / 2 := by
      have hpt : ∀ m ∈ Ioc m₀ Q₁,
          (if c < (m : ℝ) then
            topCollarDualSeventhMass M N (conductorResidualVector c m N) /
              completedConductorEnergy tiltedUnitSpline c m
          else 0) ≤
            (K_vq / κ) * ((Q₁ : ℝ) * (257 * L ^ (1 / 256 : ℝ)) ^ 2) *
              ((257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ)) := by
        intro m hm
        split_ifs with hmc
        · obtain ⟨hm_gt, hmQ⟩ := mem_Ioc.mp hm
          have hm1 : 1 ≤ m := by omega
          have hmQ' : (m : ℝ) ≤ Q₁ := by exact_mod_cast hmQ
          have hm_L : (m : ℝ) ≤ L :=
            (hmQ'.trans hQ₁_le).trans
              ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
          have hEm : κ ≤ completedConductorEnergy tiltedUnitSpline c m :=
            tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm1 hmc.le
          have hEpos := completedConductorEnergy_tilted_pos hc0 hm1
          have hqm := (topCollarDualSeventhMass_le_norm_sq M N _).trans
            ((hqN m hm1 (hmQ'.trans hQ₁_le) c hc1 hlarge).trans
              (mul_le_mul_of_nonneg_left hr_q (by
                have : 0 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
                positivity)))
          have hm_log : (m : ℝ) * (1 + Real.log m) ^ 2 ≤
              (Q₁ : ℝ) * (257 * L ^ (1 / 256 : ℝ)) ^ 2 :=
            mul_le_mul hmQ'
              (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg m])
                ((add_le_add_right (Real.log_le_log (by exact_mod_cast hm1) hm_L) 1).trans
                  h1_logL_256) 2)
              (sq_nonneg _) (Nat.cast_nonneg _)
          calc topCollarDualSeventhMass M N (conductorResidualVector c m N) /
                  completedConductorEnergy tiltedUnitSpline c m
              ≤ (K_vq * ((m : ℝ) * (1 + Real.log m) ^ 2) *
                  ((257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ))) / κ :=
                (div_le_div_of_nonneg_right hqm hEpos.le).trans
                  (div_le_div_of_nonneg_left (by
                    have : 0 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
                    positivity) hκ hEm)
            _ ≤ (K_vq / κ) * ((Q₁ : ℝ) * (257 * L ^ (1 / 256 : ℝ)) ^ 2) *
                  ((257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ)) := by
                have hm2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_log hKvq.le)
                  (by positivity : 0 ≤ (257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ))
                exact (div_le_div_of_nonneg_right hm2 hκ.le).trans_eq (by ring)
        · positivity
      have hc7_div : c ^ 7 / L ≤ R₀ ^ 7 * L ^ (-1 / 8 : ℝ) := by
        calc c ^ 7 / L ≤ (R₀ * L ^ (1 / 8 : ℝ)) ^ 7 * L ^ (-1 : ℝ) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg_one L]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le hc_R₀ 7) (by positivity)
          _ = R₀ ^ 7 * L ^ (-1 / 8 : ℝ) := by
              rw [mul_pow, mul_assoc, ← Real.rpow_natCast (L ^ (1 / 8 : ℝ)) 7,
                ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
              norm_num
      have hcard : ((Ioc m₀ Q₁).card : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
        rw [Nat.card_Ioc]
        exact (by exact_mod_cast Nat.sub_le Q₁ m₀ : ((Q₁ - m₀ : ℕ) : ℝ) ≤ Q₁).trans hQ₁_le
      calc (c ^ 7 / L) * ∑ m ∈ Ioc m₀ Q₁, _
          ≤ (c ^ 7 / L) * ∑ _m ∈ Ioc m₀ Q₁,
              (K_vq / κ) * ((Q₁ : ℝ) * (257 * L ^ (1 / 256 : ℝ)) ^ 2) *
                ((257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_le_sum hpt) (by positivity)
        _ ≤ (R₀ ^ 7 * L ^ (-1 / 8 : ℝ)) *
              (L ^ (13 / 32 : ℝ) * ((K_vq / κ) * (L ^ (13 / 32 : ℝ) *
                (66049 * L ^ (1 / 128 : ℝ))) *
                ((257 ^ 3 + 1) * R₀ ^ 2 * L ^ (-187 / 256 : ℝ)))) := by
            rw [sum_const, nsmul_eq_mul]
            have h257 : (257 * L ^ (1 / 256 : ℝ)) ^ 2 = 66049 * L ^ (1 / 128 : ℝ) := by
              rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 2, ← Real.rpow_mul hL0.le]
              norm_num
            rw [h257]
            exact mul_le_mul hc7_div
              (mul_le_mul hcard
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hQ₁_le (by positivity)) (by positivity))
                  (by positivity))
                (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = C_hi1 * L ^ (-9 / 256 : ℝ) := by
            dsimp only [C_hi1]
            have hexp : L ^ (-1 / 8 : ℝ) * L ^ (13 / 32 : ℝ) * L ^ (13 / 32 : ℝ) *
                L ^ (1 / 128 : ℝ) * L ^ (-187 / 256 : ℝ) = L ^ (-9 / 256 : ℝ) := by
              rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
                ← Real.rpow_add hL0]
              norm_num
            rw [← hexp]; ring
        _ ≤ C_hi1 / L ^ (1 / 32 : ℝ) :=
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (-9 / 256 : ℝ) ≤ -(1 / 32)))
              hChi1_0).trans_eq (by rw [Real.rpow_neg hL0.le, div_eq_mul_inv])
        _ ≤ ε / 2 := by
            rw [div_le_iff₀ (by positivity)]
            have hm := mul_le_mul_of_nonneg_left hL_32 hε.le
            have heq : ε * (2 * C_hi1 / ε + 1) = 2 * C_hi1 + ε := by field_simp [hε.ne']
            linarith only [hm, heq, hε]
    have hsplit : (∑ m ∈ Ioc m₀ Q₁,
        topCollarDualSeventhMass M N (conductorResidualVector c m N) /
          completedConductorEnergy tiltedUnitSpline c m) =
        (∑ m ∈ Ioc m₀ Q₁, if (m : ℝ) ≤ c then _ else 0) +
          (∑ m ∈ Ioc m₀ Q₁, if c < (m : ℝ) then _ else 0) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      by_cases hmc : (m : ℝ) ≤ c
      · rw [if_pos hmc, if_neg (not_lt.mpr hmc), add_zero]
      · rw [if_neg hmc, if_pos (lt_of_not_ge hmc), zero_add]
    rw [hsplit, mul_add]
    linarith only [hlow1, hhi1]
  · -- Part 2: Sub-quarter packet `Ioc m₀ ⌊L^{1/4}⌋₊` with `(1 / c)` weight
    set Q₀ := ⌊L ^ (1 / 4 : ℝ)⌋₊
    have hlow2 : (1 / c) * (∑ m ∈ Ioc m₀ Q₀,
        if (m : ℝ) ≤ c then
          topCollarDualSeventhMass M N (conductorResidualVector c m N) /
            completedConductorEnergy tiltedUnitSpline c m
        else 0) ≤ ε / 2 := by
      have hbase := above_cutoff_low_range_dualSeventh_sum_le hm₀1 hc1 hL1 hR₀0 hKd7
        (hc8.trans (mul_le_mul_of_nonneg_right hR_le hL0.le))
        (fun m hm _ => hd7_pt m (lt_of_le_of_lt hm₀1 (mem_Ioc.mp hm).1))
      have h1 : 3 * K_d7 * R₀ / κ ≤ 3 * K_d7 * R₀ ^ 2 / κ := by
        have : R₀ ≤ R₀ ^ 2 := le_self_pow₀ hR₀1 two_ne_zero
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity)) hκ.le
      exact hbase.trans ((div_le_div_of_nonneg_right h1 (by positivity)).trans hlow_eps)
    have hQ₀_le : (Q₀ : ℝ) ≤ L ^ (1 / 4 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have hhi2 : (1 / c) * (∑ m ∈ Ioc m₀ Q₀,
        if c < (m : ℝ) then
          topCollarDualSeventhMass M N (conductorResidualVector c m N) /
            completedConductorEnergy tiltedUnitSpline c m
        else 0) ≤ ε / 2 := by
      have hpt2 : ∀ m ∈ Ioc m₀ Q₀,
          (if c < (m : ℝ) then
            topCollarDualSeventhMass M N (conductorResidualVector c m N) /
              completedConductorEnergy tiltedUnitSpline c m
          else 0) ≤ (3 * K_d7 / κ) * c ^ 2 * L ^ (-1 / 2 : ℝ) := by
        intro m hm
        split_ifs with hmc
        · obtain ⟨hm_gt, hmQ⟩ := mem_Ioc.mp hm
          have hm1 : 1 ≤ m := by omega
          have hm2 : (m : ℝ) ^ 2 ≤ L ^ (1 / 2 : ℝ) := by
            calc (m : ℝ) ^ 2 ≤ (L ^ (1 / 4 : ℝ)) ^ 2 :=
                  pow_le_pow_left₀ (Nat.cast_nonneg m) ((by exact_mod_cast hmQ : (m : ℝ) ≤ Q₀).trans hQ₀_le) 2
              _ = L ^ (1 / 2 : ℝ) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
          have hEm : κ ≤ completedConductorEnergy tiltedUnitSpline c m :=
            tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm1 hmc.le
          have hEpos := completedConductorEnergy_tilted_pos hc0 hm1
          calc topCollarDualSeventhMass M N (conductorResidualVector c m N) /
                  completedConductorEnergy tiltedUnitSpline c m
              ≤ (K_d7 * (m : ℝ) ^ 2 * (3 * c ^ 2 / L)) / κ :=
                (div_le_div_of_nonneg_right (hd7_pt m hm1) hEpos.le).trans
                  (div_le_div_of_nonneg_left (by positivity) hκ hEm)
            _ ≤ (K_d7 * L ^ (1 / 2 : ℝ) * (3 * c ^ 2 * L ^ (-1 : ℝ))) / κ := by
                rw [div_eq_mul_inv, ← Real.rpow_neg_one L]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 hKd7.le) (by positivity))
                  hκ.le
            _ = (3 * K_d7 / κ) * c ^ 2 * L ^ (-1 / 2 : ℝ) := by
                have hexp : L ^ (1 / 2 : ℝ) * L ^ (-1 : ℝ) = L ^ (-1 / 2 : ℝ) := by
                  rw [← Real.rpow_add hL0]; norm_num
                calc (K_d7 * L ^ (1 / 2 : ℝ) * (3 * c ^ 2 * L ^ (-1 : ℝ))) / κ
                    = (3 * K_d7 / κ) * c ^ 2 * (L ^ (1 / 2 : ℝ) * L ^ (-1 : ℝ)) := by ring
                  _ = (3 * K_d7 / κ) * c ^ 2 * L ^ (-1 / 2 : ℝ) := by rw [hexp]
        · positivity
      have hcard0 : ((Ioc m₀ Q₀).card : ℝ) ≤ L ^ (1 / 4 : ℝ) := by
        rw [Nat.card_Ioc]
        exact (by exact_mod_cast Nat.sub_le Q₀ m₀ : ((Q₀ - m₀ : ℕ) : ℝ) ≤ Q₀).trans hQ₀_le
      calc (1 / c) * ∑ m ∈ Ioc m₀ Q₀, _
          ≤ (1 / c) * ∑ _m ∈ Ioc m₀ Q₀, (3 * K_d7 / κ) * c ^ 2 * L ^ (-1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left (sum_le_sum hpt2) (by positivity)
        _ = ((Ioc m₀ Q₀).card : ℝ) * ((3 * K_d7 / κ) * c * L ^ (-1 / 2 : ℝ)) := by
            rw [sum_const, nsmul_eq_mul]; field_simp [hc0.ne']
        _ ≤ L ^ (1 / 4 : ℝ) * ((3 * K_d7 / κ) * (R₀ * L ^ (1 / 8 : ℝ)) * L ^ (-1 / 2 : ℝ)) :=
            mul_le_mul hcard0
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_R₀ (by positivity))
                (by positivity))
              (by positivity) (by positivity)
        _ = C_hi2 / L ^ (1 / 8 : ℝ) := by
            dsimp only [C_hi2]
            have hexp : L ^ (1 / 4 : ℝ) * L ^ (1 / 8 : ℝ) * L ^ (-1 / 2 : ℝ) =
                (L ^ (1 / 8 : ℝ))⁻¹ := by
              rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_neg hL0.le]
              norm_num
            rw [div_eq_mul_inv, ← hexp]; ring
        _ ≤ ε / 2 := by
            rw [div_le_iff₀ (by positivity)]
            have hm := mul_le_mul_of_nonneg_left
              (show 2 * C_hi2 / ε + 1 ≤ L ^ (1 / 8 : ℝ) by linarith only [hL_18, hR₀0]) hε.le
            have heq : ε * (2 * C_hi2 / ε + 1) = 2 * C_hi2 + ε := by field_simp [hε.ne']
            linarith only [hm, heq, hε]
    have hsplit2 : (∑ m ∈ Ioc m₀ Q₀,
        topCollarDualSeventhMass M N (conductorResidualVector c m N) /
          completedConductorEnergy tiltedUnitSpline c m) =
        (∑ m ∈ Ioc m₀ Q₀, if (m : ℝ) ≤ c then _ else 0) +
          (∑ m ∈ Ioc m₀ Q₀, if c < (m : ℝ) then _ else 0) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      by_cases hmc : (m : ℝ) ≤ c
      · rw [if_pos hmc, if_neg (not_lt.mpr hmc), add_zero]
      · rw [if_neg hmc, if_pos (lt_of_not_ge hmc), zero_add]
    rw [hsplit2, mul_add]
    linarith only [hlow2, hhi2]

/-- **All-ratio operator-residual Schur decoupling above a finite conductor cutoff.**
Below any critical ratio `R_max > 0`, there exists `B_R ≥ 0` such that for every `ε > 0`, there
exists a finite conductor cutoff `m₀ ≥ 1` such that eventually in `N`, for every `1 ≤ c` with
`c⁸ ≤ R_max log N`, every coefficient vector `b : ℕ → ℝ` on `Ioc m₀ ⌊(log N)^{1/4}⌋₊`, and every
collar vector `y` vanishing on `Icc 1 (N / linearDefectCutoff c)`, the diagonal-subtracted
bilinear pairing of `u = ∑ m ∈ Ioc m₀ ⌊(log N)^{1/4}⌋₊, b m • v_m` against `y` satisfies the
unit-`ℓ²` Schur bound against `weilQuad U_y + B_R ∫ U_y²`. -/
theorem exists_above_cutoff_subquarter_packet_collar_schur_below_ratio {R_max : ℝ} (hR : 0 < R_max) :
    ∃ B_R : ℝ, 0 ≤ B_R ∧ ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
        ∀ (b : ℕ → ℝ) (y : EuclideanSpace ℝ (PrimeHorizonIndex N)),
          (∀ n, n ≤ N / linearDefectCutoff c → primeHorizonExtension y n = 0) →
          (weilBilin
              (normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension y) c N)
              (normalizedCentredAtomicTest tiltedUnitSpline
                (primeHorizonExtension
                  (∑ m ∈ Ioc m₀ ⌊Real.log (N : ℝ) ^ (1 / 4 : ℝ)⌋₊,
                    b m • normalizedRamanujanHorizonVector m N)) c N) -
            ((∫ t, tiltedUnitSpline t ^ 2) / c) *
              ∑ m ∈ Ioc m₀ ⌊Real.log (N : ℝ) ^ (1 / 4 : ℝ)⌋₊,
                b m * completedConductorEnergy tiltedUnitSpline c m *
                  ⟪normalizedRamanujanHorizonVector m N, y⟫) ^ 2 ≤
            ε * (((∫ t, tiltedUnitSpline t ^ 2) / c) *
              ∑ m ∈ Ioc m₀ ⌊Real.log (N : ℝ) ^ (1 / 4 : ℝ)⌋₊,
                completedConductorEnergy tiltedUnitSpline c m * b m ^ 2) *
              (weilQuad (normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension y) c N) +
                B_R * ∫ t, normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension y) c N t ^ 2) := by
  obtain ⟨B_g, a_R, κ_R, hBg0, haR, hκR, hgard_ev⟩ := exists_collar_atomic_garding_below_ratio hR
  have hI₂ : 0 < ∫ t, tiltedUnitSpline t ^ 2 := integral_tiltedUnitSpline_sq_pos
  refine ⟨B_g, hBg0, fun ε hε => ?_⟩
  set ε' : ℝ := ε * κ_R / (2 * ∫ t, tiltedUnitSpline t ^ 2)
  have hε' : 0 < ε' := by dsimp only [ε']; positivity
  obtain ⟨m₀, hm₀1, hcut_ev⟩ := exists_finite_conductor_cutoff_collar_dualSeventh_below_ratio hR hε'
  refine ⟨m₀, hm₀1, ?_⟩
  filter_upwards [hgard_ev, hcut_ev, eventually_ge_atTop 1] with N hgardN hcutN hN1 c hc1 hc8 b y hy_supp
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  set I₂ := ∫ t, tiltedUnitSpline t ^ 2
  set M := N / linearDefectCutoff c
  set Q₀ := ⌊Real.log (N : ℝ) ^ (1 / 4 : ℝ)⌋₊
  have hMN : M ≤ N := Nat.div_le_self _ _
  obtain ⟨h2BM, hd7_both⟩ := hcutN hc1 hc8
  have hd7_sum := (hd7_both h2BM).2
  set u := ∑ m ∈ Ioc m₀ Q₀, b m • normalizedRamanujanHorizonVector m N
  set U_y := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension y) c N
  set U_u := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension u) c N
  set Qy := weilQuad U_y + B_g * ∫ t, U_y t ^ 2
  have hy_tail : atomicTailCoefficients M (primeHorizonExtension y) = primeHorizonExtension y := by
    funext n; unfold atomicTailCoefficients
    by_cases h : M < n
    · exact if_pos h
    · rw [if_neg h, hy_supp n (Nat.not_lt.mp h)]
  have hgard := hgardN c hc1 hc8 (primeHorizonExtension y)
  dsimp only at hgard
  rw [hy_tail] at hgard
  have hW8_nn : 0 ≤ a_R * ∫ t, U_y t ^ 2 * Real.exp (-(8 * t)) :=
    mul_nonneg haR.le (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hS7_Qy : topCollarSeventhMass M N (primeHorizonExtension y) ≤ Qy / κ_R :=
    (le_div_iff₀ hκR).mpr (by linarith only [hgard, hW8_nn, mul_comm κ_R
      (topCollarSeventhMass M N (primeHorizonExtension y))])
  have hQy0 : 0 ≤ Qy :=
    (mul_nonneg hκR.le (topCollarSeventhMass_nonneg M N _)).trans (by linarith only [hgard, hW8_nn])
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
  have hbil_eq : weilBilin U_y U_u -
      (I₂ / c) * ∑ m ∈ Ioc m₀ Q₀,
        b m * completedConductorEnergy tiltedUnitSpline c m *
          ⟪normalizedRamanujanHorizonVector m N, y⟫ =
      (I₂ / c) * ∑ m ∈ Ioc m₀ Q₀, b m * ⟪conductorResidualVector c m N, y⟫ := by
    rw [weilBilin_normalizedCentredAtomicTest_eq contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      hI₂ hc0 hN1 y u, hsym y u, real_inner_comm y u]
    dsimp only [u, conductorResidualVector]
    rw [map_sum, sum_inner, ← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [map_smul, real_inner_smul_left, inner_sub_left, real_inner_smul_left]
    ring
  have hcs : (∑ m ∈ Ioc m₀ Q₀, b m * ⟪conductorResidualVector c m N, y⟫) ^ 2 ≤
      (∑ m ∈ Ioc m₀ Q₀, completedConductorEnergy tiltedUnitSpline c m * b m ^ 2) *
        (∑ m ∈ Ioc m₀ Q₀, ⟪conductorResidualVector c m N, y⟫ ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m) := by
    have hrew : (∑ m ∈ Ioc m₀ Q₀, b m * ⟪conductorResidualVector c m N, y⟫) =
        ∑ m ∈ Ioc m₀ Q₀,
          (Real.sqrt (completedConductorEnergy tiltedUnitSpline c m) * b m) *
            (⟪conductorResidualVector c m N, y⟫ /
              Real.sqrt (completedConductorEnergy tiltedUnitSpline c m)) := by
      refine sum_congr rfl fun m hm => ?_
      have hEpos := completedConductorEnergy_tilted_pos hc0 (lt_of_le_of_lt hm₀1 (mem_Ioc.mp hm).1)
      field_simp [(Real.sqrt_pos.mpr hEpos).ne']
    rw [hrew]
    refine (Finset.sum_mul_sq_le_sq_mul_sq (Ioc m₀ Q₀) _ _).trans_eq ?_
    congr 1
    · refine sum_congr rfl fun m hm => ?_
      have hEpos := completedConductorEnergy_tilted_pos hc0 (lt_of_le_of_lt hm₀1 (mem_Ioc.mp hm).1)
      rw [mul_pow, Real.sq_sqrt hEpos.le]
    · refine sum_congr rfl fun m hm => ?_
      have hEpos := completedConductorEnergy_tilted_pos hc0 (lt_of_le_of_lt hm₀1 (mem_Ioc.mp hm).1)
      rw [div_pow, Real.sq_sqrt hEpos.le]
  have hy_pre0 : ∑ n ∈ Icc 1 M, primeHorizonExtension y n ^ 2 = 0 :=
    sum_eq_zero fun n hn => by rw [hy_supp n (mem_Icc.mp hn).2]; ring
  have hinner_sum : (∑ m ∈ Ioc m₀ Q₀, ⟪conductorResidualVector c m N, y⟫ ^ 2 /
        completedConductorEnergy tiltedUnitSpline c m) ≤
      (2 * Qy / κ_R) * ∑ m ∈ Ioc m₀ Q₀,
        topCollarDualSeventhMass M N (conductorResidualVector c m N) /
          completedConductorEnergy tiltedUnitSpline c m := by
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have hEpos := completedConductorEnergy_tilted_pos hc0 (lt_of_le_of_lt hm₀1 (mem_Ioc.mp hm).1)
    have hin := inner_sq_le_prefix_add_topCollarSeventh hMN (conductorResidualVector c m N) y
    rw [hy_pre0, mul_zero, zero_add] at hin
    have hin2 : ⟪conductorResidualVector c m N, y⟫ ^ 2 ≤
        (2 * Qy / κ_R) * topCollarDualSeventhMass M N (conductorResidualVector c m N) := by
      have hm1 := mul_le_mul_of_nonneg_left hS7_Qy
        (mul_nonneg zero_le_two (topCollarDualSeventhMass_nonneg M N _))
      linarith only [hin, hm1,
        (by ring : 2 * topCollarDualSeventhMass M N (conductorResidualVector c m N) * (Qy / κ_R) =
          (2 * Qy / κ_R) * topCollarDualSeventhMass M N (conductorResidualVector c m N))]
    exact (div_le_div_of_nonneg_right hin2 hEpos.le).trans_eq (mul_div_assoc _ _ _)
  set E_b := ∑ m ∈ Ioc m₀ Q₀, completedConductorEnergy tiltedUnitSpline c m * b m ^ 2
  have hEb0 : 0 ≤ E_b := sum_nonneg fun m hm =>
    mul_nonneg (completedConductorEnergy_tilted_pos hc0
      (lt_of_le_of_lt hm₀1 (mem_Ioc.mp hm).1)).le (sq_nonneg _)
  rw [hbil_eq, mul_pow]
  calc (I₂ / c) ^ 2 * (∑ m ∈ Ioc m₀ Q₀, b m * ⟪conductorResidualVector c m N, y⟫) ^ 2
      ≤ (I₂ / c) ^ 2 * (E_b * ((2 * Qy / κ_R) * ∑ m ∈ Ioc m₀ Q₀,
          topCollarDualSeventhMass M N (conductorResidualVector c m N) /
            completedConductorEnergy tiltedUnitSpline c m)) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hinner_sum hEb0))
          (sq_nonneg _)
    _ = ((2 * I₂ / κ_R) * ((1 / c) * ∑ m ∈ Ioc m₀ Q₀,
          topCollarDualSeventhMass M N (conductorResidualVector c m N) /
            completedConductorEnergy tiltedUnitSpline c m)) * ((I₂ / c) * E_b) * Qy := by
        field_simp [hc0.ne', hκR.ne']; ring
    _ ≤ ((2 * I₂ / κ_R) * ε') * ((I₂ / c) * E_b) * Qy :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hd7_sum (by positivity))
            (mul_nonneg (div_nonneg hI₂.le hc0.le) hEb0)) hQy0
    _ = ε * ((I₂ / c) * E_b) * Qy := by
        dsimp only [ε', I₂]; field_simp [hI₂.ne', hκR.ne']

/-- **Complete two-sided resolution of prefix and low-packet collar coupling at a fixed critical ratio.**
Along any critical schedule `c_N ≥ 1` with `c_N⁸ / log N → R > 0`:
1. **Physical tearing fails on `(conductorSubspace Q₁ N)ᗮ` (`4 / 13` Schur limit):** for every
   `B_R ∈ ℝ`, the Schur ratio of `lowPacketOrthogonalPrimeQuasimode N` split at
   `M = N / linearDefectCutoff (c_N)` converges to `4 / 13`;
2. **Conductor-adapted prefix decoupling holds on `(conductorSubspace R₁ N)ᗮ`:** there exists
   `B_R ≥ 0` such that `o(1)` prefix–collar Schur decoupling holds across `M` on the far-conductor
   complement (`R₁ = farConductorCutoff N`);
3. **Finite-conductor low-packet reduction:** for every `ε > 0`, there exists a finite conductor
   cutoff `m₀ ≥ 1` above which the low-packet dual seventh-power collar residual budget on
   `Ioc m₀ (lowPacketCutoff N)` is eventually at most `ε`;
4. **Sharp `m = 1` polar retention:** on every compact terminal window `[-A, 0]`, the optimally
   pole-corrected complete energy converges to
   `windowPencil R (halfWeight h) - generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R`,
   and eventual nonnegativity of `completeWeilMatrix tiltedUnitSpline (c_N) N` forces
   `PolarPaymentAt R A` on every `A ≥ 0`. -/
theorem complete_prefix_and_low_packet_collar_resolution {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc : ∀ N, 1 ≤ c N) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    (∀ B_R : ℝ, Tendsto (fun N : ℕ =>
        let M := N / linearDefectCutoff (c N)
        let U_p := normalizedCentredAtomicTest tiltedUnitSpline
          (primeHorizonExtension (horizonPrefixVector M (lowPacketOrthogonalPrimeQuasimode N)))
          (c N) N
        let U_y := normalizedCentredAtomicTest tiltedUnitSpline
          (primeHorizonExtension (horizonCollarVector M (lowPacketOrthogonalPrimeQuasimode N)))
          (c N) N
        weilBilin U_y U_p ^ 2 / (weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2)))
      atTop (𝓝 (4 / 13 : ℝ))) ∧
    (∃ B_R : ℝ, 0 ≤ B_R ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ p y : EuclideanSpace ℝ (PrimeHorizonIndex N),
        p ∈ (conductorSubspace (farConductorCutoff N) N)ᗮ →
        (∀ n, N / linearDefectCutoff (c N) < n → primeHorizonExtension p n = 0) →
        (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension y n = 0) →
        let U_p := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension p) (c N) N
        let U_y := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension y) (c N) N
        weilBilin U_y U_p ^ 2 ≤
          ε * weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ᶠ N : ℕ in atTop,
      (c N ^ 7 / Real.log (N : ℝ)) *
        (∑ m ∈ Ioc m₀ (lowPacketCutoff N),
          topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
            (conductorResidualVector (c N) m N) /
            completedConductorEnergy tiltedUnitSpline (c N) m) ≤ ε) ∧
    ((∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
        0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) z, z⟫) →
      ∀ A : ℝ, 0 ≤ A → PolarPaymentAt R A) := by
  have hc_ev : ∀ᶠ N in atTop, 1 ≤ c N := Eventually.of_forall hc
  refine ⟨fun B_R => tendsto_prime_quasimode_prefix_collar_schur_ratio hR hc_ev hcrit B_R,
    exists_far_prefix_collar_schur_decoupling hR hc_ev hcrit,
    fun ε hε => ?_,
    fun hpsd _A hA => polarPaymentAt_of_eventually_nonneg hc hR hcrit hpsd hA⟩
  obtain ⟨m₀, hm₀1, hcut⟩ :=
    exists_finite_conductor_cutoff_collar_dualSeventh_below_ratio (R_max := R + 1) (by linarith) hε
  refine ⟨m₀, hm₀1, ?_⟩
  filter_upwards [hcut, hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    eventually_ge_atTop 3] with N hN hrat hN3
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨h2BM, hboth⟩ := hN (hc N) ((div_lt_iff₀ hL0).mp hrat).le
  exact (hboth h2BM).1

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
