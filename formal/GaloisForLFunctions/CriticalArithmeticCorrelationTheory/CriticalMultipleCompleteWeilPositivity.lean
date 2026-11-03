import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals

/-!
# Positivity of the complete Weil family at a fixed critical multiple

There exists an explicit critical multiple `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N` and
uniformly across `1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, both `spectralFloorWeilMatrix c N` and
`completeWeilMatrix tiltedUnitSpline c N` are positive definite on the entire prime-horizon space
`EuclideanSpace ℝ (PrimeHorizonIndex N)`, retaining the uniform `(κ₀ / (2 c^7)) ‖x‖^2` spectral
floor (`κ₀ = tiltedSplineSpectralFloorConstant`).

Below `(log N)^{1/16}`, positive definiteness of `spectralFloorWeilMatrix c N` is supplied by
`eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth`. Across the upper
band `(log N)^{1/16} ≤ c ≤ 2 K₁ (log N)^{1/8}`, we split `x = y + u₀ + u₁ + w` along
`V_{Q₁} ⊂ V_{R₀} ⊂ V_{R₁}` with `Q₁ = ⌊(log N)^{13/32}⌋₊`, `R₀ = ⌊exp √(log N)⌋₊`, and the
subexponential cutoff `R₁ = subexpCutoff N = ⌊exp (log N / (1 + log log N)^5)⌋₊`:

* On `V_{Q₁}`, `exists_critical_multiple_low_packet_and_collar_budget` gives the uniform `(1 / 4)`
  packet energy floor, the total inverse-energy residual bound `Ψ ≤ (log N)^{1/4}`, and the
  top-collar dual seventh-power residual bound `(c^7 / log N) Ψ_{d7} ≤ g₀ / 2048`.
* On `(V_{R₁})ᗮ`, `exists_critical_multiple_far_reserve` (`B = 5`, `κ_P = 1 / (16 D)`) combined
  with `poleDefect_prefix_ge_of_conductor_orthogonal` retains `(k / 4) P_w` on the prefix rows and
  `(g₀ log N / (16 c^7)) S7_w` on the dyadic seventh-power top-collar mass.
* In `(V_{Q₁})ᗮ`, `exists_band_far_cross_le_reserve_shape` at `k = log N / (2 D ℓ^5)` and
  `b = (g₀ D / 4) ℓ^5` (`b k = g₀ log N / 8`) absorbs the band–far cross terms while keeping
  `(κ₀ + 2) ‖u₀ + u₁ + w‖^2` plus separate block reserves `‖u₀‖^2`, `(√(log N) / 32) ‖u₁‖^2`,
  `(k / 8) P_w`, and `(g₀ log N / (32 c^7)) S7_w`; the lower bound `c ≥ (log N)^{1/16}` ensures
  `log N / c^7 ≤ (log N)^{9/16} ≪ k`.
* The Schur coupling `∑_{m ≤ Q₁} ⟪r_m, u₀ + u₁ + w⟫^2 / E_m` is split across deep/top rows on
  `u₀`, by `L^2` norm on `u₁`, and across prefix/collar seventh-power masses on `w` via
  `inner_sq_le_prefix_add_topCollarSeventh`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-! ### 1. Subexponential conductor cutoff geometry -/

/-- The subexponential third-band cutoff `R₁(N) = ⌊exp (log N / (1 + log log N)^5)⌋₊`. -/
def subexpCutoff (N : ℕ) : ℕ :=
  ⌊Real.exp (Real.log (N : ℝ) / (1 + Real.log (Real.log (N : ℝ))) ^ 5)⌋₊

private lemma subexpCutoff_bounds {N : ℕ} {D : ℝ} (hD : 0 < D) (hN1 : 1 ≤ N)
    (hL3000 : 3000 ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hpoly5 : 2 * (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ Real.log (N : ℝ) ^ (1 / 4 : ℝ))
    (hL34_D : 4 * D + 4 ≤ Real.log (N : ℝ) ^ (3 / 4 : ℝ)) :
    ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ ≤ subexpCutoff N ∧
    1 + Real.log (subexpCutoff N : ℝ) ≤
      2 * Real.log (N : ℝ) / (1 + Real.log (Real.log (N : ℝ))) ^ 5 ∧
    1080 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N : ℝ) ∧
    Real.log (N : ℝ) / (2 * D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) ≤
      Real.log (subexpCutoff N : ℝ) / D - 1 ∧
    Real.log (subexpCutoff N : ℝ) / D - 1 ≤
      Real.log (N : ℝ) / (D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) ∧
    Real.log (N : ℝ) ^ 18 * (subexpCutoff N : ℝ) ^ 16 ≤ N := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (N : ℝ) := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log L := ⟨_, rfl⟩
  rw [← hLdef] at hL3000 hLX hpoly5 hL34_D ⊢
  rw [← hℓdef] at hpoly5 ⊢
  have hL1 : 1 ≤ L := by linarith only [hL3000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hℓ5_pos : 0 < ℓ ^ 5 := pow_pos hℓ0 5
  have hL_split : L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ) = L := by
    rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have h2L34 : 2 * L ^ (3 / 4 : ℝ) ≤ L / ℓ ^ 5 := by
    rw [le_div_iff₀ hℓ5_pos]
    have hm := mul_le_mul_of_nonneg_left hpoly5 (Real.rpow_nonneg hL0.le (3 / 4))
    linarith only [hm, hL_split,
      (by ring : L ^ (3 / 4 : ℝ) * (2 * ℓ ^ 5) = 2 * L ^ (3 / 4 : ℝ) * ℓ ^ 5),
      (by ring : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ))]
  have hL34_le : L ^ (3 / 4 : ℝ) ≤ L / ℓ ^ 5 := by
    have : 0 ≤ L ^ (3 / 4 : ℝ) := Real.rpow_nonneg hL0.le _
    linarith only [h2L34, this]
  have hLh_le : L ^ (1 / 2 : ℝ) ≤ L / ℓ ^ 5 :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans hL34_le
  have hR₀R₁ : ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ ≤ subexpCutoff N := by
    rw [subexpCutoff, ← hLdef, ← hℓdef]
    exact Nat.floor_mono (Real.exp_le_exp.mpr hLh_le)
  have hx4 : 4 * D + 4 ≤ L / ℓ ^ 5 := hL34_D.trans hL34_le
  have hexp_ge5 : 5 ≤ Real.exp (L / ℓ ^ 5) := by
    have h1 := Real.add_one_le_exp (L / ℓ ^ 5)
    linarith only [h1, hx4, hD]
  have hR₁_le_exp : (subexpCutoff N : ℝ) ≤ Real.exp (L / ℓ ^ 5) := by
    rw [subexpCutoff, ← hLdef, ← hℓdef]
    exact Nat.floor_le (Real.exp_pos _).le
  have hhalf_exp : (1 / 2 : ℝ) * Real.exp (L / ℓ ^ 5) ≤ (subexpCutoff N : ℝ) := by
    have hgt : Real.exp (L / ℓ ^ 5) - 1 < (subexpCutoff N : ℝ) := by
      rw [subexpCutoff, ← hLdef, ← hℓdef]
      exact sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hgt, hexp_ge5]
  have hR₁_pos : (0 : ℝ) < subexpCutoff N := by linarith only [hhalf_exp, hexp_ge5]
  have hlogR₁_ub : Real.log (subexpCutoff N : ℝ) ≤ L / ℓ ^ 5 :=
    (Real.log_le_log hR₁_pos hR₁_le_exp).trans_eq (Real.log_exp _)
  have hlogR₁_lb : L / ℓ ^ 5 - 1 ≤ Real.log (subexpCutoff N : ℝ) := by
    have hdiv_exp : Real.exp (L / ℓ ^ 5) / 2 ≤ (subexpCutoff N : ℝ) := by
      linarith only [hhalf_exp]
    have h1 := Real.log_le_log (by positivity) hdiv_exp
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [h1, hlog2]
  have h1_ub : 1 + Real.log (subexpCutoff N : ℝ) ≤ 2 * L / ℓ ^ 5 := by
    rw [mul_div_assoc]
    linarith only [hlogR₁_ub, hx4, hD]
  have hℓ_ge5 : 5 ≤ ℓ := by
    have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have he4 : Real.exp 4 ≤ L := by
      have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hp : (Real.exp 1) ^ 4 ≤ 81 :=
        (pow_le_pow_left₀ (Real.exp_pos 1).le he1 4).trans_eq (by norm_num)
      linarith only [h4, hp, hL3000]
    have hl4 : 4 ≤ Real.log L := (Real.log_exp 4).symm.trans_le (Real.log_le_log (by positivity) he4)
    rw [hℓdef]; linarith only [hl4]
  have hℓ5_3125 : (3125 : ℝ) ≤ ℓ ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num) hℓ_ge5 5
    norm_num at hp; exact hp
  have hx_3125 : L / ℓ ^ 5 ≤ L / 3125 :=
    div_le_div_of_nonneg_left hL0.le (by norm_num) hℓ5_3125
  have h1080 : 1080 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ L := by
    have h := hlogR₁_ub.trans hx_3125
    linarith only [h, hL3000]
  have hgap_lo : L / (2 * D * ℓ ^ 5) ≤ Real.log (subexpCutoff N : ℝ) / D - 1 := by
    have h34 : (3 / 4 : ℝ) * (L / ℓ ^ 5) ≤ Real.log (subexpCutoff N : ℝ) := by
      linarith only [hlogR₁_lb, hx4, hD]
    have hdiv := div_le_div_of_nonneg_right h34 hD.le
    have h1 : D ≤ (1 / 4 : ℝ) * (L / ℓ ^ 5) := by linarith only [hx4]
    have h1' : 1 ≤ (1 / 4 : ℝ) * (L / ℓ ^ 5) / D := (le_div_iff₀ hD).mpr (by linarith only [h1])
    have hid : (3 / 4 : ℝ) * (L / ℓ ^ 5) / D =
        L / (2 * D * ℓ ^ 5) + (1 / 4 : ℝ) * (L / ℓ ^ 5) / D := by
      field_simp [hD.ne', hℓ5_pos.ne']; ring
    linarith only [hdiv, h1', hid]
  have hgap_hi : Real.log (subexpCutoff N : ℝ) / D - 1 ≤ L / (D * ℓ ^ 5) := by
    have hdiv := div_le_div_of_nonneg_right hlogR₁_ub hD.le
    rw [div_div] at hdiv
    have : L / (ℓ ^ 5 * D) = L / (D * ℓ ^ 5) := by ring
    linarith only [hdiv, this]
  have hRN₁ : L ^ 18 * (subexpCutoff N : ℝ) ^ 16 ≤ N := by
    have hR₁_N : (subexpCutoff N : ℝ) ≤ (N : ℝ) ^ (1 / 3125 : ℝ) := by
      calc
        (subexpCutoff N : ℝ) ≤ Real.exp (L / ℓ ^ 5) := hR₁_le_exp
        _ ≤ Real.exp (L / 3125) := Real.exp_le_exp.mpr hx_3125
        _ = (N : ℝ) ^ (1 / 3125 : ℝ) := by
          rw [Real.rpow_def_of_pos hN0, hLdef]; congr 1; ring
    have hR16 : (subexpCutoff N : ℝ) ^ 16 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        (subexpCutoff N : ℝ) ^ 16 ≤ ((N : ℝ) ^ (1 / 3125 : ℝ)) ^ 16 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hR₁_N 16
        _ = (N : ℝ) ^ (16 / 3125 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
        _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
    have hL18 : L ^ 18 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        L ^ 18 ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 18 := pow_le_pow_left₀ hL0.le hLX 18
        _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    calc
      L ^ 18 * (subexpCutoff N : ℝ) ^ 16 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul hL18 hR16 (by positivity) (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; norm_num [Real.rpow_one]
  exact ⟨hR₀R₁, h1_ub, h1080, hgap_lo, hgap_hi, hRN₁⟩

/-! ### 2. Far-sector prefix + dyadic seventh-power collar reserve at `subexpCutoff N` -/

private lemma subexp_far_collar_reserve {N : ℕ} {c D g₀ CB : ℝ}
    (hD_eq : D = explicitConductorCutoffConstant)
    (hD : 0 < D) (hg₀ : 0 < g₀) (hCB0 : 0 ≤ CB)
    (hc1 : 1 ≤ c) (hc8_le : c ^ 8 ≤ Real.log (N : ℝ))
    (hL2 : 2 ≤ Real.log (N : ℝ))
    (hR₁2 : 2 ≤ subexpCutoff N)
    (hM2 : 2 ≤ N / linearDefectCutoff c)
    (hRM1 : subexpCutoff N * subexpCutoff N ≤ N / linearDefectCutoff c)
    (hlogM1 : 18 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N / linearDefectCutoff c : ℕ))
    (hhalf_M : Real.log (N : ℝ) / 2 ≤ Real.log (N / linearDefectCutoff c : ℕ))
    (hB1_ub : terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N ≤
      CB * (1 + Real.log c))
    (h1c_ℓ : 1 + Real.log c ≤ 1 + Real.log (Real.log (N : ℝ)))
    (hgap_lo : Real.log (N : ℝ) / (2 * D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) ≤
      Real.log (subexpCutoff N : ℝ) / D - 1)
    (hgap_hi : Real.log (subexpCutoff N : ℝ) / D - 1 ≤
      Real.log (N : ℝ) / (D * (1 + Real.log (Real.log (N : ℝ))) ^ 5))
    (hℓ_leak : 56 * CB / (D * g₀) ≤ 1 + Real.log (Real.log (N : ℝ)))
    (hfar : ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
      (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
        (g₀ / (8 * c ^ 7)) * Real.log (N : ℝ) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
        ((1 / (16 * D)) * Real.log (N : ℝ) / (1 + Real.log (Real.log (N : ℝ))) ^ 5) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) ≤
        completeWeilEnergy tiltedUnitSpline c N z)
    {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hw : w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ) :
    (Real.log (N : ℝ) / (2 * D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) / 4) *
        (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
      (g₀ * Real.log (N : ℝ) / (16 * c ^ 7)) *
        topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
      completeWeilEnergy tiltedUnitSpline c N w := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (N : ℝ) := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log L := ⟨_, rfl⟩
  rw [← hLdef] at hc8_le hL2 hhalf_M h1c_ℓ hgap_lo hgap_hi hℓ_leak hfar ⊢
  rw [← hℓdef] at h1c_ℓ hgap_lo hgap_hi hℓ_leak hfar ⊢
  have hL0 : 0 < L := by linarith only [hL2]
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hk_pos : 0 < L / (2 * D * ℓ ^ 5) := by positivity
  have hscale : explicitConductorCutoffConstant ≤ Real.log (subexpCutoff N : ℝ) := by
    rw [← hD_eq]
    have h1 : 1 ≤ Real.log (subexpCutoff N : ℝ) / D := by linarith only [hgap_lo, hk_pos]
    simpa only [one_mul] using (le_div_iff₀ hD).mp h1
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR₁2 hM2 (Nat.div_le_self _ _) hRM1
    hlogM1 hscale hw
  rw [← hD_eq, mul_div_assoc] at hpre
  have hw1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ subexpCutoff N) N hv)
  have hfarw := hfar hw1
  have hSw_le : (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
      topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) :=
    sum_sq_Ioc_le_topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w)
  have hP0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) :=
    hS0.trans hSw_le
  have hlogM_pos : 0 < Real.log (N / linearDefectCutoff c : ℕ) := by linarith only [hhalf_M, hL0]
  have hB_le : terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
      Real.log (N / linearDefectCutoff c : ℕ) ≤ 2 * CB * ℓ / L := by
    rw [div_le_div_iff₀ hlogM_pos hL0]
    have h1 : terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N ≤ CB * ℓ :=
      hB1_ub.trans (mul_le_mul_of_nonneg_left h1c_ℓ hCB0)
    have h0 := terminalPacketCost_nonneg (subexpCutoff N) (Nat.div_le_self N (linearDefectCutoff c))
    nlinarith only [h1, h0, hhalf_M, hL0, mul_nonneg hCB0 hℓ0.le]
  have hB0 : 0 ≤ terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
      Real.log (N / linearDefectCutoff c : ℕ) :=
    div_nonneg (terminalPacketCost_nonneg _ (Nat.div_le_self _ _)) hlogM_pos.le
  have hleak : (7 / 4 : ℝ) * (Real.log (subexpCutoff N : ℝ) / D - 1) *
      (terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
        Real.log (N / linearDefectCutoff c : ℕ)) ≤ g₀ * L / (16 * c ^ 7) := by
    have h1 : (7 / 4 : ℝ) * (Real.log (subexpCutoff N : ℝ) / D - 1) *
        (terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
          Real.log (N / linearDefectCutoff c : ℕ)) ≤
        (7 / 4 : ℝ) * (L / (D * ℓ ^ 5)) * (2 * CB * ℓ / L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hgap_hi (by norm_num)) hB_le hB0 (by positivity)
    have h2 : (7 / 4 : ℝ) * (L / (D * ℓ ^ 5)) * (2 * CB * ℓ / L) =
        (7 * CB / (2 * D)) / ℓ ^ 4 := by
      field_simp [hD.ne', hℓ0.ne', hL0.ne']; ring
    have h3 : (7 * CB / (2 * D)) / ℓ ^ 4 ≤ (7 * CB / (2 * D)) / ℓ :=
      div_le_div_of_nonneg_left (by positivity) hℓ0
        (by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 4))
    have h4 : (7 * CB / (2 * D)) / ℓ ≤ g₀ / 16 := by
      rw [div_le_iff₀ hℓ0]
      have hm := mul_le_mul_of_nonneg_left hℓ_leak (by positivity : 0 ≤ g₀ / 16)
      have hid : (g₀ / 16) * (56 * CB / (D * g₀)) = 7 * CB / (2 * D) := by
        field_simp [hD.ne', hg₀.ne']; ring
      linarith only [hm, hid]
    have hc7_L : c ^ 7 ≤ L := (pow_le_pow_right₀ hc1 (by norm_num : 7 ≤ 8)).trans hc8_le
    have h5 : g₀ / 16 ≤ g₀ * L / (16 * c ^ 7) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith only [hc7_L, hg₀]
    exact h1.trans (h2.trans_le (h3.trans (h4.trans h5)))
  generalize (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) = P at
    hpre hfarw hP0 ⊢
  generalize (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) = S at
    hpre hSw_le hS0
  generalize topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) = S7 at
    hfarw hSw_le hS7_0 ⊢
  generalize (Real.log (subexpCutoff N : ℝ) / D - 1) = kg at hpre hgap_lo hleak
  generalize (terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
    Real.log (N / linearDefectCutoff c : ℕ)) = Bp at hpre hleak
  have hpre' : (15 / 16 : ℝ) * (kg * P) - 2 * (kg * Bp * S) ≤
      poleDefect (N / linearDefectCutoff c) (primeHorizonExtension w) := by
    linarith only [hpre,
      (by ring : kg * ((15 / 16 : ℝ) * P - 2 * Bp * S) =
        (15 / 16 : ℝ) * (kg * P) - 2 * (kg * Bp * S))]
  have hP1 := mul_le_mul_of_nonneg_right hgap_lo hP0
  have hS1 := mul_le_mul_of_nonneg_left hSw_le (by positivity : 0 ≤ g₀ * L / (16 * c ^ 7))
  have hS2 : (7 / 4 : ℝ) * (kg * Bp * S) ≤ (g₀ * L / (16 * c ^ 7)) * S7 := by
    have hm := mul_le_mul_of_nonneg_right hleak hS0
    exact ((by ring : (7 / 4 : ℝ) * (kg * Bp * S) = (7 / 4 : ℝ) * kg * Bp * S).trans_le hm).trans hS1
  have hid_far : (1 / (16 * D)) * L / ℓ ^ 5 = (1 / 8 : ℝ) * (L / (2 * D * ℓ ^ 5)) := by
    field_simp [hD.ne', hℓ0.ne']; ring
  have hid_top : (g₀ / (8 * c ^ 7)) * L = 2 * (g₀ * L / (16 * c ^ 7)) := by
    field_simp [hc0.ne']; ring
  rw [hid_far, hid_top] at hfarw
  have hkp : 0 ≤ (L / (2 * D * ℓ ^ 5)) * P := mul_nonneg hk_pos.le hP0
  linarith only [hpre', hfarw, hP1, hS2, hkp,
    (by ring : 2 * (g₀ * L / (16 * c ^ 7)) * S7 = 2 * ((g₀ * L / (16 * c ^ 7)) * S7)),
    (by ring : (1 / 8 : ℝ) * (L / (2 * D * ℓ ^ 5)) * P =
      (1 / 8 : ℝ) * ((L / (2 * D * ℓ ^ 5)) * P)),
    (by ring : (L / (2 * D * ℓ ^ 5) / 4) * P =
      (1 / 4 : ℝ) * ((L / (2 * D * ℓ ^ 5)) * P))]

/-! ### 3. Scalar budgets `hsE ≤ 1 / 32` and `hsU ≤ 1 / 4` at the subexponential cutoff -/

private lemma critical_band_far_budgetE_le {R M N : ℕ}
    {c Sg₁ k b L ℓ D g₀ CB C_pr C_np K_tot : ℝ}
    (hLdef : L = Real.log (N : ℝ)) (hℓdef : ℓ = 1 + Real.log L)
    (hk_def : k = L / (2 * D * ℓ ^ 5)) (hb_def : b = (g₀ * D / 4) * ℓ ^ 5)
    (hD : 0 < D) (hg₀ : 0 < g₀) (hCpr : 0 < C_pr) (hCnp : 0 ≤ C_np) (hCB0 : 0 ≤ CB)
    (hK_tot : 1 ≤ K_tot) (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hc8_le : c ^ 8 ≤ L)
    (hR1 : 1 ≤ R) (hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N)
    (hlR : 1 + Real.log (R : ℝ) ≤ 2 * L / ℓ ^ 5)
    (hTPC : terminalPacketCost R M N ≤ CB * (1 + Real.log c))
    (hSg : Sg₁ ≤ 2 * K_tot * ℓ) (hSg0 : 0 ≤ Sg₁)
    (hℓ_E : 128 * (1024 * D * C_pr + 2048 * C_pr * CB / g₀ +
      512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) + 1 ≤ ℓ) :
    128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (Real.log (N : ℝ) * k) +
      128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
        (Real.log (N : ℝ) * b * k) +
      32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤ 1 / 32 := by
  rw [← hLdef]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hR1R : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hlR0 : 0 ≤ 1 + Real.log (R : ℝ) := by linarith [Real.log_natCast_nonneg R]
  have h1c_ℓ : 1 + Real.log c ≤ ℓ := by rw [hℓdef]; linarith [Real.log_le_log hc0 hcL]
  have h1c0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hc7_L : c ^ 7 ≤ L := (pow_le_pow_right₀ hc1 (by norm_num : 7 ≤ 8)).trans hc8_le
  have hbk : b * k = g₀ * L / 8 := by
    rw [hb_def, hk_def]; field_simp [hD.ne', hℓ0.ne']; ring
  have hLbk : L * b * k = g₀ * L ^ 2 / 8 := by rw [mul_assoc, hbk]; ring
  have hLk : L * k = L ^ 2 / (2 * D * ℓ ^ 5) := by rw [hk_def]; ring
  have hE1 : 128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (L * k) ≤ (1024 * D * C_pr) / ℓ := by
    have hsq : (1 + Real.log (R : ℝ)) ^ 2 ≤ (2 * L / ℓ ^ 5) ^ 2 := pow_le_pow_left₀ hlR0 hlR 2
    calc
      128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (L * k)
          ≤ 128 * C_pr * (2 * L / ℓ ^ 5) ^ 2 / (L ^ 2 / (2 * D * ℓ ^ 5)) := by
            rw [hLk]; exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
      _ = (1024 * D * C_pr) / ℓ ^ 5 := by field_simp [hL0.ne', hD.ne', hℓ0.ne']; ring
      _ ≤ (1024 * D * C_pr) / ℓ := div_le_div_of_nonneg_left (by positivity) hℓ0
          (by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 5))
  have hE2 : 128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
      (L * b * k) ≤ (2048 * C_pr * CB / g₀) / ℓ := by
    have hTPC_ℓ : terminalPacketCost R M N ≤ CB * ℓ :=
      hTPC.trans (mul_le_mul_of_nonneg_left h1c_ℓ hCB0)
    have hTPC0 : 0 ≤ terminalPacketCost R M N := by
      by_cases hMN : M ≤ N
      · exact terminalPacketCost_nonneg R hMN
      · unfold terminalPacketCost
        have : N - M = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hMN)
        rw [this, Nat.cast_zero, zero_add]; positivity
    have hnum : c ^ 7 * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N ≤
        L * (2 * L / ℓ ^ 5) * (CB * ℓ) :=
      mul_le_mul (mul_le_mul hc7_L hlR hlR0 hL0.le) hTPC_ℓ hTPC0 (by positivity)
    calc
      128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N / (L * b * k)
          = 128 * C_pr * (c ^ 7 * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N) /
              (g₀ * L ^ 2 / 8) := by rw [hLbk]; ring
      _ ≤ 128 * C_pr * (L * (2 * L / ℓ ^ 5) * (CB * ℓ)) / (g₀ * L ^ 2 / 8) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by positivity)) (by positivity)
      _ = (2048 * C_pr * CB / g₀) / ℓ ^ 4 := by field_simp [hg₀.ne', hL0.ne', hℓ0.ne']; ring
      _ ≤ (2048 * C_pr * CB / g₀) / ℓ := div_le_div_of_nonneg_left (by positivity) hℓ0
          (by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 4))
  have hE3 : 32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤
      (512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) / ℓ := by
    have hc13 : c ^ 13 / N ≤ 1 :=
      (cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN (one_div_le_one_div_of_le zero_lt_one hL1)
        (by norm_num) (by norm_num)).trans (by norm_num)
    have hc11 : c ^ 11 * (R : ℝ) ^ 4 / (N * L) ≤ 1 := by
      have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hRN
      exact (div_le_div_of_nonneg_left (by positivity) hN0 (le_mul_of_one_le_right hN0.le hL1)).trans
        ((cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN (one_div_le_one_div_of_le zero_lt_one hL1)
          (by norm_num) (by norm_num)).trans (by norm_num))
    have hSg2 : Sg₁ ^ 2 ≤ 4 * K_tot ^ 2 * ℓ ^ 2 := by
      have hp := pow_le_pow_left₀ hSg0 hSg 2
      linarith only [hp, (by ring : (2 * K_tot * ℓ) ^ 2 = 4 * K_tot ^ 2 * ℓ ^ 2)]
    have ht1 : c ^ 7 * (1 + Real.log c) / L ≤ ℓ ^ 3 := by
      calc
        c ^ 7 * (1 + Real.log c) / L ≤ L * ℓ / L :=
          div_le_div_of_nonneg_right (mul_le_mul hc7_L h1c_ℓ h1c0 hL0.le) hL0.le
        _ = ℓ := by field_simp [hL0.ne']
        _ ≤ ℓ ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 3)
    have ht2 : c ^ 8 * Sg₁ ^ 2 * (1 + Real.log c) / L ≤ 4 * K_tot ^ 2 * ℓ ^ 3 := by
      calc
        c ^ 8 * Sg₁ ^ 2 * (1 + Real.log c) / L ≤ L * (4 * K_tot ^ 2 * ℓ ^ 2) * ℓ / L :=
          div_le_div_of_nonneg_right
            (mul_le_mul (mul_le_mul hc8_le hSg2 (sq_nonneg _) hL0.le) h1c_ℓ h1c0 (by positivity))
            hL0.le
        _ = 4 * K_tot ^ 2 * ℓ ^ 3 := by field_simp [hL0.ne']; ring
    have hℓ3_1 : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
    have hG_inner : c ^ 7 * bandFarBudgetG R N c Sg₁ ≤
        (1 + Real.log (R : ℝ)) * ((4 * K_tot ^ 2 + 3) * ℓ ^ 3) := by
      have hid : c ^ 7 * bandFarBudgetG R N c Sg₁ =
          (1 + Real.log (R : ℝ)) * (c ^ 7 * (1 + Real.log c) / L +
            c ^ 8 * Sg₁ ^ 2 * (1 + Real.log c) / L + c ^ 13 / N +
            c ^ 11 * (R : ℝ) ^ 4 / (N * L)) := by
        unfold bandFarBudgetG; rw [← hLdef]; ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left (by linarith only [ht1, ht2, hc13, hc11, hℓ3_1]) hlR0
    calc
      32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k)
          = 32 * C_np * (c ^ 7 * bandFarBudgetG R N c Sg₁) / (g₀ * L / 8) := by rw [hbk]; ring
      _ ≤ 32 * C_np * ((2 * L / ℓ ^ 5) * ((4 * K_tot ^ 2 + 3) * ℓ ^ 3)) / (g₀ * L / 8) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (hG_inner.trans (mul_le_mul_of_nonneg_right hlR (by positivity))) hCnp)
            (by positivity)
      _ = (512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) / ℓ ^ 2 := by
          field_simp [hg₀.ne', hL0.ne', hℓ0.ne']; ring
      _ ≤ (512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) / ℓ := div_le_div_of_nonneg_left (by positivity) hℓ0
          (by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 2))
  calc
    _ ≤ (1024 * D * C_pr + 2048 * C_pr * CB / g₀ +
          512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) / ℓ := by
        linarith only [hE1, hE2, hE3,
          (by ring : (1024 * D * C_pr + 2048 * C_pr * CB / g₀ +
              512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) / ℓ =
            (1024 * D * C_pr) / ℓ + (2048 * C_pr * CB / g₀) / ℓ +
              (512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) / ℓ)]
    _ ≤ 1 / 128 := by rw [div_le_iff₀ hℓ0]; linarith only [hℓ_E]
    _ ≤ 1 / 32 := by norm_num

private lemma critical_band_far_budgetU_le {R M N : ℕ}
    {c ρ Sg₁ k b L ℓ D g₀ C_pr C_up C_upT C_np K_tot K_res : ℝ}
    (hLdef : L = Real.log (N : ℝ)) (hℓdef : ℓ = 1 + Real.log L)
    (hk_def : k = L / (2 * D * ℓ ^ 5)) (hb_def : b = (g₀ * D / 4) * ℓ ^ 5)
    (hD : 0 < D) (hg₀ : 0 < g₀) (hCpr : 0 < C_pr) (hCup : 0 ≤ C_up) (hCupT : 0 ≤ C_upT)
    (hCnp : 0 ≤ C_np) (hK_tot : 1 ≤ K_tot) (hK_res : 0 ≤ K_res)
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hc_L8 : c ≤ L ^ (1 / 8 : ℝ))
    (hR1 : 1 ≤ R) (hMN : M ≤ N) (hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N)
    (hlR : 1 + Real.log (R : ℝ) ≤ 2 * L / ℓ ^ 5)
    (hNM : (N : ℝ) / M ≤ 2 * (256 * Real.exp 2 + 4) * c)
    (hpoly5 : 2 * ℓ ^ 5 ≤ L ^ (1 / 4 : ℝ))
    (hSg : Sg₁ ≤ 2 * K_tot * ℓ) (hSg0 : 0 ≤ Sg₁)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 * K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L))
    (hsE : 128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (Real.log (N : ℝ) * k) +
      128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
        (Real.log (N : ℝ) * b * k) +
      32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤ 1 / 32)
    (hL8_U : 8 * (1024 * D * C_pr + 4096 * C_pr / g₀ +
      256 * C_np * (8 * K_res + 1560 * K_tot + 100) / g₀ +
      128 * D * C_up + 2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) + 1 ≤ L ^ (1 / 8 : ℝ)) :
    256 * C_pr * (1 + Real.log (R : ℝ)) / (Real.log (N : ℝ) * k) +
      256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (Real.log (N : ℝ) * b * k) +
      32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetG R N c Sg₁ +
        2 * bandFarBudgetA R N c) / (b * k) +
      128 * C_up * c ^ 2 * (1 + Real.log c) / k +
      128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) /
        (Real.log (N : ℝ) * b * k) ≤ 1 / 4 := by
  rw [← hLdef] at hsE ⊢
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hc_L8.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hR1R : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hRN
  have hlR0 : 0 ≤ 1 + Real.log (R : ℝ) := by linarith [Real.log_natCast_nonneg R]
  have hlR_2L : 1 + Real.log (R : ℝ) ≤ 2 * L :=
    hlR.trans (div_le_self (by positivity) (one_le_pow₀ hℓ1))
  have h1c_ℓ : 1 + Real.log c ≤ ℓ := by rw [hℓdef]; linarith [Real.log_le_log hc0 hcL]
  have h1c0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hℓ5_L14 : ℓ ^ 5 ≤ L ^ (1 / 4 : ℝ) := by linarith only [hpoly5, pow_pos hℓ0 5]
  have hℓ_L14 : ℓ ≤ L ^ (1 / 4 : ℝ) :=
    (by simpa only [pow_one] using pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 5)).trans hℓ5_L14
  have hℓ3_L14 : ℓ ^ 3 ≤ L ^ (1 / 4 : ℝ) :=
    (pow_le_pow_right₀ hℓ1 (by norm_num : 3 ≤ 5)).trans hℓ5_L14
  have h1c_L14 : 1 + Real.log c ≤ L ^ (1 / 4 : ℝ) := h1c_ℓ.trans hℓ_L14
  have h1c3_L14 : (1 + Real.log c) ^ 3 ≤ L ^ (1 / 4 : ℝ) :=
    (pow_le_pow_left₀ h1c0 h1c_ℓ 3).trans hℓ3_L14
  have hk_pos : 0 < k := by rw [hk_def]; positivity
  have hb_pos : 0 < b := by rw [hb_def]; positivity
  have hbk : b * k = g₀ * L / 8 := by
    rw [hb_def, hk_def]; field_simp [hD.ne', hℓ0.ne']; ring
  have hLbk : L * b * k = g₀ * L ^ 2 / 8 := by rw [mul_assoc, hbk]; ring
  have hLk : L * k = L ^ 2 / (2 * D * ℓ ^ 5) := by rw [hk_def]; ring
  have hk_lb : L ^ (3 / 4 : ℝ) / D ≤ k := by
    rw [hk_def, div_le_div_iff₀ hD (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hpoly5 (Real.rpow_nonneg hL0.le (3 / 4))
    have hsplit : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
    nlinarith only [hm, hsplit, hD]
  have hL8_pos : 0 < L ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hinvL_L8 : 1 / L ≤ 1 / L ^ (1 / 8 : ℝ) :=
    one_div_le_one_div_of_le hL8_pos
      ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hc2_14 : c ^ 2 ≤ L ^ (1 / 4 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 2
    exact hp.trans_eq (by congr 1; norm_num)
  have hc7_78 : c ^ 7 ≤ L ^ (7 / 8 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 7; push_cast at hp; exact hp
  have hc9_98 : c ^ 9 ≤ L ^ (9 / 8 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 9; push_cast at hp; exact hp
  have hc10_54 : c ^ 10 ≤ L ^ (5 / 4 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 10
    exact hp.trans_eq (by congr 1; norm_num)
  have hc11_118 : c ^ 11 ≤ L ^ (11 / 8 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 11; push_cast at hp; exact hp
  -- Extract the `2 * bandFarBudgetG` contribution (`≤ 1 / 16`) directly from `hsE ≤ 1 / 32`.
  have hU3G : 32 * c ^ 7 * C_np * (2 * bandFarBudgetG R N c Sg₁) / (b * k) ≤ 1 / 16 := by
    have hTPC0 : 0 ≤ terminalPacketCost R M N := terminalPacketCost_nonneg R hMN
    have he1_0 : 0 ≤ 128 * C_pr * (1 + Real.log (R : ℝ)) ^ 2 / (L * k) := by positivity
    have he2_0 : 0 ≤ 128 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) * terminalPacketCost R M N /
        (L * b * k) := by positivity
    linarith only [hsE, he1_0, he2_0,
      (by ring : 32 * c ^ 7 * C_np * (2 * bandFarBudgetG R N c Sg₁) / (b * k) =
        2 * (32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k)))]
  -- Bound the remaining five pieces by `O(L^(-1/8))`.
  have hU1 : 256 * C_pr * (1 + Real.log (R : ℝ)) / (L * k) ≤
      (1024 * D * C_pr) / L ^ (1 / 8 : ℝ) := by
    calc
      256 * C_pr * (1 + Real.log (R : ℝ)) / (L * k)
          ≤ 256 * C_pr * (2 * L / ℓ ^ 5) / (L ^ 2 / (2 * D * ℓ ^ 5)) := by
            rw [hLk]; exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlR (by positivity)) (by positivity)
      _ = (1024 * D * C_pr) * (1 / L) := by field_simp [hL0.ne', hD.ne', hℓ0.ne']; ring
      _ ≤ (1024 * D * C_pr) * (1 / L ^ (1 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hinvL_L8 (by positivity)
      _ = (1024 * D * C_pr) / L ^ (1 / 8 : ℝ) := by ring
  have hU2 : 256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (L * b * k) ≤
      (4096 * C_pr / g₀) / L ^ (1 / 8 : ℝ) := by
    have hsplit : L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
    calc
      256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (L * b * k)
          ≤ 256 * L ^ (7 / 8 : ℝ) * C_pr * (2 * L) / (g₀ * L ^ 2 / 8) := by
            rw [hLbk]
            exact div_le_div_of_nonneg_right
              (mul_le_mul (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hc7_78 (by norm_num)) hCpr.le) hlR_2L hlR0 (by positivity))
              (by positivity)
      _ = (4096 * C_pr / g₀) * (L ^ (7 / 8 : ℝ) / L) := by field_simp [hg₀.ne', hL0.ne']; ring
      _ = (4096 * C_pr / g₀) / L ^ (1 / 8 : ℝ) := by
          rw [← hsplit]; field_simp [hg₀.ne', hL8_pos.ne']
  have hβU : c ^ 7 * bandFarBudgetU R N c ρ Sg₁ / L ≤
      (8 * K_res + 1560 * K_tot + 98) / L ^ (1 / 8 : ℝ) := by
    have hsplit : c ^ 7 * bandFarBudgetU R N c ρ Sg₁ / L =
        ((1 + Real.log (R : ℝ)) / L) ^ 2 * (c ^ 7 * ρ / L) +
          (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) * (c ^ 9 / L ^ 2) +
          c ^ 11 * (1 + Real.log c) / L ^ 2 +
          c ^ 10 * (R : ℝ) ^ 2 / N := by
      unfold bandFarBudgetU; rw [← hLdef]; field_simp [hL0.ne']; ring
    rw [hsplit]
    have hlRL_sq : ((1 + Real.log (R : ℝ)) / L) ^ 2 ≤ 4 := by
      have h1 : (1 + Real.log (R : ℝ)) / L ≤ 2 := (div_le_iff₀ hL0).mpr hlR_2L
      exact (pow_le_pow_left₀ (by positivity) h1 2).trans_eq (by norm_num)
    have ht_ρ : ((1 + Real.log (R : ℝ)) / L) ^ 2 * (c ^ 7 * ρ / L) ≤
        8 * K_res / L ^ (1 / 8 : ℝ) := by
      have hnum : c ^ 9 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) ≤ L ^ (15 / 8 : ℝ) := by
        calc
          c ^ 9 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ)
              ≤ L ^ (9 / 8 : ℝ) * L ^ (1 / 4 : ℝ) * L ^ (1 / 16 : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hc9_98 h1c3_L14 (by positivity) (by positivity)) (by positivity)
          _ = L ^ (23 / 16 : ℝ) := by rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
          _ ≤ L ^ (15 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have hden : L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ 2 := by
        rw [← Real.rpow_add hL0]; norm_num [Real.rpow_two]
      have hρc7 : c ^ 7 * ρ / L ≤ 2 * K_res / L ^ (1 / 8 : ℝ) := by
        calc
          c ^ 7 * ρ / L
              ≤ c ^ 7 * (2 * K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L)) / L :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (by positivity)) hL0.le
          _ = 2 * K_res * ((c ^ 9 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ)) / L ^ 2) := by
            field_simp [hL0.ne']; ring
          _ ≤ 2 * K_res * (L ^ (15 / 8 : ℝ) / (L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ))) := by
            rw [← hden]
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hnum (by positivity)) (by positivity)
          _ = 2 * K_res / L ^ (1 / 8 : ℝ) := by
            field_simp [(Real.rpow_pos_of_pos hL0 _).ne']; ring
      calc
        ((1 + Real.log (R : ℝ)) / L) ^ 2 * (c ^ 7 * ρ / L)
            ≤ 4 * (2 * K_res / L ^ (1 / 8 : ℝ)) :=
          mul_le_mul hlRL_sq hρc7 (by positivity) (by norm_num)
        _ = 8 * K_res / L ^ (1 / 8 : ℝ) := by ring
    have ht_Sg : (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) * (c ^ 9 / L ^ 2) ≤
        (1560 * K_tot + 96) / L ^ (1 / 8 : ℝ) := by
      have hR15 : (R : ℝ) ^ 15 / N ≤ 1 := by
        rw [div_le_one hN0]
        have h1 : (R : ℝ) ^ 15 ≤ (R : ℝ) ^ 16 := pow_le_pow_right₀ hR1R (by norm_num)
        have h2 : (R : ℝ) ^ 16 ≤ L ^ 18 * (R : ℝ) ^ 16 :=
          le_mul_of_one_le_left (by positivity) (one_le_pow₀ hL1)
        linarith only [h1, h2, hRN]
      have h72 : 72 * (R : ℝ) ^ 15 / N ≤ 72 := by rw [mul_div_assoc]; linarith only [hR15]
      have hcoef : 24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N ≤
          (1560 * K_tot + 96) * L ^ (1 / 4 : ℝ) := by
        have h1 : 24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N ≤ (1560 * K_tot + 96) * ℓ := by
          linarith only [hSg, h72, hℓ1]
        exact h1.trans (mul_le_mul_of_nonneg_left hℓ_L14 (by positivity))
      have hnum : L ^ (1 / 4 : ℝ) * c ^ 9 ≤ L ^ (15 / 8 : ℝ) := by
        calc
          L ^ (1 / 4 : ℝ) * c ^ 9 ≤ L ^ (1 / 4 : ℝ) * L ^ (9 / 8 : ℝ) :=
            mul_le_mul_of_nonneg_left hc9_98 (by positivity)
          _ = L ^ (11 / 8 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
          _ ≤ L ^ (15 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have hden : L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ 2 := by
        rw [← Real.rpow_add hL0]; norm_num [Real.rpow_two]
      calc
        (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) * (c ^ 9 / L ^ 2)
            ≤ ((1560 * K_tot + 96) * L ^ (1 / 4 : ℝ)) * (c ^ 9 / L ^ 2) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = (1560 * K_tot + 96) * ((L ^ (1 / 4 : ℝ) * c ^ 9) / L ^ 2) := by ring
        _ ≤ (1560 * K_tot + 96) *
              (L ^ (15 / 8 : ℝ) / (L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ))) := by
          rw [← hden]
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum (by positivity)) (by positivity)
        _ = (1560 * K_tot + 96) / L ^ (1 / 8 : ℝ) := by
          field_simp [(Real.rpow_pos_of_pos hL0 _).ne']; ring
    have ht_11 : c ^ 11 * (1 + Real.log c) / L ^ 2 ≤ 1 / L ^ (1 / 8 : ℝ) := by
      have hnum : c ^ 11 * (1 + Real.log c) ≤ L ^ (15 / 8 : ℝ) := by
        calc
          c ^ 11 * (1 + Real.log c) ≤ L ^ (11 / 8 : ℝ) * L ^ (1 / 4 : ℝ) :=
            mul_le_mul hc11_118 h1c_L14 h1c0 (by positivity)
          _ = L ^ (13 / 8 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
          _ ≤ L ^ (15 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have hden : L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ 2 := by
        rw [← Real.rpow_add hL0]; norm_num [Real.rpow_two]
      calc
        c ^ 11 * (1 + Real.log c) / L ^ 2
            ≤ L ^ (15 / 8 : ℝ) / (L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ)) := by
          rw [← hden]; exact div_le_div_of_nonneg_right hnum (by positivity)
        _ = 1 / L ^ (1 / 8 : ℝ) := by field_simp [(Real.rpow_pos_of_pos hL0 _).ne']
    have ht_10 : c ^ 10 * (R : ℝ) ^ 2 / N ≤ 1 / L ^ (1 / 8 : ℝ) :=
      cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN hinvL_L8 (by norm_num) (by norm_num)
    linarith only [ht_ρ, ht_Sg, ht_11, ht_10,
      (by ring : (8 * K_res + 1560 * K_tot + 98) / L ^ (1 / 8 : ℝ) =
        8 * K_res / L ^ (1 / 8 : ℝ) + (1560 * K_tot + 96) / L ^ (1 / 8 : ℝ) +
          1 / L ^ (1 / 8 : ℝ) + 1 / L ^ (1 / 8 : ℝ))]
  have hβA : c ^ 7 * bandFarBudgetA R N c / L ≤ 1 / L ^ (1 / 8 : ℝ) := by
    have he : c ^ 7 * bandFarBudgetA R N c / L =
        (c ^ 9 * (R : ℝ) ^ 5 / N) * (1 / ((N : ℝ) * L ^ 2)) := by
      unfold bandFarBudgetA; rw [← hLdef]; field_simp [hN0.ne', hL0.ne']; ring
    rw [he]
    have h1 := cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN hinvL_L8
      (i := 9) (j := 5) (by norm_num) (by norm_num)
    have hN1R : (1 : ℝ) ≤ N :=
      le_trans (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hR1R)) hRN
    have h2 : 1 / ((N : ℝ) * L ^ 2) ≤ 1 :=
      (div_le_one (by positivity)).mpr (one_le_mul_of_one_le_of_one_le hN1R (one_le_pow₀ hL1))
    exact (mul_le_mul h1 h2 (by positivity) (by positivity)).trans_eq (mul_one _)
  have hU3UA : 32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) /
      (b * k) ≤ (256 * C_np * (8 * K_res + 1560 * K_tot + 100) / g₀) / L ^ (1 / 8 : ℝ) := by
    have hid : 32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) /
        (b * k) = (256 * C_np / g₀) *
          (c ^ 7 * bandFarBudgetU R N c ρ Sg₁ / L + 2 * (c ^ 7 * bandFarBudgetA R N c / L)) := by
      rw [hbk]; field_simp [hg₀.ne', hL0.ne']; ring
    rw [hid]
    have hsum : c ^ 7 * bandFarBudgetU R N c ρ Sg₁ / L +
        2 * (c ^ 7 * bandFarBudgetA R N c / L) ≤
        (8 * K_res + 1560 * K_tot + 100) / L ^ (1 / 8 : ℝ) := by
      linarith only [hβU, hβA,
        (by ring : (8 * K_res + 1560 * K_tot + 100) / L ^ (1 / 8 : ℝ) =
          (8 * K_res + 1560 * K_tot + 98) / L ^ (1 / 8 : ℝ) + 2 * (1 / L ^ (1 / 8 : ℝ)))]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)
  have hU4 : 128 * C_up * c ^ 2 * (1 + Real.log c) / k ≤
      (128 * D * C_up) / L ^ (1 / 8 : ℝ) := by
    have hnum : c ^ 2 * (1 + Real.log c) ≤ L ^ (5 / 8 : ℝ) := by
      calc
        c ^ 2 * (1 + Real.log c) ≤ L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) :=
          mul_le_mul hc2_14 h1c_L14 h1c0 (by positivity)
        _ = L ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
        _ ≤ L ^ (5 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hden : L ^ (5 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    calc
      128 * C_up * c ^ 2 * (1 + Real.log c) / k
          ≤ 128 * C_up * L ^ (5 / 8 : ℝ) / (L ^ (3 / 4 : ℝ) / D) :=
        (div_le_div_of_nonneg_right
          (by linarith only [mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ 128 * C_up),
            (by ring : 128 * C_up * (c ^ 2 * (1 + Real.log c)) =
              128 * C_up * c ^ 2 * (1 + Real.log c))]) hk_pos.le).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hk_lb)
      _ = (128 * D * C_up) * (L ^ (5 / 8 : ℝ) / (L ^ (5 / 8 : ℝ) * L ^ (1 / 8 : ℝ))) := by
        rw [← hden]; field_simp [hD.ne']; ring
      _ = (128 * D * C_up) / L ^ (1 / 8 : ℝ) := by
        field_simp [(Real.rpow_pos_of_pos hL0 _).ne']; ring
  have hU5 : 128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (L * b * k) ≤
      (2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) / L ^ (1 / 8 : ℝ) := by
    have hnum : ((N : ℝ) / M) * (c ^ 9 * (1 + Real.log c)) ≤
        2 * (256 * Real.exp 2 + 4) * L ^ (15 / 8 : ℝ) := by
      have hc10_1c : c ^ 10 * (1 + Real.log c) ≤ L ^ (15 / 8 : ℝ) := by
        calc
          c ^ 10 * (1 + Real.log c) ≤ L ^ (5 / 4 : ℝ) * L ^ (1 / 4 : ℝ) :=
            mul_le_mul hc10_54 h1c_L14 h1c0 (by positivity)
          _ = L ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
          _ ≤ L ^ (15 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      calc
        ((N : ℝ) / M) * (c ^ 9 * (1 + Real.log c))
            ≤ (2 * (256 * Real.exp 2 + 4) * c) * (c ^ 9 * (1 + Real.log c)) :=
          mul_le_mul_of_nonneg_right hNM (by positivity)
        _ = 2 * (256 * Real.exp 2 + 4) * (c ^ 10 * (1 + Real.log c)) := by ring
        _ ≤ 2 * (256 * Real.exp 2 + 4) * L ^ (15 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hc10_1c (by positivity)
    have hden : L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ 2 := by
      rw [← Real.rpow_add hL0]; norm_num [Real.rpow_two]
    calc
      128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (L * b * k)
          = (1024 * C_upT / g₀) * (((N : ℝ) / M) * (c ^ 9 * (1 + Real.log c)) / L ^ 2) := by
            rw [hLbk]; field_simp [hg₀.ne', hL0.ne']; ring
      _ ≤ (1024 * C_upT / g₀) *
            ((2 * (256 * Real.exp 2 + 4) * L ^ (15 / 8 : ℝ)) /
              (L ^ (15 / 8 : ℝ) * L ^ (1 / 8 : ℝ))) := by
          rw [← hden]
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum (by positivity)) (by positivity)
      _ = (2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) / L ^ (1 / 8 : ℝ) := by
          field_simp [hg₀.ne', (Real.rpow_pos_of_pos hL0 _).ne']; ring
  have hsplit3 : 32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ +
      2 * bandFarBudgetG R N c Sg₁ + 2 * bandFarBudgetA R N c) / (b * k) =
      32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) / (b * k) +
        32 * c ^ 7 * C_np * (2 * bandFarBudgetG R N c Sg₁) / (b * k) := by ring
  rw [hsplit3]
  have h5_le :
      256 * C_pr * (1 + Real.log (R : ℝ)) / (L * k) +
        256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (L * b * k) +
        32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetA R N c) / (b * k) +
        128 * C_up * c ^ 2 * (1 + Real.log c) / k +
        128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (L * b * k) ≤ 1 / 8 := by
    calc
      _ ≤ (1024 * D * C_pr + 4096 * C_pr / g₀ +
            256 * C_np * (8 * K_res + 1560 * K_tot + 100) / g₀ +
            128 * D * C_up + 2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) /
              L ^ (1 / 8 : ℝ) := by
          linarith only [hU1, hU2, hU3UA, hU4, hU5,
            (by ring : (1024 * D * C_pr + 4096 * C_pr / g₀ +
                256 * C_np * (8 * K_res + 1560 * K_tot + 100) / g₀ +
                128 * D * C_up + 2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) / L ^ (1 / 8 : ℝ) =
              (1024 * D * C_pr) / L ^ (1 / 8 : ℝ) +
                (4096 * C_pr / g₀) / L ^ (1 / 8 : ℝ) +
                (256 * C_np * (8 * K_res + 1560 * K_tot + 100) / g₀) / L ^ (1 / 8 : ℝ) +
                (128 * D * C_up) / L ^ (1 / 8 : ℝ) +
                (2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) / L ^ (1 / 8 : ℝ))]
      _ ≤ 1 / 8 := by rw [div_le_iff₀ hL8_pos]; linarith only [hL8_U]
  linarith only [h5_le, hU3G]

/-! ### 4. Band 0 / Band 1 scalars and three-band collar-reserve assembly on the upper band -/

private lemma critical_band0_band1_scalars {N Q₁ R₀ : ℕ}
    {c L Lh κ₀ C_small0 C_coerc0 C_band1 C_cross01 : ℝ}
    (hc1 : 1 ≤ c) (hc_L8 : c ≤ L ^ (1 / 8 : ℝ)) (hL1 : 1 ≤ L) (hLh_eq : Lh = L ^ (1 / 2 : ℝ))
    (hκ₀ : 0 < κ₀) (hC_small0 : 0 < C_small0) (hC_cross01 : 0 < C_cross01)
    (hVc : 1 + Real.log c ≤ L ^ (1 / 128 : ℝ))
    (hsqrtQ : (1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2) ≤ Real.sqrt Q₁)
    (hlogQ_lb : (13 / 32 : ℝ) * Real.log L - 1 ≤ Real.log (Q₁ : ℝ))
    (hH₀_ub : 1 + Real.log (R₀ : ℝ) ≤ 2 * Lh)
    (hlogR₀_lb : Lh - 1 ≤ Real.log (R₀ : ℝ))
    (hR₀_tail : (R₀ : ℝ) * Real.sqrt (L / N) ≤ 1 / L)
    (hc5N : c ^ 5 * L / N ≤ 1 / L)
    (hc3R₀4 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ 1 / L)
    (hc3R₀2 : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / N) ≤ 1 / L)
    (hν_b1 : C_small0 * 18 ≤ L ^ (1 / 128 : ℝ))
    (hν_b2 : C_cross01 * 4 ≤ L ^ (1 / 128 : ℝ))
    (hν_b6 : 32 * C_band1 ≤ L ^ (1 / 128 : ℝ))
    (hll_scaled : κ₀ + 4 + C_coerc0 + 3 / 4 ≤ (23 / 128 : ℝ) * Real.log L)
    (hL_Lh_gap : (8 * (κ₀ + 3)) ^ 2 ≤ L) :
    C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 ∧
    C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 ∧
    κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 ∧
    κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := by rw [hLh_eq]; exact Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by
    rw [hLh_eq, ← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlc_ge1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hlc_nn : 0 ≤ 1 + Real.log c := zero_le_one.trans hlc_ge1
  set ν : ℝ := 1 / 128
  have hLν0 : 0 ≤ L ^ ν := Real.rpow_nonneg hL0.le _
  have hLmν0 : 0 ≤ L ^ (-ν) := Real.rpow_nonneg hL0.le _
  have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have h1_invL : 1 / L ≤ L ^ (-ν) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num [ν])
  have h1_invLh : 1 / Lh ≤ L ^ (-ν) := by
    rw [hLh_eq, one_div, ← Real.rpow_neg hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num [ν])
  have hH₀_div : (1 + Real.log (R₀ : ℝ)) / L ≤ 2 / Lh := by
    rw [div_le_div_iff₀ hL0 hLh0]
    calc
      (1 + Real.log (R₀ : ℝ)) * Lh ≤ (2 * Lh) * Lh := mul_le_mul_of_nonneg_right hH₀_ub hLh0.le
      _ = 2 * (Lh * Lh) := by ring
      _ = 2 * L := by rw [hLh_sq]
  have hc2_vc_Lh : c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (-ν) := by
    have h1 := monomial_le_rpow hL1 hc0.le hc_L8 hlc_nn hVc 2 1 (2 * (1 / 8) + ν)
      (by push_cast; norm_num [ν])
    rw [pow_one] at h1
    calc c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (2 * (1 / 8) + ν) / L ^ (1 / 2 : ℝ) := by
          rw [← hLh_eq]; exact div_le_div_of_nonneg_right h1 hLh0.le
      _ ≤ L ^ (-ν) := rpow_div_rpow_le hL1 (by norm_num [ν])
  have hc2_vc_L : c ^ 2 * (1 + Real.log c) / L ≤ L ^ (-ν) :=
    (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg c) hlc_nn) hLh0
      (by nlinarith only [hLh1, hLh_sq])).trans hc2_vc_Lh
  have hc4_vc : c ^ 4 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
    have h1 := monomial_le_rpow hL1 hc0.le hc_L8 hlc_nn hVc 4 1 (4 * (1 / 8) + ν)
      (by push_cast; norm_num [ν])
    rw [pow_one] at h1
    calc c ^ 4 * (1 + Real.log c) / L ≤ L ^ (4 * (1 / 8) + ν) / L ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact div_le_div_of_nonneg_right h1 hL0.le
      _ ≤ L ^ (-ν) := rpow_div_rpow_le hL1 (by norm_num [ν])
  have hout1 : C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have hmid_Q₁ : c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤ 2 * L ^ (-ν) := by
      have hc32 : c * Real.sqrt c ≤ L ^ (3 / 16 : ℝ) := by
        have hsq : (c * Real.sqrt c) ^ 2 ≤ (L ^ (3 / 16 : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc0.le, show c ^ 2 * c = c ^ 3 by ring,
            ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le]
          have h3 := monomial_le_rpow hL1 hc0.le hc_L8 hlc_nn hVc 3 0 (3 / 8)
            (by push_cast; norm_num)
          rw [pow_zero, mul_one] at h3
          exact h3.trans_eq (by congr 1; norm_num)
        have hp1 : 0 ≤ c * Real.sqrt c := mul_nonneg hc0.le (Real.sqrt_nonneg c)
        have hp2 : 0 ≤ L ^ (3 / 16 : ℝ) := Real.rpow_nonneg hL0.le _
        nlinarith only [hsq, hp1, hp2]
      have hden_pos : 0 < (1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2) :=
        mul_pos (by norm_num) (Real.rpow_pos_of_pos hL0 _)
      calc
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤
            (L ^ (3 / 16 : ℝ) * L ^ ν) / ((1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2)) :=
          (div_le_div_of_nonneg_right
            (mul_le_mul hc32 hVc hlc_nn (Real.rpow_nonneg hL0.le _))
            (Real.sqrt_nonneg _)).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg (Real.rpow_nonneg hL0.le _) hLν0) hden_pos hsqrtQ)
        _ = 2 * L ^ ((3 / 16 : ℝ) + ν - (13 / 32 : ℝ) / 2) := by
          rw [show (L ^ (3 / 16 : ℝ) * L ^ ν) / ((1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2)) =
            2 * ((L ^ (3 / 16 : ℝ) * L ^ ν) / L ^ ((13 / 32 : ℝ) / 2)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_sub hL0]
        _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num [ν])) zero_le_two
    have ht4 : c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L ≤ 2 * L ^ (-ν) := by
      calc
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L =
            c ^ 2 * (1 + Real.log c) * ((1 + Real.log R₀) / L) := by ring
        _ ≤ c ^ 2 * (1 + Real.log c) * (2 / Lh) :=
          mul_le_mul_of_nonneg_left hH₀_div (mul_nonneg (sq_nonneg c) hlc_nn)
        _ = 2 * (c ^ 2 * (1 + Real.log c) / Lh) := by ring
        _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left hc2_vc_Lh zero_le_two
    have hlogR₀_nn : 0 ≤ 1 + Real.log (R₀ : ℝ) := by linarith [Real.log_natCast_nonneg R₀]
    have ht1 : c * (1 + Real.log c) * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) := by
      have hm : c * (1 + Real.log c) ≤ c ^ 2 * (1 + Real.log c) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hc1]) hlc_nn
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm hlogR₀_nn) hL0.le).trans
        ((by ring : c ^ 2 * (1 + Real.log c) * (1 + Real.log R₀) / L =
          c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L).trans_le ht4)
    have ht2 : c * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc0.le hlc_ge1) hlogR₀_nn) hL0.le).trans ht1
    have ht3 : c ^ 2 / L ≤ L ^ (-ν) :=
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg c) hlc_ge1) hL0.le).trans
        hc2_vc_L
    have ht5 : c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) ≤ L ^ (-ν) := by
      calc
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) = c ^ 2 * ((R₀ : ℝ) * Real.sqrt (L / N)) := by ring
        _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR₀_tail (sq_nonneg c)
        _ = c ^ 2 / L := by ring
        _ ≤ L ^ (-ν) := ht3
    have ht6 : c ^ 5 * L / N ≤ L ^ (-ν) := hc5N.trans h1_invL
    have ht8 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ L ^ (-ν) := hc3R₀4.trans h1_invL
    have hsum18 : c * (1 + Real.log c) * (1 + Real.log R₀) / L +
        c * (1 + Real.log R₀) / L + c ^ 2 / L +
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
        c ^ 5 * L / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
        c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L ≤ 18 * L ^ (-ν) := by
      linarith only [ht1, ht2, ht3, ht4, ht5, ht6, hmid_Q₁, ht8, hc2_vc_L, hLmν0]
    calc
      _ ≤ C_small0 * (18 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum18 hC_small0.le
      _ = (C_small0 * 18) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b1 hLmν0
      _ = 1 := hmul_ν
  have hout2 : C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 := by
    have hc3_N : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ L ^ (-ν) := hc3R₀2.trans h1_invL
    have hsum4 : 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ 4 * L ^ (-ν) := by
      linarith only [h1_invLh, hc2_vc_Lh, hc4_vc, hc3_N]
    calc
      _ ≤ C_cross01 * (4 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum4 hC_cross01.le
      _ = (C_cross01 * 4) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b2 hLmν0
      _ = 1 := hmul_ν
  have hout3 : κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 := by
    have hlogc : Real.log c ≤ (1 / 8 : ℝ) * Real.log L :=
      (Real.log_le_log hc0 hc_L8).trans_eq (Real.log_rpow hL0 (1 / 8))
    have hq_scaled : (39 / 128 : ℝ) * Real.log L - 3 / 4 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hlogQ_lb (by norm_num : (0 : ℝ) ≤ 3 / 4)
      linarith only [hm]
    linarith only [hlogc, hq_scaled, hll_scaled]
  have hout4 : κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
    have hc2_Lh : C_band1 * c ^ 2 * (1 + Real.log c) ≤ Lh / 32 := by
      have h1 : (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ 1 := by
        calc
          (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ L ^ ν * L ^ (-ν) :=
            mul_le_mul hν_b6 hc2_vc_Lh
              (div_nonneg (mul_nonneg (sq_nonneg c) hlc_nn) hLh0.le) hLν0
          _ = 1 := hmul_ν
      have hm := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ Lh / 32)
      have hid : (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) * (Lh / 32) =
          C_band1 * c ^ 2 * (1 + Real.log c) := by field_simp
      linarith only [hm, hid]
    have hLh_lb : 8 * (κ₀ + 3) ≤ Lh := by
      have hsq : (8 * (κ₀ + 3)) ^ 2 ≤ Lh ^ 2 := by rw [sq Lh, hLh_sq]; exact hL_Lh_gap
      have hp : 0 ≤ 8 * (κ₀ + 3) := by linarith only [hκ₀]
      nlinarith only [hsq, hp, hLh0]
    linarith only [hlogR₀_lb, hc2_Lh, hLh_lb, hκ₀]
  exact ⟨hout1, hout2, hout3, hout4⟩

private lemma complement_three_band_collar_reserve_assembly
    {Q₁ R₀ R₁ N : ℕ} {c b k₁ L Lh g₀ κ₀ C_coerc0 C_band1 : ℝ}
    (hQ2 : 2 ≤ Q₁) (hQR₀ : Q₁ ≤ R₀) (hc1 : 1 ≤ c) (hκ₀ : 0 < κ₀)
    (hbk : b * k₁ = g₀ * L / 8)
    (hband0 : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace Q₁ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₀ a₀ +
        ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) *
          ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N))
    (hband1 : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace R₀ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
        ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) *
          ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N))
    (hband2 : ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      w ∈ (conductorSubspace R₁ N)ᗮ →
      (k₁ / 4) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (g₀ * L / (16 * c ^ 7)) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
        completeWeilEnergy tiltedUnitSpline c N w)
    (hcr01_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {u₁ : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u₁ ∈ (conductorSubspace R₀ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), u₁⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2)
    (hcr0w_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k₁ / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hcr1w_fn : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₁ a₁ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k₁ / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hfl0 : κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0)
    (hfl1 : κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c))
    (hP_debit : g₀ * L / (128 * c ^ 7) ≤ k₁ / 32)
    (hP_floor : κ₀ + 2 ≤ k₁ / 32)
    (hS_floor : κ₀ + 2 ≤ g₀ * L / (64 * c ^ 7))
    {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu₀_mem : u₀ ∈ conductorSubspace R₀ N) (hu₀_orthQ : u₀ ∈ (conductorSubspace Q₁ N)ᗮ)
    (hu₁_mem : u₁ ∈ conductorSubspace R₁ N) (hu₁_orthR₀ : u₁ ∈ (conductorSubspace R₀ N)ᗮ)
    (hw_orthR₁ : w ∈ (conductorSubspace R₁ N)ᗮ) :
    (κ₀ + 3) * ‖u₀‖ ^ 2 + (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 + (κ₀ + 2) * ‖w‖ ^ 2 +
        (k₁ / 8) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (g₀ * L / (32 * c ^ 7)) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  obtain ⟨a₀, -, ha₀⟩ := (mem_conductorSubspace_iff (M := R₀) (N := N) (x := u₀)).mp hu₀_mem
  obtain ⟨a₁, -, ha₁⟩ := (mem_conductorSubspace_iff (M := R₁) (N := N) (x := u₁)).mp hu₁_mem
  have hu₀_1 : u₀ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₀_orthQ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hQ2) N hv)
  have hu₁_1 : u₁ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₁_orthR₀ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hR₀2) N hv)
  have hdiag0 := hband0 a₀ (ha₀.symm ▸ hu₀_orthQ)
  rw [← ha₀] at hdiag0
  have hdiag1 := hband1 a₁ (ha₁.symm ▸ hu₁_orthR₀)
  rw [← ha₁] at hdiag1
  have hdiag2 := hband2 hw_orthR₁
  have hcr01 := hcr01_fn a₀ (ha₀.symm ▸ hu₀_1) hu₁_orthR₀
  rw [← ha₀] at hcr01
  have hcr0w := hcr0w_fn a₀ (ha₀.symm ▸ hu₀_1) hw_orthR₁
  rw [← ha₀] at hcr0w
  have hcr1w := hcr1w_fn a₁ (ha₁.symm ▸ hu₁_1) hw_orthR₁
  rw [← ha₁] at hcr1w
  have hPw0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hSw0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hSw_S7 : (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
      topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) :=
    sum_sq_Ioc_le_topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w)
  have hS7_0 : 0 ≤ topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) :=
    hSw0.trans hSw_S7
  have hw_split : ‖w‖ ^ 2 =
      (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) := by
    rw [← sum_primeHorizonExtension_sq w,
      Ioc_eq_Icc_sdiff_Icc_telescoped (N / linearDefectCutoff c) N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl (Nat.div_le_self N _))).symm
  generalize (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) = P_w at
    hdiag2 hcr0w hcr1w hPw0 hw_split ⊢
  generalize (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) = S_w at
    hcr0w hcr1w hSw0 hSw_S7 hw_split
  generalize topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) = S7_w at
    hdiag2 hSw_S7 hS7_0 ⊢
  have hfloor0 : (κ₀ + 3) * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 ≤
      ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) * ‖u₀‖ ^ 2 := by
    rw [show (κ₀ + 3) * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 = (κ₀ + 3 + 1 / 2) * ‖u₀‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl0 (sq_nonneg ‖u₀‖)
  have hfloor1 : (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 +
      (1 / 4 : ℝ) * ‖u₁‖ ^ 2 ≤
      ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 := by
    rw [show (κ₀ + 2 + Lh / 32) * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 +
      (1 / 4 : ℝ) * ‖u₁‖ ^ 2 = (κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4) * ‖u₁‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl1 (sq_nonneg ‖u₁‖)
  have hbk_eq : b * k₁ / (32 * c ^ 7) = g₀ * L / (256 * c ^ 7) := by
    rw [hbk]; field_simp [hc0.ne']; ring
  rw [hbk_eq] at hcr0w hcr1w
  have hfloor2 : (κ₀ + 2) * ‖w‖ ^ 2 + (k₁ / 8) * P_w + (g₀ * L / (32 * c ^ 7)) * S7_w ≤
      (k₁ / 4) * P_w + (g₀ * L / (16 * c ^ 7)) * S7_w -
        2 * ((k₁ / 32) * P_w + (g₀ * L / (256 * c ^ 7)) * S_w +
          (g₀ * L / (256 * c ^ 7)) * ‖w‖ ^ 2) := by
    rw [hw_split]
    have hP_rem : (κ₀ + 2) * P_w + (k₁ / 8) * P_w ≤
        (3 * k₁ / 16 - g₀ * L / (128 * c ^ 7)) * P_w := by
      rw [show (κ₀ + 2) * P_w + (k₁ / 8) * P_w = (κ₀ + 2 + k₁ / 8) * P_w by ring]
      exact mul_le_mul_of_nonneg_right (by linarith only [hP_debit, hP_floor]) hPw0
    have hS_rem : (κ₀ + 2) * S_w ≤ (g₀ * L / (64 * c ^ 7)) * S_w :=
      mul_le_mul_of_nonneg_right hS_floor hSw0
    have h0 : 0 ≤ g₀ * L / (64 * c ^ 7) := by linarith only [hS_floor, hκ₀]
    have hS_7 : (g₀ * L / (64 * c ^ 7)) * S_w ≤ (g₀ * L / (64 * c ^ 7)) * S7_w :=
      mul_le_mul_of_nonneg_left hSw_S7 h0
    have hid32 : (g₀ * L / (32 * c ^ 7)) * S7_w =
        (g₀ * L / (64 * c ^ 7)) * S7_w + (g₀ * L / (64 * c ^ 7)) * S7_w := by
      field_simp [hc0.ne']; ring
    have hid16 : (g₀ * L / (16 * c ^ 7)) * S7_w =
        (g₀ * L / (32 * c ^ 7)) * S7_w + (g₀ * L / (32 * c ^ 7)) * S7_w := by
      field_simp [hc0.ne']; ring
    have hident :
        (k₁ / 4) * P_w + (g₀ * L / (16 * c ^ 7)) * S7_w -
          2 * ((k₁ / 32) * P_w + (g₀ * L / (256 * c ^ 7)) * S_w +
            (g₀ * L / (256 * c ^ 7)) * (P_w + S_w)) =
        (3 * k₁ / 16 - g₀ * L / (128 * c ^ 7)) * P_w +
          (g₀ * L / (16 * c ^ 7)) * S7_w - (g₀ * L / (64 * c ^ 7)) * S_w := by
      field_simp [hc0.ne']; ring
    rw [hident, mul_add]
    linarith only [hP_rem, hS_rem, hS_7, hid32, hid16]
  have h3add := completeWeilEnergy_three_add_ge tiltedUnitSpline c u₀ u₁ w
  have hE₀_0 : 0 ≤ primeAdjunctionMass R₀ a₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hE₁_0 : 0 ≤ primeAdjunctionMass R₁ a₁ := primeAdjunctionMass_nonneg R₁ a₁
  linarith only [h3add, hdiag0, hdiag1, hdiag2, hcr01, hcr0w, hcr1w,
    hfloor0, hfloor1, hfloor2, hE₀_0, hE₁_0]

private lemma exists_complement_collar_reserves_upper_band :
    ∃ K₁_far : ℝ, 0 < K₁_far ∧ 2 * K₁_far ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, Real.log (N : ℝ) ^ (1 / 16 : ℝ) ≤ c →
          c ≤ 2 * K₁_far * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          ∀ {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
            u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N →
            u₀ ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ N)ᗮ →
            u₁ ∈ conductorSubspace (subexpCutoff N) N →
            u₁ ∈ (conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N)ᗮ →
            w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ →
            (tiltedSplineSpectralFloorConstant + 3) * ‖u₀‖ ^ 2 +
                (tiltedSplineSpectralFloorConstant + 2 + Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) *
                  ‖u₁‖ ^ 2 +
                (tiltedSplineSpectralFloorConstant + 2) * ‖w‖ ^ 2 +
                ((Real.log (N : ℝ) /
                    (2 * explicitConductorCutoffConstant *
                      (1 + Real.log (Real.log (N : ℝ))) ^ 5)) / 8) *
                  (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
                (dyadicTopMassConstant * Real.log (N : ℝ) / (32 * c ^ 7)) *
                  topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
              completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) := by
  obtain ⟨K₁_far, hK₁_pos, h2K₁_le1, hfar_ev⟩ := exists_critical_multiple_far_reserve
  obtain ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, hcross_shape⟩ :=
    exists_band_far_cross_le_reserve_shape
  obtain ⟨C_cross01, hC_cross01, hcross01⟩ := exists_band0_band1_cross_le
  obtain ⟨C_coerc0, C_small0, hC_coerc0, hC_small0, hcoerc0⟩ :=
    exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
  obtain ⟨C_band1, hC_band1, hcoerc1⟩ := exists_band1_coercive_homogeneous
  obtain ⟨K_res, hK_res, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  obtain ⟨K_tot, hK_tot, htot⟩ := exists_div_totient_le_loglog
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  obtain ⟨D, hDdef⟩ : ∃ D, D = explicitConductorCutoffConstant := ⟨_, rfl⟩
  obtain ⟨g₀, hg₀def⟩ : ∃ g₀, g₀ = dyadicTopMassConstant := ⟨_, rfl⟩
  obtain ⟨κ₀, hκ₀def⟩ : ∃ κ₀, κ₀ = tiltedSplineSpectralFloorConstant := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  rw [← hg₀def] at hg₀ ⊢
  rw [← hκ₀def] at hκ₀ ⊢
  refine ⟨K₁_far, hK₁_pos, h2K₁_le1, ?_⟩
  obtain ⟨CB, hCBdef⟩ : ∃ CB : ℝ, CB = 4 + Real.log (2 * (256 * Real.exp 2 + 4)) + 1 := ⟨_, rfl⟩
  have hCB0 : 0 ≤ CB := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (256 * Real.exp 2 + 4) by
      nlinarith only [Real.exp_pos 2])
    rw [hCBdef]; linarith only [this]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [hfar_ev 5 (by positivity : 0 < 1 / (16 * D)),
    eventually_three_cutoff_bounds_one_ninth (by norm_num : (0 : ℝ) < 13 / 32)
      (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) < 1 / 4096) le_rfl,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1 / 4) 2),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 128) 1),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 128)).comp hLlim).eventually_ge_atTop
      (max (max (C_small0 * 18) (C_cross01 * 4)) (32 * C_band1)),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hLlim).eventually_ge_atTop
      (4 * D + 4),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim).eventually_ge_atTop
      (8 * (1024 * D * C_pr + 4096 * C_pr / g₀ +
        256 * C_np * (8 * K_res + 1560 * K_tot + 100) / g₀ +
        128 * D * C_up + 2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) + 1),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim).eventually_ge_atTop
      (max (max (g₀ * D / 4) (32 * D * (κ₀ + 2))) (64 * (κ₀ + 2) / g₀)),
    hllim.eventually_ge_atTop ((κ₀ + 4 + C_coerc0 + 3 / 4) / (23 / 128)),
    hllim.eventually_ge_atTop (56 * CB / (D * g₀)),
    hllim.eventually_ge_atTop (128 * (1024 * D * C_pr + 2048 * C_pr * CB / g₀ +
      512 * C_np * (4 * K_tot ^ 2 + 3) / g₀)),
    hLlim.eventually_ge_atTop (max 3000 ((8 * (κ₀ + 3)) ^ 2)),
    hres 0 le_rfl 16 (by norm_num),
    eventually_ge_atTop 3] with
      N hfarN hcut hLX hpoly5 hpoly128 hν_max hL34_D hL8_U hL8_floors
      hll_fl0 hll_leak hll_E hL_max hresN hN3
  dsimp only [Function.comp_def] at hpoly5 hpoly128 hν_max hL34_D hL8_U hL8_floors
    hll_fl0 hll_leak hll_E hL_max
  rw [← hg₀def] at hfarN
  intro c hc_lo hc_hi u₀ u₁ w hu₀_mem hu₀_orthQ hu₁_mem hu₁_orthR₀ hw
  have hL3000 : 3000 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
  have hL_Lh_gap : (8 * (κ₀ + 3)) ^ 2 ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL_max
  have hL2 : 2 ≤ Real.log (N : ℝ) := by linarith only [hL3000]
  have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hL3000]
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by omega
  have hc1 : 1 ≤ c := (Real.one_le_rpow hL1 (by norm_num)).trans hc_lo
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc_L8 : c ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
    hc_hi.trans ((mul_le_mul_of_nonneg_right h2K₁_le1 (by positivity)).trans_eq (one_mul _))
  have hc8_le : c ^ 8 ≤ Real.log (N : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 8
    exact hp.trans_eq (by push_cast; norm_num [Real.rpow_one])
  have hcL : c ≤ Real.log (N : ℝ) :=
    hc_L8.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one _))
  obtain ⟨hQ2, hQR₀, -, -, hsqrtQ, hlogQ_lb, hH₀_ub, hlogR₀_lb, h36_R₀, -, -, -⟩ := hcut
  obtain ⟨hR₀R₁, h1_R₁, h1080_R₁, hgap_lo, hgap_hi, hRN₁⟩ :=
    subexpCutoff_bounds hD hN1 hL3000 hLX hpoly5 hL34_D
  have hR₀2 : 2 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ := hQ2.trans hQR₀
  have hR₁2 : 2 ≤ subexpCutoff N := hR₀2.trans hR₀R₁
  have h36_R₁ : 36 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N : ℝ) := by
    linarith only [h1080_R₁, Real.log_natCast_nonneg (subexpCutoff N)]
  have h18_R₀ : 18 * (1 + Real.log (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ)) ≤
      Real.log (N : ℝ) := by
    linarith only [h36_R₀, Real.log_natCast_nonneg ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊]
  have h18_R₁ : 18 * (1 + Real.log (subexpCutoff N : ℝ)) ≤ Real.log (N : ℝ) := by
    linarith only [h1080_R₁, Real.log_natCast_nonneg (subexpCutoff N)]
  obtain ⟨hcutN, hwidth, hw1, hrad, hR₀6, hsize_near0, hsize_up0, hR₀_tail, hc5N, hc3R₀4, hc3R₀2,
    -⟩ := rpow_horizon_N_bounds_one_ninth hN1 hR₀2 hc1 (by linarith only [hL3000]) hLX hcL h36_R₀
  obtain ⟨-, -, -, -, hR₁6, hsize_near1, hsize_up1, hR₁_tail, -, -, -, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₁2 hc1 (by linarith only [hL3000]) hLX hcL h36_R₁
  obtain ⟨hRM0, -, hB0_ub, -⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₀2 hc1 hL3000 hLX hcL h36_R₀
  obtain ⟨hRM1, hlogM1, hB1_ub, hhalf_M⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₁2 hc1 hL3000 hLX hcL h36_R₁
  rw [← hCBdef] at hB0_ub hB1_ub
  have hM2 : 2 ≤ N / linearDefectCutoff c := (by omega : 2 ≤ subexpCutoff N * subexpCutoff N).trans hRM1
  have hM1 : 1 ≤ N / linearDefectCutoff c := by omega
  have h1c_ℓ : 1 + Real.log c ≤ 1 + Real.log (Real.log (N : ℝ)) := by
    linarith [Real.log_le_log hc0 hcL]
  have hℓ_leak : 56 * CB / (D * g₀) ≤ 1 + Real.log (Real.log (N : ℝ)) := by
    linarith only [hll_leak]
  have hband2 : ∀ {w' : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      w' ∈ (conductorSubspace (subexpCutoff N) N)ᗮ →
      (Real.log (N : ℝ) / (2 * D * (1 + Real.log (Real.log (N : ℝ))) ^ 5) / 4) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w' n ^ 2) +
        (g₀ * Real.log (N : ℝ) / (16 * c ^ 7)) *
          topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w') ≤
        completeWeilEnergy tiltedUnitSpline c N w' := fun hw' =>
    subexp_far_collar_reserve hDdef hD hg₀ hCB0 hc1 hc8_le hL2 hR₁2 hM2 hRM1 hlogM1 hhalf_M
      hB1_ub h1c_ℓ hgap_lo hgap_hi hℓ_leak (hfarN c hc1 hc_hi) hw'
  -- Band 0 and Band 1 scalar smallness and floors
  have hpoly128' : 1 + Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) := by
    simpa only [one_mul, pow_one] using hpoly128
  have hVc : 1 + Real.log c ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) := h1c_ℓ.trans hpoly128'
  have hν_b1 : C_small0 * 18 ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hν_max
  have hν_b2 : C_cross01 * 4 ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hν_max
  have hν_b6 : 32 * C_band1 ≤ Real.log (N : ℝ) ^ (1 / 128 : ℝ) :=
    (le_max_right _ _).trans hν_max
  have hll_scaled : κ₀ + 4 + C_coerc0 + 3 / 4 ≤
      (23 / 128 : ℝ) * Real.log (Real.log (N : ℝ)) :=
    ((div_le_iff₀ (by norm_num : (0 : ℝ) < 23 / 128)).mp hll_fl0).trans_eq (mul_comm _ _)
  obtain ⟨hsmall_band0, hsmall_cross01, hfl0, hfl1⟩ :=
    critical_band0_band1_scalars hc1 hc_L8 hL1 rfl hκ₀ hC_small0 hC_cross01 hVc hsqrtQ hlogQ_lb
      hH₀_ub hlogR₀_lb hR₀_tail hc5N hc3R₀4 hc3R₀2 hν_b1 hν_b2 hν_b6 hll_scaled hL_Lh_gap
  -- Band–far cross terms at `R₀` and `subexpCutoff N`
  set L := Real.log (N : ℝ) with hL_eq
  set ℓ := 1 + Real.log L with hℓ_eq
  set k₁ := L / (2 * D * ℓ ^ 5) with hk₁_eq
  set b := (g₀ * D / 4) * ℓ ^ 5 with hb_eq
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ_eq]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hk₁_pos : 0 < k₁ := by rw [hk₁_eq]; positivity
  have hb_pos : 0 < b := by rw [hb_eq]; positivity
  have hbk : b * k₁ = g₀ * L / 8 := by rw [hb_eq, hk₁_eq]; field_simp [hD.ne', hℓ0.ne']; ring
  have hRN₀ : L ^ 18 * (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ) ^ 16 ≤ N := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hRN₁
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hR₀R₁) 16
  obtain ⟨hceil0, hRK0, h8c, hc4⟩ :=
    near_ceil_side_conditions (by omega : 1 ≤ ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊) hc1 hcL
      (by linarith only [hL3000]) hRN₀
  obtain ⟨hceil1, hRK1, -, -⟩ :=
    near_ceil_side_conditions (by omega : 1 ≤ subexpCutoff N) hc1 hcL
      (by linarith only [hL3000]) hRN₁
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hNM : (N : ℝ) / (N / linearDefectCutoff c : ℕ) ≤ 2 * (256 * Real.exp 2 + 4) * c := by
    have h1 := nat_div_div_le_two_mul (by omega : 1 ≤ linearDefectCutoff c) hcutN
    linarith only [h1, hTup]
  set Sg₁ := K_tot * (1 + Real.log (1 + Real.log (subexpCutoff N : ℝ))) with hSg₁_eq
  have hSg1 : 1 ≤ Sg₁ := by
    have : 0 ≤ Real.log (1 + Real.log (subexpCutoff N : ℝ)) :=
      Real.log_nonneg (by linarith [Real.log_natCast_nonneg (subexpCutoff N)])
    rw [hSg₁_eq]; exact one_le_mul_of_one_le_of_one_le hK_tot (by linarith only [this])
  have hSg_ub : Sg₁ ≤ 2 * K_tot * ℓ := by
    rw [hSg₁_eq, hℓ_eq]
    exact loglog_budget_le (by linarith only [hK_tot]) hL1
      (by linarith only [h1080_R₁, Real.log_natCast_nonneg (subexpCutoff N)])
  set ρ := K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (16 : ℕ)) / L +
      c ^ 10 * (L / N) ^ 2) with hρ_eq
  have hρ_norm : ‖poleModeResidual c N‖ ^ 2 ≤ ρ := by
    have h := hresN 1 one_pos (by simp) c hc1 hwidth
    simpa only [poleModeResidual, Nat.cast_one, Real.log_one, add_zero, one_pow, one_mul,
      mul_one, hρ_eq, hL_eq] using h
  have hL11 : L ^ 11 ≤ N := by
    refine le_trans ?_ hRN₁
    have h1 : L ^ 11 ≤ L ^ 18 := pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (subexpCutoff N : ℝ) ^ 16 :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ subexpCutoff N by omega))
    exact h1.trans (le_mul_of_one_le_right (by positivity) h2)
  have hρ_ub : ρ ≤ 2 * K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L) := by
    rw [hρ_eq]
    exact pole_rate_le hK_res.le hc1 hcL hL1 (k := 16) (by norm_num) (by push_cast; norm_num) hL11
  have hρ0 : 0 ≤ ρ := (sq_nonneg _).trans hρ_norm
  have h1_R₀ : 1 + Real.log (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ) ≤ 2 * L / ℓ ^ 5 := by
    have hle : Real.log (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ) ≤ Real.log (subexpCutoff N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ by omega))
        (by exact_mod_cast hR₀R₁)
    linarith only [hle, h1_R₁]
  have hℓ_E : 128 * (1024 * D * C_pr + 2048 * C_pr * CB / g₀ +
      512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) + 1 ≤ ℓ := by
    rw [hℓ_eq]; linarith only [hll_E]
  have hsE0 := critical_band_far_budgetE_le hL_eq hℓ_eq hk₁_eq hb_eq hD hg₀ hCpr hCnp hCB0
    hK_tot hL1 hc1 hcL hc8_le (by omega : 1 ≤ ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊) hRN₀ h1_R₀ hB0_ub
    hSg_ub (zero_le_one.trans hSg1) hℓ_E
  have hsU0 := critical_band_far_budgetU_le hL_eq hℓ_eq hk₁_eq hb_eq hD hg₀ hCpr hCup hCupT
    hCnp hK_tot hK_res.le hL1 hc1 hc_L8 (by omega) (Nat.div_le_self _ _) hRN₀ h1_R₀ hNM hpoly5
    hSg_ub (zero_le_one.trans hSg1) hρ0 hρ_ub hsE0 hL8_U
  have hsE1 := critical_band_far_budgetE_le hL_eq hℓ_eq hk₁_eq hb_eq hD hg₀ hCpr hCnp hCB0
    hK_tot hL1 hc1 hcL hc8_le (by omega : 1 ≤ subexpCutoff N) hRN₁ h1_R₁ hB1_ub
    hSg_ub (zero_le_one.trans hSg1) hℓ_E
  have hsU1 := critical_band_far_budgetU_le hL_eq hℓ_eq hk₁_eq hb_eq hD hg₀ hCpr hCup hCupT
    hCnp hK_tot hK_res.le hL1 hc1 hc_L8 (by omega) (Nat.div_le_self _ _) hRN₁ h1_R₁ hNM hpoly5
    hSg_ub (zero_le_one.trans hSg1) hρ0 hρ_ub hsE1 hL8_U
  have hcr0w : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊,
          a₀ m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w' : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        w' ∈ (conductorSubspace (subexpCutoff N) N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊,
            a₀ m • normalizedRamanujanHorizonVector m N), w'⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊,
            a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k₁ / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w' n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w' n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) * ‖w'‖ ^ 2 := fun a₀ hu₀_1 w' hw' =>
    hcross_shape hR₀2 (by exact_mod_cast hR₀6) hM1 (Nat.div_le_self _ _) h18_R₀ hc1 h8c hc4
      hsize_near0 hsize_up0 hrad hceil0 hRK0 hSg1 (div_totient_le_loglog_of_le hK_tot htot hR₀R₁)
      hρ_norm hk₁_pos hb_pos hsE0 hsU0 a₀ hu₀_1
      (fun v hv => hw' v (conductorSubspace_mono hR₀R₁ N hv))
  have hcr1w := hcross_shape hR₁2 (by exact_mod_cast hR₁6) hM1 (Nat.div_le_self _ _) h18_R₁ hc1
    h8c hc4 hsize_near1 hsize_up1 hrad hceil1 hRK1 hSg1
    (div_totient_le_loglog_of_le hK_tot htot le_rfl) hρ_norm hk₁_pos hb_pos hsE1 hsU1
  -- Band 2 debit and norm floors on `L^(1/16) ≤ c ≤ L^(1/8)`
  have hk₁_lb : L ^ (3 / 4 : ℝ) / D ≤ k₁ := by
    rw [hk₁_eq, div_le_div_iff₀ hD (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hpoly5 (Real.rpow_nonneg hL0.le (3 / 4))
    have hsplit : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
    nlinarith only [hm, hsplit, hD]
  have hfl_d : g₀ * D / 4 ≤ L ^ (1 / 8 : ℝ) :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hL8_floors
  have hfl_p : 32 * D * (κ₀ + 2) ≤ L ^ (1 / 8 : ℝ) :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hL8_floors
  have hfl_s : 64 * (κ₀ + 2) / g₀ ≤ L ^ (1 / 8 : ℝ) :=
    (le_max_right _ _).trans hL8_floors
  have hP_debit : g₀ * L / (128 * c ^ 7) ≤ k₁ / 32 := by
    have hc7_lo : L ^ (7 / 16 : ℝ) ≤ c ^ 7 := by
      have hp := pow_le_pow_left₀ (by positivity) hc_lo 7
      have he : (L ^ (1 / 16 : ℝ)) ^ 7 = L ^ (7 / 16 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
      exact he.symm.trans_le hp
    have hLc7 : L / c ^ 7 ≤ L ^ (9 / 16 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      calc
        L = L ^ (9 / 16 : ℝ) * L ^ (7 / 16 : ℝ) := by
          rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
        _ ≤ L ^ (9 / 16 : ℝ) * c ^ 7 := mul_le_mul_of_nonneg_left hc7_lo (by positivity)
    have hgd3 : g₀ * D / 4 ≤ L ^ (3 / 16 : ℝ) :=
      hfl_d.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
    have h1 : g₀ * L / (128 * c ^ 7) ≤ L ^ (3 / 4 : ℝ) / (32 * D) := by
      have hm1 : g₀ * L / (128 * c ^ 7) ≤ (g₀ / 128) * L ^ (9 / 16 : ℝ) := by
        calc
          g₀ * L / (128 * c ^ 7) = (g₀ / 128) * (L / c ^ 7) := by ring
          _ ≤ (g₀ / 128) * L ^ (9 / 16 : ℝ) := mul_le_mul_of_nonneg_left hLc7 (by positivity)
      have hm2 : (g₀ / 128) * L ^ (9 / 16 : ℝ) ≤ (L ^ (3 / 16 : ℝ) / (32 * D)) * L ^ (9 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (by rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith only [hgd3])
          (by positivity)
      have hid : (L ^ (3 / 16 : ℝ) / (32 * D)) * L ^ (9 / 16 : ℝ) = L ^ (3 / 4 : ℝ) / (32 * D) := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hL0]; norm_num
      exact hm1.trans (hm2.trans_eq hid)
    have h2 : L ^ (3 / 4 : ℝ) / (32 * D) ≤ k₁ / 32 := by
      have := div_le_div_of_nonneg_right hk₁_lb (by norm_num : (0 : ℝ) ≤ 32)
      exact (by ring : L ^ (3 / 4 : ℝ) / (32 * D) = (L ^ (3 / 4 : ℝ) / D) / 32).trans_le this
    exact h1.trans h2
  have hP_floor : κ₀ + 2 ≤ k₁ / 32 := by
    have h1 : 32 * D * (κ₀ + 2) ≤ L ^ (3 / 4 : ℝ) :=
      hfl_p.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
    have h2 : κ₀ + 2 ≤ (L ^ (3 / 4 : ℝ) / D) / 32 := by
      rw [le_div_iff₀ (by norm_num), le_div_iff₀ hD]; linarith only [h1]
    exact h2.trans (div_le_div_of_nonneg_right hk₁_lb (by norm_num))
  have hS_floor : κ₀ + 2 ≤ g₀ * L / (64 * c ^ 7) := by
    have hc7_hi : c ^ 7 ≤ L ^ (7 / 8 : ℝ) := by
      have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 7; push_cast at hp; exact hp
    have hLc7 : L ^ (1 / 8 : ℝ) ≤ L / c ^ 7 := by
      rw [le_div_iff₀ (by positivity)]
      calc
        L ^ (1 / 8 : ℝ) * c ^ 7 ≤ L ^ (1 / 8 : ℝ) * L ^ (7 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hc7_hi (by positivity)
        _ = L := by rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
    rw [le_div_iff₀ (by positivity)]
    have h1 : (κ₀ + 2) * 64 ≤ g₀ * L ^ (1 / 8 : ℝ) := by
      have hm := (div_le_iff₀ hg₀).mp hfl_s
      linarith only [hm]
    have h2 := mul_le_mul_of_nonneg_left hLc7 hg₀.le
    have h3 : g₀ * (L / c ^ 7) * c ^ 7 = g₀ * L := by field_simp [hc0.ne']
    have h4 := mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity : (0 : ℝ) ≤ c ^ 7)
    linarith only [h4, h3, (by ring : (κ₀ + 2) * 64 * c ^ 7 = (κ₀ + 2) * (64 * c ^ 7))]
  exact complement_three_band_collar_reserve_assembly hQ2 hQR₀ hc1 hκ₀ hbk
    (hcoerc0 hQ2 hQR₀ hR₀6 h36_R₀ hc1 hcL hw1 hrad hsize_near0 hsmall_band0)
    (hcoerc1 hR₀2 hR₀R₁ hR₁6 h1080_R₁ hc1 hcL hw1 hsize_near1
      (hR₁_tail.trans ((div_le_one hL0).mpr hL1)))
    hband2
    (hcross01 hR₀2 hR₀6 h18_R₀ hc1 hw1 hsize_near0 hsize_up0 hH₀_ub hsmall_cross01)
    hcr0w hcr1w hfl0 hfl1 hP_debit hP_floor hS_floor
    hu₀_mem hu₀_orthQ hu₁_mem hu₁_orthR₀ hw

/-! ### 5. Schur synthesis with the collar seventh-power pairing and public theorems -/

private lemma critical_pairing_sum_le {M N : ℕ} {s : Finset ℕ} {E : ℕ → ℝ}
    {r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N)} {X Ψ Ψ_D Ψ_7 ρ_top : ℝ}
    {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hMN : M ≤ N) (hE : ∀ m ∈ s, 0 < E m)
    (htop : (∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2) ≤ ρ_top * ‖u₀‖ ^ 2)
    (hΨ : (∑ m ∈ s, ‖r m‖ ^ 2 / E m) ≤ Ψ)
    (hΨD : (∑ m ∈ s, deepMass X (r m) / E m) ≤ Ψ_D)
    (hΨ7 : (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) ≤ Ψ_7) :
    (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      (6 * Ψ * ρ_top + 6 * Ψ_D) * ‖u₀‖ ^ 2 +
        3 * Ψ * ‖u₁‖ ^ 2 +
        6 * Ψ * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        6 * Ψ_7 * topCollarSeventhMass M N (primeHorizonExtension w) := by
  have htop0 : 0 ≤ ∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hPw0 : 0 ≤ ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ topCollarSeventhMass M N (primeHorizonExtension w) :=
    (sum_nonneg fun _ _ => sq_nonneg _).trans
      (sum_sq_Ioc_le_topCollarSeventhMass M N (primeHorizonExtension w))
  have hdeep := fun m => inner_sq_le_deep_add_top X (r m) u₀
  have hw_cs : ∀ m, ⟪r m, w⟫ ^ 2 ≤
      2 * (‖r m‖ ^ 2 * ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        2 * (topCollarDualSeventhMass M N (r m) *
          topCollarSeventhMass M N (primeHorizonExtension w)) := by
    intro m
    have hrm_pre : (∑ n ∈ Icc 1 M, primeHorizonExtension (r m) n ^ 2) ≤ ‖r m‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq (r m)]
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) fun _ _ _ => sq_nonneg _
    have hcs := inner_sq_le_prefix_add_topCollarSeventh hMN (r m) w
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrm_pre zero_le_two) hPw0
    linarith only [hcs, hm,
      (by ring : 2 * ‖r m‖ ^ 2 * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) =
        2 * (‖r m‖ ^ 2 * ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2)),
      (by ring : 2 * topCollarDualSeventhMass M N (r m) *
          topCollarSeventhMass M N (primeHorizonExtension w) =
        2 * (topCollarDualSeventhMass M N (r m) *
          topCollarSeventhMass M N (primeHorizonExtension w)))]
  generalize (∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2) = top at htop htop0 hdeep
  generalize (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) = P_w at hw_cs hPw0 ⊢
  generalize topCollarSeventhMass M N (primeHorizonExtension w) = S7_w at hw_cs hS7_0 ⊢
  have hpair : ∀ m, ⟪r m, u₀ + u₁ + w⟫ ^ 2 ≤
      6 * (‖r m‖ ^ 2 * top) + 6 * (deepMass X (r m) * ‖u₀‖ ^ 2) +
        3 * (‖r m‖ ^ 2 * ‖u₁‖ ^ 2) +
        6 * (‖r m‖ ^ 2 * P_w) + 6 * (topCollarDualSeventhMass M N (r m) * S7_w) := by
    intro m
    have hsplit : ⟪r m, u₀ + u₁ + w⟫ = ⟪r m, u₀⟫ + ⟪r m, u₁⟫ + ⟪r m, w⟫ := by
      rw [inner_add_right, inner_add_right]
    have h3sq : (⟪r m, u₀⟫ + ⟪r m, u₁⟫ + ⟪r m, w⟫) ^ 2 ≤
        3 * ⟪r m, u₀⟫ ^ 2 + 3 * ⟪r m, u₁⟫ ^ 2 + 3 * ⟪r m, w⟫ ^ 2 := by
      nlinarith only [sq_nonneg (⟪r m, u₀⟫ - ⟪r m, u₁⟫),
        sq_nonneg (⟪r m, u₀⟫ - ⟪r m, w⟫), sq_nonneg (⟪r m, u₁⟫ - ⟪r m, w⟫)]
    have hu₁_cs : ⟪r m, u₁⟫ ^ 2 ≤ ‖r m‖ ^ 2 * ‖u₁‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _)
        (abs_real_inner_le_norm (r m) u₁) 2)
    rw [hsplit]
    linarith only [h3sq, hdeep m, hu₁_cs, hw_cs m]
  have hΨ0 : 0 ≤ ∑ m ∈ s, ‖r m‖ ^ 2 / E m :=
    sum_nonneg fun m hm => div_nonneg (sq_nonneg _) (hE m hm).le
  have hsum : (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      6 * top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
        6 * ‖u₀‖ ^ 2 * (∑ m ∈ s, deepMass X (r m) / E m) +
        3 * ‖u₁‖ ^ 2 * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
        6 * P_w * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
        6 * S7_w * (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) := by
    have hrhs :
        6 * top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
          6 * ‖u₀‖ ^ 2 * (∑ m ∈ s, deepMass X (r m) / E m) +
          3 * ‖u₁‖ ^ 2 * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
          6 * P_w * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
          6 * S7_w * (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) =
        ∑ m ∈ s, (6 * top * (‖r m‖ ^ 2 / E m) +
          6 * ‖u₀‖ ^ 2 * (deepMass X (r m) / E m) +
          3 * ‖u₁‖ ^ 2 * (‖r m‖ ^ 2 / E m) +
          6 * P_w * (‖r m‖ ^ 2 / E m) +
          6 * S7_w * (topCollarDualSeventhMass M N (r m) / E m)) := by
      simp only [sum_add_distrib, mul_sum]
    rw [hrhs]
    refine sum_le_sum fun m hm => ?_
    have hEm := hE m hm
    rw [div_le_iff₀ hEm]
    have e : (6 * top * (‖r m‖ ^ 2 / E m) +
        6 * ‖u₀‖ ^ 2 * (deepMass X (r m) / E m) +
        3 * ‖u₁‖ ^ 2 * (‖r m‖ ^ 2 / E m) +
        6 * P_w * (‖r m‖ ^ 2 / E m) +
        6 * S7_w * (topCollarDualSeventhMass M N (r m) / E m)) * E m =
      6 * (‖r m‖ ^ 2 * top) + 6 * (deepMass X (r m) * ‖u₀‖ ^ 2) +
        3 * (‖r m‖ ^ 2 * ‖u₁‖ ^ 2) +
        6 * (‖r m‖ ^ 2 * P_w) + 6 * (topCollarDualSeventhMass M N (r m) * S7_w) := by
      field_simp [hEm.ne']
    rw [e]; exact hpair m
  have ht0 := mul_le_mul htop hΨ hΨ0 (htop0.trans htop)
  have htD := mul_le_mul_of_nonneg_left hΨD (by positivity : (0 : ℝ) ≤ 6 * ‖u₀‖ ^ 2)
  have ht1 := mul_le_mul_of_nonneg_left hΨ (by positivity : (0 : ℝ) ≤ 3 * ‖u₁‖ ^ 2)
  have htwP := mul_le_mul_of_nonneg_left hΨ (mul_nonneg (by norm_num) hPw0)
  have htw7 := mul_le_mul_of_nonneg_left hΨ7 (mul_nonneg (by norm_num) hS7_0)
  linarith only [hsum, ht0, htD, ht1, htwP, htw7,
    (by ring : 6 * top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) = 6 * (top * ∑ m ∈ s, ‖r m‖ ^ 2 / E m)),
    (by ring : 6 * ((ρ_top * ‖u₀‖ ^ 2) * Ψ) + 6 * ‖u₀‖ ^ 2 * Ψ_D =
      (6 * Ψ * ρ_top + 6 * Ψ_D) * ‖u₀‖ ^ 2),
    (by ring : 3 * ‖u₁‖ ^ 2 * Ψ = 3 * Ψ * ‖u₁‖ ^ 2),
    (by ring : 6 * P_w * Ψ = 6 * Ψ * P_w),
    (by ring : 6 * S7_w * Ψ_7 = 6 * Ψ_7 * S7_w)]

private lemma critical_schur_posDef_of_collar_blocks {Q₁ R₀ R₁ N : ℕ}
    {c X Ψ Ψ_D Ψ_7 ρ_top μ₀ μ₁ μ_P μ_7 : ℝ}
    (hc1 : 1 ≤ c) (hQR₀ : Q₁ ≤ R₀) (hR₀R₁ : R₀ ≤ R₁)
    (hlow : ∀ a : ℕ → ℝ,
      (1 / 4 : ℝ) * (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
        ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
            (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N⟫)
    (hcomp : ∀ {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      u₀ ∈ conductorSubspace R₀ N → u₀ ∈ (conductorSubspace Q₁ N)ᗮ →
      u₁ ∈ conductorSubspace R₁ N → u₁ ∈ (conductorSubspace R₀ N)ᗮ →
      w ∈ (conductorSubspace R₁ N)ᗮ →
      (tiltedSplineSpectralFloorConstant + 2 + μ₀) * ‖u₀‖ ^ 2 +
          (tiltedSplineSpectralFloorConstant + 2 + μ₁) * ‖u₁‖ ^ 2 +
          (tiltedSplineSpectralFloorConstant + 2) * ‖w‖ ^ 2 +
          μ_P * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          μ_7 * topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
        completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w))
    (htop : ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace R₀ N →
      (∑ n ∈ topRows N X, primeHorizonExtension u n ^ 2) ≤ ρ_top * ‖u‖ ^ 2)
    (hΨ : (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m) ≤ Ψ)
    (hΨD : (∑ m ∈ Icc 1 Q₁,
        deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤ Ψ_D)
    (hΨ7 : (∑ m ∈ Icc 1 Q₁,
        topCollarDualSeventhMass (N / linearDefectCutoff c) N
          (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤ Ψ_7)
    (hμ₀ : 48 * Ψ * ρ_top + 48 * Ψ_D ≤ μ₀)
    (hμ₁ : 24 * Ψ ≤ μ₁) (hμP : 48 * Ψ ≤ μ_P) (hμ7 : 48 * Ψ_7 ≤ μ_7) :
    (spectralFloorWeilMatrix c N).PosDef := by
  refine posDef_of_inner_pos_on_ne_zero (spectralFloorWeilMatrix_isHermitian c N) fun x hx_ne => ?_
  have hy_mem : (conductorSubspace Q₁ N).starProjection x ∈ conductorSubspace Q₁ N :=
    (conductorSubspace Q₁ N).starProjection_apply_mem x
  have hz_orth : x - (conductorSubspace Q₁ N).starProjection x ∈ (conductorSubspace Q₁ N)ᗮ :=
    sub_starProjection_mem_orthogonal_telescoped _ x
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (M := Q₁) (N := N)
    (x := (conductorSubspace Q₁ N).starProjection x)).mp hy_mem
  obtain ⟨u₀, u₁, w, hz_eq, hu₀_mem, hu₀_orthQ, hu₁_mem, hu₁_orthR₀, hw_orthR₁, hnorm⟩ :=
    telescoped_three_band_orthogonal_split hQR₀ hR₀R₁ hz_orth
  have hx_eq : x = (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) +
      (u₀ + u₁ + w) := by
    rw [← hz_eq, ha]; abel
  rw [hz_eq] at hz_orth hnorm
  rw [hx_eq]
  have hne : (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w) ≠ 0 :=
    hx_eq ▸ hx_ne
  have hE_pos : ∀ m ∈ Icc 1 Q₁, 0 < completedConductorEnergy tiltedUnitSpline c m := by
    intro m hm
    have hc0 : 0 < c := zero_lt_one.trans_le hc1
    have hs : 0 < tiltedSplineSpectralFloorConstant / (2 * c ^ 7) :=
      div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
    exact hs.trans_le (spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1)
  have hSy0 : 0 ≤ ∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2 :=
    sum_nonneg fun m hm => mul_nonneg (hE_pos m hm).le (sq_nonneg _)
  have hy_mem' : (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) ∈
      conductorSubspace Q₁ N := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N a
  have hyz0 : ⟪∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N, u₀ + u₁ + w⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hy_mem' hz_orth
  have hvm_z0 : ∀ m ∈ Icc 1 Q₁, ⟪normalizedRamanujanHorizonVector m N, u₀ + u₁ + w⟫ = 0 := by
    intro m hm
    let b : ℕ → ℝ := fun k => if k = m then 1 else 0
    have hb_eq : (∑ k ∈ Icc 1 Q₁, b k • normalizedRamanujanHorizonVector k N) =
        normalizedRamanujanHorizonVector m N := by
      dsimp only [b]
      rw [sum_eq_single m]
      · simp
      · intro k _ hkm; rw [if_neg hkm, zero_smul]
      · intro hm_not; exact False.elim (hm_not hm)
    exact Submodule.inner_right_of_mem_orthogonal
      (hb_eq ▸ sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N b) hz_orth
  have hcross_eq : ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
        (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫ =
      ∑ m ∈ Icc 1 Q₁, a m * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N,
        u₀ + u₁ + w⟫ := by
    have h1 : ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫ =
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫ := by
      simp only [spectralFloorWeilMatrix, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, identity_euclid_apply_telescoped, inner_sub_left,
        real_inner_smul_left, hyz0, mul_zero, sub_zero]
    rw [h1, map_sum, sum_inner]
    refine sum_congr rfl fun m hm => ?_
    rw [map_smul, real_inner_smul_left]
    congr 1
    rw [inner_sub_left, real_inner_smul_left, hvm_z0 m hm, mul_zero, sub_zero]
  have hcross_abs := two_abs_weighted_sum_le (a := a) (t := fun m =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N,
        u₀ + u₁ + w⟫) hE_pos
  rw [← hcross_eq] at hcross_abs
  have hΦ := critical_pairing_sum_le (Nat.div_le_self N _) hE_pos (htop hu₀_mem) hΨ hΨD hΨ7
  have hz_floor := hcomp hu₀_mem hu₀_orthQ hu₁_mem hu₁_orthR₀ hw_orthR₁
  have hz_A : 2 * ‖u₀ + u₁ + w‖ ^ 2 + μ₀ * ‖u₀‖ ^ 2 + μ₁ * ‖u₁‖ ^ 2 +
      μ_P * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
      μ_7 * topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) ≤
      ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) (u₀ + u₁ + w), u₀ + u₁ + w⟫ := by
    rw [spectralFloorWeilMatrix_inner]
    have hc7 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
    have hshift_le : tiltedSplineSpectralFloorConstant / (2 * c ^ 7) ≤
        tiltedSplineSpectralFloorConstant :=
      div_le_self tiltedSplineSpectralFloorConstant_pos.le (by linarith only [hc7])
    have hm := mul_le_mul_of_nonneg_right hshift_le (sq_nonneg ‖u₀ + u₁ + w‖)
    rw [hnorm] at hm ⊢
    linarith only [hz_floor, hm]
  have hPw0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) :=
    (sum_nonneg fun _ _ => sq_nonneg _).trans
      (sum_sq_Ioc_le_topCollarSeventhMass _ N (primeHorizonExtension w))
  have hΦμ : 8 * ((6 * Ψ * ρ_top + 6 * Ψ_D) * ‖u₀‖ ^ 2 +
      3 * Ψ * ‖u₁‖ ^ 2 +
      6 * Ψ * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
      6 * Ψ_7 * topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w)) ≤
      μ₀ * ‖u₀‖ ^ 2 + μ₁ * ‖u₁‖ ^ 2 +
        μ_P * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        μ_7 * topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) := by
    have h0 := mul_le_mul_of_nonneg_right hμ₀ (sq_nonneg ‖u₀‖)
    have h1 := mul_le_mul_of_nonneg_right hμ₁ (sq_nonneg ‖u₁‖)
    have h2 := mul_le_mul_of_nonneg_right hμP hPw0
    have h3 := mul_le_mul_of_nonneg_right hμ7 hS7_0
    linarith only [h0, h1, h2, h3]
  have hexp := hermitian_inner_add_eq_telescoped (spectralFloorWeilMatrix_isHermitian c N)
    (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) (u₀ + u₁ + w)
  have habs := neg_abs_le ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
    (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫
  have hy_fl := hlow a
  have hlb : (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) / 8 +
      2 * ‖u₀ + u₁ + w‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          ((∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w)),
        (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w)⟫ := by
    rw [hexp]
    linarith only [hy_fl, hz_A, hcross_abs, habs, hΦμ, hΦ]
  refine lt_of_lt_of_le ?_ hlb
  by_contra hnot
  have hle0 := not_lt.mp hnot
  have hz_sq0 : ‖u₀ + u₁ + w‖ ^ 2 = 0 := by linarith only [hle0, hSy0, sq_nonneg ‖u₀ + u₁ + w‖]
  have hSy00 : (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) = 0 := by
    linarith only [hle0, hSy0, sq_nonneg ‖u₀ + u₁ + w‖]
  have hz0 : u₀ + u₁ + w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz_sq0)
  have hterm0 : ∀ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2 = 0 :=
    fun m hm => (sum_eq_zero_iff_of_nonneg fun k hk => mul_nonneg (hE_pos k hk).le
      (sq_nonneg _)).mp hSy00 m hm
  have ha0 : ∀ m ∈ Icc 1 Q₁, a m = 0 := by
    intro m hm
    rcases mul_eq_zero.mp (hterm0 m hm) with hE0 | ha_sq
    · exact absurd hE0 (hE_pos m hm).ne'
    · exact sq_eq_zero_iff.mp ha_sq
  have hy0 : (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) = 0 :=
    sum_eq_zero fun m hm => by rw [ha0 m hm, zero_smul]
  exact hne (by rw [hy0, hz0, add_zero])

/-- **Positive definiteness of `spectralFloorWeilMatrix` at a fixed critical multiple.**
There exists an explicit `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N` and uniformly across
`1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, the shifted complete Weil matrix `spectralFloorWeilMatrix c N` is
positive definite on `EuclideanSpace ℝ (PrimeHorizonIndex N)`. -/
theorem exists_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_at_critical_multiple :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          (spectralFloorWeilMatrix c N).PosDef := by
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  obtain ⟨K₁_low, hK₁_low_pos, hK₁_low_half, hlow_ev⟩ :=
    exists_critical_multiple_low_packet_and_collar_budget
      (by positivity : 0 < dyadicTopMassConstant / 2048)
  obtain ⟨K₁_far, hK₁_far_pos, h2K₁_far_le1, hcomp_ev⟩ :=
    exists_complement_collar_reserves_upper_band
  obtain ⟨C_p, C_s, C_q, K_up, hCp, hCs, hCq, hKup, hdeep⟩ :=
    exists_deepMass_conductorResidual_le contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_sh, hC_sh, hsh⟩ :=
    exists_tiltedUnitSpline_conductor_uniform_affineShellCorrection_linear_log_rate
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hsh 2 (by norm_num) 4)
  obtain ⟨Kβ, hKβ⟩ : ∃ Kβ : ℝ, Kβ = C_s + 4 + 162 +
      32 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 +
      2048 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) ^ 2 + C_q +
      46875 * K_up + 2457600 + 6 * (65536 * C_sh ^ 2) := ⟨_, rfl⟩
  let K₁ : ℝ := min K₁_low K₁_far
  have hK₁_pos : 0 < K₁ := lt_min hK₁_low_pos hK₁_far_pos
  have hK₁_le_low : K₁ ≤ K₁_low := min_le_left _ _
  have hK₁_le_far : K₁ ≤ K₁_far := min_le_right _ _
  have h2K₁_le1 : 2 * K₁ ≤ 1 := by linarith only [hK₁_le_far, h2K₁_far_le1]
  refine ⟨K₁, hK₁_pos, h2K₁_le1, ?_⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
    eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth
      (by norm_num : (0 : ℝ) < 1 / 16) (by unfold oneEighthPowerLogExponent; norm_num),
    hlow_ev, hcomp_ev,
    eventually_three_cutoff_bounds_one_ninth (by norm_num : (0 : ℝ) < 13 / 32)
      (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) < 1 / 4096) le_rfl,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1 / 4) 2),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 32) 1),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 2) 16),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hLlim).eventually_ge_atTop
      (4 * explicitConductorCutoffConstant + 4),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hLlim).eventually_ge_atTop 960,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hLlim).eventually_ge_atTop
      (384 * explicitConductorCutoffConstant),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim).eventually_ge_atTop
      (6912 * (C_p + 1) / tiltedSplineSpectralFloorConstant),
    hLlim.eventually_ge_atTop (max 3000 (|Kβ| + 2 * |Y₀|)),
    eventually_ge_atTop 3] with
      N hbelow hlowN hcompN hcut hLX hpoly5 hpoly32 hpoly16 hL34_D hL14_960 hL12_384 hL8_deep
      hL_max hN3
  dsimp only [Function.comp_def] at hpoly5 hpoly32 hpoly16 hL34_D hL14_960 hL12_384 hL8_deep hL_max
  intro c hc1 hcup
  by_cases hc16 : c ≤ Real.log (N : ℝ) ^ (1 / 16 : ℝ)
  · exact hbelow c hc1 hc16
  · have hc_lo : Real.log (N : ℝ) ^ (1 / 16 : ℝ) ≤ c := le_of_not_ge hc16
    have hL3000 : 3000 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
    have hKY : |Kβ| + 2 * |Y₀| ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL_max
    have hKβL : Kβ ≤ Real.log (N : ℝ) := by linarith only [hKY, le_abs_self Kβ, abs_nonneg Y₀]
    have hY₀L : 2 * Y₀ ≤ Real.log (N : ℝ) := by linarith only [hKY, le_abs_self Y₀, abs_nonneg Kβ]
    have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hL3000]
    have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
    have hN1 : 1 ≤ N := by omega
    have hc0 : 0 < c := zero_lt_one.trans_le hc1
    have hc_low : c ≤ 2 * K₁_low * Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
      hcup.trans (mul_le_mul_of_nonneg_right (by linarith only [hK₁_le_low]) (by positivity))
    have hc_far : c ≤ 2 * K₁_far * Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
      hcup.trans (mul_le_mul_of_nonneg_right (by linarith only [hK₁_le_far]) (by positivity))
    have hc_L8 : c ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
      hcup.trans ((mul_le_mul_of_nonneg_right h2K₁_le1 (by positivity)).trans_eq (one_mul _))
    have hcL : c ≤ Real.log (N : ℝ) :=
      hc_L8.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one _))
    obtain ⟨hQ2, hQR₀, -, hQ_le, -, -, hH₀_ub, hlogR₀_lb, h36_R₀, -, -, -⟩ := hcut
    obtain ⟨hR₀R₁, -, -, -, -, hRN₁⟩ := subexpCutoff_bounds hD hN1 hL3000 hLX hpoly5 hL34_D
    have hR₀2 : 2 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ := hQ2.trans hQR₀
    have hR₀1 : (1 : ℝ) ≤ (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ) := by
      exact_mod_cast (show 1 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ by omega)
    obtain ⟨-, -, -, -, hR₀6, -, -, -, -, -, -, -⟩ :=
      rpow_horizon_N_bounds_one_ninth hN1 hR₀2 hc1 (by linarith only [hL3000]) hLX hcL h36_R₀
    obtain ⟨hRM0, -, -, -⟩ :=
      linear_prefix_horizon_bounds_one_ninth hN1 hR₀2 hc1 hL3000 hLX hcL h36_R₀
    have hNL : Real.log (N : ℝ) ^ 18 ≤ N := by
      refine le_trans ?_ hRN₁
      exact le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by exact_mod_cast (show 1 ≤ subexpCutoff N by omega)))
    have hQ1 : (1 : ℝ) ≤ (⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast (show 1 ≤ ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ by omega)
    have hQh : (⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 2 : ℝ) :=
      hQ_le.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
    have hQL : (⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊ : ℝ) ≤ Real.log (N : ℝ) :=
      hQ_le.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one _))
    have hpoly16' : 16 * (1 + Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) ^ (1 / 2 : ℝ) := by
      simpa only [pow_one] using hpoly16
    obtain ⟨hR₀L8, hlogY, hYY₀, hQY⟩ := deep_cutoff_facts (by linarith only [hL3000]) hc1 hcL
      hpoly16' hR₀1 hlogR₀_lb hY₀L hQh
    have hΨD := deep_inverse_energy_mass_le (Q := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊)
      hCp hCs hCq hKup hdeep (hY₀ _ hYY₀).2 (by linarith only [hL3000]) hc1 hcL hQL hQY hR₀L8 hNL
      (by field_simp) hlogY (hKβ ▸ hKβL)
    obtain ⟨hlow_a, hΨ, hΨ7_all⟩ := hlowN c hc1 hc_low
    have h2BM : 2 * linearPrimeStrip c ≤ N / linearDefectCutoff c := by
      have hB := linearPrimeStrip_le_four_mul hc1 hcL
      have hL2 : 2 ≤ Real.log (N : ℝ) := by linarith only [hL3000]
      have h8L : 8 * Real.log (N : ℝ) ≤ Real.log (N : ℝ) ^ 8 := by
        have h7 : (128 : ℝ) ≤ Real.log (N : ℝ) ^ 7 :=
          (pow_le_pow_left₀ (by norm_num) hL2 7).trans_eq' (by norm_num)
        have hm := mul_le_mul_of_nonneg_left h7 hL0.le
        linarith only [hm, (by ring : Real.log (N : ℝ) * Real.log (N : ℝ) ^ 7 =
          Real.log (N : ℝ) ^ 8)]
      have h2B_R₀ : ((2 * linearPrimeStrip c : ℕ) : ℝ) ≤
          (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ) := by
        push_cast; linarith only [hB, h8L, hR₀L8]
      have h2B_nat : 2 * linearPrimeStrip c ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ :=
        Nat.cast_le.mp h2B_R₀
      exact h2B_nat.trans
        ((Nat.le_mul_of_pos_right _ (by omega : 0 < ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊)).trans
          hRM0)
    have hΨ7 : (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
        topCollarDualSeventhMass (N / linearDefectCutoff c) N
          (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤
        (dyadicTopMassConstant / 2048) * Real.log (N : ℝ) / c ^ 7 := by
      have hraw := hΨ7_all (N / linearDefectCutoff c) h2BM
      rw [le_div_iff₀ (by positivity)]
      have hm := mul_le_mul_of_nonneg_right hraw hL0.le
      have hid : (c ^ 7 / Real.log (N : ℝ)) *
          (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
            topCollarDualSeventhMass (N / linearDefectCutoff c) N
              (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
                  (normalizedRamanujanHorizonVector m N) -
                completedConductorEnergy tiltedUnitSpline c m •
                  normalizedRamanujanHorizonVector m N) /
              completedConductorEnergy tiltedUnitSpline c m) * Real.log (N : ℝ) =
          (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
            topCollarDualSeventhMass (N / linearDefectCutoff c) N
              (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
                  (normalizedRamanujanHorizonVector m N) -
                completedConductorEnergy tiltedUnitSpline c m •
                  normalizedRamanujanHorizonVector m N) /
              completedConductorEnergy tiltedUnitSpline c m) * c ^ 7 := by
        field_simp [hL0.ne']; ring
      linarith only [hm, hid]
    have hRNX := sq_add_one_mul_le_of_pow_six_le hR₀2 hR₀6
    have h18_R₀ : 18 * (1 + Real.log (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ)) ≤
        Real.log (N : ℝ) := by
      linarith only [h36_R₀, Real.log_natCast_nonneg ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊]
    -- The four Schur scalar inequalities
    set L := Real.log (N : ℝ) with hL_eq
    have hμ₀ : 48 * L ^ (1 / 4 : ℝ) *
          (2 * (Real.log (2 * (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ)) + 3) / L) +
        48 * (8 * ((C_p + 1) / L) *
          ((8 * c ^ 7 + (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ) ^ 2 *
            (1 + Real.log (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ)) ^ 2) /
            tiltedSplineSpectralFloorConstant)) ≤ 1 := by
      have htop_le : 2 * (Real.log (2 * (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ)) + 3) ≤
          10 * L ^ (1 / 2 : ℝ) := by
        have hl2 : Real.log (2 * (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ)) =
            Real.log 2 + Real.log (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ) :=
          Real.log_mul (by norm_num) (by linarith only [hR₀1])
        have hlog2 : Real.log 2 ≤ 1 := by
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hLh1 : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
        rw [hl2]; linarith only [hlog2, hH₀_ub, hLh1]
      have hpart1 : 48 * L ^ (1 / 4 : ℝ) *
          (2 * (Real.log (2 * (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ)) + 3) / L) ≤ 1 / 2 := by
        have hsplit : L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num [Real.rpow_one]
        calc
          48 * L ^ (1 / 4 : ℝ) *
              (2 * (Real.log (2 * (⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊ : ℝ)) + 3) / L)
              ≤ 48 * L ^ (1 / 4 : ℝ) * (10 * L ^ (1 / 2 : ℝ) / L) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htop_le hL0.le) (by positivity)
          _ = 480 / L ^ (1 / 4 : ℝ) := by
            rw [← hsplit]; field_simp [(Real.rpow_pos_of_pos hL0 _).ne']; ring
          _ ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith only [hL14_960]
      have hpart2 : 48 * (8 * ((C_p + 1) / L) *
          ((8 * c ^ 7 + (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ) ^ 2 *
            (1 + Real.log (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ)) ^ 2) /
            tiltedSplineSpectralFloorConstant)) ≤ 1 / 2 := by
        have hc7 : c ^ 7 ≤ L ^ (7 / 8 : ℝ) := by
          have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 7; push_cast at hp; exact hp
        have hpoly32' : 1 + Real.log L ≤ L ^ (1 / 32 : ℝ) := by
          simpa only [one_mul, pow_one, hL_eq] using hpoly32
        have hlQ : 1 + Real.log (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ) ≤ L ^ (1 / 32 : ℝ) :=
          (by linarith [Real.log_le_log (by linarith only [hQ1]) hQL]).trans hpoly32'
        have hQ2_ub : (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ) ^ 2 *
            (1 + Real.log (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ)) ^ 2 ≤ L ^ (7 / 8 : ℝ) := by
          have h1 := pow_le_rpow_mul hL0 (by positivity) hQ_le 2
          have h2 := pow_le_rpow_mul hL0
            (by linarith [Real.log_natCast_nonneg ⌊L ^ (13 / 32 : ℝ)⌋₊]) hlQ 2
          push_cast at h1 h2
          exact (mul_le_rpow_add hL0 h1 (by positivity) h2).trans_eq (by congr 1; norm_num)
        have hsum9 : 8 * c ^ 7 + (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ) ^ 2 *
            (1 + Real.log (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ)) ^ 2 ≤ 9 * L ^ (7 / 8 : ℝ) := by
          linarith only [hc7, hQ2_ub]
        have hsplit : L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L := by
          rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
        calc
          48 * (8 * ((C_p + 1) / L) *
              ((8 * c ^ 7 + (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ) ^ 2 *
                (1 + Real.log (⌊L ^ (13 / 32 : ℝ)⌋₊ : ℝ)) ^ 2) /
                tiltedSplineSpectralFloorConstant))
              ≤ 48 * (8 * ((C_p + 1) / L) *
                  ((9 * L ^ (7 / 8 : ℝ)) / tiltedSplineSpectralFloorConstant)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum9 hκ₀.le) (by positivity))
              (by norm_num)
          _ = (3456 * (C_p + 1) / tiltedSplineSpectralFloorConstant) / L ^ (1 / 8 : ℝ) := by
            rw [← hsplit]; field_simp [hκ₀.ne', (Real.rpow_pos_of_pos hL0 _).ne']; ring
          _ ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith only [hL8_deep]
      linarith only [hpart1, hpart2]
    have hμ₁ : 24 * L ^ (1 / 4 : ℝ) ≤ L ^ (1 / 2 : ℝ) / 32 := by
      have hsplit : L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [le_div_iff₀ (by norm_num), ← hsplit]
      have hm := mul_le_mul_of_nonneg_right
        (by linarith only [hL14_960] : (768 : ℝ) ≤ L ^ (1 / 4 : ℝ))
        (by positivity : 0 ≤ L ^ (1 / 4 : ℝ))
      linarith only [hm]
    have hμP : 48 * L ^ (1 / 4 : ℝ) ≤
        (L / (2 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) / 8 := by
      have hk_lb : L ^ (3 / 4 : ℝ) / explicitConductorCutoffConstant ≤
          L / (2 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5) := by
        rw [div_le_div_iff₀ hD (by positivity)]
        have hm := mul_le_mul_of_nonneg_left hpoly5 (Real.rpow_nonneg hL0.le (3 / 4))
        have hsplit : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
          rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
        nlinarith only [hm, hsplit, hD]
      have hsplit : L ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) = L ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      have h1 : 48 * L ^ (1 / 4 : ℝ) ≤ (L ^ (3 / 4 : ℝ) / explicitConductorCutoffConstant) / 8 := by
        rw [le_div_iff₀ (by norm_num), le_div_iff₀ hD, ← hsplit]
        have hm := mul_le_mul_of_nonneg_right hL12_384 (by positivity : 0 ≤ L ^ (1 / 4 : ℝ))
        linarith only [hm]
      exact h1.trans (div_le_div_of_nonneg_right hk_lb (by norm_num))
    have hμ7 : 48 * ((dyadicTopMassConstant / 2048) * L / c ^ 7) ≤
        dyadicTopMassConstant * L / (32 * c ^ 7) := by
      have h1 : (48 / 2048 : ℝ) ≤ 1 / 32 := by norm_num
      have hm := mul_le_mul_of_nonneg_right h1
        (by positivity : 0 ≤ dyadicTopMassConstant * L / c ^ 7)
      linarith only [hm,
        (by ring : 48 * ((dyadicTopMassConstant / 2048) * L / c ^ 7) =
          (48 / 2048 : ℝ) * (dyadicTopMassConstant * L / c ^ 7)),
        (by ring : dyadicTopMassConstant * L / (32 * c ^ 7) =
          (1 / 32 : ℝ) * (dyadicTopMassConstant * L / c ^ 7))]
    refine critical_schur_posDef_of_collar_blocks hc1 hQR₀ hR₀R₁ hlow_a
      (μ₀ := 1) (μ₁ := L ^ (1 / 2 : ℝ) / 32)
      (μ_P := (L / (2 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) / 8)
      (μ_7 := dyadicTopMassConstant * L / (32 * c ^ 7))
      (fun hu₀ hu₀' hu₁ hu₁' hw => by
        have h := hcompN c hc_lo hc_far hu₀ hu₀' hu₁ hu₁' hw
        linarith only [h])
      (fun hu => sum_topRows_sq_le hR₀2 hR₀1 hRNX h18_R₀ hu)
      hΨ hΨD hΨ7 hμ₀ hμ₁ hμP hμ7

/-- **Uniform `c⁻⁷` spectral floor of `completeWeilEnergy` at a fixed critical multiple.**
There exists `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N` and uniformly across
`1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, the complete Weil quadratic form of `tiltedUnitSpline` dominates
`(tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2` on the entire space. -/
theorem exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
            (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤
              completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨K₁, hK₁_pos, h2K₁, hpos_ev⟩ :=
    exists_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_at_critical_multiple
  refine ⟨K₁, hK₁_pos, h2K₁, ?_⟩
  filter_upwards [hpos_ev] with N hpos c hc hcup x
  have hA := spectralFloorWeilMatrix_isHermitian c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hnonneg : 0 ≤ ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [spectralFloorWeilMatrix_inner] at hnonneg
  linarith only [hnonneg]

/-- **All-vector positive definiteness of `completeWeilMatrix` at a fixed critical multiple.**
There exists `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N` and uniformly across
`1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, `completeWeilMatrix tiltedUnitSpline c N` is positive definite on
`EuclideanSpace ℝ (PrimeHorizonIndex N)`. -/
theorem exists_tiltedUnitSpline_completeWeilMatrix_posDef_at_critical_multiple :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  obtain ⟨K₁, hK₁_pos, h2K₁, hfloor_ev⟩ :=
    exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
  refine ⟨K₁, hK₁_pos, h2K₁, ?_⟩
  filter_upwards [hfloor_ev] with N hfloor c hc hcup
  refine posDef_of_inner_pos_on_ne_zero (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
    fun x hx_ne => ?_
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hpos : 0 < (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 :=
    mul_pos (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
      (sq_pos_of_pos (norm_pos_iff.mpr hx_ne))
  exact hpos.trans_le (hfloor c hc hcup x)

/-- **Literal `weilQuad` nonnegativity of the complete Weil family at a fixed critical multiple.**
There exists `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N` and uniformly across
`1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, every atomic horizon test `atomicTest N y (atomDilate tiltedUnitSpline (c / N))`
has nonnegative Weil quadratic form. -/
theorem exists_tiltedUnitSpline_weilQuad_nonneg_at_critical_multiple :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          ∀ y : ℕ → ℝ,
            0 ≤ weilQuad (atomicTest N y (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨K₁, hK₁_pos, h2K₁, hpos_ev⟩ :=
    exists_tiltedUnitSpline_completeWeilMatrix_posDef_at_critical_multiple
  refine ⟨K₁, hK₁_pos, h2K₁, ?_⟩
  filter_upwards [hpos_ev, eventually_ge_atTop 1] with N hpos hN c hc hcup y
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc0 hN0
  have hM : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hquad : 0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (horizonProfileVector y N), horizonProfileVector y N⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN] at hquad
  have htest : atomicTest N (primeHorizonExtension (horizonProfileVector y N))
      (atomDilate tiltedUnitSpline (c / N)) =
      atomicTest N y (atomDilate tiltedUnitSpline (c / N)) := by
    funext u
    unfold atomicTest
    apply sum_congr rfl
    intro n hn
    exact congrArg (· * atomDilate tiltedUnitSpline (c / N) (u - Real.log n))
      (primeHorizonExtension_coe (horizonProfileVector y N) ⟨n, hn⟩)
  rw [htest, div_nonneg_iff] at hquad
  rcases hquad with ⟨hq, -⟩ | ⟨-, hneg⟩
  · exact hq
  · linarith only [hM, hneg]

/-- **Growing-conductor uniformity on the pole hyperplane `(conductorSubspace 1 N)ᗮ` at a fixed
critical multiple.** There exists `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N` and uniformly
across `1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, every vector `z ∈ (conductorSubspace 1 N)ᗮ` satisfies the
uniform `(log N)^{-7/8}` spectral floor
`(tiltedSplineSpectralFloorConstant / (2 * (2 * K₁) ^ 7 * (log N)^{7/8})) * ‖z‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N z`,
and `0 < completeWeilEnergy tiltedUnitSpline c N z` whenever `z ≠ 0`. -/
theorem exists_tiltedUnitSpline_growing_conductor_uniformity_at_critical_multiple :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
            (tiltedSplineSpectralFloorConstant /
                (2 * (2 * K₁) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ))) * ‖z‖ ^ 2 ≤
              completeWeilEnergy tiltedUnitSpline c N z ∧
            (z ≠ 0 → 0 < completeWeilEnergy tiltedUnitSpline c N z) := by
  obtain ⟨K₁, hK₁_pos, h2K₁, hfloor_ev⟩ :=
    exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
  refine ⟨K₁, hK₁_pos, h2K₁, ?_⟩
  filter_upwards [hfloor_ev, eventually_ge_atTop 3] with N hfloor hN3 c hc hcup z _hz
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN3R : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hL_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith only [hN3R])
  have hc7_le : c ^ 7 ≤ (2 * K₁) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ) := by
    calc
      c ^ 7 ≤ (2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) ^ 7 := pow_le_pow_left₀ hc0.le hcup 7
      _ = (2 * K₁) ^ 7 * (Real.log (N : ℝ) ^ (1 / 8 : ℝ)) ^ 7 := mul_pow _ _ 7
      _ = (2 * K₁) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]; norm_num
  have hdiv_le : tiltedSplineSpectralFloorConstant /
      (2 * (2 * K₁) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ)) ≤
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7) := by
    refine div_le_div_of_nonneg_left tiltedSplineSpectralFloorConstant_pos.le (by positivity) ?_
    linarith only [hc7_le,
      (by ring : 2 * ((2 * K₁) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ)) =
        2 * (2 * K₁) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ))]
  have hf := hfloor c hc hcup z
  refine ⟨(mul_le_mul_of_nonneg_right hdiv_le (sq_nonneg ‖z‖)).trans hf, fun hz_ne => ?_⟩
  exact (mul_pos (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
    (sq_pos_of_pos (norm_pos_iff.mpr hz_ne))).trans_le hf

#print axioms exists_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_at_critical_multiple
#print axioms exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
#print axioms exists_tiltedUnitSpline_completeWeilMatrix_posDef_at_critical_multiple
#print axioms exists_tiltedUnitSpline_weilQuad_nonneg_at_critical_multiple
#print axioms exists_tiltedUnitSpline_growing_conductor_uniformity_at_critical_multiple

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
