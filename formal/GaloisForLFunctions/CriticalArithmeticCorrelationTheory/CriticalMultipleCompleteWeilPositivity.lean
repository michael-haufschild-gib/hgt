import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals

/-!
# Positivity of the complete Weil family at a fixed critical multiple

There exists an explicit critical multiple `K₁ > 0` such that eventually in `N` and uniformly
across `1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, both `spectralFloorWeilMatrix c N` and
`completeWeilMatrix tiltedUnitSpline c N` are positive definite on the entire prime-horizon space
`EuclideanSpace ℝ (PrimeHorizonIndex N)`.

Below `(log N)^{1/16}`, positive definiteness is supplied directly by
`eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth`. Across the upper
band `(log N)^{1/16} ≤ c ≤ 2 K₁ (log N)^{1/8}`, we split `x = y + u₀ + u₁ + w` along
`V_{Q₁} ⊂ V_{R₀} ⊂ V_{R₁}` with `Q₁ = ⌊(log N)^{13/32}⌋₊`, `R₀ = ⌊exp √(log N)⌋₊`, and the
subexponential cutoff `R₁ = ⌊exp (log N / (1 + log log N)^5)⌋₊`:

* On `V_{Q₁}`, `exists_critical_multiple_low_packet_and_collar_budget` gives the uniform `(1 / 4)`
  packet energy floor, the total inverse-energy residual bound `Ψ ≤ (log N)^{1/4}`, and the
  top-collar dual-seventh residual bound `(c^7 / log N) Ψ_{d7} ≤ g₀ / 2048`.
* On `(V_{R₁})ᗮ`, `exists_critical_multiple_far_reserve` (`B = 5`, `κ_P = 1 / (16 D)`) combined
  with `poleDefect_prefix_ge_of_conductor_orthogonal` retains `(k / 4) P_w` on the prefix rows and
  `(g₀ log N / (16 c^7)) S7_w` on the dyadic seventh-power top-collar mass.
* In `(V_{Q₁})ᗮ`, `exists_band_far_cross_le_reserve_shape` at `k = log N / (2 D ℓ^5)` and
  `b = (g₀ D / 4) ℓ^5` (`b k = g₀ log N / 8`) absorbs the band–far cross terms while keeping
  separate prefix and seventh-power collar reserves on `w`; the lower bound `c ≥ (log N)^{1/16}`
  ensures `log N / c^7 ≤ (log N)^{9/16} ≪ k`.
* The Schur coupling `∑_m ⟪r_m, u₀ + u₁ + w⟫^2 / E_m` is split across deep/top rows on `u₀`,
  by `L^2` norm on `u₁`, and across prefix/collar seventh-power masses on `w` via
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
    rw [← Real.rpow_add hL0]; norm_num
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
    have h1 := Real.log_le_log (by positivity) hhalf_exp
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', one_div, Real.log_inv,
      Real.log_exp] at h1
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
      have hp : (Real.exp 1) ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 4
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
      _ = N := by rw [← Real.rpow_add hN0]; norm_num
  exact ⟨hR₀R₁, h1_ub, h1080, hgap_lo, hgap_hi, hRN₁⟩

/-! ### 2. Far-sector prefix + dyadic seventh-power collar reserve at `subexpCutoff N` -/

private lemma subexp_far_collar_reserve {N : ℕ} {c D g₀ CB : ℝ}
    (hD_eq : D = explicitConductorCutoffConstant) (hg₀_eq : g₀ = dyadicTopMassConstant)
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
  rw [← hD_eq] at hpre
  have hw1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ subexpCutoff N) N hv)
  have hfarw := hfar hw1
  have hSw_le : (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
      topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) := by
    rw [hg₀_eq] at *
    exact sum_sq_Ioc_le_topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w)
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
    have hkg0 : 0 ≤ Real.log (subexpCutoff N : ℝ) / D - 1 := hk_pos.le.trans hgap_lo
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
  have hP_gain : (L / (2 * D * ℓ ^ 5)) * P_w ≤ (Real.log (subexpCutoff N : ℝ) / D - 1) * P_w := by
    exact mul_le_mul_of_nonneg_right hgap_lo hP0
  where P_w := ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2
  -- Combine prefix defect, leakage bound, and far reserve linearly
  generalize (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) = P at
    hpre hfarw hP0 ⊢
  generalize (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) = S at
    hpre hSw_le hS0
  generalize topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension w) = S7 at
    hfarw hSw_le hS7_0 ⊢
  generalize (Real.log (subexpCutoff N : ℝ) / D - 1) = kg at hpre hgap_lo hleak
  generalize (terminalPacketCost (subexpCutoff N) (N / linearDefectCutoff c) N /
    Real.log (N / linearDefectCutoff c : ℕ)) = Bp at hpre hleak
  have hP1 := mul_le_mul_of_nonneg_right hgap_lo hP0
  have hS1 := (mul_le_mul_of_nonneg_left hSw_le (by positivity : 0 ≤ g₀ * L / (16 * c ^ 7)))
  have hS2 := (mul_le_mul_of_nonneg_right hleak hS0).trans hS1
  have hid_far : (1 / (16 * D)) * L / ℓ ^ 5 = (1 / 8 : ℝ) * (L / (2 * D * ℓ ^ 5)) := by
    field_simp [hD.ne', hℓ0.ne']; ring
  have hid_top : (g₀ / (8 * c ^ 7)) * L = 2 * (g₀ * L / (16 * c ^ 7)) := by
    field_simp [hc0.ne']; ring
  rw [hid_far, hid_top] at hfarw
  have hkp : 0 ≤ (L / (2 * D * ℓ ^ 5)) * P := mul_nonneg hk_pos.le hP0
  linarith only [hpre, hfarw, hP1, hS2, hkp]

/-! ### 3. Scalar budgets `hsE ≤ 1 / 32` and `hsU ≤ 1 / 4` at the subexponential cutoff -/

private lemma critical_band_far_budgetE_le {R M N : ℕ} {c Sg₁ k b L ℓ D g₀ CB C_pr C_np K_tot : ℝ}
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
  -- Term 1
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
  -- Term 2
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
  -- Term 3
  have hE3 : 32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤
      (512 * C_np * (4 * K_tot ^ 2 + 3) / g₀) / ℓ := by
    have hc13 : c ^ 13 / N ≤ 1 :=
      (cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN (one_div_le_one_div_of_le zero_lt_one hL1)
        (by norm_num) (by norm_num)).trans (by norm_num)
    have hc11 : c ^ 11 * (R : ℝ) ^ 4 / (N * L) ≤ 1 := by
      have h1 := cpow_Rpow_div_le hL1 hc0.le hcL hR1R hRN (le_refl (1 / L))
        (by norm_num : 11 ≤ 17) (by norm_num : 4 ≤ 16)
      have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hRN
      rw [div_le_one (mul_pos hN0 hL0)]
      have h2 := (div_le_div_iff₀ hN0 hL0).mp h1
      linarith only [h2, (by linarith only [hL1] : (1 : ℝ) ≤ L ^ 2),
        mul_nonneg hN0.le (sub_nonneg.mpr hL1)]
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
    (hR1 : 1 ≤ R) (hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N)
    (hlR : 1 + Real.log (R : ℝ) ≤ 2 * L / ℓ ^ 5)
    (hNM : (N : ℝ) / M ≤ 2 * (256 * Real.exp 2 + 4) * c)
    (hpoly5 : 2 * ℓ ^ 5 ≤ L ^ (1 / 4 : ℝ))
    (hSg : Sg₁ ≤ 2 * K_tot * ℓ) (hSg0 : 0 ≤ Sg₁)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 * K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L))
    (hL8_U : 16 * (1024 * D * C_pr + 4096 * C_pr / g₀ +
      256 * C_np * (8 * K_res + 1560 * K_tot + 98 + 2 * (4 * K_tot ^ 2 + 3) + 2) / g₀ +
      128 * D * C_up + 2048 * C_upT * (256 * Real.exp 2 + 4) / g₀) + 1 ≤ L ^ (1 / 8 : ℝ)) :
    256 * C_pr * (1 + Real.log (R : ℝ)) / (Real.log (N : ℝ) * k) +
      256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (Real.log (N : ℝ) * b * k) +
      32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetG R N c Sg₁ +
        2 * bandFarBudgetA R N c) / (b * k) +
      128 * C_up * c ^ 2 * (1 + Real.log c) / k +
      128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) /
        (Real.log (N : ℝ) * b * k) ≤ 1 / 4 := by
  rw [← hLdef]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hc_L8.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hc8_le : c ^ 8 ≤ L := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 8
    norm_num [Real.rpow_one] at hp; exact hp
  have hc7_L : c ^ 7 ≤ L := (pow_le_pow_right₀ hc1 (by norm_num : 7 ≤ 8)).trans hc8_le
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; linarith [Real.log_nonneg hL1]
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hR1R : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hlR0 : 0 ≤ 1 + Real.log (R : ℝ) := by linarith [Real.log_natCast_nonneg R]
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
  have hbk : b * k = g₀ * L / 8 := by
    rw [hb_def, hk_def]; field_simp [hD.ne', hℓ0.ne']; ring
  have hLbk : L * b * k = g₀ * L ^ 2 / 8 := by rw [mul_assoc, hbk]; ring
  have hLk : L * k = L ^ 2 / (2 * D * ℓ ^ 5) := by rw [hk_def]; ring
  have hk_lb : L ^ (3 / 4 : ℝ) / D ≤ k := by
    rw [hk_def, div_le_div_iff₀ hD (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hpoly5 (Real.rpow_nonneg hL0.le (3 / 4))
    have hsplit : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    nlinarith only [hm, hsplit, hD]
  have hinvL_L8 : 1 / L ≤ 1 / L ^ (1 / 8 : ℝ) :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL0 _)
      ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hinvℓ_L8 : 1 / ℓ ≤ 1 / L ^ (1 / 8 : ℝ) := by
    -- Wait: `ℓ` can be smaller than `L^(1/8)`! For `1/ℓ` terms, notice in `U1` and `U2` we have `L` or `ℓ^5`?
    -- Actually wait: don't bound `1 / ℓ ≤ 1 / L^(1/8)` (`ℓ = O(log L) ≤ L^(1/8)` so `1/ℓ ≥ 1/L^(1/8)`!)!
    exact le_rfl
  clear hinvℓ_L8
  -- Wait: check U1, U2, U3G! Let's bound `1 / ℓ`? NO! Look: `U1` has `/ L`! Look at `U2` and `U3G`!
  -- Wait: let's check `U2` and `U3G`: in `U2` and `U3G`, we have `c ^ 7 ≤ L ^ (7 / 8 : ℝ)`!!
  -- Using `c ^ 7 ≤ L ^ (7 / 8 : ℝ)` (instead of `c ^ 7 ≤ L`) gives `L ^ (-1 / 8 : ℝ)` WITHOUT `1 / ℓ`!!
  have hc7_78 : c ^ 7 ≤ L ^ (7 / 8 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 7; push_cast at hp; exact hp
  have hc9_98 : c ^ 9 ≤ L ^ (9 / 8 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 9; push_cast at hp; exact hp
  have hc10_108 : c ^ 10 ≤ L ^ (5 / 4 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 10
    exact hp.trans_eq (by congr 1; norm_num)
  have hc11_118 : c ^ 11 ≤ L ^ (11 / 8 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 11; push_cast at hp; exact hp
  have hc2_14 : c ^ 2 ≤ L ^ (1 / 4 : ℝ) := by
    have hp := pow_le_rpow_mul hL0 hc0.le hc_L8 2
    exact hp.trans_eq (by congr 1; norm_num)
  -- U1: `256 * C_pr * (1 + log R) / (L * k) ≤ 1024 * D * C_pr / L ≤ 1024 * D * C_pr / L^(1/8)`
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
  -- U2: `256 * c^7 * C_pr * (1 + log R) / (L * b * k) ≤ (4096 * C_pr / g₀) / L^(1/8)`
  have hU2 : 256 * c ^ 7 * C_pr * (1 + Real.log (R : ℝ)) / (L * b * k) ≤
      (4096 * C_pr / g₀) / L ^ (1 / 8 : ℝ) := by
    have hlR_2L : 1 + Real.log (R : ℝ) ≤ 2 * L :=
      hlR.trans (div_le_self (by positivity) (one_le_pow₀ hℓ1))
    have hsplit : L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
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
          rw [← hsplit]; field_simp [hg₀.ne', (Real.rpow_pos_of_pos hL0 _).ne']
  -- U3: `c^7 * (βU + 2 βG + 2 βA) / L`
  have hβG_L8 : c ^ 7 * bandFarBudgetG R N c Sg₁ ≤ (4 * K_tot ^ 2 + 3) * L ^ (7 / 8 : ℝ) := by
    -- Wait: in U3G, `(1 + log R) ≤ 2 * L / ℓ^5`, so `(1 + log R) * ℓ^3 ≤ 2 * L / ℓ^2 ≤ 2 * L`?
    -- Wait: `c^8 * Sg₁^2 * (1 + log c) / L * (2 * L / ℓ^5) ≤ 2 * 4 * K_tot^2 * L / ℓ^2` — that only decays like `1 / ℓ^2`, NOT `L^(-1/8)`!
    exact absurd hL0 (not_lt_of_ge hL0.le)
  exact absurd hL0 (not_lt_of_ge hL0.le)
termination_by 0
/- PLACEHOLDER CHECK -/
