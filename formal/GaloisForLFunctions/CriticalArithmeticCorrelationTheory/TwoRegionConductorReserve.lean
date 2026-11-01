import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSeparatedPrefixRetainsItsDefect
import GaloisForLFunctions.CompletedArithmeticForms.ConductorPrefixLeakage

/-!
# Two mass reserves on the conductor-orthogonal complement

The prefix keeps a fixed fraction of the full reverse defect gap. Its projection
leak is paid from the terminal reserve, whose coefficient loses only `c⁷`.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis
open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms CriticalScaleArithmeticRigidity

/-- Enlarging the conductor cutoff pays the global mass cost while preserving distinct
prefix and terminal coercivity. -/
theorem exists_completeWeilEnergy_two_region_conductor_reserve :
    ∃ a K H : ℝ, 0 < a ∧ a ≤ 1 / 8 ∧ 0 < K ∧ 0 < H ∧
      ∀ {c : ℝ} {R N : ℕ}, 1 ≤ c → 2 ≤ R → H * c ^ 8 ≤ (N : ℝ) →
        R * R ≤ N / growingDefectCutoff c →
        18 * (1 + Real.log R) ≤ Real.log (N / growingDefectCutoff c : ℕ) →
        K * c ^ 16 ≤ Real.log R / explicitConductorCutoffConstant - 1 →
        terminalPacketCost R (N / growingDefectCutoff c) N /
          Real.log (N / growingDefectCutoff c : ℕ) ≤ a / (4 * c ^ 7) →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
        (Real.log R / explicitConductorCutoffConstant - 1) / 4 *
          (∑ n ∈ Icc 1 (N / growingDefectCutoff c), primeHorizonExtension w n ^ 2) +
        a * (Real.log R / explicitConductorCutoffConstant - 1) / (2 * c ^ 7) *
          (∑ n ∈ Ioc (N / growingDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N w := by
  obtain ⟨a, C, H, ha, ha8, hC, hH, hreserve⟩ := exists_completeWeilEnergy_prefix_reserve_polynomial
  refine ⟨a, 4 * C / a, H, ha, ha8, by positivity, hH, ?_⟩
  intro c R N hc hR hN hRM hlog hcut hleak w hw
  let M := N / growingDefectCutoff c
  let x := primeHorizonExtension w
  let P := ∑ n ∈ Icc 1 M, x n ^ 2
  let S := ∑ n ∈ Ioc M N, x n ^ 2
  let k := Real.log R / explicitConductorCutoffConstant - 1
  let B := terminalPacketCost R M N / Real.log M
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hM : 2 ≤ M := by have hh := Nat.mul_le_mul hR hR; omega
  have hMN : M ≤ N := Nat.div_le_self N (growingDefectCutoff c)
  have hN2 : 2 ≤ N := hM.trans hMN
  have hk : 0 < k := (mul_pos (div_pos (mul_pos (by norm_num) hC) ha) (pow_pos hc0 16)).trans_le hcut
  have hscale : explicitConductorCutoffConstant ≤ Real.log R := by
    have hh : 1 ≤ Real.log R / explicitConductorCutoffConstant := by dsimp only [k] at hk; linarith only [hk]
    simpa only [one_mul] using (le_div_iff₀ explicitConductorCutoffConstant_pos).mp hh
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hsplit : ‖w‖ ^ 2 = P + S := by
    rw [← sum_primeHorizonExtension_sq]
    have hs : (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
      omega
    dsimp only [P, S, x]
    rw [hs, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR hM hMN hRM hlog hscale hw
  have hwhole := poleDefect_ge_explicit_on_conductor_orthogonal hR hN2 hw
  have htwoB : 2 * terminalPacketCost R M N / Real.log M = 2 * B := by
    dsimp only [B]
    ring
  rw [htwoB] at hpre
  change k * ((15 / 16 : ℝ) * P - 2 * B * S) ≤ poleDefect M x at hpre
  rw [hsplit] at hwhole
  change k * (P + S) ≤ poleDefect N x at hwhole
  have hraw := hreserve c hc N hN w
  rw [hsplit] at hraw
  change (1 / 2 : ℝ) * poleDefect M x + a / c ^ 7 * poleDefect N x -
    C * c ^ 9 * (P + S) ≤ completeWeilEnergy tiltedUnitSpline c N w at hraw
  have hcost : C * c ^ 9 ≤ a * k / (4 * c ^ 7) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * c ^ 7)).mpr
    have hh := mul_le_mul_of_nonneg_left hcut ha.le
    have he : a * (4 * C / a * c ^ 16) = 4 * C * c ^ 16 := by field_simp [ha.ne']
    rw [he] at hh
    change _ ≤ a * k at hh
    exact (show C * c ^ 9 * (4 * c ^ 7) = 4 * C * c ^ 16 by ring).trans_le hh
  have hpre' := mul_le_mul_of_nonneg_left hpre (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hwhole' := mul_le_mul_of_nonneg_left hwhole (div_nonneg ha.le (pow_nonneg hc0.le 7))
  have hcost' := mul_le_mul_of_nonneg_right hcost (add_nonneg hP hS)
  have hleak' := mul_le_mul_of_nonneg_left hleak (mul_nonneg hk.le hS)
  change (k * S) * B ≤ (k * S) * (a / (4 * c ^ 7)) at hleak'
  have hpay : (1 / 2 : ℝ) * poleDefect M x + a / c ^ 7 * poleDefect N x -
      C * c ^ 9 * (P + S) ≥
        (15 / 32 : ℝ) * k * P + 3 * a * k / (4 * c ^ 7) * P +
          a * k / (2 * c ^ 7) * S := by
    calc
      _ = (15 / 32 : ℝ) * k * P + 3 * a * k / (4 * c ^ 7) * P +
          3 * a * k / (4 * c ^ 7) * S - k * S * (a / (4 * c ^ 7)) := by
        field_simp [hc0.ne']
        ring
      _ ≤ (15 / 32 : ℝ) * k * P + 3 * a * k / (4 * c ^ 7) * P +
          3 * a * k / (4 * c ^ 7) * S - k * S * B := sub_le_sub_left hleak' _
      _ = (1 / 2 : ℝ) * (k * ((15 / 16 : ℝ) * P - 2 * B * S)) +
          a / c ^ 7 * (k * (P + S)) - a * k / (4 * c ^ 7) * (P + S) := by
        field_simp [hc0.ne']
        ring
      _ ≤ _ := sub_le_sub (add_le_add hpre' hwhole') hcost'
  have hpextra : 0 ≤ 3 * a * k / (4 * c ^ 7) * P := by positivity
  have hkP : 0 ≤ k * P := mul_nonneg hk.le hP
  change k / 4 * P + a * k / (2 * c ^ 7) * S ≤ _
  linarith only [hraw, hpay, hpextra, hkP]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeilEnergy_two_region_conductor_reserve
