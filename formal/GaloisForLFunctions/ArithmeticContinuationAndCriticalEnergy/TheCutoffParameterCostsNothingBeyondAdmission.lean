import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.FiniteHeadCutoffTransportAndPhysicalShellCost
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy

/-!
# The cutoff parameter costs nothing beyond admission

Cutoff transport pays every change of denominator cutoff along a growing-head schedule, but the
exact stage balance also exposes a *physical shell*: the cells between the old and the new horizon,
measured with the new cutoff.  The accumulated shell cost was the cutoff analogue of the damping
budget, and it was open whether it is a second arithmetic obligation.

It is not.  On a shell the Ramanujan prefix differs from the actual source by at most
`n Q^{-β} C_{ε,β}`, and the pronic weight turns that into a geometric contribution, so each stage
costs at most twice the actual energy of its own cells plus one geometric term
(`ramanujanPhysicalShellEnergy_le_energy_add`).  Along the dyadic schedule `T_j = 2^j` with
cutoffs `R_j = 2^{m(j+1)}` and `m ε > 1` the cells of different stages are disjoint and exhaust the
horizon, so the shells telescope into the critical energy
(`sum_shellWindow_energy_eq`), and the geometric terms sum
(`summable_shellErrorBudget`).  Hence:

* with admission at a damping, the accumulated shell cost is bounded at that damping, with no
  further arithmetic input (`exists_bound_sum_ramanujanPhysicalShellEnergy_of_admits`).

So the cutoff parameter is free: a continuation in the cutoff adds nothing to the damping problem,
and the open obligation of the programme is the damping one alone.
-/

open Finset RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. On a shell the Ramanujan prefix is the actual source, up to a geometric term -/

/-- At an integer horizon the complex remainder is the real centred prefix. -/
theorem norm_pmPowerDampedDivisorRemainder_natCast {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ‖pmPowerDampedDivisorRemainder ε n‖ = |pmPowerDampedCenteredDivisorPrefix ε n| := by
  rw [pmPowerDampedDivisorRemainder_eq_centered_prefix hε (Nat.cast_nonneg n)]
  simp

/-- The energy of the actual source on a window of horizons. -/
def shellWindowEnergy (ε : ℝ) (T U : ℕ) : ℝ :=
  ∑ n ∈ Ioc T U, pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

theorem shellWindowEnergy_nonneg (ε : ℝ) (T U : ℕ) : 0 ≤ shellWindowEnergy ε T U :=
  sum_nonneg fun n _ => by positivity

/-- **One stage of the shell cost.**  The exposed cells cost at most twice their actual energy plus
a geometric term in the cutoff. -/
theorem ramanujanPhysicalShellEnergy_le_energy_add {ε β : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β)
    (hβε : β < ε) {R T U : ℕ} (hR : 0 < R) (hUR : U ≤ R) :
    ramanujanPhysicalShellEnergy ε R T U ≤
      2 * shellWindowEnergy ε T U +
        2 * (U : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 := by
  have hC : 0 ≤ ramanujanCutoffErrorConstant ε β := ramanujanCutoffErrorConstant_nonneg ε β
  have hcell : ∀ n ∈ Ioc T U,
      ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        2 * (pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
          2 * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hw : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have herr : ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n -
        pmPowerDampedDivisorRemainder ε n‖ ≤
          (n : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) := by
      have h := norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le hε hβ hβε hR
        (hn.2.trans hUR)
      simpa only [ramanujanCutoffErrorConstant, mul_assoc] using h
    have htri : ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n‖ ≤
        |pmPowerDampedCenteredDivisorPrefix ε n| +
          (n : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) := by
      have h := norm_add_le (pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n -
        pmPowerDampedDivisorRemainder ε n) (pmPowerDampedDivisorRemainder ε n)
      rw [sub_add_cancel, norm_pmPowerDampedDivisorRemainder_natCast hε] at h
      linarith
    have hsq : ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n‖ ^ 2 ≤
        2 * pmPowerDampedCenteredDivisorPrefix ε n ^ 2 +
          2 * ((n : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β)) ^ 2 := by
      have h1 : (0 : ℝ) ≤ |pmPowerDampedCenteredDivisorPrefix ε n| := abs_nonneg _
      have h2 : (0 : ℝ) ≤ (n : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) := by
        have : (0 : ℝ) ≤ (R : ℝ) ^ (-β) := Real.rpow_nonneg (Nat.cast_nonneg R) _
        positivity
      have hmono := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have habs : |pmPowerDampedCenteredDivisorPrefix ε n| ^ 2 =
          pmPowerDampedCenteredDivisorPrefix ε n ^ 2 := sq_abs _
      nlinarith [sq_nonneg (|pmPowerDampedCenteredDivisorPrefix ε n| -
        (n : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β))]
    rw [div_le_iff₀ hw]
    have hfac : ((n : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β)) ^ 2 =
        ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 * (n : ℝ) ^ 2 := by ring
    have hle : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
    have hE : (0 : ℝ) ≤ ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 := sq_nonneg _
    calc ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n‖ ^ 2
        ≤ 2 * pmPowerDampedCenteredDivisorPrefix ε n ^ 2 +
            2 * (((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 * (n : ℝ) ^ 2) := by
          rw [← hfac]; exact hsq
      _ ≤ 2 * pmPowerDampedCenteredDivisorPrefix ε n ^ 2 +
            2 * (((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 *
              ((n : ℝ) * ((n : ℝ) + 1))) := by
          have := mul_le_mul_of_nonneg_left hle hE
          linarith
      _ = (2 * (pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2) *
              ((n : ℝ) * ((n : ℝ) + 1)) := by
          field_simp
  calc ramanujanPhysicalShellEnergy ε R T U
      ≤ ∑ _n ∈ Ioc T U, (2 * (pmPowerDampedCenteredDivisorPrefix ε _n ^ 2 /
          ((_n : ℝ) * ((_n : ℝ) + 1))) +
          2 * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2) :=
        sum_le_sum hcell
    _ = 2 * shellWindowEnergy ε T U +
          ((Ioc T U).card : ℝ) * (2 * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, shellWindowEnergy, mul_sum]
    _ ≤ 2 * shellWindowEnergy ε T U +
          2 * (U : ℝ) * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 := by
        have hcard : ((Ioc T U).card : ℝ) ≤ (U : ℝ) := by
          rw [Nat.card_Ioc]
          have : (U - T : ℕ) ≤ U := by omega
          exact_mod_cast this
        have hE : (0 : ℝ) ≤ 2 * ((R : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 := by
          positivity
        nlinarith

/-! ## §2. The shells telescope into the critical energy -/

/-- The dyadic shells exhaust the horizon: their energies sum to the energy above the first cell. -/
theorem sum_shellWindow_energy_eq (ε : ℝ) (J : ℕ) :
    (∑ j ∈ range J, shellWindowEnergy ε (2 ^ j) (2 ^ (j + 1))) = shellWindowEnergy ε 1 (2 ^ J) := by
  induction J with
  | zero => simp [shellWindowEnergy]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, shellWindowEnergy, shellWindowEnergy, shellWindowEnergy,
      sum_Ioc_consecutive _ (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ J))]

theorem shellWindowEnergy_one_le_energy (ε : ℝ) (T : ℕ) :
    shellWindowEnergy ε 1 T ≤ dampedMobiusEnergy ε T := by
  have hsub : Ioc 1 T ⊆ Icc 1 T := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  unfold shellWindowEnergy dampedMobiusEnergy pmPowerDampedDivisorDiscreteEnergy
  exact sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity

/-! ## §3. The accumulated shell cost is bounded by admission alone -/

/-- The dyadic cutoff scale, as a geometric factor. -/
private theorem dyadic_shell_scale (ε : ℝ) (m j : ℕ) :
    ((2 : ℕ) ^ (m * (j + 1)) : ℝ) ^ (-(ε / 2)) =
      ((2 : ℝ) ^ (-((m : ℝ) * ε / 2))) ^ (j + 1) := by
  push_cast
  rw [← Real.rpow_natCast (2 : ℝ) (m * (j + 1)), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast ((2 : ℝ) ^ (-((m : ℝ) * ε / 2))) (j + 1),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

/-- The geometric ratio of the shell error budget. -/
def shellRatio (ε : ℝ) (m : ℕ) : ℝ := 2 * ((2 : ℝ) ^ (-((m : ℝ) * ε / 2))) ^ 2

theorem shellRatio_nonneg (ε : ℝ) (m : ℕ) : 0 ≤ shellRatio ε m := by
  rw [shellRatio]
  positivity

theorem shellRatio_lt_one {ε : ℝ} {m : ℕ} (hmε : 1 < (m : ℝ) * ε) : shellRatio ε m < 1 := by
  have hq2 : ((2 : ℝ) ^ (-((m : ℝ) * ε / 2))) ^ 2 = (2 : ℝ) ^ (-((m : ℝ) * ε)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-((m : ℝ) * ε / 2))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have hcomb : (2 : ℝ) * (2 : ℝ) ^ (-((m : ℝ) * ε)) = (2 : ℝ) ^ (1 - (m : ℝ) * ε) := by
    rw [show (1 : ℝ) - (m : ℝ) * ε = 1 + -((m : ℝ) * ε) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [shellRatio, hq2, hcomb]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- Each stage's error term is a term of a geometric series. -/
theorem shellError_eq (ε C : ℝ) (m j : ℕ) :
    2 * ((2 : ℝ) ^ (j + 1)) * (((2 : ℕ) ^ (m * (j + 1)) : ℝ) ^ (-(ε / 2)) * C) ^ 2 =
      2 * C ^ 2 * shellRatio ε m ^ (j + 1) := by
  rw [dyadic_shell_scale, shellRatio]
  ring

/-- The geometric budget of the shell errors along the dyadic schedule. -/
theorem summable_shellErrorBudget {ε : ℝ} {m : ℕ} (hmε : 1 < (m : ℝ) * ε) :
    Summable (fun j : ℕ => 2 * ((2 : ℝ) ^ (j + 1)) *
      (((2 : ℕ) ^ (m * (j + 1)) : ℝ) ^ (-(ε / 2)) *
        ramanujanCutoffErrorConstant ε (ε / 2)) ^ 2) := by
  have hfun : (fun j : ℕ => 2 * ((2 : ℝ) ^ (j + 1)) *
      (((2 : ℕ) ^ (m * (j + 1)) : ℝ) ^ (-(ε / 2)) *
        ramanujanCutoffErrorConstant ε (ε / 2)) ^ 2) =
      fun j : ℕ => (2 * ramanujanCutoffErrorConstant ε (ε / 2) ^ 2 * shellRatio ε m) *
        shellRatio ε m ^ j :=
    funext fun j => by rw [shellError_eq]; ring
  rw [hfun]
  refine Summable.mul_left _ (summable_geometric_iff_norm_lt_one.mpr ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (shellRatio_nonneg ε m)]
  exact shellRatio_lt_one hmε

/-- **The cutoff parameter is free.**  Given admission at a damping, the accumulated physical shell
cost of the dyadic cutoff transport is bounded there, with no further arithmetic input. -/
theorem exists_bound_sum_ramanujanPhysicalShellEnergy_of_admits {ε : ℝ} (hε : 0 < ε)
    (hadm : Admits dampedMobiusEnergy ε) :
    ∃ m : ℕ, 1 ≤ m ∧ 1 < (m : ℝ) * ε ∧ ∃ K : ℝ, ∀ J : ℕ,
      (∑ j ∈ range J, ramanujanPhysicalShellEnergy ε (2 ^ (m * (j + 1))) (2 ^ j) (2 ^ (j + 1)))
        ≤ K := by
  obtain ⟨m, hm1, hmε, -⟩ := exists_summable_ramanujanCutoffTransport_depth hε
  obtain ⟨B, hB⟩ := hadm
  have hsum := summable_shellErrorBudget hmε
  refine ⟨m, hm1, hmε, 2 * max B 0 + ∑' j : ℕ, 2 * ((2 : ℝ) ^ (j + 1)) *
    (((2 : ℕ) ^ (m * (j + 1)) : ℝ) ^ (-(ε / 2)) *
      ramanujanCutoffErrorConstant ε (ε / 2)) ^ 2, fun J => ?_⟩
  have hstage : ∀ j ∈ range J,
      ramanujanPhysicalShellEnergy ε (2 ^ (m * (j + 1))) (2 ^ j) (2 ^ (j + 1)) ≤
        2 * shellWindowEnergy ε (2 ^ j) (2 ^ (j + 1)) +
          2 * ((2 : ℝ) ^ (j + 1)) * ((((2 : ℕ) ^ (m * (j + 1)) : ℕ) : ℝ) ^ (-(ε / 2)) *
            ramanujanCutoffErrorConstant ε (ε / 2)) ^ 2 := by
    intro j _
    have hUR : (2 : ℕ) ^ (j + 1) ≤ 2 ^ (m * (j + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm1)
    have h := ramanujanPhysicalShellEnergy_le_energy_add hε (by positivity : (0 : ℝ) ≤ ε / 2)
      (by linarith : ε / 2 < ε) (R := 2 ^ (m * (j + 1))) (T := 2 ^ j) (U := 2 ^ (j + 1))
      (by positivity) hUR
    have hcast : (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by push_cast; ring
    rw [hcast] at h
    exact h
  calc (∑ j ∈ range J, ramanujanPhysicalShellEnergy ε (2 ^ (m * (j + 1))) (2 ^ j) (2 ^ (j + 1)))
      ≤ ∑ j ∈ range J, (2 * shellWindowEnergy ε (2 ^ j) (2 ^ (j + 1)) +
          2 * ((2 : ℝ) ^ (j + 1)) * ((((2 : ℕ) ^ (m * (j + 1)) : ℕ) : ℝ) ^ (-(ε / 2)) *
            ramanujanCutoffErrorConstant ε (ε / 2)) ^ 2) := sum_le_sum hstage
    _ = 2 * shellWindowEnergy ε 1 (2 ^ J) +
          ∑ j ∈ range J, 2 * ((2 : ℝ) ^ (j + 1)) *
            ((((2 : ℕ) ^ (m * (j + 1)) : ℕ) : ℝ) ^ (-(ε / 2)) *
              ramanujanCutoffErrorConstant ε (ε / 2)) ^ 2 := by
        rw [sum_add_distrib, ← mul_sum, sum_shellWindow_energy_eq]
    _ ≤ 2 * max B 0 + ∑' j : ℕ, 2 * ((2 : ℝ) ^ (j + 1)) *
          (((2 : ℕ) ^ (m * (j + 1)) : ℝ) ^ (-(ε / 2)) *
            ramanujanCutoffErrorConstant ε (ε / 2)) ^ 2 := by
        have h1 : shellWindowEnergy ε 1 (2 ^ J) ≤ max B 0 :=
          (shellWindowEnergy_one_le_energy ε (2 ^ J)).trans ((hB _).trans (le_max_left B 0))
        have h2 := hsum.sum_le_tsum (range J) fun j _ => by positivity
        push_cast at h2 ⊢
        linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
