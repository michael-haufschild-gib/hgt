import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheEvenFlipShiftsThePoleValueByTheEvenPartOfTheKernel
import GaloisForLFunctions.TransHorizonIncidenceMechanics.LogarithmicMomentsAreACompleteReceiverInvariant

/-!
# Simultaneous Odd–Even Pole Calibration and Logarithmic Moment Pinning

On the small-scale cofactor side (`TransHorizonIncidenceMechanics`), any weight of the form
`c = k ⋆ o` (`o = oddSqfWeight ε`, `k` supported on `[1, J]` and vanishing on multiples of `4`)
admits an even flip `c^♭ = k^♭ ⋆ o` (`k^♭ = flipKernelOf k`) with identical Ramanujan amplitude
moduli `|B_e(c^♭)| = |B_e(c)|` at every modulus `e`.

This file proves the **Simultaneous Odd–Even Pole Calibration Law** and couples it with the
**Logarithmic Moment Receiver Completeness Theorem**:
1. Decomposes the pole value into its odd-kernel and even-kernel components:
   `poleValue k J ε = poleValue (oddPartKernel k) J ε + 2^{ε - 1} * poleValue (evenPartWeight k) J ε`
   (`poleValue_eq_oddPartKernel_add_evenPartWeight`).
2. Proves that `c = k ⋆ o` and its even flip `c^♭ = k^♭ ⋆ o` are simultaneously `ReceiverBounded`
   if and only if `poleValue k J ε = 0 ∧ poleValue (evenPartWeight k) J ε = 0`
   (`both_evenFlip_pair_receiverBounded_iff`), which is in turn equivalent to the simultaneous
   vanishing of both the odd and even kernel parts at the pole:
   `poleValue (oddPartKernel k) J ε = 0 ∧ poleValue (evenPartWeight k) J ε = 0`
   (`both_evenFlip_pair_receiverBounded_iff_odd_and_even_pole`).
3. Proves that on the generalized Fermi locus (`poleValue k J ε = 0` and
   `poleValue (evenPartWeight k) J ε ≠ 0`), even though `c` and `c^♭` have identical Ramanujan
   amplitudes at all moduli `e`, some logarithmic pronic moment `M(· log^m)` strictly separates
   them (`exists_logMoment_ne_of_fermi_evenFlip`), while equality of all logarithmic moments
   pins `c^♭ d = c d` for all `d ≥ 2` (`evenFlip_eq_of_logMoments_eq`).
-/

noncomputable section

open Finset Filter Topology BigOperators Real

namespace GaloisForLFunctions.SmoothBernoulliPoleCalibration

open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- Exact decomposition of `poleValue k J ε` into the pole values of `oddPartKernel k` and
`evenPartWeight k` for any kernel `k` on `[1, J]` vanishing on multiples of `4`. -/
theorem poleValue_eq_oddPartKernel_add_evenPartWeight {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) (ε : ℝ) :
    poleValue k J ε =
      poleValue (oddPartKernel k) J ε + (2 : ℝ) ^ (ε - 1) * poleValue (evenPartWeight k) J ε := by
  have hshift : ∑ j ∈ Icc 1 J, shiftTwo (evenPartWeight k) j * (j : ℝ) ^ (-(1 - ε)) =
      (2 : ℝ) ^ (ε - 1) * poleValue (evenPartWeight k) J ε := by
    have hfilter : ∑ j ∈ Icc 1 J, shiftTwo (evenPartWeight k) j * (j : ℝ) ^ (-(1 - ε)) =
        ∑ j ∈ (Icc 1 J).filter (fun j => 2 ∣ j),
          evenPartWeight k (j / 2) * (j : ℝ) ^ (-(1 - ε)) := by
      rw [sum_filter]
      exact sum_congr rfl fun j _ => by unfold shiftTwo; split_ifs <;> simp
    rw [hfilter, RHTower.sum_Icc_filter_dvd_reindex 2 J two_pos, poleValue]
    have hJ : ∑ i ∈ Icc 1 J, evenPartWeight k i * (i : ℝ) ^ (-(1 - ε)) =
        ∑ i ∈ Icc 1 (J / 2), evenPartWeight k i * (i : ℝ) ^ (-(1 - ε)) := by
      refine (sum_subset (Icc_subset_Icc le_rfl (Nat.div_le_self J 2)) fun i hi hiJ => ?_).symm
      have : J < 2 * i := by simp only [mem_Icc] at hi hiJ; omega
      simp [evenPartWeight, hkJ (2 * i) this]
    rw [hJ, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (mem_Icc.mp hi).1
    rw [Nat.mul_div_cancel_left i two_pos, Nat.cast_mul, Nat.cast_two,
      Real.mul_rpow (by norm_num) hi0.le, show -(1 - ε) = ε - 1 by ring]
    ring
  rw [← hshift, poleValue, poleValue, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by rw [kernel_eq_odd_add_shift hk4 j]; ring

/-- Both members `c = k ⋆ o` and `c^♭ = k^♭ ⋆ o` of an even-flip pair over the odd squarefree
weight are `ReceiverBounded` if and only if both `poleValue k J ε = 0` and
`poleValue (evenPartWeight k) J ε = 0`. -/
theorem both_evenFlip_pair_receiverBounded_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
      ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε))) ↔
      (poleValue k J ε = 0 ∧ poleValue (evenPartWeight k) J ε = 0) := by
  obtain ⟨_, _, _, hiff, _, hpres, hnot⟩ := evenFlip_exactLoss hε hε2 hk4 hkJ
  constructor
  · intro hboth
    refine ⟨hiff.mp hboth.1, ?_⟩
    by_contra he
    exact hnot he hboth
  · rintro ⟨hk0, he0⟩
    have hc : ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) := hiff.mpr hk0
    exact ⟨hc, (hpres he0).mp hc⟩

/-- **Simultaneous Odd–Even Pole Calibration Law.**
Both members `c = k ⋆ o` and `c^♭ = k^♭ ⋆ o` of an even-flip pair are `ReceiverBounded` if and
only if both the odd part `oddPartKernel k` and the even part `evenPartWeight k` vanish at the
pole `s = 1 - ε`. -/
theorem both_evenFlip_pair_receiverBounded_iff_odd_and_even_pole
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
      ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε))) ↔
      (poleValue (oddPartKernel k) J ε = 0 ∧ poleValue (evenPartWeight k) J ε = 0) := by
  rw [both_evenFlip_pair_receiverBounded_iff hε hε2 hk4 hkJ,
    poleValue_eq_oddPartKernel_add_evenPartWeight hk4 hkJ ε]
  constructor
  · rintro ⟨hsum, he0⟩
    rw [he0, mul_zero, add_zero] at hsum
    exact ⟨hsum, he0⟩
  · rintro ⟨ho0, he0⟩
    rw [ho0, he0, mul_zero, add_zero]
    exact ⟨rfl, rfl⟩

/-- **Logarithmic Moment Separation on the Generalized Fermi Horizon.**
If `poleValue k J ε = 0` (so `c = k ⋆ o` is `ReceiverBounded`) but
`poleValue (evenPartWeight k) J ε ≠ 0` (so `k` fails even-pole calibration), then:
1. `c` and `c^♭` have identical Ramanujan amplitude moduli at every modulus `e`,
2. `c` is `ReceiverBounded` while `c^♭` is not `ReceiverBounded`, and
3. there exists a logarithmic moment order `m : ℕ` such that
   `firstPronicMoment (logPowWeight c m) ≠ firstPronicMoment (logPowWeight c^♭ m)`. -/
theorem exists_logMoment_ne_of_fermi_evenFlip {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (hk0 : poleValue k J ε = 0) (he_ne : poleValue (evenPartWeight k) J ε ≠ 0) :
    (∀ e, |weightRamanujanCoeff (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) e| =
      |weightRamanujanCoeff (RHTower.dirichletConv k (oddSqfWeight ε)) e|) ∧
    ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
    ¬ ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) ∧
    ∃ m : ℕ,
      firstPronicMoment (logPowWeight (RHTower.dirichletConv k (oddSqfWeight ε)) m) ≠
        firstPronicMoment (logPowWeight (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) m) := by
  obtain ⟨_, hram, _, hiff, _, _, hnot⟩ := evenFlip_exactLoss hε hε2 hk4 hkJ
  have hc : ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) := hiff.mpr hk0
  have hc_flip : ¬ ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) :=
    fun hflip => hnot he_ne ⟨hc, hflip⟩
  have hdiff : ¬ (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ↔
      ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε))) := by
    intro heq
    exact hc_flip (heq.mp hc)
  have h_log := exists_logMoment_ne hε
    (dirichletConv_oddSqfWeight_mem_dampedClass hkJ ε)
    (dirichletConv_oddSqfWeight_mem_dampedClass (flipKernelOf_support hkJ) ε)
    hdiff
  exact ⟨hram, hc, hc_flip, h_log⟩

/-- **Logarithmic Moment Pinning of the Even Flip.**
If `c = k ⋆ o` and its even flip `c^♭ = k^♭ ⋆ o` have equal logarithmic pronic moments of every
order `m : ℕ`, then `c d = c^♭ d` for all `d ≥ 2`, and their receivers have identical
boundedness status. -/
theorem evenFlip_eq_of_logMoments_eq {ε : ℝ} (hε : 0 < ε)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (hM : ∀ m : ℕ,
      firstPronicMoment (logPowWeight (RHTower.dirichletConv k (oddSqfWeight ε)) m) =
        firstPronicMoment (logPowWeight (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) m)) :
    (∀ d : ℕ, 2 ≤ d →
      RHTower.dirichletConv k (oddSqfWeight ε) d =
        RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε) d) ∧
    (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ↔
      ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε))) := by
  have hc_damped := dirichletConv_oddSqfWeight_mem_dampedClass hkJ ε
  have hflip_damped := dirichletConv_oddSqfWeight_mem_dampedClass (flipKernelOf_support hkJ) ε
  have heq_d := eq_add_unitMass_of_logMoments_eq hε hc_damped hflip_damped hM
  refine ⟨heq_d, ?_⟩
  by_contra hdiff
  obtain ⟨m, hm⟩ := exists_logMoment_ne hε hc_damped hflip_damped hdiff
  exact hm (hM m)

end GaloisForLFunctions.SmoothBernoulliPoleCalibration
