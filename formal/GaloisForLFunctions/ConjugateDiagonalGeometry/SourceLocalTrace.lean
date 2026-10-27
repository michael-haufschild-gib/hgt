import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceLocalCutoff
import GaloisForLFunctions.ConjugateDiagonalGeometry.CommonSourceRegulator
import GaloisForLFunctions.RHTower.ModulusSlopeQuantization

/-!
# Local source traces and enclosed divisor mass

A smooth bump between the indicators of two concentric discs brackets
the actual xi divisor mass, including multiplicities. This connects the
local source readings to the existing integer-valued ball counts.
-/

open Complex Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open HTGeometry _root_.RHTower

/-- The local smooth trace brackets the full multiplicity in the inner and outer discs. -/
theorem sourceLocalTrace_mass_sandwich (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (xiBallOrderSum c r : ℝ) ≤ zetaSourceTrace (sourceLocalCutoff c r) ∧
      zetaSourceTrace (sourceLocalCutoff c r) ≤ (xiBallOrderSum c (2 * r) : ℝ) := by
  classical
  let T := ((MeromorphicOn.divisor xi (closedBall c (2 * r))).finiteSupport
    (isCompact_closedBall c (2 * r))).toFinset
  have hdom (u : ℂ) (hu : u ∈ T) : u ∈ closedBall c (2 * r) :=
    (MeromorphicOn.divisor xi (closedBall c (2 * r))).supportWithinDomain
      (by rwa [Set.Finite.mem_toFinset] at hu)
  have hpair : zetaSourceTrace (sourceLocalCutoff c r) =
      ∑ u ∈ T, (zeroMult xi u : ℝ) * sourceLocalCutoff c r u := by
    rw [zetaSourceTrace, ← xi_realDivisorPairing_eq_carrier _ (hasCompactSupport_sourceLocalCutoff c hr.ne')]
    apply realDivisorPairing_eq_sum
    intro u hm hφ
    have hu := sourceLocalCutoff_support c hr (subset_tsupport _ hφ)
    change u ∈ ((MeromorphicOn.divisor xi (closedBall c (2 * r))).finiteSupport
      (isCompact_closedBall c (2 * r))).toFinset
    rw [Set.Finite.mem_toFinset, Function.mem_support,
      xi_divisor_closedBall_eq_order_toNat hu]
    exact_mod_cast hm
  have houter : (xiBallOrderSum c (2 * r) : ℝ) = ∑ u ∈ T, (zeroMult xi u : ℝ) := by
    rw [xiBallOrderSum_cast_eq_finsetSum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [xi_divisor_closedBall_eq_order_toNat (hdom u hu)]
    simp only [Int.cast_natCast, zeroMult]
  have hsupp : Function.support ⇑(MeromorphicOn.divisor xi (closedBall c r)) ⊆ ↑T := by
    intro u hu
    have hne := Function.mem_support.mp hu
    have hui : u ∈ closedBall c r :=
      (MeromorphicOn.divisor xi (closedBall c r)).supportWithinDomain hu
    have huo : u ∈ closedBall c (2 * r) :=
      closedBall_subset_closedBall (by linarith only [hr]) hui
    change u ∈ ((MeromorphicOn.divisor xi (closedBall c (2 * r))).finiteSupport
      (isCompact_closedBall c (2 * r))).toFinset
    rw [Set.Finite.mem_toFinset, Function.mem_support,
      xi_divisor_closedBall_eq_order_toNat huo]
    rwa [xi_divisor_closedBall_eq_order_toNat hui] at hne
  have hinner : (xiBallOrderSum c r : ℝ) =
      ∑ u ∈ T, ((MeromorphicOn.divisor xi (closedBall c r)) u : ℝ) := by
    rw [xiBallOrderSum, finsum_eq_sum_of_support_subset _ hsupp]
    push_cast
    rfl
  rw [hpair, hinner, houter]
  constructor
  · apply Finset.sum_le_sum
    intro u hu
    by_cases hui : u ∈ closedBall c r
    · have hφ := sourceLocalCutoff_eq_one c hr
        (show ‖u - c‖ ≤ r from by simpa only [mem_closedBall, dist_eq_norm] using hui)
      rw [xi_divisor_closedBall_eq_order_toNat hui, hφ, mul_one]
      simp only [Int.cast_natCast]
      exact le_rfl
    · rw [xi_divisor_closedBall_eq_zero_of_notMem hui, Int.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (sourceLocalCutoff_nonneg _ _ _)
  · apply Finset.sum_le_sum
    intro u hu
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (sourceLocalCutoff_le_one _ _ _)

/-- A zero-free closed disc has zero enclosed multiplicity. -/
lemma xiBallOrderSum_eq_zero_of_zeroFree (c : ℂ) (r : ℝ)
    (hfree : ∀ z ∈ closedBall c r, xi z ≠ 0) : xiBallOrderSum c r = 0 := by
  have hzero (z : ℂ) : MeromorphicOn.divisor xi (closedBall c r) z = 0 := by
    by_cases hz : z ∈ closedBall c r
    · rw [xi_divisor_closedBall_eq_order_toNat hz,
        (xi_orderToNat_eq_zero_iff z).mpr (hfree z hz), Nat.cast_zero]
    · exact xi_divisor_closedBall_eq_zero_of_notMem hz
  unfold xiBallOrderSum
  calc
    (∑ᶠ z, MeromorphicOn.divisor xi (closedBall c r) z) =
        MeromorphicOn.divisor xi (closedBall c r) c :=
      finsum_eq_single (fun z => MeromorphicOn.divisor xi (closedBall c r) z) c
        (fun z _ => hzero z)
    _ = 0 := hzero c

/-- Positive local trace forces an actual zero inside the outer closed disc. -/
theorem exists_zero_of_sourceLocalTrace_pos (c : ℂ) {r : ℝ} (hr : 0 < r)
    (htrace : 0 < zetaSourceTrace (sourceLocalCutoff c r)) :
    ∃ z ∈ closedBall c (2 * r), xi z = 0 := by
  by_contra h
  push Not at h
  have hmass := (sourceLocalTrace_mass_sandwich c hr).2
  rw [xiBallOrderSum_eq_zero_of_zeroFree c (2 * r) h, Int.cast_zero] at hmass
  exact (not_lt_of_ge hmass) htrace

/-- Every zero in the inner disc supplies at least one unit of local trace. -/
theorem one_le_sourceLocalTrace_of_zero (c : ℂ) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z ∈ closedBall c r) (hzero : xi z = 0) :
    1 ≤ zetaSourceTrace (sourceLocalCutoff c r) := by
  have hmass : (1 : ℝ) ≤ (xiBallOrderSum c r : ℝ) := by
    exact_mod_cast one_le_xiBallOrderSum_of_zero hz hzero
  exact hmass.trans (sourceLocalTrace_mass_sandwich c hr).1

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceLocalTrace_mass_sandwich
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_zero_of_sourceLocalTrace_pos
