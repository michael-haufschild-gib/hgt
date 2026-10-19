import GaloisForLFunctions.BiScaleUncertainty.SieveLinearVisibility
import GaloisForLFunctions.BiScaleUncertainty.SieveVisibilitySpikeEstimate

/-! Actual missing-mode perturbations and cubic bounds for complete raw lag arrays. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
open ValuationPhase ParityNeighborhood
set_option autoImplicit false

/-- Coordinates outside the actual active support vanish, including orders outside the cutoff. -/
theorem coordinate_zero_of_not_active (N : ℕ) (b : ℕ → ℝ) (q : ℕ)
    (hq : q ∉ activeModes N b) : selbergMultiplesCoord N b q = 0 := by
  by_cases hqN : q ∈ Icc 1 N
  · by_contra hne
    exact hq (mem_filter.mpr ⟨hqN, hne⟩)
  · exact selbergMultiplesCoord_eq_zero_of_notMem b hqN

/-- A finite positive budget bounds every base coordinate. -/
def coordinateBudget (N : ℕ) (b : ℕ → ℝ) : ℝ :=
  1+∑ q ∈ Icc 1 N, |selbergMultiplesCoord N b q|

theorem coordinateBudget_one_le (N : ℕ) (b : ℕ → ℝ) : 1 ≤ coordinateBudget N b := by
  have := Finset.sum_nonneg (s := Icc 1 N)
    (f := fun q => |selbergMultiplesCoord N b q|) (fun _ _ => abs_nonneg _)
  dsimp [coordinateBudget]
  linarith

theorem coordinate_le_budget (N : ℕ) (b : ℕ → ℝ) (q : ℕ) :
    |selbergMultiplesCoord N b q| ≤ coordinateBudget N b := by
  by_cases hq : q ∈ Icc 1 N
  · have := single_le_sum (s := Icc 1 N)
      (f := fun u => |selbergMultiplesCoord N b u|) (fun _ _ => abs_nonneg _) hq
    dsimp [coordinateBudget]
    linarith
  · rw [selbergMultiplesCoord_eq_zero_of_notMem b hq, abs_zero]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans (coordinateBudget_one_le N b)

/-- Actual divisor weights with one replaced signed coordinate. -/
def spikeWeights (N : ℕ) (b : ℕ → ℝ) (q : ℕ) (t : ℝ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (spikeProfile (selbergMultiplesCoord N b) q t) N

theorem coordinate_spikeWeights (N : ℕ) (b : ℕ → ℝ) (q : ℕ) (t : ℝ)
    (hq : q ∈ Icc 1 N) (u : ℕ) :
    selbergMultiplesCoord N (spikeWeights N b q t) u =
      spikeProfile (selbergMultiplesCoord N b) q t u := by
  rw [spikeWeights, selbergMultiplesCoord_ramanujan_inverse]
  by_cases hu : u ∈ Icc 1 N
  · rw [if_pos hu]
  · have huq : u ≠ q := by intro h; subst u; exact hu hq
    simp [hu, spikeProfile, huq, selbergMultiplesCoord_eq_zero_of_notMem b hu]

/-- A missing-coordinate spike enters every physical neighborhood at linear speed. -/
theorem spike_near_base (N : ℕ) (b : ℕ → ℝ) (q : ℕ) (hq : q ∈ Icc 1 N)
    (hb : selbergMultiplesCoord N b q = 0) (t : ℝ) (n : ℕ) :
    |sieveSeq N (spikeWeights N b q t) n-sieveSeq N b n| ≤ (q.totient : ℝ)*|t| := by
  calc
    _ ≤ ∑ u ∈ Icc 1 N, (u.totient : ℝ)*
        |selbergMultiplesCoord N (spikeWeights N b q t) u-selbergMultiplesCoord N b u| :=
      sieveSeq_error_le_coordinate_sum N (spikeWeights N b q t) b n
    _ = ∑ u ∈ Icc 1 N, if u = q then (q.totient : ℝ)*|t| else 0 := by
      apply sum_congr rfl
      intro u _
      rw [coordinate_spikeWeights N b q t hq]
      by_cases hu : u = q
      · subst u
        simp [spikeProfile, hb]
      · simp [spikeProfile, hu]
    _ = _ := by simp [hq]

/-- Invisibility excludes the sole first-order sign-changing resonance. -/
theorem invisible_resonant_error (N : ℕ) (b : ℕ → ℝ) (q : ℕ) (hq : q ∈ Icc 1 N)
    (hv : ¬Visible N (activeModes N b) q) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) (hm : m = 5 ∨ m = 6) (r : Fin m → ZMod N.factorial) (hz : (∑ i, r i) = 0) :
    |(∏ i, selbergMultiplesCoord N (spikeWeights N b q t) (addOrderOf (r i)))-
      (∏ i, selbergMultiplesCoord N (spikeWeights N b q (-t)) (addOrderOf (r i)))| ≤
      2*(coordinateBudget N b)^6*t^3 := by
  classical
  have hm6 : Fintype.card (Fin m) ≤ 6 := by rcases hm with rfl | rfl <;> simp
  have hdeg : (∀ i, addOrderOf (r i) ≠ q → selbergMultiplesCoord N b (addOrderOf (r i)) ≠ 0) →
      Odd (orderCount r q) → 3 ≤ orderCount r q := by
    intro hs ho
    have hn : orderCount r q ≠ 1 := by
      intro h1
      obtain ⟨i, hi, hother⟩ := orderCount_eq_one_witness r q h1
      apply hv
      refine ⟨m, hm, r, hz, i, hi, ?_⟩
      intro j hji
      by_contra hj
      exact hs j (hother j hji) (coordinate_zero_of_not_active N b _ hj)
    rcases ho with ⟨k, hk⟩
    omega
  have hh := spike_product_error (fun i => addOrderOf (r i)) (selbergMultiplesCoord N b)
    q t (coordinateBudget N b) hm6 ht ht1 (coordinateBudget_one_le N b)
    (coordinate_le_budget N b) hdeg
  simpa only [coordinate_spikeWeights N b q t hq, coordinate_spikeWeights N b q (-t) hq]
    using hh

/-- Full literal fifth/sixth arrays change at most cubically at an invisible missing mode. -/
theorem invisible_raw_error (N : ℕ) (b : ℕ → ℝ) (q : ℕ) (hq : q ∈ Icc 1 N)
    (hv : ¬Visible N (activeModes N b) q) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) (hm : m = 5 ∨ m = 6) (v : Fin m → ℕ) :
    |translatedMoment N (spikeWeights N b q t) v-
      translatedMoment N (spikeWeights N b q (-t)) v| ≤
      (2*(N.factorial : ℝ)^6*(coordinateBudget N b)^6)*t^3 := by
  have hM : 0 ≤ coordinateBudget N b :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (coordinateBudget_one_le N b)
  have hm6 : m ≤ 6 := by rcases hm with rfl | rfl <;> omega
  have hP : 1 ≤ (N.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ N.factorial from Nat.factorial_pos N)
  calc
    _ ≤ (N.factorial : ℝ)^m*(2*(coordinateBudget N b)^6*t^3) :=
      raw_error_of_resonant_products N _ _ m _ (by positivity)
        (fun r hz => invisible_resonant_error N b q hq hv t ht ht1 m hm r hz) v
    _ ≤ (N.factorial : ℝ)^6*(2*(coordinateBudget N b)^6*t^3) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP hm6) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
