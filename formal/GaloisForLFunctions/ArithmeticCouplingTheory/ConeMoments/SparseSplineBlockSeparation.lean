import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineTailEstimates

/-!
# Separation of exact spline height blocks

For geometric node counts, the eighth-root heights matched to masses
`exp(-4^k)` eventually double at every step. This leaves gaps between finite
correction blocks once their spans are smaller than their starting heights.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma correctionMass_succ (k : ℕ) : correctionMass (k+1)=(correctionMass k)^4 := by
  simp only [correctionMass,pow_succ,pow_zero,one_mul]
  rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

lemma eventually_small_correction_mass_cube {n : ℕ → ℕ} {U R : ℝ}
    (hU : 0 < U) (hR : 0 < R) (hnU : ∀ k, (n k:ℝ) ≤ U*R^k) :
    ∀ᶠ k : ℕ in atTop, 256*(n k:ℝ)*(correctionMass k)^3 ≤ 1 := by
  have hlim := ((summable_correctionMass_mul_pow hR).mul_left (256*U)).tendsto_atTop_zero
  have hsmall := hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hsmall] with k hk
  have hA := correctionMass_pos k
  have hA1 : correctionMass k ≤ 1 := (correctionMass_le_geometric k).trans
    (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1))
  have hA2 : (correctionMass k)^2 ≤ 1 :=
    pow_le_one₀ hA.le hA1
  have hA3 : (correctionMass k)^3 ≤ correctionMass k := by
    have hh := mul_le_mul_of_nonneg_right hA2 hA.le
    nlinarith only [hh]
  calc
    _ ≤ 256*(U*R^k)*correctionMass k :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hnU k) (by norm_num)) hA3
        (pow_nonneg hA.le 3) (by positivity)
    _ = (256*U)*(correctionMass k*R^k) := by ring
    _ ≤ 1 := hk.le

/-- Supergeometric masses force adjacent matched heights to at least double,
regardless of the next block's positive node count. -/
lemma matched_spline_height_double_le {n : ℕ → ℕ} (hn : ∀ k, 0 < n k) (k : ℕ)
    (hsmall : 256*(n k:ℝ)*(correctionMass k)^3 ≤ 1) :
    2*massRadius (2*correctionMass k) (n k) ≤
      massRadius (2*correctionMass (k+1)) (n (k+1)) := by
  have hA := correctionMass_pos k
  have hH := matched_spline_height_pos hA (hn k)
  have hH' := matched_spline_height_pos (correctionMass_pos (k+1)) (hn (k+1))
  have hn1 : (1:ℝ) ≤ n (k+1) := by exact_mod_cast (Nat.succ_le_iff.mpr (hn (k+1)))
  have hp : (2*massRadius (2*correctionMass k) (n k))^8 ≤
      (massRadius (2*correctionMass (k+1)) (n (k+1)))^8 := by
    rw [mul_pow,matched_spline_height_pow hA (hn k),
      matched_spline_height_pow (correctionMass_pos (k+1)) (hn (k+1)),correctionMass_succ]
    norm_num only [show (2:ℝ)^8=256 by norm_num]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hA (pow_pos hA 4)).mpr
    calc
      (256*(n k:ℝ))*(correctionMass k)^4=
          (256*(n k:ℝ)*(correctionMass k)^3)*correctionMass k := by ring
      _ ≤ 1*correctionMass k := mul_le_mul_of_nonneg_right hsmall hA.le
      _ ≤ (n (k+1):ℝ)*correctionMass k := mul_le_mul_of_nonneg_right hn1 hA.le
  exact (pow_le_pow_iff_left₀ (by positivity) hH'.le (by norm_num : (8:ℕ) ≠ 0)).mp hp

lemma eventually_matched_spline_height_double {n : ℕ → ℕ} (hn : ∀ k, 0 < n k)
    {U R : ℝ} (hU : 0 < U) (hR : 0 < R) (hnU : ∀ k, (n k:ℝ) ≤ U*R^k) :
    ∀ᶠ k : ℕ in atTop, 2*massRadius (2*correctionMass k) (n k) ≤
      massRadius (2*correctionMass (k+1)) (n (k+1)) := by
  filter_upwards [eventually_small_correction_mass_cube hU hR hnU] with k hk
  exact matched_spline_height_double_le hn k hk

#print axioms correctionMass_succ
#print axioms eventually_matched_spline_height_double
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
