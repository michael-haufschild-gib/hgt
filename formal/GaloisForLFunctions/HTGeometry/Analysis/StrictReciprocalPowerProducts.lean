import GaloisForLFunctions.HTGeometry.Analysis.InfiniteReciprocalPowerProducts

/-!
# Strictness of the reciprocal-power envelope

The secant inequality is strict at three for every integral exponent above two.
Keeping this single factor through the remaining telescoping product makes the
infinite envelope strict, completing the strict assertion of Li–Yang, Lemma 2.1.
-/

namespace GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts

open Finset Filter
open scoped Topology

private noncomputable def envelope (k N : ℕ) : ℝ :=
  (slope k + 1) * ((N : ℝ) + 1) / (slope k * ((N : ℝ) + 1) + 1)

private theorem envelope_pos (k N : ℕ) : 0 < envelope k N := by
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  unfold envelope
  positivity

private theorem envelope_lt_uniform (k N : ℕ) :
    envelope k N < (slope k + 1) / slope k := by
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  unfold envelope
  apply (div_lt_div_iff₀ (by positivity) hc).mpr
  nlinarith only [hc]

private theorem envelope_step (k N : ℕ) :
    envelope k N *
      (((slope k * ((N : ℝ) + 1) + 1) * ((N : ℝ) + 2)) /
        ((slope k * ((N : ℝ) + 2) + 1) * ((N : ℝ) + 1))) = envelope k (N + 1) := by
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  unfold envelope
  push_cast
  field_simp
  ring

private theorem product_le_scaled_envelope (k a N : ℕ) :
    product k (a + N) ≤ product k a / envelope k a * envelope k (a + N) := by
  have hr : 0 ≤ product k a / envelope k a :=
    div_nonneg (product_nonneg k a) (envelope_pos k a).le
  induction N with
  | zero => simp only [Nat.add_zero, div_mul_cancel₀ _ (ne_of_gt (envelope_pos k a)), le_refl]
  | succ N ih =>
      change (∏ n ∈ range (a + N + 1), (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹) ≤ _
      rw [prod_range_succ]
      change product k (a + N) * _ ≤ _
      calc
        product k (a + N) * _ ≤
            (product k a / envelope k a * envelope k (a + N)) *
            (((slope k * (((a + N : ℕ) : ℝ) + 1) + 1) * (((a + N : ℕ) : ℝ) + 2)) /
              ((slope k * (((a + N : ℕ) : ℝ) + 2) + 1) * (((a + N : ℕ) : ℝ) + 1))) :=
          mul_le_mul ih (factor_le_ratio k (a + N))
            (inv_pos.mpr (factor_pos k (a + N))).le
            (mul_nonneg hr (envelope_pos k (a + N)).le)
        _ = _ := by rw [mul_assoc, envelope_step]; rfl

private theorem product_one_eq_envelope (k : ℕ) : product k 1 = envelope k 1 := by
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  have he : (2 : ℝ) ^ (k + 2) = 2 * (slope k + 1) := by
    dsimp [slope]
    rw [pow_succ]
    ring
  have hd : 2 * (slope k + 1) - 1 ≠ 0 := by linarith
  norm_num only [product, prod_range_one, Nat.cast_zero, zero_add, envelope, Nat.cast_one]
  rw [he]
  field_simp
  ring

private theorem factor_three_lt_ratio (k : ℕ) :
    (1 - 1 / (3 : ℝ) ^ (k + 1 + 2))⁻¹ <
      ((slope (k + 1) * 2 + 1) * 3) / ((slope (k + 1) * 3 + 1) * 2) := by
  have hc : 0 < slope k := lt_of_lt_of_le zero_lt_one (slope_ge_one k)
  have hc' : 0 < slope (k + 1) := lt_of_lt_of_le zero_lt_one (slope_ge_one (k + 1))
  have hs : slope (k + 1) = 2 * slope k + 1 := by
    simp only [slope, pow_succ]
    ring
  have hm := mul_le_mul_of_nonneg_right (secant_le_power k 1) (by norm_num : (0 : ℝ) ≤ 3)
  norm_num only [Nat.cast_one] at hm
  have hstrict : slope (k + 1) * 2 + 1 < (3 : ℝ) ^ (k + 2) := by
    rw [hs, pow_succ]
    nlinarith only [hm, hc]
  have hp : 0 < (3 : ℝ) ^ (k + 1 + 2) := by positivity
  have hquot : ((slope (k + 1) * 2 + 1) * 3) / (3 : ℝ) ^ (k + 1 + 2) < 1 := by
    apply (div_lt_one hp).mpr
    simpa only [pow_succ, mul_lt_mul_right (by norm_num : (0 : ℝ) < 3)] using
      mul_lt_mul_of_pos_right hstrict (by norm_num : (0 : ℝ) < 3)
  have hpos : 0 < 1 - 1 / (3 : ℝ) ^ (k + 1 + 2) := by
    simpa only [Nat.cast_one] using factor_pos (k + 1) 1
  rw [← one_div, div_lt_div_iff₀ hpos (by positivity), one_mul, mul_sub, mul_one, mul_one_div]
  nlinarith only [hquot]

private theorem product_two_lt_envelope (k : ℕ) : product (k + 1) 2 < envelope (k + 1) 2 := by
  have h := factor_three_lt_ratio k
  have hprod : product (k + 1) 2 = product (k + 1) 1 * (1 - 1 / (3 : ℝ) ^ (k + 1 + 2))⁻¹ := by
    simpa only [Nat.cast_one] using
      (prod_range_succ (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2) ^ (k + 1 + 2))⁻¹) 1)
  rw [hprod, product_one_eq_envelope]
  exact (mul_lt_mul_of_pos_left h (envelope_pos (k + 1) 1)).trans_eq
    (by simpa only [Nat.cast_one] using envelope_step (k + 1) 1)

/-- For every integral exponent above two, the infinite rational envelope is strict. -/
theorem infiniteProduct_lt_uniform (k : ℕ) :
    infiniteProduct (k + 1) < (slope (k + 1) + 1) / slope (k + 1) := by
  let R := product (k + 1) 2 / envelope (k + 1) 2
  let U := (slope (k + 1) + 1) / slope (k + 1)
  have hR : 0 ≤ R := div_nonneg (product_nonneg _ _) (envelope_pos _ _).le
  have hRlt : R < 1 := (div_lt_one (envelope_pos _ _)).mpr (product_two_lt_envelope k)
  have hU : 0 < U := by
    have hc : 0 < slope (k + 1) := lt_of_lt_of_le zero_lt_one (slope_ge_one (k + 1))
    dsimp [U]
    positivity
  have hshift : Tendsto (fun N : ℕ => 2 + N) atTop atTop :=
    tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨b, by omega⟩
  have hbound : infiniteProduct (k + 1) ≤ R * U := by
    apply le_of_tendsto' ((product_tendsto (k + 1)).comp hshift)
    intro N
    exact (product_le_scaled_envelope (k + 1) 2 N).trans
      (mul_le_mul_of_nonneg_left (envelope_lt_uniform (k + 1) (2 + N)).le hR)
  exact hbound.trans_lt (by nlinarith only [mul_lt_mul_of_pos_right hRlt hU])

#print axioms infiniteProduct_lt_uniform

end GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts
