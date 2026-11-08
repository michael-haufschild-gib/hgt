import GaloisForLFunctions.ArithmeticElectrostatics.TheElapsedDepthActionHasItsZeroVelocityDerivative

/-!
# Elapsed-depth comparison for the heat divisor

Freeze the nonreal count at the final time. Adding its elapsed baseline to
the corrected action gives a continuous function with nonpositive forward
derivative. Comparison therefore passes through every collision without
integrating the discontinuous count.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- The full elapsed-depth moment, including the baseline of every surviving
nonreal multiplicity copy. -/
def heatElapsedDepthMoment (q t : ℝ) : ℝ :=
  heatElapsedDepthAction q t + (2 * t) ^ q * (nonrealZeroCount t : ℝ)

/-- The moment is exactly the finite sum of elapsed powers over the nonreal divisor. -/
theorem heatElapsedDepthMoment_eq_sum (q : ℝ) {t : ℝ} (ht : 0 < t) :
    heatElapsedDepthMoment q t =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) * (z.im ^ 2 + 2 * t) ^ q := by
  classical
  have hsum : heatElapsedDepthAction q t =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) *
          ((z.im ^ 2 + 2 * t) ^ q - (2 * t) ^ q) := by
    unfold heatElapsedDepthAction heatWeightedZeroSum elapsedDepthActionWeight
    apply tsum_eq_sum
    intro z hz
    by_cases hf : riemannHeat t z = 0
    · have hi : z.im = 0 := by
        by_contra hi
        exact hz ((Set.Finite.mem_toFinset _).mpr ⟨hf, hi⟩)
      simp only [hi, zero_pow two_ne_zero, zero_add, sub_self, mul_zero]
    · rw [zeroMult_riemannHeat_eq_zero ht.le hf, Nat.cast_zero, zero_mul]
  rw [heatElapsedDepthMoment, hsum, nonrealZeroCount_eq ht, Nat.cast_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Freezing the final count gives a continuous comparison across all collisions. -/
theorem heatElapsedDepthAction_add_final_count_le {q a b : ℝ}
    (hq : 0 ≤ q) (ha : 0 < a) (hab : a ≤ b) :
    heatElapsedDepthAction q b + (2 * b) ^ q * (nonrealZeroCount b : ℝ) ≤
      heatElapsedDepthAction q a + (2 * a) ^ q * (nonrealZeroCount b : ℝ) := by
  have hp : Continuous (fun s : ℝ => (2 * s) ^ q) :=
    (continuous_const.mul continuous_id).rpow_const (fun _ => Or.inr hq)
  have hc : ContinuousOn
      (fun s => heatElapsedDepthAction q s + (2 * s) ^ q * (nonrealZeroCount b : ℝ))
      (Icc a b) :=
    ((continuousOn_heatElapsedDepthAction q).mono (fun s hs => ha.trans_le hs.1)).add
      (hp.mul continuous_const).continuousOn
  apply le_initial_of_forward_intervals_interior hab hc
  intro t ht
  obtain ⟨δ, hδ, hreg⟩ := heatElapsedDepthAction_forward_derivative t (ha.trans ht.1)
  refine ⟨δ, hδ, fun s hs hsb => ?_⟩
  have hs0 : 0 < s := (ha.trans ht.1).trans hs.1
  obtain ⟨D, hD, hbound⟩ := hreg s hs q hq
  have hpow : HasDerivAt (fun s : ℝ => (2 * s) ^ q)
      (2 * q * (2 * s) ^ (q - 1)) s := by
    have h := ((hasDerivAt_id s).const_mul 2).rpow_const
      (Or.inl (show 2 * s ≠ 0 by positivity)) (p := q)
    simpa only [id_eq, mul_one] using h
  have hcount : (nonrealZeroCount b : ℝ) ≤ (nonrealZeroCount s : ℝ) := by
    exact_mod_cast nonrealZeroCount_antitoneOn hs0 (ha.trans_le hab) hsb.le
  have hcoef : 0 ≤ 2 * q * (2 * s) ^ (q - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hq) (Real.rpow_nonneg (by positivity) _)
  have hpay := mul_le_mul_of_nonneg_left hcount hcoef
  refine ⟨D + (2 * q * (2 * s) ^ (q - 1)) * (nonrealZeroCount b : ℝ),
    hD.add (hpow.mul_const (nonrealZeroCount b : ℝ)).hasDerivWithinAt, ?_⟩
  nlinarith only [hbound, hpay]

/-- Every nonnegative elapsed-depth moment decreases on positive heat time. -/
theorem antitoneOn_heatElapsedDepthMoment {q : ℝ} (hq : 0 ≤ q) :
    AntitoneOn (heatElapsedDepthMoment q) (Ioi 0) := by
  intro a ha b hb hab
  have h := heatElapsedDepthAction_add_final_count_le hq ha hab
  have hcount : (nonrealZeroCount b : ℝ) ≤ (nonrealZeroCount a : ℝ) := by
    exact_mod_cast nonrealZeroCount_antitoneOn ha hb hab
  have hcredit := mul_le_mul_of_nonneg_left hcount
    (Real.rpow_nonneg (show 0 ≤ 2 * a by positivity) q)
  exact h.trans (add_le_add le_rfl hcredit)

/-- Removing the real-axis baseline leaves a nonnegative action. -/
theorem heatElapsedDepthAction_nonneg {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    0 ≤ heatElapsedDepthAction q t := by
  unfold heatElapsedDepthAction heatWeightedZeroSum elapsedDepthActionWeight
  apply tsum_nonneg
  intro z
  apply mul_nonneg (Nat.cast_nonneg _)
  apply sub_nonneg.mpr
  exact Real.rpow_le_rpow (by positivity) (le_add_of_nonneg_left (sq_nonneg _)) hq

/-- Every surviving multiplicity copy costs at least the elapsed baseline. -/
theorem nonrealCount_elapsed_power_le_moment {q a b : ℝ}
    (hq : 0 ≤ q) (ha : 0 < a) (hab : a ≤ b) :
    (2 * b) ^ q * (nonrealZeroCount b : ℝ) ≤ heatElapsedDepthMoment q a := by
  have hb : 0 < b := ha.trans_le hab
  have hbase : (2 * b) ^ q * (nonrealZeroCount b : ℝ) ≤ heatElapsedDepthMoment q b :=
    le_add_of_nonneg_left (heatElapsedDepthAction_nonneg hq hb.le)
  exact hbase.trans (antitoneOn_heatElapsedDepthMoment hq ha hb hab)

#print axioms heatElapsedDepthMoment_eq_sum
#print axioms heatElapsedDepthAction_add_final_count_le
#print axioms antitoneOn_heatElapsedDepthMoment
#print axioms nonrealCount_elapsed_power_le_moment

end

end GaloisForLFunctions.ArithmeticElectrostatics
