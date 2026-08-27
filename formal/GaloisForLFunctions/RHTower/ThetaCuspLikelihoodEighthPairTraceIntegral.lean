import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthBellPairAlgebraicTrace

open MeasureTheory Set
open scoped BigOperators

/-!
# Exact product-measure trace behind the eighth Bell pair sector

The raw algebraic pair trace is the integral of the eighth ordinary score over two independent
copies of the intrinsic tilted higher-tail measure.  This identifies every Bell grade-two
allocation with an honest ordered two-particle convolution trace before atom-ray expansion.
-/

namespace RHTower

noncomputable section

private theorem integrable_add_pow_thetaCuspHigherLikelihoodTiltedMeasure_prod
    {B : ℝ} (hB : 0 < B) (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => (z.1 + z.2) ^ n)
      ((thetaCuspHigherLikelihoodTiltedMeasure B).prod
        (thetaCuspHigherLikelihoodTiltedMeasure B)) := by
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  letI : IsFiniteMeasure μ := by
    have hzero := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 0 hB
    simp only [pow_zero] at hzero
    exact (integrable_const_iff.mp hzero).resolve_left one_ne_zero
  rw [show (fun z : ℝ × ℝ => (z.1 + z.2) ^ n) =
      fun z => ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * z.1 ^ i * z.2 ^ (n - i) by
    funext z
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hni : n - i ≤ n := Nat.sub_le n i
  have hp :=
    (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure i hB).mul_prod
      (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure (n - i) hB)
  simpa only [μ, mul_assoc] using hp.const_mul (n.choose i : ℝ)

private theorem integral_add_pow_thetaCuspHigherLikelihoodTiltedMeasure_prod
    {B : ℝ} (hB : 0 < B) (n : ℕ) :
    (∫ z : ℝ × ℝ, (z.1 + z.2) ^ n
        ∂(thetaCuspHigherLikelihoodTiltedMeasure B).prod
          (thetaCuspHigherLikelihoodTiltedMeasure B)) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        thetaCuspHigherLikelihoodSpectralMoment B i *
        thetaCuspHigherLikelihoodSpectralMoment B (n - i) := by
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  letI : IsFiniteMeasure μ := by
    have hzero := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 0 hB
    simp only [pow_zero] at hzero
    exact (integrable_const_iff.mp hzero).resolve_left one_ne_zero
  rw [show (fun z : ℝ × ℝ => (z.1 + z.2) ^ n) =
      fun z => ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (z.1 ^ i * z.2 ^ (n - i)) by
    funext z
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  have hint : ∀ i ∈ Finset.range (n + 1),
      Integrable (fun z : ℝ × ℝ =>
        (n.choose i : ℝ) * (z.1 ^ i * z.2 ^ (n - i))) (μ.prod μ) := by
    intro i hi
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hni : n - i ≤ n := Nat.sub_le n i
    exact ((integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure i hB).mul_prod
      (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure (n - i) hB)).const_mul _
  rw [MeasureTheory.integral_finsetSum _ hint]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => t ^ i) (fun t : ℝ => t ^ (n - i))]
  unfold thetaCuspHigherLikelihoodSpectralMoment
  dsimp only [μ]
  ring

/-- Algebraic ordered-pair trace is exactly the eighth score on the product tilted measure. -/
theorem thetaCuspLikelihoodEighthAlgebraicPairTrace_eq_integral
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthAlgebraicPairTrace x =
      ∫ z : ℝ × ℝ,
        thetaCuspLikelihoodEighthSourceScore
          (thetaCuspSingleAtomReflectionScale 1 x * (z.1 + z.2))
        ∂(thetaCuspHigherLikelihoodTiltedMeasure
            (thetaCuspLikelihoodCoordinate x)).prod
          (thetaCuspHigherLikelihoodTiltedMeasure
            (thetaCuspLikelihoodCoordinate x)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  let M := thetaCuspHigherLikelihoodSpectralMoment B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hpow (n : ℕ) :
      Integrable (fun z : ℝ × ℝ => (z.1 + z.2) ^ n) (μ.prod μ) := by
    simpa only [μ] using
      integrable_add_pow_thetaCuspHigherLikelihoodTiltedMeasure_prod hB n
  have heval (n : ℕ) :
      (∫ z : ℝ × ℝ, (z.1 + z.2) ^ n ∂μ.prod μ) =
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M i * M (n - i) := by
    simpa only [μ, M] using
      integral_add_pow_thetaCuspHigherLikelihoodTiltedMeasure_prod hB n
  have hscore :
      (∫ z : ℝ × ℝ,
          thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) ∂μ.prod μ) =
        A ^ 8 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 8 ∂μ.prod μ) -
        28 * A ^ 7 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 7 ∂μ.prod μ) +
        266 * A ^ 6 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 6 ∂μ.prod μ) -
        1050 * A ^ 5 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 5 ∂μ.prod μ) +
        1701 * A ^ 4 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 4 ∂μ.prod μ) -
        966 * A ^ 3 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 3 ∂μ.prod μ) +
        127 * A ^ 2 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 2 ∂μ.prod μ) -
        A * (∫ z : ℝ × ℝ, (z.1 + z.2) ∂μ.prod μ) := by
    unfold thetaCuspLikelihoodEighthSourceScore
    rw [show (fun z : ℝ × ℝ =>
        (A * (z.1 + z.2)) ^ 8 - 28 * (A * (z.1 + z.2)) ^ 7 +
          266 * (A * (z.1 + z.2)) ^ 6 - 1050 * (A * (z.1 + z.2)) ^ 5 +
          1701 * (A * (z.1 + z.2)) ^ 4 - 966 * (A * (z.1 + z.2)) ^ 3 +
          127 * (A * (z.1 + z.2)) ^ 2 - A * (z.1 + z.2)) =
        fun z =>
          A ^ 8 * (z.1 + z.2) ^ 8 - 28 * A ^ 7 * (z.1 + z.2) ^ 7 +
          266 * A ^ 6 * (z.1 + z.2) ^ 6 - 1050 * A ^ 5 * (z.1 + z.2) ^ 5 +
          1701 * A ^ 4 * (z.1 + z.2) ^ 4 - 966 * A ^ 3 * (z.1 + z.2) ^ 3 +
          127 * A ^ 2 * (z.1 + z.2) ^ 2 - A * (z.1 + z.2) by
      funext z
      ring]
    let f8 : ℝ × ℝ → ℝ := fun z => A ^ 8 * (z.1 + z.2) ^ 8
    let f7 : ℝ × ℝ → ℝ := fun z => 28 * A ^ 7 * (z.1 + z.2) ^ 7
    let f6 : ℝ × ℝ → ℝ := fun z => 266 * A ^ 6 * (z.1 + z.2) ^ 6
    let f5 : ℝ × ℝ → ℝ := fun z => 1050 * A ^ 5 * (z.1 + z.2) ^ 5
    let f4 : ℝ × ℝ → ℝ := fun z => 1701 * A ^ 4 * (z.1 + z.2) ^ 4
    let f3 : ℝ × ℝ → ℝ := fun z => 966 * A ^ 3 * (z.1 + z.2) ^ 3
    let f2 : ℝ × ℝ → ℝ := fun z => 127 * A ^ 2 * (z.1 + z.2) ^ 2
    let f1 : ℝ × ℝ → ℝ := fun z => A * (z.1 + z.2)
    have h8 : Integrable f8 (μ.prod μ) := (hpow 8).const_mul _
    have h7 : Integrable f7 (μ.prod μ) := (hpow 7).const_mul _
    have h6 : Integrable f6 (μ.prod μ) := (hpow 6).const_mul _
    have h5 : Integrable f5 (μ.prod μ) := (hpow 5).const_mul _
    have h4 : Integrable f4 (μ.prod μ) := (hpow 4).const_mul _
    have h3 : Integrable f3 (μ.prod μ) := (hpow 3).const_mul _
    have h2 : Integrable f2 (μ.prod μ) := (hpow 2).const_mul _
    have h1 : Integrable f1 (μ.prod μ) := by
      simpa only [f1, pow_one] using (hpow 1).const_mul A
    rw [show (fun z : ℝ × ℝ =>
        A ^ 8 * (z.1 + z.2) ^ 8 - 28 * A ^ 7 * (z.1 + z.2) ^ 7 +
          266 * A ^ 6 * (z.1 + z.2) ^ 6 - 1050 * A ^ 5 * (z.1 + z.2) ^ 5 +
          1701 * A ^ 4 * (z.1 + z.2) ^ 4 - 966 * A ^ 3 * (z.1 + z.2) ^ 3 +
          127 * A ^ 2 * (z.1 + z.2) ^ 2 - A * (z.1 + z.2)) =
        ((((((f8 - f7) + f6) - f5) + f4) - f3) + f2) - f1 by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply, f8, f7, f6, f5, f4, f3, f2, f1]]
    rw [integral_sub' (((((h8.sub h7).add h6).sub h5).add h4).sub h3 |>.add h2) h1,
      integral_add' ((((h8.sub h7).add h6).sub h5).add h4 |>.sub h3) h2,
      integral_sub' (((h8.sub h7).add h6).sub h5 |>.add h4) h3,
      integral_add' (((h8.sub h7).add h6).sub h5) h4,
      integral_sub' ((h8.sub h7).add h6) h5,
      integral_add' (h8.sub h7) h6,
      integral_sub' h8 h7]
    simp only [f8, f7, f6, f5, f4, f3, f2, f1, integral_const_mul]
  rw [hscore, heval 8, heval 7, heval 6, heval 5, heval 4, heval 3, heval 2]
  have heval1 := heval 1
  simp only [pow_one] at heval1
  rw [heval1]
  norm_num [Finset.sum_range_succ, Nat.choose]
  unfold thetaCuspLikelihoodEighthAlgebraicPairTrace
    thetaCuspLikelihoodEighthRawJetOne thetaCuspLikelihoodEighthRawJetTwo
    thetaCuspLikelihoodEighthRawJetThree thetaCuspLikelihoodEighthRawJetFour
    thetaCuspLikelihoodEighthRawJetFive thetaCuspLikelihoodEighthRawJetSix
    thetaCuspLikelihoodEighthRawJetSeven thetaCuspLikelihoodEighthRawJetEight
  dsimp only [A, B, M, μ]
  rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  ring

end

end RHTower
