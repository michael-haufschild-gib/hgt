import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodHighSourceJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthFockSector

open MeasureTheory Set
open scoped BigOperators

/-!
# Strict sixth source likelihood orientation

Finite Faà di Bruno grading separates sixth logarithmic source jet into particle grades.
Sharp binary score fusion absorbs grade two; calibrated tail activity absorbs grades four and
six. Odd grades are positive. Result is unconditional and uses only theta source measure,
support arithmetic, and finite product integration.
-/

namespace RHTower
noncomputable section

private theorem integrable_add_pow_prod
    {μ : Measure ℝ} [IsFiniteMeasure μ] (n : ℕ)
    (hm : ∀ i, i ≤ n → Integrable (fun t : ℝ => t ^ i) μ) :
    Integrable (fun z : ℝ × ℝ => (z.1 + z.2) ^ n) (μ.prod μ) := by
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
  have hp := (hm i hi').mul_prod (hm (n - i) hni)
  simpa only [mul_assoc] using hp.const_mul (n.choose i : ℝ)

private theorem integral_add_pow_prod
    {μ : Measure ℝ} [IsFiniteMeasure μ] (n : ℕ)
    (hm : ∀ i, i ≤ n → Integrable (fun t : ℝ => t ^ i) μ) :
    (∫ z : ℝ × ℝ, (z.1 + z.2) ^ n ∂μ.prod μ) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (∫ t : ℝ, t ^ i ∂μ) * (∫ t : ℝ, t ^ (n - i) ∂μ) := by
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
    exact ((hm i hi').mul_prod (hm (n - i) hni)).const_mul _
  rw [MeasureTheory.integral_finsetSum _ hint]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]
  rw [MeasureTheory.integral_prod_mul (μ := μ) (ν := μ)
    (fun t : ℝ => t ^ i) (fun t : ℝ => t ^ (n - i))]
  ring

private theorem ae_three_le_fst_prod
    {μ : Measure ℝ} [SFinite μ] (hμ : ∀ᵐ x ∂μ, 3 ≤ x) :
    ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, 3 ≤ z.1 := by
  have hsupp : μ (Iio 3) = 0 := by
    change μ {a : ℝ | a < 3} = 0
    simpa only [not_le] using ae_iff.mp hμ
  have hnull : (μ.prod μ) ((Iio (3 : ℝ)) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, hsupp, zero_mul]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro z hz
  exact Set.mem_prod.mpr ⟨not_le.mp hz, Set.mem_univ _⟩

private theorem ae_three_le_snd_prod
    {μ : Measure ℝ} [SFinite μ] (hμ : ∀ᵐ x ∂μ, 3 ≤ x) :
    ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, 3 ≤ z.2 := by
  have hsupp : μ (Iio 3) = 0 := by
    change μ {a : ℝ | a < 3} = 0
    simpa only [not_le] using ae_iff.mp hμ
  have hnull : (μ.prod μ) ((univ : Set ℝ) ×ˢ (Iio (3 : ℝ))) = 0 := by
    rw [Measure.prod_prod, hsupp, mul_zero]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro z hz
  exact Set.mem_prod.mpr ⟨Set.mem_univ _, not_le.mp hz⟩

set_option maxHeartbeats 1600000 in
private theorem source_pair_grade_two_raw_bound
    {x : ℝ} (hx : 0 ≤ x) :
    let A := thetaCuspSingleAtomReflectionScale 1 x
    let B := thetaCuspLikelihoodCoordinate x
    let M := thetaCuspHigherLikelihoodSpectralMoment B
    let r := M 0
    let a1 := 2 * A * M 1
    let a2 := 4 * (A ^ (2 : ℕ) * M 2 - A * M 1)
    let a3 := 8 * (A ^ (3 : ℕ) * M 3 - 3 * A ^ (2 : ℕ) * M 2 + A * M 1)
    let a4 := 16 * (A ^ (4 : ℕ) * M 4 - 6 * A ^ (3 : ℕ) * M 3 +
      7 * A ^ (2 : ℕ) * M 2 - A * M 1)
    let a5 := 32 * (A ^ (5 : ℕ) * M 5 - 10 * A ^ (4 : ℕ) * M 4 +
      25 * A ^ (3 : ℕ) * M 3 - 15 * A ^ (2 : ℕ) * M 2 + A * M 1)
    let a6 := 64 * (A ^ (6 : ℕ) * M 6 - 15 * A ^ (5 : ℕ) * M 5 +
      65 * A ^ (4 : ℕ) * M 4 - 90 * A ^ (3 : ℕ) * M 3 +
      31 * A ^ (2 : ℕ) * M 2 - A * M 1)
    6 * a1 * a5 + 15 * a2 * a4 + 10 * a3 ^ (2 : ℕ) ≤ 383 * r * a6 := by
  dsimp only
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  let M := thetaCuspHigherLikelihoodSpectralMoment B
  let score : ℝ → ℝ := fun t => thetaLikelihoodSixthScore (A * t)
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : (47 / 15 : ℝ) < A := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    have hmul : Real.pi ≤ Real.pi * Real.exp (2 * x) :=
      le_mul_of_one_le_right Real.pi_pos.le he
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    nlinarith [Real.pi_gt_d2]
  letI : IsFiniteMeasure μ := by
    have hzero := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 0 hB
    simp only [pow_zero] at hzero
    exact (integrable_const_iff.mp hzero).resolve_left one_ne_zero
  have hm : ∀ i, i ≤ 6 → Integrable (fun t : ℝ => t ^ i) μ := by
    intro i hi
    simpa only [μ] using integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure i hB
  have hpow (n : ℕ) (hn : n ≤ 6) :
      Integrable (fun z : ℝ × ℝ => (z.1 + z.2) ^ n) (μ.prod μ) :=
    integrable_add_pow_prod n (fun i hi => hm i (hi.trans hn))
  have hpair : Integrable
      (fun z : ℝ × ℝ => thetaLikelihoodSixthScore (A * (z.1 + z.2)))
      (μ.prod μ) := by
    unfold thetaLikelihoodSixthScore
    have h1 := (hpow 6 (by norm_num)).const_mul (A ^ (6 : ℕ))
    have h2 := (hpow 5 (by norm_num)).const_mul (15 * A ^ (5 : ℕ))
    have h3 := (hpow 4 (by norm_num)).const_mul (65 * A ^ (4 : ℕ))
    have h4 := (hpow 3 (by norm_num)).const_mul (90 * A ^ (3 : ℕ))
    have h5 := (hpow 2 (by norm_num)).const_mul (31 * A ^ (2 : ℕ))
    have h6 := (hpow 1 (by norm_num)).const_mul A
    convert ((((h1.sub h2).add h3).sub h4).add h5).sub h6 using 1
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hs : Integrable score μ := by
    unfold score thetaLikelihoodSixthScore
    have h1 := (hm 6 (by norm_num)).const_mul (A ^ (6 : ℕ))
    have h2 := (hm 5 (by norm_num)).const_mul (15 * A ^ (5 : ℕ))
    have h3 := (hm 4 (by norm_num)).const_mul (65 * A ^ (4 : ℕ))
    have h4 := (hm 3 (by norm_num)).const_mul (90 * A ^ (3 : ℕ))
    have h5 := (hm 2 (by norm_num)).const_mul (31 * A ^ (2 : ℕ))
    have h6 := (hm 1 (by norm_num)).const_mul A
    convert ((((h1.sub h2).add h3).sub h4).add h5).sub h6 using 1
    funext t
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hright : Integrable
      (fun z : ℝ × ℝ => 384 * (score z.1 + score z.2)) (μ.prod μ) := by
    have hfst := hs.mul_prod hone
    have hsnd := hone.mul_prod hs
    convert (hfst.add hsnd).const_mul 384 using 1
    funext z
    simp only [Pi.add_apply, mul_one, one_mul]
  have hmono :
      (∫ z : ℝ × ℝ, thetaLikelihoodSixthScore (A * (z.1 + z.2)) ∂μ.prod μ) ≤
        ∫ z : ℝ × ℝ, 384 * (score z.1 + score z.2) ∂μ.prod μ := by
    apply integral_mono_ae hpair hright
    filter_upwards [ae_three_le_fst_prod
        (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B),
      ae_three_le_snd_prod
        (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B)] with z hz hw
    have hz' : (47 / 5 : ℝ) < A * z.1 := by
      have := mul_lt_mul_of_pos_right hA (by linarith : 0 < z.1)
      nlinarith
    have hw' : (47 / 5 : ℝ) < A * z.2 := by
      have := mul_lt_mul_of_pos_right hA (by linarith : 0 < z.2)
      nlinarith
    simpa only [score, mul_add] using thetaLikelihoodSixthScore_add_le_384_mul hz' hw'
  have heval (n : ℕ) (hn : n ≤ 6) :
      (∫ z : ℝ × ℝ, (z.1 + z.2) ^ n ∂μ.prod μ) =
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M i * M (n - i) := by
    rw [integral_add_pow_prod n (fun i hi => hm i (hi.trans hn))]
    rfl
  have hleft :
      (∫ z : ℝ × ℝ, thetaLikelihoodSixthScore (A * (z.1 + z.2)) ∂μ.prod μ) =
        A ^ (6 : ℕ) * (2 * M 0 * M 6 + 12 * M 1 * M 5 +
          30 * M 2 * M 4 + 20 * M 3 ^ (2 : ℕ)) -
        15 * A ^ (5 : ℕ) * (2 * M 0 * M 5 + 10 * M 1 * M 4 +
          20 * M 2 * M 3) +
        65 * A ^ (4 : ℕ) * (2 * M 0 * M 4 + 8 * M 1 * M 3 +
          6 * M 2 ^ (2 : ℕ)) -
        90 * A ^ (3 : ℕ) * (2 * M 0 * M 3 + 6 * M 1 * M 2) +
        31 * A ^ (2 : ℕ) * (2 * M 0 * M 2 + 2 * M 1 ^ (2 : ℕ)) -
        A * (2 * M 0 * M 1) := by
    unfold thetaLikelihoodSixthScore
    rw [show (fun z : ℝ × ℝ =>
          (A * (z.1 + z.2)) ^ (6 : ℕ) - 15 * (A * (z.1 + z.2)) ^ (5 : ℕ) +
            65 * (A * (z.1 + z.2)) ^ (4 : ℕ) - 90 * (A * (z.1 + z.2)) ^ (3 : ℕ) +
            31 * (A * (z.1 + z.2)) ^ (2 : ℕ) - A * (z.1 + z.2)) =
        fun z => A ^ (6 : ℕ) * (z.1 + z.2) ^ (6 : ℕ) -
          15 * A ^ (5 : ℕ) * (z.1 + z.2) ^ (5 : ℕ) +
          65 * A ^ (4 : ℕ) * (z.1 + z.2) ^ (4 : ℕ) -
          90 * A ^ (3 : ℕ) * (z.1 + z.2) ^ (3 : ℕ) +
          31 * A ^ (2 : ℕ) * (z.1 + z.2) ^ (2 : ℕ) -
          A * (z.1 + z.2) by funext z; ring]
    let f6 : ℝ × ℝ → ℝ := fun z => A ^ (6 : ℕ) * (z.1 + z.2) ^ (6 : ℕ)
    let f5 : ℝ × ℝ → ℝ := fun z => 15 * A ^ (5 : ℕ) * (z.1 + z.2) ^ (5 : ℕ)
    let f4 : ℝ × ℝ → ℝ := fun z => 65 * A ^ (4 : ℕ) * (z.1 + z.2) ^ (4 : ℕ)
    let f3 : ℝ × ℝ → ℝ := fun z => 90 * A ^ (3 : ℕ) * (z.1 + z.2) ^ (3 : ℕ)
    let f2 : ℝ × ℝ → ℝ := fun z => 31 * A ^ (2 : ℕ) * (z.1 + z.2) ^ (2 : ℕ)
    let f1 : ℝ × ℝ → ℝ := fun z => A * (z.1 + z.2)
    have h6 : Integrable f6 (μ.prod μ) := (hpow 6 (by norm_num)).const_mul _
    have h5 : Integrable f5 (μ.prod μ) := (hpow 5 (by norm_num)).const_mul _
    have h4 : Integrable f4 (μ.prod μ) := (hpow 4 (by norm_num)).const_mul _
    have h3 : Integrable f3 (μ.prod μ) := (hpow 3 (by norm_num)).const_mul _
    have h2 : Integrable f2 (μ.prod μ) := (hpow 2 (by norm_num)).const_mul _
    have h1 : Integrable f1 (μ.prod μ) := by
      simpa only [f1, pow_one] using (hpow 1 (by norm_num)).const_mul A
    rw [show (fun z : ℝ × ℝ =>
        A ^ (6 : ℕ) * (z.1 + z.2) ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * (z.1 + z.2) ^ (5 : ℕ) +
          65 * A ^ (4 : ℕ) * (z.1 + z.2) ^ (4 : ℕ) - 90 * A ^ (3 : ℕ) * (z.1 + z.2) ^ (3 : ℕ) +
          31 * A ^ (2 : ℕ) * (z.1 + z.2) ^ (2 : ℕ) - A * (z.1 + z.2)) =
        ((((f6 - f5) + f4) - f3) + f2) - f1 by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply, f6, f5, f4, f3, f2, f1]]
    rw [integral_sub' (((h6.sub h5).add h4).sub h3 |>.add h2) h1,
      integral_add' ((h6.sub h5).add h4 |>.sub h3) h2,
      integral_sub' ((h6.sub h5).add h4) h3,
      integral_add' (h6.sub h5) h4,
      integral_sub' h6 h5]
    simp only [f6, f5, f4, f3, f2, f1, integral_const_mul]
    have heval1 :
        (∫ z : ℝ × ℝ, z.1 + z.2 ∂μ.prod μ) = 2 * M 0 * M 1 := by
      have h := heval 1 (by norm_num)
      simp only [pow_one] at h
      norm_num [Finset.sum_range_succ] at h
      rw [h]
      ring
    rw [heval 6 (by norm_num), heval 5 (by norm_num), heval 4 (by norm_num),
      heval 3 (by norm_num), heval 2 (by norm_num), heval1]
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring
  have hrightEval :
      (∫ z : ℝ × ℝ, 384 * (score z.1 + score z.2) ∂μ.prod μ) =
        768 * M 0 * (A ^ (6 : ℕ) * M 6 - 15 * A ^ (5 : ℕ) * M 5 +
          65 * A ^ (4 : ℕ) * M 4 - 90 * A ^ (3 : ℕ) * M 3 +
          31 * A ^ (2 : ℕ) * M 2 - A * M 1) := by
    rw [integral_const_mul]
    rw [show (fun z : ℝ × ℝ => score z.1 + score z.2) =
        fun z => score z.1 * 1 + 1 * score z.2 by funext z; ring]
    rw [integral_add (hs.mul_prod hone) (hone.mul_prod hs)]
    rw [MeasureTheory.integral_prod_mul (μ := μ) (ν := μ)
      score (fun _ : ℝ => (1 : ℝ)),
      MeasureTheory.integral_prod_mul (μ := μ) (ν := μ)
      (fun _ : ℝ => (1 : ℝ)) score]
    have hmass : (∫ _ : ℝ, (1 : ℝ) ∂μ) = M 0 := by
      change (∫ t : ℝ, t ^ (0 : ℕ) ∂μ) = M 0
      rfl
    have hscoreEval : (∫ t : ℝ, score t ∂μ) =
        A ^ (6 : ℕ) * M 6 - 15 * A ^ (5 : ℕ) * M 5 + 65 * A ^ (4 : ℕ) * M 4 -
          90 * A ^ (3 : ℕ) * M 3 + 31 * A ^ (2 : ℕ) * M 2 - A * M 1 := by
      unfold score thetaLikelihoodSixthScore
      rw [show (fun t : ℝ =>
          (A * t) ^ (6 : ℕ) - 15 * (A * t) ^ (5 : ℕ) + 65 * (A * t) ^ (4 : ℕ) -
            90 * (A * t) ^ (3 : ℕ) + 31 * (A * t) ^ (2 : ℕ) - A * t) =
        fun t => A ^ (6 : ℕ) * t ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ) +
          65 * A ^ (4 : ℕ) * t ^ (4 : ℕ) - 90 * A ^ (3 : ℕ) * t ^ (3 : ℕ) +
          31 * A ^ (2 : ℕ) * t ^ (2 : ℕ) - A * t by funext t; ring]
      let f6 : ℝ → ℝ := fun t => A ^ (6 : ℕ) * t ^ (6 : ℕ)
      let f5 : ℝ → ℝ := fun t => 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ)
      let f4 : ℝ → ℝ := fun t => 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ)
      let f3 : ℝ → ℝ := fun t => 90 * A ^ (3 : ℕ) * t ^ (3 : ℕ)
      let f2 : ℝ → ℝ := fun t => 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ)
      let f1 : ℝ → ℝ := fun t => A * t
      have h6 : Integrable f6 μ := (hm 6 (by norm_num)).const_mul _
      have h5 : Integrable f5 μ := (hm 5 (by norm_num)).const_mul _
      have h4 : Integrable f4 μ := (hm 4 (by norm_num)).const_mul _
      have h3 : Integrable f3 μ := (hm 3 (by norm_num)).const_mul _
      have h2 : Integrable f2 μ := (hm 2 (by norm_num)).const_mul _
      have h1 : Integrable f1 μ := by
        simpa only [f1, pow_one] using (hm 1 (by norm_num)).const_mul A
      rw [show (fun t : ℝ =>
          A ^ (6 : ℕ) * t ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ) + 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ) -
            90 * A ^ (3 : ℕ) * t ^ (3 : ℕ) + 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ) - A * t) =
          ((((f6 - f5) + f4) - f3) + f2) - f1 by
        funext t
        simp only [Pi.add_apply, Pi.sub_apply, f6, f5, f4, f3, f2, f1]]
      rw [integral_sub' (((h6.sub h5).add h4).sub h3 |>.add h2) h1,
        integral_add' ((h6.sub h5).add h4 |>.sub h3) h2,
        integral_sub' ((h6.sub h5).add h4) h3,
        integral_add' (h6.sub h5) h4,
        integral_sub' h6 h5]
      simp only [f6, f5, f4, f3, f2, f1, integral_const_mul]
      rw [integral_const_mul]
      dsimp only [μ, M, thetaCuspHigherLikelihoodSpectralMoment]
      simp only [pow_one]
    rw [hmass, hscoreEval]
    ring
  rw [hleft, hrightEval] at hmono
  dsimp only [A, B, M] at hmono ⊢
  nlinarith

set_option maxHeartbeats 2400000 in
/-- Quantitative sixth logarithmic source orientation.  After every negative Faa di Bruno
particle grade is paid, more than `2/25` of the normalized leading sixth spectral moment
survives. -/
theorem two_twentyFifths_mul_likelihoodSixthMoment_lt_sourceLogPartitionJetSix
    {x : ℝ} (hx : 0 ≤ x) :
    (2 / 25 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 6 <
      thetaCuspLikelihoodSourceLogPartitionJetSix x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let e6 := thetaCuspLikelihoodNormalizedMoment B 6
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ (2 : ℕ) * e2 - A * e1)
  let b3 := 8 * (A ^ (3 : ℕ) * e3 - 3 * A ^ (2 : ℕ) * e2 + A * e1)
  let b4 := 16 * (A ^ (4 : ℕ) * e4 - 6 * A ^ (3 : ℕ) * e3 +
    7 * A ^ (2 : ℕ) * e2 - A * e1)
  let b5 := 32 * (A ^ (5 : ℕ) * e5 - 10 * A ^ (4 : ℕ) * e4 +
    25 * A ^ (3 : ℕ) * e3 - 15 * A ^ (2 : ℕ) * e2 + A * e1)
  let b6 := 64 * (A ^ (6 : ℕ) * e6 - 15 * A ^ (5 : ℕ) * e5 +
    65 * A ^ (4 : ℕ) * e4 - 90 * A ^ (3 : ℕ) * e3 +
    31 * A ^ (2 : ℕ) * e2 - A * e1)
  let q2 := 6 * b1 * b5 + 15 * b2 * b4 + 10 * b3 ^ (2 : ℕ)
  let q3 := 15 * b1 ^ (2 : ℕ) * b4 + 60 * b1 * b2 * b3 + 15 * b2 ^ (3 : ℕ)
  let q4 := 20 * b1 ^ (3 : ℕ) * b3 + 45 * b1 ^ (2 : ℕ) * b2 ^ (2 : ℕ)
  let q5 := 15 * b1 ^ (4 : ℕ) * b2
  let q6 := b1 ^ (6 : ℕ)
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have he1 : 0 < e1 := by simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    have h := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
    simpa only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean, e1, e2] using h
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he56 : 3 * e5 ≤ e6 := by
    simpa only [e5, e6] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have he5 : 0 < e5 := lt_of_lt_of_le (mul_pos (by norm_num) he4) he45
  have he6 : 0 < e6 := lt_of_lt_of_le (mul_pos (by norm_num) he5) he56
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have h22 : e2 ^ (2 : ℕ) ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hp : 0 < p := by nlinarith [sq_pos_of_pos he2]
  have hp0 : 0 ≤ p := hp.le
  have h11 : e1 ^ (2 : ℕ) ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h13 : e1 * e3 ≤ p * e4 := by
    simpa only [B, p, e1, e3, e4,
      thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 3 = 4 by norm_num] using
        thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 3
  have h24 : e2 * e4 ≤ p * e6 := by
    simpa only [B, p, e2, e4, e6, show 2 + 4 = 6 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 4
  have he113 : e1 ^ (3 : ℕ) * e3 ≤ p ^ (3 : ℕ) * e6 := by
    calc
      e1 ^ (3 : ℕ) * e3 = e1 ^ (2 : ℕ) * (e1 * e3) := by ring
      _ ≤ (p * e2) * (p * e4) :=
        mul_le_mul h11 h13 (by positivity) (by positivity)
      _ = p ^ (2 : ℕ) * (e2 * e4) := by ring
      _ ≤ p ^ (2 : ℕ) * (p * e6) := mul_le_mul_of_nonneg_left h24 (sq_nonneg p)
      _ = p ^ (3 : ℕ) * e6 := by ring
  have he122 : e1 ^ (2 : ℕ) * e2 ^ (2 : ℕ) ≤ p ^ (3 : ℕ) * e6 := by
    calc
      e1 ^ (2 : ℕ) * e2 ^ (2 : ℕ) ≤ (p * e2) * (p * e4) :=
        mul_le_mul h11 h22 (by positivity) (by positivity)
      _ = p ^ (2 : ℕ) * (e2 * e4) := by ring
      _ ≤ p ^ (2 : ℕ) * (p * e6) := mul_le_mul_of_nonneg_left h24 (sq_nonneg p)
      _ = p ^ (3 : ℕ) * e6 := by ring
  have he23cube : e2 ^ (3 : ℕ) ≤ p ^ (2 : ℕ) * e6 := by
    calc
      e2 ^ (3 : ℕ) = e2 * e2 ^ (2 : ℕ) := by ring
      _ ≤ e2 * (p * e4) := mul_le_mul_of_nonneg_left h22 he2.le
      _ = p * (e2 * e4) := by ring
      _ ≤ p * (p * e6) := mul_le_mul_of_nonneg_left h24 hp0
      _ = p ^ (2 : ℕ) * e6 := by ring
  have he16 : e1 ^ (6 : ℕ) ≤ p ^ (5 : ℕ) * e6 := by
    calc
      e1 ^ (6 : ℕ) = (e1 ^ (2 : ℕ)) ^ (3 : ℕ) := by ring
      _ ≤ (p * e2) ^ (3 : ℕ) := pow_le_pow_left₀ (sq_nonneg e1) h11 3
      _ = p ^ (3 : ℕ) * e2 ^ (3 : ℕ) := by ring
      _ ≤ p ^ (3 : ℕ) * (p ^ (2 : ℕ) * e6) :=
        mul_le_mul_of_nonneg_left he23cube (pow_nonneg hp0 3)
      _ = p ^ (5 : ℕ) * e6 := by ring
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right hA he2
    nlinarith
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hAe4 : 6 * e3 < A * e4 := by
    have hmul := mul_lt_mul_of_pos_right hA he4
    nlinarith
  have hb1 : 0 < b1 := by dsimp only [b1]; positivity
  have hb1nonneg : 0 ≤ b1 := hb1.le
  have hb1Upper : b1 ≤ 2 * A * e1 := by rfl
  have hb2 : 0 < b2 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hb2nonneg : 0 ≤ b2 := hb2.le
  have hb2Upper : b2 ≤ 4 * A ^ (2 : ℕ) * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have hb3nonneg : 0 ≤ b3 := hb3.le
  have hb3Upper : b3 ≤ 8 * A ^ (3 : ℕ) * e3 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b3]
    nlinarith
  have hb4 : 0 < b4 := by
    have hmul := mul_lt_mul_of_pos_left hAe4 (pow_pos hA0 3)
    have htail : A * e1 < 7 * A ^ (2 : ℕ) * e2 := by
      have h := mul_lt_mul_of_pos_left hAe2 hA0
      nlinarith
    dsimp only [b4]
    nlinarith
  have hb4nonneg : 0 ≤ b4 := hb4.le
  have hb5Lower : (32 / 6 : ℝ) * A ^ (5 : ℕ) * e5 ≤ b5 := by
    have h := one_sixth_mul_likelihoodSourceLinearFive_le hx
    dsimp only [A, B, e1, e2, e3, e4, e5, b5] at h ⊢
    nlinarith
  have hb5 : 0 < b5 := by
    have hlead : 0 < (32 / 6 : ℝ) * A ^ (5 : ℕ) * e5 := by positivity
    exact lt_of_lt_of_le hlead hb5Lower
  have hb5nonneg : 0 ≤ b5 := hb5.le
  have hb6Lower : (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6 ≤ b6 := by
    have h := one_thirtieth_mul_likelihoodSourceLinearSix_le hx
    dsimp only [A, B, e1, e2, e3, e4, e5, e6, b6] at h ⊢
    nlinarith
  have hb6 : 0 < b6 := by
    have hlead : 0 < (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6 := by positivity
    exact lt_of_lt_of_le hlead hb6Lower
  have hpair : q2 ≤ 383 * p * b6 := by
    have hraw := source_pair_grade_two_raw_bound hx
    let P := thetaCuspLikelihoodPartition B
    let M := thetaCuspHigherLikelihoodSpectralMoment B
    let a1 := 2 * A * M 1
    let a2 := 4 * (A ^ (2 : ℕ) * M 2 - A * M 1)
    let a3 := 8 * (A ^ (3 : ℕ) * M 3 - 3 * A ^ (2 : ℕ) * M 2 + A * M 1)
    let a4 := 16 * (A ^ (4 : ℕ) * M 4 - 6 * A ^ (3 : ℕ) * M 3 +
      7 * A ^ (2 : ℕ) * M 2 - A * M 1)
    let a5 := 32 * (A ^ (5 : ℕ) * M 5 - 10 * A ^ (4 : ℕ) * M 4 +
      25 * A ^ (3 : ℕ) * M 3 - 15 * A ^ (2 : ℕ) * M 2 + A * M 1)
    let a6 := 64 * (A ^ (6 : ℕ) * M 6 - 15 * A ^ (5 : ℕ) * M 5 +
      65 * A ^ (4 : ℕ) * M 4 - 90 * A ^ (3 : ℕ) * M 3 +
      31 * A ^ (2 : ℕ) * M 2 - A * M 1)
    have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
    have hraw' : 6 * a1 * a5 + 15 * a2 * a4 + 10 * a3 ^ (2 : ℕ) ≤
        383 * M 0 * a6 := by
      simpa only [A, B, M, a1, a2, a3, a4, a5, a6] using hraw
    have hq2Eq : q2 =
        (6 * a1 * a5 + 15 * a2 * a4 + 10 * a3 ^ (2 : ℕ)) / P ^ (2 : ℕ) := by
      dsimp only [q2, b1, b2, b3, b4, b5, e1, e2, e3, e4, e5,
        thetaCuspLikelihoodMean, thetaCuspLikelihoodNormalizedMoment,
        A, B, M, a1, a2, a3, a4, a5, P]
      field_simp [ne_of_gt hP]
    have hrhsEq : 383 * p * b6 = (383 * M 0 * a6) / P ^ (2 : ℕ) := by
      dsimp only [p, b6, e1, e2, e3, e4, e5, e6,
        thetaCuspLikelihoodTailProbability, thetaCuspLikelihoodMean,
        thetaCuspLikelihoodNormalizedMoment, A, B, M, a6, P]
      field_simp [ne_of_gt hP]
    rw [hq2Eq, hrhsEq]
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hP)).2 hraw'
  have hq3 : 0 ≤ q3 := by
    dsimp only [q3]
    positivity
  have hq5 : 0 ≤ q5 := by
    dsimp only [q5]
    positivity
  have hb1CubeB3 : b1 ^ (3 : ℕ) * b3 ≤ 64 * A ^ (6 : ℕ) * (e1 ^ (3 : ℕ) * e3) := by
    calc
      b1 ^ (3 : ℕ) * b3 ≤ (2 * A * e1) ^ (3 : ℕ) * (8 * A ^ (3 : ℕ) * e3) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 ^ (3 : ℕ) * e3) := by ring
  have hb1SqB2Sq : b1 ^ (2 : ℕ) * b2 ^ (2 : ℕ) ≤ 64 * A ^ (6 : ℕ) * (e1 ^ (2 : ℕ) * e2 ^ (2 : ℕ)) := by
    calc
      b1 ^ (2 : ℕ) * b2 ^ (2 : ℕ) ≤ (2 * A * e1) ^ (2 : ℕ) * (4 * A ^ (2 : ℕ) * e2) ^ (2 : ℕ) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 ^ (2 : ℕ) * e2 ^ (2 : ℕ)) := by ring
  have hq4 : q4 ≤ 1950 * p ^ (3 : ℕ) * b6 := by
    have hterm1 : 20 * b1 ^ (3 : ℕ) * b3 ≤ 1280 * A ^ (6 : ℕ) * p ^ (3 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1CubeB3 (by norm_num : (0 : ℝ) ≤ 20)
      have h2 := mul_le_mul_of_nonneg_left he113
        (show 0 ≤ 64 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hterm2 : 45 * b1 ^ (2 : ℕ) * b2 ^ (2 : ℕ) ≤ 2880 * A ^ (6 : ℕ) * p ^ (3 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1SqB2Sq (by norm_num : (0 : ℝ) ≤ 45)
      have h2 := mul_le_mul_of_nonneg_left he122
        (show 0 ≤ 64 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hlead := mul_le_mul_of_nonneg_left hb6Lower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1950) (pow_nonneg hp0 3))
    dsimp only [q4]
    nlinarith
  have hb1Six : b1 ^ (6 : ℕ) ≤ 64 * A ^ (6 : ℕ) * e1 ^ (6 : ℕ) := by
    calc
      b1 ^ (6 : ℕ) ≤ (2 * A * e1) ^ (6 : ℕ) := pow_le_pow_left₀ hb1nonneg hb1Upper 6
      _ = 64 * A ^ (6 : ℕ) * e1 ^ (6 : ℕ) := by ring
  have hq6 : q6 ≤ 30 * p ^ (5 : ℕ) * b6 := by
    have h1 := mul_le_mul_of_nonneg_left he16
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) (pow_nonneg hA0.le 6))
    have hlead := mul_le_mul_of_nonneg_left hb6Lower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30) (pow_nonneg hp0 5))
    dsimp only [q6]
    nlinarith
  have hpLt : p < (1 / 400 : ℝ) := by nlinarith
  have hp3 : p ^ (3 : ℕ) < (1 / 400 : ℝ) ^ (3 : ℕ) :=
    pow_lt_pow_left₀ hpLt hp0 (by norm_num)
  have hp5 : p ^ (5 : ℕ) < (1 / 400 : ℝ) ^ (5 : ℕ) :=
    pow_lt_pow_left₀ hpLt hp0 (by norm_num)
  have hbudget : 383 * p + 11700 * p ^ (3 : ℕ) + 3600 * p ^ (5 : ℕ) < 24 / 25 := by
    norm_num at hp3 hp5 ⊢
    nlinarith
  have hloss : q2 + 6 * q4 + 120 * q6 < (24 / 25 : ℝ) * b6 := by
    have hscaled := mul_lt_mul_of_pos_right hbudget hb6
    nlinarith
  have hdecomp :
      thetaCuspLikelihoodSourceLogPartitionJetSix x =
        b6 - q2 + 2 * q3 - 6 * q4 + 24 * q5 - 120 * q6 := by
    dsimp only [b1, b2, b3, b4, b5, b6, q2, q3, q4, q5, q6,
      A, B, e1, e2, e3, e4, e5, e6]
    unfold thetaCuspLikelihoodSourceLogPartitionJetSix
      thetaCuspLikelihoodSixthCumulant thetaCuspLikelihoodFifthCumulant
      thetaCuspLikelihoodFourthCumulant thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment
    ring
  rw [hdecomp]
  nlinarith

/-- Sixth logarithmic source jet is strictly positive on the nonnegative source half-line. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSourceLogPartitionJetSix x := by
  have h :=
    two_twentyFifths_mul_likelihoodSixthMoment_lt_sourceLogPartitionJetSix hx
  have hA : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx
  have h2 : 0 < thetaCuspLikelihoodNormalizedMoment
      (thetaCuspLikelihoodCoordinate x) 2 :=
    thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have h23 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have h34 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have h45 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have h56 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
  have hmoment : 0 < thetaCuspLikelihoodNormalizedMoment
      (thetaCuspLikelihoodCoordinate x) 6 := by
    nlinarith
  have hlead : 0 < (2 / 25 : ℝ) *
      thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 6 := by
    positivity
  linarith

end
end RHTower
