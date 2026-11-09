import GaloisForLFunctions.RHTower.Heat.LocalizedHeatPacketFlux

/-!
# Crowding increases vertical dissipation

In a conjugation-closed packet inside a radius `R`, each nonreal zero pays its
own reflected interaction. The remaining interactions dissipate at least
`(card S - 2) / R²` times the squared-height energy. Real members of the packet
also increase this rate.
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

private theorem sum_im_eq_zero (S : Finset ℂ)
    (hc : ∀ a ∈ S, starRingEnd ℂ a ∈ S) : (∑ a ∈ S, a.im) = 0 := by
  classical
  have hi : S.image (starRingEnd ℂ) = S := by
    ext a
    constructor
    · rintro h
      obtain ⟨b, hb, rfl⟩ := mem_image.mp h
      exact hc b hb
    · intro ha
      exact mem_image.mpr ⟨starRingEnd ℂ a, hc a ha, by simp⟩
  have hs := sum_image (s := S) (f := fun z : ℂ => z.im)
    (g := starRingEnd ℂ) (fun a _ b _ h => (starRingEnd ℂ).injective h)
  rw [hi] at hs
  simp only [Complex.conj_im, sum_neg_distrib] at hs
  linarith only [hs]

private theorem sum_squared_vertical_gaps (S : Finset ℂ)
    (hc : ∀ a ∈ S, starRingEnd ℂ a ∈ S) :
    (∑ a ∈ S, ∑ b ∈ S, (a.im - b.im)^2) =
      2 * (S.card : ℝ) * heatPacketVerticalEnergy S := by
  have hz := sum_im_eq_zero S hc
  have hi (a : ℂ) : (∑ b ∈ S, (a.im - b.im)^2) =
      (S.card : ℝ) * a.im^2 + heatPacketVerticalEnergy S := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
      ← mul_sum, hz, mul_zero, sub_zero, heatPacketVerticalEnergy]
  simp only [hi, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
    heatPacketVerticalEnergy]
  ring

private theorem pair_force_le_crowding {R : ℝ} (hR : 0 < R)
    {a b : ℂ} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    localizedHeatPairForce (fun _ => 1) (fun _ => 0) a.re b.re a.im b.im ≤
      -(if a.im ≠ 0 ∧ b = starRingEnd ℂ a then 4 else 0) -
        ((a.im - b.im)^2 -
          (if a.im ≠ 0 ∧ b = starRingEnd ℂ a then 4 * a.im^2 else 0)) / R^2 := by
  classical
  by_cases hc : a.im ≠ 0 ∧ b = starRingEnd ℂ a
  · obtain ⟨hai, rfl⟩ := hc
    simp only [hai, ne_eq, not_false_eq_true, and_self, if_true,
      Complex.conj_re, Complex.conj_im, sub_neg_eq_add]
    rw [localizedHeatPairForce_conjugate (fun _ => 1) (fun _ => 0) a.re hai]
    have he : (a.im + a.im)^2 - 4 * a.im^2 = 0 := by ring
    rw [he, zero_div, sub_zero]
    norm_num
  simp only [if_neg hc, neg_zero, sub_zero, zero_sub]
  by_cases hab : a = b
  · subst b
    simp only [localizedHeatPairForce, sub_self, mul_zero, zero_div,
      zero_pow two_ne_zero, neg_zero, le_refl]
  have hd : 0 < (a.re - b.re)^2 + (a.im - b.im)^2 := by
    simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]
      using Complex.normSq_pos.mpr (sub_ne_zero.mpr hab)
  have hdist : (a.re - b.re)^2 + (a.im - b.im)^2 ≤ 4 * R^2 := by
    have hn : ‖a - b‖ ≤ 2 * R := (norm_sub_le a b).trans (by linarith only [ha, hb])
    have hs := (sq_le_sq₀ (norm_nonneg (a - b)) (by positivity : 0 ≤ 2 * R)).mpr hn
    rw [← Complex.normSq_eq_norm_sq] at hs
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hs
    nlinarith only [hs]
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (a.im - b.im)) hd hdist
  have hf : localizedHeatPairForce (fun _ => 1) (fun _ => 0) a.re b.re a.im b.im =
      -4 * ((a.im - b.im)^2 / ((a.re - b.re)^2 + (a.im - b.im)^2)) := by
    unfold localizedHeatPairForce
    ring
  have he : (a.im - b.im)^2 / R^2 = 4 * ((a.im - b.im)^2 / (4 * R^2)) := by
    field_simp
  rw [hf, he]
  linarith only [hdiv]

/-- The full packet size, including real zeros, strengthens conjugate-pair
dissipation. The energy vanishes when the packet has no nonreal members. -/
theorem heatPacketPairDrift_le_crowding {S : Finset ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ∀ a ∈ S, starRingEnd ℂ a ∈ S) (hn : ∀ a ∈ S, ‖a‖ ≤ R) :
    heatPacketPairDrift S (fun _ => 1) (fun _ => 0) ≤
      -2 * heatPacketNonrealWeight S (fun _ => 1) -
        ((S.card : ℝ) - 2) / R^2 * heatPacketVerticalEnergy S := by
  classical
  have hsum := sum_le_sum fun a ha => sum_le_sum fun b hb =>
    pair_force_le_crowding hR (hn a ha) (hn b hb)
  have hcount : (∑ a ∈ S, ∑ b ∈ S,
      if a.im ≠ 0 ∧ b = starRingEnd ℂ a then (4 : ℝ) else 0) =
      4 * heatPacketNonrealWeight S (fun _ => 1) := by
    rw [heatPacketNonrealWeight, mul_sum]
    apply sum_congr rfl
    intro a ha
    by_cases hi : a.im = 0
    · simp only [hi, ne_eq, not_true_eq_false, false_and, if_false, if_true,
        sum_const_zero, mul_zero]
    · simp [hi, hc a ha]
  have hself : (∑ a ∈ S, ∑ b ∈ S,
      if a.im ≠ 0 ∧ b = starRingEnd ℂ a then 4 * a.im^2 else 0) =
      4 * heatPacketVerticalEnergy S := by
    rw [heatPacketVerticalEnergy, mul_sum]
    apply sum_congr rfl
    intro a ha
    by_cases hi : a.im = 0
    · simp only [hi, ne_eq, not_true_eq_false, false_and, if_false,
        sum_const_zero, zero_pow two_ne_zero, mul_zero]
    · simp [hi, hc a ha]
  simp only [sum_sub_distrib, sum_neg_distrib, ← sum_div] at hsum
  rw [hcount, hself, sum_squared_vertical_gaps S hc] at hsum
  unfold heatPacketPairDrift
  have he : (2 * (S.card : ℝ) * heatPacketVerticalEnergy S -
      4 * heatPacketVerticalEnergy S) / R^2 =
      2 * (((S.card : ℝ) - 2) / R^2 * heatPacketVerticalEnergy S) := by ring
  rw [he] at hsum
  linarith only [hsum]

#print axioms heatPacketPairDrift_le_crowding

end

end GaloisForLFunctions.ArithmeticElectrostatics
