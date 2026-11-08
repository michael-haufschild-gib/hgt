import GaloisForLFunctions.ArithmeticElectrostatics.ConjugatePairsDissipateLogarithmicDepth
import Mathlib.Analysis.Complex.Basic

/-!
# Elapsed-depth work of a complex zero packet

Splitting a conjugation-closed nonreal packet into its upper roots and their
reflections identifies the complex reciprocal field with the paired real
kernel. The self-reflection contributes exactly the elapsed heat credit.
-/

open Complex

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- Coordinates of the reciprocal field, with totalized division at coincidence. -/
theorem im_reciprocal_difference (z w : ℂ) :
    ((z - w)⁻¹).im = -(z.im - w.im) /
      ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [Complex.inv_im]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]

/-- A conjugate pair contributes the negative paired imaginary field. -/
theorem im_reciprocal_conjugate_pair (z w : ℂ) :
    ((z - w)⁻¹ + (z - starRingEnd ℂ w)⁻¹).im =
      -upperPairField z.im w.im (z.re - w.re) := by
  rw [Complex.add_im, im_reciprocal_difference, im_reciprocal_difference]
  simp only [Complex.conj_re, Complex.conj_im, sub_neg_eq_add, upperPairField]
  ring

/-- A nonreal conjugation-closed packet is exactly its upper half and its reflection. -/
theorem sum_conjugate_packet (S : Finset ℂ)
    (hnonreal : ∀ z ∈ S, z.im ≠ 0)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S) (F : ℂ → ℂ) :
    (∑ z ∈ S, F z) =
      ∑ z ∈ S.filter (fun z => 0 < z.im), (F z + F (starRingEnd ℂ z)) := by
  classical
  let U := S.filter (fun z => 0 < z.im)
  have hsplit : S = U ∪ U.image (starRingEnd ℂ) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_image, U, Finset.mem_filter]
    constructor
    · intro hz
      by_cases hpos : 0 < z.im
      · exact Or.inl ⟨hz, hpos⟩
      · have hneg : z.im < 0 := by
          rcases lt_or_eq_of_le (le_of_not_gt hpos) with h | h
          · exact h
          · exact False.elim (hnonreal z hz h)
        exact Or.inr ⟨starRingEnd ℂ z, ⟨hconj z hz, by
          simpa only [Complex.conj_im] using neg_pos.mpr hneg⟩, by simp⟩
    · rintro (⟨hz, _⟩ | ⟨w, ⟨hw, _⟩, rfl⟩)
      · exact hz
      · exact hconj w hw
  have hdisj : Disjoint U (U.image (starRingEnd ℂ)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz'
    have hzpos := (Finset.mem_filter.mp hz).2
    have hwpos := (Finset.mem_filter.mp hw).2
    simp only [Complex.conj_im] at hzpos
    linarith only [hzpos, hwpos]
  change (∑ z ∈ S, F z) = ∑ z ∈ U, (F z + F (starRingEnd ℂ z))
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image
    (fun a _ b _ h => (starRingEnd ℂ).injective h), Finset.sum_add_distrib]

/-- The imaginary velocity from a conjugation-closed packet separates the
self-conjugate force from all other conjugate pairs. -/
theorem conjugate_packet_im_velocity (S : Finset ℂ)
    (hnonreal : ∀ z ∈ S, z.im ≠ 0)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S)
    {a : ℂ} (ha : a ∈ S) (hai : 0 < a.im) :
    (2 * ∑ b ∈ S, (a - b)⁻¹).im =
      -a.im⁻¹ - 2 * ∑ b ∈ S.filter (fun z => 0 < z.im),
        if a = b then 0 else upperPairField a.im b.im (a.re - b.re) := by
  classical
  let U := S.filter (fun z => 0 < z.im)
  have haU : a ∈ U := Finset.mem_filter.mpr ⟨ha, hai⟩
  have hsum := sum_conjugate_packet S hnonreal hconj (fun b => (a - b)⁻¹)
  have hself : upperPairField a.im a.im (a.re - a.re) = a.im⁻¹ / 2 := by
    unfold upperPairField
    simp only [sub_self, zero_pow two_ne_zero, zero_add, zero_div]
    field_simp [hai.ne']
    ring
  have hsplit : (∑ b ∈ U, upperPairField a.im b.im (a.re - b.re)) =
      upperPairField a.im a.im (a.re - a.re) +
        ∑ b ∈ U, if a = b then 0 else upperPairField a.im b.im (a.re - b.re) := by
    have heq (b : ℂ) : upperPairField a.im b.im (a.re - b.re) =
        (if a = b then upperPairField a.im a.im (a.re - a.re) else 0) +
        (if a = b then 0 else upperPairField a.im b.im (a.re - b.re)) := by
      split_ifs with h
      · subst b
        rw [add_zero]
      · rw [zero_add]
    rw [Finset.sum_congr rfl (fun b _ => heq b), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, haU, if_true]
  rw [hsum]
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    add_zero, Complex.im_sum, im_reciprocal_conjugate_pair, Finset.sum_neg_distrib]
  change 2 * -(∑ b ∈ U, upperPairField a.im b.im (a.re - b.re)) = _
  rw [hsplit, hself]
  ring

/-- Every finite conjugate packet pays the sharp elapsed-depth credit. -/
theorem elapsedDepth_complex_packet_drift_nonpos (S : Finset ℂ)
    (hnonreal : ∀ z ∈ S, z.im ≠ 0)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    (∑ a ∈ S.filter (fun z => 0 < z.im),
      (2 * q * (a.im ^ 2 + c) ^ (q - 1) +
        elapsedDepthWeight q c a.im * (2 * ∑ b ∈ S, (a - b)⁻¹).im)) ≤ 0 := by
  classical
  apply elapsedDepth_packet_drift_nonpos_of_velocity_le _ Complex.re Complex.im
    (fun a => (2 * ∑ b ∈ S, (a - b)⁻¹).im) hq hc
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a _ b _ hab
    have hn := Complex.normSq_pos.mpr (sub_ne_zero.mpr hab)
    simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two] using hn
  · intro a ha
    exact (conjugate_packet_im_velocity S hnonreal hconj
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).le

#print axioms elapsedDepth_complex_packet_drift_nonpos

/-- Real zeros add a nonpositive imaginary field above the real axis. -/
theorem real_packet_im_velocity_nonpos (R : Finset ℂ)
    (hreal : ∀ b ∈ R, b.im = 0) {a : ℂ} (ha : 0 ≤ a.im) :
    (2 * ∑ b ∈ R, (a - b)⁻¹).im ≤ 0 := by
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    add_zero, Complex.im_sum]
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply Finset.sum_nonpos
  intro b hb
  rw [Complex.inv_im, Complex.sub_im, hreal b hb, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Complex.normSq_nonneg _)

/-- Adding any finite real packet preserves the elapsed-depth inequality. -/
theorem elapsedDepth_complex_packet_with_real_drift_nonpos (S R : Finset ℂ)
    (hnonreal : ∀ z ∈ S, z.im ≠ 0)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S)
    (hreal : ∀ z ∈ R, z.im = 0)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    (∑ a ∈ S.filter (fun z => 0 < z.im),
      (2 * q * (a.im ^ 2 + c) ^ (q - 1) + elapsedDepthWeight q c a.im *
        (2 * ∑ b ∈ S, (a - b)⁻¹ + 2 * ∑ b ∈ R, (a - b)⁻¹).im)) ≤ 0 := by
  apply le_trans _ (elapsedDepth_complex_packet_drift_nonpos S hnonreal hconj hq hc)
  apply Finset.sum_le_sum
  intro a ha
  have hai := (Finset.mem_filter.mp ha).2
  have hw : 0 ≤ elapsedDepthWeight q c a.im := by
    unfold elapsedDepthWeight
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hq) hai.le)
      (Real.rpow_nonneg (add_nonneg (sq_nonneg _) hc) _)
  have hrealwork := mul_nonpos_of_nonneg_of_nonpos hw
    (real_packet_im_velocity_nonpos R hreal hai.le)
  rw [Complex.add_im, mul_add]
  linarith only [hrealwork]

#print axioms elapsedDepth_complex_packet_with_real_drift_nonpos

/-- A finite conjugation-closed configuration, including its real roots,
pays the same elapsed-depth credit. -/
theorem elapsedDepth_conjugation_closed_drift_nonpos (S : Finset ℂ)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    (∑ a ∈ S.filter (fun z => 0 < z.im),
      (2 * q * (a.im ^ 2 + c) ^ (q - 1) + elapsedDepthWeight q c a.im *
        (2 * ∑ b ∈ S, (a - b)⁻¹).im)) ≤ 0 := by
  classical
  let N := S.filter (fun z => z.im ≠ 0)
  let R := S.filter (fun z => z.im = 0)
  have hN (z : ℂ) (hz : z ∈ N) : z.im ≠ 0 := (Finset.mem_filter.mp hz).2
  have hNc (z : ℂ) (hz : z ∈ N) : starRingEnd ℂ z ∈ N := by
    refine Finset.mem_filter.mpr ⟨hconj z (Finset.mem_filter.mp hz).1, ?_⟩
    simpa only [Complex.conj_im, neg_ne_zero] using hN z hz
  have hR (z : ℂ) (hz : z ∈ R) : z.im = 0 := (Finset.mem_filter.mp hz).2
  have hU : N.filter (fun z => 0 < z.im) = S.filter (fun z => 0 < z.im) := by
    ext z
    simp only [N, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.ne'⟩, h.2⟩⟩
  have hsum (a : ℂ) :
      2 * ∑ b ∈ N, (a - b)⁻¹ + 2 * ∑ b ∈ R, (a - b)⁻¹ =
        2 * ∑ b ∈ S, (a - b)⁻¹ := by
    rw [← mul_add]
    congr 1
    simp only [N, R, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b.im = 0 <;> simp only [hb, ne_eq, not_true_eq_false,
      not_false_eq_true, if_true, if_false, zero_add, add_zero]
  have h := elapsedDepth_complex_packet_with_real_drift_nonpos N R hN hNc hR hq hc
  simpa only [hU, hsum] using h

/-- Any additional downward field preserves the sharp elapsed-depth credit. -/
theorem elapsedDepth_drift_nonpos_of_upper_velocity_le (S : Finset ℂ)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S) (v : ℂ → ℝ)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hv : ∀ a ∈ S, 0 < a.im → v a ≤ (2 * ∑ b ∈ S, (a - b)⁻¹).im) :
    (∑ a ∈ S.filter (fun z => 0 < z.im),
      (2 * q * (a.im ^ 2 + c) ^ (q - 1) + elapsedDepthWeight q c a.im * v a)) ≤ 0 := by
  apply le_trans _ (elapsedDepth_conjugation_closed_drift_nonpos S hconj hq hc)
  apply Finset.sum_le_sum
  intro a ha
  have hai := (Finset.mem_filter.mp ha).2
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left (hv a (Finset.mem_filter.mp ha).1 hai)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hq) hai.le)
    (Real.rpow_nonneg (add_nonneg (sq_nonneg _) hc) _)

#print axioms elapsedDepth_conjugation_closed_drift_nonpos
#print axioms elapsedDepth_drift_nonpos_of_upper_velocity_le

end

end GaloisForLFunctions.ArithmeticElectrostatics
