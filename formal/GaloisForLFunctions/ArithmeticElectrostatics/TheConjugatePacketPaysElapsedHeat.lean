import GaloisForLFunctions.ArithmeticElectrostatics.ConjugatePairsDissipateLogarithmicDepth
import Mathlib.Analysis.Complex.Basic

/-!+# Elapsed-depth work of a complex zero packet

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
    add_zero, map_sum, im_reciprocal_conjugate_pair, Finset.sum_neg_distrib]
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

end

end GaloisForLFunctions.ArithmeticElectrostatics
