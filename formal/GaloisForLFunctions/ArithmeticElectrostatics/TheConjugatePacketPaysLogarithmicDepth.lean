import GaloisForLFunctions.ArithmeticElectrostatics.TheLogarithmicDepthProfilesDissipate
import GaloisForLFunctions.ArithmeticElectrostatics.TheConjugatePacketPaysElapsedHeat

/-!
# Logarithmic elapsed-depth work of a conjugate packet

Any nonnegative increasing logarithmic derivative weight dissipates the
full finite reciprocal field after paying the self-conjugate credit `f(y)/y`.
Real exterior roots add nonpositive work. The logarithmic depth profiles
therefore satisfy the exact moving-clock packet inequality.
-/

open Complex Set

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Pairwise logarithmic admissibility controls a packet with any extra downward field. -/
theorem logarithmicWeight_packet_drift_nonpos {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x y v : ι → ℝ) (f : ℝ → ℝ)
    (hy : ∀ i ∈ S, 0 < y i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      0 < (x i - x j) ^ 2 + (y i - y j) ^ 2)
    (hn : ∀ a, 0 < a → 0 ≤ a * f a)
    (hm : MonotoneOn (fun a => a * f a) (Ioi 0))
    (hv : ∀ i ∈ S, v i ≤ -(y i)⁻¹ - 2 * ∑ j ∈ S,
      if i = j then 0 else upperPairField (y i) (y j) (x i - x j)) :
    (∑ i ∈ S, (f (y i) / y i + f (y i) * v i)) ≤ 0 := by
  have hsum := sum_upperPairField_nonneg S x y f hy hsep hn hm
  have hbound (i : ι) (hi : i ∈ S) :
      f (y i) / y i + f (y i) * v i ≤
        -2 * ∑ j ∈ S, if i = j then 0 else
          f (y i) * upperPairField (y i) (y j) (x i - x j) := by
    have hf : 0 ≤ f (y i) := (mul_nonneg_iff_of_pos_left (hy i hi)).mp (hn _ (hy i hi))
    have hmul : (∑ j ∈ S, if i = j then 0 else
        f (y i) * upperPairField (y i) (y j) (x i - x j)) =
        f (y i) * ∑ j ∈ S, if i = j then 0 else
          upperPairField (y i) (y j) (x i - x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp only [mul_zero]
    calc
      _ ≤ f (y i) / y i + f (y i) *
          (-(y i)⁻¹ - 2 * ∑ j ∈ S,
            if i = j then 0 else upperPairField (y i) (y j) (x i - x j)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hv i hi) hf)
      _ = _ := by rw [hmul, div_eq_mul_inv]; ring
  calc
    _ ≤ ∑ i ∈ S, -2 * ∑ j ∈ S, if i = j then 0 else
        f (y i) * upperPairField (y i) (y j) (x i - x j) :=
      Finset.sum_le_sum hbound
    _ ≤ 0 := by
      rw [← Finset.mul_sum]
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hsum

/-- The full reciprocal field pays the self-conjugate credit for every admissible weight. -/
theorem conjugation_closed_logarithmicWeight_drift_nonpos (S : Finset ℂ)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S) (f : ℝ → ℝ)
    (hn : ∀ a, 0 < a → 0 ≤ a * f a)
    (hm : MonotoneOn (fun a => a * f a) (Ioi 0)) :
    (∑ a ∈ S.filter (fun z => 0 < z.im),
      (f a.im / a.im + f a.im * (2 * ∑ b ∈ S, (a - b)⁻¹).im)) ≤ 0 := by
  classical
  let N := S.filter (fun z => z.im ≠ 0)
  let R := S.filter (fun z => z.im = 0)
  let U := S.filter (fun z => 0 < z.im)
  have hN (z : ℂ) (hz : z ∈ N) : z.im ≠ 0 := (Finset.mem_filter.mp hz).2
  have hNc (z : ℂ) (hz : z ∈ N) : starRingEnd ℂ z ∈ N := by
    refine Finset.mem_filter.mpr ⟨hconj z (Finset.mem_filter.mp hz).1, ?_⟩
    simpa only [Complex.conj_im, neg_ne_zero] using hN z hz
  have hR (z : ℂ) (hz : z ∈ R) : z.im = 0 := (Finset.mem_filter.mp hz).2
  have hU : N.filter (fun z => 0 < z.im) = U := by
    ext z
    simp only [N, U, Finset.mem_filter]
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
  refine logarithmicWeight_packet_drift_nonpos U Complex.re Complex.im
    (fun a => (2 * ∑ b ∈ S, (a - b)⁻¹).im) f
    (fun a ha => (Finset.mem_filter.mp ha).2) ?_ hn hm ?_
  · intro a _ b _ hab
    have h := Complex.normSq_pos.mpr (sub_ne_zero.mpr hab)
    simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two] using h
  · intro a ha
    have hai := (Finset.mem_filter.mp ha).2
    have haN : a ∈ N := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, hai.ne'⟩
    have hp := conjugate_packet_im_velocity N hN hNc haN hai
    rw [hU] at hp
    rw [← hsum, Complex.add_im, ← hp]
    exact add_le_of_nonpos_right (real_packet_im_velocity_nonpos R hR hai.le)

/-- Logarithmic depth profiles dissipate under the complete finite heat velocity. -/
theorem elapsedLogDepth_conjugation_closed_drift_nonpos (S : Finset ℂ)
    (hconj : ∀ z ∈ S, starRingEnd ℂ z ∈ S)
    {r A c : ℝ} (hr : 0 ≤ r) (hA : 0 < A) (hc : 0 ≤ c) :
    (∑ a ∈ S.filter (fun z => 0 < z.im),
      (2 * r * (a.im ^ 2 + c) ^ (r - 1) / (A + (a.im ^ 2 + c) ^ r) +
        elapsedLogDepthWeight r A c a.im * (2 * ∑ b ∈ S, (a - b)⁻¹).im)) ≤ 0 := by
  have h := conjugation_closed_logarithmicWeight_drift_nonpos S hconj
    (elapsedLogDepthWeight r A c) (elapsedLogDepthWeight_admissible hr hA hc).1
      (elapsedLogDepthWeight_admissible hr hA hc).2
  convert h using 1
  apply Finset.sum_congr rfl
  intro a ha
  have hai := (Finset.mem_filter.mp ha).2
  have hcredit : elapsedLogDepthWeight r A c a.im / a.im =
      2 * r * (a.im ^ 2 + c) ^ (r - 1) / (A + (a.im ^ 2 + c) ^ r) := by
    calc
      _ = (2 * r * (a.im ^ 2 + c) ^ (r - 1) / (A + (a.im ^ 2 + c) ^ r)) *
          (a.im / a.im) := by unfold elapsedLogDepthWeight elapsedDepthWeight; ring
      _ = _ := by rw [div_self hai.ne', mul_one]
  rw [hcredit]

#print axioms conjugation_closed_logarithmicWeight_drift_nonpos
#print axioms elapsedLogDepth_conjugation_closed_drift_nonpos

end
end GaloisForLFunctions.ArithmeticElectrostatics
