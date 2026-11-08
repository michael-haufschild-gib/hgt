import GaloisForLFunctions.ArithmeticElectrostatics.TheGlobalHeatDepthDissipates
import GaloisForLFunctions.ArithmeticElectrostatics.TheConjugatePacketPaysElapsedHeat

/-!
# Elapsed-depth dissipation for the actual heat packet

The real exterior lowers the imaginary velocity of every upper simple zero.
Combining this pointwise comparison with conjugate-pair dissipation pays the
elapsed heat credit for every nonnegative power, including powers below one.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.HTGeometry
open RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

private theorem simple_zero_copy_eq {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (q r : ZeroCopy f)
    (heq : zeroCopyPoint f q = zeroCopyPoint f r)
    (hd : deriv f (zeroCopyPoint f r) ≠ 0) : q = r := by
  apply Sigma.eq (Subtype.ext heq)
  have ho := (hf (zeroCopyPoint f r) (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (apply_zeroCopyPoint hf r) hd
  have hm : ((MeromorphicOn.divisor f univ) (r.1 : ℂ)).toNat = 1 := by
    rw [divisor_univ_eq_analyticOrder hf, ho]
    rfl
  haveI : Subsingleton (Fin ((MeromorphicOn.divisor f univ) (r.1 : ℂ)).toNat) := by
    rw [hm]
    infer_instance
  exact Subsingleton.elim _ _

/-- At an upper simple zero, the real exterior can only lower the imaginary
velocity relative to the finite enclosing packet. -/
theorem heatGlobalPacket_upper_velocity_le {t : ℝ} (ht : 0 < t) {S : Finset ℂ}
    (hzero : ∀ a ∈ S, riemannHeat t a = 0)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hcover : ∀ a, riemannHeat t a = 0 → a.im ≠ 0 → a ∈ S)
    {a : ℂ} (ha : a ∈ S) (hai : 0 < a.im) :
    (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im ≤
      (2 * ∑ b ∈ S, (a - b)⁻¹).im := by
  classical
  have hf := riemannHeat_analytic ht.le
  have hf0 := RHTower.riemannHeat_zero_ne ht.le
  choose q hq using fun b : S => exists_zeroCopy_of_eq_zero hf hf0 (hzero b b.property)
  have hqi : Function.Injective q := by
    intro b c heq
    apply Subtype.ext
    rw [← hq b, ← hq c, heq]
  let N := S.attach.image q
  have hreal : ∀ r, r ∉ N → (zeroCopyPoint (riemannHeat t) r).im = 0 := by
    intro r hr
    by_contra hi
    have hb := hcover _ (apply_zeroCopyPoint hf r) hi
    let b : S := ⟨zeroCopyPoint (riemannHeat t) r, hb⟩
    have heq : q b = r := simple_zero_copy_eq hf (q b) r (hq b) (hsimple _ hb)
    exact hr (Finset.mem_image.mpr ⟨b, Finset.mem_attach S b, heq⟩)
  let aS : S := ⟨a, ha⟩
  have hqa : q aS ∈ N := Finset.mem_image.mpr ⟨aS, Finset.mem_attach S aS, rfl⟩
  have hsum : (∑ r ∈ N, (a - zeroCopyPoint (riemannHeat t) r)⁻¹) =
      ∑ b ∈ S, (a - b)⁻¹ := by
    rw [Finset.sum_image (fun r _ s _ hrs => hqi hrs)]
    simp only [hq]
    exact Finset.sum_attach S (fun b : ℂ => (a - b)⁻¹)
  have herase : (∑ r ∈ N.erase (q aS), (a - zeroCopyPoint (riemannHeat t) r)⁻¹) =
      ∑ b ∈ S, (a - b)⁻¹ := by
    rw [← hsum]
    simpa only [hq aS, sub_self, inv_zero, add_zero] using
      Finset.sum_erase_add N (fun r => (a - zeroCopyPoint (riemannHeat t) r)⁻¹) hqa
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq ht.le).exists_envelope
  have h := im_mul_simple_regular_exterior_nonpos hC hf hf0 (riemannHeat_neg ht.le)
    hbound N hreal (q aS) hqa (by rw [hq aS]; exact hsimple a ha)
  rw [hq aS, herase, Complex.sub_im] at h
  by_contra hbad
  exact (not_lt_of_ge h) (mul_pos hai (sub_pos.mpr (lt_of_not_ge hbad)))

/-- Every nonnegative elapsed-depth power dissipates along the actual simple
heat-zero packet, including the force of all real exterior zeros. -/
theorem heatGlobalPacket_elapsedDepth_drift_nonpos {t : ℝ} (ht : 0 < t) {S : Finset ℂ}
    (hzero : ∀ a ∈ S, riemannHeat t a = 0)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hcover : ∀ a, riemannHeat t a = 0 → a.im ≠ 0 → a ∈ S)
    (hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S)
    {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    (∑ a ∈ S.filter (fun z => 0 < z.im),
      (2 * q * (a.im ^ 2 + c) ^ (q - 1) + elapsedDepthWeight q c a.im *
        (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im)) ≤ 0 :=
  elapsedDepth_drift_nonpos_of_upper_velocity_le S hconj
    (fun a => (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) hq hc
    (fun _ ha hai => heatGlobalPacket_upper_velocity_le ht hzero hsimple hcover ha hai)

#print axioms heatGlobalPacket_upper_velocity_le
#print axioms heatGlobalPacket_elapsedDepth_drift_nonpos

/-- The elapsed-depth velocity sum of the actual upper heat divisor, with
analytic multiplicity. At simple times it is the moment's derivative. -/
def heatUpperElapsedDepthDrift (q c t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun a => if 0 < a.im then
    2 * q * (a.im ^ 2 + c) ^ (q - 1) + elapsedDepthWeight q c a.im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im else 0) t

private theorem heatUpperElapsedDepthDrift_eq_packet {t : ℝ} (ht : 0 < t)
    {S : Finset ℂ} (hzero : ∀ a ∈ S, riemannHeat t a = 0)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hcover : ∀ a, riemannHeat t a = 0 → a.im ≠ 0 → a ∈ S) (q c : ℝ) :
    heatUpperElapsedDepthDrift q c t =
      ∑ a ∈ S.filter (fun z => 0 < z.im),
        (2 * q * (a.im ^ 2 + c) ^ (q - 1) + elapsedDepthWeight q c a.im *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im) := by
  classical
  unfold heatUpperElapsedDepthDrift heatWeightedZeroSum
  rw [tsum_eq_sum (s := S) (fun a ha => ?_), Finset.sum_filter]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [zeroMult_riemannHeat_eq_one ht.le (hzero a ha) (hsimple a ha),
      Nat.cast_one, one_mul]
  · by_cases hz : riemannHeat t a = 0
    · have hi : ¬ 0 < a.im := fun hi => ha (hcover a hz hi.ne')
      rw [if_neg hi, mul_zero]
    · rw [zeroMult_riemannHeat_eq_zero ht.le hz, Nat.cast_zero, zero_mul]

/-- Immediately after every positive time, the actual heat divisor pays every
elapsed-depth power. The same forward interval works for all powers and offsets. -/
theorem heatUpperElapsedDepthDrift_nonpos_forward (t : ℝ) (ht : 0 < t) :
    ∃ δ > 0, ∀ s ∈ Ioo t (t + δ), ∀ q c : ℝ, 0 ≤ q → 0 ≤ c →
      heatUpperElapsedDepthDrift q c s ≤ 0 := by
  classical
  obtain ⟨R, hR⟩ := exists_heat_nonreal_norm_bound ht
  obtain ⟨δ, hδ, hreg⟩ := exists_compact_simple_riemannHeat_zeros_forward ht
    (Metric.isCompact_closedBall (0 : ℂ) R)
  refine ⟨δ, hδ, fun s hs q c hq hc => ?_⟩
  have hs0 : 0 < s := ht.trans hs.1
  have han : AnalyticOnNhd ℂ (riemannHeat s) (Metric.closedBall 0 R) :=
    fun z _ => (riemannHeat_analytic hs0.le) z (mem_univ z)
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top hs0.le z (analyticOrderAt_eq_top.mpr h))
  let S := hfin.toFinset
  have hpacket (a : ℂ) : a ∈ S ↔ riemannHeat s a = 0 ∧ ‖a‖ ≤ R := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Metric.mem_closedBall,
      dist_zero_right, and_comm]
  have hzero (a : ℂ) (ha : a ∈ S) : riemannHeat s a = 0 := ((hpacket a).mp ha).1
  have hsimple (a : ℂ) (ha : a ∈ S) : deriv (riemannHeat s) a ≠ 0 := by
    obtain ⟨hz, hn⟩ := (hpacket a).mp ha
    exact (hreg s hs.1 hs.2 a
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hn) hz).1
  have hcover (a : ℂ) (hz : riemannHeat s a = 0) (hi : a.im ≠ 0) : a ∈ S :=
    (hpacket a).mpr ⟨hz, (hR s hs.1.le a hz hi).le⟩
  have hconj (a : ℂ) (ha : a ∈ S) : starRingEnd ℂ a ∈ S := by
    obtain ⟨hz, hn⟩ := (hpacket a).mp ha
    apply (hpacket (starRingEnd ℂ a)).mpr
    constructor
    · rw [riemannHeat_conj hs0.le, hz, map_zero]
    · simpa only [Complex.norm_conj] using hn
  rw [heatUpperElapsedDepthDrift_eq_packet hs0 hzero hsimple hcover]
  exact heatGlobalPacket_elapsedDepth_drift_nonpos hs0 hzero hsimple hcover hconj hq hc

#print axioms heatUpperElapsedDepthDrift_nonpos_forward

end

end GaloisForLFunctions.ArithmeticElectrostatics
