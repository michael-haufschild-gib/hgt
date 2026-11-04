import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibreCentering
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibreCompleteEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeSignedReceiver
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedConductorCompleteCancellation

/-!
# The complete signed law for simultaneous receiving coordinates

Common prime exclusion changes each original fibre by a fixed finite
conductor packet. Its complete critical output vanishes. Thus the exact
finite receiving vector is read diagonally by the common complementary
terminal receivers, with coefficient `1/80` in every mode.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory

/-- A finite extra prime exclusion has asymptotically no effect on the coherent normalization. -/
theorem tendsto_fibreScale_div_common {m M : ℕ} (hM : 0 < M) (hmM : m ∣ M) :
    Tendsto (fun Q : ℕ => fibreScale m Q / fibreScale M Q) atTop (𝓝 (1 : ℝ)) := by
  have hB := fibreScale_tendsto_atTop hM
  have h := (hB.const_div_atTop
    (∑ p ∈ additionalFibrePrimes m M, Real.log p / p)).const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop M, hB.eventually_gt_atTop 0] with Q hQ hb
  rw [fibreScale_common_difference hM hmM hQ, add_div, div_self hb.ne']

/-- A fixed finite deletion contributes zero to every bounded terminal receiver. -/
theorem tendsto_additionalFibre_complete_pairing {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 0 < K)
    {m M l R : ℕ} (hm : 0 < m) (hM : 0 < M) (hl : 0 < l) (hR : 0 < R) (t : ℝ) :
    Tendsto (fun X : ℕ => (t / fibreScale M (X ^ 2)) *
      ⟪Matrix.toEuclideanLin
          (completeWeilMatrix φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40))
          (harmonicCenteredPacketVector (X ^ 40)
            (normalizedConductorPacket (m * M)
              (primeFibreIncidenceCoefficients (additionalFibrePrimes m M) m (fun _ => 1)))),
        fibreChargeTerminalReceiver l R X⟫) atTop (𝓝 0) := by
  have hX2 : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hX40 : Tendsto (fun X : ℕ => X ^ 40) atTop atTop := tendsto_pow_atTop (by omega)
  have hfix := (tendsto_harmonicCentered_fixedPacket_complete_norm_at_critical_overlap
    hφ hsupp hφM hK (m * M)
      (primeFibreIncidenceCoefficients (additionalFibrePrimes m M) m (fun _ => 1))).comp hX40
  have hlim := (((fibreScale_tendsto_atTop hM).comp hX2).const_div_atTop t).abs.mul hfix
  simp only [Function.comp_apply, abs_zero, zero_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_fibreChargeTerminalReceiver_norm_le_one hl hR] with X hx
  rw [Real.norm_eq_abs, abs_mul,
    harmonicCenteredPacketVector_conductor (Nat.mul_pos hm hM)]
  exact mul_le_mul_of_nonneg_left
    ((abs_real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq
      (mul_one _))) (abs_nonneg _)

/-- A common prime exclusion preserves the complete signed receiving coefficient of each fibre. -/
theorem tendsto_commonPrimeFibreCharge_complete_terminalReceiver {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {m M l R : ℕ}
    (hm : 0 < m) (hM : 0 < M) (hmM : m ∣ M) (hl : 0 < l) (hmR : m ≤ R) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪Matrix.toEuclideanLin
          (completeWeilMatrix φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40))
          (commonPrimeFibreChargeVector m M (X ^ 2) (X ^ 40) t),
        fibreChargeTerminalReceiver l R X⟫)
      atTop (𝓝 ((if m = l then 1 else 0) * (t / 80))) := by
  have hX2 : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have h := (((tendsto_fibreScale_div_common hM hmM).comp hX2).mul
    (tendsto_harmonicFibreCharge_complete_terminalReceiver hφ hφ0 hsupp hφM hK hm hl hmR t)).sub
      (tendsto_additionalFibre_complete_pairing hφ hsupp hφM hK hm hM hl (hm.trans_le hmR) t)
  simp only [one_mul, sub_zero, Function.comp_apply] at h
  apply h.congr'
  filter_upwards [hX2.eventually_ge_atTop M,
    ((fibreScale_tendsto_atTop hm).comp hX2).eventually_gt_atTop 0] with X hQ hb
  rw [commonPrimeFibreChargeVector_eq hm hM hmM hQ hb,
    map_sub, map_smul, map_smul, inner_sub_left, real_inner_smul_left, real_inner_smul_left]

/-- The common physical packet is the literal sum of its individually centered fibres. -/
theorem commonPrimeFibreVector_eq_sum {M Q : ℕ} (hM : 0 < M) (hQ : 1 ≤ Q)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (N : ℕ) (t : ℕ → ℝ) :
    commonPrimeFibreVector S M Q N t = ∑ m ∈ S, commonPrimeFibreChargeVector m M Q N (t m) := by
  have he : commonPrimeFibreVector S M Q N t =
      harmonicCenteredPacketVector N (commonPrimeFibreProfile S M Q t) := by
    unfold commonPrimeFibreVector harmonicCenteredPacketVector
    congr 2
    funext n
    exact commonPrimeFibre_packet_formula hM hQ S hS N t n
  rw [he]
  unfold commonPrimeFibreProfile
  rw [harmonicCenteredPacketVector_sum]
  rfl

/-- Every exact prescribed finite receiving coordinate survives in the complete signed form. -/
theorem tendsto_commonPrimeFibre_complete_terminalReceiver {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {M l : ℕ} (hM : 0 < M) (hl : 0 < l)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪Matrix.toEuclideanLin
          (completeWeilMatrix φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40))
          (commonPrimeFibreVector S M (X ^ 2) (X ^ 40) t),
        fibreChargeTerminalReceiver l M X⟫)
      atTop (𝓝 (if l ∈ S then t l / 80 else 0)) := by
  have h := tendsto_finsetSum S (fun m hm =>
    tendsto_commonPrimeFibreCharge_complete_terminalReceiver hφ hφ0 hsupp hφM hK
      (hS m hm).1 hM (hS m hm).2 hl (Nat.le_of_dvd hM (hS m hm).2) (t m))
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq'] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [commonPrimeFibreVector_eq_sum hM (Nat.one_le_pow 2 X hX) S hS, map_sum, sum_inner]

#print axioms tendsto_fibreScale_div_common
#print axioms tendsto_commonPrimeFibreCharge_complete_terminalReceiver
#print axioms tendsto_commonPrimeFibre_complete_terminalReceiver

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
