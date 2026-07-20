import GaloisForLFunctions.RHTower.XiCompletedBalancedResponseDirichletDecomposition
import GaloisForLFunctions.RHTower.XiSquaredEulerRayFullResponse

/-!
# Positive local stiffness of the corrected physical endpoint

The proposed cofinal ratio-kernel cancellation cannot start with a vanishing continuum mode.
The corrected completed endpoint kernel has a strictly positive value at zero frequency.  The
proof is source-only: its value contains

* twice the positive Xi Euler response at `s = 2`;
* the negative endpoint contribution `-xiEndpointCompletedCurvature / 2`; and
* the fused valuation correction, whose prime-two term alone is `log 2 / 6`.

The established curvature bound makes the prime-two correction strictly larger than the negative
endpoint contribution.  Thus the zero mode is positive without RH.

This exposes the exact positive survivor of the failed continuum-cancellation conjecture.  The
completed signed aperture energy splits into a mandatory positive local stiffness and a uniquely
zero-frequency-renormalized tangent energy.  Any height-localized contraction must act on this
tangent kernel; asking the unrenormalized energy to vanish loses this source-forced term.
-/

open Complex Set
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem summable_endpointFusedCorrectionMass :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) + 1))) := by
  have h := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 1 2 (by norm_num)
  have hnat : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
    apply h.congr
    intro n
    rcases n with _ | n
    · simp
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by norm_num)
    rw [abs_of_nonneg hlog, pow_one, Real.rpow_neg hn.le]
    rw [show ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) by
      exact Real.rpow_natCast _ 2]
    field_simp
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) / (p : ℝ) ^ 2) :=
    hnat.comp_injective Subtype.val_injective
  apply Summable.of_nonneg_of_le
  · intro p
    exact div_nonneg (Real.log_nonneg (by
      exact_mod_cast p.prop.one_lt.le)) (by positivity)
  · intro p
    have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
    exact div_le_div_of_nonneg_left hlog (sq_pos_of_pos hp) (by nlinarith)
  · exact hprime

/-- At zero frequency the phase-preserving valuation correction is its positive fused
ordinary-prime mass. -/
theorem xiPhysicalEndpointValuationCorrectionKernel_zero_eq_fusedMass :
    xiPhysicalEndpointValuationCorrectionKernel 0 =
      (∑' p : Nat.Primes,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) : ℝ) := by
  rw [xiPhysicalEndpointValuationCorrectionKernel]
  have hsum := summable_xiPhysicalEndpointValuationCorrectionKernelTerm 0
  rw [hsum.tsum_prod]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  simp only [xiPhysicalEndpointValuationCorrectionKernelTerm]
  simp
  rw [tsum_mul_left, ← Complex.ofReal_tsum,
    tsum_xiPhysicalEndpointValuationCorrection]
  push_cast
  ring

/-- The real logarithmic derivative of Xi at one is half the completed endpoint curvature. -/
theorem logDeriv_xi_one_re_eq_half_endpointCompletedCurvature :
    (logDeriv xi 1).re = xiEndpointCompletedCurvature / 2 := by
  have hchain := logDeriv_XiC_eq_mul_I_logDeriv_xi (I / 2)
  have harg : (1 / 2 : ℂ) + (I / 2) * I = 0 := by
    field_simp
    rw [I_sq]
    ring
  rw [harg] at hchain
  have hrec : logDeriv xi 0 = -logDeriv xi 1 := by
    have h := logDeriv_xi_reciprocity 1
    norm_num at h
    exact h
  rw [hrec] at hchain
  rw [xiEndpointCompletedCurvature, hchain]
  simp [div_re, normSq_apply, mul_re, mul_im]
  ring

/-- The positive real Euler ray makes the Xi logarithmic derivative strictly positive at two. -/
theorem logDeriv_xi_two_re_pos : 0 < (logDeriv xi 2).re := by
  have hQ := xiSquaredEulerFullQ_eq_logDeriv_re
    (x := (3 / 2 : ℝ)) (by norm_num)
  norm_num at hQ
  rw [← hQ, xiSquaredEulerFullQ]
  exact mul_pos (by norm_num)
    (xiSquaredEulerFullResponse_pos (sq_nonneg (3 / 2 : ℝ)))

/-- The prime-two fibre gives an explicit positive lower bound for the complete fused
correction. -/
theorem primeTwo_le_endpointFusedCorrectionMass :
    Real.log 2 / 6 ≤
      ∑' p : Nat.Primes,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) := by
  have hle := summable_endpointFusedCorrectionMass.le_tsum
    (⟨2, by norm_num⟩ : Nat.Primes) (fun p _ =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le))
        (by positivity))
  norm_num at hle ⊢
  exact hle

/-- **Source-forced local stiffness.**  The corrected physical endpoint kernel is strictly
positive at zero frequency, unconditionally. -/
theorem xiPhysicalEndpointCompletedKernel_zero_re_pos :
    0 < (xiPhysicalEndpointCompletedKernel 0).re := by
  have htwo := logDeriv_xi_two_re_pos
  have hcorr := primeTwo_le_endpointFusedCorrectionMass
  have hcurv := xiEndpointCompletedCurvature_lt_two_over_fortyThree
  have hlog := Real.log_two_gt_d9
  have hgap : xiEndpointCompletedCurvature / 2 < Real.log 2 / 6 := by
    nlinarith
  rw [xiPhysicalEndpointCompletedKernel,
    xiCompletedApertureOffDiagonalKernel,
    xiCompletedApertureOffDiagonalKernel,
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num,
    sub_self, ofReal_zero, zero_mul, add_zero,
    seamFluxCochain, seamFluxCochain,
    xiPhysicalEndpointValuationCorrectionKernel_zero_eq_fusedMass]
  norm_num
  rw [logDeriv_xi_one_re_eq_half_endpointCompletedCurvature]
  nlinarith

/-- Remove the source-forced zero-frequency stiffness from the corrected ratio kernel. -/
def xiPhysicalEndpointTangentPrimeRatioRealKernel
    (p q : Nat.Primes) : ℝ :=
  xiPhysicalEndpointCompletedPrimeRatioRealKernel p q -
    (xiPhysicalEndpointCompletedKernel 0).re

theorem xiPhysicalEndpointCompletedPrimeRatioRealKernel_self_eq
    (p : Nat.Primes) :
    xiPhysicalEndpointCompletedPrimeRatioRealKernel p p =
      (xiPhysicalEndpointCompletedKernel 0).re := by
  rw [xiPhysicalEndpointCompletedPrimeRatioRealKernel]
  simp

theorem xiPhysicalEndpointTangentPrimeRatioRealKernel_symm
    (p q : Nat.Primes) :
    xiPhysicalEndpointTangentPrimeRatioRealKernel p q =
      xiPhysicalEndpointTangentPrimeRatioRealKernel q p := by
  rw [xiPhysicalEndpointTangentPrimeRatioRealKernel,
    xiPhysicalEndpointTangentPrimeRatioRealKernel,
    xiPhysicalEndpointCompletedPrimeRatioRealKernel_symm]

theorem xiPhysicalEndpointTangentPrimeRatioRealKernel_self
    (p : Nat.Primes) :
    xiPhysicalEndpointTangentPrimeRatioRealKernel p p = 0 := by
  rw [xiPhysicalEndpointTangentPrimeRatioRealKernel,
    xiPhysicalEndpointCompletedPrimeRatioRealKernel_self_eq]
  ring

/-- The positive zero-frequency part of the completed endpoint Dirichlet energy. -/
def xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      (xiPhysicalEndpointCompletedKernel 0).re *
        xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2

/-- The residual Dirichlet energy after removing the positive local stiffness. -/
def xiPhysicalEndpointCompletedApertureTangentEnergy
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalEndpointTangentPrimeRatioRealKernel p q *
        xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2

theorem xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy_nonneg
    (P : Finset Nat.Primes) (A m k : ℝ) :
    0 ≤ xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy P A m k := by
  unfold xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (physicalPrimeEndpointWeight_pos p).le
        (physicalPrimeEndpointWeight_pos q).le)
      xiPhysicalEndpointCompletedKernel_zero_re_pos.le)
    (sq_nonneg _)

/-- On a two-prime packet the local stiffness is exactly twice the positive weighted aperture
separation.  Thus the source-forced zero mode is not merely nonnegative: it is strictly present
whenever the true aperture distinguishes the two primes. -/
theorem xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy_pair
    {p q : Nat.Primes} (hpq : p ≠ q) (A m k : ℝ) :
    xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy {p, q} A m k =
      2 * physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
        (xiPhysicalEndpointCompletedKernel 0).re *
          xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 := by
  rw [xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy]
  simp only [Finset.sum_insert, Finset.mem_singleton, hpq, not_false_eq_true,
    Finset.sum_singleton, xiPhysicalPrimeLogApertureHilbertDistance_self,
    xiPhysicalPrimeLogApertureHilbertDistance_symm]
  ring

theorem xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy_pair_pos
    {p q : Nat.Primes} (hpq : p ≠ q) {A m k : ℝ}
    (hdist : 0 < xiPhysicalPrimeLogApertureHilbertDistance A m k p q) :
    0 < xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy {p, q} A m k := by
  rw [xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy_pair hpq]
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos (by norm_num) (physicalPrimeEndpointWeight_pos p))
        (physicalPrimeEndpointWeight_pos q))
      xiPhysicalEndpointCompletedKernel_zero_re_pos)
    (sq_pos_of_pos hdist)

/-- **Exact local-stiffness decomposition.**  The completed signed energy is a mandatory positive
zero-frequency term plus the uniquely tangent-renormalized energy. -/
theorem xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_localStiffness_add_tangent
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy P A m k =
      xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy P A m k +
        xiPhysicalEndpointCompletedApertureTangentEnergy P A m k := by
  rw [xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_kernel_distance,
    xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy,
    xiPhysicalEndpointCompletedApertureTangentEnergy,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [xiPhysicalEndpointTangentPrimeRatioRealKernel]
  ring

/-- The physical completed response pairing has a forced positive local-stiffness debit and one
remaining tangent response.  This is the corrected replacement for the false claim that the raw
Dirichlet energy itself can vanish cofinally. -/
theorem xiPhysicalEndpointCompletedBalancedAperturePairing_eq_marginal_sub_half_localStiffness_sub_half_tangent
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalEndpointCompletedBalancedAperturePairing P A m k =
      (∑ p ∈ P, physicalPrimeEndpointWeight p *
        ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ ^ 2) -
      (1 / 2 : ℝ) *
        xiPhysicalEndpointCompletedApertureLocalStiffnessEnergy P A m k -
      (1 / 2 : ℝ) *
        xiPhysicalEndpointCompletedApertureTangentEnergy P A m k := by
  rw [xiPhysicalEndpointCompletedBalancedAperturePairing_eq_marginal_sub_half_dirichlet,
    xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_localStiffness_add_tangent]
  ring

end

end RHTower
