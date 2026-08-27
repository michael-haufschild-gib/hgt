import GaloisForLFunctions.RHTower.XiPhysicalEndpointLocalStiffness
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointHilbertSchmidt
import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureSourceRetentionWall
import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelVariance
import GaloisForLFunctions.RHTower.ReciprocalCoareaEnergy

/-!
# Cofinal invariance under physical endpoint valuation completion

The completed physical endpoint retains the ordinary-prime layer and removes every deeper
prime-power layer through an absolutely summable valuation correction.  This module identifies
that correction coefficientwise inside the finite physical aperture Dirichlet energy.

On a translated support packet of fixed logarithmic width, Mertens' first theorem bounds the total
physical endpoint mass independently of translation.  The Hilbert aperture diameter and the
absolute correction-kernel mass then give one explicit, scale-free perturbation budget.  Hence
existence of either a cofinal upper bound or a cofinal lower floor is equivalent before and after
valuation completion.

This removes prime-power completion from the open cofinal-growth burden.  It does not prove the
remaining bound for the refinement-oriented completed seam response and makes no RH assertion.
-/

open scoped BigOperators RealInnerProductSpace
open Complex

namespace RHTower

noncomputable section

/-- Real-symmetric sampling of the phase-preserving valuation correction. -/
def xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel
    (p q : Nat.Primes) : ℝ :=
  ((xiPhysicalEndpointValuationCorrectionKernel
      (Real.log (p : ℝ) - Real.log (q : ℝ)) +
    xiPhysicalEndpointValuationCorrectionKernel
      (Real.log (q : ℝ) - Real.log (p : ℝ))) / 2).re

theorem xiPhysicalEndpointCompletedPrimeRatioRealKernel_eq_refinement_add_correction
    (p q : Nat.Primes) :
    xiPhysicalEndpointCompletedPrimeRatioRealKernel p q =
      -xiUnitDoubleCompletedPrimeRatioRealKernel p q +
        xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel p q := by
  rw [xiPhysicalEndpointCompletedPrimeRatioRealKernel,
    xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel,
    xiPhysicalEndpointCompletedKernel_eq_neg_unitDouble_add_correction,
    xiPhysicalEndpointCompletedKernel_eq_neg_unitDouble_add_correction]
  have hswap := xiUnitDoubleCompletedOffDiagonalResponseKernel_swap
    (Real.log (p : ℝ)) (Real.log (q : ℝ))
  have hforward :
      xiUnitDoubleCompletedOffDiagonalResponseKernel
          (Real.log (p : ℝ)) (Real.log (q : ℝ)) =
        xiUnitDoubleCompletedOffDiagonalResponseKernel
          (Real.log (p : ℝ) - Real.log (q : ℝ)) 0 := by
    rw [xiUnitDoubleCompletedOffDiagonalResponseKernel,
      xiUnitDoubleCompletedOffDiagonalResponseKernel,
      xiCompletedApertureOffDiagonalKernel,
      xiCompletedApertureOffDiagonalKernel,
      xiCompletedApertureOffDiagonalKernel,
      xiCompletedApertureOffDiagonalKernel]
    ring_nf
  have hbackward :
      xiUnitDoubleCompletedOffDiagonalResponseKernel
          (Real.log (q : ℝ)) (Real.log (p : ℝ)) =
        xiUnitDoubleCompletedOffDiagonalResponseKernel
          (Real.log (q : ℝ) - Real.log (p : ℝ)) 0 := by
    rw [xiUnitDoubleCompletedOffDiagonalResponseKernel,
      xiUnitDoubleCompletedOffDiagonalResponseKernel,
      xiCompletedApertureOffDiagonalKernel,
      xiCompletedApertureOffDiagonalKernel,
      xiCompletedApertureOffDiagonalKernel,
      xiCompletedApertureOffDiagonalKernel]
    ring_nf
  rw [← hforward, ← hbackward]
  rw [show xiUnitDoubleCompletedPrimeRatioRealKernel p q =
      (xiUnitDoubleCompletedOffDiagonalResponseKernel
        (Real.log (p : ℝ)) (Real.log (q : ℝ))).re by rfl]
  rw [hswap]
  simp
  ring

/-- Signed aperture Dirichlet energy carried only by valuation correction. -/
def xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
      xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel p q *
        xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2

theorem xiUnitDoubleCompletedRefinementApertureDirichletEnergy_eq_kernel_distance
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiUnitDoubleCompletedRefinementApertureDirichletEnergy P A m k =
      ∑ p ∈ P, ∑ q ∈ P,
        physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
          (-xiUnitDoubleCompletedPrimeRatioRealKernel p q) *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 := by
  rw [xiUnitDoubleCompletedRefinementApertureDirichletEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hpq : p = q
  · subst q
    simp [xiPhysicalPrimeLogApertureHilbertDistance]
  · rw [xiUnitDoubleCompletedRefinementCoupling,
      xiUnitDoubleCompletedBalancedResponseCoupling, if_neg hpq,
      xiUnitDoubleCompletedPhysicalPairResponse,
      xiPhysicalPrimeLogApertureHilbertDistance, dist_eq_norm]
    ring

/-- Exact coefficientwise split of completed endpoint energy into refinement and correction. -/
theorem xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy P A m k =
      xiUnitDoubleCompletedRefinementApertureDirichletEnergy P A m k +
        xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy P A m k := by
  rw [xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_kernel_distance,
    xiUnitDoubleCompletedRefinementApertureDirichletEnergy_eq_kernel_distance,
    xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [xiPhysicalEndpointCompletedPrimeRatioRealKernel_eq_refinement_add_correction]
  ring

theorem abs_xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel_le
    (p q : Nat.Primes) :
    |xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel p q| ≤
      routeKPhysicalEndpointCorrectionMass := by
  let t : ℝ := Real.log (p : ℝ) - Real.log (q : ℝ)
  have hplus := norm_xiPhysicalEndpointValuationCorrectionKernel_le t
  have hminus := norm_xiPhysicalEndpointValuationCorrectionKernel_le (-t)
  have hre :
      |((xiPhysicalEndpointValuationCorrectionKernel t +
          xiPhysicalEndpointValuationCorrectionKernel (-t)) / 2).re| ≤
        (‖xiPhysicalEndpointValuationCorrectionKernel t‖ +
          ‖xiPhysicalEndpointValuationCorrectionKernel (-t)‖) / 2 := by
    calc
      |((xiPhysicalEndpointValuationCorrectionKernel t +
          xiPhysicalEndpointValuationCorrectionKernel (-t)) / 2).re| ≤
          ‖(xiPhysicalEndpointValuationCorrectionKernel t +
            xiPhysicalEndpointValuationCorrectionKernel (-t)) / 2‖ :=
        Complex.abs_re_le_norm _
      _ ≤ (‖xiPhysicalEndpointValuationCorrectionKernel t‖ +
          ‖xiPhysicalEndpointValuationCorrectionKernel (-t)‖) / 2 := by
        rw [norm_div, norm_ofNat]
        gcongr
        exact norm_add_le _ _
  have hfinal :
      |((xiPhysicalEndpointValuationCorrectionKernel t +
          xiPhysicalEndpointValuationCorrectionKernel (-t)) / 2).re| ≤
        routeKPhysicalEndpointCorrectionMass := by
    calc
      _ ≤ (‖xiPhysicalEndpointValuationCorrectionKernel t‖ +
          ‖xiPhysicalEndpointValuationCorrectionKernel (-t)‖) / 2 := hre
      _ ≤ (routeKPhysicalEndpointCorrectionMass +
          routeKPhysicalEndpointCorrectionMass) / 2 := by gcongr
      _ = routeKPhysicalEndpointCorrectionMass := by ring
  simpa [xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel, t,
    sub_eq_add_neg] using hfinal

theorem xiPhysicalPrimeLogApertureHilbertDistance_sq_le_four_mul
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p q : Nat.Primes) :
    xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 ≤ 4 * A := by
  let vp := xiPhysicalPrimeLogCenteredApertureCarrier A m k p
  let vq := xiPhysicalPrimeLogCenteredApertureCarrier A m k q
  have hpLength := norm_sq_xiPhysicalPrimeLogCenteredApertureCarrier_le_length
    hA m k p
  have hqLength := norm_sq_xiPhysicalPrimeLogCenteredApertureCarrier_le_length
    hA m k q
  have hpA := xiPhysicalPrimeLogApertureLength_le hA.le m k p
  have hqA := xiPhysicalPrimeLogApertureLength_le hA.le m k q
  have hp : ‖vp‖ ^ 2 ≤ A := hpLength.trans hpA
  have hq : ‖vq‖ ^ 2 ≤ A := hqLength.trans hqA
  have htri : ‖vp - vq‖ ≤ ‖vp‖ + ‖vq‖ := norm_sub_le _ _
  have hsq : ‖vp - vq‖ ^ 2 ≤ (‖vp‖ + ‖vq‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
  have hsum : (‖vp‖ + ‖vq‖) ^ 2 ≤ 4 * A := by
    nlinarith [sq_nonneg (‖vp‖ - ‖vq‖)]
  rw [xiPhysicalPrimeLogApertureHilbertDistance, dist_eq_norm]
  exact hsq.trans hsum

/-- Uniform finite-packet perturbation budget.  Completion by all prime powers costs at most the
absolute valuation-correction mass times four aperture lengths and the square of endpoint mass. -/
theorem abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_le
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    |xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy P A m k| ≤
      4 * A * routeKPhysicalEndpointCorrectionMass *
        xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by
  rw [xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy]
  calc
    |∑ p ∈ P, ∑ q ∈ P,
        physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
          xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel p q *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2| ≤
      ∑ p ∈ P, ∑ q ∈ P,
        |physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
          xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel p q *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        4 * A * routeKPhysicalEndpointCorrectionMass *
          (physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q) := by
      refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
      have hwp : 0 ≤ physicalPrimeEndpointWeight p :=
        (physicalPrimeEndpointWeight_pos p).le
      have hwq : 0 ≤ physicalPrimeEndpointWeight q :=
        (physicalPrimeEndpointWeight_pos q).le
      have hk := abs_xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel_le p q
      have hd := xiPhysicalPrimeLogApertureHilbertDistance_sq_le_four_mul hA m k p q
      rw [abs_mul,
        abs_of_nonneg (sq_nonneg
          (xiPhysicalPrimeLogApertureHilbertDistance A m k p q)),
        abs_mul, abs_mul,
        abs_of_nonneg hwp, abs_of_nonneg hwq]
      have hmass := routeKPhysicalEndpointCorrectionMass_nonneg
      let w := physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q
      have hw : 0 ≤ w := mul_nonneg hwp hwq
      calc
        w * |xiPhysicalEndpointValuationCorrectionPrimeRatioRealKernel p q| *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 ≤
          w * routeKPhysicalEndpointCorrectionMass *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hk hw) (sq_nonneg _)
        _ ≤ w * routeKPhysicalEndpointCorrectionMass * (4 * A) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hw hmass)
        _ = 4 * A * routeKPhysicalEndpointCorrectionMass * w := by ring
    _ = 4 * A * routeKPhysicalEndpointCorrectionMass *
        xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by
      rw [xiPhysicalPrimeLogEndpointTotalWeight, sq, Finset.sum_mul_sum]
      simp_rw [Finset.mul_sum]

private theorem loop82_sum_Ioc_eq_sum_Icc_sub
    (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U, f n) =
      (∑ n ∈ Finset.Icc 1 U, f n) - ∑ n ∈ Finset.Icc 1 L, f n := by
  have hsub : Finset.Icc 1 L ⊆ Finset.Icc 1 U := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hLU⟩
  have hdiff : Finset.Icc 1 U \ Finset.Icc 1 L = Finset.Ioc L U := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hdiff, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff hsub

theorem sum_primeLogWindow_log_div_eq_mertensPrimeWeightSum_sub
    {H T : ℝ} (hHT : H ≤ T) :
    (∑ n ∈ primeLogWindow H T, Real.log n / (n : ℝ)) =
      mertensPrimeWeightSum ⌊Real.exp T⌋₊ -
        mertensPrimeWeightSum ⌊Real.exp H⌋₊ := by
  have hfloor : ⌊Real.exp H⌋₊ ≤ ⌊Real.exp T⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hHT)
  rw [primeLogWindow, mertensPrimeWeightSum_eq, mertensPrimeWeightSum_eq]
  rw [show (∑ n ∈ (Finset.Ioc ⌊Real.exp H⌋₊ ⌊Real.exp T⌋₊).filter Nat.Prime,
      Real.log n / (n : ℝ)) =
      ∑ n ∈ Finset.Ioc ⌊Real.exp H⌋₊ ⌊Real.exp T⌋₊,
        mertensPrimeWeight n by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp [mertensPrimeWeight]]
  rw [loop82_sum_Ioc_eq_sum_Icc_sub mertensPrimeWeight hfloor]
  congr 1 <;>
    rw [Finset.sum_filter] <;>
    apply Finset.sum_congr rfl <;>
    intro n hn <;>
    simp [mertensPrimeWeight]

/-- Mertens gives a scale-free endpoint-mass bound on every fixed logarithmic support window. -/
theorem xiPhysicalPrimeLogWindowPacket_totalWeight_le_fixedWidth
    {A m c : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (hlow : 2 ≤ Real.exp (m - A)) :
    xiPhysicalPrimeLogEndpointTotalWeight
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) ≤
      A + c + primeLogWindowConst := by
  have hHT : m - A ≤ m + c := by linarith
  have hhigh : 2 ≤ Real.exp (m + c) := by
    exact hlow.trans (Real.exp_le_exp.mpr hHT)
  have hlowErr := abs_le.mp
    (abs_mertensPrimeWeightSum_floor_sub_log_le hlow)
  have hhighErr := abs_le.mp
    (abs_mertensPrimeWeightSum_floor_sub_log_le hhigh)
  rw [xiPhysicalPrimeLogEndpointTotalWeight,
    sum_xiPhysicalPrimeLogWindowPacket_weight_eq,
    sum_primeLogWindow_log_div_eq_mertensPrimeWeightSum_sub hHT]
  rw [Real.log_exp] at hlowErr hhighErr
  rw [primeLogWindowConst]
  linarith [hlowErr.1, hhighErr.2]

/-- **Scale-free valuation-completion law.** At fixed physical aperture and fixed logarithmic
window width, all prime-power completion changes the signed aperture Dirichlet energy by a bound
independent of the translated prime scale `m`. -/
theorem abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_supportPacket_le
    {A m c : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (hlow : 2 ≤ Real.exp (m - A)) :
    |xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c))
        A m (m + c)| ≤
      4 * A * routeKPhysicalEndpointCorrectionMass *
        (A + c + primeLogWindowConst) ^ 2 := by
  let P := xiPhysicalPrimeLogWindowPacket (m - A) (m + c)
  have hbase :=
    abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_le
      P hA m (m + c)
  have hW : 0 ≤ xiPhysicalPrimeLogEndpointTotalWeight P :=
    xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have hWle : xiPhysicalPrimeLogEndpointTotalWeight P ≤
      A + c + primeLogWindowConst :=
    xiPhysicalPrimeLogWindowPacket_totalWeight_le_fixedWidth hA hc hlow
  have hB : 0 ≤ A + c + primeLogWindowConst := hW.trans hWle
  have hsquare : xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 ≤
      (A + c + primeLogWindowConst) ^ 2 :=
    (sq_le_sq₀ hW hB).2 hWle
  have hcoef : 0 ≤ 4 * A * routeKPhysicalEndpointCorrectionMass :=
    mul_nonneg (mul_nonneg (by norm_num) hA.le)
      routeKPhysicalEndpointCorrectionMass_nonneg
  exact hbase.trans (mul_le_mul_of_nonneg_left hsquare hcoef)

theorem abs_physicalEndpointCompleted_sub_refinement_supportPacket_le
    {A m c : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (hlow : 2 ≤ Real.exp (m - A)) :
    |xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
          (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c) -
        xiUnitDoubleCompletedRefinementApertureDirichletEnergy
          (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)| ≤
      4 * A * routeKPhysicalEndpointCorrectionMass *
        (A + c + primeLogWindowConst) ^ 2 := by
  rw [xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction]
  have h :=
    abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_supportPacket_le
      hA hc hlow
  simpa only [add_sub_cancel_left] using h

/-- Valuation completion is invisible to existence of a cofinal lower floor on fixed-width
physical packets: its entire contribution is one uniformly bounded perturbation. -/
theorem physicalEndpointCompleted_lowerFloor_iff_refinement_lowerFloor
    {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c) :
    (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
      B ≤ xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)) ↔
    (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
      B ≤ xiUnitDoubleCompletedRefinementApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)) := by
  let K : ℝ := 4 * A * routeKPhysicalEndpointCorrectionMass *
    (A + c + primeLogWindowConst) ^ 2
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B - K, ?_⟩
    intro m hlow
    let P := xiPhysicalPrimeLogWindowPacket (m - A) (m + c)
    have hsplit :=
      xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction
        P A m (m + c)
    have hperturb :=
      abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_supportPacket_le
        hA hc hlow
    have hupper :
        xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy P A m (m + c) ≤ K :=
      (abs_le.mp hperturb).2
    have hcompleted := hB m hlow
    rw [hsplit] at hcompleted
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨B - K, ?_⟩
    intro m hlow
    let P := xiPhysicalPrimeLogWindowPacket (m - A) (m + c)
    have hsplit :=
      xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction
        P A m (m + c)
    have hperturb :=
      abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_supportPacket_le
        hA hc hlow
    have hlower :
        -K ≤ xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy P A m (m + c) :=
      (abs_le.mp hperturb).1
    have hrefinement := hB m hlow
    rw [hsplit]
    linarith

/-- The still-open cofinal upper bound on completed physical endpoint Dirichlet energy is
equivalent to the same bound for refinement alone. Prime-power valuation completion contributes no
new cofinal growth burden. -/
theorem physicalEndpointCompleted_upperBound_iff_refinement_upperBound
    {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c) :
    (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
      xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c) ≤ B) ↔
    (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
      xiUnitDoubleCompletedRefinementApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c) ≤ B) := by
  let K : ℝ := 4 * A * routeKPhysicalEndpointCorrectionMass *
    (A + c + primeLogWindowConst) ^ 2
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + K, ?_⟩
    intro m hlow
    let P := xiPhysicalPrimeLogWindowPacket (m - A) (m + c)
    have hsplit :=
      xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction
        P A m (m + c)
    have hperturb :=
      abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_supportPacket_le
        hA hc hlow
    have hlower :
        -K ≤ xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy P A m (m + c) :=
      (abs_le.mp hperturb).1
    have hcompleted := hB m hlow
    rw [hsplit] at hcompleted
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨B + K, ?_⟩
    intro m hlow
    let P := xiPhysicalPrimeLogWindowPacket (m - A) (m + c)
    have hsplit :=
      xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction
        P A m (m + c)
    have hperturb :=
      abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_supportPacket_le
        hA hc hlow
    have hupper :
        xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy P A m (m + c) ≤ K :=
      (abs_le.mp hperturb).2
    have hrefinement := hB m hlow
    rw [hsplit]
    linarith

end

end RHTower
