import GaloisForLFunctions.RHTower.XiMassCriticalDiagonalPrimeCoronaGrowth
import GaloisForLFunctions.RHTower.XiHeightAdaptiveFiniteLadder
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity

/-!
# Sharp zero-density growth of the critical Xi diagonal corona

The exact critical-wall localization leaves one finite packet of Xi zero copies whose Poisson
height is comparable to the moving mass.  This module counts that packet with the corpus's
unconditional global Xi zero-count envelope.

The key bridge is multiplicity-exact: every finite packet supported in a closed Xi disc injects,
fiber by fiber, into the divisor mass of that disc.  Thus the critical corona has `O(r log r)`
cardinality, and the literal von-Mangoldt source on `4σv=1` obeys the same sharp envelope up to
fixed trace and Archimedean constants.  No RH, zero-free, or cancellation assumption enters.
-/

open Complex Metric Set
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem card_xiZeroCopyFiber_eq_order_toNat (ρ : XiDivisorSupport) :
    (xiZeroCopyFiber ρ).card = (analyticOrderAt xi (ρ : ℂ)).toNat := by
  rw [card_xiZeroCopyFiber, MeromorphicOn.AnalyticOnNhd.divisor_apply
    xi_analyticOnNhd_univ (Set.mem_univ _)]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (xi_order_ne_top (ρ : ℂ))
  rw [← hm]
  simp

/-- Any finite multiplicity-copy packet supported in one Xi disc is bounded by the disc divisor
mass. -/
theorem card_le_xiBallOrderSum_of_support_mem
    {r : ℝ} (S : Finset XiZeroCopy)
    (hS : ∀ q ∈ S, (q.1 : ℂ) ∈ closedBall (2 : ℂ) r) :
    (S.card : ℝ) ≤ ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) := by
  classical
  let B : Finset XiDivisorSupport := S.image Sigma.fst
  let Q : Finset XiZeroCopy := B.biUnion xiZeroCopyFiber
  have hdisj : (B : Set XiDivisorSupport).PairwiseDisjoint xiZeroCopyFiber := by
    intro ρ hρ τ hτ hne
    change Disjoint (xiZeroCopyFiber ρ) (xiZeroCopyFiber τ)
    rw [Finset.disjoint_left]
    intro q hqρ hqτ
    have hρeq : q.1 = ρ := mem_xiZeroCopyFiber.mp hqρ
    have hτeq : q.1 = τ := mem_xiZeroCopyFiber.mp hqτ
    exact hne (hρeq.symm.trans hτeq)
  have hSQ : S ⊆ Q := by
    intro q hq
    rw [show Q = B.biUnion xiZeroCopyFiber from rfl, Finset.mem_biUnion]
    refine ⟨q.1, ?_, ?_⟩
    · rw [show B = S.image Sigma.fst from rfl, Finset.mem_image]
      exact ⟨q, hq, rfl⟩
    · exact mem_xiZeroCopyFiber.mpr rfl
  have hcardSQ : S.card ≤ Q.card := Finset.card_le_card hSQ
  have hcardQ : Q.card = ∑ ρ ∈ B, (xiZeroCopyFiber ρ).card := by
    exact Finset.card_biUnion hdisj
  let D := MeromorphicOn.divisor xi (closedBall (2 : ℂ) r)
  let DT := D.finiteSupport (isCompact_closedBall (2 : ℂ) r)
  let e : XiDivisorSupport ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let BC : Finset ℂ := B.map e
  have hBCsub : BC ⊆ DT.toFinset := by
    intro z hz
    rw [show BC = B.map e from rfl, Finset.mem_map] at hz
    obtain ⟨ρ, hρB, rfl⟩ := hz
    have hρimage : ∃ q ∈ S, q.1 = ρ := by
      simpa only [B, Finset.mem_image] using hρB
    obtain ⟨q, hqS, hqρ⟩ := hρimage
    have hball : (ρ : ℂ) ∈ closedBall (2 : ℂ) r := by
      rw [← hqρ]
      exact hS q hqS
    have hDρ : D (ρ : ℂ) = ((analyticOrderAt xi (ρ : ℂ)).toNat : ℤ) := by
      exact xi_divisor_closedBall_eq_order_toNat hball
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    change D (ρ : ℂ) ≠ 0
    rw [hDρ]
    exact_mod_cast xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support ρ)
  have hterm (ρ : XiDivisorSupport) (hρ : ρ ∈ B) :
      ((xiZeroCopyFiber ρ).card : ℝ) = (D (ρ : ℂ) : ℝ) := by
    have hρimage : ∃ q ∈ S, q.1 = ρ := by
      simpa only [B, Finset.mem_image] using hρ
    obtain ⟨q, hqS, hqρ⟩ := hρimage
    have hball : (ρ : ℂ) ∈ closedBall (2 : ℂ) r := by
      rw [← hqρ]
      exact hS q hqS
    rw [xi_divisor_closedBall_eq_order_toNat hball,
      card_xiZeroCopyFiber_eq_order_toNat]
    norm_cast
  have hsumMap :
      (∑ ρ ∈ B, ((xiZeroCopyFiber ρ).card : ℝ)) =
        ∑ z ∈ BC, (D z : ℝ) := by
    rw [show BC = B.map e from rfl, Finset.sum_map]
    exact Finset.sum_congr rfl hterm
  have hDnonneg : ∀ z ∈ DT.toFinset, 0 ≤ (D z : ℝ) := by
    intro z hz
    have hzsupport : z ∈ D.support := by
      rw [← Set.Finite.mem_toFinset]
      exact hz
    have hzdom : z ∈ closedBall (2 : ℂ) r :=
      D.supportWithinDomain hzsupport
    rw [xi_divisor_closedBall_eq_order_toNat hzdom]
    positivity
  have hsumle : (∑ z ∈ BC, (D z : ℝ)) ≤ ∑ z ∈ DT.toFinset, (D z : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hBCsub (fun z hz _ => hDnonneg z hz)
  have hballSum :
      (∑ z ∈ DT.toFinset, (D z : ℝ)) =
        ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) := by
    simpa only [D, DT] using (xiBallOrderSum_cast_eq_finsetSum (2 : ℂ) r).symm
  have hcardReal : (S.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcardSQ
  rw [hcardQ] at hcardReal
  push_cast at hcardReal
  calc
    (S.card : ℝ) ≤ ∑ ρ ∈ B, ((xiZeroCopyFiber ρ).card : ℝ) := hcardReal
    _ = ∑ z ∈ BC, (D z : ℝ) := hsumMap
    _ ≤ ∑ z ∈ DT.toFinset, (D z : ℝ) := hsumle
    _ = ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) := hballSum

/-- Every zero copy in the critical diagonal corona lies in an explicit global Xi disc. -/
theorem xiMassCriticalDiagonalCorona_support_mem_closedBall
    {a : ℝ} (_ha : 2 ≤ a) {q : XiZeroCopy}
    (hq : q ∈ xiMassCriticalDiagonalCorona a) :
    (q.1 : ℂ) ∈ closedBall (2 : ℂ) (2 * (a - 1 / 2) + 2) := by
  have hmem := xiPoissonAbstract.mem_criticalDiagonalCorona.mp hq
  have hR : (xiPoissonPoint q).re ≤ 2 * (a - 1 / 2) := by
    simpa only [xiMassCriticalDiagonalCorona, xiPoissonAbstract_pt] using hmem.2
  have hRnn : 0 ≤ (xiPoissonPoint q).re := xiPoissonPoint_re_nonneg q
  have himP : |(xiPoissonPoint q).im| < 1 / 2 := abs_xiPoissonPoint_im_lt_half q
  have himAbs : |(xiSpectralPoint q).im| = |(xiPoissonPoint q).im| := by
    unfold xiPoissonPoint
    split_ifs <;> simp
  have himAlpha : |(xiSpectralPoint q).im| < 1 / 2 := by rw [himAbs]; exact himP
  have hAlphaIm : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    rw [xiSpectralPoint]
    simp [Complex.mul_im]
  have hrhoRe : 0 < (q.1 : ℂ).re ∧ (q.1 : ℂ).re < 1 := by
    rw [abs_lt] at himAlpha
    constructor <;> linarith
  have hAlphaRe : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    rw [xiSpectralPoint]
    simp [Complex.mul_re]
  have himRho : |(q.1 : ℂ).im| = (xiPoissonPoint q).re := by
    rw [← hAlphaRe, xiPoissonPoint_re_eq_abs]
  rw [mem_closedBall, dist_eq_norm]
  apply le_of_lt
  calc
    ‖(q.1 : ℂ) - 2‖ ≤ |((q.1 : ℂ) - 2).re| + |((q.1 : ℂ) - 2).im| :=
      norm_le_abs_re_add_abs_im _
    _ < 2 + (xiPoissonPoint q).re := by
      rw [sub_re, sub_im]
      norm_num
      rw [abs_of_neg (by linarith : (q.1 : ℂ).re - 2 < 0), himRho]
      linarith
    _ ≤ 2 * (a - 1 / 2) + 2 := by linarith

/-- Sharp corpus zero-density envelope for the critical cofinal corona. -/
theorem xiMassCriticalDiagonalCorona_card_le_zeroCountEnvelope
    {a : ℝ} (ha : 2 ≤ a) :
    let r := 2 * (a - 1 / 2) + 2
    ((xiMassCriticalDiagonalCorona a).card : ℝ) ≤
      xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r) := by
  dsimp only
  let r : ℝ := 2 * (a - 1 / 2) + 2
  have hr : 1 ≤ r := by dsimp only [r]; linarith
  have hpacket := card_le_xiBallOrderSum_of_support_mem
    (r := r) (xiMassCriticalDiagonalCorona a)
    (fun q hq => by
      dsimp only [r]
      exact xiMassCriticalDiagonalCorona_support_mem_closedBall ha hq)
  exact hpacket.trans (xiBallOrderSum_le_zeroCountEnvelope r hr)

/-- **Critical `O(r log r)` source law.**  The literal prime source on the phase wall is bounded by
the sharp unconditional Xi zero-count envelope, plus fixed spectral and Gamma constants. -/
theorem norm_xiMassBottomPrimeIntegral_critical_le_zeroCountEnvelope
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) (u : ℝ) :
    let a := xiObliqueComovingMass v u
    let r := 2 * (a - 1 / 2) + 2
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ *
          (xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r)) +
        ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (σ / 12) +
        xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let a : ℝ := xiObliqueComovingMass v u
  let r : ℝ := 2 * (a - 1 / 2) + 2
  have ha : 2 ≤ a := by
    dsimp only [a]
    exact xiObliqueComovingMass_ge_two hv.le u
  have hsource :=
    norm_xiMassBottomPrimeIntegral_critical_le_coronaCard_add_tails hσ hv hcritical u
  have hcard : ((xiMassCriticalDiagonalCorona a).card : ℝ) ≤
      xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r) := by
    simpa only [r] using xiMassCriticalDiagonalCorona_card_le_zeroCountEnvelope ha
  have htraceNonneg : 0 ≤ xiPoissonTraceReal (σ / 12) := xiPoissonTraceReal_nonneg _
  have harchNonneg : 0 ≤ xiMassBottomArchUniformBound 2 (σ / 2) :=
    xiMassBottomArchUniformBound_nonneg (by norm_num) (by positivity)
  have hA : 0 ≤ a - 1 / 2 := by linarith
  have hexpTrace : Real.exp (-(σ / 12) * (a - 1 / 2)) ≤ 1 := by
    have hnonpos : -(σ / 12) * (a - 1 / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hA
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonpos
  have hexpArch : Real.exp (-(σ / 2) * (a - 1 / 2)) ≤ 1 := by
    have hnonpos : -(σ / 2) * (a - 1 / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hA
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonpos
  have htraceTail :
      Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12) ≤
        xiPoissonTraceReal (σ / 12) :=
    mul_le_of_le_one_left htraceNonneg hexpTrace
  have harchTail :
      Real.exp (-(σ / 2) * (a - 1 / 2)) * xiMassBottomArchUniformBound 2 (σ / 2) ≤
        xiMassBottomArchUniformBound 2 (σ / 2) :=
    mul_le_of_le_one_left harchNonneg hexpArch
  have hcardMul := mul_le_mul_of_nonneg_left hcard (norm_nonneg ((Real.pi : ℂ) * I))
  have htraceMul := mul_le_mul_of_nonneg_left htraceTail (norm_nonneg ((Real.pi : ℂ) * I))
  have hsource' :
      ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
        ‖(Real.pi : ℂ) * I‖ * (xiMassCriticalDiagonalCorona a).card +
          ‖(Real.pi : ℂ) * I‖ *
            (Real.exp (-(σ / 12) * (a - 1 / 2)) *
              xiPoissonTraceReal (σ / 12)) +
          Real.exp (-(σ / 2) * (a - 1 / 2)) *
            xiMassBottomArchUniformBound 2 (σ / 2) := by
    simpa only [a] using hsource
  have hbound :
      ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
        ‖(Real.pi : ℂ) * I‖ *
            (xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r)) +
          ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (σ / 12) +
          xiMassBottomArchUniformBound 2 (σ / 2) :=
    hsource'.trans (by linarith)
  simpa only [a, r] using hbound

end

end RHTower
