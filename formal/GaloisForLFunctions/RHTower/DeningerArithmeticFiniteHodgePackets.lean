import GaloisForLFunctions.RHTower.DeningerArithmeticLocalHodgeObstruction
import GaloisForLFunctions.RHTower.DeningerArithmeticGeometricJetExhaustion

/-!
# Finite positive Hodge packets and no cancellation

Positive real combinations of the canonical local rank-one Hodge forms give finite
source-defined Hodge packets.  Each packet is positive semidefinite, and its Frobenius commutator
is the corresponding weighted sum of local purity defects.

Finite Hermite interpolation isolates any selected Xi coordinate.  Therefore distinct local
defects cannot cancel in a Frobenius-invariant packet with strictly positive weights: every point
in the packet must already have real centered coordinate.  Applying this to the geometric
closed-disk exhaustion gives an exact finite-window Hodge route to RH, with no limiting trace or
divisor-defined Hilbert carrier hidden in the statement.
-/

open Complex

namespace RHTower

noncomputable section

/-- Positive finite packet assembled from source-local zeroth-jet Hodge forms. -/
def deningerCompactOpenFiniteJetHodge
    (S : Finset XiDivisorSupport)
    (weight : XiDivisorSupport → ℝ) :
    DeningerArithmeticCompactOpenH1 →L⋆[ℂ]
      DeningerArithmeticTopologicalH1Compact :=
  ∑ rho ∈ S,
    (weight rho : ℂ) •
      deningerCompactOpenLocalJetHodge rho

@[simp]
theorem deningerCompactOpenFiniteJetHodge_apply
    (S : Finset XiDivisorSupport)
    (weight : XiDivisorSupport → ℝ)
    (x y : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenFiniteJetHodge S weight x y =
      ∑ rho ∈ S,
        (weight rho : ℂ) *
          (starRingEnd ℂ
            (deningerCompactOpenH1Jet rho
              (deningerArithmeticJetIndexZero rho) x) *
            deningerCompactOpenH1Jet rho
              (deningerArithmeticJetIndexZero rho) y) := by
  simp [deningerCompactOpenFiniteJetHodge,
    deningerCompactOpenLocalJetHodge_apply]

/-- A packet diagonal is the weighted sum of local squared jet norms. -/
theorem deningerCompactOpenFiniteJetHodge_self_re
    (S : Finset XiDivisorSupport)
    (weight : XiDivisorSupport → ℝ)
    (x : DeningerArithmeticCompactOpenH1) :
    (deningerCompactOpenFiniteJetHodge S weight x x).re =
      ∑ rho ∈ S,
        weight rho * Complex.normSq
          (deningerCompactOpenH1Jet rho
            (deningerArithmeticJetIndexZero rho) x) := by
  rw [deningerCompactOpenFiniteJetHodge_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

/-- Nonnegative packet weights give an unconditional positive-semidefinite Hodge form. -/
theorem deningerCompactOpenFiniteJetHodge_nonnegative
    (S : Finset XiDivisorSupport)
    (weight : XiDivisorSupport → ℝ)
    (hweight : ∀ rho ∈ S, 0 ≤ weight rho)
    (x : DeningerArithmeticCompactOpenH1) :
    0 ≤ (deningerCompactOpenFiniteJetHodge S weight x x).re := by
  rw [deningerCompactOpenFiniteJetHodge_self_re]
  exact Finset.sum_nonneg fun rho hrho =>
    mul_nonneg (hweight rho hrho)
      (Complex.normSq_nonneg _)

/-- Exact Frobenius commutator of a finite weighted local Hodge packet. -/
theorem deningerCompactOpenFiniteJetHodge_theta_defect
    (S : Finset XiDivisorSupport)
    (weight : XiDivisorSupport → ℝ)
    (x : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenThetaCompact
          (deningerCompactOpenFiniteJetHodge S weight x) -
        deningerCompactOpenFiniteJetHodge S weight
          (deningerCompactOpenTheta x) =
      ∑ rho ∈ S,
        ((weight rho : ℂ) *
          (1 -
            (1 / 2 + Complex.I *
              xiSpectralPointSupport rho) -
            starRingEnd ℂ
              (1 / 2 + Complex.I *
                xiSpectralPointSupport rho))) •
          deningerCompactOpenLocalJetHodge rho x := by
  unfold deningerCompactOpenFiniteJetHodge
  simp only [ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  rw [map_sum]
  simp_rw [map_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  apply ContinuousLinearMap.ext
  intro y
  have h :=
    congrArg
      (fun L : DeningerArithmeticTopologicalH1Compact =>
        L y)
      (deningerCompactOpenLocalJetHodge_theta_defect
        rho x)
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply] at h ⊢
  linear_combination (weight rho : ℂ) * h

/--
No-cancellation theorem at one point: invariance of a positive finite Hodge packet forces that
point's centered coordinate to be real.
-/
theorem deningerCompactOpenFiniteJetHodge_commutes_point_real
    (S : Finset XiDivisorSupport)
    (weight : XiDivisorSupport → ℝ)
    (rho : XiDivisorSupport)
    (hrho : rho ∈ S)
    (hweight : 0 < weight rho)
    (hcomm :
      ∀ x : DeningerArithmeticCompactOpenH1,
        deningerCompactOpenThetaCompact
            (deningerCompactOpenFiniteJetHodge
              S weight x) =
          deningerCompactOpenFiniteJetHodge S weight
            (deningerCompactOpenTheta x)) :
    (xiSpectralPointSupport rho).im = 0 := by
  classical
  let target :
      (tau : ↥S) →
        DeningerArithmeticJetIndex tau.1 → ℂ :=
    fun tau k =>
      if tau.1 = rho ∧ (k : ℕ) = 0 then 1 else 0
  obtain ⟨F, hF⟩ :=
    exists_deningerCompactOpenPolynomial_finiteXiScalarJets
      S target
  let x : DeningerArithmeticCompactOpenH1 :=
    deningerArithmeticCompactOpenH1Class F
  have hjet
      (tau : ↥S) :
      deningerCompactOpenH1Jet tau.1
          (deningerArithmeticJetIndexZero tau.1) x =
        if tau.1 = rho then 1 else 0 := by
    dsimp only [x]
    rw [deningerCompactOpenH1Jet_class,
      hF tau (deningerArithmeticJetIndexZero tau.1)]
    simp [target, deningerArithmeticJetIndexZero]
  have hdefect :=
    deningerCompactOpenFiniteJetHodge_theta_defect
      S weight x
  rw [hcomm x, sub_self] at hdefect
  have heval :=
    congrArg
      (fun L : DeningerArithmeticTopologicalH1Compact =>
        L x)
      hdefect
  simp only [ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply] at heval
  have hsum :
      ∑ tau ∈ S,
        ((weight tau : ℂ) *
          (1 -
            (1 / 2 + Complex.I *
              xiSpectralPointSupport tau) -
            starRingEnd ℂ
              (1 / 2 + Complex.I *
                xiSpectralPointSupport tau))) *
          (starRingEnd ℂ
            (deningerCompactOpenH1Jet tau
              (deningerArithmeticJetIndexZero tau) x) *
            deningerCompactOpenH1Jet tau
              (deningerArithmeticJetIndexZero tau) x) =
        0 := by
    simpa only [
      deningerCompactOpenLocalJetHodge_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      mul_assoc] using heval.symm
  have hrhoScalar :
      (weight rho : ℂ) *
        (1 -
          (1 / 2 + Complex.I *
            xiSpectralPointSupport rho) -
          starRingEnd ℂ
            (1 / 2 + Complex.I *
              xiSpectralPointSupport rho)) = 0 := by
    rw [Finset.sum_eq_single rho] at hsum
    · have hjetrho :
          deningerCompactOpenH1Jet rho
              (deningerArithmeticJetIndexZero rho) x =
            1 := by
        simpa using hjet ⟨rho, hrho⟩
      simpa [hjetrho] using hsum
    · intro tau htau hne
      have hjettau :
          deningerCompactOpenH1Jet tau
              (deningerArithmeticJetIndexZero tau) x =
            0 := by
        have hne' : tau ≠ rho := hne
        simpa [hne'] using hjet ⟨tau, htau⟩
      simp [hjettau]
    · intro hnot
      exact (hnot hrho).elim
  have hweightC : (weight rho : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hweight
  have hc :
      1 -
        (1 / 2 + Complex.I *
          xiSpectralPointSupport rho) -
        starRingEnd ℂ
          (1 / 2 + Complex.I *
            xiSpectralPointSupport rho) = 0 :=
    (mul_eq_zero.mp hrhoScalar).resolve_left hweightC
  have hre := congrArg Complex.re hc
  norm_num [Complex.mul_re] at hre
  linarith

/-- A commuting packet with positive support weights has only real centered Xi points. -/
theorem deningerCompactOpenFiniteJetHodge_commutes_support_real
    (S : Finset XiDivisorSupport)
    (weight : XiDivisorSupport → ℝ)
    (hweight : ∀ rho ∈ S, 0 < weight rho)
    (hcomm :
      ∀ x : DeningerArithmeticCompactOpenH1,
        deningerCompactOpenThetaCompact
            (deningerCompactOpenFiniteJetHodge
              S weight x) =
          deningerCompactOpenFiniteJetHodge S weight
            (deningerCompactOpenTheta x)) :
    ∀ rho ∈ S, (xiSpectralPointSupport rho).im = 0 :=
  fun rho hrho =>
    deningerCompactOpenFiniteJetHodge_commutes_point_real
      S weight rho hrho (hweight rho hrho) hcomm

/--
Frobenius invariance on every finite geometric Hodge window implies RH.

This statement exposes the remaining arithmetic task as a family of finite source identities.
-/
theorem riemannHypothesis_of_deningerFiniteJetHodge_exhaustion_commutes
    (weight : XiDivisorSupport → ℝ)
    (hweight : ∀ rho, 0 < weight rho)
    (hcomm :
      ∀ (n : ℕ)
        (x : DeningerArithmeticCompactOpenH1),
        deningerCompactOpenThetaCompact
            (deningerCompactOpenFiniteJetHodge
              (deningerXiSupportClosedBallFinset n)
              weight x) =
          deningerCompactOpenFiniteJetHodge
            (deningerXiSupportClosedBallFinset n)
            weight (deningerCompactOpenTheta x)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  obtain ⟨n, hn⟩ :=
    deningerXiSupportClosedBallFinset_covers q.1
  have him :
      (xiSpectralPointSupport q.1).im = 0 :=
    deningerCompactOpenFiniteJetHodge_commutes_point_real
      (deningerXiSupportClosedBallFinset n)
      weight q.1 hn (hweight q.1) (hcomm n)
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · rw [xiSpectralPoint_eq_support]
    simpa using him

end

end RHTower
