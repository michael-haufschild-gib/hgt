import GaloisForLFunctions.RHTower.BottcherPrueferXiCharge
import GaloisForLFunctions.RHTower.IrrationalCircleOrderCharge
import GaloisForLFunctions.RHTower.PrimeAlgebraicTranslationWeylPhase
import GaloisForLFunctions.RHTower.PrimeIrrationalRotationKZeroRH
import GaloisForLFunctions.RHTower.PrimeQuadraticGelfondSchneiderPhase
import GaloisForLFunctions.RHTower.QuadraticCircleFreeOrbitCharge
import GaloisForLFunctions.RHTower.SEMFittingCharge
import GaloisForLFunctions.RHTower.SEMTruncatedJetWeylCharge

/-!
# Xi local analytic-order phase universality

The finite local Xi analytic order is one invariant seen independently by algebraic prime phases,
irrational circle charges, rotation `K₀`, algebraic Weyl descent, the Böttcher Prüfer tower, and
completed symmetric Euler--Maclaurin phases.  This pointwise law precedes—and is stronger than—the
separate vacuous right-half-zero RH consumers.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Every actual completed-SEM realization at `rho` has trivial prime circle, dyadic phase, and
integral Fitting charge. -/
def XiLocalAnalyticOrderSEMPhaseCertificate (p : Nat.Primes) (rho : ℂ) : Prop :=
  ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
    ∀ h : SEMSplitData rho r₀ R N zs u,
      completedSEMPrimeCircleCharge p rho r₀ R N = 0 ∧
      ∀ k : ℕ,
        Bottcher.dyadicRoot k ^ zs.length = 1 ∧
        integralJetCharge 1 (2 ^ k) (by omega)
          (fittingBoundaryClass 1 (standardPresZ 1)
            (semHoleDefectZ h)) = 0

/-- Simultaneous algebraic, circle, `K₀`, Weyl, Prüfer, and completed-SEM realization of one
local analytic-order datum. -/
def XiLocalAnalyticOrderPhaseUniversalCertificate
    (p : Nat.Primes) (q : ℕ) (rho : ℂ) : Prop :=
  IsAlgebraic ℚ (xiReflectionPairQuadraticAlgebraicPhase p rho) ∧
  xiReflectionPairQuadraticCircleCharge p rho = 0 ∧
  Nonempty (XiPrimeRotationKZeroIndexDatum p q rho) ∧
  Nonempty (XiAlgebraicPrimeWeylDeterminantDescent p q rho) ∧
  (∀ n : ℕ, xiBottcherPrueferCharge rho n = 1) ∧
  xiPrimeOrderCircleCharge p rho = 0 ∧
  XiLocalAnalyticOrderSEMPhaseCertificate p rho

/-- **Xi local analytic-order phase universality law.** At every complex point and every nonzero
prime-translation step, local Xi order zero is equivalent to simultaneous realization in seven
algebraic, topological, `K`-theoretic, Prüfer, and completed-SEM charts. -/
theorem xiLocalAnalyticOrder_eq_zero_iff_phaseUniversalCertificate
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) (rho : ℂ) :
    (analyticOrderAt xi rho).toNat = 0 ↔
      XiLocalAnalyticOrderPhaseUniversalCertificate p q rho := by
  constructor
  · intro horder
    have hprimeCircle : xiPrimeOrderCircleCharge p rho = 0 :=
      (xiPrimeOrderCircleCharge_eq_zero_iff p rho).2 horder
    refine ⟨
      (xiReflectionPairQuadraticAlgebraicPhase_isAlgebraic_iff p rho).2 horder,
      (xiReflectionPairQuadraticCircleCharge_eq_zero_iff p rho).2 horder,
      (primeRotationKZeroIndexDatum_iff p hq
        (analyticOrderAt xi rho).toNat).2 horder,
      (algebraicPrimeWeylDeterminantDescent_iff p
        (analyticOrderAt xi rho).toNat hq).2 horder,
      (xiBottcherPrueferCharge_all_one_iff rho).2 horder,
      hprimeCircle,
      ?_⟩
    intro r₀ R N zs u hsplit
    have hlen : zs.length = 0 := by
      rw [← semSplitData_count_eq hsplit]
      exact horder
    refine ⟨?_, fun k => ⟨?_, ?_⟩⟩
    · rw [completedSEMPrimeCircleCharge_eq_xiPrimeOrderCircleCharge p hsplit]
      exact hprimeCircle
    · simp [hlen]
    · rw [integralJetCharge_semHoleDefectZ_eq_xiOrder hsplit (by omega), horder]
      simp
  · intro hcertificate
    exact (xiReflectionPairQuadraticAlgebraicPhase_isAlgebraic_iff p rho).1
      hcertificate.1

/-- Simultaneous explicit failure of all six pointwise non-SEM order detectors. -/
def XiLocalAnalyticOrderPhaseFailureUniversalCertificate
    (p : Nat.Primes) (q : ℕ) (rho : ℂ) : Prop :=
  (¬ IsAlgebraic ℚ (xiReflectionPairQuadraticAlgebraicPhase p rho)) ∧
  xiReflectionPairQuadraticCircleCharge p rho ≠ 0 ∧
  (¬ Nonempty (XiPrimeRotationKZeroIndexDatum p q rho)) ∧
  (¬ Nonempty (XiAlgebraicPrimeWeylDeterminantDescent p q rho)) ∧
  (∃ n : ℕ, xiBottcherPrueferCharge rho n ≠ 1) ∧
  xiPrimeOrderCircleCharge p rho ≠ 0

/-- **Complementary local analytic-order phase failure law.** Nonzero finite local order is
equivalent to simultaneous algebraic, circle, `K₀`, Weyl, and Prüfer failure witnesses. -/
theorem xiLocalAnalyticOrder_ne_zero_iff_phaseFailureUniversalCertificate
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) (rho : ℂ) :
    (analyticOrderAt xi rho).toNat ≠ 0 ↔
      XiLocalAnalyticOrderPhaseFailureUniversalCertificate p q rho := by
  classical
  constructor
  · intro horder
    have hnotBottcher : ¬∀ n : ℕ, xiBottcherPrueferCharge rho n = 1 :=
      (xiBottcherPrueferCharge_all_one_iff rho).not.2 horder
    push Not at hnotBottcher
    exact ⟨
      (xiReflectionPairQuadraticAlgebraicPhase_isAlgebraic_iff p rho).not.2 horder,
      (xiReflectionPairQuadraticCircleCharge_eq_zero_iff p rho).not.2 horder,
      (primeRotationKZeroIndexDatum_iff p hq
        (analyticOrderAt xi rho).toNat).not.2 horder,
      (algebraicPrimeWeylDeterminantDescent_iff p
        (analyticOrderAt xi rho).toNat hq).not.2 horder,
      hnotBottcher,
      (xiPrimeOrderCircleCharge_eq_zero_iff p rho).not.2 horder⟩
  · intro hcertificate horder
    exact hcertificate.1
      ((xiReflectionPairQuadraticAlgebraicPhase_isAlgebraic_iff p rho).2 horder)

/-- Right-half-zero corollary of the pointwise law.  This is the common non-vacuous core behind
the separate algebraic, circle, `K₀`, Weyl, Prüfer, and SEM RH consumers. -/
theorem riemannHypothesis_iff_all_rightZeros_localPhaseUniversalCertificate
    (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    RiemannHypothesis ↔
      ∀ rho ∈ rightHalf, xi rho = 0 →
        XiLocalAnalyticOrderPhaseUniversalCertificate p q rho := by
  constructor
  · intro hRH rho hrho hzero
    exact (rh_iff_xi_ne_zero_right.1 hRH rho hrho hzero).elim
  · intro hcertificate
    apply rh_iff_xi_ne_zero_right.2
    intro rho hrho hzero
    have horder :=
      (xiLocalAnalyticOrder_eq_zero_iff_phaseUniversalCertificate p hq rho).2
        (hcertificate rho hrho hzero)
    exact (xi_order_toNat_ne_zero hzero horder).elim

end

end RHTower
