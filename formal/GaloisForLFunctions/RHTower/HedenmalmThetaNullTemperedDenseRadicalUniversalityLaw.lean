import GaloisForLFunctions.HTGeometry.SchwartzSesquilinearTempered
import GaloisForLFunctions.RHTower.HedenmalmUniversalPositiveFormClassification
import GaloisForLFunctions.RHTower.XiThetaSchwartzL2Nonclosability

/-!
# Hedenmalm theta-null tempered dense-radical universality

For a nonnegative momentum-symmetric Schwartz form, one scalar equality at the completed theta
source forces far more than a single null vector.  The positive spectral representation upgrades
diagonal theta nullity to a complete left-radical statement.  Translation covariance and ordinary
`L²` cyclicity then put the full theta orbit in a dense radical image, while tempered currying
identifies ordinary-`L²` closability with vanishing of the entire distribution family.
-/

open Complex Function Filter Set MeasureTheory
open scoped Topology SchwartzMap

noncomputable section

namespace RHTower

/-- Scalar theta nullity forces every curried tempered distribution to annihilate every real
translate of the completed theta source. -/
theorem universalPositiveForm_thetaNull_leftTemperedDistribution_translationOrbit
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0)
    (v : SchwartzMap ℝ ℂ) (a : ℝ) :
    Q.leftTemperedDistribution v (xiThetaSchwartzTranslationOrbit a) = 0 := by
  exact (xiThetaSchwartzTranslationOrbit_mem_leftRadical Q hQ
    (universalPositiveForm_theta_leftRadical_of_thetaNull Q hQ hQnonneg hnull) a) v

/-- Scalar theta nullity already makes the ordinary-`L²` image of the form radical dense. -/
theorem dense_xiThetaL2RadicalImage_of_scalarThetaNull
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    Dense (xiThetaL2RadicalImage Q : Set XiThetaL2) :=
  dense_xiThetaL2RadicalImage Q hQ
    (universalPositiveForm_theta_leftRadical_of_thetaNull Q hQ hQnonneg hnull)

/-- In the scalar theta-null cone, ordinary-`L²` closability is exactly disappearance of every
curried tempered distribution. -/
theorem universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_leftTemperedDistribution_zero
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 ↔
      ∀ v : SchwartzMap ℝ ℂ, Q.leftTemperedDistribution v = 0 := by
  rw [universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_zero
    Q hQ hQnonneg hnull]
  constructor
  · intro hzero v
    ext u
    exact hzero u v
  · intro hzero u v
    have huv := congrArg (fun T : TemperedDistribution ℝ ℂ => T u) (hzero v)
    exact huv

/-- **Theta-null tempered dense-radical law.** A nonzero nonnegative momentum-symmetric form
annihilating only the theta diagonal has a nonzero atomic divisor measure, a dense proper
nonclosed ordinary-`L²` radical image, a nonzero curried tempered distribution, and is not
sequentially closable through ordinary `L²`. -/
theorem universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hQ : Q.MomentumSymmetric) (hQnonneg : Q.IsNonnegative)
    (hnull : Q xiThetaSchwartzSource xiThetaSchwartzSource = 0)
    (hNonzero : ∃ u v : SchwartzMap ℝ ℂ, Q u v ≠ 0) :
    Q.compactSpectralRieszMeasure hQ hQnonneg ≠ 0 ∧
      Dense (xiThetaL2RadicalImage Q : Set XiThetaL2) ∧
      ¬ IsClosed (xiThetaL2RadicalImage Q : Set XiThetaL2) ∧
      (∃ v : SchwartzMap ℝ ℂ, Q.leftTemperedDistribution v ≠ 0) ∧
      ¬ Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 := by
  have hleft : ∀ w : SchwartzMap ℝ ℂ, Q xiThetaSchwartzSource w = 0 :=
    universalPositiveForm_theta_leftRadical_of_thetaNull Q hQ hQnonneg hnull
  have hmeasure : Q.compactSpectralRieszMeasure hQ hQnonneg ≠ 0 := by
    intro hzero
    obtain ⟨u, v, huv⟩ := hNonzero
    exact huv ((universalPositiveForm_identicallyZero_iff_canonicalMeasure_zero
      Q hQ hQnonneg).mpr hzero u v)
  have hdense : Dense (xiThetaL2RadicalImage Q : Set XiThetaL2) :=
    dense_xiThetaL2RadicalImage Q hQ hleft
  have hnotClosed : ¬ IsClosed (xiThetaL2RadicalImage Q : Set XiThetaL2) :=
    not_isClosed_xiThetaL2RadicalImage Q hQ hleft hNonzero
  have hdistribution : ∃ v : SchwartzMap ℝ ℂ, Q.leftTemperedDistribution v ≠ 0 := by
    by_contra hnone
    have hall : ∀ v : SchwartzMap ℝ ℂ, Q.leftTemperedDistribution v = 0 := by
      intro v
      by_contra hv
      exact hnone ⟨v, hv⟩
    obtain ⟨u, v, huv⟩ := hNonzero
    have hzero := congrArg (fun T : TemperedDistribution ℝ ℂ => T u) (hall v)
    exact huv hzero
  have hnotClosable : ¬ Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 := by
    rw [universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_leftTemperedDistribution_zero
      Q hQ hQnonneg hnull]
    exact not_forall.mpr hdistribution
  exact ⟨hmeasure, hdense, hnotClosed, hdistribution, hnotClosable⟩

end RHTower
