import GaloisForLFunctions.RHTower.Deninger.DeningerEntireScalingCoverQuotientFunctoriality
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCenteredPrimeMarkXiFiberComparison

/-!
# Big-Witt / scaled completed-Xi cross-fibre natural transformation

Half-scaling pullback changes the completed-Xi quotient together with the scaling cover.  The
resulting algebra equivalence sends the centered theta fibre at `alpha` to the target fibre at
`2 * alpha`.  Big-Witt Frobenius two and the centered-prime-mark reporters then form an exact
naturality square.

This is a genuine cross-fibre map because the analytic receiver varies.  It assumes neither
`XiC alpha = 0 → XiC (2 * alpha) = 0` nor stability of the fixed completed-Xi quotient.
-/

open Complex

namespace RHTower

noncomputable section

/-- Coordinate class on the degree-two scaled completed-Xi quotient. -/
def deningerEntireScaledTwoCoordinateClass : DeningerEntireScaledTwoH1 :=
  deningerEntireScaledTwoH1Class deningerEntireCoordinate

/-- Theta class on the degree-two scaled completed-Xi quotient. -/
def deningerEntireScaledTwoThetaClass : DeningerEntireScaledTwoH1 :=
  algebraMap ℂ DeningerEntireScaledTwoH1 (1 / 2) +
    algebraMap ℂ DeningerEntireScaledTwoH1 Complex.I *
      deningerEntireScaledTwoCoordinateClass

/-- Theta generator on the degree-two scaled completed-Xi quotient. -/
def deningerEntireScaledTwoTheta :
    Module.End ℂ DeningerEntireScaledTwoH1 :=
  LinearMap.mulLeft ℂ deningerEntireScaledTwoThetaClass

@[simp] theorem deningerEntireScaledTwoTheta_apply
    (x : DeningerEntireScaledTwoH1) :
    deningerEntireScaledTwoTheta x =
      deningerEntireScaledTwoThetaClass * x :=
  rfl

/-- The coordinate has scaling weight two under half-scaling pullback. -/
theorem deningerEntireScaledTwoCoordinateClass_eq_two_mul_pullback :
    deningerEntireScaledTwoCoordinateClass =
      algebraMap ℂ DeningerEntireScaledTwoH1 2 *
        deningerEntireHalfPullbackQuotientEquiv
          deningerEntireCoordinateClass := by
  have hcoordinate :
      deningerEntireCoordinate =
        algebraMap ℂ DeningerEntire 2 *
          deningerEntireHalfPullback deningerEntireCoordinate := by
    apply DeningerEntire.ext
    intro z
    change z = 2 * (z / 2)
    rw [mul_comm]
    norm_num
  rw [deningerEntireScaledTwoCoordinateClass,
    deningerEntireCoordinateClass]
  calc
    deningerEntireScaledTwoH1Class deningerEntireCoordinate =
        deningerEntireScaledTwoH1Class
          (algebraMap ℂ DeningerEntire 2 *
            deningerEntireHalfPullback deningerEntireCoordinate) :=
      congrArg deningerEntireScaledTwoH1Class hcoordinate
    _ = algebraMap ℂ DeningerEntireScaledTwoH1 2 *
        deningerEntireScaledTwoH1Class
          (deningerEntireHalfPullback deningerEntireCoordinate) := by
      rw [map_mul, deningerEntireScaledTwoH1Class.commutes]
    _ = algebraMap ℂ DeningerEntireScaledTwoH1 2 *
        deningerEntireHalfPullbackQuotientEquiv
          (deningerEntireH1Class deningerEntireCoordinate) := by
      rw [deningerEntireHalfPullbackQuotientEquiv_class]

/-- Affine weight-two relation for the theta classes. -/
theorem deningerEntireScaledTwoThetaClass_eq_affine_pullback :
    deningerEntireScaledTwoThetaClass =
      algebraMap ℂ DeningerEntireScaledTwoH1 2 *
          deningerEntireHalfPullbackQuotientEquiv
            deningerEntireThetaClass -
        algebraMap ℂ DeningerEntireScaledTwoH1 (1 / 2) := by
  rw [deningerEntireScaledTwoThetaClass,
    deningerEntireScaledTwoCoordinateClass_eq_two_mul_pullback,
    deningerEntireThetaClass_eq,
    map_add, map_mul,
    deningerEntireHalfPullbackQuotientEquiv.commutes,
    deningerEntireHalfPullbackQuotientEquiv.commutes]
  have htwo_half :
      algebraMap ℂ DeningerEntireScaledTwoH1 2 *
          algebraMap ℂ DeningerEntireScaledTwoH1 (1 / 2) = 1 := by
    rw [← map_mul]
    norm_num
  have hhalf_add_half :
      algebraMap ℂ DeningerEntireScaledTwoH1 (1 / 2) +
          algebraMap ℂ DeningerEntireScaledTwoH1 (1 / 2) = 1 := by
    rw [← map_add]
    norm_num
  linear_combination hhalf_add_half - htwo_half

/-- Half-scaling pullback intertwines theta by the exact affine weight-two law. -/
theorem deningerEntireScaledTwoTheta_halfPullback_intertwining
    (x : DeningerEntireH1) :
    deningerEntireScaledTwoTheta
        (deningerEntireHalfPullbackQuotientEquiv x) =
      (2 : ℂ) •
          deningerEntireHalfPullbackQuotientEquiv
            (deningerEntireTheta x) -
        (1 / 2 : ℂ) •
          deningerEntireHalfPullbackQuotientEquiv x := by
  rw [deningerEntireScaledTwoTheta_apply, deningerEntireTheta_apply,
    deningerEntireScaledTwoThetaClass_eq_affine_pullback, map_mul]
  have htwo :
      (2 : ℂ) •
          (deningerEntireHalfPullbackQuotientEquiv deningerEntireThetaClass *
            deningerEntireHalfPullbackQuotientEquiv x) =
        algebraMap ℂ DeningerEntireScaledTwoH1 2 *
          (deningerEntireHalfPullbackQuotientEquiv deningerEntireThetaClass *
            deningerEntireHalfPullbackQuotientEquiv x) :=
    Algebra.smul_def (R := ℂ) (A := DeningerEntireScaledTwoH1) _ _
  have hhalf :
      (1 / 2 : ℂ) • deningerEntireHalfPullbackQuotientEquiv x =
        algebraMap ℂ DeningerEntireScaledTwoH1 (1 / 2) *
          deningerEntireHalfPullbackQuotientEquiv x :=
    Algebra.smul_def (R := ℂ) (A := DeningerEntireScaledTwoH1) _ _
  rw [htwo, hhalf]
  ring

/-- Exact spectral equation transport under the degree-two scaling cover. -/
theorem deningerEntireTheta_eigen_equation_halfPullback_iff
    (alpha : ℂ) (x : DeningerEntireH1) :
    deningerEntireTheta x =
        (1 / 2 + Complex.I * alpha) • x ↔
      deningerEntireScaledTwoTheta
          (deningerEntireHalfPullbackQuotientEquiv x) =
        (1 / 2 + Complex.I * ((2 : ℂ) * alpha)) •
          deningerEntireHalfPullbackQuotientEquiv x := by
  constructor
  · intro hx
    rw [deningerEntireScaledTwoTheta_halfPullback_intertwining, hx,
      map_smul]
    module
  · intro hx
    apply deningerEntireHalfPullbackQuotientEquiv.injective
    rw [map_smul]
    have hintertwining :=
      deningerEntireScaledTwoTheta_halfPullback_intertwining x
    rw [hx] at hintertwining
    linear_combination (norm := module) (-1 / 2 : ℂ) • hintertwining

/-- Nonzero theta spectral fibre on the degree-two scaled completed-Xi quotient. -/
abbrev ScaledTwoCompletedXiThetaSpectralFiber (alpha : ℂ) :=
  {x : DeningerEntireScaledTwoH1 //
    x ≠ 0 ∧
      deningerEntireScaledTwoTheta x =
        (1 / 2 + Complex.I * alpha) • x}

/-- Canonical cross-fibre equivalence induced by the degree-two scaling cover. -/
def completedXiScaledTwoCrossFiberEquiv (alpha : ℂ) :
    CompletedXiThetaSpectralFiber alpha ≃
      ScaledTwoCompletedXiThetaSpectralFiber ((2 : ℂ) * alpha) :=
  deningerEntireHalfPullbackQuotientEquiv.toEquiv.subtypeEquiv fun x => by
    constructor
    · rintro ⟨hx0, hx⟩
      exact ⟨deningerEntireHalfPullbackQuotientEquiv.injective.ne hx0,
        (deningerEntireTheta_eigen_equation_halfPullback_iff alpha x).mp hx⟩
    · rintro ⟨hx0, hx⟩
      exact ⟨fun hzero => hx0 (by rw [hzero]; simp),
        (deningerEntireTheta_eigen_equation_halfPullback_iff alpha x).mpr hx⟩

/-- Big-Witt reporter on a scaled completed-Xi theta fibre. -/
def scaledTwoCompletedXiThetaFiberBigWittReporter
    (p : ℕ) (alpha : ℂ)
    (_ : ScaledTwoCompletedXiThetaSpectralFiber alpha) :
    DeningerBigWittRing ℂ :=
  completedXiBigWittPrimeMark p alpha

/-- Big-Witt Frobenius and the scaling-cover cross-fibre equivalence form a naturality square. -/
theorem deningerBigWittFrobeniusTwo_crossFiber_naturality
    (p : ℕ) (alpha : ℂ)
    (x : CompletedXiThetaSpectralFiber alpha) :
    deningerBigWittFrobeniusTwoRingHom
        (completedXiThetaFiberBigWittReporter p alpha x) =
      scaledTwoCompletedXiThetaFiberBigWittReporter p
        ((2 : ℂ) * alpha)
        (completedXiScaledTwoCrossFiberEquiv alpha x) := by
  calc
    deningerBigWittFrobeniusTwoRingHom
        (completedXiThetaFiberBigWittReporter p alpha x) =
        deningerBigWittFrobeniusTwoRingHom
          (completedXiBigWittPrimeMarkOrbit p alpha 0) := by
            rw [completedXiBigWittPrimeMarkOrbit_zero]
            rfl
    _ = completedXiBigWittPrimeMarkOrbit p alpha 1 := by
      simpa using
        deningerBigWittFrobeniusTwo_completedXiPrimeMarkOrbit p alpha 0
    _ = completedXiBigWittPrimeMark p
        (completedXiSpectralDilation (2 ^ (1 : ℕ)) alpha) :=
      completedXiBigWittPrimeMarkOrbit_eq_spectralDilation p alpha 1
    _ = scaledTwoCompletedXiThetaFiberBigWittReporter p
        ((2 : ℂ) * alpha)
        (completedXiScaledTwoCrossFiberEquiv alpha x) := by
      simp [completedXiSpectralDilation,
        scaledTwoCompletedXiThetaFiberBigWittReporter]

/-- Closed cross-fibre capstone: quotient equivalence, spectral transport, and Big-Witt naturality. -/
theorem deningerBigWitt_completedXi_scaledTwo_crossFiberNaturalTransformation :
    Function.Bijective deningerEntireHalfPullbackQuotientEquiv ∧
      (∀ alpha : ℂ,
        Nonempty (CompletedXiThetaSpectralFiber alpha) ↔
          Nonempty
            (ScaledTwoCompletedXiThetaSpectralFiber ((2 : ℂ) * alpha))) ∧
      (∀ p : ℕ, ∀ alpha : ℂ,
        ∀ x : CompletedXiThetaSpectralFiber alpha,
          deningerBigWittFrobeniusTwoRingHom
              (completedXiThetaFiberBigWittReporter p alpha x) =
            scaledTwoCompletedXiThetaFiberBigWittReporter p
              ((2 : ℂ) * alpha)
              (completedXiScaledTwoCrossFiberEquiv alpha x)) := by
  refine ⟨deningerEntireHalfPullbackQuotientEquiv.bijective, ?_,
    deningerBigWittFrobeniusTwo_crossFiber_naturality⟩
  intro alpha
  exact Equiv.nonempty_congr (completedXiScaledTwoCrossFiberEquiv alpha)

end

end RHTower
