import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThirdOrderCokernelThresholdRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEThirdOrderFieldRedefinition

/-!
# Field_cCMRationalContinuousTraceNormFieldCyclicContinuity_cCMRationalStrongCyclicRealContinuity-redefinition orbit and minimax classification of the third-order source split

Quadratic perturbation-coordinate changes redistribute two complex projection amplitudes from the
stationary and second-harmonic cascades into the direct third variation.  The induced affine action
is `(a,b,c) ↦ (a-δ,b-ε,c+δ+ε)`, preserving only the total projection.  Every two triples with equal
total lie in the same orbit, with unique transfer coordinates.

Consequently individual channel values and HC46 equipartition are not coordinate invariants.  The
positive invariant survivor is minimax: every triple with total `-target` has peak channel norm at
least `‖target‖/3`, and equipartition is the unique representative attaining this value.  The actual
Einstein field-redefinition formulas realize the affine transfer law exactly.  A closed scalar
countermodel changes the direct projection while preserving total projection.

`[NEW] [FIELD REDEFINITION] [AFFINE ORBIT] [UNIQUE MINIMAX] [SOURCE NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Three named resonant projections in one perturbation coordinate. -/
@[ext] structure D4ThirdOrderProjectionTriple where
  orthogonal : ℂ
  secondHarmonic : ℂ
  direct : ℂ
deriving DecidableEq

/-- Coordinate-invariant aggregate projection. -/
def D4ThirdOrderProjectionTriple.total (t : D4ThirdOrderProjectionTriple) : ℂ :=
  t.orthogonal + t.secondHarmonic + t.direct

/-- Affine transfer of two cascade amplitudes into the direct vertex. -/
def D4ThirdOrderProjectionTriple.redistribute
    (delta epsilon : ℂ) (t : D4ThirdOrderProjectionTriple) :
    D4ThirdOrderProjectionTriple where
  orthogonal := t.orthogonal - delta
  secondHarmonic := t.secondHarmonic - epsilon
  direct := t.direct + delta + epsilon

/-- Largest projected channel norm in one perturbation coordinate. -/
def D4ThirdOrderProjectionTriple.peak (t : D4ThirdOrderProjectionTriple) : ℝ :=
  max ‖t.orthogonal‖ (max ‖t.secondHarmonic‖ ‖t.direct‖)

/-- Aligned equal-third representative of a negative target total. -/
def d4ThirdOrderProjectionEquipartition (target : ℂ) :
    D4ThirdOrderProjectionTriple where
  orthogonal := -target / 3
  secondHarmonic := -target / 3
  direct := -target / 3

/-- Affine redistribution preserves aggregate projection exactly. -/
theorem d4ThirdOrderProjectionRedistribution_total
    (delta epsilon : ℂ) (t : D4ThirdOrderProjectionTriple) :
    (t.redistribute delta epsilon).total = t.total := by
  simp [D4ThirdOrderProjectionTriple.redistribute,
    D4ThirdOrderProjectionTriple.total]
  ring

/-- Two projection triples lie in the same redistribution orbit exactly when their totals agree;
the transfer coordinates are unique. -/
theorem d4ThirdOrderProjectionRedistribution_eq_iff_total_eq
    (x y : D4ThirdOrderProjectionTriple) :
    x.total = y.total ↔
      ∃! shifts : ℂ × ℂ, x.redistribute shifts.1 shifts.2 = y := by
  constructor
  · intro htotal
    let shifts : ℂ × ℂ :=
      (x.orthogonal - y.orthogonal, x.secondHarmonic - y.secondHarmonic)
    refine ⟨shifts, ?_, ?_⟩
    · apply D4ThirdOrderProjectionTriple.ext
      · simp [shifts, D4ThirdOrderProjectionTriple.redistribute]
      · simp [shifts, D4ThirdOrderProjectionTriple.redistribute]
      · simp [shifts, D4ThirdOrderProjectionTriple.redistribute,
          D4ThirdOrderProjectionTriple.total] at htotal ⊢
        linear_combination htotal
    · intro other hother
      have hOrthogonal := congrArg D4ThirdOrderProjectionTriple.orthogonal hother
      have hSecond := congrArg D4ThirdOrderProjectionTriple.secondHarmonic hother
      apply Prod.ext
      · dsimp [shifts, D4ThirdOrderProjectionTriple.redistribute] at hOrthogonal ⊢
        linear_combination -hOrthogonal
      · dsimp [shifts, D4ThirdOrderProjectionTriple.redistribute] at hSecond ⊢
        linear_combination -hSecond
  · rintro ⟨shifts, hshifts, _⟩
    rw [← hshifts]
    exact (d4ThirdOrderProjectionRedistribution_total shifts.1 shifts.2 x).symm

theorem d4ThirdOrderProjectionEquipartition_total (target : ℂ) :
    (d4ThirdOrderProjectionEquipartition target).total = -target := by
  simp [d4ThirdOrderProjectionEquipartition, D4ThirdOrderProjectionTriple.total]
  ring

/-- Every representative has peak channel norm at least one third of target norm. -/
theorem d4ThirdOrderProjectionPeak_ge_oneThird
    (t : D4ThirdOrderProjectionTriple) (target : ℂ)
    (htotal : t.total = -target) :
    ‖target‖ / 3 ≤ t.peak := by
  have hsum : t.orthogonal + t.secondHarmonic + t.direct = -target := htotal
  rcases d4ThreeChannelResonantNormPigeonhole
      t.orthogonal t.secondHarmonic t.direct target hsum with h | h | h
  · exact h.trans (le_max_left _ _)
  · exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Equipartition is the unique representative attaining the sharp one-third peak. -/
theorem d4ThirdOrderProjectionPeak_eq_oneThird_iff
    (t : D4ThirdOrderProjectionTriple) (target : ℂ)
    (htotal : t.total = -target) :
    t.peak = ‖target‖ / 3 ↔ t = d4ThirdOrderProjectionEquipartition target := by
  constructor
  · intro hpeak
    have hOrthogonal : ‖t.orthogonal‖ ≤ ‖target‖ / 3 := by
      rw [← hpeak]
      exact le_max_left _ _
    have hSecond : ‖t.secondHarmonic‖ ≤ ‖target‖ / 3 := by
      rw [← hpeak]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hDirect : ‖t.direct‖ ≤ ‖target‖ / 3 := by
      rw [← hpeak]
      exact (le_max_right _ _).trans (le_max_right _ _)
    have hrigid := d4ThreeChannelResonantNormThresholdRigidity
      t.orthogonal t.secondHarmonic t.direct target htotal
        hOrthogonal hSecond hDirect
    rcases hrigid with ⟨hOrthogonalEq, hSecondEq, hDirectEq⟩
    ext <;> simp [d4ThirdOrderProjectionEquipartition, hOrthogonalEq,
      hSecondEq, hDirectEq]
  · rintro rfl
    simp [D4ThirdOrderProjectionTriple.peak, d4ThirdOrderProjectionEquipartition]

/-- Every equal-total orbit contains one unique minimax equipartition representative. -/
theorem d4ThirdOrderProjectionOrbit_unique_minimax
    (t : D4ThirdOrderProjectionTriple) (target : ℂ)
    (htotal : t.total = -target) :
    ∃! shifts : ℂ × ℂ,
      t.redistribute shifts.1 shifts.2 = d4ThirdOrderProjectionEquipartition target := by
  exact (d4ThirdOrderProjectionRedistribution_eq_iff_total_eq t
    (d4ThirdOrderProjectionEquipartition target)).mp
      (htotal.trans (d4ThirdOrderProjectionEquipartition_total target).symm)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Projection triple in the original physical quadratic coefficients. -/
def d4EinsteinOriginalPhysicalProjectionTriple
    (ell : V →ₗ[ℂ] ℂ) (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus vPlusPlus vPlusMinus : V) : D4ThirdOrderProjectionTriple where
  orthogonal := ell (B hPlus
    (d4EinsteinQuadraticFieldRedefinedPhysicalPlusMinus
      K hPlus hMinus vPlusMinus))
  secondHarmonic := ell (B hMinus
    (d4EinsteinQuadraticFieldRedefinedPhysicalPlusPlus K hPlus vPlusPlus))
  direct := ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus)

/-- Projection triple after a quadratic perturbation-coordinate change. -/
def d4EinsteinRedefinedProjectionTriple
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus vPlusPlus vPlusMinus : V) : D4ThirdOrderProjectionTriple where
  orthogonal := ell (d4EinsteinQuadraticFieldRedefinedHessianValue
    L B K hPlus vPlusMinus)
  secondHarmonic := ell (d4EinsteinQuadraticFieldRedefinedHessianValue
    L B K hMinus vPlusPlus)
  direct := ell (d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus
    B C K hPlus hMinus)

def d4EinsteinFieldRedefinitionOrthogonalTransfer
    (ell : V →ₗ[ℂ] ℂ) (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus : V) : ℂ :=
  ell (B hPlus (K hPlus hMinus))

def d4EinsteinFieldRedefinitionSecondHarmonicTransfer
    (ell : V →ₗ[ℂ] ℂ) (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus : V) : ℂ :=
  ell ((1 / 2 : ℂ) • B hMinus (K hPlus hPlus))

/-- Actual Einstein field redefinition realizes the two-transfer affine redistribution law. -/
theorem d4EinsteinQuadraticFieldRedefinition_projectionTriple_eq_redistribute
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus vPlusPlus vPlusMinus : V)
    (hK : ∀ x y, K x y = K y x)
    (hleft : ∀ v, ell (L v) = 0) :
    d4EinsteinRedefinedProjectionTriple L ell B K C
        hPlus hMinus vPlusPlus vPlusMinus =
      (d4EinsteinOriginalPhysicalProjectionTriple ell B K C
        hPlus hMinus vPlusPlus vPlusMinus).redistribute
          (d4EinsteinFieldRedefinitionOrthogonalTransfer ell B K hPlus hMinus)
          (d4EinsteinFieldRedefinitionSecondHarmonicTransfer ell B K hPlus hMinus) := by
  apply D4ThirdOrderProjectionTriple.ext
  · simp [d4EinsteinRedefinedProjectionTriple,
      d4EinsteinOriginalPhysicalProjectionTriple,
      d4EinsteinFieldRedefinitionOrthogonalTransfer,
      D4ThirdOrderProjectionTriple.redistribute,
      d4EinsteinQuadraticFieldRedefinedHessianValue,
      d4EinsteinQuadraticFieldRedefinedPhysicalPlusMinus,
      map_add, hleft]
  · simp [d4EinsteinRedefinedProjectionTriple,
      d4EinsteinOriginalPhysicalProjectionTriple,
      d4EinsteinFieldRedefinitionSecondHarmonicTransfer,
      D4ThirdOrderProjectionTriple.redistribute,
      d4EinsteinQuadraticFieldRedefinedHessianValue,
      d4EinsteinQuadraticFieldRedefinedPhysicalPlusPlus,
      map_add, map_smul, hleft]
  · rw [d4EinsteinRedefinedProjectionTriple,
      d4EinsteinOriginalPhysicalProjectionTriple,
      D4ThirdOrderProjectionTriple.redistribute]
    simp only [d4EinsteinFieldRedefinitionOrthogonalTransfer,
      d4EinsteinFieldRedefinitionSecondHarmonicTransfer]
    rw [d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus_eq
      B C K hPlus hMinus hK]
    simp only [map_add, map_smul]

/-- Total projection is invariant under the actual Einstein redistribution. -/
theorem d4EinsteinQuadraticFieldRedefinition_projectionTriple_total_invariant
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus vPlusPlus vPlusMinus : V)
    (hK : ∀ x y, K x y = K y x)
    (hleft : ∀ v, ell (L v) = 0) :
    (d4EinsteinRedefinedProjectionTriple L ell B K C
        hPlus hMinus vPlusPlus vPlusMinus).total =
      (d4EinsteinOriginalPhysicalProjectionTriple ell B K C
        hPlus hMinus vPlusPlus vPlusMinus).total := by
  rw [d4EinsteinQuadraticFieldRedefinition_projectionTriple_eq_redistribute
    L ell B K C hPlus hMinus vPlusPlus vPlusMinus hK hleft]
  exact d4ThirdOrderProjectionRedistribution_total _ _ _

/-- Closed countermodel: a quadratic field redefinition changes the direct projection from zero to
`3/2` while the full three-channel projection remains invariant. -/
theorem d4EinsteinQuadraticFieldRedefinition_scalar_directChanges_totalInvariant :
    (d4EinsteinRedefinedProjectionTriple
        (0 : ℂ →ₗ[ℂ] ℂ) (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (LinearMap.lsmul ℂ ℂ) (LinearMap.lsmul ℂ ℂ)
        (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) 1 1 1 1).direct ≠
      (d4EinsteinOriginalPhysicalProjectionTriple
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (LinearMap.lsmul ℂ ℂ) (LinearMap.lsmul ℂ ℂ)
        (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) 1 1 1 1).direct ∧
    (d4EinsteinRedefinedProjectionTriple
        (0 : ℂ →ₗ[ℂ] ℂ) (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (LinearMap.lsmul ℂ ℂ) (LinearMap.lsmul ℂ ℂ)
        (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) 1 1 1 1).total =
      (d4EinsteinOriginalPhysicalProjectionTriple
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (LinearMap.lsmul ℂ ℂ) (LinearMap.lsmul ℂ ℂ)
        (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) 1 1 1 1).total := by
  constructor
  · change
      d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus
          (LinearMap.lsmul ℂ ℂ)
          (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ)
          (LinearMap.lsmul ℂ ℂ) 1 1 ≠
        d4EinsteinDirectThirdVariationPlusPlusMinus
          (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) 1 1
    rw [d4EinsteinQuadraticFieldRedefinition_scalarRedefinedDirect_eq_threeHalves,
      d4EinsteinQuadraticFieldRedefinition_scalarOriginalDirect_eq_zero]
    norm_num
  · apply d4EinsteinQuadraticFieldRedefinition_projectionTriple_total_invariant
    · intro x y
      change x * y = y * x
      ring
    · intro v
      simp

end

end RHTower
