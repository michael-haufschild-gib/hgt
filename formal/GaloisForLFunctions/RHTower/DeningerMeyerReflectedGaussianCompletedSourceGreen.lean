import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianGreenRangeWall

/-!
# Completed source Green primitive for the reflected Meyer Gaussian horizon

The compact-source Green range is exactly the finite Xi-jet subspace and therefore misses the
reflected-Gaussian horizon vector.  The source Gelfand triple already supplies the forced nonlocal
completion: its Hilbert middle is the square-summable Xi-jet carrier, and finite source jets are
dense in it.

This module extends finite oriented Green reflection to a linear isometric automorphism of that
source Hilbert middle.  The extension squares to minus the identity, is surjective, agrees with the
compact-source Green map on its dense image, and is uniquely determined by its finite-jet action.
It therefore gives an explicit completed source primitive of the reflected-Gaussian admitted
residue and transports that primitive to the actual incidence and resolved provenance classes.

This closes the functional-analytic completion wall.  It does not identify this Hilbert-completed
source with the independent adaptive prime-normal source range; that arithmetic range intertwiner
and its Hermitian Gram domination remain open.
-/

open Complex Function Set Topology

namespace RHTower

noncomputable section

/-- Isometric identification of the source-jet Hilbert middle with the completed Xi carrier. -/
def deningerArithmeticSourceJetHilbertEquivCompleted :
    DeningerArithmeticJetHilbert ≃ₗᵢ[ℂ] XiDivisorL2 where
  toLinearEquiv := deningerArithmeticGradedHilbertEquivSourceJets.symm
  norm_map' _ := rfl

/-- Finite source jets inserted into the completed source Hilbert middle. -/
def deningerArithmeticSourceJetTestToCompleted :
    DeningerArithmeticJetTest →ₗ[ℂ] XiDivisorL2 :=
  deningerArithmeticSourceJetHilbertEquivCompleted.toLinearMap.comp
    deningerArithmeticJetTestToHilbert

@[simp]
theorem deningerArithmeticSourceJetTestToCompleted_apply
    (a : DeningerArithmeticJetTest) (q : XiZeroCopy) :
    deningerArithmeticSourceJetTestToCompleted a q = a q := by
  exact deningerArithmeticJetTestToHilbert_apply a q

/-- The finite compact-source jets are dense in the nonlocal source Hilbert completion. -/
theorem deningerArithmeticSourceJetTestToCompleted_dense :
    DenseRange deningerArithmeticSourceJetTestToCompleted := by
  have hcomp :
      DenseRange
        (deningerArithmeticSourceJetHilbertEquivCompleted ∘
          deningerArithmeticJetTestToHilbert) :=
    DenseRange.comp
      deningerArithmeticSourceJetHilbertEquivCompleted.surjective.denseRange
      deningerArithmeticJetTestToHilbert_dense
      deningerArithmeticSourceJetHilbertEquivCompleted.continuous
  simpa only [deningerArithmeticSourceJetTestToCompleted,
    Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv] using hcomp

/-- Isometric completed source Green reflection.  The two conjugate-linear source operations,
Riesz conjugation and odd Hodge reflection, compose to this complex-linear operator. -/
def deningerArithmeticCompletedSourceGreenIsometry :
    XiDivisorL2 →ₗᵢ[ℂ] XiDivisorL2 where
  toFun a := -deningerArithmeticOrientedHodgeLp (star a)
  map_add' a b := by
    ext q
    simp [deningerArithmeticOrientedHodgeLp_apply]
    ring
  map_smul' c a := by
    ext q
    rw [lp.coeFn_smul, Pi.smul_apply]
    simp only [smul_eq_mul]
    change
      -(-deningerArithmeticFEOrientation q *
          (starRingEnd ℂ) ((star (c • a)) (xiZeroCopyReflectEquiv q))) =
        c *
          -(-deningerArithmeticFEOrientation q *
            (starRingEnd ℂ) ((star a) (xiZeroCopyReflectEquiv q)))
    simp
    ring
  norm_map' a := by
    change ‖-deningerArithmeticOrientedHodgeLp (star a)‖ = ‖a‖
    rw [norm_neg, norm_deningerArithmeticOrientedHodgeLp, norm_star]

/-- Continuous completed Green operator on the source Hilbert middle. -/
def deningerArithmeticCompletedSourceGreen :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  deningerArithmeticCompletedSourceGreenIsometry.toContinuousLinearMap

@[simp]
theorem deningerArithmeticCompletedSourceGreen_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerArithmeticCompletedSourceGreen a q =
      deningerArithmeticFEOrientation q * a (xiZeroCopyReflectEquiv q) := by
  change
    -(-deningerArithmeticFEOrientation q *
      (starRingEnd ℂ) ((star a) (xiZeroCopyReflectEquiv q))) = _
  simp

/-- Completed oriented Green reflection retains the finite odd square law. -/
theorem deningerArithmeticCompletedSourceGreen_sq
    (a : XiDivisorL2) :
    deningerArithmeticCompletedSourceGreen
        (deningerArithmeticCompletedSourceGreen a) = -a := by
  ext q
  rw [deningerArithmeticCompletedSourceGreen_apply,
    deningerArithmeticCompletedSourceGreen_apply,
    xiZeroCopyReflectEquiv_apply_apply,
    deningerArithmeticFEOrientation_reflect]
  have heps := deningerArithmeticFEOrientation_sq q
  change deningerArithmeticFEOrientation q *
      (-deningerArithmeticFEOrientation q * a q) = -a q
  linear_combination -a q * heps

/-- Every completed Xi vector has an explicit completed source Green primitive. -/
theorem deningerArithmeticCompletedSourceGreen_surjective :
    Function.Surjective deningerArithmeticCompletedSourceGreen := by
  intro y
  refine ⟨-deningerArithmeticCompletedSourceGreen y, ?_⟩
  rw [map_neg, deningerArithmeticCompletedSourceGreen_sq, neg_neg]

/-- The completed operator is exactly oriented Green reflection on every finite source jet. -/
theorem deningerArithmeticCompletedSourceGreen_finite
    (a : DeningerArithmeticJetTest) :
    deningerArithmeticCompletedSourceGreen
        (deningerArithmeticSourceJetTestToCompleted a) =
      deningerArithmeticSourceJetTestToCompleted
        (deningerArithmeticOrientedGreenJetTest a) := by
  ext q
  rw [deningerArithmeticCompletedSourceGreen_apply,
    deningerArithmeticSourceJetTestToCompleted_apply,
    deningerArithmeticSourceJetTestToCompleted_apply,
    deningerArithmeticOrientedGreenJetTest_apply]

/-- Density makes the completed source Green extension unique. -/
theorem deningerArithmeticCompletedSourceGreen_unique
    (T : XiDivisorL2 →L[ℂ] XiDivisorL2)
    (hT : ∀ a : DeningerArithmeticJetTest,
      T (deningerArithmeticSourceJetTestToCompleted a) =
        deningerArithmeticSourceJetTestToCompleted
          (deningerArithmeticOrientedGreenJetTest a)) :
    T = deningerArithmeticCompletedSourceGreen := by
  apply DFunLike.coe_injective
  refine deningerArithmeticSourceJetTestToCompleted_dense.equalizer
    T.continuous deningerArithmeticCompletedSourceGreen.continuous ?_
  funext a
  change T (deningerArithmeticSourceJetTestToCompleted a) =
    deningerArithmeticCompletedSourceGreen
      (deningerArithmeticSourceJetTestToCompleted a)
  rw [hT a, deningerArithmeticCompletedSourceGreen_finite]

/-- On the embedded compact dual, the completed operator is the original source Green map. -/
theorem deningerArithmeticCompletedSourceGreen_extends_compact
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerArithmeticCompletedSourceGreen
        (star (deningerArithmeticJetCompactToHilbert ell)) =
      deningerArithmeticSourceGreen ell := by
  rw [deningerArithmeticSourceGreen_apply]
  change
    -deningerArithmeticOrientedHodgeLp
        (star (star (deningerArithmeticJetCompactToHilbert ell))) =
      -deningerArithmeticOrientedHodgeLp
        (deningerArithmeticJetCompactToHilbert ell)
  rw [star_star]

namespace DeningerMeyerGaussianGreen

/-- Explicit nonlocal source primitive of the reflected-Gaussian admitted residue. -/
def reflectedGaussianHorizonCompletedGreenPrimitive : XiDivisorL2 :=
  -deningerArithmeticCompletedSourceGreen
    reflectedGaussianHorizonAdmittedResidue

@[simp]
theorem reflectedGaussianHorizonCompletedGreenPrimitive_apply
    (q : XiZeroCopy) :
    reflectedGaussianHorizonCompletedGreenPrimitive q =
      -deningerArithmeticFEOrientation q *
        reflectedGaussianHorizonGrade q := by
  change
    -(deningerArithmeticCompletedSourceGreen
      reflectedGaussianHorizonAdmittedResidue q) = _
  rw [deningerArithmeticCompletedSourceGreen_apply,
    reflectedGaussianHorizonAdmittedResidue_apply,
    reflectedGaussianHorizonGrade_reflect]
  ring

/-- The completed source Green operator sends the explicit primitive to the admitted residue. -/
theorem reflectedGaussianHorizonCompletedGreenPrimitive_green :
    deningerArithmeticCompletedSourceGreen
        reflectedGaussianHorizonCompletedGreenPrimitive =
      reflectedGaussianHorizonAdmittedResidue := by
  rw [reflectedGaussianHorizonCompletedGreenPrimitive, map_neg,
    deningerArithmeticCompletedSourceGreen_sq, neg_neg]

/-- The completed reflected-Gaussian Green primitive is forced uniquely. -/
theorem deningerArithmeticCompletedSourceGreen_eq_admittedResidue_iff
    (u : XiDivisorL2) :
    deningerArithmeticCompletedSourceGreen u =
        reflectedGaussianHorizonAdmittedResidue ↔
      u = reflectedGaussianHorizonCompletedGreenPrimitive := by
  constructor
  · intro hu
    apply deningerArithmeticCompletedSourceGreenIsometry.injective
    change deningerArithmeticCompletedSourceGreen u =
      deningerArithmeticCompletedSourceGreen
        reflectedGaussianHorizonCompletedGreenPrimitive
    rw [hu, reflectedGaussianHorizonCompletedGreenPrimitive_green]
  · rintro rfl
    exact reflectedGaussianHorizonCompletedGreenPrimitive_green

theorem reflectedGaussianHorizonCompletedGreenPrimitive_ne_zero :
    reflectedGaussianHorizonCompletedGreenPrimitive ≠ 0 := by
  intro hzero
  have hgreen :=
    congrArg deningerArithmeticCompletedSourceGreen hzero
  rw [reflectedGaussianHorizonCompletedGreenPrimitive_green,
    map_zero] at hgreen
  exact reflectedGaussianHorizonAdmittedResidue_ne_zero
    (Classical.arbitrary XiZeroCopy) hgreen

/-- Completed Green transport of the primitive is the actual admitted incidence vector. -/
theorem reflectedGaussianHorizonCompletedGreenPrimitive_incidence
    (p q : Nat.Primes) (hpq : p ≠ q) :
    deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq
        (deningerArithmeticCompletedSourceGreen
          reflectedGaussianHorizonCompletedGreenPrimitive) =
      reflectedGaussianHorizonAdmittedIncidence p q hpq := by
  rw [reflectedGaussianHorizonCompletedGreenPrimitive_green]
  rfl

/-- Resolved provenance receives the actual completed source Green primitive. -/
theorem reflectedGaussianHorizonCompletedGreenPrimitive_resolved
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    hellingerGammaResolvedProvenanceQuotientSource hpq a
        (deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq
          (deningerArithmeticCompletedSourceGreen
            reflectedGaussianHorizonCompletedGreenPrimitive)) =
      reflectedGaussianHorizonAdmittedResolvedClass p q hpq a := by
  rw [reflectedGaussianHorizonCompletedGreenPrimitive_incidence]
  rfl

end DeningerMeyerGaussianGreen

end

end RHTower
