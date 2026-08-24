import GaloisForLFunctions.HTGeometry.KoszulCohomology
import GaloisForLFunctions.HTGeometry.SecondOrderConstraintDescent
import GaloisForLFunctions.RHTower.DeningerCalderonWittCotangentNoether
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiHeatCassiniReflectedPhaseSourceJet
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Xi zeros as pure defects of a nodal two-sector constraint

The horizontal grade and vertical phase of a divisor point are independent before completion.
Their mixed neutral source jet is `2 * grade * phase`.  This file packages the proposed
constraint, rather than a flow or a positivity condition: an admissible zero defect must factor
through the nodal Stanley--Reisner ring `ℝ[x,y]/(xy)`.

The two branches have distinct arithmetic meanings.  Trivial zeta zeros occupy the phase-zero
branch.  Since Xi-divisor points have nonzero phase, a nodally pure Xi defect must occupy the
grade-zero branch, which is the critical line.  Thus RH becomes the statement that the complete
zeta divisor has no mixed defects.

Nothing below assumes this superselection law.  The final equivalences expose its exact strength;
the missing theorem is a source-semantic reason that a zeta zero induces the quotient lift.
-/

open Complex Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Polynomial evaluation at the actual horizontal-grade/vertical-phase pair of one Xi zero
copy.  Before imposing the missing-edge relation this is an ordinary two-coordinate point. -/
def xiNodalGradePhasePolynomialEvaluation (q : XiZeroCopy) :
    MvPolynomial (Fin 2) ℝ →+* ℝ :=
  MvPolynomial.eval₂Hom (RingHom.id ℝ)
    ![primeDepthBVWoldXiCenteredRate q.1, (q.1 : ℂ).im]

/-- Local nodal superselection: the grade--phase point annihilates the missing-edge ideal. -/
def XiNodalDefectSuperselected (q : XiZeroCopy) : Prop :=
  nodalNonedgeIdeal ℝ ≤ RingHom.ker (xiNodalGradePhasePolynomialEvaluation q)

/-- Nodal superselection is exactly vanishing of the mixed grade--phase coordinate. -/
theorem xiNodalDefectSuperselected_iff_grade_mul_phase_eq_zero (q : XiZeroCopy) :
    XiNodalDefectSuperselected q ↔
      primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im = 0 := by
  constructor
  · intro h
    have hgenerator :
        MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ∈
          nodalNonedgeIdeal ℝ := by
      rw [nodalNonedgeIdeal]
      exact Ideal.subset_span (by simp)
    have hkernel := RingHom.mem_ker.mp (h hgenerator)
    simpa [xiNodalGradePhasePolynomialEvaluation] using hkernel
  · intro hmixed
    rw [XiNodalDefectSuperselected, nodalNonedgeIdeal, Ideal.span_le]
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    apply RingHom.mem_ker.mpr
    simpa [xiNodalGradePhasePolynomialEvaluation] using hmixed

/-- When local superselection holds, the actual grade--phase evaluation factors through the
nodal Stanley--Reisner quotient. -/
def xiNodalDefectEvaluation (q : XiZeroCopy) (h : XiNodalDefectSuperselected q) :
    NodalStanleyReisnerRing ℝ →+* ℝ :=
  Ideal.Quotient.lift (nodalNonedgeIdeal ℝ)
    (xiNodalGradePhasePolynomialEvaluation q)
    (fun _ hp => RingHom.mem_ker.mp (h hp))

@[simp]
theorem xiNodalDefectEvaluation_X (q : XiZeroCopy)
    (h : XiNodalDefectSuperselected q) :
    xiNodalDefectEvaluation q h nodalStanleyReisnerX =
      primeDepthBVWoldXiCenteredRate q.1 := by
  rw [xiNodalDefectEvaluation, nodalStanleyReisnerX, Ideal.Quotient.lift_mk]
  simp [xiNodalGradePhasePolynomialEvaluation]

@[simp]
theorem xiNodalDefectEvaluation_Y (q : XiZeroCopy)
    (h : XiNodalDefectSuperselected q) :
    xiNodalDefectEvaluation q h nodalStanleyReisnerY = (q.1 : ℂ).im := by
  rw [xiNodalDefectEvaluation, nodalStanleyReisnerY, Ideal.Quotient.lift_mk]
  simp [xiNodalGradePhasePolynomialEvaluation]

/-- The quotient obstruction is the already-constructed mixed neutral source jet. -/
theorem xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero (q : XiZeroCopy) :
    XiNodalDefectSuperselected q ↔ xiReflectedPhaseNeutralMixedJet q = 0 := by
  rw [xiNodalDefectSuperselected_iff_grade_mul_phase_eq_zero,
    xiReflectedPhaseNeutralMixedJet, xiReflectedPhaseLogScaleSecondJet_zero]
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- Xi support never lies on the phase-zero branch, so nodal purity selects the grade-zero
branch exactly. -/
theorem xiNodalDefectSuperselected_iff_re_eq_half (q : XiZeroCopy) :
    XiNodalDefectSuperselected q ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [xiNodalDefectSuperselected_iff_grade_mul_phase_eq_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hgrade | hphase
    · exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mp hgrade
    · exact False.elim (xiSupport_im_ne_zero q.1 hphase)
  · intro hline
    exact mul_eq_zero.mpr <| Or.inl
      ((primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mpr hline)

/-! ## BV/BRST realization of the nodal constraint -/

/-- Square-zero horizontal defect differential. -/
def xiNodalGradeDifferential (q : XiZeroCopy) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, primeDepthBVWoldXiCenteredRate q.1; 0, 0]

/-- Square-zero vertical phase differential. -/
def xiNodalPhaseDifferential (q : XiZeroCopy) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; (q.1 : ℂ).im, 0]

/-- Total two-sector defect differential.  Its square is the mixed interaction, not either
marginal defect. -/
def xiNodalTotalDefectDifferential (q : XiZeroCopy) : Matrix (Fin 2) (Fin 2) ℝ :=
  xiNodalGradeDifferential q + xiNodalPhaseDifferential q

@[simp]
theorem xiNodalGradeDifferential_sq_zero (q : XiZeroCopy) :
    xiNodalGradeDifferential q * xiNodalGradeDifferential q = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xiNodalGradeDifferential, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem xiNodalPhaseDifferential_sq_zero (q : XiZeroCopy) :
    xiNodalPhaseDifferential q * xiNodalPhaseDifferential q = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xiNodalPhaseDifferential, Matrix.mul_apply, Fin.sum_univ_two]

/-- The BV curvature of the total defect differential is the scalar mixed grade--phase
obstruction on both diagonal sectors. -/
theorem xiNodalTotalDefectDifferential_sq (q : XiZeroCopy) :
    xiNodalTotalDefectDifferential q * xiNodalTotalDefectDifferential q =
      (primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xiNodalTotalDefectDifferential, xiNodalGradeDifferential,
      xiNodalPhaseDifferential, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Classical master equation for the combined internal/transverse defect resolution. -/
def XiNodalDefectMasterEquation (q : XiZeroCopy) : Prop :=
  xiNodalTotalDefectDifferential q * xiNodalTotalDefectDifferential q = 0

/-- Individual marginal nilpotence is automatic; total nilpotence is exactly the missing-edge
law. -/
theorem xiNodalDefectMasterEquation_iff_superselected (q : XiZeroCopy) :
    XiNodalDefectMasterEquation q ↔ XiNodalDefectSuperselected q := by
  rw [XiNodalDefectMasterEquation,
    xiNodalDefectSuperselected_iff_grade_mul_phase_eq_zero]
  constructor
  · intro h
    have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
    simpa [xiNodalTotalDefectDifferential, xiNodalGradeDifferential,
      xiNodalPhaseDifferential, Matrix.mul_apply, Fin.sum_univ_two] using h00
  · intro h
    rw [xiNodalTotalDefectDifferential_sq, h]
    simp

/-- The master-equation anomaly is exactly the mixed neutral arithmetic source jet. -/
theorem xiNodalDefectMasterEquation_iff_mixedSourceJet_eq_zero (q : XiZeroCopy) :
    XiNodalDefectMasterEquation q ↔ xiReflectedPhaseNeutralMixedJet q = 0 := by
  rw [xiNodalDefectMasterEquation_iff_superselected,
    xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero]

/-- Global nodal superselection over the multiplicity-exact Xi divisor. -/
def XiNodalDefectSuperselection : Prop :=
  ∀ q : XiZeroCopy, XiNodalDefectSuperselected q

/-- Global constitutive master equation for all multiplicity-exact Xi defects. -/
def XiNodalDefectMasterEquationGlobal : Prop :=
  ∀ q : XiZeroCopy, XiNodalDefectMasterEquation q

/-- The new language has exactly RH strength until its source-semantic factorization law is
proved independently. -/
theorem xiNodalDefectSuperselection_iff_riemannHypothesis :
    XiNodalDefectSuperselection ↔ RiemannHypothesis := by
  constructor
  · intro h
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    let q : XiZeroCopy :=
      ⟨support, ⟨0, xiSupportMultiplicity_pos support⟩⟩
    exact (xiNodalDefectSuperselected_iff_re_eq_half q).mp (h q)
  · intro hRH q
    exact (xiNodalDefectSuperselected_iff_re_eq_half q).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)

/-- Global master-equation form of the same frontier. -/
theorem xiNodalDefectMasterEquationGlobal_iff_riemannHypothesis :
    XiNodalDefectMasterEquationGlobal ↔ RiemannHypothesis := by
  rw [← xiNodalDefectSuperselection_iff_riemannHypothesis]
  apply forall_congr'
  exact xiNodalDefectMasterEquation_iff_superselected

/-! ## Source-level two-cell descent

The all-prime Calderón--Witt complex has a square-zero differential before any Xi zero is chosen.
Its oriented top degree has two independent coordinates: the finite-support center trace and the
Arakelov orientation coordinate.  They give a fixed surjective two-channel observation.

Strict intertwining with the local nodal differential would be unnecessarily strong.  We retain
its first-order anomaly and ask only that this anomaly satisfy the covariant second-order
coherence equation.  The general two-cell descent theorem then transports source nilpotence to
the local master equation.
-/

/-- Complex two-channel carrier read by the local nodal defect. -/
abbrev XiNodalDefectChannel := Fin 2 → ℂ

/-- Complex-linear form of the local grade--phase defect differential. -/
def xiNodalTotalDefectEnd (q : XiZeroCopy) : Module.End ℂ XiNodalDefectChannel where
  toFun v := ![
    (primeDepthBVWoldXiCenteredRate q.1 : ℂ) * v 1,
    ((q.1 : ℂ).im : ℂ) * v 0]
  map_add' v w := by
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [mul_left_comm]

/-- Complex and real master equations have the same mixed grade--phase obstruction. -/
theorem xiNodalTotalDefectEnd_sq_eq_zero_iff (q : XiZeroCopy) :
    (xiNodalTotalDefectEnd q).comp (xiNodalTotalDefectEnd q) = 0 ↔
      XiNodalDefectMasterEquation q := by
  rw [xiNodalDefectMasterEquation_iff_superselected,
    xiNodalDefectSuperselected_iff_grade_mul_phase_eq_zero]
  constructor
  · intro h
    have hv := LinearMap.congr_fun h (![1, 0] : XiNodalDefectChannel)
    have hmixed :
        (primeDepthBVWoldXiCenteredRate q.1 : ℂ) * ((q.1 : ℂ).im : ℂ) = 0 := by
      have hcoord := congrArg (fun v : XiNodalDefectChannel => v 0) hv
      simpa [xiNodalTotalDefectEnd, LinearMap.comp_apply] using hcoord
    exact_mod_cast hmixed
  · intro hmixed
    rcases mul_eq_zero.mp hmixed with hgrade | hphase
    · apply LinearMap.ext
      intro v
      ext i
      fin_cases i <;>
        simp [xiNodalTotalDefectEnd, LinearMap.comp_apply, hgrade]
    · apply LinearMap.ext
      intro v
      ext i
      fin_cases i <;>
        simp [xiNodalTotalDefectEnd, LinearMap.comp_apply, hphase]

/-- Fixed two-channel observation of the actual all-prime oriented arithmetic source. -/
def deningerCalderonWittNodalTopObservation :
    DeningerCalderonWittGlobalOrientedKoszulTotalCarrier →ₗ[ℂ]
      XiNodalDefectChannel where
  toFun x := ![
    deningerCalderonWittAlgebraicGlobalCenterTrace x.2.2.1,
    x.2.2.2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

/-- Center trace and Arakelov orientation are genuinely independent source channels. -/
theorem deningerCalderonWittNodalTopObservation_surjective :
    Function.Surjective deningerCalderonWittNodalTopObservation := by
  intro y
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let z : DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
    deningerCalderonWittGlobalPrimeCenterOrientationSection p (y 0)
  refine ⟨(0, (0, (z, y 1))), ?_⟩
  ext i
  fin_cases i
  · simp [deningerCalderonWittNodalTopObservation, z,
      deningerCalderonWittAlgebraicGlobalCenterTrace_primeSection]
  · simp [deningerCalderonWittNodalTopObservation]

/-- First-order failure of the fixed arithmetic observation to intertwine one local Xi defect. -/
def xiNodalArithmeticDescentAnomaly (q : XiZeroCopy) :
    DeningerCalderonWittGlobalOrientedKoszulTotalCarrier →ₗ[ℂ]
      XiNodalDefectChannel :=
  GaloisForLFunctions.HTGeometry.clockDescentAnomaly
    (K := ℂ)
    (V := DeningerCalderonWittGlobalOrientedKoszulTotalCarrier)
    (O := XiNodalDefectChannel)
    deningerCalderonWittGlobalOrientedKoszulTotalDifferential
    deningerCalderonWittNodalTopObservation
    (xiNodalTotalDefectEnd q)

/-- The first anomaly retains the source boundary trace.  Its two appearances have opposite
signs, reflecting the oriented center graph `(z, -tr z)` rather than an imposed cancellation. -/
theorem xiNodalArithmeticDescentAnomaly_apply (q : XiZeroCopy)
    (x : DeningerCalderonWittGlobalOrientedKoszulTotalCarrier) :
    xiNodalArithmeticDescentAnomaly q x = ![
      (primeDepthBVWoldXiCenteredRate q.1 : ℂ) * x.2.2.2 -
        deningerCalderonWittAlgebraicGlobalCenterTrace
          (deningerCalderonWittGlobalKoszulBoundary x.2.1),
      ((q.1 : ℂ).im : ℂ) *
          deningerCalderonWittAlgebraicGlobalCenterTrace x.2.2.1 +
        deningerCalderonWittAlgebraicGlobalCenterTrace
          (deningerCalderonWittGlobalKoszulBoundary x.2.1)] := by
  ext i
  fin_cases i <;>
    simp [xiNodalArithmeticDescentAnomaly,
      GaloisForLFunctions.HTGeometry.clockDescentAnomaly,
      xiNodalTotalDefectEnd, deningerCalderonWittNodalTopObservation,
      deningerCalderonWittGlobalOrientedKoszulTotalDifferential,
      deningerThreeTermTotalDifferential,
      deningerCalderonWittGlobalOrientedKoszulSourceComplex,
      deningerCalderonWittGlobalOrientedKoszulBoundary,
      deningerCalderonWittGlobalOrientedCenterGraph,
      LinearMap.comp_apply]

/-- RH-bearing local law: the first-order arithmetic descent anomaly is a coherent two-cell.
It need not vanish. -/
def XiNodalArithmeticSecondOrderCoherent (q : XiZeroCopy) : Prop :=
  GaloisForLFunctions.HTGeometry.SecondOrderConstraintDescentCoherent
    (K := ℂ)
    (V := DeningerCalderonWittGlobalOrientedKoszulTotalCarrier)
    (O := XiNodalDefectChannel)
    deningerCalderonWittGlobalOrientedKoszulTotalDifferential
    deningerCalderonWittNodalTopObservation
    (xiNodalTotalDefectEnd q)

/-- Exact cancellation law.  Applying the covariant boundary to the nonzero first anomaly
cancels every internal arithmetic boundary trace and leaves only the mixed grade--phase
curvature acting on the observed top source. -/
theorem xiNodalArithmeticSecondOrderDefect_apply (q : XiZeroCopy)
    (x : DeningerCalderonWittGlobalOrientedKoszulTotalCarrier) :
    GaloisForLFunctions.HTGeometry.secondOrderConstraintDescentDefect
        deningerCalderonWittGlobalOrientedKoszulTotalDifferential
        deningerCalderonWittNodalTopObservation
        (xiNodalTotalDefectEnd q) x =
      ((primeDepthBVWoldXiCenteredRate q.1 : ℂ) * ((q.1 : ℂ).im : ℂ)) •
        deningerCalderonWittNodalTopObservation x := by
  rw [GaloisForLFunctions.HTGeometry.
    secondOrderConstraintDescentDefect_eq_targetCurvature_comp
      (K := ℂ)
      (V := DeningerCalderonWittGlobalOrientedKoszulTotalCarrier)
      (O := XiNodalDefectChannel)
      deningerCalderonWittGlobalOrientedKoszulTotalDifferential
      deningerCalderonWittNodalTopObservation
      (xiNodalTotalDefectEnd q)
      deningerCalderonWittGlobalOrientedKoszulTotalDifferential_sq]
  ext i
  fin_cases i <;>
    simp [xiNodalTotalDefectEnd, deningerCalderonWittNodalTopObservation,
      LinearMap.comp_apply]
  <;> ring

/-- Source square-zero plus two-cell coherence is exactly the local nodal master equation. -/
theorem xiNodalArithmeticSecondOrderCoherent_iff (q : XiZeroCopy) :
    XiNodalArithmeticSecondOrderCoherent q ↔ XiNodalDefectMasterEquation q := by
  rw [XiNodalArithmeticSecondOrderCoherent,
    GaloisForLFunctions.HTGeometry.secondOrderConstraintDescentCoherent_iff_target_sq_zero
      (K := ℂ)
      (V := DeningerCalderonWittGlobalOrientedKoszulTotalCarrier)
      (O := XiNodalDefectChannel)
      deningerCalderonWittGlobalOrientedKoszulTotalDifferential
      deningerCalderonWittNodalTopObservation
      (xiNodalTotalDefectEnd q)
      deningerCalderonWittGlobalOrientedKoszulTotalDifferential_sq
      deningerCalderonWittNodalTopObservation_surjective,
    xiNodalTotalDefectEnd_sq_eq_zero_iff]

/-- Universal provenance-resolved two-cell descent law. -/
def XiNodalArithmeticSecondOrderCoherence : Prop :=
  ∀ q : XiZeroCopy, XiNodalArithmeticSecondOrderCoherent q

/-- Exact frontier: coherent second-order descent of the fixed source constraint is equivalent to
RH.  Unlike strict quotient descent, the first-order comparison anomaly remains visible. -/
theorem xiNodalArithmeticSecondOrderCoherence_iff_riemannHypothesis :
    XiNodalArithmeticSecondOrderCoherence ↔ RiemannHypothesis := by
  rw [← xiNodalDefectMasterEquationGlobal_iff_riemannHypothesis]
  apply forall_congr'
  exact xiNodalArithmeticSecondOrderCoherent_iff

/-- The underlying two-axis equation for an arbitrary complex zeta-zero coordinate. -/
def ZetaZeroNodalDefectPure (rho : ℂ) : Prop :=
  (2 * rho.re - 1) * rho.im = 0

/-- Trivial zeta zeros occupy the phase-zero branch of the node. -/
theorem zetaTrivialZero_nodalDefectPure (n : ℕ) :
    ZetaZeroNodalDefectPure (-(2 * ((n : ℂ) + 1))) := by
  simp [ZetaZeroNodalDefectPure]

/-- **Two-sector divisor reformulation.**  RH says that every zeta zero is a pure defect on one
of two axes: trivial zeros on the real branch and nontrivial zeros on the critical branch. -/
theorem everyZetaZeroNodalDefectPure_iff_riemannHypothesis :
    (∀ rho : ℂ, riemannZeta rho = 0 → ZetaZeroNodalDefectPure rho) ↔
      RiemannHypothesis := by
  constructor
  · intro hpure
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hxi
    have hzeta := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
    have hp := hpure rho hzeta
    have him : rho.im ≠ 0 := by
      let support : XiDivisorSupport :=
        ⟨rho, mem_xi_divisor_support_of_eq_zero hxi⟩
      exact xiSupport_im_ne_zero support
    rw [ZetaZeroNodalDefectPure] at hp
    rcases mul_eq_zero.mp hp with hgrade | hphase
    · linarith
    · exact False.elim (him hphase)
  · intro hRH rho hzeta
    rcases (riemannZeta_eq_zero_iff_xi_or_trivial.mp hzeta) with hxi | ⟨n, rfl⟩
    · rw [ZetaZeroNodalDefectPure,
        (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH rho hxi)]
      norm_num
    · exact zetaTrivialZero_nodalDefectPure n

end

end RHTower
