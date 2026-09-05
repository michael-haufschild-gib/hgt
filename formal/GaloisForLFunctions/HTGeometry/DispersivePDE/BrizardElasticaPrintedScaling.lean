import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScalingClosure
import Mathlib.Tactic

/-!
# Audit of the paper's printed inverse-amplitude scaling

The prose before equation (26) of arXiv:2607.21750 prints the active-looking expression
`a⁻¹ u(a²t, ax)`.  For cubic NLS, the standard active symmetry is `a u(a²t, ax)`, as formalized in
`BrizardElasticaScaling`.  This module constructs the printed inverse-amplitude jet literally and
derives its exact residual `2(a⁻³-a)|u|²u`.  A closed corpus plane-wave counterexample at `a=2`
shows that the printed expression is not an arbitrary-scale active symmetry.  It remains compatible
with a passive coordinate convention after inverse relabelling.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

/-- Literal certified jet for the printed expression `a⁻¹u(a²t,ax)`. -/
noncomputable def printedInverseScaleJet (a : ℝˣ)
    (J : ComplexEvolutionJet2) : ComplexEvolutionJet2 where
  u := fun t x => ((↑(a⁻¹) : ℝ) : ℂ) * J.u ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)
  ut := fun t x => ((a : ℝ) : ℂ) * J.ut ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)
  ux := fun t x => J.ux ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)
  uxx := fun t x => ((a : ℝ) : ℂ) * J.uxx ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)
  hasDerivAt_time := by
    intro t x
    have hinner : HasDerivAt (fun s : ℝ => (a : ℝ) ^ 2 * s) ((a : ℝ) ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul ((a : ℝ) ^ 2)
    have h := (J.hasDerivAt_time ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)).scomp t hinner
      |>.const_mul (((↑(a⁻¹) : ℝ) : ℂ))
    apply h.congr_deriv
    simp only [Complex.real_smul]
    push_cast
    field_simp [a.ne_zero]
  hasDerivAt_space := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => (a : ℝ) * y) (a : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (a : ℝ)
    have h := (J.hasDerivAt_space ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)).scomp x hinner
      |>.const_mul (((↑(a⁻¹) : ℝ) : ℂ))
    apply h.congr_deriv
    simp only [Complex.real_smul]
    push_cast
    field_simp [a.ne_zero]
  hasDerivAt_space_one := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => (a : ℝ) * y) (a : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (a : ℝ)
    have h := (J.hasDerivAt_space_one ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)).scomp x hinner
    apply h.congr_deriv
    simp only [Complex.real_smul]

theorem norm_printedInverseScaleJet_sq (a : ℝˣ) (J : ComplexEvolutionJet2) (t x : ℝ) :
    ‖(printedInverseScaleJet a J).u t x‖ ^ 2 =
      ((a : ℝ)⁻¹) ^ 2 * ‖J.u ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)‖ ^ 2 := by
  simp only [printedInverseScaleJet]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  simp

noncomputable def focusingResidual (J : ComplexEvolutionJet2) (t x : ℝ) : ℂ :=
  Complex.I * J.ut t x + J.uxx t x +
    ((2 * ‖J.u t x‖ ^ 2 : ℝ) : ℂ) * J.u t x

/-- Exact defect in the literal printed active scaling, for every certified focusing solution. -/
theorem printedInverseScale_residual (a : ℝˣ) (S : FocusingSolutionJet) (t x : ℝ) :
    focusingResidual (printedInverseScaleJet a S) t x =
      2 * ((((a : ℝ) : ℂ)⁻¹ ^ 3 - ((a : ℝ) : ℂ))) *
        (‖S.val.u ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)‖ ^ 2 : ℂ) *
          S.val.u ((a : ℝ) ^ 2 * t) ((a : ℝ) * x) := by
  have h := S.property ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)
  have hnorm :
      ‖((↑(a⁻¹) : ℝ) : ℂ) * S.val.u ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)‖ ^ 2 =
        ((a : ℝ)⁻¹) ^ 2 *
          ‖S.val.u ((a : ℝ) ^ 2 * t) ((a : ℝ) * x)‖ ^ 2 := by
    simpa only [printedInverseScaleJet] using
      norm_printedInverseScaleJet_sq a S.val t x
  rw [focusingResidual]
  simp only [printedInverseScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  field_simp [a.ne_zero] at h ⊢
  linear_combination (a : ℂ) ^ 4 * h

noncomputable def realTwoUnit : ℝˣ := Units.mk0 2 (by norm_num)

noncomputable def corpusPlaneSolution : FocusingSolutionJet :=
  ⟨nlsPlaneWaveJet, nlsPlaneWave_solves⟩

/-- Closed corpus counterexample to the literal arbitrary-scale active interpretation. -/
theorem printedInverseScale_two_plane_not_solves :
    ¬ SolvesFocusingNLS (printedInverseScaleJet realTwoUnit nlsPlaneWaveJet) := by
  intro h
  have hzero := h 0 0
  have hres := printedInverseScale_residual realTwoUnit corpusPlaneSolution 0 0
  simp only [corpusPlaneSolution] at hres
  rw [focusingResidual] at hres
  rw [hzero] at hres
  norm_num [realTwoUnit, corpusPlaneSolution, nlsPlaneWaveJet, nlsPlaneWave,
    brightPhase, staggerPhase] at hres

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
