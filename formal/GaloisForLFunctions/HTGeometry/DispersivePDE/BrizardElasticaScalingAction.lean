import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScalingClosure
import Mathlib.Tactic

/-!
# Full certified-jet scaling action

The scaling law preceding equation (26) of arXiv:2607.21750 was already proved on solutions and on
field values.  This module upgrades identity, composition, and zero-scale laws to equality of whole
certified jets.  It therefore supplies actual multiplicative actions on each bundled NLS solution
space, not only pointwise field equations.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Certified zero complex jet. -/
noncomputable def zeroComplexEvolutionJet2 : ComplexEvolutionJet2 where
  u := fun _ _ => 0
  ut := fun _ _ => 0
  ux := fun _ _ => 0
  uxx := fun _ _ => 0
  hasDerivAt_time := by
    intro t x
    exact hasDerivAt_const t (0 : ℂ)
  hasDerivAt_space := by
    intro t x
    exact hasDerivAt_const x (0 : ℂ)
  hasDerivAt_space_one := by
    intro t x
    exact hasDerivAt_const x (0 : ℂ)

theorem zeroComplexEvolutionJet2_solvesNLS (D : ℝ) :
    SolvesNLS D zeroComplexEvolutionJet2 := by
  intro t x
  simp [zeroComplexEvolutionJet2]

theorem zeroComplexEvolutionJet2_solvesFocusing :
    SolvesFocusingNLS zeroComplexEvolutionJet2 := by
  intro t x
  simp [zeroComplexEvolutionJet2]

theorem zeroComplexEvolutionJet2_solvesDefocusing :
    SolvesDefocusingNLS zeroComplexEvolutionJet2 := by
  intro t x
  simp [zeroComplexEvolutionJet2]

/-- Scale one is identity on every jet component and certificate. -/
theorem nlsScaleJet_one_full (J : ComplexEvolutionJet2) : nlsScaleJet 1 J = J := by
  cases J
  simp only [nlsScaleJet, ComplexEvolutionJet2.mk.injEq]
  constructor
  · funext t x
    simp
  constructor
  · funext t x
    simp
  constructor <;> funext t x <;> simp

/-- Scaling composition holds as equality of complete certified jets. -/
theorem nlsScaleJet_mul_full (a b : ℝ) (J : ComplexEvolutionJet2) :
    nlsScaleJet a (nlsScaleJet b J) = nlsScaleJet (a * b) J := by
  simp only [nlsScaleJet, ComplexEvolutionJet2.mk.injEq]
  have ht (t : ℝ) : b ^ (2 : ℕ) * (a ^ (2 : ℕ) * t) = (a * b) ^ (2 : ℕ) * t := by ring
  have hx (x : ℝ) : b * (a * x) = (a * b) * x := by ring
  constructor
  · funext t x
    rw [ht, hx]
    push_cast
    ring
  constructor
  · funext t x
    rw [ht, hx]
    push_cast
    ring
  constructor
  · funext t x
    rw [ht, hx]
    push_cast
    ring
  · funext t x
    rw [ht, hx]
    push_cast
    ring

/-- Scale zero collapses every jet to the certified zero jet. -/
theorem nlsScaleJet_zero_full (J : ComplexEvolutionJet2) :
    nlsScaleJet 0 J = zeroComplexEvolutionJet2 := by
  cases J
  simp only [nlsScaleJet, zeroComplexEvolutionJet2, ComplexEvolutionJet2.mk.injEq]
  constructor
  · funext t x
    simp
  constructor
  · funext t x
    simp
  constructor <;> funext t x <;> simp

noncomputable def zeroBrizardSolution (D : ℝ) : BrizardSolutionJet D :=
  ⟨zeroComplexEvolutionJet2, zeroComplexEvolutionJet2_solvesNLS D⟩

noncomputable def zeroFocusingSolution : FocusingSolutionJet :=
  ⟨zeroComplexEvolutionJet2, zeroComplexEvolutionJet2_solvesFocusing⟩

noncomputable def zeroDefocusingSolution : DefocusingSolutionJet :=
  ⟨zeroComplexEvolutionJet2, zeroComplexEvolutionJet2_solvesDefocusing⟩

theorem scaleBrizardSolution_one (D : ℝ) (S : BrizardSolutionJet D) :
    scaleBrizardSolution D 1 S = S := by
  apply Subtype.ext
  exact nlsScaleJet_one_full S.val

theorem scaleBrizardSolution_mul (D a b : ℝ) (S : BrizardSolutionJet D) :
    scaleBrizardSolution D a (scaleBrizardSolution D b S) =
      scaleBrizardSolution D (a * b) S := by
  apply Subtype.ext
  exact nlsScaleJet_mul_full a b S.val

theorem scaleBrizardSolution_zero (D : ℝ) (S : BrizardSolutionJet D) :
    scaleBrizardSolution D 0 S = zeroBrizardSolution D := by
  apply Subtype.ext
  exact nlsScaleJet_zero_full S.val

theorem scaleFocusingSolution_mul (a b : ℝ) (S : FocusingSolutionJet) :
    scaleFocusingSolution a (scaleFocusingSolution b S) =
      scaleFocusingSolution (a * b) S := by
  apply Subtype.ext
  exact nlsScaleJet_mul_full a b S.val

theorem scaleDefocusingSolution_mul (a b : ℝ) (S : DefocusingSolutionJet) :
    scaleDefocusingSolution a (scaleDefocusingSolution b S) =
      scaleDefocusingSolution (a * b) S := by
  apply Subtype.ext
  exact nlsScaleJet_mul_full a b S.val

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
