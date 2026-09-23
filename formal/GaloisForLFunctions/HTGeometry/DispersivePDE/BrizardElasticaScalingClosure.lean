import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScaling
import Mathlib.Tactic

/-!
# Closed scaling actions on certified NLS solution spaces

The scaling symmetry discussed before equation (26) of arXiv:2607.21750 applies to every NLS
solution, not only the explicit plane and soliton families.  Packaging a solution with its proof
turns this into unconditional maps on the corpus's focusing, defocusing, and arbitrary-dispersion
Brizard solution spaces.  The induced fields have identity, zero, and multiplicative composition
laws at scales `1`, `0`, and `ab`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

abbrev FocusingSolutionJet := {J : ComplexEvolutionJet2 // SolvesFocusingNLS J}
abbrev DefocusingSolutionJet := {J : ComplexEvolutionJet2 // SolvesDefocusingNLS J}
abbrev BrizardSolutionJet (D : ℝ) := {J : ComplexEvolutionJet2 // SolvesNLS D J}

/-- Paper scaling as an unconditional endomorphism of certified focusing-NLS solutions. -/
noncomputable def scaleFocusingSolution (a : ℝ) (S : FocusingSolutionJet) :
    FocusingSolutionJet := ⟨nlsScaleJet a S, by
  intro t x
  have h := S.property (a ^ (2 : ℕ) * t) (a * x)
  have hnorm :
      ‖(a : ℂ) * S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    simpa only [nlsScaleJet] using norm_nlsScaleJet_sq a S.val t x
  simp only [nlsScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * S.val.ut (a ^ (2 : ℕ) * t) (a * x) +
          S.val.uxx (a ^ (2 : ℕ) * t) (a * x) +
          (2 : ℂ) * (‖S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            S.val.u (a ^ (2 : ℕ) * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]⟩

/-- Paper scaling as an unconditional endomorphism of certified defocusing-NLS solutions. -/
noncomputable def scaleDefocusingSolution (a : ℝ) (S : DefocusingSolutionJet) :
    DefocusingSolutionJet := ⟨nlsScaleJet a S, by
  intro t x
  have h := S.property (a ^ (2 : ℕ) * t) (a * x)
  have hnorm :
      ‖(a : ℂ) * S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    simpa only [nlsScaleJet] using norm_nlsScaleJet_sq a S.val t x
  simp only [nlsScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * S.val.ut (a ^ (2 : ℕ) * t) (a * x) +
          S.val.uxx (a ^ (2 : ℕ) * t) (a * x) -
          (2 : ℂ) * (‖S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            S.val.u (a ^ (2 : ℕ) * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]⟩

/-- Scaling closure for the paper's equation at arbitrary real dispersion `D`. -/
noncomputable def scaleBrizardSolution (D a : ℝ) (S : BrizardSolutionJet D) :
    BrizardSolutionJet D := ⟨nlsScaleJet a S, by
  intro t x
  have h := S.property (a ^ (2 : ℕ) * t) (a * x)
  have hnorm :
      ‖(a : ℂ) * S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    simpa only [nlsScaleJet] using norm_nlsScaleJet_sq a S.val t x
  simp only [nlsScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * S.val.ut (a ^ (2 : ℕ) * t) (a * x) +
          (D : ℂ) * S.val.uxx (a ^ (2 : ℕ) * t) (a * x) +
          (D : ℂ) / 2 * (‖S.val.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            S.val.u (a ^ (2 : ℕ) * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]⟩

theorem nlsScaleJet_u_one (J : ComplexEvolutionJet2) (t x : ℝ) :
    (nlsScaleJet 1 J).u t x = J.u t x := by
  simp [nlsScaleJet]

theorem nlsScaleJet_u_zero (J : ComplexEvolutionJet2) (t x : ℝ) :
    (nlsScaleJet 0 J).u t x = 0 := by
  simp [nlsScaleJet]

/-- Consecutive paper scalings compose by multiplying their real scale parameters. -/
theorem nlsScaleJet_u_mul (a b : ℝ) (J : ComplexEvolutionJet2) (t x : ℝ) :
    (nlsScaleJet a (nlsScaleJet b J)).u t x =
      (nlsScaleJet (a * b) J).u t x := by
  simp only [nlsScaleJet]
  have ht : b ^ (2 : ℕ) * (a ^ (2 : ℕ) * t) = (a * b) ^ (2 : ℕ) * t := by ring
  have hx : b * (a * x) = (a * b) * x := by ring
  rw [ht, hx]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
