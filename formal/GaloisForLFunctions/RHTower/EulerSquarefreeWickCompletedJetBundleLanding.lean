import GaloisForLFunctions.RHTower.EulerSquarefreeWickTriangularCompletedExtension
import GaloisForLFunctions.RHTower.EulerSquarefreeWickGlobalMeromorphicMatrixLanding
import GaloisForLFunctions.HTGeometry.EntireIdentityTheorem
import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure

/-!
# Completed EWQ jet-bundle landing

The scalar primitive mod-12 carrier can vanish at an unknown spectral point, so one scalar
off-diagonal does not remove auxiliary zero-avoidance from the EWQ route.  The full analytic jet
does.  An entire nonzero function cannot have every derivative vanish at one point; the primitive
EWQ completed interaction is nonzero because its value at `2` is nonzero.

This module replaces the scalar triangular extension by its countable completed jet family.  Every
coordinate remains entire and has determinant `Xi²`.  At every complex point some graded
off-diagonal is nonzero.  Consequently a point lies on the Xi divisor exactly when some jet
coordinate is a nonzero square-zero matrix.  This is a coefficient-faithful completed Xi landing
formed before selecting any divisor point, with no auxiliary zero-avoidance premise.
-/

open Complex Matrix Filter Set Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Full completed analytic jet of the primitive EWQ interaction. -/
def eulerWickPrimitiveCompletedInteractionJet (s : ℂ) : ℕ → ℂ :=
  fun n => iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s

/-- The complete EWQ interaction jet is nowhere zero. -/
theorem eulerWickPrimitiveCompletedInteractionJet_ne_zero (s : ℂ) :
    eulerWickPrimitiveCompletedInteractionJet s ≠ 0 := by
  intro hzero
  have hflat : ∀ n : ℕ,
      iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s = 0 := by
    intro n
    simpa [eulerWickPrimitiveCompletedInteractionJet] using congrFun hzero n
  have hA : AnalyticOnNhd ℂ eulerWickQuadraticPrimitiveCompletedInteraction Set.univ :=
    eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.differentiableOn.analyticOnNhd
      isOpen_univ
  have hgerm : eulerWickQuadraticPrimitiveCompletedInteraction =ᶠ[nhds s] 0 :=
    _root_.HTGeometry.eventuallyEq_zero_of_iteratedDeriv_eq_zero
      (hA s (Set.mem_univ s)) hflat
  have hglobal : Set.EqOn eulerWickQuadraticPrimitiveCompletedInteraction 0 Set.univ :=
    hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ s) hgerm
  exact eulerWickQuadraticPrimitiveCompletedInteraction_two_ne_zero
    (by simpa using hglobal (Set.mem_univ (2 : ℂ)))

/-- Entire triangular Xi extension in every completed EWQ jet channel. -/
def eulerWickCompletedJetExtension (s : ℂ) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![_root_.RHTower.xi s,
      iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s;
     0, _root_.RHTower.xi s]

/-- Every jet coordinate is an entire matrix entry. -/
theorem eulerWickCompletedJetExtension_entry_differentiable
    (n : ℕ) (i j : Fin 2) :
    Differentiable ℂ (fun s => eulerWickCompletedJetExtension s n i j) := by
  fin_cases i <;> fin_cases j
  · simpa [eulerWickCompletedJetExtension] using _root_.RHTower.xi_differentiable
  · simpa [eulerWickCompletedJetExtension] using
      (GaloisForLFunctions.differentiable_iteratedDeriv_of_entire
        eulerWickQuadraticPrimitiveCompletedInteraction_differentiable n)
  · simp [eulerWickCompletedJetExtension]
  · simpa [eulerWickCompletedJetExtension] using _root_.RHTower.xi_differentiable

/-- Every completed jet coordinate has determinant exactly `Xi²`. -/
theorem det_eulerWickCompletedJetExtension (s : ℂ) (n : ℕ) :
    (eulerWickCompletedJetExtension s n).det = _root_.RHTower.xi s ^ (2 : ℕ) := by
  rw [Matrix.det_fin_two]
  simp [eulerWickCompletedJetExtension, pow_two]

/-- The grading reads the `n`-th completed EWQ jet with no scalarization. -/
theorem eulerWickCompletedJetExtension_orientationCommutator
    (s : ℂ) (n : ℕ) :
    eulerWickCompletedJetExtension s n * eulerWickTriangularCompletedGrading -
        eulerWickTriangularCompletedGrading * eulerWickCompletedJetExtension s n =
      !![0, -2 * iteratedDeriv n
        eulerWickQuadraticPrimitiveCompletedInteraction s; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [eulerWickCompletedJetExtension, eulerWickTriangularCompletedGrading]
  all_goals ring

/-- Some completed jet channel retains nonzero EWQ orientation at every spectral point. -/
theorem eulerWickCompletedJetExtension_orientationFamily_ne_zero (s : ℂ) :
    (fun n =>
      eulerWickCompletedJetExtension s n * eulerWickTriangularCompletedGrading -
        eulerWickTriangularCompletedGrading * eulerWickCompletedJetExtension s n) ≠ 0 := by
  intro hzero
  apply eulerWickPrimitiveCompletedInteractionJet_ne_zero s
  funext n
  have hmatrix := congrFun hzero n
  have h01 := congrFun (congrFun hmatrix (0 : Fin 2)) (1 : Fin 2)
  rw [eulerWickCompletedJetExtension_orientationCommutator] at h01
  simpa [eulerWickPrimitiveCompletedInteractionJet] using h01

/-- Xi vanishing is exactly the occurrence of a nonzero square-zero completed jet channel. -/
theorem eulerWickCompletedJetExtension_nonzero_squareZero_iff (s : ℂ) :
    (∃ n : ℕ, eulerWickCompletedJetExtension s n ≠ 0 ∧
      eulerWickCompletedJetExtension s n * eulerWickCompletedJetExtension s n = 0) ↔
      _root_.RHTower.xi s = 0 := by
  constructor
  · rintro ⟨n, _hne, hsquare⟩
    have h00 := congrFun (congrFun hsquare (0 : Fin 2)) (0 : Fin 2)
    simp [eulerWickCompletedJetExtension, Matrix.mul_apply, Fin.sum_univ_two] at h00
    exact h00
  · intro hxi
    have hjet := eulerWickPrimitiveCompletedInteractionJet_ne_zero s
    obtain ⟨n, hn⟩ : ∃ n : ℕ,
        iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s ≠ 0 := by
      simpa [eulerWickPrimitiveCompletedInteractionJet, funext_iff] using hjet
    refine ⟨n, ?_, ?_⟩
    · intro hmatrix
      have h01 := congrFun (congrFun hmatrix (0 : Fin 2)) (1 : Fin 2)
      simp [eulerWickCompletedJetExtension] at h01
      exact hn h01
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [eulerWickCompletedJetExtension, Matrix.mul_apply,
          Fin.sum_univ_two, hxi]

end

end GaloisForLFunctions.RHTower
