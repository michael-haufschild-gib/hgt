import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinFlow
import GaloisForLFunctions.Bottcher.CrossRatioNormalBridge

set_option autoImplicit false

/-!
# Global homogeneous Landau–Lifshitz evolution

The Schaffer–Exl spin flow (arXiv:2609.04530) extends through the north pole
using the existing homogeneous quotient sphere from the Böttcher/Montel
corpus. Nonzero homogeneous pairs give unit spins; the zero pair gives the
stationary zero spin. The actual global trajectory solves the established
cross-product field, preserves spin length, inherits exact time composition,
and is invariant under common nonzero complex scaling.
-/
open scoped Matrix RealInnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Global spin evolution through the corpus's homogeneous Riemann-sphere coordinates. -/
def projectiveSpinFlow (a : ℝ) (N D : ℂ) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  _root_.Bottcher.homogeneousRatioStereo (spinPlaneFlow a N t) D

/-- The zero homogeneous pair represents the zero spin at every time. -/
theorem projectiveSpinFlow_zero_pair (a t : ℝ) : projectiveSpinFlow a 0 0 t = 0 := by
  simp [projectiveSpinFlow, spinPlaneFlow, _root_.Bottcher.homogeneousRatioStereo]

/-- The established north-gradient spin field vanishes at the north pole. -/
theorem spinSphereField_north (a : ℝ) :
    spinSphereField a (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) = 0 := by
  rw [spinSphereField_components]
  simp

theorem spinSphereField_zero (a : ℝ) : spinSphereField a 0 = 0 := by
  rw [spinSphereField_components]
  simp

/-- A zero homogeneous denominator gives the north pole, with the degenerate zero pair explicit. -/
theorem projectiveSpinFlow_pole (a : ℝ) (N : ℂ) (t : ℝ) :
    projectiveSpinFlow a N 0 t =
      if N = 0 then 0 else (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) := by
  by_cases hN : N = 0
  · subst N
    simp [projectiveSpinFlow_zero_pair]
  · have hf : spinPlaneFlow a N t ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) hN
    have hn : Complex.normSq (spinPlaneFlow a N t) ≠ 0 :=
      mt Complex.normSq_eq_zero.mp hf
    simp [projectiveSpinFlow, _root_.Bottcher.homogeneousRatioStereo, hN, hn]

/-- Exact global chart classification, including the north pole and the zero spin. -/
theorem projectiveSpinFlow_chart (a : ℝ) (N D : ℂ) (t : ℝ) :
    projectiveSpinFlow a N D t =
      if D = 0 then (if N = 0 then 0 else (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)))
      else spinSphereFlow a (N / D) t := by
  by_cases hD : D = 0
  · subst D
    simpa using projectiveSpinFlow_pole a N t
  · rw [if_neg hD, projectiveSpinFlow, _root_.Bottcher.homogeneousRatioStereo_eq_stereo_div hD]
    congr 1
    simp only [spinPlaneFlow, mul_div_assoc]

/-- The homogeneous construction solves the actual spin equation globally, with no excluded pole. -/
theorem hasDerivAt_projectiveSpinFlow (a : ℝ) (N D : ℂ) (t : ℝ) :
    HasDerivAt (projectiveSpinFlow a N D) (spinSphereField a (projectiveSpinFlow a N D t)) t := by
  by_cases hD : D = 0
  · subst D
    by_cases hN : N = 0
    · subst N
      have hf : projectiveSpinFlow a 0 0 = fun _ => 0 := by
        funext s
        exact projectiveSpinFlow_zero_pair a s
      rw [hf, spinSphereField_zero]
      exact hasDerivAt_const t 0
    · have hf : projectiveSpinFlow a N 0 = fun _ => (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) := by
        funext s
        simp only [projectiveSpinFlow_pole, if_neg hN]
      rw [hf, spinSphereField_north]
      exact hasDerivAt_const t _
  · have hf : projectiveSpinFlow a N D = spinSphereFlow a (N / D) := by
      funext s
      simp only [projectiveSpinFlow_chart, if_neg hD]
    rw [hf]
    exact hasDerivAt_spinSphereFlow a (N / D) t

/-- Every nonzero homogeneous pair has unit spin length; only the zero pair has zero length. -/
theorem projectiveSpinFlow_norm (a : ℝ) (N D : ℂ) (t : ℝ) :
    ‖projectiveSpinFlow a N D t‖ = if N = 0 ∧ D = 0 then 0 else 1 := by
  by_cases hD : D = 0
  · subst D
    by_cases hN : N = 0
    · subst N
      simp [projectiveSpinFlow_zero_pair]
    · rw [projectiveSpinFlow_pole, if_neg hN, if_neg (by simp [hN]), _root_.Bottcher.norm_euclidean3]
      simp
  · rw [projectiveSpinFlow_chart, if_neg hD, spinSphereFlow_norm, if_neg (by simp [hD])]

/-- Exact spin-length preservation for every homogeneous input and all real times. -/
theorem projectiveSpinFlow_norm_preserved (a : ℝ) (N D : ℂ) (s t : ℝ) :
    ‖projectiveSpinFlow a N D s‖ = ‖projectiveSpinFlow a N D t‖ := by
  rw [projectiveSpinFlow_norm, projectiveSpinFlow_norm]

/-- Nonzero homogeneous coordinates are precisely the unit-spin states of the flow. -/
theorem projectiveSpinFlow_unit_iff (a : ℝ) (N D : ℂ) (t : ℝ) :
    ‖projectiveSpinFlow a N D t‖ = 1 ↔ N ≠ 0 ∨ D ≠ 0 := by
  rw [projectiveSpinFlow_norm]
  by_cases h : N = 0 ∧ D = 0
  · rcases h with ⟨rfl, rfl⟩
    simp
  · rw [if_neg h]
    constructor
    · intro _
      exact not_and_or.mp h
    · intro _
      rfl

/-- The homogeneous evolution inherits the exact chart composition law. -/
theorem projectiveSpinFlow_add (a : ℝ) (N D : ℂ) (s t : ℝ) :
    projectiveSpinFlow a N D (s + t) = projectiveSpinFlow a (spinPlaneFlow a N s) D t := by
  rw [projectiveSpinFlow, spinPlaneFlow_add]
  rfl

/-- Arbitrary common nonzero complex scaling is invisible in the projective spin trajectory. -/
theorem projectiveSpinFlow_exp_gauge (a : ℝ) (N D c : ℂ) (t : ℝ) :
    projectiveSpinFlow a (Complex.exp c * N) (Complex.exp c * D) t = projectiveSpinFlow a N D t := by
  have h : spinPlaneFlow a (Complex.exp c * N) t = Complex.exp c * spinPlaneFlow a N t := by
    unfold spinPlaneFlow
    ring
  rw [projectiveSpinFlow, h, _root_.Bottcher.homogeneousRatioStereo_smul (Complex.exp_ne_zero c)]
  rfl

end
end GaloisForLFunctions.HTGeometry.SchafferExl
