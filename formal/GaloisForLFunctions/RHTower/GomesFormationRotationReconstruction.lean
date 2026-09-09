import GaloisForLFunctions.HTGeometry.GomesPlanarRotationReconstruction
import GaloisForLFunctions.HTGeometry.GomesPolynomialGaugeRigidity
import GaloisForLFunctions.RHTower.FormationBlowupProjectiveKinkBarrierTransgression

/-!
# Formation-curve symmetry reconstruction

The existing formation rotation curve detects the full planar complex commutant through its
quarter-turn endpoint. Its invariant bilinear matrices retain metric and area components.
Reflection reverses its parameter, but no fixed proper rotation implements that reflection.
Compact polynomial rigidity rules out a globally polynomial real matrix realization.

These are applications of the reconstruction and algebraic-representation distinctions in
Gomes, arXiv:2607.24901, Propositions 2–3.
https://arxiv.org/abs/2607.24901
-/

open scoped Matrix Topology
open Filter
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

/-- The existing formation frame as a bundled special orthogonal transformation. -/
def formationGaugeRotation (u : ℝ) : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨formationRotation u,Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' _ _).mpr (formationRotation_transpose_mul u),
      formationRotation_det u⟩⟩

/-- The formation frame uses the standard real model of a unit complex scalar. -/
theorem formationRotation_planar_complex (u : ℝ) :
    formationRotation u = gomesPlanarComplexMatrix (formationVisibility u) (formationContrast u) := rfl

/-- The nonuniform formation curve detects the full planar rotation commutant through its
quarter-turn endpoint; no surjectivity of the curve onto SO(2) is required. -/
theorem formationRotation_matrix_commutant (C : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ u : ℝ, C * formationRotation u = formationRotation u * C) ↔
      C = gomesPlanarComplexMatrix (C 0 0) (C 1 0) := by
  constructor
  · intro h
    have hl : Tendsto (fun u => C * formationRotation u) atTop
        (nhds (C * formationQuarterTurn)) := tendsto_const_nhds.mul formationRotation_tendsto_atTop
    have hr : Tendsto (fun u => formationRotation u * C) atTop
        (nhds (formationQuarterTurn * C)) := formationRotation_tendsto_atTop.mul tendsto_const_nhds
    have he : (fun u => C * formationRotation u) = (fun u => formationRotation u * C) := funext h
    rw [he] at hl
    have hc := tendsto_nhds_unique hl hr
    exact (planar_quarterTurn_commutant C).mp hc
  · intro h u
    exact (planar_specialOrthogonal_commutant C).mpr h (formationGaugeRotation u)

/-- Formation-invariant bilinear forms retain exactly a metric component and an area component. -/
theorem formationRotation_invariant_bilinear (C : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ u : ℝ, (formationRotation u)ᵀ * C * formationRotation u = C) ↔
      C = gomesPlanarComplexMatrix (C 0 0) (C 1 0) := by
  rw [← formationRotation_matrix_commutant]
  constructor
  · intro h u
    have hRR := (Matrix.mem_orthogonalGroup_iff _ _).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp (formationGaugeRotation u).property).1
    change formationRotation u * (formationRotation u)ᵀ = 1 at hRR
    calc
      C * formationRotation u =
          (formationRotation u * (formationRotation u)ᵀ) * C * formationRotation u := by
            rw [hRR]; simp
      _ = formationRotation u * ((formationRotation u)ᵀ * C * formationRotation u) := by
        simp only [mul_assoc]
      _ = formationRotation u * C := by rw [h u]
  · intro h u
    rw [mul_assoc,h u,← mul_assoc,formationRotation_transpose_mul,one_mul]

/-- Reflection reverses the formation parameter exactly. -/
theorem formationRotation_reflection_reverses_parameter (u : ℝ) :
    gomesAxisReflection (0 : Fin 2) * formationRotation u * gomesAxisReflection (0 : Fin 2) =
      formationRotation (-u) := by
  have h := planar_reflection_conjugation (formationGaugeRotation u)
  change gomesAxisReflection 0 * formationRotation u * gomesAxisReflection 0 =
    (formationRotation u)ᵀ at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formationRotation]

/-- Distinct asymptotic contrast limits exclude any constant formation frame. -/
theorem formationRotation_not_constant :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) ℝ, ∀ u : ℝ, formationRotation u = M := by
  rintro ⟨M,h⟩
  have he : formationContrast = fun _ : ℝ => M 1 0 := by
    funext u
    have hu := congrFun (congrFun (h u) 1) 0
    simpa [formationRotation] using hu
  have ht := formationContrast_tendsto_atTop
  have hb := formationContrast_tendsto_atBot
  rw [he] at ht hb
  have ht' : M 1 0 = 1 := tendsto_nhds_unique tendsto_const_nhds ht
  have hb' : M 1 0 = -1 := tendsto_nhds_unique tendsto_const_nhds hb
  linarith

/-- No globally polynomial real matrix curve can equal the existing formation rotation. -/
theorem formationRotation_no_polynomial_matrix_curve :
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) (Polynomial ℝ),
      ∀ u : ℝ, P.map (Polynomial.eval u) = formationRotation u := by
  rintro ⟨P,h⟩
  have hp := (polynomial_orthogonal_family_iff P).mp (by
    intro u
    rw [h u]
    exact formationRotation_transpose_mul u)
  apply formationRotation_not_constant
  refine ⟨P.map (Polynomial.eval 0),?_⟩
  intro u
  rw [← h u]
  ext i j
  change (P i j).eval u = (P i j).eval 0
  conv_lhs => rw [hp.1 i j,Polynomial.eval_C]

/-- No fixed proper rotation implements reflection on the entire formation curve. -/
theorem formationRotation_reflection_not_inner :
    ¬ ∃ S : Matrix.specialOrthogonalGroup (Fin 2) ℝ, ∀ u : ℝ,
      gomesAxisReflection (0 : Fin 2) * formationRotation u * gomesAxisReflection (0 : Fin 2) =
        S.val * formationRotation u * S.valᵀ := by
  rintro ⟨S,h⟩
  have hs := (Matrix.mem_orthogonalGroup_iff _ _).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp S.property).1
  have hz : ∀ u : ℝ, formationContrast u = 0 := by
    intro u
    have hc := (planar_specialOrthogonal_commutant S.val).mpr
      (planar_specialOrthogonal_complex_form S) (formationGaugeRotation u)
    change S.val * formationRotation u = formationRotation u * S.val at hc
    have hh := h u
    rw [formationRotation_reflection_reverses_parameter] at hh
    simp only [hc,mul_assoc,hs,mul_one] at hh
    have he := congrFun (congrFun hh 1) 0
    simp [formationRotation] at he
    linarith
  have ht := formationContrast_tendsto_atTop
  rw [show formationContrast = fun _ : ℝ => 0 from funext hz] at ht
  have hf : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds ht
  linarith

end RHTower
