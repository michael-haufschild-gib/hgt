import GaloisForLFunctions.ArithmeticOrientationTheory.WienerCoefficientEvaluation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The complete graph domain of arithmetic cofactor action

Every output coordinate is a finite continuous linear combination of Wiener
coefficients. Requiring the pronic-weighted output to belong to `ell2` therefore
defines a closed graph in a product of Banach spaces, for every arithmetic row.
Its complete graph norm exists even when its image in the Wiener algebra is
not closed.
-/

noncomputable section
open Finset
open scoped ENNReal
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Square-summable pronic coordinates, indexed by positive integer cells. -/
abbrev PronicCoordinateSpace := lp (fun _ : ℕ => ℂ) 2

/-- One coordinate of the cofactor action, normalized by its exact pronic weight. -/
def cofactorPronicCoordinate (v : ℕ → ℂ) (n : ℕ) : WienerAlgebraAt (1 / 2) →L[ℂ] ℂ :=
  ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℂ)⁻¹) •
    ∑ j ∈ Icc 1 (n + 1), v ((n + 1) / j) • WienerAlgebraAt.coefficientLinear (1 / 2) j

theorem cofactorPronicCoordinate_apply (v : ℕ → ℂ) (k : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    cofactorPronicCoordinate v n k =
      (∑ j ∈ Icc 1 (n + 1), k.toFn j * v ((n + 1) / j)) /
        (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℂ) := by
  simp only [cofactorPronicCoordinate, _root_.smul_apply,
    _root_.sum_apply, WienerAlgebraAt.coefficientLinear_apply, smul_eq_mul,
    div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  exact sum_congr rfl fun j _ => mul_comm _ _

private def cofactorGraphEquation (v : ℕ → ℂ) (n : ℕ) :
    (WienerAlgebraAt (1 / 2) × PronicCoordinateSpace) →L[ℂ] ℂ :=
  (lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℕ => ℂ) (p := 2) n).comp
      (ContinuousLinearMap.snd ℂ _ _) -
    (cofactorPronicCoordinate v n).comp (ContinuousLinearMap.fst ℂ _ _)

/-- The actual cofactor graph, with no growth or payment premise on its source row. -/
def cofactorGraphDomain (v : ℕ → ℂ) :
    Submodule ℂ (WienerAlgebraAt (1 / 2) × PronicCoordinateSpace) where
  carrier := {p | ∀ n, cofactorGraphEquation v n p = 0}
  zero_mem' := fun n => map_zero _
  add_mem' hp hq n := by rw [map_add, hp n, hq n, add_zero]
  smul_mem' z p hp n := by rw [map_smul, hp n, smul_zero]

theorem mem_cofactorGraphDomain (v : ℕ → ℂ)
    (p : WienerAlgebraAt (1 / 2) × PronicCoordinateSpace) :
    p ∈ cofactorGraphDomain v ↔ ∀ n, p.2 n = cofactorPronicCoordinate v n p.1 := by
  change (∀ n, p.2 n - cofactorPronicCoordinate v n p.1 = 0) ↔ _
  simp only [sub_eq_zero]

/-- Coordinate continuity makes the cofactor graph closed for every arithmetic source row. -/
theorem isClosed_cofactorGraphDomain (v : ℕ → ℂ) :
    IsClosed (cofactorGraphDomain v : Set (WienerAlgebraAt (1 / 2) × PronicCoordinateSpace)) := by
  have he : (cofactorGraphDomain v : Set (WienerAlgebraAt (1 / 2) × PronicCoordinateSpace)) =
      ⋂ n : ℕ, {p | cofactorGraphEquation v n p = 0} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [he]
  apply isClosed_iInter
  intro n
  exact isClosed_eq (cofactorGraphEquation v n).continuous continuous_const

/-- The inherited graph norm is complete without assuming ambient closedness of payment. -/
instance cofactorGraphDomain_completeSpace (v : ℕ → ℂ) : CompleteSpace (cofactorGraphDomain v) :=
  completeSpace_coe_iff_isComplete.mpr (isClosed_cofactorGraphDomain v).isComplete

/-- Continuous inclusion of the graph domain into the original Wiener algebra. -/
def cofactorGraphInput (v : ℕ → ℂ) : cofactorGraphDomain v →L[ℂ] WienerAlgebraAt (1 / 2) :=
  (ContinuousLinearMap.fst ℂ _ _).comp (cofactorGraphDomain v).subtypeL

/-- The cofactor action is continuous in the complete graph norm. -/
def cofactorGraphOutput (v : ℕ → ℂ) : cofactorGraphDomain v →L[ℂ] PronicCoordinateSpace :=
  (ContinuousLinearMap.snd ℂ _ _).comp (cofactorGraphDomain v).subtypeL

/-- A kernel uniquely determines every output coordinate. -/
theorem cofactorGraphInput_injective (v : ℕ → ℂ) : Function.Injective (cofactorGraphInput v) := by
  intro p q hpq
  have hx : p.val.1 = q.val.1 := hpq
  have hy : p.val.2 = q.val.2 := by
    apply lp.ext
    funext n
    rw [(mem_cofactorGraphDomain v p.val).mp p.property n,
      (mem_cofactorGraphDomain v q.val).mp q.property n, hx]
  exact Subtype.ext (Prod.ext hx hy)

/-- The graph image is exactly the square-summability domain of the actual finite cofactor coordinates. -/
theorem mem_range_cofactorGraphInput_iff (v : ℕ → ℂ) (k : WienerAlgebraAt (1 / 2)) :
    k ∈ Set.range (cofactorGraphInput v) ↔
      Summable (fun n : ℕ => ‖cofactorPronicCoordinate v n k‖ ^ 2) := by
  constructor
  · rintro ⟨p, rfl⟩
    have h := (lp.memℓp p.val.2).summable (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    refine h.congr fun n => ?_
    rw [ENNReal.toReal_ofNat, Real.rpow_two,
      (mem_cofactorGraphDomain v p.val).mp p.property n]
    rfl
  · intro h
    let w : PronicCoordinateSpace := ⟨fun n => cofactorPronicCoordinate v n k,
      memℓp_gen (h.congr fun n => by rw [ENNReal.toReal_ofNat, Real.rpow_two])⟩
    have hgraph : (k, w) ∈ cofactorGraphDomain v :=
      (mem_cofactorGraphDomain v (k, w)).mpr fun n => rfl
    exact ⟨⟨(k, w), hgraph⟩, rfl⟩

end GaloisForLFunctions.BiarithmeticGeometry
