import GaloisForLFunctions.goldbach.LiLiu.Boundary.LeftEdgeForm
import GaloisForLFunctions.goldbach.LiLiu.Mellin.ResidualIntegral

/-! # The weighted Goldbach error as an arithmetic Hardy form -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter HTGeometry
open scoped ComplexConjugate InnerProductSpace
noncomputable section

/-- One constant works for every admissible modulus and depends only on the weight. -/
theorem goldbach_error_le_hardyOperator (φ : TestWeight) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (hN : 4 ≤ k+2) (hg : modulusGRH (k+2))
      (ha : 0 < leftEdge (k+2)) (ht : leftEdge (k+2) < 1/8) (hl : 1 ≤ Real.log (k+2 : ℕ)),
      |correlation φ (k+2) - φ.mass * singularSeries (k+2)| ≤ C * ‖hardyOperator hN hg ha ht.le‖ := by
  obtain ⟨D,hD⟩ := boundaryTest_norm_sq_bounded φ
  let c := (1/(2*Real.pi):ℂ)
  refine ⟨‖c‖^2 * max 0 D,by positivity,?_⟩
  intro k hN hg ha ht hl
  let N := k+2
  let a := leftEdge N
  let f := fun t => conj (boundaryTest φ N t)
  have hm : Measurable f := continuous_conj.measurable.comp (boundaryTest_continuous φ (by dsimp [N]; omega)).measurable
  have hi := conjugateBoundaryTest_memLp φ hl
  let u := (leftLift_memLp ht hm hi).toLp (leftLift a f)
  have hnorm : ‖u‖^2 ≤ max 0 D := by
    rw [show ‖u‖^2=‖hi.toLp f‖^2 from leftLift_norm_sq ht hm hi,
      HTGeometry.norm_sq_toLp_eq_integral hi]
    have hd := hD N hl
    rw [HTGeometry.norm_sq_toLp_eq_integral] at hd
    simpa only [f,RCLike.norm_conj] using hd.trans (le_max_right 0 D)
  have he := residual_contour_integral hN φ hg ha ht.le
  rw [← arithmetic_test_form (n := k+1) φ hN hg hl ha ht] at he
  have hv := congrArg norm he
  change ‖c^2 * ⟪u,(arithmeticSqKernel hN hg ha ht.le).op u⟫_ℂ‖ = _ at hv
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] at hv
  rw [← hv]
  calc
    _ ≤ ‖c‖^2 * (‖hardyOperator hN hg ha ht.le‖ * ‖u‖^2) :=
      mul_le_mul_of_nonneg_left (hardyOperator_form_bound hN hg ha ht.le u) (sq_nonneg _)
    _ ≤ ‖c‖^2 * (‖hardyOperator hN hg ha ht.le‖ * max 0 D) := by gcongr
    _ = _ := by ring

#print axioms goldbach_error_le_hardyOperator
end
end GaloisForLFunctions.Goldbach.LiLiu
