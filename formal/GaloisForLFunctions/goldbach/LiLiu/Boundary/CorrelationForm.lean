import GaloisForLFunctions.goldbach.LiLiu.Boundary.LeftEdgeForm
import GaloisForLFunctions.goldbach.LiLiu.Mellin.ResidualIntegral

/-! # The weighted Goldbach error as an arithmetic Hardy form -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter HTGeometry
open scoped ComplexConjugate InnerProductSpace
noncomputable section

/-- The signed Goldbach error is the Hardy quadratic form at a vector of
uniformly bounded squared norm. The vector is the normalized projection
of the Mellin test supported on the left edge. -/
theorem exists_hardy_error_vector (φ : TestWeight) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (hN : 4 ≤ k+2) (hg : modulusGRH (k+2))
      (ha : 0 < leftEdge (k+2)) (ht : leftEdge (k+2) < 1/8) (_ : 1 ≤ Real.log (k+2 : ℕ)),
      ∃ v : hardySpace (leftEdge (k+2)) (1/8), ‖v‖^2 ≤ C ∧
        ⟪v,hardyOperator hN hg ha ht.le v⟫_ℂ =
          ((φ.mass*singularSeries (k+2)-correlation φ (k+2) : ℝ) : ℂ) := by
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
  let H := hardySpace a (1/8)
  let p := H.orthogonalProjectionOnto u
  let T := hardyOperator hN hg ha ht.le
  refine ⟨c • p,?_,?_⟩
  · rw [norm_smul,mul_pow]
    exact mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (norm_nonneg p) (H.norm_orthogonalProjectionOnto_apply_le u) 2).trans hnorm)
      (sq_nonneg _)
  · have hc : conj c = c := by simp only [c,map_div₀,map_one,map_mul,map_ofNat,Complex.conj_ofReal]
    change ⟪c • p,T (c • p)⟫_ℂ = _
    rw [map_smul,inner_smul_left,inner_smul_right,hc,← mul_assoc,← sq]
    change c^2 * ⟪u,(arithmeticSqKernel hN hg ha ht.le).op u⟫_ℂ = _ at he
    rw [hardyOperator_form] at he
    exact he

/-- One constant works for every admissible modulus and depends only on the weight. -/
theorem goldbach_error_le_hardyOperator (φ : TestWeight) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (hN : 4 ≤ k+2) (hg : modulusGRH (k+2))
      (ha : 0 < leftEdge (k+2)) (ht : leftEdge (k+2) < 1/8) (hl : 1 ≤ Real.log (k+2 : ℕ)),
      |correlation φ (k+2) - φ.mass * singularSeries (k+2)| ≤ C * ‖hardyOperator hN hg ha ht.le‖ := by
  obtain ⟨C,hC,hv⟩ := exists_hardy_error_vector φ
  refine ⟨C,hC,?_⟩
  intro k hN hg ha ht hl
  obtain ⟨v,hn,he⟩ := hv k hN hg ha ht hl
  let T := hardyOperator hN hg ha ht.le
  have e := congrArg norm he
  rw [Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] at e
  calc
    _ = ‖⟪v,T v⟫_ℂ‖ := e.symm
    _ ≤ ‖v‖*‖T v‖ := norm_inner_le_norm (𝕜 := ℂ) v (T v)
    _ ≤ ‖v‖*(‖T‖*‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg v)
    _ = ‖v‖^2*‖T‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hn (norm_nonneg T)

#print axioms exists_hardy_error_vector
#print axioms goldbach_error_le_hardyOperator
end
end GaloisForLFunctions.Goldbach.LiLiu
