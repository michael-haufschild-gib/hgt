import GaloisForLFunctions.goldbach.LiLiu.Boundary.LeftEdgeForm
import GaloisForLFunctions.goldbach.LiLiu.Mellin.CharacterMoment
import GaloisForLFunctions.goldbach.LiLiu.Mellin.DiagonalInversion
import GaloisForLFunctions.goldbach.LiLiu.Mellin.DoubleModel

/-! # The weighted Goldbach error as an arithmetic Hardy form -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter HTGeometry
open scoped ComplexConjugate InnerProductSpace
noncomputable section

private def diagonalTestKernel (N : ℕ) (φ : TestWeight) (a : ℝ) (p : ℝ × ℝ) : ℂ :=
  let s := mellinLine a p.1
  let z := mellinLine a p.2
  (mellinMultiplier N φ s * conj (mellinMultiplier N φ z)) * diagonalSeries N (s+conj z)

private theorem diagonalTestKernel_integrable {N : ℕ} (hN : 0 < N) (φ : TestWeight) {a : ℝ} (ha : 0 < a) :
    Integrable (diagonalTestKernel N φ a) := by
  obtain ⟨D,hD,hd⟩ := diagonalSeries_halfPlane_bound N (a := 2*a) (by positivity)
  let s := mellinLine a
  let V := fun t => mellinMultiplier N φ (s t)
  let w := fun p : ℝ × ℝ => s p.1 + conj (s p.2)
  have hw : Continuous w := ((mellinLine_continuous a).comp continuous_fst).add
    (continuous_conj.comp ((mellinLine_continuous a).comp continuous_snd))
  have hre (p : ℝ × ℝ) : (w p).re=2*a := by simp [w,s,two_mul]
  have hD' : Continuous (fun p => diagonalSeries N (w p)) := continuous_iff_continuousAt.mpr fun p =>
    (diagonalSeries_differentiableAt N ((hre p).symm ▸ mul_pos (by norm_num) ha)).continuousAt.comp hw.continuousAt
  have hv : Continuous V := (mellinMultiplier_continuous N hN φ).comp (mellinLine_continuous a)
  have hv' := (mellinMultiplier_integrable N hN φ a).norm
  apply ((hv'.mul_prod hv').const_mul D).mono'
    (((hv.comp continuous_fst).mul (continuous_conj.comp (hv.comp continuous_snd))).mul hD').aestronglyMeasurable
  filter_upwards with p
  change ‖(V p.1 * conj (V p.2))* diagonalSeries N (w p)‖ ≤ D * (‖V p.1‖ * ‖V p.2‖)
  rw [norm_mul,norm_mul,RCLike.norm_conj,mul_comm D]
  exact mul_le_mul_of_nonneg_left (hd _ (hre p).ge) (by positivity)

/-- Exact signed contour identity. Each of the three product integrals converges absolutely. -/
theorem residual_contour_integral {k : ℕ} (hN : 4 ≤ k+2) (φ : TestWeight) (hg : modulusGRH (k+2))
    {a : ℝ} (ha : 0 < a) (ht : a ≤ 1/8) :
    (1/(2*Real.pi):ℂ)^2 * (∫ x : ℝ, ∫ y : ℝ, (mellinMultiplier (k+2) φ (mellinLine a x) *
        conj (mellinMultiplier (k+2) φ (mellinLine a y))) *
        residualKernel (k+2) (mellinLine a x) (mellinLine a y)) =
      ((φ.mass * singularSeries (k+2) - correlation φ (k+2) : ℝ) : ℂ) := by
  let N := k+2
  let C := characterTestKernel N φ a
  let D := diagonalTestKernel N φ a
  let B := modelTestKernel N φ a
  let c := (1/(2*Real.pi):ℂ)
  obtain ⟨hC,hCE⟩ := characterMoment_integral (n := k+1) φ hg ha (by linarith only [ht])
  have hD := diagonalTestKernel_integrable (N := N) (by dsimp [N]; omega) φ ha
  have hB := modelTestKernel_integrable hN φ ha ht
  have hDE : c^2 * (∫ p, D p) = (diagonal φ N : ℂ) := by
    simpa only [c,D,diagonalTestKernel,mul_comm (diagonalSeries _ _)] using diagonal_mellin_evaluation N φ ha
  have hBE := doubleModel_integral hN φ ha ht
  have hrs (x y : ℝ) : (mellinMultiplier N φ (mellinLine a x) *
      conj (mellinMultiplier N φ (mellinLine a y))) * residualKernel N (mellinLine a x) (mellinLine a y) =
      C (x,y)-D (x,y)-B (x,y) := by
    dsimp [residualKernel,C,D,B,characterTestKernel,diagonalTestKernel,modelTestKernel]
    ring
  have hCD : Integrable (fun p => C p-D p) := hC.sub hD
  have hCDB : Integrable (fun p => C p-D p-B p) := hCD.sub hB
  change c^2 * _ = _
  simp_rw [hrs]
  rw [← integral_prod (fun p : ℝ × ℝ => C p-D p-B p) hCDB,
    integral_sub hCD hB,integral_sub hC hD,mul_sub,mul_sub,hDE]
  change c^2 * (∫ p, characterTestKernel (k+2) φ a p) - (diagonal φ (k+2):ℂ) -
    c^2 * (∫ p, modelTestKernel (k+2) φ a p) = _
  rw [hCE,hBE,correlation_eq_diagonal_sub_oddMoment]
  push_cast
  ring

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

#print axioms residual_contour_integral
#print axioms goldbach_error_le_hardyOperator
end
end GaloisForLFunctions.Goldbach.LiLiu
