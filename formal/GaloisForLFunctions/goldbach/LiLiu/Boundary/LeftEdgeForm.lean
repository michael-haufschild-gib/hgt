import GaloisForLFunctions.goldbach.LiLiu.Boundary.HardyOperator

/-! # Testing the arithmetic quadratic form on the left boundary

A test supported on the left line removes all three terms involving the
right line. Its two linear factors cancel the Hardy denominators.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter Set HTGeometry
open scoped ComplexConjugate InnerProductSpace
noncomputable section

private theorem integral_supported_left {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hm : Measurable F) (hs : ∀ z : ℂ, z.re ≠ a → F z=0) :
    (∫ z, F z ∂boundaryMeasure a b) = ∫ t : ℝ, F (mellinLine a t) := by
  have hz (t : ℝ) : F (mellinLine b t)=0 := hs _ (by simpa using hab.ne')
  by_cases hi : Integrable (fun t => F (mellinLine a t))
  · have hr : Integrable (fun t : ℝ => F (mellinLine b t)) :=
      hi.norm.mono' (hm.comp (mellinLine_continuous b).measurable).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          change ‖F (mellinLine b t)‖ ≤ ‖F (mellinLine a t)‖
          rw [hz, norm_zero]
          exact norm_nonneg _)
    rw [integral_boundaryMeasure hm ((integrable_boundaryMeasure_iff hm a b).mpr ⟨hi,hr⟩)]
    simp only [hz,integral_zero,add_zero]
  · rw [integral_undef hi,integral_undef (fun h => hi ((integrable_boundaryMeasure_iff hm a b).mp h).1)]

/-- The exact left-edge pairing for any square-integrable kernel. -/
theorem leftLift_inner_op {a b : ℝ} (hab : a < b)
    (K : SqIntKernel (boundaryMeasure a b) (boundaryMeasure a b)) {f : ℝ → ℂ}
    (hm : Measurable f) (hi : MemLp f 2 volume) :
    let u := (leftLift_memLp hab hm hi).toLp (leftLift a f)
    ⟪u,K.op u⟫_ℂ = ∫ x : ℝ, ∫ y : ℝ,
      conj (f x) * K.toFun (mellinLine a x) (mellinLine a y) * f y := by
  let L := leftLift a f
  let u := (leftLift_memLp hab hm hi).toLp L
  let μ := boundaryMeasure a b
  have hu : (u : ℂ → ℂ) =ᵐ[μ] L := (leftLift_memLp hab hm hi).coeFn_toLp
  have hL : Measurable L := leftLift_measurable hm a
  have hleft (t : ℝ) : L (mellinLine a t)=f t := by simp [L,leftLift]
  let G (s z : ℂ) := K.toFun s z * L z
  have hG : Measurable (Function.uncurry G) := K.measurable.mul (hL.comp measurable_snd)
  have hrow (s : ℂ) : K.apply u s = ∫ z, G s z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu] with z hz
    simp only [G,hz]
  have hG' (s : ℂ) : (∫ z, G s z ∂μ) = ∫ y : ℝ, K.toFun s (mellinLine a y)*f y := by
    have hmrow : Measurable (G s) := hG.comp
      (show Measurable (fun z : ℂ => (s,z)) from measurable_const.prodMk measurable_id)
    calc
      _ = ∫ y : ℝ, G s (mellinLine a y) :=
        integral_supported_left hab hmrow (by intro z hz; simp [G,L,leftLift,hz])
      _ = _ := by simp only [G,hleft]
  change ⟪u,K.op u⟫_ℂ = _
  rw [K.inner_op]
  calc
    _ = ∫ s, conj (L s) * (∫ z, G s z ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hu] with s hs
      rw [hs,hrow]
    _ = ∫ x : ℝ, conj (L (mellinLine a x)) * (∫ z, G (mellinLine a x) z ∂μ) := by
      exact integral_supported_left hab ((continuous_conj.measurable.comp hL).mul
        (hG.stronglyMeasurable.integral_prod_right (ν := μ)).measurable)
        (by intro z hz; simp [L,leftLift,hz])
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hG',hleft,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring

theorem conjugateBoundaryTest_memLp (φ : TestWeight) {N : ℕ} (hN : 1 ≤ Real.log N) :
    MemLp (fun t => conj (boundaryTest φ N t)) 2 volume := by
  have hi := boundaryTest_memLp φ hN
  exact hi.of_le (continuous_conj.comp_aestronglyMeasurable hi.1)
    (Eventually.of_forall fun t => (RCLike.norm_conj _).le)

private theorem one_add_line_ne_zero {a : ℝ} (ha : 0 < a) (t : ℝ) : 1+mellinLine a t ≠ 0 := by
  intro he
  have h := congrArg Complex.re he
  simp only [add_re,one_re,mellinLine_re,zero_re] at h
  linarith only [h,ha]

private theorem cancel_factors (u v k r s : ℂ) (hr : r ≠ 0) (hs : s ≠ 0) :
    (u*r) * (k/(r*s)) * (v*s) = (u*v)*k := by
  field_simp [hr,hs] <;> ring

/-- The denominators cancel pointwise before either Mellin integral is taken. -/
theorem arithmetic_test_form {n : ℕ} (φ : TestWeight) (hN : 4 ≤ n+1) (hg : modulusGRH (n+1))
    (hl : 1 ≤ Real.log (n+1 : ℕ)) (ha : 0 < leftEdge (n+1)) (hab : leftEdge (n+1) < 1/8) :
    let a := leftEdge (n+1)
    let f := fun t => conj (boundaryTest φ (n+1) t)
    let hm := continuous_conj.measurable.comp (boundaryTest_continuous φ (Nat.succ_pos n)).measurable
    let u := (leftLift_memLp hab hm (conjugateBoundaryTest_memLp φ hl)).toLp (leftLift a f)
    ⟪u,(arithmeticSqKernel hN hg ha hab.le).op u⟫_ℂ =
      ∫ x : ℝ, ∫ y : ℝ, (mellinMultiplier (n+1) φ (mellinLine a x) *
        conj (mellinMultiplier (n+1) φ (mellinLine a y))) *
        residualKernel (n+1) (mellinLine a x) (mellinLine a y) := by
  dsimp only
  rw [leftLift_inner_op hab (arithmeticSqKernel hN hg ha hab.le)
    (f := fun t => conj (boundaryTest φ (n+1) t))
    (continuous_conj.measurable.comp (boundaryTest_continuous φ (Nat.succ_pos n)).measurable)
    (conjugateBoundaryTest_memLp φ hl)]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with y
  let a := leftEdge (n+1)
  have hedge (t : ℝ) : (mellinLine a t).re ∈ Icc a (1/8) := by
    rw [mellinLine_re]
    exact ⟨le_rfl,hab.le⟩
  change conj (conj (boundaryTest φ (n+1) x)) *
    extendedKernel (n+1) a (mellinLine a x) (mellinLine a y) * conj (boundaryTest φ (n+1) y) = _
  rw [extendedKernel,clippedPoint_eq (hedge x),clippedPoint_eq (hedge y)]
  have hz : 1+conj (mellinLine a y) ≠ 0 := by
    intro he
    have h := congrArg conj he
    apply one_add_line_ne_zero ha y
    simpa only [map_add,map_one,Complex.conj_conj,map_zero] using h
  change conj (conj (mellinMultiplier (n+1) φ (mellinLine a x)*(1+mellinLine a x))) *
    (residualKernel (n+1) (mellinLine a x) (mellinLine a y) /
      ((1+mellinLine a x)*(1+conj (mellinLine a y)))) *
    conj (mellinMultiplier (n+1) φ (mellinLine a y)*(1+mellinLine a y)) = _
  rw [Complex.conj_conj,map_mul,map_add,map_one]
  exact cancel_factors _ _ _ _ _ (one_add_line_ne_zero ha x) hz

#print axioms arithmetic_test_form
end
end GaloisForLFunctions.Goldbach.LiLiu
