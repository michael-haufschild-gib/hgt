import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
import GaloisForLFunctions.RHTower.SelbergModularStripComparison

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A real rotation and scale multiplies total squared norm by its complex norm square. -/
theorem rotation_scale_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℂ) (u₀ u₁ : E) :
    ‖d.re • u₀ + d.im • u₁‖ ^ 2 + ‖(-d.im) • u₀ + d.re • u₁‖ ^ 2 =
      Complex.normSq d * (‖u₀‖ ^ 2 + ‖u₁‖ ^ 2) := by
  rw [norm_add_sq_real, norm_add_sq_real]
  simp only [real_inner_smul_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  rw [Complex.normSq_apply]
  ring

/-- Equivariance differentiates to the literal reciprocal-square tangent law. -/
theorem chartDeriv_modular {N : ℕ} (F : formPreDomain N)
    (A : SL2Z) (z : ℍ) (v : ℂ) :
    chartDeriv (F : ℍ → DeckSpace N) ((1 / (denom A z) ^ 2) * v) (A • z) =
      finiteRegularUnitary (QuotientGroup.mk A : Deck N) (chartDeriv (F : ℍ → DeckSpace N) v z) := by
  let G : ℂ → ℂ := fun w => ((A • ofComplex w : ℍ) : ℂ)
  let V := finiteRegularUnitary (QuotientGroup.mk A : Deck N)
  let U : DeckSpace N →L[ℝ] DeckSpace N :=
    (V.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hG : HasFDerivAt G (UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ)) (z : ℂ) :=
    (UpperHalfPlane.hasStrictFDerivAt_smul (A : GL (Fin 2) ℝ) z).hasFDerivAt
  have hFz : DifferentiableAt ℝ (chartFun (F : ℍ → DeckSpace N)) (z : ℂ) :=
    ((formPreDomain.c1 F).differentiableOn one_ne_zero).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hF : DifferentiableAt ℝ (chartFun (F : ℍ → DeckSpace N)) (G (z : ℂ)) := by
    apply ((formPreDomain.c1 F).differentiableOn one_ne_zero).differentiableAt
    have hGpos : 0 < (G (z : ℂ)).im := by
      simp only [G, ofComplex_apply]
      exact (A • z).im_pos
    exact isOpen_upperHalfPlaneSet.mem_nhds hGpos
  have he : chartFun (F : ℍ → DeckSpace N) ∘ G = U ∘ chartFun (F : ℍ → DeckSpace N) := by
    funext w
    dsimp only [Function.comp_apply, chartFun, G, U, V]
    rw [ofComplex_apply]
    exact formPreDomain.equivariant F A (ofComplex w)
  have hc := hF.hasFDerivAt.comp (z : ℂ) hG
  rw [he] at hc
  have hU := U.hasFDerivAt.comp (z : ℂ) hFz.hasFDerivAt
  have hderiv := (hU.fderiv.symm.trans hc.fderiv).symm
  have h := congrArg (fun L => L v) hderiv
  have hU_apply (x : DeckSpace N) : U x = V x := rfl
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [hU_apply] at h
  have hj : UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ) v =
      (1 / (denom A z) ^ 2) * v := by
    simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, mul_comm]
  simpa only [chartDeriv, G, ofComplex_apply, ContinuousLinearMap.comp_apply, V, hj] using h


/-- Every real chart derivative is determined by its two complex-coordinate directions. -/
theorem chartDeriv_components {N : ℕ} (F : formPreDomain N) (v : ℂ) (z : ℍ) :
    chartDeriv (F : ℍ → DeckSpace N) v z =
      v.re • chartDeriv (F : ℍ → DeckSpace N) 1 z +
        v.im • chartDeriv (F : ℍ → DeckSpace N) Complex.I z := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using v.re_add_im.symm
  unfold chartDeriv
  conv_lhs => rw [hv, map_add, map_smul, map_smul]

def chartGradientNormSq {N : ℕ} (F : ℍ → DeckSpace N) (z : ℍ) : ℝ :=
  ‖chartDeriv F 1 z‖ ^ 2 + ‖chartDeriv F Complex.I z‖ ^ 2

theorem chartGradientNormSq_modular {N : ℕ} (F : formPreDomain N)
    (A : SL2Z) (z : ℍ) :
    chartGradientNormSq (F : ℍ → DeckSpace N) z =
      Complex.normSq (1 / (denom A z) ^ 2) *
        chartGradientNormSq (F : ℍ → DeckSpace N) (A • z) := by
  let d : ℂ := 1 / (denom A z) ^ 2
  let V := finiteRegularUnitary (QuotientGroup.mk A : Deck N)
  have h1 : d.re • chartDeriv (F : ℍ → DeckSpace N) 1 (A • z) +
      d.im • chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z) =
      V (chartDeriv (F : ℍ → DeckSpace N) 1 z) := by
    calc
      d.re • chartDeriv (F : ℍ → DeckSpace N) 1 (A • z) +
          d.im • chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z) =
          chartDeriv (F : ℍ → DeckSpace N) d (A • z) := by
            simpa only using (chartDeriv_components F d (A • z)).symm
      _ = V (chartDeriv (F : ℍ → DeckSpace N) 1 z) := by
            simpa only [d, mul_one, V] using chartDeriv_modular F A z 1
  have h2 : (-d.im) • chartDeriv (F : ℍ → DeckSpace N) 1 (A • z) +
      d.re • chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z) =
      V (chartDeriv (F : ℍ → DeckSpace N) Complex.I z) := by
    calc
      (-d.im) • chartDeriv (F : ℍ → DeckSpace N) 1 (A • z) +
          d.re • chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z) =
          chartDeriv (F : ℍ → DeckSpace N) (d * Complex.I) (A • z) := by
            simpa only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
              zero_mul, mul_zero, one_mul, mul_one, zero_sub, zero_add, add_zero] using
              (chartDeriv_components F (d * Complex.I) (A • z)).symm
      _ = V (chartDeriv (F : ℍ → DeckSpace N) Complex.I z) := by
            simpa only [d, V] using chartDeriv_modular F A z Complex.I
  change ‖chartDeriv (F : ℍ → DeckSpace N) 1 z‖ ^ 2 +
      ‖chartDeriv (F : ℍ → DeckSpace N) Complex.I z‖ ^ 2 =
        Complex.normSq d * (‖chartDeriv (F : ℍ → DeckSpace N) 1 (A • z)‖ ^ 2 +
          ‖chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z)‖ ^ 2)
  calc
    ‖chartDeriv (F : ℍ → DeckSpace N) 1 z‖ ^ 2 +
        ‖chartDeriv (F : ℍ → DeckSpace N) Complex.I z‖ ^ 2 =
        ‖V (chartDeriv (F : ℍ → DeckSpace N) 1 z)‖ ^ 2 +
          ‖V (chartDeriv (F : ℍ → DeckSpace N) Complex.I z)‖ ^ 2 := by
            rw [V.norm_map, V.norm_map]
    _ = ‖d.re • chartDeriv (F : ℍ → DeckSpace N) 1 (A • z) +
          d.im • chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z)‖ ^ 2 +
        ‖(-d.im) • chartDeriv (F : ℍ → DeckSpace N) 1 (A • z) +
          d.re • chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z)‖ ^ 2 := by
            rw [h1, h2]
    _ = Complex.normSq d * (‖chartDeriv (F : ℍ → DeckSpace N) 1 (A • z)‖ ^ 2 +
          ‖chartDeriv (F : ℍ → DeckSpace N) Complex.I (A • z)‖ ^ 2) :=
      rotation_scale_normSq d _ _

def hyperbolicChartGradientDensity {N : ℕ} (F : ℍ → DeckSpace N) (z : ℍ) : ℝ :=
  z.im ^ 2 * chartGradientNormSq F z

theorem hyperbolicChartGradientDensity_modular {N : ℕ} (F : formPreDomain N)
    (A : SL2Z) (z : ℍ) :
    hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) (A • z) =
      hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z := by
  have hden : Complex.normSq (denom A z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero A z))
  unfold hyperbolicChartGradientDensity
  rw [ModularGroup.im_smul_eq_div_normSq, chartGradientNormSq_modular F A z]
  simp only [show Complex.normSq (1 / denom A z ^ 2) =
      1 / Complex.normSq (denom A z) ^ 2 by simp [one_div]]
  field_simp

theorem hyperbolicChartGradientDensity_eq_hypGradNormSq {N : ℕ}
    (F : ℍ → DeckSpace N) (z : ℍ) :
    hyperbolicChartGradientDensity F z =
      ‖hypGradX F z‖ ^ 2 + ‖hypGradY F z‖ ^ 2 := by
  unfold hyperbolicChartGradientDensity chartGradientNormSq hypGradX hypGradY
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem hyperbolicChartGradientDensity_integrable_fd {N : ℕ} (F : formPreDomain N) :
    IntegrableOn (hyperbolicChartGradientDensity (F : ℍ → DeckSpace N)) fd volume := by
  have hsum : IntegrableOn (fun z =>
      ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ 2 + ‖hypGradY (F : ℍ → DeckSpace N) z‖ ^ 2)
      fd volume :=
    ((memLp_two_iff_integrable_sq_norm (formPreDomain.memLp_gradX F).aestronglyMeasurable).mp
      (formPreDomain.memLp_gradX F)).add
    ((memLp_two_iff_integrable_sq_norm (formPreDomain.memLp_gradY F).aestronglyMeasurable).mp
      (formPreDomain.memLp_gradY F))
  refine hsum.congr_fun ?_ ModularGroup.isClosed_fd.measurableSet
  intro z _
  exact (hyperbolicChartGradientDensity_eq_hypGradNormSq (F : ℍ → DeckSpace N) z).symm

theorem hyperbolicChartGradientDensity_strip_le_twice {N : ℕ} (F : formPreDomain N) :
    (∫ z in SelbergModularStripComparison.strip,
      hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z) ≤
      2 * ∫ z in fd, hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z := by
  apply SelbergModularStripComparison.integral_strip_le_twice
    (hyperbolicChartGradientDensity_integrable_fd F)
  · intro z
    rw [hyperbolicChartGradientDensity_eq_hypGradNormSq]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro z
    exact hyperbolicChartGradientDensity_modular F S z

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
