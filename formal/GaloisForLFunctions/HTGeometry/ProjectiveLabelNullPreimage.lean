import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage
import GaloisForLFunctions.HTGeometry.ProjectiveSingularContinuousResidual

/-!
# Analytic null-preimage law for the Nevanlinna projective label

This file discharges the null-preimage condition isolated by the residual
carrier transport. The proof uses the standard Cauchy representative of
projective Lebesgue measure, the nonconstant projective derivative numerator,
and the real-analytic null-preimage law.
-/

open MeasureTheory Set Filter Metric Topology OnePoint
open scoped ENNReal NNReal Topology OnePoint

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem volume_absolutelyContinuous_standardCauchy :
    (volume : Measure ℝ) ≪ ProbabilityTheory.cauchyMeasure 0 1 := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (γ := 1) (by norm_num)]
  apply withDensity_absolutelyContinuous'
  · exact (ProbabilityTheory.measurable_cauchyPDF 0 1).aemeasurable
  · filter_upwards [] with x
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (ProbabilityTheory.cauchyPDF_pos 0 (by norm_num) x))

theorem projectiveLebesgueProbability_null_finiteChart
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hnull : (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0) :
    (volume : Measure ℝ) (((↑) : ℝ → OnePoint ℝ) ⁻¹' E) = 0 := by
  apply volume_absolutelyContinuous_standardCauchy
  rw [← Measure.map_apply OnePoint.continuous_coe.measurable hE]
  rw [← projectiveLebesgueProbability_toMeasure]
  exact hnull

/-- Numerator of the derivative of the real affine projective label `-D/C`. -/
def realProjectiveDerivativeNumerator (C D : ℝ → ℝ) (x : ℝ) : ℝ :=
  D x * deriv C x - deriv D x * C x

theorem realProjectiveDerivativeNumerator_analytic
    {C D : ℝ → ℝ} (hC : AnalyticOnNhd ℝ C univ)
    (hD : AnalyticOnNhd ℝ D univ) :
    AnalyticOnNhd ℝ (realProjectiveDerivativeNumerator C D) univ := by
  intro x _
  exact ((hD x trivial).mul (hC.deriv x trivial)).sub
    ((hD.deriv x trivial).mul (hC x trivial))

theorem deriv_neg_div_eq_realProjectiveDerivativeNumerator_div_sq
    {C D : ℝ → ℝ} (hC : AnalyticOnNhd ℝ C univ)
    (hD : AnalyticOnNhd ℝ D univ) {x : ℝ} (hCx : C x ≠ 0) :
    deriv (fun y => -D y / C y) x =
      realProjectiveDerivativeNumerator C D x / C x ^ 2 := by
  have hCdiff : Differentiable ℝ C := differentiableOn_univ.mp hC.differentiableOn
  have hDdiff : Differentiable ℝ D := differentiableOn_univ.mp hD.differentiableOn
  have hneg : HasDerivAt (fun y => -D y) (-deriv D x) x :=
    (hDdiff x).hasDerivAt.neg
  have hdiv := hneg.div (hCdiff x).hasDerivAt hCx
  change deriv (((fun y => -D y) / C)) x = _
  rw [hdiv.deriv]
  unfold realProjectiveDerivativeNumerator
  ring

theorem realProjectiveDerivativeNumerator_ne_zero
    {C D : ℝ → ℝ} (hC : AnalyticOnNhd ℝ C univ)
    (hD : AnalyticOnNhd ℝ D univ)
    (hnoCommon : ∀ x, ¬ (C x = 0 ∧ D x = 0))
    {p c : ℝ} (hCp : C p = 0) (hCc : C c ≠ 0) :
    realProjectiveDerivativeNumerator C D ≠ 0 := by
  intro hN
  have hopen : IsOpen {x : ℝ | C x ≠ 0} :=
    (continuousOn_univ.mp hC.continuousOn).isOpen_preimage
      {y : ℝ | y ≠ 0} isOpen_ne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen c hCc
  let q : ℝ → ℝ := fun x => -D x / C x
  have hCdiff : Differentiable ℝ C := differentiableOn_univ.mp hC.differentiableOn
  have hDdiff : Differentiable ℝ D := differentiableOn_univ.mp hD.differentiableOn
  have hqdiff : DifferentiableOn ℝ q (ball c r) := by
    apply DifferentiableOn.div hDdiff.neg.differentiableOn hCdiff.differentiableOn
    intro x hx
    exact hball hx
  have hqderiv : (ball c r).EqOn (deriv q) 0 := by
    intro x hx
    rw [deriv_neg_div_eq_realProjectiveDerivativeNumerator_div_sq
      hC hD (hball hx)]
    have hNx : realProjectiveDerivativeNumerator C D x = 0 := by
      simpa using congrFun hN x
    rw [hNx, zero_div]
    rfl
  have hqconst : ∀ x ∈ ball c r, q x = q c := by
    intro x hx
    exact isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c r).isPreconnected hqdiff hqderiv hx (mem_ball_self hr)
  let G : ℝ → ℝ := fun x => D x * C c - D c * C x
  have hGzeroBall : ∀ x ∈ ball c r, G x = 0 := by
    intro x hx
    have hqeq := hqconst x hx
    have hcross := (div_eq_div_iff (hball hx) hCc).mp hqeq
    dsimp [G]
    rw [sub_eq_zero]
    simpa only [neg_mul, neg_inj] using hcross
  have hGevent : G =ᶠ[𝓝 c] 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with x hx
    exact hGzeroBall x hx
  have hGan : AnalyticOnNhd ℝ G univ := by
    intro x _
    exact ((hD x trivial).mul analyticAt_const).sub
      (analyticAt_const.mul (hC x trivial))
  have hzeroAn : AnalyticOnNhd ℝ (0 : ℝ → ℝ) univ :=
    fun _ _ => analyticAt_const
  have hGzero : G = 0 := hGan.eq_of_eventuallyEq hzeroAn hGevent
  have hGp := congrFun hGzero p
  have hDp : D p ≠ 0 := by
    intro h
    exact hnoCommon p ⟨hCp, h⟩
  dsimp [G] at hGp
  rw [hCp, mul_zero, sub_zero] at hGp
  exact hDp (mul_eq_zero.mp hGp |>.resolve_right hCc)

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

theorem finiteDenominatorFiber_nonempty (tau : ℝ) :
    F.matrix.finiteDenominatorFiber tau |>.Nonempty := by
  by_contra h
  have hempty : F.matrix.finiteDenominatorFiber tau = ∅ := not_nonempty_iff_eq_empty.mp h
  have hcarry := F.finite_carried tau
  rw [hempty] at hcarry
  simp at hcarry

theorem infinityDenominatorFiber_nonempty :
    F.matrix.infinityDenominatorFiber.Nonempty := by
  by_contra h
  have hempty : F.matrix.infinityDenominatorFiber = ∅ := not_nonempty_iff_eq_empty.mp h
  have hcarry := F.infinity_carried
  rw [hempty] at hcarry
  simp at hcarry

theorem affineProjectiveLabel_deriv_not_eventually_zero
    (hC : AnalyticOnNhd ℝ F.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.matrix.d univ) :
    ∀ x, F.matrix.c x ≠ 0 →
      ¬ ∀ᶠ y in 𝓝 x, deriv (fun z => -F.matrix.d z / F.matrix.c z) y = 0 := by
  obtain ⟨p, hp⟩ := F.infinityDenominatorFiber_nonempty
  obtain ⟨c, hc⟩ := F.finiteDenominatorFiber_nonempty 0
  have hCp : F.matrix.c p = 0 := hp
  have hDc : F.matrix.d c = 0 := by
    change F.matrix.c c * 0 + F.matrix.d c = 0 at hc
    simpa using hc
  have hCc : F.matrix.c c ≠ 0 := by
    intro h
    exact F.matrix.C_D_ne_zero c ⟨h, hDc⟩
  have hNne : realProjectiveDerivativeNumerator F.matrix.c F.matrix.d ≠ 0 :=
    realProjectiveDerivativeNumerator_ne_zero hC hD F.matrix.C_D_ne_zero hCp hCc
  have hNan := realProjectiveDerivativeNumerator_analytic hC hD
  have hzeroAn : AnalyticOnNhd ℝ (0 : ℝ → ℝ) univ :=
    fun _ _ => analyticAt_const
  intro x hCx hflat
  have hCev : ∀ᶠ y in 𝓝 x, F.matrix.c y ≠ 0 :=
    (continuousOn_univ.mp hC.continuousOn).continuousAt.eventually_ne hCx
  have hNev : realProjectiveDerivativeNumerator F.matrix.c F.matrix.d =ᶠ[𝓝 x] 0 := by
    filter_upwards [hCev, hflat] with y hCy hdy
    rw [deriv_neg_div_eq_realProjectiveDerivativeNumerator_div_sq hC hD hCy] at hdy
    exact (div_eq_zero_iff.mp hdy).resolve_right (pow_ne_zero 2 hCy)
  exact hNne (hNan.eq_of_eventuallyEq hzeroAn hNev)

/-- A real-analytic Nevanlinna projective label pulls projective-Lebesgue-null
Borel sets back to real-Lebesgue-null sets. -/
theorem projectiveLabel_preimage_volume_eq_zero
    (hC : AnalyticOnNhd ℝ F.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.matrix.d univ)
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hnull : (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0) :
    (volume : Measure ℝ) (F.matrix.projectiveLabel ⁻¹' E) = 0 := by
  let U : Set ℝ := {x | F.matrix.c x ≠ 0}
  let q : ℝ → ℝ := fun x => -F.matrix.d x / F.matrix.c x
  have hUopen : IsOpen U :=
    (continuousOn_univ.mp hC.continuousOn).isOpen_preimage
      {y : ℝ | y ≠ 0} isOpen_ne
  have hqAnalytic : AnalyticOnNhd ℝ q U := by
    intro x hx
    exact (hD x trivial).neg.div (hC x trivial) hx
  have hqNonflat : ∀ x ∈ U, ¬ ∀ᶠ y in 𝓝 x, deriv q y = 0 := by
    intro x hx
    exact F.affineProjectiveLabel_deriv_not_eventually_zero hC hD x hx
  let finitePart : Set ℝ := ((↑) : ℝ → OnePoint ℝ) ⁻¹' E
  have hfiniteNull : (volume : Measure ℝ) finitePart = 0 :=
    projectiveLebesgueProbability_null_finiteChart hE hnull
  have hregularNull : volume (q ⁻¹' finitePart ∩ U) = 0 :=
    analyticOnNhd_preimage_volume_eq_zero_of_deriv_not_eventually_zero
      hUopen hqAnalytic hqNonflat hfiniteNull
  obtain ⟨c, hc⟩ := F.finiteDenominatorFiber_nonempty 0
  have hDc : F.matrix.d c = 0 := by
    change F.matrix.c c * 0 + F.matrix.d c = 0 at hc
    simpa using hc
  have hCc : F.matrix.c c ≠ 0 := by
    intro h
    exact F.matrix.C_D_ne_zero c ⟨h, hDc⟩
  have hpolesCountable : {x | F.matrix.c x = 0}.Countable :=
    analytic_zero_set_countable hC ⟨c, hCc⟩
  have hpolesNull : volume {x | F.matrix.c x = 0} = 0 :=
    hpolesCountable.measure_zero volume
  apply measure_mono_null ?_ (measure_union_null hregularNull hpolesNull)
  intro x hx
  by_cases hCx : F.matrix.c x = 0
  · exact Or.inr hCx
  · apply Or.inl
    refine ⟨?_, hCx⟩
    change ((q x : ℝ) : OnePoint ℝ) ∈ E
    simpa [q, NevanlinnaMatrixData.projectiveLabel, hCx] using hx

/-- Real analyticity discharges the sole null-preimage hypothesis in the
transported carrier singularity theorem. -/
theorem singularContinuousParameterCarrierPhase_mutuallySingular_volume_of_analytic
    (hC : AnalyticOnNhd ℝ F.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.matrix.d univ)
    (nu : F.carrierRange)
    (hnu : nu ∈ F.singularContinuousParameterCarrierPhase) :
    (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) := by
  exact F.singularContinuousParameterCarrierPhase_mutuallySingular_volume
    (fun _ hE hnull => F.projectiveLabel_preimage_volume_eq_zero hC hD hE hnull)
    nu hnu

/-- Every carrier in the residual transported phase is singular continuous
whenever the lower Nevanlinna row is real analytic. -/
theorem singularContinuousParameterCarrierPhase_isSingularContinuous_of_analytic
    (hC : AnalyticOnNhd ℝ F.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.matrix.d univ)
    (nu : F.carrierRange)
    (hnu : nu ∈ F.singularContinuousParameterCarrierPhase) :
    NoAtoms (nu.1 : Measure ℝ) ∧
      (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) :=
  ⟨F.singularContinuousParameterCarrierPhase_noAtoms nu hnu,
    F.singularContinuousParameterCarrierPhase_mutuallySingular_volume_of_analytic
      hC hD nu hnu⟩

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
