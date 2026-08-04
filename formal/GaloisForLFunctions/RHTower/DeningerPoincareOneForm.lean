import GaloisForLFunctions.RHTower.DeningerStageDeRham
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Poincaré lemma for holomorphic one-forms

A holomorphic one-form on a finite-dimensional complex vector space whose derivative is symmetric —
the closedness condition in degree one — has a primitive, given by integrating the form along the
segment from the origin.  The proof differentiates under the integral sign and uses the symmetry to
recognize the integrand as a total derivative in the segment parameter.

* `deningerHomotopyPrimitive` : the integral of a one-form along the segment to the origin.
* `deningerHomotopyDeriv` : the derivative of the integrand in the base point.
* `deningerExists_primitive_of_symm` : a closed holomorphic one-form has a primitive.
-/

namespace RHTower

open scoped Topology

section Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The scaling of the base point by a segment parameter, as a continuous linear map. -/
noncomputable def deningerScale (t : ℝ) : E →L[ℂ] E :=
  (t : ℂ) • ContinuousLinearMap.id ℂ E

omit [FiniteDimensional ℂ E] in
@[simp]
theorem deningerScale_apply (t : ℝ) (x : E) : deningerScale t x = (t : ℂ) • x := rfl

/-- **The homotopy primitive of a one-form**: its integral along the segment from the origin. -/
noncomputable def deningerHomotopyPrimitive (ω : E → (E →L[ℂ] ℂ)) (w : E) : ℂ :=
  ∫ t in (0 : ℝ)..1, ω (deningerScale t w) w

/-- The derivative in the base point of the integrand of the homotopy primitive. -/
noncomputable def deningerHomotopyDeriv (ω : E → (E →L[ℂ] ℂ)) (x : E) (t : ℝ) : E →L[ℂ] ℂ :=
  ω (deningerScale t x) + ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t)).flip x

omit [FiniteDimensional ℂ E] in
theorem deningerHomotopyDeriv_apply (ω : E → (E →L[ℂ] ℂ)) (x : E) (t : ℝ) (u : E) :
    deningerHomotopyDeriv ω x t u =
      ω (deningerScale t x) u + (fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u) x := rfl

omit [FiniteDimensional ℂ E] in
/-- The integrand of the homotopy primitive is differentiable in the base point. -/
theorem deningerHomotopyDeriv_hasFDerivAt {ω : E → (E →L[ℂ] ℂ)}
    (hana : AnalyticOnNhd ℂ ω Set.univ) (x : E) (t : ℝ) :
    HasFDerivAt (fun y : E => ω (deningerScale t y) y) (deningerHomotopyDeriv ω x t) x := by
  have hc : HasFDerivAt (fun y : E => ω (deningerScale t y))
      ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t)) x :=
    ((hana _ (Set.mem_univ _)).differentiableAt.hasFDerivAt).comp x (deningerScale t).hasFDerivAt
  have h := hc.clm_apply (hasFDerivAt_id x)
  rwa [ContinuousLinearMap.comp_id] at h

/-- The compact set swept by the segments from the origin to a ball. -/
theorem deningerScale_image_isCompact (w₀ : E) :
    IsCompact ((fun p : ℝ × E => (p.1 : ℂ) • p.2) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)) := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  refine IsCompact.image ((isCompact_Icc).prod (isCompact_closedBall w₀ 1)) ?_
  fun_prop

omit [FiniteDimensional ℂ E] in
theorem deningerScale_mem_image {w₀ : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : E}
    (hx : x ∈ Metric.closedBall w₀ 1) :
    deningerScale t x ∈ (fun p : ℝ × E => (p.1 : ℂ) • p.2) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1) :=
  ⟨(t, x), ⟨ht, hx⟩, rfl⟩

end Poincare

end RHTower

namespace RHTower

section PoincareMain

open MeasureTheory intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- The integrand of the homotopy primitive, in the segment parameter, is continuous. -/
theorem deningerHomotopyIntegrand_continuous {ω : E → (E →L[ℂ] ℂ)} (hcont : Continuous ω) (x : E) :
    Continuous fun t : ℝ => ω (deningerScale t x) x := by
  have h1 : Continuous fun t : ℝ => ((t : ℂ) • x) := by fun_prop
  have h2 : Continuous fun t : ℝ => ω ((t : ℂ) • x) := hcont.comp h1
  exact (ContinuousLinearMap.apply ℂ ℂ x).continuous.comp h2

omit [FiniteDimensional ℂ E] in
/-- The derivative of the integrand, in the segment parameter, is continuous. -/
theorem deningerHomotopyDeriv_continuous {ω : E → (E →L[ℂ] ℂ)} (hcont : Continuous ω)
    (hcont' : Continuous (fderiv ℂ ω)) (x : E) :
    Continuous fun t : ℝ => deningerHomotopyDeriv ω x t := by
  have hscale : Continuous fun t : ℝ => (deningerScale t : E →L[ℂ] E) := by
    have : Continuous fun t : ℝ => ((t : ℂ) : ℂ) := by fun_prop
    exact this.smul continuous_const
  have hpoint : Continuous fun t : ℝ => deningerScale t x :=
    (ContinuousLinearMap.apply ℂ E x).continuous.comp hscale
  have h1 : Continuous fun t : ℝ => ω (deningerScale t x) := hcont.comp hpoint
  have h2 : Continuous fun t : ℝ => fderiv ℂ ω (deningerScale t x) := hcont'.comp hpoint
  have h3 : Continuous fun t : ℝ =>
      (fderiv ℂ ω (deningerScale t x)).comp (deningerScale t) :=
    isBoundedBilinearMap_comp.continuous.comp (h2.prodMk hscale)
  have hflip : ∀ A : E →L[ℂ] (E →L[ℂ] ℂ),
      A.flip x = (ContinuousLinearMap.apply ℂ ℂ x).comp A := by
    intro A
    ext u
    rfl
  have h4 : Continuous fun t : ℝ =>
      ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t)).flip x := by
    simp only [hflip]
    exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk h3)
  exact h1.add h4

/-- The real-linear derivative of the coordinate embedding. -/
theorem deningerRealCast_hasDerivAt (t : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
  have h := Complex.ofRealCLM.hasDerivAt (x := t)
  rw [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
  exact h

omit [FiniteDimensional ℂ E] in
/-- **The integrand of the homotopy primitive is a total derivative in the segment parameter**, by
the symmetry of the derivative of the form. -/
theorem deningerHomotopyDeriv_eq_deriv {ω : E → (E →L[ℂ] ℂ)}
    (hana : AnalyticOnNhd ℂ ω Set.univ)
    (hsymm : ∀ w u v : E, fderiv ℂ ω w u v = fderiv ℂ ω w v u) (w₀ u : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * (ω (deningerScale t w₀) u))
      (deningerHomotopyDeriv ω w₀ t u) t := by
  have hcurve : HasDerivAt (fun t : ℝ => (t : ℂ) • w₀) w₀ t := by
    have h := (deningerRealCast_hasDerivAt t).smul_const w₀
    rw [one_smul] at h
    exact h
  have hω1 : HasDerivAt (fun t : ℝ => ω ((t : ℂ) • w₀))
      ((fderiv ℂ ω ((t : ℂ) • w₀)) w₀) t := by
    have hfd := ((hana _ (Set.mem_univ ((t : ℂ) • w₀))).differentiableAt.hasFDerivAt)
    have h := (hfd.restrictScalars ℝ).comp_hasDerivAt t hcurve
    exact h
  have hω2 : HasDerivAt (fun t : ℝ => ω ((t : ℂ) • w₀) u)
      ((fderiv ℂ ω ((t : ℂ) • w₀)) w₀ u) t := by
    have h := (((ContinuousLinearMap.apply ℂ ℂ u).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
      t hω1
    exact h
  have hprod := (deningerRealCast_hasDerivAt t).mul hω2
  have hval : (1 : ℂ) * ω ((t : ℂ) • w₀) u +
      (t : ℂ) * ((fderiv ℂ ω ((t : ℂ) • w₀)) w₀ u) = deningerHomotopyDeriv ω w₀ t u := by
    simp only [deningerHomotopyDeriv_apply, deningerScale_apply, one_mul]
    rw [hsymm ((t : ℂ) • w₀) ((t : ℂ) • u) w₀, map_smul, smul_eq_mul]
  rw [hval] at hprod
  exact hprod

/-- **The Poincaré lemma in degree one**: a holomorphic one-form whose derivative is symmetric has
a primitive, namely its integral along the segment from the origin. -/
theorem deningerHomotopyPrimitive_hasFDerivAt {ω : E → (E →L[ℂ] ℂ)}
    (hana : AnalyticOnNhd ℂ ω Set.univ)
    (hsymm : ∀ w u v : E, fderiv ℂ ω w u v = fderiv ℂ ω w v u) (w₀ : E) :
    HasFDerivAt (deningerHomotopyPrimitive ω) (ω w₀) w₀ := by
  have hcont : Continuous ω := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hana x (Set.mem_univ x)).continuousAt
  have hana' : AnalyticOnNhd ℂ (fderiv ℂ ω) Set.univ := hana.fderiv_of_isOpen isOpen_univ
  have hcont' : Continuous (fderiv ℂ ω) := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hana' x (Set.mem_univ x)).continuousAt
  obtain ⟨C₁, hC₁⟩ := (deningerScale_image_isCompact w₀).exists_bound_of_continuousOn
    hcont.continuousOn
  have hcontOn' : ContinuousOn (fderiv ℂ ω) ((fun p : ℝ × E => (p.1 : ℂ) • p.2) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)) := hcont'.continuousOn
  obtain ⟨C₂, hC₂⟩ : ∃ C : ℝ, ∀ x ∈ ((fun p : ℝ × E => (p.1 : ℂ) • p.2) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)), ‖fderiv ℂ ω x‖ ≤ C := by
    exact (deningerScale_image_isCompact w₀).exists_bound_of_continuousOn hcontOn' 
  set B : ℝ := max C₁ 0 + max C₂ 0 * (‖w₀‖ + 1) with hB
  have hBnonneg : 0 ≤ B := by
    have h1 : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
    have h2 : (0 : ℝ) ≤ max C₂ 0 * (‖w₀‖ + 1) :=
      mul_nonneg (le_max_right _ _) (by positivity)
    exact add_nonneg h1 h2
  have hbound : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.ball w₀ 1,
      ‖deningerHomotopyDeriv ω x t‖ ≤ B := by
    intro t ht x hx
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hxc : x ∈ Metric.closedBall w₀ 1 := Metric.ball_subset_closedBall hx
    have hmem := deningerScale_mem_image ht01 hxc
    have hxn : ‖x‖ ≤ ‖w₀‖ + 1 := by
      have := Metric.mem_closedBall.1 hxc
      have h := norm_le_norm_add_norm_sub' x w₀
      calc ‖x‖ ≤ ‖w₀‖ + ‖x - w₀‖ := by
            have := norm_add_le w₀ (x - w₀)
            simpa using this
        _ ≤ ‖w₀‖ + 1 := by
            have hd : ‖x - w₀‖ ≤ 1 := by
              rw [← dist_eq_norm]
              exact Metric.mem_closedBall.1 hxc
            linarith
    have htn : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_ofReal]
      rw [abs_of_nonneg ht01.1]
      exact ht01.2
    refine ContinuousLinearMap.opNorm_le_bound _ hBnonneg fun u => ?_
    rw [deningerHomotopyDeriv_apply]
    have hterm1 : ‖ω (deningerScale t x) u‖ ≤ max C₁ 0 * ‖u‖ :=
      le_trans ((ω (deningerScale t x)).le_opNorm u)
        (mul_le_mul_of_nonneg_right (le_trans (hC₁ _ hmem) (le_max_left _ _)) (norm_nonneg u))
    have hterm2 : ‖(fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u) x‖ ≤
        max C₂ 0 * (‖w₀‖ + 1) * ‖u‖ := by
      have h1 : ‖(fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u) x‖ ≤
          ‖(fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u)‖ * ‖x‖ :=
        ((fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u)).le_opNorm x
      have h2 : ‖(fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u)‖ ≤
          max C₂ 0 * ‖u‖ := by
        refine le_trans ((fderiv ℂ ω (deningerScale t x)).le_opNorm _) ?_
        have hb : ‖fderiv ℂ ω (deningerScale t x)‖ ≤ max C₂ 0 :=
          le_trans (hC₂ _ hmem) (le_max_left _ _)
        have hs : ‖(t : ℂ) • u‖ ≤ ‖u‖ := by
          rw [norm_smul]
          calc ‖(t : ℂ)‖ * ‖u‖ ≤ 1 * ‖u‖ :=
                mul_le_mul_of_nonneg_right htn (norm_nonneg u)
            _ = ‖u‖ := one_mul _
        exact mul_le_mul hb hs (norm_nonneg _) (le_max_right _ _)
      calc ‖(fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u) x‖
          ≤ ‖(fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u)‖ * ‖x‖ := h1
        _ ≤ (max C₂ 0 * ‖u‖) * (‖w₀‖ + 1) :=
            mul_le_mul h2 hxn (norm_nonneg x) (mul_nonneg (le_max_right _ _) (norm_nonneg u))
        _ = max C₂ 0 * (‖w₀‖ + 1) * ‖u‖ := by ring
    calc ‖ω (deningerScale t x) u + (fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u) x‖
        ≤ ‖ω (deningerScale t x) u‖ +
          ‖(fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u) x‖ := norm_add_le _ _
      _ ≤ max C₁ 0 * ‖u‖ + max C₂ 0 * (‖w₀‖ + 1) * ‖u‖ := add_le_add hterm1 hterm2
      _ = B * ‖u‖ := by rw [hB]; ring
  have hmain : HasFDerivAt (deningerHomotopyPrimitive ω)
      (∫ t in (0 : ℝ)..1, deningerHomotopyDeriv ω w₀ t) w₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun (x : E) (t : ℝ) => ω (deningerScale t x) x)
      (F' := fun (x : E) (t : ℝ) => deningerHomotopyDeriv ω x t)
      (bound := fun _ : ℝ => B)
      (Metric.ball_mem_nhds w₀ one_pos)
      (Filter.Eventually.of_forall fun x =>
        (deningerHomotopyIntegrand_continuous hcont x).aestronglyMeasurable)
      ((deningerHomotopyIntegrand_continuous hcont w₀).intervalIntegrable 0 1)
      ((deningerHomotopyDeriv_continuous hcont hcont' w₀).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
      (intervalIntegrable_const)
      (Filter.Eventually.of_forall fun t _ x _ => deningerHomotopyDeriv_hasFDerivAt hana x t)
  have hfinal : (∫ t in (0 : ℝ)..1, deningerHomotopyDeriv ω w₀ t) = ω w₀ := by
    have hint : IntervalIntegrable (fun t => deningerHomotopyDeriv ω w₀ t)
        MeasureTheory.volume 0 1 :=
      (deningerHomotopyDeriv_continuous hcont hcont' w₀).intervalIntegrable 0 1
    ext u
    rw [intervalIntegral.integral_of_le zero_le_one,
      ContinuousLinearMap.integral_apply hint.1, ← intervalIntegral.integral_of_le zero_le_one]
    have hcontu : Continuous fun t : ℝ => deningerHomotopyDeriv ω w₀ t u :=
      (ContinuousLinearMap.apply ℂ ℂ u).continuous.comp
        (deningerHomotopyDeriv_continuous hcont hcont' w₀)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => deningerHomotopyDeriv_eq_deriv hana hsymm w₀ u t)
      (hcontu.intervalIntegrable 0 1)]
    simp
  rwa [hfinal] at hmain

end PoincareMain

end RHTower
