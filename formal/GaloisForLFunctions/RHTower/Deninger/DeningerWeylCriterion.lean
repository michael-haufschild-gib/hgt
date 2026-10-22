import GaloisForLFunctions.RHTower.Deninger.DeningerTorusFlow

/-!
# Weyl's criterion for a linear flow on the torus

A linear flow whose velocity vector pairs nontrivially with every nonzero integer vector is
equidistributed: the time average of every continuous function converges to its mean over the
torus.

The proof is the classical three-step argument.  On the exponential monomials the two sides agree,
because a nontrivial character oscillates and has vanishing long-time average while its mean is
zero by orthogonality.  The functions for which the two sides agree form a submodule, and that
submodule is closed because the averaging operators and the mean are all bounded by the uniform
norm.  Stone–Weierstrass makes the span of the monomials uniformly dense, so the submodule is
everything.

* `deningerMFourier_integral_eq_zero` : a nontrivial character has zero mean.
* `deningerFlowAverage_norm_le` : the averaging operators are uniformly bounded.
* `deningerMeanSubmodule` : the functions whose averages converge to their mean.
* `deningerWeyl` : Weyl's criterion.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Filter Topology

/-- The circle is normalised to total mass one, as in the multivariate Fourier theory. -/
noncomputable local instance deningerWeylCriterionMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance deningerWeylCriterionIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance deningerWeylCriterionIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Weyl

variable {d : Type*} [Fintype d]

/-- A continuous function on the torus is integrable. -/
theorem deningerTorusIntegrable (f : C(UnitAddTorus d, ℂ)) :
    Integrable (fun x => f x) (volume : Measure (UnitAddTorus d)) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **A nontrivial character has zero mean on the torus.**  This is orthogonality to the constant
function. -/
theorem deningerMFourier_integral_eq_zero {n : d → ℤ} (hn : n ≠ 0) :
    ∫ x : UnitAddTorus d, mFourier n x = 0 := by
  have h : (inner ℂ (mFourierLp (d := d) 2 0) (mFourierLp (d := d) 2 n) : ℂ) = 0 :=
    orthonormal_mFourier.2 (Ne.symm hn)
  rw [ContinuousMap.inner_toLp] at h
  simpa [mFourier_zero] using h

/-- The trivial character has mean one. -/
theorem deningerMFourier_integral_zero :
    ∫ x : UnitAddTorus d, mFourier (0 : d → ℤ) x = 1 := by
  simp [mFourier_zero]

/-- The mean over the torus is bounded by the uniform norm. -/
theorem deningerTorusIntegral_norm_le (f : C(UnitAddTorus d, ℂ)) :
    ‖∫ x : UnitAddTorus d, f x‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus d)))
    (C := ‖f‖) (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  simpa [probReal_univ] using h

omit [Fintype d] in
theorem deningerFlowAverage_sub (lam : d → ℝ) (f g : C(UnitAddTorus d, ℂ)) (T : ℝ) :
    deningerFlowAverage lam (f - g) T
      = deningerFlowAverage lam f T - deningerFlowAverage lam g T := by
  have hf : IntervalIntegrable (fun t => f (deningerTorusFlow lam t)) volume 0 T :=
    (f.continuous.comp (deningerTorusFlow_continuous lam)).intervalIntegrable 0 T
  have hg : IntervalIntegrable (fun t => g (deningerTorusFlow lam t)) volume 0 T :=
    (g.continuous.comp (deningerTorusFlow_continuous lam)).intervalIntegrable 0 T
  rw [deningerFlowAverage, deningerFlowAverage, deningerFlowAverage, ← mul_sub]
  congr 1
  rw [← intervalIntegral.integral_sub hf hg]
  rfl

omit [Fintype d] in
theorem deningerFlowAverage_add (lam : d → ℝ) (f g : C(UnitAddTorus d, ℂ)) (T : ℝ) :
    deningerFlowAverage lam (f + g) T
      = deningerFlowAverage lam f T + deningerFlowAverage lam g T := by
  have hf : IntervalIntegrable (fun t => f (deningerTorusFlow lam t)) volume 0 T :=
    (f.continuous.comp (deningerTorusFlow_continuous lam)).intervalIntegrable 0 T
  have hg : IntervalIntegrable (fun t => g (deningerTorusFlow lam t)) volume 0 T :=
    (g.continuous.comp (deningerTorusFlow_continuous lam)).intervalIntegrable 0 T
  rw [deningerFlowAverage, deningerFlowAverage, deningerFlowAverage, ← mul_add]
  congr 1
  rw [← intervalIntegral.integral_add hf hg]
  rfl

omit [Fintype d] in
theorem deningerFlowAverage_smul (lam : d → ℝ) (c : ℂ) (f : C(UnitAddTorus d, ℂ)) (T : ℝ) :
    deningerFlowAverage lam (c • f) T = c * deningerFlowAverage lam f T := by
  rw [deningerFlowAverage, deningerFlowAverage]
  rw [show (∫ t in (0 : ℝ)..T, (c • f) (deningerTorusFlow lam t))
      = ∫ t in (0 : ℝ)..T, c * f (deningerTorusFlow lam t) from rfl,
    intervalIntegral.integral_const_mul]
  ring

omit [Fintype d] in
theorem deningerFlowAverage_zero (lam : d → ℝ) (T : ℝ) :
    deningerFlowAverage lam 0 T = 0 := by
  rw [deningerFlowAverage]
  simp

omit [Fintype d] in
/-- **The averaging operators are bounded by the uniform norm.**  The integrand is bounded by the
uniform norm on an interval of length `T`, and the average divides by `T`. -/
theorem deningerFlowAverage_norm_le (lam : d → ℝ) (f : C(UnitAddTorus d, ℂ)) {T : ℝ}
    (hT : 0 < T) : ‖deningerFlowAverage lam f T‖ ≤ ‖f‖ := by
  have hb : ‖∫ t in (0 : ℝ)..T, f (deningerTorusFlow lam t)‖ ≤ ‖f‖ * |T - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => f.norm_coe_le_norm _
  rw [sub_zero, abs_of_pos hT] at hb
  rw [deningerFlowAverage, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hT]
  have hstep : T⁻¹ * ‖∫ t in (0 : ℝ)..T, f (deningerTorusFlow lam t)‖ ≤ T⁻¹ * (‖f‖ * T) :=
    mul_le_mul_of_nonneg_left hb (inv_pos.mpr hT).le
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- The continuous functions whose flow averages converge to their mean over the torus. -/
def deningerMeanSubmodule (lam : d → ℝ) : Submodule ℂ C(UnitAddTorus d, ℂ) where
  carrier := {f | Tendsto (deningerFlowAverage lam f) atTop (nhds (∫ x : UnitAddTorus d, f x))}
  add_mem' := by
    intro f g hf hg
    have hint : (∫ x : UnitAddTorus d, (f + g) x)
        = (∫ x : UnitAddTorus d, f x) + ∫ x : UnitAddTorus d, g x :=
      integral_add (deningerTorusIntegrable f) (deningerTorusIntegrable g)
    show Tendsto (deningerFlowAverage lam (f + g)) atTop _
    rw [hint]
    have := (hf.add hg).congr fun T => (deningerFlowAverage_add lam f g T).symm
    exact this
  zero_mem' := by
    show Tendsto (deningerFlowAverage lam 0) atTop _
    have hint : (∫ x : UnitAddTorus d, (0 : C(UnitAddTorus d, ℂ)) x) = 0 := by simp
    rw [hint]
    exact (tendsto_const_nhds (x := (0 : ℂ)) (f := (atTop : Filter ℝ))).congr
      fun T => (deningerFlowAverage_zero lam T).symm
  smul_mem' := by
    intro c f hf
    have hint : (∫ x : UnitAddTorus d, (c • f) x) = c • ∫ x : UnitAddTorus d, f x :=
      integral_smul c (fun x => f x)
    show Tendsto (deningerFlowAverage lam (c • f)) atTop _
    rw [hint, smul_eq_mul]
    exact (hf.const_mul c).congr fun T => (deningerFlowAverage_smul lam c f T).symm

theorem deningerMem_meanSubmodule (lam : d → ℝ) (f : C(UnitAddTorus d, ℂ)) :
    f ∈ deningerMeanSubmodule lam ↔
      Tendsto (deningerFlowAverage lam f) atTop (nhds (∫ x : UnitAddTorus d, f x)) := Iff.rfl

/-- **The set of functions with convergent averages is closed.**  Uniformly close functions have
uniformly close averages and uniformly close means, so the convergence passes to uniform limits. -/
theorem deningerMeanSubmodule_isClosed (lam : d → ℝ) :
    IsClosed ((deningerMeanSubmodule lam : Submodule ℂ C(UnitAddTorus d, ℂ)) :
      Set C(UnitAddTorus d, ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro f hf
  show Tendsto (deningerFlowAverage lam f) atTop (nhds (∫ x : UnitAddTorus d, f x))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by linarith)
  have hgt : Tendsto (deningerFlowAverage lam g) atTop (nhds (∫ x : UnitAddTorus d, g x)) := hg
  rw [Metric.tendsto_atTop] at hgt
  obtain ⟨N, hN⟩ := hgt (ε / 3) (by linarith)
  refine ⟨max N 1, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos (le_trans (le_max_right N 1) hT)
  have h1 : dist (deningerFlowAverage lam f T) (deningerFlowAverage lam g T) < ε / 3 := by
    rw [dist_eq_norm, ← deningerFlowAverage_sub]
    calc ‖deningerFlowAverage lam (f - g) T‖ ≤ ‖f - g‖ :=
          deningerFlowAverage_norm_le lam _ hT0
      _ = dist f g := (dist_eq_norm f g).symm
      _ < ε / 3 := hdist
  have h2 : dist (deningerFlowAverage lam g T) (∫ x : UnitAddTorus d, g x) < ε / 3 :=
    hN T (le_trans (le_max_left N 1) hT)
  have h3 : dist (∫ x : UnitAddTorus d, g x) (∫ x : UnitAddTorus d, f x) < ε / 3 := by
    rw [dist_eq_norm, ← integral_sub (deningerTorusIntegrable g) (deningerTorusIntegrable f)]
    calc ‖∫ x : UnitAddTorus d, (g x - f x)‖ ≤ ‖g - f‖ := by
          simpa using deningerTorusIntegral_norm_le (g - f)
      _ = dist g f := (dist_eq_norm g f).symm
      _ < ε / 3 := by rwa [dist_comm]
  have htri := dist_triangle4 (deningerFlowAverage lam f T) (deningerFlowAverage lam g T)
    (∫ x : UnitAddTorus d, g x) (∫ x : UnitAddTorus d, f x)
  linarith

/-- **Weyl's criterion.**  If the velocity vector pairs nontrivially with every nonzero integer
vector, then the time averages of every continuous function along the linear flow converge to its
mean over the torus. -/
theorem deningerWeyl (lam : d → ℝ)
    (hlam : ∀ n : d → ℤ, n ≠ 0 → deningerFrequency n lam ≠ 0) (f : C(UnitAddTorus d, ℂ)) :
    Tendsto (deningerFlowAverage lam f) atTop (nhds (∫ x : UnitAddTorus d, f x)) := by
  have hchar : ∀ n : d → ℤ, mFourier n ∈ deningerMeanSubmodule lam := by
    intro n
    rw [deningerMem_meanSubmodule]
    by_cases hn : n = 0
    · subst hn
      rw [deningerMFourier_integral_zero]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)) (f := (atTop : Filter ℝ)))
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact (deningerFlowAverage_mFourier_zero_freq lam hT.ne').symm
    · rw [deningerMFourier_integral_eq_zero hn]
      exact deningerFlowAverage_mFourier_tendsto n lam (hlam n hn)
  have hsub : Submodule.span ℂ (Set.range (mFourier (d := d))) ≤ deningerMeanSubmodule lam :=
    Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hchar n)
  have htop := Submodule.topologicalClosure_minimal _ hsub (deningerMeanSubmodule_isClosed lam)
  rw [span_mFourier_closure_eq_top] at htop
  exact htop Submodule.mem_top

end Weyl

end RHTower
