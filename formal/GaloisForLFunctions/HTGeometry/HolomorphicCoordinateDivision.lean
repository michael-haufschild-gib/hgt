import GaloisForLFunctions.HTGeometry.DbarCoordinateProduct
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import GaloisForLFunctions.HTGeometry.PolydiscWeierstrass

/-!
# Dividing a holomorphic function by a coordinate

A holomorphic function on a polydisc centred on the divisor of the last coordinate, vanishing on
that divisor, is the coordinate times a holomorphic function.  The quotient is written down: it is
the integral of the last partial derivative along the segment contracting the last coordinate to
zero,
`u(x) = ∫₀¹ (∂ₙf)(x₁,…,xₙ, t·xₙ₊₁) dt`,
and the identity `xₙ₊₁·u = f` is the fundamental theorem of calculus along that segment, the
constant term vanishing because `f` vanishes on the divisor.  The contraction preserves the
polydisc, because its centre lies on the divisor.

* `HTGeometry.coordContract` : the contraction of the last coordinate.
* `HTGeometry.coordDivQuotient` : the quotient.
* `HTGeometry.coordDivQuotient_mul` : the division identity.
-/

namespace HTGeometry

open Complex MeasureTheory intervalIntegral

section Contraction

variable {n : ℕ}

/-- **The contraction of the last coordinate by a factor.** -/
noncomputable def coordContract (t : ℂ) : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = Fin.last n then t • ContinuousLinearMap.proj i else ContinuousLinearMap.proj i

@[simp] theorem coordContract_apply_last (t : ℂ) (x : Fin (n + 1) → ℂ) :
    coordContract t x (Fin.last n) = t * x (Fin.last n) := by
  show (if Fin.last n = Fin.last n then
      (t • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) (Fin.last n))
    else ContinuousLinearMap.proj (Fin.last n)) x = _
  rw [if_pos rfl]
  rfl

@[simp] theorem coordContract_apply_of_ne (t : ℂ) (x : Fin (n + 1) → ℂ) {i : Fin (n + 1)}
    (hi : i ≠ Fin.last n) : coordContract t x i = x i := by
  show (if i = Fin.last n then
      (t • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) i)
    else ContinuousLinearMap.proj i) x = _
  rw [if_neg hi]
  rfl

@[simp] theorem coordContract_one (x : Fin (n + 1) → ℂ) : coordContract 1 x = x := by
  funext i
  by_cases hi : i = Fin.last n
  · subst hi
    rw [coordContract_apply_last, one_mul]
  · rw [coordContract_apply_of_ne _ _ hi]

@[simp] theorem coordContract_zero_last (x : Fin (n + 1) → ℂ) :
    coordContract 0 x (Fin.last n) = 0 := by
  rw [coordContract_apply_last, zero_mul]

/-- **The contraction preserves a polydisc centred on the divisor.** -/
theorem coordContract_mem_ball {c x : Fin (n + 1) → ℂ} {r : ℝ}
    (hc : c (Fin.last n) = 0) (hx : x ∈ Metric.ball c r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    coordContract (t : ℂ) x ∈ Metric.ball c r := by
  have hxr : dist x c < r := Metric.mem_ball.1 hx
  refine Metric.mem_ball.2 (lt_of_le_of_lt ?_ hxr)
  show dist (coordContract (t : ℂ) x) c ≤ dist x c
  refine (dist_pi_le_iff (X := fun _ : Fin (n + 1) => ℂ) (r := dist x c)
    dist_nonneg).2 fun i => ?_
  by_cases hi : i = Fin.last n
  · subst hi
    rw [coordContract_apply_last]
    have hxl : dist ((t : ℂ) * x (Fin.last n)) (c (Fin.last n)) = t * ‖x (Fin.last n)‖ := by
      rw [hc, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    have hdl : ‖x (Fin.last n)‖ = dist (x (Fin.last n)) (c (Fin.last n)) := by
      rw [dist_eq_norm, hc, sub_zero]
    rw [hxl, hdl]
    calc t * dist (x (Fin.last n)) (c (Fin.last n))
        ≤ 1 * dist (x (Fin.last n)) (c (Fin.last n)) :=
          mul_le_mul_of_nonneg_right ht.2 dist_nonneg
      _ = dist (x (Fin.last n)) (c (Fin.last n)) := one_mul _
      _ ≤ dist x c := dist_le_pi_dist x c (Fin.last n)
  · rw [coordContract_apply_of_ne _ _ hi]
    exact dist_le_pi_dist x c i

end Contraction

end HTGeometry

namespace HTGeometry

open Complex MeasureTheory intervalIntegral

section Quotient

variable {n : ℕ}

/-- The last partial derivative of a function of several complex variables. -/
noncomputable def lastCoordDeriv (f : (Fin (n + 1) → ℂ) → ℂ) (x : Fin (n + 1) → ℂ) : ℂ :=
  fderiv ℂ f x (Pi.single (Fin.last n) 1)

/-- **The quotient of a function vanishing on the divisor by the last coordinate**: the average of
the last partial derivative along the segment contracting that coordinate to zero. -/
noncomputable def coordDivQuotient (f : (Fin (n + 1) → ℂ) → ℂ) (x : Fin (n + 1) → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, lastCoordDeriv f (coordContract (t : ℂ) x)

/-- The contraction, as a function of the parameter, is an affine path with constant velocity. -/
theorem hasDerivAt_coordContract (x : Fin (n + 1) → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordContract (s : ℂ) x)
      (Pi.single (Fin.last n) (x (Fin.last n))) t := by
  have hcomp : (fun s : ℝ => coordContract (s : ℂ) x)
      = fun s : ℝ => Function.update x (Fin.last n) ((s : ℂ) * x (Fin.last n)) := by
    funext s
    funext i
    by_cases hi : i = Fin.last n
    · subst hi
      rw [coordContract_apply_last, Function.update_self]
    · rw [coordContract_apply_of_ne _ _ hi, Function.update_of_ne hi]
  rw [hcomp]
  set v : Fin (n + 1) → ℂ := Pi.single (Fin.last n) (x (Fin.last n)) with hv
  set b : Fin (n + 1) → ℂ := Function.update x (Fin.last n) (0 : ℂ) with hb
  have hbase : ∀ s : ℝ, Function.update x (Fin.last n) ((s : ℂ) * x (Fin.last n)) = b + s • v := by
    intro s
    funext i
    by_cases hi : i = Fin.last n
    · subst hi
      rw [Function.update_self]
      show (s : ℂ) * x (Fin.last n) = b (Fin.last n) + (s • v) (Fin.last n)
      rw [hb, Function.update_self, zero_add]
      show _ = s • v (Fin.last n)
      rw [hv, Pi.single_eq_same, Complex.real_smul]
    · rw [Function.update_of_ne hi]
      show x i = b i + (s • v) i
      rw [hb, Function.update_of_ne hi]
      show _ = x i + s • v i
      rw [hv, Pi.single_eq_of_ne hi, smul_zero, add_zero]
  simp only [hbase]
  simpa using ((hasDerivAt_id t).smul_const v).const_add b

end Quotient

end HTGeometry

namespace HTGeometry

open Complex MeasureTheory intervalIntegral

section Division

variable {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ} {c : Fin (n + 1) → ℂ} {r : ℝ}

/-- The last partial derivative of an analytic function is analytic. -/
theorem lastCoordDeriv_analyticOnNhd (hf : AnalyticOnNhd ℂ f (Metric.ball c r)) :
    AnalyticOnNhd ℂ (lastCoordDeriv f) (Metric.ball c r) := by
  have hev : AnalyticOnNhd ℂ (⇑(ContinuousLinearMap.apply ℂ ℂ
      ((Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ)))) Set.univ :=
    (ContinuousLinearMap.apply ℂ ℂ
      ((Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ))).analyticOnNhd Set.univ
  exact hev.comp hf.fderiv (Set.mapsTo_univ _ _)

/-- The derivative of a function along the contraction path. -/
theorem hasDerivAt_comp_coordContract (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    (hc : c (Fin.last n) = 0) {x : Fin (n + 1) → ℂ} (hx : x ∈ Metric.ball c r) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => f (coordContract (s : ℂ) x))
      (x (Fin.last n) * lastCoordDeriv f (coordContract (t : ℂ) x)) t := by
  have hmem : coordContract (t : ℂ) x ∈ Metric.ball c r := coordContract_mem_ball hc hx ht
  have hfd : HasFDerivAt f (fderiv ℂ f (coordContract (t : ℂ) x)) (coordContract (t : ℂ) x) :=
    (hf _ hmem).differentiableAt.hasFDerivAt
  have hcomp := (hfd.restrictScalars ℝ).comp_hasDerivAt t (hasDerivAt_coordContract x t)
  have hsingle : (Pi.single (Fin.last n) (x (Fin.last n)) : Fin (n + 1) → ℂ)
      = x (Fin.last n) • (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) := by
    funext i
    by_cases hi : i = Fin.last n
    · subst hi
      rw [Pi.single_eq_same]
      show _ = x (Fin.last n) •
        (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) (Fin.last n)
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [Pi.single_eq_of_ne hi]
      show _ = x (Fin.last n) • (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) i
      rw [Pi.single_eq_of_ne hi, smul_zero]
  have hval : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ f (coordContract (t : ℂ) x)))
        ((Pi.single (Fin.last n) (x (Fin.last n)) : Fin (n + 1) → ℂ))
      = x (Fin.last n) * lastCoordDeriv f (coordContract (t : ℂ) x) := by
    show fderiv ℂ f (coordContract (t : ℂ) x)
      ((Pi.single (Fin.last n) (x (Fin.last n)) : Fin (n + 1) → ℂ)) = _
    rw [hsingle, map_smul, smul_eq_mul]
    rfl
  rwa [hval] at hcomp

/-- The last partial derivative is continuous along the contraction path. -/
theorem continuousOn_coordDeriv_path (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    (hc : c (Fin.last n) = 0) {x : Fin (n + 1) → ℂ} (hx : x ∈ Metric.ball c r) :
    ContinuousOn (fun t : ℝ => lastCoordDeriv f (coordContract (t : ℂ) x)) (Set.Icc 0 1) := by
  have hpath : Continuous (fun t : ℝ => coordContract (t : ℂ) x) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_coordContract x t).continuousAt
  intro t ht
  show ContinuousWithinAt ((fun z => lastCoordDeriv f z) ∘ fun s : ℝ => coordContract (s : ℂ) x)
    (Set.Icc 0 1) t
  exact ContinuousAt.comp_continuousWithinAt
    ((lastCoordDeriv_analyticOnNhd hf) _ (coordContract_mem_ball hc hx ht)).continuousAt
    hpath.continuousWithinAt

/-- **The division identity.**  The last coordinate times the quotient is the function, because the
fundamental theorem of calculus along the contraction path has no constant term: the function
vanishes on the divisor, where the path starts. -/
theorem coordDivQuotient_mul (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    (hc : c (Fin.last n) = 0)
    (hvanish : ∀ z ∈ Metric.ball c r, z (Fin.last n) = 0 → f z = 0)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ Metric.ball c r) :
    x (Fin.last n) * coordDivQuotient f x = f x := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hcont := continuousOn_coordDeriv_path hf hc hx
  have hint : IntervalIntegrable
      (fun t : ℝ => x (Fin.last n) * lastCoordDeriv f (coordContract (t : ℂ) x))
      volume 0 1 := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [huIcc]
    exact continuousOn_const.mul hcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => f (coordContract (s : ℂ) x))
    (f' := fun t : ℝ => x (Fin.last n) * lastCoordDeriv f (coordContract (t : ℂ) x))
    (fun t htu => hasDerivAt_comp_coordContract hf hc hx (huIcc ▸ htu)) hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hzero : f (coordContract (((0 : ℝ)) : ℂ) x) = 0 :=
    hvanish _ (coordContract_mem_ball hc hx (Set.left_mem_Icc.2 zero_le_one))
      (by rw [coordContract_apply_last, Complex.ofReal_zero, zero_mul])
  rw [coordDivQuotient, hFTC, hzero, sub_zero,
    show ((1 : ℝ) : ℂ) = (1 : ℂ) from Complex.ofReal_one, coordContract_one]

end Division

end HTGeometry

namespace HTGeometry

open Complex MeasureTheory intervalIntegral

section Holomorphy

variable {n : ℕ}

/-- The part of a point away from the last coordinate. -/
noncomputable def coordDrop : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i => if i = Fin.last n then 0 else ContinuousLinearMap.proj i

/-- The last coordinate of a point. -/
noncomputable def coordKeepLast : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i => if i = Fin.last n then ContinuousLinearMap.proj i else 0

theorem coordContract_eq (t : ℂ) :
    coordContract (n := n) t = coordDrop + t • coordKeepLast := by
  refine ContinuousLinearMap.ext fun x => ?_
  funext i
  by_cases hi : i = Fin.last n
  · subst hi
    rw [coordContract_apply_last]
    show _ = (if Fin.last n = Fin.last n then (0 : (Fin (n + 1) → ℂ) →L[ℂ] ℂ)
        else ContinuousLinearMap.proj (Fin.last n)) x
      + t • (if Fin.last n = Fin.last n
        then ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) (Fin.last n)
        else 0) x
    rw [if_pos rfl, if_pos rfl]
    show _ = 0 + t • x (Fin.last n)
    rw [zero_add, smul_eq_mul]
  · rw [coordContract_apply_of_ne _ _ hi]
    show _ = (if i = Fin.last n then (0 : (Fin (n + 1) → ℂ) →L[ℂ] ℂ)
        else ContinuousLinearMap.proj i) x
      + t • (if i = Fin.last n
        then ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) i
        else 0) x
    rw [if_neg hi, if_neg hi]
    show _ = x i + t • (0 : ℂ)
    rw [smul_zero, add_zero]

theorem continuous_coordContract :
    Continuous fun t : ℝ => coordContract (n := n) (t : ℂ) := by
  simp only [coordContract_eq]
  exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

/-- **The contraction does not increase distances.** -/
theorem coordContract_dist_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x y : Fin (n + 1) → ℂ) :
    dist (coordContract (t : ℂ) x) (coordContract (t : ℂ) y) ≤ dist x y := by
  refine (dist_pi_le_iff (X := fun _ : Fin (n + 1) => ℂ) (r := dist x y) dist_nonneg).2 fun i => ?_
  by_cases hi : i = Fin.last n
  · subst hi
    rw [coordContract_apply_last, coordContract_apply_last, dist_eq_norm, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ht.1]
    calc t * ‖x (Fin.last n) - y (Fin.last n)‖
        ≤ 1 * ‖x (Fin.last n) - y (Fin.last n)‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = dist (x (Fin.last n)) (y (Fin.last n)) := by rw [one_mul, dist_eq_norm]
      _ ≤ dist x y := dist_le_pi_dist x y (Fin.last n)
  · rw [coordContract_apply_of_ne _ _ hi, coordContract_apply_of_ne _ _ hi]
    exact dist_le_pi_dist x y i

end Holomorphy

end HTGeometry

namespace HTGeometry

open Complex MeasureTheory intervalIntegral

section Differentiability

variable {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ} {c : Fin (n + 1) → ℂ} {r : ℝ}

/-- The derivative of the integrand of the quotient in its base point. -/
noncomputable def coordDivDeriv (f : (Fin (n + 1) → ℂ) → ℂ) (x : Fin (n + 1) → ℂ) (t : ℝ) :
    (Fin (n + 1) → ℂ) →L[ℂ] ℂ :=
  (fderiv ℂ (lastCoordDeriv f) (coordContract (t : ℂ) x)).comp (coordContract (t : ℂ))

theorem continuous_coordContract_apply (x : Fin (n + 1) → ℂ) :
    Continuous fun t : ℝ => coordContract (t : ℂ) x :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_coordContract x t).continuousAt

set_option maxHeartbeats 1000000 in
/-- **The quotient is holomorphic.**  It is a parametric integral over a compact interval of a
family of holomorphic functions: their derivatives are continuous in the parameter, and their
Lipschitz constants are uniform in it because the contraction does not increase distances and lands
in a compact sub-polydisc on which the derivative of the last partial derivative is bounded. -/
theorem coordDivQuotient_differentiableAt (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    (hc : c (Fin.last n) = 0) {x₀ : Fin (n + 1) → ℂ} (hx₀ : x₀ ∈ Metric.ball c r) :
    DifferentiableAt ℂ (coordDivQuotient f) x₀ := by
  have hx₀d : dist x₀ c < r := Metric.mem_ball.1 hx₀
  set ρ : ℝ := (dist x₀ c + r) / 2 with hρdef
  have hρx : dist x₀ c < ρ := by rw [hρdef]; linarith
  have hρr : ρ < r := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg hρx
  have hx₀ρ : x₀ ∈ Metric.ball c ρ := Metric.mem_ball.2 hρx
  have hKsub : Metric.closedBall c ρ ⊆ Metric.ball c r := fun z hz =>
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hρr)
  have hDan : AnalyticOnNhd ℂ (lastCoordDeriv f) (Metric.ball c r) :=
    lastCoordDeriv_analyticOnNhd hf
  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ Metric.closedBall c ρ, ‖fderiv ℂ (lastCoordDeriv f) z‖ ≤ C :=
    (isCompact_closedBall c ρ).exists_bound_of_continuousOn
      (fun z hz => (hDan.fderiv z (hKsub hz)).continuousAt.continuousWithinAt)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC c (Metric.mem_closedBall_self hρ0.le))
  have hmemK : ∀ x ∈ Metric.ball c ρ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      coordContract (t : ℂ) x ∈ Metric.closedBall c ρ := fun x hx t ht =>
    Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 (coordContract_mem_ball hc hx ht)))
  have hLipD : ∀ z ∈ Metric.closedBall c ρ, ∀ y ∈ Metric.closedBall c ρ,
      ‖lastCoordDeriv f y - lastCoordDeriv f z‖ ≤ C * ‖y - z‖ := fun z hz y hy =>
    (convex_closedBall c ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f' := fun w => fderiv ℂ (lastCoordDeriv f) w)
      (fun w hw => ((hDan w (hKsub hw)).differentiableAt.hasFDerivAt).hasFDerivWithinAt)
      (fun w hw => hC w hw) hz hy
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμdef
  set F : (Fin (n + 1) → ℂ) → ℝ → ℂ :=
    fun x t => lastCoordDeriv f (coordContract (t : ℂ) x) with hFdef
  have hIoc : Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self
  have hFcontOn : ∀ x ∈ Metric.ball c ρ, ContinuousOn (F x) (Set.Icc (0 : ℝ) 1) := by
    intro x hx t ht
    show ContinuousWithinAt ((fun z => lastCoordDeriv f z) ∘ fun s : ℝ => coordContract (s : ℂ) x)
      (Set.Icc 0 1) t
    exact ContinuousAt.comp_continuousWithinAt
      ((hDan _ (hKsub (hmemK x hx t ht))).continuousAt)
      (continuous_coordContract_apply x).continuousWithinAt
  have hF'cont : ContinuousOn (coordDivDeriv f x₀) (Set.Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn
        (fun t : ℝ => fderiv ℂ (lastCoordDeriv f) (coordContract (t : ℂ) x₀))
        (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      show ContinuousWithinAt ((fun z => fderiv ℂ (lastCoordDeriv f) z)
        ∘ fun s : ℝ => coordContract (s : ℂ) x₀) (Set.Icc 0 1) t
      exact ContinuousAt.comp_continuousWithinAt
        ((hDan.fderiv _ (hKsub (hmemK x₀ hx₀ρ t ht))).continuousAt)
        (continuous_coordContract_apply x₀).continuousWithinAt
    exact h1.clm_comp continuous_coordContract.continuousOn
  have hquot : coordDivQuotient f = fun x => ∫ t, F x t ∂μ :=
    funext fun x => intervalIntegral.integral_of_le zero_le_one
  rw [hquot]
  refine (hasFDerivAt_integral_of_dominated_loc_of_lip (F := F) (F' := coordDivDeriv f x₀)
    (bound := fun _ => C) (s := Metric.ball c ρ)
    (Metric.isOpen_ball.mem_nhds hx₀ρ)
    (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx₀ρ) fun x hx =>
      ((hFcontOn x hx).mono hIoc).aestronglyMeasurable measurableSet_Ioc)
    (((hFcontOn x₀ hx₀ρ).integrableOn_Icc).mono_set hIoc)
    ((hF'cont.mono hIoc).aestronglyMeasurable measurableSet_Ioc)
    ?_ (((continuous_const.continuousOn).integrableOn_Icc).mono_set hIoc) ?_).2.differentiableAt
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hCabs : ((Real.nnabs C : NNReal) : ℝ) = C := by
      rw [Real.coe_nnabs, abs_of_nonneg hC0]
    rw [hCabs, dist_eq_norm]
    calc ‖lastCoordDeriv f (coordContract (t : ℂ) x) - lastCoordDeriv f (coordContract (t : ℂ) y)‖
        ≤ C * ‖coordContract (t : ℂ) x - coordContract (t : ℂ) y‖ :=
          hLipD _ (hmemK y hy t (hIoc ht)) _ (hmemK x hx t (hIoc ht))
      _ = C * dist (coordContract (t : ℂ) x) (coordContract (t : ℂ) y) := by rw [dist_eq_norm]
      _ ≤ C * dist x y :=
          mul_le_mul_of_nonneg_left (coordContract_dist_le (hIoc ht) x y) hC0
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    have hz : coordContract (t : ℂ) x₀ ∈ Metric.ball c r :=
      hKsub (hmemK x₀ hx₀ρ t (hIoc ht))
    exact ((hDan _ hz).differentiableAt.hasFDerivAt).comp x₀
      (coordContract (t : ℂ)).hasFDerivAt

end Differentiability

end HTGeometry

namespace HTGeometry

open Complex MeasureTheory

section Capstone

variable {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ} {c : Fin (n + 1) → ℂ} {r : ℝ}

/-- **A holomorphic function vanishing on the divisor of the last coordinate is that coordinate
times a holomorphic function.**  The quotient is explicit: the integral of the last partial
derivative along the segment contracting that coordinate to zero.  The polydisc must be centred on
the divisor, which is what makes the contraction preserve it. -/
theorem coordDivQuotient_analyticOnNhd (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    (hc : c (Fin.last n) = 0) :
    AnalyticOnNhd ℂ (coordDivQuotient f) (Metric.ball c r) := by
  have hdiff : DifferentiableOn ℂ (coordDivQuotient f) (Metric.ball c r) :=
    fun x hx => (coordDivQuotient_differentiableAt hf hc hx).differentiableWithinAt
  exact fun x hx => GaloisForLFunctions.HTGeometry.analyticAt_of_differentiableOn
    Metric.isOpen_ball hdiff hx

/-- **The division theorem**, as an existence statement. -/
theorem exists_analyticOnNhd_coord_mul (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    (hc : c (Fin.last n) = 0)
    (hvanish : ∀ z ∈ Metric.ball c r, z (Fin.last n) = 0 → f z = 0) :
    ∃ u : (Fin (n + 1) → ℂ) → ℂ, AnalyticOnNhd ℂ u (Metric.ball c r) ∧
      ∀ x ∈ Metric.ball c r, x (Fin.last n) * u x = f x :=
  ⟨coordDivQuotient f, coordDivQuotient_analyticOnNhd hf hc,
    fun _ hx => coordDivQuotient_mul hf hc hvanish hx⟩

end Capstone

end HTGeometry
