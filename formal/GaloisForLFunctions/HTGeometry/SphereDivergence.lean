import GaloisForLFunctions.HTGeometry.DivergenceEuclidean
import GaloisForLFunctions.HTGeometry.LebesguePolarIntegral

/-!
# The divergence theorem on the unit sphere

A radial cutoff times a tangential field has divergence the cutoff times the field's divergence:
the radial derivative term pairs the gradient of the norm with the field and dies by tangentiality.

If the field is homogeneous of degree zero, its divergence is homogeneous of degree `-1`, so the
polar decomposition turns the total divergence into the radial integral of the cutoff against the
Jacobian times the angular integral of the divergence.  The flat divergence theorem makes the total
vanish, so the angular integral vanishes whenever the radial factor does not: the sphere carries no
boundary, hence no boundary term.
-/

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The gradient of the norm -/

section NormDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The norm of an inner product space is differentiable away from the origin, with derivative the
inner product against the unit vector. -/
theorem hasFDerivAt_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) ((‖x‖⁻¹) • (innerSL ℝ x)) x := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : HasFDerivAt (fun y : E => ‖y‖ ^ 2) ((2 : ℕ) • (innerSL ℝ x)) x := by
    simpa using (hasFDerivAt_id x).norm_sq
  have hne : ‖x‖ ^ 2 ≠ 0 := by positivity
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖x‖ ^ 2))) (‖x‖ ^ 2) :=
    Real.hasDerivAt_sqrt hne
  have hcomp := hsqrt.hasFDerivAt.comp x hsq
  have hfun : (Real.sqrt ∘ fun y : E => ‖y‖ ^ 2) = fun y : E => ‖y‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [hfun] at hcomp
  have hval : (ContinuousLinearMap.toSpanSingleton ℝ
        (1 / (2 * Real.sqrt (‖x‖ ^ 2)))).comp ((2 : ℕ) • (innerSL ℝ x))
      = (‖x‖⁻¹) • (innerSL ℝ x) := by
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_apply, smul_eq_mul, nsmul_eq_mul,
      innerSL_apply_apply]
    rw [Real.sqrt_sq (norm_nonneg x)]
    field_simp
    ring
  rwa [hval] at hcomp

end NormDeriv

/-! ## The radial cutoff of a tangential field -/

section Cutoff

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The coordinate expansion of the inner product against a basis vector. -/
theorem inner_single (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (inner ℝ x (EuclideanSpace.single i (1 : ℝ)) : ℝ) = x i := by
  rw [EuclideanSpace.inner_single_right]
  simp

/-- The derivative of a radially cut-off field, in closed form. -/
def radialCutoffDeriv
    (X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))))
    (φ φ' : ℝ → ℝ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  φ ‖y‖ • X' y + ((φ' ‖y‖ * ‖y‖⁻¹) • (innerSL ℝ y)).smulRight (X y)

/-- **The product rule for a radial cutoff.**  Away from the origin the cut-off field is
differentiable with the closed-form derivative. -/
theorem hasFDerivAt_radialCutoff
    {X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    {φ φ' : ℝ → ℝ}
    (hX : ∀ x, HasFDerivAt X (X' x) x)
    (hφ : ∀ r, HasDerivAt φ (φ' r) r)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ≠ 0) :
    HasFDerivAt (fun y => φ ‖y‖ • X y) (radialCutoffDeriv X X' φ φ' x) x := by
  have hnorm := hasFDerivAt_norm_of_ne_zero hx
  have hc : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (n + 1)) => φ ‖y‖)
      ((φ' ‖x‖ * ‖x‖⁻¹) • (innerSL ℝ x)) x := by
    have hcomp := (hφ ‖x‖).hasFDerivAt.comp x hnorm
    have hval : (ContinuousLinearMap.toSpanSingleton ℝ (φ' ‖x‖)).comp
        ((‖x‖⁻¹) • (innerSL ℝ x)) = (φ' ‖x‖ * ‖x‖⁻¹) • (innerSL ℝ x) := by
      ext v
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_apply, smul_eq_mul, innerSL_apply_apply]
      ring
    rw [hval] at hcomp
    exact hcomp
  exact hc.smul (hX x)

/-- **The divergence of a radially cut-off tangential field.**  The radial term dies by
tangentiality, leaving the cutoff times the divergence. -/
theorem euclideanDivergence_radialCutoffDeriv
    {X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    {φ φ' : ℝ → ℝ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (htan : (inner ℝ x (X x) : ℝ) = 0) :
    euclideanDivergence (radialCutoffDeriv X X' φ φ') x
      = φ ‖x‖ * euclideanDivergence X' x := by
  classical
  rw [euclideanDivergence, euclideanDivergence, Finset.mul_sum]
  have hterm : ∀ i : Fin (n + 1),
      (radialCutoffDeriv X X' φ φ' x) (EuclideanSpace.single i (1 : ℝ)) i
        = φ ‖x‖ * (X' x (EuclideanSpace.single i (1 : ℝ))) i
          + (φ' ‖x‖ * ‖x‖⁻¹ * x i) * (X x) i := by
    intro i
    rw [radialCutoffDeriv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, innerSL_apply_apply]
    rw [inner_single]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  have hzero : ∑ i, (φ' ‖x‖ * ‖x‖⁻¹ * x i) * (X x) i = 0 := by
    have hsum : ∑ i, x i * (X x) i = (inner ℝ x (X x) : ℝ) := by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
    calc ∑ i, (φ' ‖x‖ * ‖x‖⁻¹ * x i) * (X x) i
        = (φ' ‖x‖ * ‖x‖⁻¹) * ∑ i, x i * (X x) i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hsum, htan, mul_zero]
  rw [hzero, add_zero]

/-- **Euclidean homogeneity of the divergence.**  A degree-zero homogeneous field has divergence
homogeneous of degree `-1`. -/
theorem euclideanDivergence_smul_of_homogeneous
    {X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    (hd : ∀ x, HasFDerivAt X (X' x) x)
    (hhom : ∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))), 0 < c → X (c • x) = X x)
    {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanDivergence X' (c • x) = c⁻¹ * euclideanDivergence X' x := by
  classical
  have hscale : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (n + 1)) => X (c • y))
      ((X' (c • x)).comp (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))))) x := by
    have hinner : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (n + 1)) => c • y)
        (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1)))) x := by
      have hcl := (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1)))).hasFDerivAt
        (x := x)
      refine hcl.congr_of_eventuallyEq ?_
      filter_upwards with y
      simp
    exact (hd (c • x)).comp x hinner
  have hfun : (fun y : EuclideanSpace ℝ (Fin (n + 1)) => X (c • y)) = X := by
    funext y
    exact hhom c y hc
  rw [hfun] at hscale
  have hEq := hscale.unique (hd x)
  have hpoint : ∀ v : EuclideanSpace ℝ (Fin (n + 1)), c • (X' (c • x)) v = X' x v := by
    intro v
    have := congrArg
      (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) => L v) hEq
    simpa [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      map_smul] using this
  have hentry : ∀ i, (X' (c • x) (EuclideanSpace.single i (1 : ℝ))) i
      = c⁻¹ * (X' x (EuclideanSpace.single i (1 : ℝ))) i := by
    intro i
    have h := congrFun (congrArg WithLp.ofLp (hpoint (EuclideanSpace.single i (1 : ℝ)))) i
    have hcne : c ≠ 0 := ne_of_gt hc
    have hval : c * ((X' (c • x)) (EuclideanSpace.single i (1 : ℝ))) i
        = ((X' x) (EuclideanSpace.single i (1 : ℝ))) i := by
      simpa using h
    field_simp
    linarith [hval]
  rw [euclideanDivergence, euclideanDivergence, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hentry i

/-! ## The scalar product rule -/

/-- **The product rule for a scalar multiple.**  Multiplying a field by a scalar function adds the
pairing of the scalar's gradient with the field. -/
theorem euclideanDivergence_scalar_smul
    {u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {u' : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {Y : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {Y' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    euclideanDivergence (fun y => u y • Y' y + (u' y).smulRight (Y y)) x
      = u x * euclideanDivergence Y' x
        + ∑ i, (u' x (EuclideanSpace.single i (1 : ℝ))) * (Y x) i := by
  classical
  rw [euclideanDivergence, euclideanDivergence, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]

/-- The scalar product rule at the level of derivatives. -/
theorem hasFDerivAt_scalar_smul
    {u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {u' : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {Y : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {Y' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    (hu : ∀ x, HasFDerivAt u (u' x) x) (hY : ∀ x, HasFDerivAt Y (Y' x) x)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt (fun y => u y • Y y) (u x • Y' x + (u' x).smulRight (Y x)) x :=
  (hu x).smul (hY x)

/-- A linear functional is recovered from its values on the coordinate basis. -/
theorem sum_apply_single_mul (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ∑ i, L (EuclideanSpace.single i (1 : ℝ)) * v i = L v := by
  classical
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]

/-! ## The divergence theorem on the sphere -/

/-- **The divergence theorem on the unit sphere.**  A tangential field, homogeneous of degree zero
and continuously differentiable, has vanishing total divergence over the sphere: the sphere has no
boundary, so the flat theorem applied to a radial cutoff leaves only the angular integral. -/
theorem integral_toSphere_euclideanDivergence_eq_zero
    {X : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {X' : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))}
    {φ φ' : ℝ → ℝ}
    (hX : ∀ x, HasFDerivAt X (X' x) x)
    (htan : ∀ x, (inner ℝ x (X x) : ℝ) = 0)
    (hhom : ∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))), 0 < c → X (c • x) = X x)
    (hφ : ∀ r, HasDerivAt φ (φ' r) r) (hcontφ : Continuous φ)
    (hφ0 : ∀ r : ℝ, r ≤ 1 / 2 → φ r = 0) (hφ2 : ∀ r : ℝ, 2 ≤ r → φ r = 0)
    (hcontX : Continuous (euclideanDivergence X'))
    (hrad : (∫ r in Ioi (0 : ℝ), r ^ n * (φ r / r)) ≠ 0) :
    ∫ ω, euclideanDivergence X' ω
        ∂((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere) = 0 := by
  classical
  set V : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y => φ ‖y‖ • X y with hVdef
  set V' := radialCutoffDeriv X X' φ φ' with hV'def
  have hzeroDeriv : V' 0 = 0 := by
    rw [hV'def, radialCutoffDeriv]
    have hφzero : φ ‖(0 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 0 := by
      rw [norm_zero]
      exact hφ0 0 (by norm_num)
    rw [hφzero]
    ext v
    simp
  have hV : ∀ y, HasFDerivAt V (V' y) y := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have hloc : V =ᶠ[nhds (0 : EuclideanSpace ℝ (Fin (n + 1)))] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin (n + 1)))
          (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
        have hnz : ‖z‖ ≤ 1 / 2 := by
          have := mem_ball_zero_iff.mp hz
          linarith
        rw [hVdef]
        simp [hφ0 _ hnz]
      have hconst : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin (n + 1)) =>
          (0 : EuclideanSpace ℝ (Fin (n + 1)))) 0 0 :=
        (0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).hasFDerivAt
      rw [hzeroDeriv]
      exact hconst.congr_of_eventuallyEq hloc
    · exact hasFDerivAt_radialCutoff hX hφ hy
  have hdivV : ∀ y, euclideanDivergence V' y = φ ‖y‖ * euclideanDivergence X' y := by
    intro y
    exact euclideanDivergence_radialCutoffDeriv (htan y)
  have hsupp : HasCompactSupport V := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2) ?_
    intro y hy
    have hgt : 2 < ‖y‖ := by
      by_contra hcon
      exact hy (mem_closedBall_zero_iff.mpr (le_of_not_gt hcon))
    rw [hVdef]
    simp [hφ2 _ (le_of_lt hgt)]
  have hcontV : Continuous (euclideanDivergence V') := by
    have : euclideanDivergence V' = fun y => φ ‖y‖ * euclideanDivergence X' y := funext hdivV
    rw [this]
    exact (hcontφ.comp continuous_norm).mul hcontX
  have hflat := integral_euclideanDivergence_eq_zero V V' hV hcontV hsupp
  have hfactor : ∀ (ω : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (r : Ioi (0 : ℝ)),
      euclideanDivergence V' (r.1 • ω.1)
        = euclideanDivergence X' ω.1 * (φ r.1 / r.1) := by
    intro ω r
    have hrpos : (0 : ℝ) < r.1 := r.2
    have hnorm : ‖(r.1 • ω.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = r.1 := by
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hrpos)]
      have : ‖(ω.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
      rw [this, mul_one]
    rw [hdivV, hnorm, euclideanDivergence_smul_of_homogeneous hX hhom hrpos]
    field_simp
  have hpolar := integral_polar_mul (m := n + 1) (by omega) (fun r => φ r / r)
    (fun ω => euclideanDivergence X' ω.1) (euclideanDivergence V') hfactor
  rw [hflat] at hpolar
  have hprod := hpolar.symm
  have hzero := mul_eq_zero.mp hprod
  rcases hzero with h | h
  · simpa using h
  · exact absurd (by simpa using h) hrad

end Cutoff

end

end GaloisForLFunctions.HTGeometry
