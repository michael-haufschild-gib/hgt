import GaloisForLFunctions.HTGeometry.RangeProjectionAnalytic
import GaloisForLFunctions.RHTower.SoninEulerCornerConcrete

/-!
# The finite Euler chart of the Sonin carrier and its tangent

For a prime scale `p > 1` and a real Euler parameter `t` with `|t| < √p`, the physical realization
of multiplication by the denominator `1 - t p^{-z}` on the critical line is

`M_t = 1 - (t/√p) U_p*`.

It is a bounded operator with bounded inverse, and its Gram operator relative to the Sonin
projection `Q` is invertible, so the orthogonal projection onto `M_t(S)` is the closed-range
formula `P_t = M_t Q A_t⁻¹ Q M_t*`.  The family is affine in `t`, hence real analytic, and

* the pullback metric is `M_t* M_t = (1 + t²/p) - (t/√p)(U_p + U_p⁻¹)`, whose derivative at the
  empty Euler parameter is `-(1/√p)(U_p + U_p⁻¹)`, so its Sonin cross-boundary is exactly the
  positive Euler corner;
* the second fundamental form of the projection family is `(1 - Q) P'_0 Q = (1 - Q) M'_0 Q`,
  the one-sided dilation corner.
-/

open ContinuousLinearMap
open scoped InnerProduct

noncomputable section

namespace RHTower

/-- The finite Euler denominator multiplier `1 - t p^{-z}` in the physical dilation model. -/
def semilocalEulerMultiplier (t p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  1 - ((t / Real.sqrt p : ℝ) : ℂ) • (dilationCLM p (zero_lt_one.trans hp))†

@[simp] theorem semilocalEulerMultiplier_zero (p : ℝ) (hp : 1 < p) :
    semilocalEulerMultiplier 0 p hp = 1 := by
  simp [semilocalEulerMultiplier]

/-- The adjoint multiplier is the numerator direction `1 - t p^{z-1}`. -/
theorem adjoint_semilocalEulerMultiplier (t p : ℝ) (hp : 1 < p) :
    (semilocalEulerMultiplier t p hp)† =
      1 - ((t / Real.sqrt p : ℝ) : ℂ) • dilationCLM p (zero_lt_one.trans hp) := by
  rw [semilocalEulerMultiplier]
  rw [map_sub, ContinuousLinearMap.adjoint_one]
  congr 1
  rw [map_smulₛₗ ContinuousLinearMap.adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp [Complex.conj_ofReal]

theorem dilationCLM_mul_adjoint (p : ℝ) (hp : 1 < p) :
    dilationCLM p (zero_lt_one.trans hp) * (dilationCLM p (zero_lt_one.trans hp))† = 1 := by
  rw [adjoint_dilationCLM]
  ext f
  simp

theorem adjoint_mul_dilationCLM (p : ℝ) (hp : 1 < p) :
    (dilationCLM p (zero_lt_one.trans hp))† * dilationCLM p (zero_lt_one.trans hp) = 1 := by
  rw [adjoint_dilationCLM]
  ext f
  simp

/-- **The pullback metric of the finite Euler chart.**
`M_t* M_t = (1 + t²/p) - (t/√p)(U_p + U_p⁻¹)`. -/
theorem adjoint_mul_semilocalEulerMultiplier (t p : ℝ) (hp : 1 < p) :
    (semilocalEulerMultiplier t p hp)† * semilocalEulerMultiplier t p hp
      = ((1 + t ^ 2 / p : ℝ) : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2)
        + ((-(t / Real.sqrt p) : ℝ) : ℂ) • dilationSum p hp := by
  have hppos : (0 : ℝ) < p := zero_lt_one.trans hp
  set c : ℂ := ((t / Real.sqrt p : ℝ) : ℂ) with hc
  set U : SoninL2 →L[ℂ] SoninL2 := dilationCLM p (zero_lt_one.trans hp) with hU
  have hsq : c * c = ((t ^ 2 / p : ℝ) : ℂ) := by
    rw [hc]
    norm_cast
    rw [div_mul_div_comm, Real.mul_self_sqrt hppos.le]
    ring
  have hUV : U * U† = 1 := dilationCLM_mul_adjoint p hp
  have expand : (1 - c • U) * (1 - c • U†)
      = 1 - c • U† - (c • U - (c * c) • (U * U†)) := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_smul]
  have hneg : ((-(t / Real.sqrt p) : ℝ) : ℂ) = -c := by rw [hc]; push_cast; ring
  have hone : ((1 + t ^ 2 / p : ℝ) : ℂ) = 1 + ((t ^ 2 / p : ℝ) : ℂ) := by push_cast; ring
  rw [adjoint_semilocalEulerMultiplier, semilocalEulerMultiplier, dilationSum, ← hU, ← hc,
    expand, hUV, hsq, hneg, hone, add_smul, one_smul, smul_add, neg_smul, neg_smul]
  abel

/-- The Euler chart is affine in the parameter. -/
theorem hasDerivAt_semilocalEulerMultiplier (p : ℝ) (hp : 1 < p) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semilocalEulerMultiplier s p hp)
      (-((((Real.sqrt p)⁻¹ : ℝ) : ℂ) • (dilationCLM p (zero_lt_one.trans hp))†)) t := by
  have hcoef : HasDerivAt (fun s : ℝ => ((s / Real.sqrt p : ℝ) : ℂ))
      ((((Real.sqrt p)⁻¹ : ℝ) : ℂ)) t := by
    have h : HasDerivAt (fun s : ℝ => s / Real.sqrt p) ((Real.sqrt p)⁻¹) t := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const ((Real.sqrt p)⁻¹)
    have hcomp := (Complex.ofRealCLM.hasFDerivAt (x := t / Real.sqrt p)).comp_hasDerivAt t h
    simpa [Function.comp_def] using hcomp
  have hsmul := hcoef.smul_const ((dilationCLM p (zero_lt_one.trans hp))† :
    SoninL2 →L[ℂ] SoninL2)
  exact hsmul.const_sub (1 : SoninL2 →L[ℂ] SoninL2)

/-- **The metric tangent at the empty Euler parameter.** -/
theorem hasDerivAt_semilocalEulerMetric (p : ℝ) (hp : 1 < p) :
    HasDerivAt (fun s : ℝ => (semilocalEulerMultiplier s p hp)† * semilocalEulerMultiplier s p hp)
      (((-(Real.sqrt p)⁻¹ : ℝ) : ℂ) • dilationSum p hp) 0 := by
  have hppos : (0 : ℝ) < p := zero_lt_one.trans hp
  have hfun : (fun s : ℝ =>
      (semilocalEulerMultiplier s p hp)† * semilocalEulerMultiplier s p hp)
      = fun s : ℝ => ((1 + s ^ 2 / p : ℝ) : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2)
        + ((-(s / Real.sqrt p) : ℝ) : ℂ) • dilationSum p hp := by
    funext s
    exact adjoint_mul_semilocalEulerMultiplier s p hp
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => ((1 + s ^ 2 / p : ℝ) : ℂ)) 0 0 := by
    have hd : HasDerivAt (fun s : ℝ => s ^ 2 / p) 0 0 := by
      simpa [div_eq_mul_inv] using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const p⁻¹)
    have h : HasDerivAt (fun s : ℝ => 1 + s ^ 2 / p) 0 0 := hd.const_add 1
    have hcomp := (Complex.ofRealCLM.hasFDerivAt (x := 1 + (0 : ℝ) ^ 2 / p)).comp_hasDerivAt 0 h
    simpa [Function.comp_def] using hcomp
  have h2 : HasDerivAt (fun s : ℝ => ((-(s / Real.sqrt p) : ℝ) : ℂ))
      ((-(Real.sqrt p)⁻¹ : ℝ) : ℂ) 0 := by
    have hd : HasDerivAt (fun s : ℝ => s / Real.sqrt p) ((Real.sqrt p)⁻¹) 0 := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℝ)).mul_const ((Real.sqrt p)⁻¹)
    have h : HasDerivAt (fun s : ℝ => -(s / Real.sqrt p)) (-(Real.sqrt p)⁻¹) 0 := hd.neg
    have hcomp := (Complex.ofRealCLM.hasFDerivAt
      (x := -((0 : ℝ) / Real.sqrt p))).comp_hasDerivAt 0 h
    simpa [Function.comp_def] using hcomp
  have hsum := (h1.smul_const (1 : SoninL2 →L[ℂ] SoninL2)).add
    (h2.smul_const (dilationSum p hp))
  simpa [Pi.add_def] using hsum

/-- **`(15)`: the Sonin cross-boundary of the metric tangent is exactly the positive Euler
corner.** -/
theorem crossBoundary_semilocalEulerMetricTangent (a p : ℝ) (hp : 1 < p) :
    crossBoundary (centralSoninProjection a)
        (((-(Real.sqrt p)⁻¹ : ℝ) : ℂ) • dilationSum p hp)
      = crossBoundary (centralSoninProjection a) (positiveEulerDilationOperator p hp) := by
  rw [centralPositiveEulerCorner_eq_smul a p hp, crossBoundary]
  rw [crossBoundary]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  push_cast
  simp

theorem norm_dilationCLM_apply (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    ‖dilationCLM a ha f‖ = ‖f‖ :=
  (dilationUnitary a ha).norm_map f

/-- **`(5)`: the Euler multiplier is bounded below whenever `|t| < √p`.** -/
theorem norm_semilocalEulerMultiplier_apply_ge (t p : ℝ) (hp : 1 < p) (f : SoninL2) :
    (1 - |t| / Real.sqrt p) * ‖f‖ ≤ ‖semilocalEulerMultiplier t p hp f‖ := by
  have hppos : (0 : ℝ) < p := zero_lt_one.trans hp
  have hsqrt : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hppos
  set V : SoninL2 →L[ℂ] SoninL2 := ContinuousLinearMap.adjoint (dilationCLM p hppos) with hV
  have hval : semilocalEulerMultiplier t p hp f
      = f - ((t / Real.sqrt p : ℝ) : ℂ) • (V f) := by
    simp [semilocalEulerMultiplier, hV]
  have hnormU : ‖V f‖ = ‖f‖ := by
    rw [hV, adjoint_dilationCLM]
    exact norm_dilationCLM_apply _ _ f
  have hc : ‖((t / Real.sqrt p : ℝ) : ℂ)‖ = |t| / Real.sqrt p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg hsqrt.le]
  have hsub : ‖f‖ - ‖((t / Real.sqrt p : ℝ) : ℂ) • (V f)‖
      ≤ ‖f - ((t / Real.sqrt p : ℝ) : ℂ) • (V f)‖ := norm_sub_norm_le _ _
  rw [norm_smul, hc, hnormU] at hsub
  rw [hval]
  calc (1 - |t| / Real.sqrt p) * ‖f‖ = ‖f‖ - |t| / Real.sqrt p * ‖f‖ := by ring
    _ ≤ ‖f - ((t / Real.sqrt p : ℝ) : ℂ) • (V f)‖ := hsub

theorem isSelfAdjoint_centralSoninProjection (a : ℝ) :
    IsSelfAdjoint (centralSoninProjection a) :=
  isSelfAdjoint_starProjection (centralSoninCarrier a)

theorem isIdempotentElem_centralSoninProjection (a : ℝ) :
    IsIdempotentElem (centralSoninProjection a) :=
  (centralSoninCarrier a).isIdempotentElem_starProjection

/-- The Gram operator of the Euler chart relative to the Sonin projection. -/
def semilocalEulerGram (a t p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.rangeProjectionGram (centralSoninProjection a) (semilocalEulerMultiplier t p hp)

/-- **`(8)`: the orthogonal projection onto the deformed Sonin carrier.** -/
def semilocalEulerProjection (a t p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.rangeProjection (centralSoninProjection a) (semilocalEulerMultiplier t p hp)

theorem isUnit_semilocalEulerGram (a t p : ℝ) (hp : 1 < p) (ht : |t| < Real.sqrt p) :
    IsUnit (semilocalEulerGram a t p hp) := by
  have hsqrt : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  have hcpos : 0 < 1 - |t| / Real.sqrt p := by
    have : |t| / Real.sqrt p < 1 := (div_lt_one hsqrt).mpr ht
    linarith
  exact HTGeometry.isUnit_rangeProjectionGram (isSelfAdjoint_centralSoninProjection a)
    (isIdempotentElem_centralSoninProjection a) hcpos
    (fun x => norm_semilocalEulerMultiplier_apply_ge t p hp _)

/-- The deformed Sonin carrier is the image of the Sonin carrier under the Euler multiplier. -/
theorem range_semilocalEulerChart (a t p : ℝ) (hp : 1 < p) :
    LinearMap.range (((semilocalEulerMultiplier t p hp * centralSoninProjection a :
        SoninL2 →L[ℂ] SoninL2) : SoninL2 →ₗ[ℂ] SoninL2))
      = Submodule.map ((semilocalEulerMultiplier t p hp : SoninL2 →L[ℂ] SoninL2) :
          SoninL2 →ₗ[ℂ] SoninL2) (centralSoninCarrier a) := by
  have hcomp : ((semilocalEulerMultiplier t p hp * centralSoninProjection a :
      SoninL2 →L[ℂ] SoninL2) : SoninL2 →ₗ[ℂ] SoninL2)
      = ((semilocalEulerMultiplier t p hp : SoninL2 →L[ℂ] SoninL2) : SoninL2 →ₗ[ℂ] SoninL2) ∘ₗ
        ((centralSoninProjection a : SoninL2 →L[ℂ] SoninL2) : SoninL2 →ₗ[ℂ] SoninL2) := rfl
  rw [hcomp, LinearMap.range_comp, centralSoninProjection,
    Submodule.range_starProjection]

/-- **`(8)`: the closed-range formula computes the orthogonal projection onto the deformed
carrier.** -/
theorem starProjection_eq_semilocalEulerProjection (a t p : ℝ) (hp : 1 < p)
    (ht : |t| < Real.sqrt p) {K : Submodule ℂ SoninL2} [K.HasOrthogonalProjection]
    (hK : K = Submodule.map ((semilocalEulerMultiplier t p hp : SoninL2 →L[ℂ] SoninL2) :
      SoninL2 →ₗ[ℂ] SoninL2) (centralSoninCarrier a)) :
    K.starProjection = semilocalEulerProjection a t p hp := by
  have hsqrt : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  have hcpos : 0 < 1 - |t| / Real.sqrt p := by
    have : |t| / Real.sqrt p < 1 := (div_lt_one hsqrt).mpr ht
    linarith
  exact HTGeometry.starProjection_eq_rangeProjection
    (isSelfAdjoint_centralSoninProjection a) (isIdempotentElem_centralSoninProjection a) hcpos
    (fun x => norm_semilocalEulerMultiplier_apply_ge t p hp _)
    (by rw [hK, ← range_semilocalEulerChart])

/-- The Euler chart is real analytic in the parameter. -/
theorem analyticAt_semilocalEulerMultiplier (p : ℝ) (hp : 1 < p) (t₀ : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => semilocalEulerMultiplier t p hp) t₀ := by
  set V : SoninL2 →L[ℂ] SoninL2 :=
    (dilationCLM p (zero_lt_one.trans hp))† with hVdef
  have hr : AnalyticAt ℝ (fun t : ℝ => t / Real.sqrt p) t₀ := by
    have h := (analyticAt_id (𝕜 := ℝ) (z := t₀)).mul
      (analyticAt_const (v := ((Real.sqrt p)⁻¹ : ℝ)))
    have hfun : (fun t : ℝ => t / Real.sqrt p)
        = (id : ℝ → ℝ) * (fun _ : ℝ => ((Real.sqrt p)⁻¹ : ℝ)) := by
      funext t; simp [div_eq_mul_inv]
    rw [hfun]
    exact h
  have hcoef : AnalyticAt ℝ (fun t : ℝ => ((t / Real.sqrt p : ℝ) : ℂ)) t₀ := by
    have hcomp := AnalyticAt.comp (g := (⇑Complex.ofRealCLM)) (f := fun t : ℝ => t / Real.sqrt p)
      (Complex.ofRealCLM.analyticAt (t₀ / Real.sqrt p)) hr
    exact hcomp
  have hsmul : AnalyticAt ℝ (fun t : ℝ => ((t / Real.sqrt p : ℝ) : ℂ) • V) t₀ := by
    have h := hcoef.smul (analyticAt_const (v := V))
    exact h
  have h := (analyticAt_const (v := (1 : SoninL2 →L[ℂ] SoninL2))).sub hsmul
  have hfun : (fun t : ℝ => semilocalEulerMultiplier t p hp)
      = (fun _ : ℝ => (1 : SoninL2 →L[ℂ] SoninL2)) - fun t : ℝ =>
        ((t / Real.sqrt p : ℝ) : ℂ) • V := by
    funext t
    rw [semilocalEulerMultiplier, hVdef]
    rfl
  rw [hfun]
  exact h

/-- **The semilocal orthogonal projection is operator-norm real analytic.** -/
theorem analyticAt_semilocalEulerProjection (a p : ℝ) (hp : 1 < p) (t₀ : ℝ)
    (ht : |t₀| < Real.sqrt p) :
    AnalyticAt ℝ (fun t : ℝ => semilocalEulerProjection a t p hp) t₀ :=
  HTGeometry.analyticAt_rangeProjection (analyticAt_semilocalEulerMultiplier p hp t₀)
    (isUnit_semilocalEulerGram a t₀ p hp ht)

/-- `(9)`: the tangent of the Euler multiplier at the empty parameter is `-p^{-1/2} U_p*`. -/
def semilocalEulerTangent (p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  -((((Real.sqrt p)⁻¹ : ℝ) : ℂ) • (dilationCLM p (zero_lt_one.trans hp))†)

theorem adjoint_semilocalEulerTangent (p : ℝ) (hp : 1 < p) :
    (semilocalEulerTangent p hp)†
      = -((((Real.sqrt p)⁻¹ : ℝ) : ℂ) • dilationCLM p (zero_lt_one.trans hp)) := by
  rw [semilocalEulerTangent, map_neg, map_smulₛₗ ContinuousLinearMap.adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  simp [Complex.conj_ofReal]

/-- **`(9)`,`(11)`: the derivative of the semilocal projection at the empty Euler parameter.** -/
theorem hasDerivAt_semilocalEulerProjection (a p : ℝ) (hp : 1 < p) :
    HasDerivAt (fun t : ℝ => semilocalEulerProjection a t p hp)
      ((1 - centralSoninProjection a) * semilocalEulerTangent p hp *
          centralSoninProjection a
        + centralSoninProjection a * (semilocalEulerTangent p hp)† *
          (1 - centralSoninProjection a)) 0 :=
  HTGeometry.hasDerivAt_rangeProjection (isIdempotentElem_centralSoninProjection a)
    (hasDerivAt_semilocalEulerMultiplier p hp 0) (semilocalEulerMultiplier_zero p hp)

/-- **`(10)`: the second fundamental form of the semilocal chart is the one-sided dilation
corner.** -/
theorem crossBoundary_semilocalEulerProjectionTangent (a p : ℝ) (hp : 1 < p) :
    crossBoundary (centralSoninProjection a)
        ((1 - centralSoninProjection a) * semilocalEulerTangent p hp *
            centralSoninProjection a
          + centralSoninProjection a * (semilocalEulerTangent p hp)† *
            (1 - centralSoninProjection a))
      = crossBoundary (centralSoninProjection a) (semilocalEulerTangent p hp) := by
  have hQ : centralSoninProjection a * centralSoninProjection a = centralSoninProjection a :=
    isIdempotentElem_centralSoninProjection a
  set Q := centralSoninProjection a with hQdef
  set X := semilocalEulerTangent p hp with hX
  set Y := (semilocalEulerTangent p hp)† with hY
  have hleft : (1 - Q) * (1 - Q) = 1 - Q := by
    have : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
    rw [this, hQ]; abel
  have hzero : (1 - Q) * Q = 0 := by rw [sub_mul, one_mul, hQ, sub_self]
  rw [crossBoundary, crossBoundary]
  calc (1 - Q) * ((1 - Q) * X * Q + Q * Y * (1 - Q)) * Q
      = ((1 - Q) * (1 - Q)) * X * (Q * Q) + ((1 - Q) * Q) * (Y * (1 - Q) * Q) := by
        noncomm_ring
    _ = (1 - Q) * X * Q := by rw [hleft, hQ, hzero, zero_mul, add_zero]

end RHTower
