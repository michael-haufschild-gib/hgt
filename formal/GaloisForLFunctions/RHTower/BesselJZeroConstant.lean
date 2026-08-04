import GaloisForLFunctions.RHTower.FresnelIntegral
import GaloisForLFunctions.RHTower.BesselJZeroSecondSolution

/-!
# The constant in the Bessel asymptotic

The tree proves `sqrt(u) J_0(u) = p cos u + q sin u + O(1/u)` with `p, q` unidentified.  The classical values
are `p = q = 1/sqrt(pi)`, i.e.

```text
J_0(u) = sqrt(2/(pi u)) cos(u - pi/4) + O(u^{-1}),
```

and identifying them is exactly one Fresnel constant.  The route is an *exact* substitution in the cosine
representation `J_0(u) = (2/pi) int_0^{pi/2} cos(u cos φ) dφ`: putting

```text
v = 2 sin(φ/2),      so   cos φ = 1 - v²/2   exactly,
```

turns the phase into a pure quadratic and the Jacobian into `(1 - v²/4)^{-1/2}`:

```text
int_0^{pi/2} exp(i u cos φ) dφ = exp(i u) int_0^{sqrt 2} exp(-i u v²/2) (1 - v²/4)^{-1/2} dv.
```

The Jacobian splits as `1 + g(v)` with `g(v) = O(v²)`, the `1` gives the scaled Fresnel integral and `g`
contributes `O(1/u)` after one integration by parts.  This file collects the pieces: the conjugate and scaled
Fresnel integrals, and the exact substitution.
-/

noncomputable section

open Complex MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-! ## The conjugate Fresnel integral -/

/-- The conjugate Fresnel kernel integrates to the conjugate constant, with the same `2/X` rate. -/
theorem norm_integral_cexp_neg_sq_sub_le {X : ℝ} (hX : 0 < X) :
    ‖(∫ w in (0 : ℝ)..X, Complex.exp (-((w ^ 2 : ℝ) * Complex.I)))
        - (starRingEnd ℂ) fresnelValue‖ ≤ 2 / X := by
  have hconj : ∀ w : ℝ, Complex.exp (-((w ^ 2 : ℝ) * Complex.I))
      = (starRingEnd ℂ) (Complex.exp ((w ^ 2 : ℝ) * Complex.I)) := by
    intro w
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  have hint : (∫ w in (0 : ℝ)..X, Complex.exp (-((w ^ 2 : ℝ) * Complex.I)))
      = (starRingEnd ℂ) (∫ w in (0 : ℝ)..X, Complex.exp ((w ^ 2 : ℝ) * Complex.I)) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    exact intervalIntegral.integral_congr fun w _ => hconj w
  rw [hint, ← map_sub]
  rw [RCLike.norm_conj]
  exact norm_integral_fresnel_sub_le hX

/-! ## The scaled Fresnel integral -/

/-- The quadratic phase `u v²/2` rescales to the pure Fresnel phase. -/
theorem integral_cexp_neg_half_mul_sq {u : ℝ} (hu : 0 < u) :
    (∫ v in (0 : ℝ)..Real.sqrt 2, Complex.exp (-((u * v ^ 2 / 2 : ℝ) * Complex.I)))
      = ((Real.sqrt (2 / u) : ℝ) : ℂ)
        * ∫ w in (0 : ℝ)..Real.sqrt u, Complex.exp (-((w ^ 2 : ℝ) * Complex.I)) := by
  have hc : Real.sqrt (u / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hcsq : Real.sqrt (u / 2) * Real.sqrt (u / 2) = u / 2 :=
    Real.mul_self_sqrt (by positivity)
  have hcv : Real.sqrt (u / 2) * Real.sqrt 2 = Real.sqrt u := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ u / 2)]
    congr 1
    field_simp
  have hcinv : (Real.sqrt (u / 2))⁻¹ = Real.sqrt (2 / u) := by
    rw [← Real.sqrt_inv]
    congr 1
    field_simp
  have hshape : ∀ v : ℝ, Complex.exp (-((u * v ^ 2 / 2 : ℝ) * Complex.I))
      = (fun w : ℝ => Complex.exp (-((w ^ 2 : ℝ) * Complex.I))) (Real.sqrt (u / 2) * v) := by
    intro v
    have hsq : (Real.sqrt (u / 2) * v) ^ 2 = u * v ^ 2 / 2 := by
      have : (Real.sqrt (u / 2)) ^ 2 = u / 2 := by
        rw [sq]
        exact hcsq
      rw [mul_pow, this]
      ring
    simp only [hsq]
  have h := intervalIntegral.integral_comp_mul_left
    (f := fun w : ℝ => Complex.exp (-((w ^ 2 : ℝ) * Complex.I))) (a := 0) (b := Real.sqrt 2) hc
  rw [intervalIntegral.integral_congr (fun v _ => hshape v), h, mul_zero, hcv, hcinv,
    Complex.real_smul]


/-! ## The exact quadratic substitution -/

/-- The Jacobian of the substitution `v = 2 sin(φ/2)`, as a function of `v`. -/
def quadJacobian (u v : ℝ) : ℂ :=
  Complex.exp (((u * (1 - v ^ 2 / 2) : ℝ)) * Complex.I) / ((Real.sqrt (1 - v ^ 2 / 4) : ℝ) : ℂ)

theorem continuousOn_quadJacobian (u : ℝ) :
    ContinuousOn (quadJacobian u) (Icc 0 (Real.pi / 2)) := by
  have hden : ∀ v ∈ Icc (0 : ℝ) (Real.pi / 2), ((Real.sqrt (1 - v ^ 2 / 4) : ℝ) : ℂ) ≠ 0 := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hv2 : v ≤ Real.pi / 2 := hv.2
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hv4 : v < 2 := by linarith
    have hpos : (0 : ℝ) < 1 - v ^ 2 / 4 := by nlinarith [hv4, hv0]
    have := Real.sqrt_pos.mpr hpos
    simpa using ne_of_gt this
  refine ContinuousOn.div ?_ ?_ hden
  · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop))).continuousOn

/-- **The exact quadratic substitution.**  Putting `v = 2 sin(φ/2)` turns `u cos φ` into
`u(1 - v²/2)` *exactly*, because `1 - cos φ = 2 sin²(φ/2)`, and the Jacobian is `(1 - v²/4)^{-1/2}`. -/
theorem integral_cexp_cos_eq_quad (u : ℝ) :
    (∫ φ in (0 : ℝ)..(Real.pi / 2), Complex.exp (((u * Real.cos φ : ℝ)) * Complex.I))
      = ∫ v in (0 : ℝ)..Real.sqrt 2, quadJacobian u v := by
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have huIcc : Set.uIcc (0 : ℝ) (Real.pi / 2) = Icc 0 (Real.pi / 2) := Set.uIcc_of_le hpi2
  have hderiv : ∀ φ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => 2 * Real.sin (t / 2)) (Real.cos (φ / 2)) φ := by
    intro φ _
    have hinner : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) φ := by
      simpa using (hasDerivAt_id φ).div_const 2
    have hsin := (Real.hasDerivAt_sin (φ / 2)).comp φ hinner
    have h := hsin.const_mul (2 : ℝ)
    have hval : 2 * (Real.cos (φ / 2) * (1 / 2)) = Real.cos (φ / 2) := by ring
    rw [hval] at h
    exact h
  have hcont' : ContinuousOn (fun φ : ℝ => Real.cos (φ / 2)) (Set.uIcc 0 (Real.pi / 2)) := by
    fun_prop
  have himage : (fun t : ℝ => 2 * Real.sin (t / 2)) '' Set.uIcc 0 (Real.pi / 2)
      ⊆ Icc 0 (Real.pi / 2) := by
    rw [Set.image_subset_iff]
    intro φ hφ
    rw [huIcc] at hφ
    have hφ0 : 0 ≤ φ := hφ.1
    have hφ2 : φ ≤ Real.pi / 2 := hφ.2
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hlow : 0 ≤ Real.sin (φ / 2) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) ?_
      linarith
    have hup : Real.sin (φ / 2) ≤ φ / 2 := Real.sin_le (by linarith)
    exact ⟨by linarith, by linarith⟩
  have hg : ContinuousOn (quadJacobian u)
      ((fun t : ℝ => 2 * Real.sin (t / 2)) '' Set.uIcc 0 (Real.pi / 2)) :=
    (continuousOn_quadJacobian u).mono himage
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := Real.pi / 2)
    (f := fun t : ℝ => 2 * Real.sin (t / 2)) (f' := fun t : ℝ => Real.cos (t / 2))
    (g := quadJacobian u) hderiv hcont' hg
  have hend0 : 2 * Real.sin ((0 : ℝ) / 2) = 0 := by simp
  have hend1 : 2 * Real.sin ((Real.pi / 2) / 2) = Real.sqrt 2 := by
    have h : (Real.pi / 2) / 2 = Real.pi / 4 := by ring
    rw [h, Real.sin_pi_div_four]
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
  rw [hend0, hend1] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr ?_
  intro φ hφ
  rw [huIcc] at hφ
  have hφ0 : 0 ≤ φ := hφ.1
  have hφ2 : φ ≤ Real.pi / 2 := hφ.2
  have hcos0 : 0 ≤ Real.cos (φ / 2) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ?_⟩
    linarith
  have hcospos : 0 < Real.cos (φ / 2) := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ?_⟩
    linarith [Real.pi_pos]
  have hsin2 : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have h2 : 2 * (φ / 2) = φ := by ring
    have h := Real.cos_two_mul (φ / 2)
    rw [h2] at h
    have hpy := Real.sin_sq_add_cos_sq (φ / 2)
    nlinarith [h, hpy]
  have hjac : Real.sqrt (1 - (2 * Real.sin (φ / 2)) ^ 2 / 4) = Real.cos (φ / 2) := by
    have hval : 1 - (2 * Real.sin (φ / 2)) ^ 2 / 4 = Real.cos (φ / 2) ^ 2 := by
      have hpy := Real.sin_sq_add_cos_sq (φ / 2)
      nlinarith [hpy]
    rw [hval, Real.sqrt_sq hcospos.le]
  have hphase : (u * (1 - (2 * Real.sin (φ / 2)) ^ 2 / 2) : ℝ) = u * Real.cos φ := by
    have h : 1 - (2 * Real.sin (φ / 2)) ^ 2 / 2 = Real.cos φ := by
      nlinarith [hsin2]
    rw [h]
  show Complex.exp (((u * Real.cos φ : ℝ)) * Complex.I)
      = Real.cos (φ / 2) • quadJacobian u (2 * Real.sin (φ / 2))
  rw [quadJacobian, hjac, hphase, Complex.real_smul]
  have hne : ((Real.cos (φ / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hcospos)
  field_simp


/-! ## The Jacobian correction

The Jacobian `(1 - v²/4)^{-1/2}` splits as `1 + g(v)` with

```text
g(v) = 1/sqrt(1 - v²/4) - 1 = v²/(4 s (1+s)),      s = sqrt(1 - v²/4),
```

so `0 <= g(v) <= v²/4` on `[0, sqrt 2]`, and its derivative `g'(v) = v/(4 s³)` is nonnegative and bounded.
The `1` produces the Fresnel integral; `g` contributes `O(u^{-3/4})`, which is `o(u^{-1/2})` and therefore
does not affect the constant. -/

/-- The Jacobian correction. -/
def jacCorr (v : ℝ) : ℝ := 1 / Real.sqrt (1 - v ^ 2 / 4) - 1

/-- Its derivative. -/
def jacCorrDeriv (v : ℝ) : ℝ := v / (4 * Real.sqrt (1 - v ^ 2 / 4) ^ 3)

theorem sqrt_one_sub_quarter_pos {v : ℝ} (hv : v ^ 2 < 4) :
    0 < Real.sqrt (1 - v ^ 2 / 4) := by
  refine Real.sqrt_pos.mpr ?_
  nlinarith

theorem sqrt_one_sub_quarter_le_one {v : ℝ} : Real.sqrt (1 - v ^ 2 / 4) ≤ 1 := by
  rcases le_or_gt (1 - v ^ 2 / 4) 0 with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    norm_num
  · calc Real.sqrt (1 - v ^ 2 / 4) ≤ Real.sqrt 1 := by
          refine Real.sqrt_le_sqrt ?_
          nlinarith [sq_nonneg v]
      _ = 1 := Real.sqrt_one

theorem jacCorr_nonneg {v : ℝ} (hv : v ^ 2 < 4) : 0 ≤ jacCorr v := by
  have hs : 0 < Real.sqrt (1 - v ^ 2 / 4) := sqrt_one_sub_quarter_pos hv
  have hle : Real.sqrt (1 - v ^ 2 / 4) ≤ 1 := sqrt_one_sub_quarter_le_one
  rw [jacCorr, sub_nonneg, le_div_iff₀ hs]
  linarith

/-- The correction is quadratic at the origin: `g(v) <= v²/4` once `s >= 1/2`. -/
theorem jacCorr_le {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ Real.sqrt 2) : jacCorr v ≤ v ^ 2 / 4 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hvsq : v ^ 2 ≤ 2 := by nlinarith [hs2, Real.sqrt_nonneg 2]
  have hv4 : v ^ 2 < 4 := by linarith
  have hs : 0 < Real.sqrt (1 - v ^ 2 / 4) := sqrt_one_sub_quarter_pos hv4
  have hssq : Real.sqrt (1 - v ^ 2 / 4) * Real.sqrt (1 - v ^ 2 / 4) = 1 - v ^ 2 / 4 :=
    Real.mul_self_sqrt (by nlinarith)
  have hhalf : (1 : ℝ) / 2 ≤ Real.sqrt (1 - v ^ 2 / 4) := by
    nlinarith [hssq, hs]
  rw [jacCorr, sub_le_iff_le_add, div_le_iff₀ hs]
  nlinarith [hssq, hs, hhalf]

theorem hasDerivAt_jacCorr {v : ℝ} (hv : v ^ 2 < 4) :
    HasDerivAt jacCorr (jacCorrDeriv v) v := by
  have hs : 0 < Real.sqrt (1 - v ^ 2 / 4) := sqrt_one_sub_quarter_pos hv
  have hpos : (0 : ℝ) < 1 - v ^ 2 / 4 := by nlinarith
  have hinner : HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 4) (-(v / 2)) v := by
    have h : HasDerivAt (fun t : ℝ => t ^ 2 / 4) (2 * v / 4) v := by
      simpa using (hasDerivAt_pow 2 v).div_const 4
    have h2 := h.const_sub 1
    have hval : -(2 * v / 4) = -(v / 2) := by ring
    rw [hval] at h2
    exact h2
  have hsqrt := hinner.sqrt hpos.ne'
  have hone : HasDerivAt (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2 / 4))
      (-(-(v / 2) / (2 * Real.sqrt (1 - v ^ 2 / 4))) / Real.sqrt (1 - v ^ 2 / 4) ^ 2) v := by
    have h := hsqrt.inv (ne_of_gt hs)
    have hfun : ((fun y : ℝ => Real.sqrt (1 - y ^ 2 / 4))⁻¹)
        = fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2 / 4) := by
      funext t
      simp [one_div]
    rw [hfun] at h
    exact h
  have h := hone.sub_const 1
  have hval : -(-(v / 2) / (2 * Real.sqrt (1 - v ^ 2 / 4))) / Real.sqrt (1 - v ^ 2 / 4) ^ 2
      = jacCorrDeriv v := by
    rw [jacCorrDeriv]
    field_simp
    ring
  rw [hval] at h
  have hfun : jacCorr = fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2 / 4) - 1 := by
    funext t
    rw [jacCorr]
  rw [hfun]
  exact h

theorem jacCorrDeriv_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv : v ^ 2 < 4) : 0 ≤ jacCorrDeriv v := by
  have hs : 0 < Real.sqrt (1 - v ^ 2 / 4) := sqrt_one_sub_quarter_pos hv
  rw [jacCorrDeriv]
  positivity

theorem continuousOn_jacCorrDeriv :
    ContinuousOn jacCorrDeriv (Icc 0 (Real.sqrt 2)) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hden : ∀ v ∈ Icc (0 : ℝ) (Real.sqrt 2),
      4 * Real.sqrt (1 - v ^ 2 / 4) ^ 3 ≠ 0 := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hvle : v ≤ Real.sqrt 2 := hv.2
    have hvsq : v ^ 2 ≤ 2 := by nlinarith [hs2, Real.sqrt_nonneg 2]
    have hs : 0 < Real.sqrt (1 - v ^ 2 / 4) := sqrt_one_sub_quarter_pos (by linarith)
    positivity
  refine ContinuousOn.div continuousOn_id ?_ hden
  exact continuousOn_const.mul
    ((Real.continuous_sqrt.comp (by fun_prop)).continuousOn.pow 3)

/-! ## Splitting the Jacobian -/

/-- The Jacobian integrand splits into the pure Fresnel kernel and the correction. -/
theorem quadJacobian_eq {u v : ℝ} (hv : v ^ 2 < 4) :
    quadJacobian u v
      = Complex.exp ((u : ℝ) * Complex.I)
        * (Complex.exp (-((u * v ^ 2 / 2 : ℝ) * Complex.I)) * ((1 + jacCorr v : ℝ) : ℂ)) := by
  have hs : 0 < Real.sqrt (1 - v ^ 2 / 4) := sqrt_one_sub_quarter_pos hv
  have hsne : ((Real.sqrt (1 - v ^ 2 / 4) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hcorr : ((1 + jacCorr v : ℝ) : ℂ) = 1 / ((Real.sqrt (1 - v ^ 2 / 4) : ℝ) : ℂ) := by
    rw [jacCorr]
    push_cast
    ring
  rw [quadJacobian, hcorr,
    show ((u * (1 - v ^ 2 / 2) : ℝ) : ℂ) * Complex.I
      = (u : ℝ) * Complex.I + -((u * v ^ 2 / 2 : ℝ) * Complex.I) by
      push_cast
      ring,
    Complex.exp_add]
  ring



/-! ## The correction is negligible

The correction integral is split at `δ`: below `δ` the integrand is at most `δ²/4` in absolute value, and
above it the phase `u v²/2` has derivative at least `u δ`, so two weighted van der Corput blocks — one with
the constant weight `g(sqrt 2)` and one with the decreasing weight `g(sqrt 2) - g(v)` — bound the rest by
`8 g(sqrt 2)/(u δ)`.  Choosing `δ = u^{-1/4}` balances the two at `u^{-3/4} = o(u^{-1/2})`, so the
correction never reaches the leading term. -/

theorem jacCorr_le_sqrt_two_sub_one {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ Real.sqrt 2) :
    jacCorr v ≤ Real.sqrt 2 - 1 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hvsq : v ^ 2 ≤ 2 := by nlinarith [hs2, Real.sqrt_nonneg 2]
  have hs : 0 < Real.sqrt (1 - v ^ 2 / 4) := sqrt_one_sub_quarter_pos (by linarith)
  have hssq : Real.sqrt (1 - v ^ 2 / 4) * Real.sqrt (1 - v ^ 2 / 4) = 1 - v ^ 2 / 4 :=
    Real.mul_self_sqrt (by nlinarith)
  have hhalf : Real.sqrt 2 / 2 ≤ Real.sqrt (1 - v ^ 2 / 4) := by
    nlinarith [hssq, hs, hs2, hs2pos]
  rw [jacCorr, sub_le_sub_iff_right, div_le_iff₀ hs]
  nlinarith [hhalf, hs2, hs2pos, hs]

/-- The decreasing weight of the far block. -/
def jacWeight (v : ℝ) : ℝ := (Real.sqrt 2 - 1) - jacCorr v

theorem jacWeight_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ Real.sqrt 2) : 0 ≤ jacWeight v := by
  have := jacCorr_le_sqrt_two_sub_one hv0 hv
  rw [jacWeight]
  linarith

theorem hasDerivAt_jacWeight {v : ℝ} (hv : v ^ 2 < 4) :
    HasDerivAt jacWeight (-jacCorrDeriv v) v := by
  have h := (hasDerivAt_jacCorr hv).const_sub (Real.sqrt 2 - 1)
  have hfun : jacWeight = fun t : ℝ => (Real.sqrt 2 - 1) - jacCorr t := by
    funext t
    rw [jacWeight]
  rw [hfun]
  exact h

/-- The far block: the phase derivative is at least `u δ` and both weights are nonnegative and
nonincreasing. -/
theorem norm_integral_jacCorr_far_le {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) (hδ2 : δ ≤ Real.sqrt 2) :
    ‖∫ v in δ..Real.sqrt 2, ((jacCorr v : ℝ) : ℂ)
        * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I)‖
      ≤ 8 * (Real.sqrt 2 - 1) / (u * δ) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs21 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hs2pos]
  have hmem : ∀ v ∈ Set.uIcc δ (Real.sqrt 2), δ ≤ v ∧ v ≤ Real.sqrt 2 := by
    intro v hv
    rw [Set.uIcc_of_le hδ2] at hv
    exact ⟨hv.1, hv.2⟩
  have hvsq : ∀ v ∈ Set.uIcc δ (Real.sqrt 2), v ^ 2 < 4 := by
    intro v hv
    obtain ⟨h1, h2⟩ := hmem v hv
    have hv0 : 0 ≤ v := le_trans hδ.le h1
    nlinarith [hs2, hs2pos]
  -- phase data
  have hg : ∀ v ∈ Set.uIcc δ (Real.sqrt 2),
      HasDerivAt (fun t : ℝ => u * t ^ 2 / 2) (u * v) v := by
    intro v _
    have h : HasDerivAt (fun t : ℝ => u * t ^ 2 / 2) (u * (2 * v) / 2) v := by
      simpa using ((hasDerivAt_pow 2 v).const_mul u).div_const 2
    have hval : u * (2 * v) / 2 = u * v := by ring
    rw [hval] at h
    exact h
  have hg' : ∀ v ∈ Set.uIcc δ (Real.sqrt 2), HasDerivAt (fun t : ℝ => u * t) u v := by
    intro v _
    simpa using (hasDerivAt_id v).const_mul u
  have hg''c : ContinuousOn (fun _ : ℝ => u) (Set.uIcc δ (Real.sqrt 2)) := continuousOn_const
  have hg'lb : ∀ v ∈ Set.uIcc δ (Real.sqrt 2), u * δ ≤ u * v := by
    intro v hv
    exact mul_le_mul_of_nonneg_left (hmem v hv).1 hu.le
  have hg''nn : ∀ v ∈ Set.uIcc δ (Real.sqrt 2), (0 : ℝ) ≤ u := fun _ _ => hu.le
  -- the constant-weight block
  have hconst := _root_.RHTower.norm_integral_weight_cexp_le (a := δ) (b := Real.sqrt 2)
    (lam := u * δ) hδ2 (by positivity)
    (w := fun _ : ℝ => Real.sqrt 2 - 1) (w' := fun _ : ℝ => 0)
    (fun v _ => hasDerivAt_const v (Real.sqrt 2 - 1)) continuousOn_const
    (fun _ _ => by linarith) (fun _ _ => le_refl 0) hg hg' hg''c hg'lb hg''nn
  -- the decreasing-weight block
  have hdec := _root_.RHTower.norm_integral_weight_cexp_le (a := δ) (b := Real.sqrt 2)
    (lam := u * δ) hδ2 (by positivity)
    (w := jacWeight) (w' := fun v : ℝ => -jacCorrDeriv v)
    (fun v hv => hasDerivAt_jacWeight (hvsq v hv))
    (by
      refine ContinuousOn.neg ?_
      refine continuousOn_jacCorrDeriv.mono ?_
      intro v hv
      obtain ⟨h1, h2⟩ := hmem v hv
      exact ⟨le_trans hδ.le h1, h2⟩)
    (fun v hv => jacWeight_nonneg (le_trans hδ.le (hmem v hv).1) (hmem v hv).2)
    (fun v hv => by
      have := jacCorrDeriv_nonneg (le_trans hδ.le (hmem v hv).1) (hvsq v hv)
      linarith)
    hg hg' hg''c hg'lb hg''nn
  -- combine
  have hsplit : (∫ v in δ..Real.sqrt 2, ((jacCorr v : ℝ) : ℂ)
        * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I))
      = (∫ v in δ..Real.sqrt 2, ((Real.sqrt 2 - 1 : ℝ) : ℂ)
          * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I))
        - ∫ v in δ..Real.sqrt 2, ((jacWeight v : ℝ) : ℂ)
          * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I) := by
    rw [← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr ?_
      intro v _
      show ((jacCorr v : ℝ) : ℂ) * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I)
        = ((Real.sqrt 2 - 1 : ℝ) : ℂ) * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I)
          - ((jacWeight v : ℝ) : ℂ) * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I)
      rw [jacWeight]
      push_cast
      ring
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      refine Continuous.mul ?_ (by fun_prop)
      refine Complex.continuous_ofReal.comp ?_
      rw [show jacWeight = fun t : ℝ => (Real.sqrt 2 - 1) - jacCorr t from by
        funext t
        rw [jacWeight]]
      refine continuous_const.sub ?_
      rw [show jacCorr = fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2 / 4) - 1 from by
        funext t
        rw [jacCorr]]
      fun_prop
  rw [hsplit]
  have htri : ‖(∫ v in δ..Real.sqrt 2, ((Real.sqrt 2 - 1 : ℝ) : ℂ)
        * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I))
      - ∫ v in δ..Real.sqrt 2, ((jacWeight v : ℝ) : ℂ)
        * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I)‖
      ≤ ‖∫ v in δ..Real.sqrt 2, ((Real.sqrt 2 - 1 : ℝ) : ℂ)
          * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I)‖
        + ‖∫ v in δ..Real.sqrt 2, ((jacWeight v : ℝ) : ℂ)
          * Complex.exp (((u * v ^ 2 / 2 : ℝ)) * Complex.I)‖ := norm_sub_le _ _
  have hw0 : jacWeight δ ≤ Real.sqrt 2 - 1 := by
    have h := jacCorr_nonneg (v := δ) (by nlinarith [hs2, hs2pos])
    rw [jacWeight]
    linarith
  have hb1 : 4 * (Real.sqrt 2 - 1) / (u * δ) + 4 * jacWeight δ / (u * δ)
      ≤ 8 * (Real.sqrt 2 - 1) / (u * δ) := by
    rw [div_add_div_same, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hw0]
  linarith [htri, hconst, hdec, hb1]


end GaloisForLFunctions.RHTower

end
