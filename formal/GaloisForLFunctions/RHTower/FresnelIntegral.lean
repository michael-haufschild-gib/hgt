import GaloisForLFunctions.RHTower.VanDerCorputWeighted
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Fresnel integral

mathlib has the Gaussian integral `int exp(-b x²) = (pi/b)^{1/2}` for every complex `b` with positive real
part, but not the boundary case `b = -i`, where the integrand no longer decays and the integral is only
conditionally convergent.  That boundary case is the Fresnel integral

```text
int_0^infinity exp(i x²) dx = sqrt(pi) exp(i pi/4)/2,
```

equivalently `int_0^infinity cos(x²) dx = int_0^infinity sin(x²) dx = sqrt(pi/2)/2`.  It is the constant
behind every stationary-phase expansion, in particular the amplitude and the phase shift of the Bessel
asymptotic `J_0(u) ~ sqrt(2/(pi u)) cos(u - pi/4)`.

The proof needs no contour integration.  The regularised kernel splits as

```text
exp(-(eps - i) x²) = exp(-eps x²) · exp(i x²),
```

a decreasing weight against a convex phase, so the weighted van der Corput test bounds every tail by `2/A`
*uniformly in the regularisation*.  Comparing the truncated Fresnel integral with the regularised Gaussian
integral therefore gives

```text
|int_0^R exp(i x²) dx - (pi/(eps - i))^{1/2}/2| <= R (1 - exp(-eps R²)) + 2/R,
```

and letting `eps -> 0` at fixed `R` kills the first term.
-/

noncomputable section

open Complex MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-! ## The regularised kernel -/

/-- The regularised Fresnel kernel is a real decreasing weight times the pure phase. -/
theorem cexp_fresnel_split (ε x : ℝ) :
    Complex.exp (-((ε : ℂ) - Complex.I) * (x : ℂ) ^ 2)
      = (Real.exp (-(ε * x ^ 2)) : ℂ) * Complex.exp ((x ^ 2 : ℝ) * Complex.I) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The uniform tail bound -/

/-- **Every tail of the regularised Fresnel integral is at most `2/A`, uniformly in the regularisation.**
The weight `exp(-eps x²)` is nonnegative and decreasing on the ray and the phase `x²` is convex with
derivative at least `2A`, so the weighted first-derivative van der Corput test applies with no dependence on
`eps`. -/
theorem norm_integral_fresnel_tail_le {ε A B : ℝ} (hε : 0 ≤ ε) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ x in A..B, (Real.exp (-(ε * x ^ 2)) : ℂ) * Complex.exp ((x ^ 2 : ℝ) * Complex.I)‖
      ≤ 2 / A := by
  have hmem : ∀ x ∈ Set.uIcc A B, A ≤ x ∧ x ≤ B := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    exact ⟨hx.1, hx.2⟩
  have hw : ∀ x ∈ Set.uIcc A B, HasDerivAt (fun t : ℝ => Real.exp (-(ε * t ^ 2)))
      (Real.exp (-(ε * x ^ 2)) * -(ε * (2 * x))) x := by
    intro x _
    have h : HasDerivAt (fun t : ℝ => ε * t ^ 2) (ε * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul ε
    have h2 := h.neg
    have hfun : (-fun t : ℝ => ε * t ^ 2) = fun t : ℝ => -(ε * t ^ 2) := by
      funext t
      simp
    rw [hfun] at h2
    exact h2.exp
  have hw'c : ContinuousOn (fun x : ℝ => Real.exp (-(ε * x ^ 2)) * -(ε * (2 * x)))
      (Set.uIcc A B) := by fun_prop
  have hwnn : ∀ x ∈ Set.uIcc A B, (0 : ℝ) ≤ Real.exp (-(ε * x ^ 2)) :=
    fun x _ => (Real.exp_pos _).le
  have hwanti : ∀ x ∈ Set.uIcc A B, Real.exp (-(ε * x ^ 2)) * -(ε * (2 * x)) ≤ 0 := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans hA.le (hmem x hx).1
    have h1 : 0 ≤ ε * (2 * x) := by positivity
    have h2 : (0 : ℝ) < Real.exp (-(ε * x ^ 2)) := Real.exp_pos _
    nlinarith [h1, h2]
  have hg : ∀ x ∈ Set.uIcc A B, HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    intro x _
    simpa using hasDerivAt_pow 2 x
  have hg' : ∀ x ∈ Set.uIcc A B, HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    intro x _
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hg''c : ContinuousOn (fun _ : ℝ => (2 : ℝ)) (Set.uIcc A B) := continuousOn_const
  have hg'lb : ∀ x ∈ Set.uIcc A B, 2 * A ≤ 2 * x := by
    intro x hx
    have := (hmem x hx).1
    linarith
  have hg''nn : ∀ x ∈ Set.uIcc A B, (0 : ℝ) ≤ 2 := fun _ _ => by norm_num
  have h := _root_.RHTower.norm_integral_weight_cexp_le (a := A) (b := B) (lam := 2 * A) hAB
    (by linarith) hw hw'c hwnn hwanti hg hg' hg''c hg'lb hg''nn
  have hexp : Real.exp (-(ε * A ^ 2)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ ε * A ^ 2 := by positivity
    linarith
  have hbound : 4 * Real.exp (-(ε * A ^ 2)) / (2 * A) ≤ 2 / A := by
    rw [div_le_div_iff₀ (by positivity) hA]
    nlinarith [hexp, hA]
  exact le_trans h hbound


/-! ## The regularised integral on the ray -/

/-- The boundary Gaussian value: the Fresnel constant, in Gaussian form. -/
def fresnelValue : ℂ := ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2

/-- The regularised Gaussian value. -/
def fresnelRegValue (ε : ℝ) : ℂ := ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2

/-- Notation for the Fresnel kernel with regularisation `ε`. -/
def fresnelKernel (ε x : ℝ) : ℂ :=
  (Real.exp (-(ε * x ^ 2)) : ℂ) * Complex.exp ((x ^ 2 : ℝ) * Complex.I)

theorem fresnelKernel_eq (ε x : ℝ) :
    fresnelKernel ε x = Complex.exp (-((ε : ℂ) - Complex.I) * (x : ℂ) ^ 2) := by
  rw [fresnelKernel, cexp_fresnel_split]

theorem re_sub_I_pos {ε : ℝ} (hε : 0 < ε) : 0 < ((ε : ℂ) - Complex.I).re := by
  simpa using hε

theorem integrable_fresnelKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => fresnelKernel ε x) volume := by
  have h := integrable_cexp_neg_mul_sq (re_sub_I_pos hε)
  refine h.congr ?_
  filter_upwards with x
  exact (fresnelKernel_eq ε x).symm

/-- The regularised Fresnel integral on the ray is mathlib's complex Gaussian integral. -/
theorem integral_Ioi_fresnelKernel {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ioi (0 : ℝ), fresnelKernel ε x) = fresnelRegValue ε := by
  rw [fresnelRegValue, ← integral_gaussian_complex_Ioi (re_sub_I_pos hε)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _
  exact fresnelKernel_eq ε x

/-- The tail of the regularised integral on the ray is at most `2/R`, uniformly in `ε`. -/
theorem norm_integral_Ioi_fresnelKernel_tail_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ‖∫ x in Ioi R, fresnelKernel ε x‖ ≤ 2 / R := by
  have hint : IntegrableOn (fun x : ℝ => fresnelKernel ε x) (Ioi R) volume :=
    (integrable_fresnelKernel hε).integrableOn
  have htend := intervalIntegral_tendsto_integral_Ioi R hint Filter.tendsto_id
  refine le_of_tendsto htend.norm ?_
  filter_upwards [Filter.eventually_ge_atTop R] with B hB
  exact norm_integral_fresnel_tail_le hε.le hR hB

/-- The ray integral splits at `R`. -/
theorem integral_Ioi_fresnelKernel_split {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (∫ x in Ioi (0 : ℝ), fresnelKernel ε x)
      = (∫ x in (0 : ℝ)..R, fresnelKernel ε x) + ∫ x in Ioi R, fresnelKernel ε x := by
  have hd : Disjoint (Ioc (0 : ℝ) R) (Ioi R) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx')
  have hunion : Ioc (0 : ℝ) R ∪ Ioi R = Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hR.le
  have hint1 : IntegrableOn (fun x : ℝ => fresnelKernel ε x) (Ioc (0 : ℝ) R) volume :=
    (integrable_fresnelKernel hε).integrableOn
  have hint2 : IntegrableOn (fun x : ℝ => fresnelKernel ε x) (Ioi R) volume :=
    (integrable_fresnelKernel hε).integrableOn
  rw [← hunion, MeasureTheory.setIntegral_union hd measurableSet_Ioi hint1 hint2,
    intervalIntegral.integral_of_le hR.le]

/-! ## Removing the regularisation -/

/-- The regularisation costs at most `R (1 - exp(-ε R²))` on `[0, R]`. -/
theorem norm_integral_fresnel_dereg_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ‖(∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
        - ∫ x in (0 : ℝ)..R, fresnelKernel ε x‖
      ≤ (1 - Real.exp (-(ε * R ^ 2))) * R := by
  have hcont1 : IntervalIntegrable (fun x : ℝ => Complex.exp ((x ^ 2 : ℝ) * Complex.I))
      volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcont2 : IntervalIntegrable (fun x : ℝ => fresnelKernel ε x) volume 0 R := by
    apply Continuous.intervalIntegrable
    rw [show (fun x : ℝ => fresnelKernel ε x)
        = fun x : ℝ => (Real.exp (-(ε * x ^ 2)) : ℂ) * Complex.exp ((x ^ 2 : ℝ) * Complex.I) from
      rfl]
    fun_prop
  rw [← intervalIntegral.integral_sub hcont1 hcont2]
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) R,
      ‖Complex.exp ((x ^ 2 : ℝ) * Complex.I) - fresnelKernel ε x‖
        ≤ 1 - Real.exp (-(ε * R ^ 2)) := by
    intro x hx
    rw [Set.uIoc_of_le hR.le] at hx
    have hx0 : 0 ≤ x := hx.1.le
    have hxR : x ≤ R := hx.2
    have hsplit : Complex.exp ((x ^ 2 : ℝ) * Complex.I) - fresnelKernel ε x
        = ((1 - Real.exp (-(ε * x ^ 2)) : ℝ) : ℂ) * Complex.exp ((x ^ 2 : ℝ) * Complex.I) := by
      rw [fresnelKernel]
      push_cast
      ring
    rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
    have h1 : Real.exp (-(ε * R ^ 2)) ≤ Real.exp (-(ε * x ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have : ε * x ^ 2 ≤ ε * R ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        nlinarith
      linarith
    have h2 : Real.exp (-(ε * x ^ 2)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ ε * x ^ 2 := by positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - Real.exp (-(ε * x ^ 2)))]
    linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [abs_of_nonneg hR.le] using h



/-! ## The Fresnel limit -/

/-- The regularised value converges as the regularisation is removed. -/
theorem tendsto_fresnelRegValue :
    Filter.Tendsto fresnelRegValue (nhds 0) (nhds fresnelValue) := by
  have hden : ((0 : ℝ) : ℂ) - Complex.I = -Complex.I := by
    push_cast
    ring
  have hne : (-Complex.I) ≠ 0 := by simp
  have hbase : (Real.pi : ℂ) / (-Complex.I) = (Real.pi : ℂ) * Complex.I := by
    rw [div_eq_iff hne]
    have hII : Complex.I * (-Complex.I) = 1 := by
      simp [Complex.I_mul_I]
    calc (Real.pi : ℂ) = (Real.pi : ℂ) * 1 := by ring
      _ = (Real.pi : ℂ) * (Complex.I * (-Complex.I)) := by rw [hII]
      _ = (Real.pi : ℂ) * Complex.I * (-Complex.I) := by ring
  have hcont1 : ContinuousAt (fun ε : ℝ => (Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) 0 := by
    have hd : ContinuousAt (fun ε : ℝ => ((ε : ℂ) - Complex.I)) 0 :=
      (Complex.continuous_ofReal.continuousAt).sub continuousAt_const
    refine continuousAt_const.div hd ?_
    rw [hden]
    exact hne
  have hpt : (Real.pi : ℂ) / ((((0 : ℝ)) : ℂ) - Complex.I) = (Real.pi : ℂ) * Complex.I := by
    rw [hden, hbase]
  have hslit : (Real.pi : ℂ) / ((((0 : ℝ)) : ℂ) - Complex.I) ∈ Complex.slitPlane := by
    rw [hpt, Complex.mem_slitPlane_iff]
    right
    simp
  have hcomp : ContinuousAt
      (fun ε : ℝ => ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ)) 0 :=
    hcont1.cpow continuousAt_const hslit
  have h := hcomp.div_const 2
  have hfun : fresnelRegValue
      = fun ε : ℝ => ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2 := by
    funext ε
    rw [fresnelRegValue]
  have hval : ((Real.pi : ℂ) / ((((0 : ℝ)) : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2
      = fresnelValue := by
    rw [fresnelValue, hden]
  rw [hfun]
  rw [ContinuousAt, hval] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **The truncated Fresnel integral is within `2/R` of the boundary Gaussian value.**  The regularised
comparison costs `R(1 - exp(-εR²))` on `[0,R]` and `2/R` beyond it, and the first cost vanishes as the
regularisation is removed. -/
theorem norm_integral_fresnel_sub_le {R : ℝ} (hR : 0 < R) :
    ‖(∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I)) - fresnelValue‖ ≤ 2 / R := by
  set F := ∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I) with hF
  have key : ∀ ε : ℝ, 0 < ε →
      ‖F - fresnelValue‖ ≤ (1 - Real.exp (-(ε * R ^ 2))) * R + 2 / R
        + ‖fresnelRegValue ε - fresnelValue‖ := by
    intro ε hε
    set G := ∫ x in (0 : ℝ)..R, fresnelKernel ε x with hG
    have e1 : G - fresnelRegValue ε = -(∫ x in Ioi R, fresnelKernel ε x) := by
      rw [hG, ← integral_Ioi_fresnelKernel hε, integral_Ioi_fresnelKernel_split hε hR]
      ring
    have h1 : ‖F - G‖ ≤ (1 - Real.exp (-(ε * R ^ 2))) * R := by
      rw [hF, hG]
      exact norm_integral_fresnel_dereg_le hε hR
    have h2 : ‖G - fresnelRegValue ε‖ ≤ 2 / R := by
      rw [e1, norm_neg]
      exact norm_integral_Ioi_fresnelKernel_tail_le hε hR
    have t1 : ‖F - fresnelValue‖ ≤ ‖F - G‖ + ‖G - fresnelValue‖ := by
      simpa [dist_eq_norm] using dist_triangle F G fresnelValue
    have t2 : ‖G - fresnelValue‖ ≤ ‖G - fresnelRegValue ε‖ + ‖fresnelRegValue ε - fresnelValue‖ := by
      simpa [dist_eq_norm] using dist_triangle G (fresnelRegValue ε) fresnelValue
    linarith [t1, t2, h1, h2]
  have htend : Filter.Tendsto (fun ε : ℝ => (1 - Real.exp (-(ε * R ^ 2))) * R + 2 / R
        + ‖fresnelRegValue ε - fresnelValue‖)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 / R)) := by
    have ha : Filter.Tendsto (fun ε : ℝ => (1 - Real.exp (-(ε * R ^ 2))) * R)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun ε : ℝ => (1 - Real.exp (-(ε * R ^ 2))) * R) 0 := by fun_prop
      have h0 : (1 - Real.exp (-((0 : ℝ) * R ^ 2))) * R = 0 := by norm_num
      have hcw := hc.continuousWithinAt (s := Set.Ioi (0 : ℝ))
      rwa [ContinuousWithinAt, h0] at hcw
    have hb : Filter.Tendsto (fun ε : ℝ => ‖fresnelRegValue ε - fresnelValue‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h0 : Filter.Tendsto fresnelRegValue (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds fresnelValue) := tendsto_fresnelRegValue.mono_left nhdsWithin_le_nhds
      have h := h0.sub_const fresnelValue
      have h2 := h.norm
      simpa using h2
    have hconst : Filter.Tendsto (fun _ : ℝ => 2 / R) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (2 / R)) := tendsto_const_nhds
    have hsum := (ha.add hconst).add hb
    simpa using hsum
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

/-- **The Fresnel integral.**  The truncated integral of the pure quadratic phase converges, and its value
is the boundary case of the Gaussian integral. -/
theorem tendsto_integral_cexp_sq_atTop :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
      Filter.atTop (nhds fresnelValue) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun R : ℝ => 2 / R)
    (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_integral_fresnel_sub_le hR
  · exact tendsto_const_nhds.div_atTop Filter.tendsto_id


/-! ## The explicit constant -/

private theorem pi_mul_I_ne_zero : (Real.pi : ℂ) * Complex.I ≠ 0 := by
  simp [Real.pi_ne_zero]

/-- The principal square root of `pi i` is `sqrt(pi) exp(i pi/4)`. -/
theorem cpow_pi_mul_I_half :
    ((Real.pi : ℂ) * Complex.I) ^ (1 / 2 : ℂ)
      = ((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  have hnorm : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have harg : Complex.arg ((Real.pi : ℂ) * Complex.I) = Real.pi / 2 := by
    rw [Complex.arg_real_mul _ Real.pi_pos, Complex.arg_I]
  have hlog : Complex.log ((Real.pi : ℂ) * Complex.I)
      = ((Real.log Real.pi : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    rw [Complex.log, hnorm, harg]
  rw [Complex.cpow_def_of_ne_zero pi_mul_I_ne_zero, hlog,
    show (((Real.log Real.pi : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) * (1 / 2 : ℂ)
      = ((Real.log Real.pi / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos]
  congr 1
  ring

/-- **The Fresnel constant in explicit form.** -/
theorem fresnelValue_eq :
    fresnelValue
      = ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  have hne : (-Complex.I) ≠ 0 := by simp
  have hbase : (Real.pi : ℂ) / (-Complex.I) = (Real.pi : ℂ) * Complex.I := by
    rw [div_eq_iff hne]
    have hII : Complex.I * (-Complex.I) = 1 := by
      simp [Complex.I_mul_I]
    calc (Real.pi : ℂ) = (Real.pi : ℂ) * 1 := by ring
      _ = (Real.pi : ℂ) * (Complex.I * (-Complex.I)) := by rw [hII]
      _ = (Real.pi : ℂ) * Complex.I * (-Complex.I) := by ring
  rw [fresnelValue, hbase, cpow_pi_mul_I_half]
  push_cast
  ring

/-! ## The real Fresnel integrals -/

theorem intervalIntegrable_cexp_sq (R : ℝ) :
    IntervalIntegrable (fun x : ℝ => Complex.exp ((x ^ 2 : ℝ) * Complex.I)) volume 0 R := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- **The Fresnel cosine integral.**  `int_0^infinity cos(x²) dx = sqrt(pi/2)/2`. -/
theorem tendsto_integral_cos_sq_atTop :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.cos (x ^ 2)) Filter.atTop
      (nhds (Real.sqrt (Real.pi / 2) / 2)) := by
  have hre : ∀ R : ℝ, (∫ x in (0 : ℝ)..R, Real.cos (x ^ 2))
      = (∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I)).re := by
    intro R
    have h := intervalIntegral.intervalIntegral_re
      (f := fun x : ℝ => Complex.exp ((x ^ 2 : ℝ) * Complex.I))
      (a := 0) (b := R) (μ := volume) (intervalIntegrable_cexp_sq R)
    have hcongr : (∫ x in (0 : ℝ)..R, Real.cos (x ^ 2))
        = ∫ x in (0 : ℝ)..R, RCLike.re (Complex.exp ((x ^ 2 : ℝ) * Complex.I)) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      show Real.cos (x ^ 2) = RCLike.re (Complex.exp (((x ^ 2 : ℝ) : ℂ) * Complex.I))
      have hpt : RCLike.re (Complex.exp (((x ^ 2 : ℝ) : ℂ) * Complex.I))
          = (Complex.exp (((x ^ 2 : ℝ) : ℂ) * Complex.I)).re := rfl
      rw [hpt, Complex.exp_ofReal_mul_I_re]
    rw [hcongr, h]
    rfl
  have hlim := tendsto_integral_cexp_sq_atTop
  have hcont : Filter.Tendsto
      (fun R : ℝ => (∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I)).re) Filter.atTop
      (nhds fresnelValue.re) := (Complex.continuous_re.continuousAt).tendsto.comp hlim
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : Real.sqrt (Real.pi / 2) = Real.sqrt Real.pi / Real.sqrt 2 :=
    Real.sqrt_div (by positivity) 2
  have hre_exp : (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)).re = Real.sqrt 2 / 2 := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]
  have hval : fresnelValue.re = Real.sqrt (Real.pi / 2) / 2 := by
    rw [fresnelValue_eq, Complex.mul_re, hre_exp]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h2]
    field_simp
    nlinarith [hsq, hs2, Real.sqrt_nonneg Real.pi]
  rw [funext hre]
  rw [← hval]
  exact hcont



/-- **The Fresnel sine integral.**  `int_0^infinity sin(x²) dx = sqrt(pi/2)/2`, the same value as the
cosine integral: the boundary Gaussian value has equal real and imaginary parts, which is exactly the
phase `pi/4`. -/
theorem tendsto_integral_sin_sq_atTop :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sin (x ^ 2)) Filter.atTop
      (nhds (Real.sqrt (Real.pi / 2) / 2)) := by
  have hre : ∀ R : ℝ, (∫ x in (0 : ℝ)..R, Real.sin (x ^ 2))
      = (∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I)).im := by
    intro R
    have h := intervalIntegral.intervalIntegral_im
      (f := fun x : ℝ => Complex.exp ((x ^ 2 : ℝ) * Complex.I))
      (a := 0) (b := R) (μ := volume) (intervalIntegrable_cexp_sq R)
    have hcongr : (∫ x in (0 : ℝ)..R, Real.sin (x ^ 2))
        = ∫ x in (0 : ℝ)..R, RCLike.im (Complex.exp ((x ^ 2 : ℝ) * Complex.I)) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      show Real.sin (x ^ 2) = RCLike.im (Complex.exp (((x ^ 2 : ℝ) : ℂ) * Complex.I))
      have hpt : RCLike.im (Complex.exp (((x ^ 2 : ℝ) : ℂ) * Complex.I))
          = (Complex.exp (((x ^ 2 : ℝ) : ℂ) * Complex.I)).im := rfl
      rw [hpt, Complex.exp_ofReal_mul_I_im]
    rw [hcongr, h]
    rfl
  have hlim := tendsto_integral_cexp_sq_atTop
  have hcont : Filter.Tendsto
      (fun R : ℝ => (∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I)).im) Filter.atTop
      (nhds fresnelValue.im) := (Complex.continuous_im.continuousAt).tendsto.comp hlim
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : Real.sqrt (Real.pi / 2) = Real.sqrt Real.pi / Real.sqrt 2 :=
    Real.sqrt_div (by positivity) 2
  have him_exp : (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)).im = Real.sqrt 2 / 2 := by
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four]
  have hval : fresnelValue.im = Real.sqrt (Real.pi / 2) / 2 := by
    rw [fresnelValue_eq, Complex.mul_im, him_exp]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [h2]
    field_simp
    nlinarith [hsq, hs2, Real.sqrt_nonneg Real.pi]
  rw [funext hre, ← hval]
  exact hcont


end GaloisForLFunctions.RHTower

end
