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
    (∫ x in Ioi (0 : ℝ), fresnelKernel ε x)
      = ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2 := by
  rw [← integral_gaussian_complex_Ioi (re_sub_I_pos hε)]
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
theorem tendsto_fresnel_reg_value :
    Filter.Tendsto (fun ε : ℝ => ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2)
      (nhds 0) (nhds (((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2)) := by
  have hden : ((0 : ℝ) : ℂ) - Complex.I = -Complex.I := by
    push_cast
    ring
  have hne : (-Complex.I) ≠ 0 := by
    simp
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
  have hcomp : ContinuousAt
      (fun ε : ℝ => ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ)) 0 := by
    refine hcont1.cpow_const ?_
    right
    rw [hpt]
    simp [Real.pi_ne_zero]
  have h := (hcomp.div_const 2)
  have hval : ((Real.pi : ℂ) / ((((0 : ℝ)) : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2
      = ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2 := by
    rw [hden]
  rw [ContinuousAt, hval] at h
  exact h

/-- **The truncated Fresnel integral is within `2/R` of the boundary Gaussian value.**  The regularised
comparison costs `R(1 - exp(-εR²))` on `[0,R]` and `2/R` beyond it, and the first cost vanishes as the
regularisation is removed. -/
theorem norm_integral_fresnel_sub_le {R : ℝ} (hR : 0 < R) :
    ‖(∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
        - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖ ≤ 2 / R := by
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
          - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖
        ≤ (1 - Real.exp (-(ε * R ^ 2))) * R + 2 / R
          + ‖((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2
              - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖ := by
    intro ε hε
    have hsplit := integral_Ioi_fresnelKernel_split hε hR
    have hval := integral_Ioi_fresnelKernel hε
    have e1 : (∫ x in (0 : ℝ)..R, fresnelKernel ε x)
        - ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2
        = -(∫ x in Ioi R, fresnelKernel ε x) := by
      rw [← hval, hsplit]
      ring
    have h1 := norm_integral_fresnel_dereg_le hε hR
    have h2 := norm_integral_Ioi_fresnelKernel_tail_le hε hR
    have t1 : ‖(∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
          - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖
        ≤ ‖(∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
            - (∫ x in (0 : ℝ)..R, fresnelKernel ε x)‖
          + ‖(∫ x in (0 : ℝ)..R, fresnelKernel ε x)
              - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖ := by
      simpa [dist_eq_norm] using dist_triangle
        (∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
        (∫ x in (0 : ℝ)..R, fresnelKernel ε x)
        (((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2)
    have t2 : ‖(∫ x in (0 : ℝ)..R, fresnelKernel ε x)
          - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖
        ≤ ‖(∫ x in (0 : ℝ)..R, fresnelKernel ε x)
            - ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2‖
          + ‖((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2
              - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖ := by
      simpa [dist_eq_norm] using dist_triangle
        (∫ x in (0 : ℝ)..R, fresnelKernel ε x)
        (((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2)
        (((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2)
    have t3 : ‖(∫ x in (0 : ℝ)..R, fresnelKernel ε x)
        - ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2‖ ≤ 2 / R := by
      rw [e1, norm_neg]
      exact h2
    linarith [t1, t2, t3, h1]
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_self_neBot
  have htend : Filter.Tendsto (fun ε : ℝ => (1 - Real.exp (-(ε * R ^ 2))) * R + 2 / R
        + ‖((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2
            - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 / R)) := by
    have ha : Filter.Tendsto (fun ε : ℝ => (1 - Real.exp (-(ε * R ^ 2))) * R)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun ε : ℝ => (1 - Real.exp (-(ε * R ^ 2))) * R) 0 := by fun_prop
      have h0 : (1 - Real.exp (-((0 : ℝ) * R ^ 2))) * R = 0 := by norm_num
      have := hc.continuousWithinAt (s := Set.Ioi (0 : ℝ))
      rwa [ContinuousWithinAt, h0] at this
    have hb : Filter.Tendsto (fun ε : ℝ =>
          ‖((Real.pi : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ) / 2
            - ((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := (tendsto_fresnel_reg_value.mono_left nhdsWithin_le_nhds).sub_const
        (((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2)
      have h2 := h.norm
      simpa using h2
    have := (ha.add tendsto_const_nhds).add hb
    simpa using this
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

/-- **The Fresnel integral.**  The truncated integral of the pure quadratic phase converges, and its value
is the boundary case of the Gaussian integral. -/
theorem tendsto_integral_cexp_sq_atTop :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Complex.exp ((x ^ 2 : ℝ) * Complex.I))
      Filter.atTop (nhds (((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ) / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_integral_fresnel_sub_le hR
  · exact tendsto_const_nhds.div_atTop Filter.tendsto_id


end GaloisForLFunctions.RHTower

end
