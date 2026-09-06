import Mathlib

/-!
# The one-dimensional Brascamp–Lieb inequality

For a probability density `ρ` on `ℝ` with `ρ' = −V' ρ` and `V'' > 0`, every `C¹` function `f`
satisfies

```text
Var_ρ(f) ≤ ∫ (f')² / V'' · ρ .
```

The proof avoids the Hörmander/Witten-Laplacian machinery entirely. Write the variance as
`½∬ (f(x) − f(y))² ρ(x)ρ(y)`. For `x < y`, Cauchy–Schwarz against the weight `V''` gives
`(f(y) − f(x))² = (∫ₓ^y f')² ≤ (∫ₓ^y (f')²/V'') · (V'(y) − V'(x))`. Exchanging the order of integration,
the coefficient of `(f')²/V''` at the point `t` is

```text
∬_{x < t < y} (V'(y) − V'(x)) ρ(x)ρ(y) dx dy  =  ρ(t) ,
```

because `∫_{y>t} V' ρ = ρ(t)` and `∫_{x<t} V' ρ = −ρ(t)` (the derivative of `−ρ` is `V' ρ`, and `ρ`
vanishes at `±∞`). Nothing else enters: no boundary behaviour of `f`, no solution of a differential
equation, no compactness. Mathlib has no version of this inequality.

The hypotheses are: `ρ > 0` with `ρ' = −V'ρ`; `V'` differentiable with `V''` continuous and positive;
`f` differentiable with `f'` continuous; `ρ → 0` at `±∞`; integrability of `ρ`, `V'ρ`, `fρ`, `f²ρ`,
`(f')²ρ/V''`; and the normalisation `∫ ρ = 1`. The corollary `variance_le_of_exp` specialises to
`ρ = exp(−V)`.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

namespace OneDimBrascampLieb

/-! ### Cauchy–Schwarz on an interval -/

/-- Cauchy–Schwarz for continuous functions on `[x, y]`. -/
theorem sq_intervalIntegral_mul_le {x y : ℝ} (hxy : x ≤ y) {a b : ℝ → ℝ}
    (ha : ContinuousOn a (Icc x y)) (hb : ContinuousOn b (Icc x y)) :
    (∫ t in x..y, a t * b t) ^ 2 ≤ (∫ t in x..y, a t ^ 2) * (∫ t in x..y, b t ^ 2) := by
  have hia : IntervalIntegrable (fun t => a t ^ 2) volume x y :=
    (ha.pow 2).intervalIntegrable_of_Icc hxy
  have hib : IntervalIntegrable (fun t => b t ^ 2) volume x y :=
    (hb.pow 2).intervalIntegrable_of_Icc hxy
  have hiab : IntervalIntegrable (fun t => a t * b t) volume x y :=
    (ha.mul hb).intervalIntegrable_of_Icc hxy
  set A := ∫ t in x..y, a t ^ 2 with hA
  set B := ∫ t in x..y, b t ^ 2 with hB
  set C := ∫ t in x..y, a t * b t with hC
  have key : ∀ l : ℝ, 0 ≤ A - 2 * l * C + l ^ 2 * B := by
    intro l
    have h0 : 0 ≤ ∫ t in x..y, (a t - l * b t) ^ 2 :=
      intervalIntegral.integral_nonneg hxy (fun t _ => sq_nonneg _)
    have hexp : ∫ t in x..y, (a t - l * b t) ^ 2 = A - 2 * l * C + l ^ 2 * B := by
      have e : (fun t => (a t - l * b t) ^ 2) =
          fun t => (a t ^ 2 - (2 * l) * (a t * b t)) + l ^ 2 * b t ^ 2 := by
        funext t; ring
      rw [e, intervalIntegral.integral_add (hia.sub (hiab.const_mul _)) (hib.const_mul _),
        intervalIntegral.integral_sub hia (hiab.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    linarith [h0, hexp]
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg hxy (fun t _ => sq_nonneg _)
  rcases hB0.lt_or_eq with hBpos | hBzero
  · have h := key (C / B)
    have h2 : A - 2 * (C / B) * C + (C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp
      ring
    rw [h2, sub_nonneg, div_le_iff₀ hBpos] at h
    linarith
  · have hC : C = 0 := by
      by_contra hC
      have h := key ((A + 1) / (2 * C))
      rw [← hBzero, mul_zero, add_zero] at h
      have h3 : 2 * ((A + 1) / (2 * C)) * C = A + 1 := by
        field_simp
      linarith
    rw [hC, ← hBzero]
    simp

/-! ### The pointwise Cauchy–Schwarz bound against the curvature -/

/-- For `x ≤ y`, `(f(y) − f(x))² ≤ (∫ₓ^y (f')²/V'') · (V'(y) − V'(x))`. -/
theorem sq_sub_le_integral_mul {f f' V' V'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hV' : ∀ x, HasDerivAt V' (V'' x) x) (hV''c : Continuous V'') (hV''pos : ∀ x, 0 < V'' x)
    {x y : ℝ} (hxy : x ≤ y) :
    (f y - f x) ^ 2 ≤ (∫ t in x..y, f' t ^ 2 / V'' t) * (V' y - V' x) := by
  have hfxy : f y - f x = ∫ t in x..y, f' t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t)
      (hf'c.intervalIntegrable _ _)).symm
  have hVxy : V' y - V' x = ∫ t in x..y, V'' t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hV' t)
      (hV''c.intervalIntegrable _ _)).symm
  have hsqrt_pos : ∀ t, 0 < Real.sqrt (V'' t) := fun t => Real.sqrt_pos.mpr (hV''pos t)
  have hac : ContinuousOn (fun t => f' t / Real.sqrt (V'' t)) (Icc x y) :=
    (hf'c.div (Real.continuous_sqrt.comp hV''c) (fun t => (hsqrt_pos t).ne')).continuousOn
  have hbc : ContinuousOn (fun t => Real.sqrt (V'' t)) (Icc x y) :=
    (Real.continuous_sqrt.comp hV''c).continuousOn
  have h := sq_intervalIntegral_mul_le hxy hac hbc
  have e1 : (fun t => f' t / Real.sqrt (V'' t) * Real.sqrt (V'' t)) = f' := by
    funext t
    field_simp [(hsqrt_pos t).ne']
  have e2 : (fun t => (f' t / Real.sqrt (V'' t)) ^ 2) = fun t => f' t ^ 2 / V'' t := by
    funext t
    rw [div_pow, Real.sq_sqrt (hV''pos t).le]
  have e3 : (fun t => Real.sqrt (V'' t) ^ 2) = V'' := by
    funext t
    exact Real.sq_sqrt (hV''pos t).le
  rw [e1, e2, e3] at h
  rw [hfxy, hVxy]
  exact h

/-! ### The two half-line integrals of `V' ρ` -/

section Density

variable {ρ V' : ℝ → ℝ}

theorem integral_Ioi_deriv_mul_density (hρd : ∀ x, HasDerivAt ρ (-(V' x * ρ x)) x)
    (hV'ρ : Integrable (fun x => V' x * ρ x))
    (hρ_top : Tendsto ρ atTop (𝓝 0)) (t : ℝ) :
    ∫ x in Ioi t, V' x * ρ x = ρ t := by
  have hderiv : ∀ x ∈ Ici t, HasDerivAt (fun x => -ρ x) (V' x * ρ x) x := by
    intro x _
    have h := (hρd x).neg
    refine h.congr_deriv ?_
    ring
  have hlim : Tendsto (fun x => -ρ x) atTop (𝓝 (-0)) := hρ_top.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hV'ρ.integrableOn hlim
  rw [h]
  ring

theorem integral_Iic_deriv_mul_density (hρd : ∀ x, HasDerivAt ρ (-(V' x * ρ x)) x)
    (hV'ρ : Integrable (fun x => V' x * ρ x))
    (hρ_bot : Tendsto ρ atBot (𝓝 0)) (t : ℝ) :
    ∫ x in Iic t, V' x * ρ x = -ρ t := by
  have hderiv : ∀ x ∈ Iic t, HasDerivAt (fun x => -ρ x) (V' x * ρ x) x := by
    intro x _
    have h := (hρd x).neg
    refine h.congr_deriv ?_
    ring
  have hlim : Tendsto (fun x => -ρ x) atBot (𝓝 (-0)) := hρ_bot.neg
  have h := integral_Iic_of_hasDerivAt_of_tendsto' hderiv hV'ρ.integrableOn hlim
  rw [h]
  ring

/-- The kernel `∬_{x<t<y} (V'(y) − V'(x)) ρ(x) ρ(y) = ρ(t)`. -/
theorem double_integral_kernel (hρd : ∀ x, HasDerivAt ρ (-(V' x * ρ x)) x)
    (hρ : Integrable ρ) (hρ1 : ∫ x, ρ x = 1)
    (hV'ρ : Integrable (fun x => V' x * ρ x))
    (hρ_top : Tendsto ρ atTop (𝓝 0)) (hρ_bot : Tendsto ρ atBot (𝓝 0)) (t : ℝ) :
    ∫ x in Iic t, ∫ y in Ioi t, (V' y - V' x) * (ρ x * ρ y) = ρ t := by
  set A := ∫ x in Iic t, ρ x with hA
  set B := ∫ x in Ioi t, ρ x with hB
  have hAB : A + B = 1 := by
    have h := integral_add_compl (s := Iic t) (μ := volume) measurableSet_Iic hρ
    rw [compl_Iic] at h
    rw [hA, hB, h, hρ1]
  have hIoi := integral_Ioi_deriv_mul_density hρd hV'ρ hρ_top t
  have hIic := integral_Iic_deriv_mul_density hρd hV'ρ hρ_bot t
  have hinner : ∀ x, ∫ y in Ioi t, (V' y - V' x) * (ρ x * ρ y) = ρ x * (ρ t - V' x * B) := by
    intro x
    have e : (fun y => (V' y - V' x) * (ρ x * ρ y)) =
        fun y => ρ x * (V' y * ρ y) - (ρ x * V' x) * ρ y := by
      funext y; ring
    rw [e, integral_sub ((hV'ρ.integrableOn).const_mul _) ((hρ.integrableOn).const_mul _),
      integral_const_mul, integral_const_mul, hIoi]
    ring
  simp_rw [hinner]
  have e2 : (fun x => ρ x * (ρ t - V' x * B)) = fun x => ρ t * ρ x - B * (V' x * ρ x) := by
    funext x; ring
  rw [e2, integral_sub ((hρ.integrableOn).const_mul _) ((hV'ρ.integrableOn).const_mul _),
    integral_const_mul, integral_const_mul, hIic]
  have : ρ t * A - B * -ρ t = ρ t * (A + B) := by ring
  rw [this, hAB, mul_one]

end Density

/-! ### The main inequality -/

section Main

variable {ρ V' V'' f f' : ℝ → ℝ}

/-- **One-dimensional Brascamp–Lieb.** -/
theorem variance_le_integral_deriv_sq_div_curvature
    (hρpos : ∀ x, 0 < ρ x) (hρd : ∀ x, HasDerivAt ρ (-(V' x * ρ x)) x)
    (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : Continuous V'') (hV''pos : ∀ x, 0 < V'' x)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hρ_top : Tendsto ρ atTop (𝓝 0)) (hρ_bot : Tendsto ρ atBot (𝓝 0))
    (hρ : Integrable ρ) (hρ1 : ∫ x, ρ x = 1)
    (hV'ρ : Integrable (fun x => V' x * ρ x))
    (hfρ : Integrable (fun x => f x * ρ x))
    (hf2ρ : Integrable (fun x => f x ^ 2 * ρ x))
    (hhρ : Integrable (fun x => f' x ^ 2 / V'' x * ρ x)) :
    ∫ x, (f x - ∫ y, f y * ρ y) ^ 2 * ρ x ≤ ∫ x, f' x ^ 2 / V'' x * ρ x := by
  -- continuity of the data
  have hρc : Continuous ρ := continuous_iff_continuousAt.mpr fun x => (hρd x).continuousAt
  have hV'c : Continuous V' := continuous_iff_continuousAt.mpr fun x => (hV' x).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hV'mono : Monotone V' := by
    refine (strictMono_of_deriv_pos fun x => ?_).monotone
    rw [(hV' x).deriv]; exact hV''pos x
  set h : ℝ → ℝ := fun t => f' t ^ 2 / V'' t with hhdef
  have hhc : Continuous h := (hf'c.pow 2).div hV''c fun t => (hV''pos t).ne'
  have hhnn : ∀ t, 0 ≤ h t := fun t => div_nonneg (sq_nonneg _) (hV''pos t).le
  set m : ℝ := ∫ y, f y * ρ y with hm
  -- Step A: 2·Var = ∬ (f x − f y)² ρ x ρ y
  set D : ℝ × ℝ → ℝ := fun p => (f p.1 - f p.2) ^ 2 * (ρ p.1 * ρ p.2) with hD
  have hDint : Integrable D (volume.prod volume) := by
    have e : D = fun p => ((fun x => f x ^ 2 * ρ x) p.1 * ρ p.2 -
        (2 : ℝ) * ((fun x => f x * ρ x) p.1 * (fun y => f y * ρ y) p.2)) +
        ρ p.1 * (fun y => f y ^ 2 * ρ y) p.2 := by
      funext p; simp only [hD]; ring
    rw [e]
    exact ((hf2ρ.mul_prod hρ).sub ((hfρ.mul_prod hfρ).const_mul 2)).add (hρ.mul_prod hf2ρ)
  have hDnn : ∀ p, 0 ≤ D p := fun p =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hρpos _).le (hρpos _).le)
  have hVar : 2 * ∫ x, (f x - m) ^ 2 * ρ x = ∫ p, D p ∂(volume.prod volume) := by
    have hI1 : Integrable (fun p : ℝ × ℝ => (f p.1 ^ 2 * ρ p.1) * ρ p.2)
        (volume.prod volume) := hf2ρ.mul_prod hρ
    have hI2 : Integrable (fun p : ℝ × ℝ => (f p.1 * ρ p.1) * (f p.2 * ρ p.2))
        (volume.prod volume) := hfρ.mul_prod hfρ
    have hI3 : Integrable (fun p : ℝ × ℝ => ρ p.1 * (f p.2 ^ 2 * ρ p.2))
        (volume.prod volume) := hρ.mul_prod hf2ρ
    have h1 : ∫ p : ℝ × ℝ, (f p.1 ^ 2 * ρ p.1) * ρ p.2 ∂(volume.prod volume) =
        (∫ x, f x ^ 2 * ρ x) * ∫ y, ρ y := integral_prod_mul (fun x => f x ^ 2 * ρ x) ρ
    have h2 : ∫ p : ℝ × ℝ, (f p.1 * ρ p.1) * (f p.2 * ρ p.2) ∂(volume.prod volume) =
        (∫ x, f x * ρ x) * ∫ y, f y * ρ y :=
      integral_prod_mul (fun x => f x * ρ x) (fun y => f y * ρ y)
    have h3 : ∫ p : ℝ × ℝ, ρ p.1 * (f p.2 ^ 2 * ρ p.2) ∂(volume.prod volume) =
        (∫ x, ρ x) * ∫ y, f y ^ 2 * ρ y := integral_prod_mul ρ (fun y => f y ^ 2 * ρ y)
    have e : ∫ p, D p ∂(volume.prod volume) =
        ∫ p : ℝ × ℝ, ((f p.1 ^ 2 * ρ p.1) * ρ p.2 - 2 * ((f p.1 * ρ p.1) * (f p.2 * ρ p.2))) +
          ρ p.1 * (f p.2 ^ 2 * ρ p.2) ∂(volume.prod volume) := by
      congr 1
      funext p
      simp only [hD]
      ring
    have hI12 : Integrable (fun p : ℝ × ℝ =>
        (f p.1 ^ 2 * ρ p.1) * ρ p.2 - 2 * ((f p.1 * ρ p.1) * (f p.2 * ρ p.2)))
        (volume.prod volume) := hI1.sub (hI2.const_mul 2)
    rw [e, integral_add hI12 hI3, integral_sub hI1 (hI2.const_mul 2),
      integral_const_mul, h1, h2, h3, hρ1]
    have e2 : ∫ x, (f x - m) ^ 2 * ρ x =
        ∫ x, ((f x ^ 2 * ρ x) - (2 * m) * (f x * ρ x)) + m ^ 2 * ρ x := by
      congr 1
      funext x
      ring
    have hJ : Integrable (fun x => (f x ^ 2 * ρ x) - (2 * m) * (f x * ρ x)) :=
      hf2ρ.sub (hfρ.const_mul _)
    rw [e2, integral_add hJ (hρ.const_mul _),
      integral_sub hf2ρ (hfρ.const_mul _), integral_const_mul, integral_const_mul, hρ1, ← hm]
    ring
  -- Step B: the pointwise bound by the kernel
  set K : ℝ × ℝ → ℝ := fun p => (∫ t in p.1..p.2, h t) * ((V' p.2 - V' p.1) * (ρ p.1 * ρ p.2))
    with hK
  set S : Set (ℝ × ℝ) := {p | p.1 < p.2} with hS
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_fst measurable_snd
  have hpoint : ∀ p, D p ≤ S.indicator K p + S.indicator K p.swap := by
    intro p
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · have h1 : S.indicator K p = K p := indicator_of_mem (show p ∈ S from hlt) K
      have h2 : S.indicator K p.swap = 0 :=
        indicator_of_notMem (show p.swap ∉ S by simp [hS, Prod.swap, not_lt.mpr hlt.le]) K
      rw [h1, h2, add_zero]
      have hb := sq_sub_le_integral_mul hf hf'c hV' hV''c hV''pos hlt.le
      simp only [hD, hK]
      have : (f p.1 - f p.2) ^ 2 = (f p.2 - f p.1) ^ 2 := by ring
      rw [this]
      have hnn : 0 ≤ ρ p.1 * ρ p.2 := mul_nonneg (hρpos _).le (hρpos _).le
      calc (f p.2 - f p.1) ^ 2 * (ρ p.1 * ρ p.2)
          ≤ ((∫ t in p.1..p.2, h t) * (V' p.2 - V' p.1)) * (ρ p.1 * ρ p.2) :=
            mul_le_mul_of_nonneg_right hb hnn
        _ = _ := by ring
    · have h0 : D p = 0 := by simp [hD, heq]
      rw [h0]
      have hnn1 : 0 ≤ S.indicator K p := by
        apply indicator_nonneg
        intro q hq
        simp only [hK]
        refine mul_nonneg ?_ (mul_nonneg (sub_nonneg.mpr (hV'mono hq.le))
          (mul_nonneg (hρpos _).le (hρpos _).le))
        exact intervalIntegral.integral_nonneg hq.le fun t _ => hhnn t
      have hnn2 : 0 ≤ S.indicator K p.swap := by
        apply indicator_nonneg
        intro q hq
        simp only [hK]
        refine mul_nonneg ?_ (mul_nonneg (sub_nonneg.mpr (hV'mono hq.le))
          (mul_nonneg (hρpos _).le (hρpos _).le))
        exact intervalIntegral.integral_nonneg hq.le fun t _ => hhnn t
      linarith
    · have h1 : S.indicator K p = 0 :=
        indicator_of_notMem (show p ∉ S by simp [hS, not_lt.mpr hgt.le]) K
      have h2 : S.indicator K p.swap = K p.swap :=
        indicator_of_mem (show p.swap ∈ S from hgt) K
      rw [h1, h2, zero_add]
      have hb := sq_sub_le_integral_mul hf hf'c hV' hV''c hV''pos hgt.le
      simp only [hD, hK, Prod.swap]
      have hnn : 0 ≤ ρ p.1 * ρ p.2 := mul_nonneg (hρpos _).le (hρpos _).le
      calc (f p.1 - f p.2) ^ 2 * (ρ p.1 * ρ p.2)
          ≤ ((∫ t in p.2..p.1, h t) * (V' p.1 - V' p.2)) * (ρ p.1 * ρ p.2) :=
            mul_le_mul_of_nonneg_right hb hnn
        _ = _ := by ring
  have hKnn : ∀ p, 0 ≤ S.indicator K p := by
    intro p
    apply indicator_nonneg
    intro q hq
    simp only [hK]
    refine mul_nonneg ?_ (mul_nonneg (sub_nonneg.mpr (hV'mono hq.le))
      (mul_nonneg (hρpos _).le (hρpos _).le))
    exact intervalIntegral.integral_nonneg hq.le fun t _ => hhnn t
  -- Step C: ∬ 1_S K = ∫ h ρ, via Tonelli in `lintegral`
  have hhρnn : ∀ t, 0 ≤ h t * ρ t := fun t => mul_nonneg (hhnn t) (hρpos t).le
  -- the real kernel identity, in indicator form for the product measure
  have hkernel : ∀ t, ∫ p, (Iio t ×ˢ Ioi t).indicator
      (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) p ∂(volume.prod volume) = ρ t := by
    intro t
    rw [integral_indicator (measurableSet_Iio.prod measurableSet_Ioi), ← Measure.prod_restrict]
    have hint : Integrable (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2))
        ((volume.restrict (Iio t)).prod (volume.restrict (Ioi t))) := by
      have e : (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) =
          fun p => ρ p.1 * (fun y => V' y * ρ y) p.2 - (fun x => V' x * ρ x) p.1 * ρ p.2 := by
        funext p; ring
      rw [e]
      exact (hρ.integrableOn.mul_prod hV'ρ.integrableOn).sub
        (hV'ρ.integrableOn.mul_prod hρ.integrableOn)
    rw [integral_prod _ hint]
    rw [setIntegral_congr_set (Iio_ae_eq_Iic (a := t))]
    exact double_integral_kernel hρd hρ hρ1 hV'ρ hρ_top hρ_bot t
  -- integrability of the indicator kernel for each `t`
  have hkernelInt : ∀ t, Integrable ((Iio t ×ˢ Ioi t).indicator
      (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2))) (volume.prod volume) := by
    intro t
    refine Integrable.indicator ?_ (measurableSet_Iio.prod measurableSet_Ioi)
    have e : (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) =
        fun p => ρ p.1 * (fun y => V' y * ρ y) p.2 - (fun x => V' x * ρ x) p.1 * ρ p.2 := by
      funext p; ring
    rw [e]
    exact (hρ.mul_prod hV'ρ).sub (hV'ρ.mul_prod hρ)
  have hkernelnn : ∀ t (p : ℝ × ℝ), 0 ≤ (Iio t ×ˢ Ioi t).indicator
      (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) p := by
    intro t p
    apply indicator_nonneg
    intro q hq
    exact mul_nonneg (sub_nonneg.mpr (hV'mono ((hq.1).le.trans (hq.2).le)))
      (mul_nonneg (hρpos _).le (hρpos _).le)
  -- the triple function
  set T : Set ((ℝ × ℝ) × ℝ) := {q | q.1.1 < q.2 ∧ q.2 < q.1.2} with hT
  have hTmeas : MeasurableSet T := by
    have h1 : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 < q.2} :=
      measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd
    have h2 : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.2 < q.1.2} :=
      measurableSet_lt measurable_snd (measurable_snd.comp measurable_fst)
    exact h1.inter h2
  set φ : (ℝ × ℝ) × ℝ → ℝ := fun q => (V' q.1.2 - V' q.1.1) * (ρ q.1.1 * ρ q.1.2) * h q.2 with hφ
  have hφc : Continuous φ := by
    apply Continuous.mul
    · apply Continuous.mul
      · exact (hV'c.comp (continuous_snd.comp continuous_fst)).sub
          (hV'c.comp (continuous_fst.comp continuous_fst))
      · exact (hρc.comp (continuous_fst.comp continuous_fst)).mul
          (hρc.comp (continuous_snd.comp continuous_fst))
    · exact hhc.comp continuous_snd
  set G : ℝ × ℝ → ℝ → ℝ := fun p t => T.indicator φ (p, t) with hG
  have hGmeas : Measurable (Function.uncurry G) := by
    have : Function.uncurry G = T.indicator φ := by
      funext q; rfl
    rw [this]
    exact hφc.measurable.indicator hTmeas
  -- inner evaluation in `t`, for fixed `p`
  have hinner_p : ∀ p : ℝ × ℝ, ∫⁻ t, ENNReal.ofReal (G p t) = ENNReal.ofReal (S.indicator K p) := by
    intro p
    by_cases hp : p.1 < p.2
    · have hmem : p ∈ S := hp
      rw [indicator_of_mem hmem]
      have hc : 0 ≤ (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2) :=
        mul_nonneg (sub_nonneg.mpr (hV'mono hp.le)) (mul_nonneg (hρpos _).le (hρpos _).le)
      have eG : ∀ t, G p t = (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2) * (Ioo p.1 p.2).indicator h t := by
        intro t
        simp only [hG, hφ]
        by_cases ht : t ∈ Ioo p.1 p.2
        · have hq : (p, t) ∈ T := ⟨ht.1, ht.2⟩
          rw [indicator_of_mem hq, indicator_of_mem ht]
        · have hq : (p, t) ∉ T := fun hq => ht ⟨hq.1, hq.2⟩
          rw [indicator_of_notMem hq, indicator_of_notMem ht, mul_zero]
      simp_rw [eG]
      have hhind : Integrable ((Ioo p.1 p.2).indicator h) :=
        (hhc.integrableOn_Ioc.mono_set Ioo_subset_Ioc_self).integrable_indicator
          measurableSet_Ioo
      have hhindnn : 0 ≤ᵐ[volume] (Ioo p.1 p.2).indicator h :=
        Filter.Eventually.of_forall fun t => indicator_nonneg (fun s _ => hhnn s) t
      calc ∫⁻ t, ENNReal.ofReal ((V' p.2 - V' p.1) * (ρ p.1 * ρ p.2) *
              (Ioo p.1 p.2).indicator h t)
          = ∫⁻ t, ENNReal.ofReal ((V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) *
              ENNReal.ofReal ((Ioo p.1 p.2).indicator h t) := by
            congr 1; funext t; exact ENNReal.ofReal_mul hc
        _ = ENNReal.ofReal ((V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) *
              ∫⁻ t, ENNReal.ofReal ((Ioo p.1 p.2).indicator h t) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal ((V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) *
              ENNReal.ofReal (∫ t, (Ioo p.1 p.2).indicator h t) := by
            rw [ofReal_integral_eq_lintegral_ofReal hhind hhindnn]
        _ = ENNReal.ofReal (K p) := by
            rw [← ENNReal.ofReal_mul hc, integral_indicator measurableSet_Ioo,
              ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hp.le]
            simp only [hK]
            congr 1
            ring
    · have hnot : p ∉ S := hp
      rw [indicator_of_notMem hnot, ENNReal.ofReal_zero]
      have eG : ∀ t, G p t = 0 := by
        intro t
        simp only [hG]
        have hq : (p, t) ∉ T := fun hq => hp (hq.1.trans hq.2)
        rw [indicator_of_notMem hq]
      simp_rw [eG, ENNReal.ofReal_zero, lintegral_zero]
  -- inner evaluation in `p`, for fixed `t`
  have hinner_t : ∀ t : ℝ, ∫⁻ p, ENNReal.ofReal (G p t) ∂(volume.prod volume) =
      ENNReal.ofReal (h t * ρ t) := by
    intro t
    have eG : ∀ p : ℝ × ℝ, G p t = h t * (Iio t ×ˢ Ioi t).indicator
        (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) p := by
      intro p
      simp only [hG, hφ]
      by_cases hp : p ∈ Iio t ×ˢ Ioi t
      · have hq : (p, t) ∈ T := ⟨hp.1, hp.2⟩
        rw [indicator_of_mem hq, indicator_of_mem hp]
        ring
      · have hq : (p, t) ∉ T := fun hq => hp ⟨hq.1, hq.2⟩
        rw [indicator_of_notMem hq, indicator_of_notMem hp, mul_zero]
    simp_rw [eG]
    calc ∫⁻ p, ENNReal.ofReal (h t * (Iio t ×ˢ Ioi t).indicator
            (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) p) ∂(volume.prod volume)
        = ∫⁻ p, ENNReal.ofReal (h t) * ENNReal.ofReal ((Iio t ×ˢ Ioi t).indicator
            (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) p) ∂(volume.prod volume) := by
          congr 1; funext p; exact ENNReal.ofReal_mul (hhnn t)
      _ = ENNReal.ofReal (h t) * ∫⁻ p, ENNReal.ofReal ((Iio t ×ˢ Ioi t).indicator
            (fun p : ℝ × ℝ => (V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) p) ∂(volume.prod volume) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (h t) * ENNReal.ofReal (ρ t) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hkernelInt t)
            (Filter.Eventually.of_forall (hkernelnn t)), hkernel t]
      _ = ENNReal.ofReal (h t * ρ t) := (ENNReal.ofReal_mul (hhnn t)).symm
  -- assemble Step C
  have hL : ∫⁻ p, ENNReal.ofReal (S.indicator K p) ∂(volume.prod volume) =
      ENNReal.ofReal (∫ t, h t * ρ t) := by
    calc ∫⁻ p, ENNReal.ofReal (S.indicator K p) ∂(volume.prod volume)
        = ∫⁻ p, (∫⁻ t, ENNReal.ofReal (G p t)) ∂(volume.prod volume) := by
          congr 1; funext p; exact (hinner_p p).symm
      _ = ∫⁻ t, ∫⁻ p, ENNReal.ofReal (G p t) ∂(volume.prod volume) :=
          lintegral_lintegral_swap (hGmeas.ennreal_ofReal.aemeasurable)
      _ = ∫⁻ t, ENNReal.ofReal (h t * ρ t) := by
          congr 1; funext t; exact hinner_t t
      _ = ENNReal.ofReal (∫ t, h t * ρ t) :=
          (ofReal_integral_eq_lintegral_ofReal hhρ (Filter.Eventually.of_forall hhρnn)).symm
  -- Step D: assemble
  have hKmeas : Measurable (S.indicator K) := by
    have hKc : Continuous K := by
      have hprim : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..x, h t :=
        intervalIntegral.continuous_primitive (fun a b => hhc.intervalIntegrable a b) 0
      have e : K = fun p => ((∫ t in (0 : ℝ)..p.2, h t) - ∫ t in (0 : ℝ)..p.1, h t) *
          ((V' p.2 - V' p.1) * (ρ p.1 * ρ p.2)) := by
        funext p
        simp only [hK]
        congr 1
        rw [intervalIntegral.integral_interval_sub_left (hhc.intervalIntegrable _ _)
          (hhc.intervalIntegrable _ _)]
      rw [e]
      exact ((hprim.comp continuous_snd).sub (hprim.comp continuous_fst)).mul
        (((hV'c.comp continuous_snd).sub (hV'c.comp continuous_fst)).mul
          ((hρc.comp continuous_fst).mul (hρc.comp continuous_snd)))
    exact hKc.measurable.indicator hSmeas
  have hswap : ∫⁻ p, ENNReal.ofReal (S.indicator K p.swap) ∂(volume.prod volume) =
      ∫⁻ p, ENNReal.ofReal (S.indicator K p) ∂(volume.prod volume) :=
    lintegral_prod_swap (fun p => ENNReal.ofReal (S.indicator K p))
  have hmain : ENNReal.ofReal (2 * ∫ x, (f x - m) ^ 2 * ρ x) ≤
      ENNReal.ofReal (2 * ∫ t, h t * ρ t) := by
    calc ENNReal.ofReal (2 * ∫ x, (f x - m) ^ 2 * ρ x)
        = ENNReal.ofReal (∫ p, D p ∂(volume.prod volume)) := by rw [hVar]
      _ = ∫⁻ p, ENNReal.ofReal (D p) ∂(volume.prod volume) :=
          ofReal_integral_eq_lintegral_ofReal hDint (Filter.Eventually.of_forall hDnn)
      _ ≤ ∫⁻ p, ENNReal.ofReal (S.indicator K p + S.indicator K p.swap) ∂(volume.prod volume) :=
          lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hpoint p)
      _ = ∫⁻ p, (ENNReal.ofReal (S.indicator K p) + ENNReal.ofReal (S.indicator K p.swap))
            ∂(volume.prod volume) := by
          congr 1; funext p; exact ENNReal.ofReal_add (hKnn p) (hKnn p.swap)
      _ = (∫⁻ p, ENNReal.ofReal (S.indicator K p) ∂(volume.prod volume)) +
            ∫⁻ p, ENNReal.ofReal (S.indicator K p.swap) ∂(volume.prod volume) :=
          lintegral_add_left hKmeas.ennreal_ofReal _
      _ = ENNReal.ofReal (∫ t, h t * ρ t) + ENNReal.ofReal (∫ t, h t * ρ t) := by
          rw [hswap, hL]
      _ = ENNReal.ofReal (2 * ∫ t, h t * ρ t) := by
          rw [two_mul, ENNReal.ofReal_add (integral_nonneg hhρnn) (integral_nonneg hhρnn)]
  have hfin := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num) (integral_nonneg hhρnn))).mp hmain
  have : ∫ t, h t * ρ t = ∫ x, f' x ^ 2 / V'' x * ρ x := rfl
  rw [this] at hfin
  linarith

end Main

/-! ### Integration by parts and the Cramér–Rao lower bound -/

section CramerRao

variable {ρ V' V'' f f' g g' : ℝ → ℝ}

/-- Cauchy–Schwarz for weighted integrals: `(∫ a b ρ)² ≤ (∫ a² ρ)(∫ b² ρ)` for `ρ ≥ 0`. -/
theorem sq_integral_mul_mul_le (hρnn : ∀ x, 0 ≤ ρ x) {a b : ℝ → ℝ}
    (ha : Integrable (fun x => a x ^ 2 * ρ x)) (hb : Integrable (fun x => b x ^ 2 * ρ x))
    (hab : Integrable (fun x => a x * b x * ρ x)) :
    (∫ x, a x * b x * ρ x) ^ 2 ≤ (∫ x, a x ^ 2 * ρ x) * ∫ x, b x ^ 2 * ρ x := by
  set A := ∫ x, a x ^ 2 * ρ x with hA
  set B := ∫ x, b x ^ 2 * ρ x with hB
  set C := ∫ x, a x * b x * ρ x with hC
  have key : ∀ l : ℝ, 0 ≤ A - 2 * l * C + l ^ 2 * B := by
    intro l
    have h0 : 0 ≤ ∫ x, (a x - l * b x) ^ 2 * ρ x :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hρnn x)
    have hJ : Integrable (fun x => a x ^ 2 * ρ x - (2 * l) * (a x * b x * ρ x)) :=
      ha.sub (hab.const_mul _)
    have hexp : ∫ x, (a x - l * b x) ^ 2 * ρ x = A - 2 * l * C + l ^ 2 * B := by
      have e : ∫ x, (a x - l * b x) ^ 2 * ρ x =
          ∫ x, (a x ^ 2 * ρ x - (2 * l) * (a x * b x * ρ x)) + l ^ 2 * (b x ^ 2 * ρ x) := by
        congr 1; funext x; ring
      rw [e, integral_add hJ (hb.const_mul _), integral_sub ha (hab.const_mul _),
        integral_const_mul, integral_const_mul]
    linarith [h0, hexp]
  have hB0 : 0 ≤ B := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hρnn x)
  rcases hB0.lt_or_eq with hBpos | hBzero
  · have h := key (C / B)
    have h2 : A - 2 * (C / B) * C + (C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp
      ring
    rw [h2, sub_nonneg, div_le_iff₀ hBpos] at h
    linarith
  · have hC : C = 0 := by
      by_contra hC
      have h := key ((A + 1) / (2 * C))
      rw [← hBzero, mul_zero, add_zero] at h
      have h3 : 2 * ((A + 1) / (2 * C)) * C = A + 1 := by
        field_simp
      linarith
    rw [hC, ← hBzero]
    simp

/-- Integration by parts against the density: `∫ g' ρ = ∫ g V' ρ` when `g ρ → 0` at `±∞`. -/
theorem integral_deriv_mul_density_eq (hρd : ∀ x, HasDerivAt ρ (-(V' x * ρ x)) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hgρ_top : Tendsto (fun x => g x * ρ x) atTop (𝓝 0))
    (hgρ_bot : Tendsto (fun x => g x * ρ x) atBot (𝓝 0))
    (hg'ρ : Integrable (fun x => g' x * ρ x))
    (hgV'ρ : Integrable (fun x => g x * V' x * ρ x)) :
    ∫ x, g' x * ρ x = ∫ x, g x * V' x * ρ x := by
  have hderiv : ∀ x, HasDerivAt (fun x => g x * ρ x) (g' x * ρ x - g x * V' x * ρ x) x := by
    intro x
    have h := (hg x).mul (hρd x)
    refine h.congr_deriv ?_
    ring
  have hint : Integrable (fun x => g' x * ρ x - g x * V' x * ρ x) := hg'ρ.sub hgV'ρ
  have h := integral_of_hasDerivAt_of_tendsto hderiv hint hgρ_bot hgρ_top
  rw [integral_sub hg'ρ hgV'ρ] at h
  linarith

/-- The score has mean zero: `∫ V' ρ = 0`. -/
theorem integral_score_mul_density_eq_zero (hρd : ∀ x, HasDerivAt ρ (-(V' x * ρ x)) x)
    (hρ_top : Tendsto ρ atTop (𝓝 0)) (hρ_bot : Tendsto ρ atBot (𝓝 0))
    (hV'ρ : Integrable (fun x => V' x * ρ x)) :
    ∫ x, V' x * ρ x = 0 := by
  have h := integral_deriv_mul_density_eq (g := fun _ => (1 : ℝ)) (g' := fun _ => (0 : ℝ)) hρd
    (fun x => hasDerivAt_const x 1) (by simpa using hρ_top) (by simpa using hρ_bot)
    (by simp) (by simpa using hV'ρ)
  simpa using h.symm

/-- **Cramér–Rao lower bound.** `(∫ f' ρ)² ≤ Var_ρ(f) · ∫ V'' ρ`. -/
theorem sq_integral_deriv_le_variance_mul_curvature
    (hρpos : ∀ x, 0 < ρ x) (hρd : ∀ x, HasDerivAt ρ (-(V' x * ρ x)) x)
    (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hρ_top : Tendsto ρ atTop (𝓝 0)) (hρ_bot : Tendsto ρ atBot (𝓝 0))
    (hfρ_top : Tendsto (fun x => f x * ρ x) atTop (𝓝 0))
    (hfρ_bot : Tendsto (fun x => f x * ρ x) atBot (𝓝 0))
    (hV'ρ_top : Tendsto (fun x => V' x * ρ x) atTop (𝓝 0))
    (hV'ρ_bot : Tendsto (fun x => V' x * ρ x) atBot (𝓝 0))
    (hρ : Integrable ρ)
    (hV'ρ : Integrable (fun x => V' x * ρ x))
    (hV'2ρ : Integrable (fun x => V' x ^ 2 * ρ x))
    (hV''ρ : Integrable (fun x => V'' x * ρ x))
    (hfρ : Integrable (fun x => f x * ρ x))
    (hf2ρ : Integrable (fun x => f x ^ 2 * ρ x))
    (hf'ρ : Integrable (fun x => f' x * ρ x))
    (hfV'ρ : Integrable (fun x => f x * V' x * ρ x)) :
    (∫ x, f' x * ρ x) ^ 2 ≤
      (∫ x, (f x - ∫ y, f y * ρ y) ^ 2 * ρ x) * ∫ x, V'' x * ρ x := by
  set m : ℝ := ∫ y, f y * ρ y with hm
  have hmean := integral_score_mul_density_eq_zero hρd hρ_top hρ_bot hV'ρ
  have hIBPf := integral_deriv_mul_density_eq hρd hf hfρ_top hfρ_bot hf'ρ hfV'ρ
  have hIBPV := integral_deriv_mul_density_eq hρd hV' hV'ρ_top hV'ρ_bot hV''ρ
    (by simp [sq] at hV'2ρ ⊢; exact hV'2ρ)
  -- Cov(f − m, V') = ∫ f' ρ
  have hcov : ∫ x, (f x - m) * V' x * ρ x = ∫ x, f' x * ρ x := by
    have e : ∫ x, (f x - m) * V' x * ρ x = ∫ x, f x * V' x * ρ x - m * (V' x * ρ x) := by
      congr 1; funext x; ring
    rw [e, integral_sub hfV'ρ (hV'ρ.const_mul _), integral_const_mul, hmean, mul_zero, sub_zero,
      hIBPf]
  -- Var(V') = ∫ V'' ρ
  have hvarV : ∫ x, V' x ^ 2 * ρ x = ∫ x, V'' x * ρ x := by
    rw [hIBPV]
    congr 1; funext x; ring
  -- Cauchy–Schwarz
  have hfm2 : Integrable (fun x => (f x - m) ^ 2 * ρ x) := by
    have e : (fun x => (f x - m) ^ 2 * ρ x) =
        fun x => (f x ^ 2 * ρ x - (2 * m) * (f x * ρ x)) + m ^ 2 * ρ x := by
      funext x; ring
    rw [e]
    exact (hf2ρ.sub (hfρ.const_mul _)).add (hρ.const_mul _)
  have hfmV : Integrable (fun x => (f x - m) * V' x * ρ x) := by
    have e : (fun x => (f x - m) * V' x * ρ x) = fun x => f x * V' x * ρ x - m * (V' x * ρ x) := by
      funext x; ring
    rw [e]
    exact hfV'ρ.sub (hV'ρ.const_mul _)
  have hcs := sq_integral_mul_mul_le (fun x => (hρpos x).le) hfm2 hV'2ρ hfmV
  rw [hcov, hvarV] at hcs
  exact hcs

end CramerRao

/-! ### The Gibbs form `ρ = exp(−V)` -/

section Gibbs

variable {V V' V'' f f' : ℝ → ℝ}

theorem hasDerivAt_exp_neg (hV : ∀ x, HasDerivAt V (V' x) x) (x : ℝ) :
    HasDerivAt (fun x => Real.exp (-V x)) (-(V' x * Real.exp (-V x))) x := by
  have h := (hV x).neg.exp
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

/-- Brascamp–Lieb for `ρ = exp(−V)`. -/
theorem variance_le_of_exp
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : Continuous V'') (hV''pos : ∀ x, 0 < V'' x)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hρ_top : Tendsto (fun x => Real.exp (-V x)) atTop (𝓝 0))
    (hρ_bot : Tendsto (fun x => Real.exp (-V x)) atBot (𝓝 0))
    (hρ : Integrable (fun x => Real.exp (-V x)))
    (hρ1 : ∫ x, Real.exp (-V x) = 1)
    (hV'ρ : Integrable (fun x => V' x * Real.exp (-V x)))
    (hfρ : Integrable (fun x => f x * Real.exp (-V x)))
    (hf2ρ : Integrable (fun x => f x ^ 2 * Real.exp (-V x)))
    (hhρ : Integrable (fun x => f' x ^ 2 / V'' x * Real.exp (-V x))) :
    ∫ x, (f x - ∫ y, f y * Real.exp (-V y)) ^ 2 * Real.exp (-V x) ≤
      ∫ x, f' x ^ 2 / V'' x * Real.exp (-V x) :=
  variance_le_integral_deriv_sq_div_curvature (fun _ => Real.exp_pos _) (hasDerivAt_exp_neg hV)
    hV' hV''c hV''pos hf hf'c hρ_top hρ_bot hρ hρ1 hV'ρ hfρ hf2ρ hhρ

end Gibbs

end OneDimBrascampLieb

end HTGeometry
