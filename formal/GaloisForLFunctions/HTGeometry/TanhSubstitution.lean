import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The hyperbolic tangent substitution

The change of variables `x = tanh t` turns the hyperbolic power integral on the half line into an
algebraic integral on the unit interval:

```text
∫_0^∞ (cosh t)^(-s) dt = ∫_0^1 (1 - x²)^(s/2 - 1) dx .
```

Everything needed for it is built here, since mathlib has no derivative or monotonicity API for
`Real.tanh`: the derivative `tanh' = 1/cosh²`, strict monotonicity, the exact image
`tanh '' (0,∞) = (0,1)`, and the Pythagorean identity `1 - tanh² = 1/cosh²`.
-/

open MeasureTheory Set

namespace HTGeometry

/-! ### The calculus of `tanh` -/

/-- The derivative of the hyperbolic tangent. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  have heq : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2
      = 1 / Real.cosh x ^ 2 := by
    rw [show Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x
        = Real.cosh x ^ 2 - Real.sinh x ^ 2 by ring, Real.cosh_sq_sub_sinh_sq]
  rw [heq] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with y
  exact Real.tanh_eq_sinh_div_cosh y

/-- The Pythagorean identity in the form used by the substitution. -/
theorem one_sub_tanh_sq (x : ℝ) : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp
  have := Real.cosh_sq_sub_sinh_sq x
  linarith

/-- The hyperbolic tangent is strictly monotone. -/
theorem tanh_strictMono : StrictMono Real.tanh := by
  refine strictMono_of_deriv_pos ?_
  intro x
  rw [(hasDerivAt_tanh x).deriv]
  positivity

/-- The hyperbolic tangent maps the positive half line onto the unit interval. -/
theorem tanh_image_Ioi_zero : Real.tanh '' Set.Ioi 0 = Set.Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, Real.tanh_lt_one t⟩
    have := tanh_strictMono ht
    rwa [Real.tanh_zero] at this
  · intro hx
    have hmem : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    refine ⟨Real.artanh x, ?_, Real.tanh_artanh hmem⟩
    have hval : Real.tanh (Real.artanh x) = x := Real.tanh_artanh hmem
    by_contra hcon
    have hle : Real.artanh x ≤ 0 := not_lt.mp hcon
    rcases lt_or_eq_of_le hle with hlt | heq
    · have := tanh_strictMono hlt
      rw [Real.tanh_zero, hval] at this
      linarith [hx.1]
    · rw [heq, Real.tanh_zero] at hval
      linarith [hx.1]

/-! ### The substitution -/

/-- **The hyperbolic tangent substitution.**  The hyperbolic power integral on the half line is the
algebraic integral on the unit interval. -/
theorem integral_cosh_rpow_neg_Ioi (s : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), (Real.cosh t) ^ (-s)
      = ∫ x in Set.Ioo (0 : ℝ) 1, (1 - x ^ 2) ^ (s / 2 - 1) := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt Real.tanh (1 / Real.cosh x ^ 2) (Set.Ioi 0) x :=
    fun x _ => (hasDerivAt_tanh x).hasDerivWithinAt
  have hinj : Set.InjOn Real.tanh (Set.Ioi 0) :=
    Set.injOn_of_injective tanh_strictMono.injective
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj (fun x : ℝ => (1 - x ^ 2) ^ (s / 2 - 1))
  rw [tanh_image_Ioi_zero] at hchange
  rw [hchange]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hcpos : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have hsq : (1 : ℝ) - Real.tanh t ^ 2 = (Real.cosh t) ^ (-2 : ℝ) := by
    rw [one_sub_tanh_sq]
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hcpos.le, Real.rpow_natCast]
    rw [one_div]
  have habs : |1 / Real.cosh t ^ 2| = (Real.cosh t) ^ (-2 : ℝ) := by
    rw [abs_of_pos (by positivity)]
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hcpos.le, Real.rpow_natCast]
    rw [one_div]
  rw [smul_eq_mul, habs, hsq, ← Real.rpow_mul hcpos.le, ← Real.rpow_add hcpos]
  congr 1
  ring

/-! ### The square substitution and the Beta integral -/

/-- The substitution `u = x²` on the unit interval. -/
theorem two_mul_integral_one_sub_sq_rpow (a : ℝ) :
    2 * ∫ x in Set.Ioo (0 : ℝ) 1, (1 - x ^ 2) ^ (a - 1)
      = ∫ u in Set.Ioo (0 : ℝ) 1, u ^ (-(1 : ℝ) / 2) * (1 - u) ^ (a - 1) := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun y : ℝ => y ^ 2) (2 * x) (Set.Ioo 0 1) x := by
    intro x _
    have h := (hasDerivAt_id x).pow 2
    simp only [id_eq, Nat.cast_ofNat] at h
    have h' : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      rw [show (fun y : ℝ => y ^ 2) = id ^ 2 by rfl]
      exact h.congr_deriv (by ring)
    exact h'.hasDerivWithinAt
  have hinj : Set.InjOn (fun y : ℝ => y ^ 2) (Set.Ioo 0 1) := by
    intro x hx y hy h
    simp only at h
    nlinarith [hx.1, hy.1]
  have himg : (fun y : ℝ => y ^ 2) '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨pow_pos hx.1 2, by nlinarith [hx.1, hx.2]⟩
    · intro hu
      refine ⟨Real.sqrt u, ⟨Real.sqrt_pos.mpr hu.1, ?_⟩, Real.sq_sqrt hu.1.le⟩
      have h := Real.sqrt_lt_sqrt hu.1.le hu.2
      rwa [Real.sqrt_one] at h
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj
    (fun u : ℝ => u ^ (-(1 : ℝ) / 2) * (1 - u) ^ (a - 1))
  rw [himg] at hchange
  rw [hchange, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hxpos : (0 : ℝ) < x := hx.1
  have hsq : (x ^ 2 : ℝ) ^ (-(1 : ℝ) / 2) = 1 / x := by
    rw [show (x ^ 2 : ℝ) = x ^ (2 : ℝ) by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    rw [← Real.rpow_mul hxpos.le]
    rw [show (2 : ℝ) * (-(1 : ℝ) / 2) = -1 by ring, Real.rpow_neg_one, one_div]
  rw [smul_eq_mul, abs_of_pos (by linarith), hsq]
  field_simp

/-- **The real Euler Beta integral.** -/
theorem integral_rpow_mul_one_sub_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Set.Ioo (0 : ℝ) 1, u ^ (a - 1) * (1 - u) ^ (b - 1)
      = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hare : (0 : ℝ) < ((a : ℂ)).re := by rw [Complex.ofReal_re]; exact ha
  have hbre : (0 : ℝ) < ((b : ℂ)).re := by rw [Complex.ofReal_re]; exact hb
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hare hbre
  have hcast : Complex.betaIntegral (a : ℂ) (b : ℂ)
      = ((∫ u in Set.Ioo (0 : ℝ) 1, u ^ (a - 1) * (1 - u) ^ (b - 1) : ℝ) : ℂ) := by
    have hcongr : (∫ x in Set.Ioc (0 : ℝ) 1,
          ((x : ℂ)) ^ ((a : ℂ) - 1) * ((1 : ℂ) - (x : ℂ)) ^ ((b : ℂ) - 1))
        = ∫ x in Set.Ioc (0 : ℝ) 1, (((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ)) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have hx1 : x ≤ 1 := hx.2
      have h1 : ((x : ℂ)) ^ ((a : ℂ) - 1) = (((x ^ (a - 1) : ℝ)) : ℂ) := by
        rw [show ((a : ℂ) - 1) = (((a - 1 : ℝ)) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow hx0.le]
      have h2 : ((1 : ℂ) - (x : ℂ)) ^ ((b : ℂ) - 1) = ((((1 - x) ^ (b - 1) : ℝ)) : ℂ) := by
        rw [show ((1 : ℂ) - (x : ℂ)) = (((1 - x : ℝ)) : ℂ) by push_cast; ring,
          show ((b : ℂ) - 1) = (((b - 1 : ℝ)) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow (by linarith)]
      rw [h1, h2, ← Complex.ofReal_mul]
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      hcongr, integral_complex_ofReal, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hcast, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    show (a : ℂ) + (b : ℂ) = ((a + b : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at hbeta
  have hreal : Real.Gamma a * Real.Gamma b
      = Real.Gamma (a + b) * ∫ u in Set.Ioo (0 : ℝ) 1, u ^ (a - 1) * (1 - u) ^ (b - 1) := by
    exact_mod_cast hbeta
  have hne : Real.Gamma (a + b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp
  linarith [hreal]

/-! ### The closed value of the hyperbolic power integral -/

/-- **The hyperbolic power integral on the half line.**  For every positive exponent,

```text
∫_0^∞ (cosh t)^(-s) dt = √π Γ(s/2) / (2 Γ((s+1)/2)) .
```
-/
theorem integral_cosh_rpow_neg_Ioi_eq {s : ℝ} (hs : 0 < s) :
    ∫ t in Set.Ioi (0 : ℝ), (Real.cosh t) ^ (-s)
      = Real.sqrt Real.pi * Real.Gamma (s / 2) / (2 * Real.Gamma ((s + 1) / 2)) := by
  have h1 := integral_cosh_rpow_neg_Ioi s
  have h2 := two_mul_integral_one_sub_sq_rpow (s / 2)
  have h3 := integral_rpow_mul_one_sub_rpow (a := 1 / 2) (b := s / 2) (by norm_num) (by linarith)
  have h3' : (∫ u in Set.Ioo (0 : ℝ) 1, u ^ (-(1 : ℝ) / 2) * (1 - u) ^ (s / 2 - 1))
      = Real.Gamma (1 / 2) * Real.Gamma (s / 2) / Real.Gamma (1 / 2 + s / 2) := by
    rw [← h3]
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    norm_num
  have hhalf : (1 : ℝ) / 2 + s / 2 = (s + 1) / 2 := by ring
  rw [hhalf, Real.Gamma_one_half_eq] at h3'
  have hGpos : 0 < Real.Gamma ((s + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  rw [h1]
  have hkey : 2 * (∫ x in Set.Ioo (0 : ℝ) 1, (1 - x ^ 2) ^ (s / 2 - 1))
      = Real.sqrt Real.pi * Real.Gamma (s / 2) / Real.Gamma ((s + 1) / 2) := by
    rw [h2, h3']
  field_simp at hkey ⊢
  linarith

/-! ### The full-line integral -/

/-- The hyperbolic cosine dominates half the exponential of the absolute value. -/
theorem exp_abs_div_two_le_cosh (t : ℝ) : Real.exp |t| / 2 ≤ Real.cosh t := by
  rw [Real.cosh_eq]
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have := (Real.exp_pos (-t)).le
    linarith
  · rw [abs_of_neg ht]
    have := (Real.exp_pos t).le
    linarith

/-- Exponential envelope of the negative hyperbolic power. -/
theorem cosh_rpow_neg_le {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    (Real.cosh t) ^ (-s) ≤ 2 ^ s * Real.exp (-(s * |t|)) := by
  have hcpos : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have hbase : (0 : ℝ) < Real.exp |t| / 2 := by positivity
  have hle : (Real.exp |t| / 2) ^ s ≤ (Real.cosh t) ^ s :=
    Real.rpow_le_rpow hbase.le (exp_abs_div_two_le_cosh t) hs
  have hbpos : (0 : ℝ) < (Real.exp |t| / 2) ^ s := Real.rpow_pos_of_pos hbase s
  have hval : (Real.exp |t| / 2) ^ s = Real.exp (|t| * s) / 2 ^ s := by
    rw [Real.div_rpow (Real.exp_pos |t|).le (by norm_num : (0 : ℝ) ≤ 2), Real.exp_mul]
  have hinv : ((Real.cosh t) ^ s)⁻¹ ≤ ((Real.exp |t| / 2) ^ s)⁻¹ := inv_anti₀ hbpos hle
  rw [Real.rpow_neg hcpos.le]
  refine le_trans hinv (le_of_eq ?_)
  rw [hval, inv_div, Real.exp_neg, show s * |t| = |t| * s by ring, div_eq_mul_inv]

/-- The negative hyperbolic power is integrable on the whole line. -/
theorem integrable_cosh_rpow_neg {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => (Real.cosh t) ^ (-s)) := by
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-(s * |t|))) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hs).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    show Real.exp (-s * t) = Real.exp (-(s * |t|))
    rw [abs_of_pos ht']
    congr 1
    ring
  have hIci : IntegrableOn (fun t : ℝ => Real.exp (-(s * |t|))) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIoi
  have hIio : IntegrableOn (fun t : ℝ => Real.exp (-(s * |t|))) (Set.Iio 0) := by
    have hmp : MeasurePreserving (fun t : ℝ => -t) volume volume :=
      Measure.measurePreserving_neg volume
    have hme : MeasurableEmbedding (fun t : ℝ => -t) := (Homeomorph.neg ℝ).measurableEmbedding
    have hpre : (fun t : ℝ => -t) ⁻¹' (Set.Ioi (0 : ℝ)) = Set.Iio 0 := by
      ext t
      simp
    have h := (hmp.integrableOn_comp_preimage hme
      (f := fun t : ℝ => Real.exp (-(s * |t|))) (s := Set.Ioi 0)).2 hIoi
    rw [hpre] at h
    refine h.congr_fun ?_ measurableSet_Iio
    intro t _
    show Real.exp (-(s * |(-t)|)) = Real.exp (-(s * |t|))
    rw [abs_neg]
  have hdomAll : Integrable (fun t : ℝ => Real.exp (-(s * |t|))) := by
    rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ))]
    exact hIio.union hIci
  refine Integrable.mono' (hdomAll.const_mul (2 ^ s)) ?_ ?_
  · refine (Real.continuous_cosh.rpow_const ?_).aestronglyMeasurable
    intro x
    exact Or.inl (Real.cosh_pos x).ne'
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos t).le _)]
    exact cosh_rpow_neg_le hs.le t

/-- **The hyperbolic power integral on the line.**  For every positive exponent,

```text
∫_ℝ (cosh t)^(-s) dt = √π Γ(s/2) / Γ((s+1)/2) .
```

At `s = 1/2` this is the Gamma cyclic normalisation `√π Γ(1/4)/Γ(3/4)`. -/
theorem integral_cosh_rpow_neg {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ, (Real.cosh t) ^ (-s)
      = Real.sqrt Real.pi * Real.Gamma (s / 2) / Real.Gamma ((s + 1) / 2) := by
  have hint := integrable_cosh_rpow_neg hs
  have hsplit := MeasureTheory.integral_add_compl (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hint
  rw [compl_Ioi] at hsplit
  have hrefl : (∫ t in Set.Iic (0 : ℝ), (Real.cosh t) ^ (-s))
      = ∫ t in Set.Ioi (0 : ℝ), (Real.cosh t) ^ (-s) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun t : ℝ => (Real.cosh t) ^ (-s))
    rw [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    rw [Real.cosh_neg]
  rw [hrefl] at hsplit
  rw [← hsplit, integral_cosh_rpow_neg_Ioi_eq hs]
  have hGpos : 0 < Real.Gamma ((s + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  field_simp
  ring

end HTGeometry


