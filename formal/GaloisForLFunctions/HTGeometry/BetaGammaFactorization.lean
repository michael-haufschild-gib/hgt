import Mathlib

/-!
# Beta–gamma factorization and power tilts of beta laws

For independent `X ~ Gamma(a, r)` and `Y ~ Gamma(b, r)` the projective-sum coordinates
`U = X/(X+Y)` and `V = X + Y` are independent with `U ~ Beta(a, b)` and `V ~ Gamma(a+b, r)`:

`(Gamma(a, r) ⊗ Gamma(b, r)) ∘ (x, y) ↦ (x/(x+y), x+y)⁻¹ = Beta(a, b) ⊗ Gamma(a+b, r)`.

The proof is the change of variables `x = uv`, `y = (1-u)v` with Jacobian `v`, carried out as a
translation `y ↦ x + y`, Tonelli, and a scaling `x ↦ uv`.  Consequences:

* `integral_pow_gammaMeasure` — `E[X^n] = Γ(a+n)/(Γ(a) rⁿ)`;
* `integral_pow_betaMeasure` — `E[Uⁿ] = E[Xⁿ]/E[Vⁿ] = Γ(a+n)Γ(a+b)/(Γ(a)Γ(a+b+n))`;
* `withDensity_pow_betaMeasure` — the power tilt `uⁿ Beta(a, b)/E[Uⁿ]` is `Beta(a+n, b)`;
* `integral_id_betaMeasure`, `variance_betaMeasure` — mean and variance, and the one-step tilt law
  `E_{tilt}[U] - E[U] = Var(U)/E[U]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### The projective-sum change of variables -/

/-- Projective-sum coordinates `(x, y) ↦ (x/(x+y), x+y)`. -/
def projectiveSum (p : ℝ × ℝ) : ℝ × ℝ := (p.1 / (p.1 + p.2), p.1 + p.2)

theorem measurable_projectiveSum : Measurable projectiveSum := by
  unfold projectiveSum
  fun_prop

theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

theorem measurable_betaPDF (a b : ℝ) : Measurable (betaPDF a b) :=
  (measurable_betaPDFReal a b).ennreal_ofReal

/-- Scaling `x = u v` in a Lebesgue integral: `∫⁻ G = v ∫⁻ G(u v) du` for `v > 0`. -/
theorem lintegral_eq_ofReal_mul_lintegral_comp_mul {v : ℝ} (hv : 0 < v) (G : ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ x, G x = ENNReal.ofReal v * ∫⁻ u, G (u * v) := by
  have hmap := Real.map_volume_mul_right hv.ne'
  have h1 : ∫⁻ u, G (u * v) = ENNReal.ofReal |v⁻¹| * ∫⁻ x, G x := by
    rw [← lintegral_map hG (by fun_prop : Measurable fun x : ℝ => x * v), hmap,
      lintegral_smul_measure, smul_eq_mul]
  rw [h1, ← mul_assoc, abs_of_pos (inv_pos.mpr hv), ← ENNReal.ofReal_mul hv.le,
    mul_inv_cancel₀ hv.ne', ENNReal.ofReal_one, one_mul]

/-- **The density identity** `v g_a(uv) g_b((1-u)v) = β_{a,b}(u) g_{a+b}(v)` for `v > 0`,
`u ∉ {0, 1}`. -/
theorem ofReal_mul_gammaPDF_mul_gammaPDF {a b r u v : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hv : 0 < v) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ENNReal.ofReal v * (gammaPDF a r (u * v) * gammaPDF b r (v - u * v)) =
      betaPDF a b u * gammaPDF (a + b) r v := by
  rcases lt_or_gt_of_ne hu0 with hneg | hpos
  · rw [gammaPDF_of_neg (mul_neg_of_neg_of_pos hneg hv), betaPDF_eq_zero_of_nonpos hneg.le]
    simp
  rcases lt_or_gt_of_ne hu1 with hlt | hgt
  · have hΓa := Real.Gamma_pos_of_pos ha
    have hΓb := Real.Gamma_pos_of_pos hb
    have hΓab := Real.Gamma_pos_of_pos (add_pos ha hb)
    have h1u : 0 < 1 - u := by linarith
    have hvu : v - u * v = (1 - u) * v := by ring
    rw [gammaPDF_of_nonneg (mul_pos hpos hv).le, gammaPDF_of_nonneg (by rw [hvu]; positivity),
      betaPDF_of_pos_lt_one hpos hlt, gammaPDF_of_nonneg hv.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hv.le,
      ← ENNReal.ofReal_mul (by
        have := beta_pos ha hb
        positivity)]
    congr 1
    rw [hvu, Real.mul_rpow hpos.le hv.le, Real.mul_rpow h1u.le hv.le]
    have hexp : Real.exp (-(r * (u * v))) * Real.exp (-(r * ((1 - u) * v))) =
        Real.exp (-(r * v)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hrr : r ^ a * r ^ b = r ^ (a + b) := (Real.rpow_add hr a b).symm
    have hvv : v * (v ^ (a - 1) * v ^ (b - 1)) = v ^ (a + b - 1) := by
      rw [← Real.rpow_add hv, show a + b - 1 = (a - 1 + (b - 1)) + 1 by ring,
        Real.rpow_add_one hv.ne']
      ring
    have hre : v * (r ^ a / Real.Gamma a * (u ^ (a - 1) * v ^ (a - 1)) *
        Real.exp (-(r * (u * v))) * (r ^ b / Real.Gamma b * ((1 - u) ^ (b - 1) * v ^ (b - 1)) *
          Real.exp (-(r * ((1 - u) * v))))) =
        (r ^ a * r ^ b) * (v * (v ^ (a - 1) * v ^ (b - 1))) * u ^ (a - 1) * (1 - u) ^ (b - 1) *
          (Real.exp (-(r * (u * v))) * Real.exp (-(r * ((1 - u) * v)))) /
            (Real.Gamma a * Real.Gamma b) := by
      field_simp
    rw [hre, hrr, hvv, hexp, beta]
    field_simp
  · have hneg : v - u * v < 0 := by nlinarith
    rw [gammaPDF_of_neg hneg, betaPDF_eq_zero_of_one_le hgt.le]
    simp

/-- **Beta–gamma factorization.**  For independent `X ~ Gamma(a, r)`, `Y ~ Gamma(b, r)`, the
projective coordinates `(X/(X+Y), X+Y)` have law `Beta(a, b) ⊗ Gamma(a+b, r)`: the ratio and the
total are independent. -/
theorem map_projectiveSum_gammaMeasure_prod {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Measure.map projectiveSum ((gammaMeasure a r).prod (gammaMeasure b r)) =
      (betaMeasure a b).prod (gammaMeasure (a + b) r) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hga := measurable_gammaPDF a r
  have hgb := measurable_gammaPDF b r
  have hgab := measurable_gammaPDF (a + b) r
  have hβ := measurable_betaPDF a b
  rw [lintegral_map hF measurable_projectiveSum, gammaMeasure, gammaMeasure, betaMeasure,
    gammaMeasure, prod_withDensity hga hgb, prod_withDensity hβ hgab,
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun z : ℝ × ℝ => gammaPDF a r z.1 * gammaPDF b r z.2)
      (by exact (hga.comp measurable_fst).mul (hgb.comp measurable_snd))
      (g := fun p => F (projectiveSum p)) (by exact hF.comp measurable_projectiveSum),
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun z : ℝ × ℝ => betaPDF a b z.1 * gammaPDF (a + b) r z.2)
      (by exact (hβ.comp measurable_fst).mul (hgab.comp measurable_snd)) (g := F) hF,
    lintegral_prod _ (by
      exact ((hga.comp measurable_fst |>.mul (hgb.comp measurable_snd)).mul
        (hF.comp measurable_projectiveSum)).aemeasurable),
    lintegral_prod _ (by
      exact ((hβ.comp measurable_fst |>.mul (hgab.comp measurable_snd)).mul hF).aemeasurable)]
  simp only [Pi.mul_apply, projectiveSum]
  -- translation `y ↦ v - x`
  have htrans : ∀ x : ℝ, ∫⁻ y, gammaPDF a r x * gammaPDF b r y * F (x / (x + y), x + y) =
      ∫⁻ v, gammaPDF a r x * gammaPDF b r (v - x) * F (x / v, v) := by
    intro x
    have := lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun v => gammaPDF a r x * gammaPDF b r (v - x) * F (x / v, v)) x
    rw [← this]
    refine lintegral_congr fun y => ?_
    simp only [add_sub_cancel_left]
  simp_rw [htrans]
  have hmeasΨ : Measurable (Function.uncurry fun (x v : ℝ) =>
      gammaPDF a r x * gammaPDF b r (v - x) * F (x / v, v)) := by
    refine ((hga.comp measurable_fst).mul (hgb.comp (measurable_snd.sub measurable_fst))).mul
      (hF.comp ?_)
    exact (measurable_fst.div measurable_snd).prodMk measurable_snd
  rw [lintegral_lintegral_swap hmeasΨ.aemeasurable]
  have hmeasΦ : Measurable (Function.uncurry fun (u v : ℝ) =>
      betaPDF a b u * gammaPDF (a + b) r v * F (u, v)) :=
    ((hβ.comp measurable_fst).mul (hgab.comp measurable_snd)).mul hF
  rw [lintegral_lintegral_swap hmeasΦ.aemeasurable]
  refine lintegral_congr_ae ?_
  have hae : ∀ c : ℝ, ∀ᵐ v : ℝ, v ≠ c := fun c => by
    rw [ae_iff]
    simp
  have hne := hae 0
  filter_upwards [hne] with v hv0
  rcases lt_or_gt_of_ne hv0 with hvneg | hvpos
  · -- both sides vanish for `v < 0`
    have hL : ∀ x : ℝ, gammaPDF a r x * gammaPDF b r (v - x) * F (x / v, v) = 0 := by
      intro x
      rcases lt_or_ge x 0 with hx | hx
      · rw [gammaPDF_of_neg hx]
        simp
      · rw [gammaPDF_of_neg (by linarith : v - x < 0)]
        simp
    have hR : ∀ u : ℝ, betaPDF a b u * gammaPDF (a + b) r v * F (u, v) = 0 := by
      intro u
      rw [gammaPDF_of_neg hvneg]
      simp
    simp only [hL, hR, lintegral_zero]
  · have hm1 : Measurable fun x => gammaPDF a r x * gammaPDF b r (v - x) * F (x / v, v) :=
      (hga.mul (hgb.comp (measurable_const.sub measurable_id))).mul
        (hF.comp ((measurable_id.div_const v).prodMk measurable_const))
    have hm2 : Measurable fun u =>
        gammaPDF a r (u * v) * gammaPDF b r (v - u * v) * F (u * v / v, v) :=
      hm1.comp (measurable_id.mul_const v)
    rw [lintegral_eq_ofReal_mul_lintegral_comp_mul hvpos _ hm1, ← lintegral_const_mul _ hm2]
    have hnull : ∀ᵐ u : ℝ, u ≠ 0 ∧ u ≠ 1 := by
      filter_upwards [hae 0, hae 1] with u hu0 hu1
      exact ⟨hu0, hu1⟩
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with u hu
    rw [mul_div_assoc, div_self hvpos.ne', mul_one, ← mul_assoc, ← mul_assoc,
      mul_assoc (ENNReal.ofReal v), ofReal_mul_gammaPDF_mul_gammaPDF ha hb hr hvpos hu.1 hu.2]

/-! ### Gamma moments -/

theorem gammaMeasure_isProbability {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r) :=
  isProbabilityMeasure_gammaMeasure ha hr

theorem betaMeasure_isProbability {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (betaMeasure a b) :=
  isProbabilityMeasureBeta ha hb

/-- Integrals against `Gamma(a, r)` are integrals against its density on `(0, ∞)`. -/
theorem integral_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂gammaMeasure a r =
      ∫ x in Ioi 0, r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * f x := by
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF a r)
    (.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_Ici_eq_integral_Ioi,
    ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (mem_Ici.mpr hx), gammaPDF_of_nonneg hx, ENNReal.toReal_ofReal]
    have := Real.Gamma_pos_of_pos ha
    positivity
  · rw [indicator_of_notMem (by simpa using hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- **Gamma moments**: `E[Xⁿ] = Γ(a+n)/(Γ(a) rⁿ)` for `X ~ Gamma(a, r)`. -/
theorem integral_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    ∫ x, x ^ n ∂gammaMeasure a r = Real.Gamma (a + n) / (Real.Gamma a * r ^ n) := by
  rw [integral_gammaMeasure ha hr]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * x ^ n =
      r ^ a / Real.Gamma a * (x ^ (a + n - 1) * Real.exp (-(r * x))) := by
    intro x hx
    rw [show a + n - 1 = (a - 1) + (n : ℝ) by ring, Real.rpow_add (mem_Ioi.mp hx),
      Real.rpow_natCast]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr]
  have hΓ := Real.Gamma_pos_of_pos ha
  rw [one_div, Real.inv_rpow hr.le, Real.rpow_add hr, Real.rpow_natCast]
  field_simp

/-! ### Beta moments through the factorization -/

/-- Gamma laws live on `(0, ∞)`. -/
theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [gammaMeasure, ae_withDensity_iff (measurable_gammaPDF a r)]
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with x hx0 hne
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · exact absurd (gammaPDF_of_neg hneg) hne
  · exact hpos

/-- **Independence of ratio and total**: `E[Xⁿ] = E[Uⁿ] E[Vⁿ]`. -/
theorem integral_pow_gammaMeasure_eq_mul {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (n : ℕ) :
    ∫ x, x ^ n ∂gammaMeasure a r =
      (∫ u, u ^ n ∂betaMeasure a b) * ∫ v, v ^ n ∂gammaMeasure (a + b) r := by
  haveI := gammaMeasure_isProbability ha hr
  haveI := gammaMeasure_isProbability hb hr
  haveI := gammaMeasure_isProbability (add_pos ha hb) hr
  haveI := betaMeasure_isProbability ha hb
  have h1 : ∫ x, x ^ n ∂gammaMeasure a r =
      ∫ p : ℝ × ℝ, p.1 ^ n ∂(gammaMeasure a r).prod (gammaMeasure b r) := by
    have := integral_fun_fst (μ := gammaMeasure a r) (ν := gammaMeasure b r) (fun x : ℝ => x ^ n)
    simp only [probReal_univ, one_smul] at this
    exact this.symm
  have hpos : ∀ᵐ p ∂(gammaMeasure a r).prod (gammaMeasure b r), 0 < p.1 ∧ 0 < p.2 := by
    have hfst := (measurePreserving_fst (μ := gammaMeasure a r)
      (ν := gammaMeasure b r)).quasiMeasurePreserving.ae (ae_pos_gammaMeasure a r)
    have hsnd := (measurePreserving_snd (μ := gammaMeasure a r)
      (ν := gammaMeasure b r)).quasiMeasurePreserving.ae (ae_pos_gammaMeasure b r)
    filter_upwards [hfst, hsnd] with p h1 h2
    exact ⟨h1, h2⟩
  have h2 : ∫ p : ℝ × ℝ, p.1 ^ n ∂(gammaMeasure a r).prod (gammaMeasure b r) =
      ∫ p : ℝ × ℝ, (projectiveSum p).1 ^ n * (projectiveSum p).2 ^ n
        ∂(gammaMeasure a r).prod (gammaMeasure b r) := by
    refine integral_congr_ae ?_
    filter_upwards [hpos] with p hp
    simp only [projectiveSum]
    rw [← mul_pow, div_mul_cancel₀ _ (by linarith [hp.1, hp.2] : p.1 + p.2 ≠ 0)]
  have hmap := integral_map (μ := (gammaMeasure a r).prod (gammaMeasure b r))
    measurable_projectiveSum.aemeasurable (f := fun q : ℝ × ℝ => q.1 ^ n * q.2 ^ n) (by fun_prop)
  rw [h1, h2, ← hmap, map_projectiveSum_gammaMeasure_prod ha hb hr]
  exact integral_prod_mul (fun u : ℝ => u ^ n) (fun v : ℝ => v ^ n)

/-- **Beta moments**: `E[Uⁿ] = Γ(a+n)Γ(a+b)/(Γ(a)Γ(a+b+n))` for `U ~ Beta(a, b)`. -/
theorem integral_pow_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ u, u ^ n ∂betaMeasure a b =
      Real.Gamma (a + n) * Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma (a + b + n)) := by
  have h := integral_pow_gammaMeasure_eq_mul ha hb one_pos n
  rw [integral_pow_gammaMeasure ha one_pos, integral_pow_gammaMeasure (add_pos ha hb) one_pos,
    one_pow, mul_one, mul_one] at h
  have hΓ1 := Real.Gamma_pos_of_pos ha
  have hΓ2 := Real.Gamma_pos_of_pos (add_pos ha hb)
  have hΓ3 := Real.Gamma_pos_of_pos (by positivity : 0 < a + b + n)
  rw [eq_div_iff (by positivity)]
  field_simp at h
  linarith

/-! ### Power tilts of beta laws -/

/-- **Power tilt**: `uⁿ Beta(a, b) / E[Uⁿ] = Beta(a+n, b)`. -/
theorem withDensity_pow_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (betaMeasure a b).withDensity
        (fun u => ENNReal.ofReal (u ^ n / ∫ x, x ^ n ∂betaMeasure a b)) =
      betaMeasure (a + n) b := by
  rw [integral_pow_betaMeasure ha hb n, betaMeasure, betaMeasure,
    ← withDensity_mul _ (measurable_betaPDF a b) (by fun_prop)]
  congr 1
  funext u
  simp only [Pi.mul_apply]
  by_cases hu : 0 < u ∧ u < 1
  · rw [betaPDF_of_pos_lt_one hu.1 hu.2, betaPDF_of_pos_lt_one hu.1 hu.2,
      ← ENNReal.ofReal_mul (by
        have := beta_pos ha hb
        have := hu.1
        have : 0 < 1 - u := by linarith [hu.2]
        positivity)]
    congr 1
    have hΓa := Real.Gamma_pos_of_pos ha
    have hΓb := Real.Gamma_pos_of_pos hb
    have hΓab := Real.Gamma_pos_of_pos (add_pos ha hb)
    have hΓan := Real.Gamma_pos_of_pos (by positivity : 0 < a + n)
    have hΓabn := Real.Gamma_pos_of_pos (by positivity : 0 < a + b + n)
    rw [show a + ↑n - 1 = (a - 1) + (n : ℝ) by ring, Real.rpow_add hu.1, Real.rpow_natCast, beta,
      beta, show a + (n : ℝ) + b = a + b + n by ring]
    field_simp
  · have hzero : ∀ c : ℝ, betaPDF c b u = 0 := fun c => by
      rw [betaPDF_eq]
      simp [hu]
    rw [hzero, hzero, zero_mul]

/-- The mean of `Beta(a, b)` is `a/(a+b)`. -/
theorem integral_id_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u, u ∂betaMeasure a b = a / (a + b) := by
  have h := integral_pow_betaMeasure ha hb 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, Real.Gamma_add_one ha.ne', Real.Gamma_add_one (add_pos ha hb).ne']
  have hΓa := Real.Gamma_pos_of_pos ha
  have hΓab := Real.Gamma_pos_of_pos (add_pos ha hb)
  field_simp

/-- The second moment of `Beta(a, b)` is `a(a+1)/((a+b)(a+b+1))`. -/
theorem integral_sq_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u, u ^ 2 ∂betaMeasure a b = a * (a + 1) / ((a + b) * (a + b + 1)) := by
  have h := integral_pow_betaMeasure ha hb 2
  rw [h, show a + ((2 : ℕ) : ℝ) = (a + 1) + 1 by push_cast; ring,
    show a + b + ((2 : ℕ) : ℝ) = (a + b + 1) + 1 by push_cast; ring,
    Real.Gamma_add_one (by linarith), Real.Gamma_add_one ha.ne',
    Real.Gamma_add_one (by linarith), Real.Gamma_add_one (add_pos ha hb).ne']
  have hΓa := Real.Gamma_pos_of_pos ha
  have hΓab := Real.Gamma_pos_of_pos (add_pos ha hb)
  field_simp

/-- Beta laws live on `(0, 1)`. -/
theorem ae_mem_Ioo_betaMeasure (a b : ℝ) : ∀ᵐ u ∂betaMeasure a b, u ∈ Ioo (0 : ℝ) 1 := by
  rw [betaMeasure, ae_withDensity_iff (measurable_betaPDF a b)]
  refine .of_forall fun u hne => ?_
  by_contra hu
  exact hne (by rw [betaPDF_eq]; simp [show ¬ (0 < u ∧ u < 1) from hu])

theorem integrable_pow_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (fun u : ℝ => u ^ n) (betaMeasure a b) := by
  haveI := betaMeasure_isProbability ha hb
  refine Integrable.of_bound (C := 1) (by fun_prop) ?_
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with u hu
  rw [Real.norm_eq_abs, abs_pow, abs_of_pos hu.1]
  exact pow_le_one₀ hu.1.le hu.2.le

/-- The variance of `Beta(a, b)` is `ab/((a+b)²(a+b+1))`. -/
theorem variance_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u, (u - a / (a + b)) ^ 2 ∂betaMeasure a b = a * b / ((a + b) ^ 2 * (a + b + 1)) := by
  haveI := betaMeasure_isProbability ha hb
  set m := a / (a + b)
  have hi1 : Integrable (fun u : ℝ => u) (betaMeasure a b) := by
    simpa using integrable_pow_betaMeasure ha hb 1
  have hi2 := integrable_pow_betaMeasure ha hb 2
  have hA : Integrable (fun u : ℝ => u ^ 2 - 2 * m * u) (betaMeasure a b) :=
    hi2.sub (hi1.const_mul _)
  have hB : Integrable (fun u : ℝ => 2 * m * u) (betaMeasure a b) := hi1.const_mul _
  have e : (fun u : ℝ => (u - m) ^ 2) = fun u => (u ^ 2 - 2 * m * u) + m ^ 2 := by
    funext u
    ring
  rw [e, integral_add hA (integrable_const _), integral_sub hi2 hB, integral_const_mul,
    integral_sq_betaMeasure ha hb, integral_id_betaMeasure ha hb, integral_const, probReal_univ,
    one_smul]
  simp only [m]
  field_simp
  ring

/-- **The one-step tilt law**: tilting `Beta(a, b)` once by `u` raises the mean by exactly
`Var(U)/E[U]`; the tilted law is `Beta(a+1, b)`. -/
theorem integral_id_betaMeasure_succ_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u, u ∂betaMeasure (a + 1) b - ∫ u, u ∂betaMeasure a b =
      (∫ u, (u - ∫ x, x ∂betaMeasure a b) ^ 2 ∂betaMeasure a b) / ∫ u, u ∂betaMeasure a b := by
  rw [integral_id_betaMeasure (by linarith) hb, integral_id_betaMeasure ha hb,
    variance_betaMeasure ha hb]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
