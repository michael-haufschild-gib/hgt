import GaloisForLFunctions.RHTower.ModularArcLineModelBlind

/-!
# Cosine moments of the arc pair slope

For an arc point `c + iy`, `y > 0`, the `c`-derivative of the arc pair
`((x − c)² + y²)^{−1/2} + ((x + c)² + y²)^{−1/2}` (at fixed `y`) is the pair slope

`x [((x − c)² + y²)^{−3/2} − ((x + c)² + y²)^{−3/2}]`.

**Theorem** (`integral_arcPairSlope_mul_cos`).  For `y, k > 0`,

`∫_ℝ x [((x − c)² + y²)^{−3/2} − ((x + c)² + y²)^{−3/2}] cos(kx) dx
   = 4 [(k c / y) K₁(k y) cos(k c) − k K₀(k y) sin(k c)]`,

with `K_j = kMoment j`.  On the unit circle (`y = √(1 − c²)`) the right side is `4 d/dc` of the arc
Whittaker mode `K₀(k √(1 − c²)) cos(k c)`.

Ingredients.
* `∫_ℝ e^t e^{−r cosh t} dt = 2 K₁(r)` (`integral_exp_mul_exp_neg_mul_cosh`): reflect `t ↦ −t` and
  average.
* `∫₀^∞ e^{−(As + B/s)} ds = 2 √(B/A) K₁(2√(AB))` (`integral_exp_neg_add_inv`): `s = e^t`, then
  shift `t` by `½ log(B/A)`.
* `∫_ℝ (x² + y²)^{−3/2} cos(kx) dx = (2k/y) K₁(ky)` (`integral_rpow_mul_cos_eq_kMoment`): Gaussian
  subordination `A^{−3/2} = (2/√π) ∫₀^∞ s^{1/2} e^{−sA} ds` and Fubini.
* The sine form `∫ x (x² + y²)^{−3/2} sin(kx) dx = 2k K₀(ky)` (`integral_mul_rpow_sin_eq_kMoment`),
  the odd parts (`integral_mul_rpow_cos_eq_zero`), and the shifts `x = t ± c`.
-/

open MeasureTheory Set Filter Topology
open RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### The `K₁` integrals -/

theorem integrable_cosh_mul_exp_neg_mul_cosh {r : ℝ} (hr : 0 < r) :
    Integrable fun t : ℝ => Real.cosh t * Real.exp (-(r * Real.cosh t)) := by
  have hO : IntegrableOn (fun t : ℝ => Real.cosh t * Real.exp (-(r * Real.cosh t))) (Ioi 0) :=
    (integrableOn_kIntegrand 1 hr).congr_fun (fun t _ => by simp [kIntegrand]) measurableSet_Ioi
  have hI : IntegrableOn (fun t : ℝ => Real.cosh t * Real.exp (-(r * Real.cosh t))) (Iic 0) := by
    have := hO.comp_neg
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    simpa [Real.cosh_neg] using this
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hI.union hO

/-- `∫_ℝ cosh t e^{−r cosh t} dt = 2 K₁(r)`. -/
theorem integral_cosh_mul_exp_neg_mul_cosh {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ, Real.cosh t * Real.exp (-(r * Real.cosh t)) = 2 * kMoment 1 r := by
  have hcosh := integrable_cosh_mul_exp_neg_mul_cosh hr
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hcosh.integrableOn
      hcosh.integrableOn]
  have hneg : ∫ t in Iic (0 : ℝ), Real.cosh t * Real.exp (-(r * Real.cosh t)) =
      ∫ t in Ioi (0 : ℝ), Real.cosh t * Real.exp (-(r * Real.cosh t)) := by
    have h := integral_comp_neg_Ioi (0 : ℝ)
      (fun t : ℝ => Real.cosh t * Real.exp (-(r * Real.cosh t)))
    simp only [neg_zero, Real.cosh_neg] at h
    exact h.symm
  rw [hneg, kMoment]
  simp only [pow_one]
  ring

/-- `∫_ℝ e^t e^{−r cosh t} dt = 2 K₁(r)`. -/
theorem integral_exp_mul_exp_neg_mul_cosh {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ, Real.exp t * Real.exp (-(r * Real.cosh t)) = 2 * kMoment 1 r := by
  have hcosh := integrable_cosh_mul_exp_neg_mul_cosh hr
  have hint : Integrable fun t : ℝ => Real.exp t * Real.exp (-(r * Real.cosh t)) :=
    (hcosh.const_mul 2).mono' (by fun_prop) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h1 : Real.exp t ≤ 2 * Real.cosh t := by
        rw [Real.cosh_eq]; linarith [Real.exp_pos (-t)]
      have h2 := Real.exp_pos (-(r * Real.cosh t))
      nlinarith)
  have hint' : Integrable fun t : ℝ => Real.exp (-t) * Real.exp (-(r * Real.cosh t)) := by
    have := hint.comp_neg
    simpa [Real.cosh_neg] using this
  have hrefl : ∫ t : ℝ, Real.exp (-t) * Real.exp (-(r * Real.cosh t)) =
      ∫ t : ℝ, Real.exp t * Real.exp (-(r * Real.cosh t)) := by
    have h := integral_neg_eq_self (fun t : ℝ => Real.exp t * Real.exp (-(r * Real.cosh t))) volume
    simpa [Real.cosh_neg] using h
  have hsum : ∫ t : ℝ, Real.cosh t * Real.exp (-(r * Real.cosh t)) =
      ((∫ t : ℝ, Real.exp t * Real.exp (-(r * Real.cosh t))) +
        ∫ t : ℝ, Real.exp (-t) * Real.exp (-(r * Real.cosh t))) / 2 := by
    rw [← integral_add hint hint', ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Real.cosh_eq]
    ring
  rw [hrefl, integral_cosh_mul_exp_neg_mul_cosh hr] at hsum
  linarith

/-- `∫₀^∞ e^{−(As + B/s)} ds = 2 √(B/A) K₁(2√(AB))`. -/
theorem integral_exp_neg_add_inv {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(A * s + B / s)) =
      2 * Real.sqrt (B / A) * kMoment 1 (2 * Real.sqrt (A * B)) := by
  have himage : Real.exp '' univ = Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun s => Real.exp (-(A * s + B / s)))
  rw [himage, Measure.restrict_univ] at hcv
  rw [hcv]
  have e1 : ∀ t : ℝ, |Real.exp t| • Real.exp (-(A * Real.exp t + B / Real.exp t)) =
      Real.exp t * Real.exp (-(A * Real.exp t + B * Real.exp (-t))) := by
    intro t
    rw [abs_of_pos (Real.exp_pos t), smul_eq_mul, div_eq_mul_inv, ← Real.exp_neg]
  simp_rw [e1]
  set c : ℝ := Real.log (B / A) / 2 with hc
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => Real.exp t * Real.exp (-(A * Real.exp t + B * Real.exp (-t)))) c
  rw [← hshift]
  have hec : Real.exp c = Real.sqrt (B / A) := by
    rw [hc, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hB hA)]
    ring_nf
  have hk1 : A * Real.sqrt (B / A) = Real.sqrt (A * B) := by
    rw [Real.sqrt_div' _ hA.le, Real.sqrt_mul hA.le]
    field_simp
    rw [Real.sq_sqrt hA.le]
  have hk2 : B * (Real.sqrt (B / A))⁻¹ = Real.sqrt (A * B) := by
    rw [Real.sqrt_div' _ hA.le, Real.sqrt_mul hA.le]
    have hsA := Real.sqrt_pos.mpr hA
    have hsB := Real.sqrt_pos.mpr hB
    field_simp
    rw [Real.sq_sqrt hB.le]
  have e2 : ∀ t : ℝ, Real.exp (t + c) * Real.exp (-(A * Real.exp (t + c) +
      B * Real.exp (-(t + c)))) =
      Real.sqrt (B / A) * (Real.exp t * Real.exp (-(2 * Real.sqrt (A * B) * Real.cosh t))) := by
    intro t
    have h1 : Real.exp (t + c) = Real.exp t * Real.sqrt (B / A) := by rw [Real.exp_add, hec]
    have h2 : Real.exp (-(t + c)) = Real.exp (-t) * (Real.sqrt (B / A))⁻¹ := by
      rw [neg_add, Real.exp_add, Real.exp_neg c, hec]
    have h3 : -(A * Real.exp (t + c) + B * Real.exp (-(t + c))) =
        -(2 * Real.sqrt (A * B) * Real.cosh t) := by
      rw [h1, h2, Real.cosh_eq]
      have : A * (Real.exp t * Real.sqrt (B / A)) + B * (Real.exp (-t) * (Real.sqrt (B / A))⁻¹) =
          Real.exp t * (A * Real.sqrt (B / A)) + Real.exp (-t) * (B * (Real.sqrt (B / A))⁻¹) := by
        ring
      rw [this, hk1, hk2]
      ring
    rw [h3, h1]
    ring
  simp_rw [e2]
  rw [integral_const_mul,
    integral_exp_mul_exp_neg_mul_cosh (by positivity : 0 < 2 * Real.sqrt (A * B))]
  ring

/-! ### The cosine transform of `(x² + y²)^{−3/2}` -/

theorem rpow_neg_three_halves_le {y x : ℝ} (hy : 0 < y) :
    (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) ≤ (max 1 (1 / y ^ 2) / y) * (1 + x ^ 2)⁻¹ := by
  have hA : 0 < x ^ 2 + y ^ 2 := by positivity
  have h1 : y ≤ (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy.le).symm
      _ ≤ Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  have hs : 0 < (x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hA _
  have e : (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) =
      (x ^ 2 + y ^ 2)⁻¹ * ((x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_neg hA.le, ← Real.rpow_add hA]
    norm_num
  have h2 : ((x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ))⁻¹ ≤ y⁻¹ := inv_anti₀ hy h1
  have hb : (x ^ 2 + y ^ 2)⁻¹ ≤ max 1 (1 / y ^ 2) * (1 + x ^ 2)⁻¹ := by
    rw [inv_le_comm₀ hA (by positivity), mul_inv, inv_inv]
    rcases le_or_gt 1 y with hy1 | hy1
    · have : max 1 (1 / y ^ 2) = 1 := max_eq_left (by
        rw [div_le_one (by positivity)]; nlinarith)
      rw [this, inv_one, one_mul]; nlinarith
    · have : max 1 (1 / y ^ 2) = 1 / y ^ 2 := max_eq_right (by
        rw [le_div_iff₀ (by positivity)]; nlinarith)
      rw [this, one_div, inv_inv]
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg x, mul_le_mul_of_nonneg_left hy2 (sq_nonneg x)]
  rw [e]
  calc (x ^ 2 + y ^ 2)⁻¹ * ((x ^ 2 + y ^ 2) ^ (1 / 2 : ℝ))⁻¹
      ≤ (max 1 (1 / y ^ 2) * (1 + x ^ 2)⁻¹) * y⁻¹ :=
        mul_le_mul hb h2 (by positivity) (by positivity)
    _ = (max 1 (1 / y ^ 2) / y) * (1 + x ^ 2)⁻¹ := by ring

theorem integrable_rpow_neg_three_halves {y : ℝ} (hy : 0 < y) :
    Integrable fun x : ℝ => (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := by
  refine (integrable_inv_one_add_sq.const_mul (max 1 (1 / y ^ 2) / y)).mono'
    (by
      refine Continuous.aestronglyMeasurable ?_
      exact (by fun_prop : Continuous fun x : ℝ => x ^ 2 + y ^ 2).rpow_const
        fun x => Or.inl (by positivity))
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact rpow_neg_three_halves_le hy

/-- **The cosine Basset integral**: `∫ (x² + y²)^{−3/2} cos(kx) dx = (2k/y) K₁(ky)`. -/
theorem integral_rpow_mul_cos_eq_kMoment {y k : ℝ} (hy : 0 < y) (hk : 0 < k) :
    ∫ x : ℝ, (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) =
      2 * k / y * kMoment 1 (k * y) := by
  set G : ℝ → ℝ → ℝ := fun x s => 2 / Real.sqrt Real.pi *
    (Real.cos (k * x) * (s ^ (1 / 2 : ℝ) * Real.exp (-(s * (x ^ 2 + y ^ 2))))) with hG
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hinS : ∀ x : ℝ, ∫ s in Ioi (0 : ℝ), G x s =
      (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) := by
    intro x
    have hA : 0 < x ^ 2 + y ^ 2 := by positivity
    simp only [hG]
    rw [integral_const_mul, integral_const_mul, rpow_neg_three_halves_eq_integral hA]
    ring
  have hintS : ∀ x : ℝ, IntegrableOn (fun s => s ^ (1 / 2 : ℝ) *
      Real.exp (-(s * (x ^ 2 + y ^ 2)))) (Ioi 0) := by
    intro x
    have hA : 0 < x ^ 2 + y ^ 2 := by positivity
    by_contra hni
    have h0 := integral_sqrt_mul_exp_neg_mul hA
    rw [integral_undef hni] at h0
    have : 0 < (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * (Real.sqrt Real.pi / 2) :=
      mul_pos (Real.rpow_pos_of_pos hA _) (by positivity)
    linarith
  have hcontG : Continuous (Function.uncurry G) := by
    have hr : Continuous fun p : ℝ × ℝ => p.2 ^ (1 / 2 : ℝ) :=
      continuous_snd.rpow_const fun _ => Or.inr (by norm_num)
    simp only [hG]
    exact continuous_const.mul ((Real.continuous_cos.comp
      (continuous_const.mul continuous_fst)).mul (hr.mul (by fun_prop)))
  have hnormS : ∀ x : ℝ, ∫ s in Ioi (0 : ℝ), ‖G x s‖ =
      |Real.cos (k * x)| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := by
    intro x
    have hA : 0 < x ^ 2 + y ^ 2 := by positivity
    have e : ∀ s ∈ Ioi (0 : ℝ), ‖G x s‖ = 2 / Real.sqrt Real.pi * |Real.cos (k * x)| *
        (s ^ (1 / 2 : ℝ) * Real.exp (-(s * (x ^ 2 + y ^ 2)))) := by
      intro s hs
      simp only [hG, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs) _), abs_of_pos (div_pos two_pos hpi)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      integral_sqrt_mul_exp_neg_mul hA]
    field_simp
  have hFint : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hcontG.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact ((hintS x).const_mul (Real.cos (k * x))).const_mul (2 / Real.sqrt Real.pi) |>.congr
        (Eventually.of_forall fun s => by simp only [hG, Function.uncurry])
    · simp only [Function.uncurry]
      simp_rw [hnormS]
      refine (integrable_rpow_neg_three_halves hy).mono' (by fun_prop)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ x ^ 2 + y ^ 2 by positivity) (-(3 / 2) : ℝ)
        positivity)]
      calc |Real.cos (k * x)| * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ)
          ≤ 1 * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Real.rpow_nonneg (by positivity) _)
        _ = (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := one_mul _
  have hswap := integral_integral_swap hFint
  have hlhs : ∫ x : ℝ, (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) =
      ∫ x : ℝ, ∫ s in Ioi (0 : ℝ), G x s := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (hinS x).symm
  rw [hlhs, hswap]
  have hinX : ∀ s ∈ Ioi (0 : ℝ), ∫ x : ℝ, G x s =
      2 * Real.exp (-(y ^ 2 * s + k ^ 2 / 4 / s)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have e : ∀ x : ℝ, G x s = 2 / Real.sqrt Real.pi * (s ^ (1 / 2 : ℝ) *
        Real.exp (-(s * y ^ 2))) * (Real.exp (-(s * x ^ 2)) * Real.cos (k * x)) := by
      intro x
      simp only [hG]
      rw [show -(s * (x ^ 2 + y ^ 2)) = -(s * y ^ 2) + -(s * x ^ 2) by ring, Real.exp_add]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_exp_neg_mul_sq_mul_cos hs0]
    have hsq : Real.sqrt (Real.pi / s) = Real.sqrt Real.pi / s ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_div' _ hs0.le, Real.sqrt_eq_rpow s]
    rw [hsq]
    have hsr : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hexp : Real.exp (-(y ^ 2 * s + k ^ 2 / 4 / s)) =
        Real.exp (-(s * y ^ 2)) * Real.exp (-(k ^ 2 / (4 * s))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [hexp]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinX, integral_const_mul,
    integral_exp_neg_add_inv (by positivity) (by positivity)]
  have hsq : Real.sqrt (y ^ 2 * (k ^ 2 / 4)) = k * y / 2 := by
    rw [show y ^ 2 * (k ^ 2 / 4) = (k * y / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsq2 : Real.sqrt (k ^ 2 / 4 / y ^ 2) = k / (2 * y) := by
    rw [show k ^ 2 / 4 / y ^ 2 = (k / (2 * y)) ^ 2 by field_simp; ring,
      Real.sqrt_sq (by positivity)]
  rw [hsq, hsq2, show 2 * (k * y / 2) = k * y by ring]
  field_simp

/-! ### Odd parts and shifts -/

theorem integral_rpow_mul_sin_eq_zero (y k : ℝ) :
    ∫ x : ℝ, (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x) = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) *
    Real.sin (k * x)) volume
  simp only [neg_sq, mul_neg, Real.sin_neg, integral_neg] at h
  linarith

/-- `∫ x ((x − c)² + y²)^{−3/2} cos(kx) dx = (2kc/y) K₁(ky) cos(kc) − 2k K₀(ky) sin(kc)`. -/
theorem integral_mul_rpow_shift_cos {y k : ℝ} (hy : 0 < y) (hk : 0 < k) (c : ℝ) :
    ∫ x : ℝ, x * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) =
      2 * k * c / y * kMoment 1 (k * y) * Real.cos (k * c) -
        2 * k * kMoment 0 (k * y) * Real.sin (k * c) := by
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => x * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x)) c
  rw [← hshift]
  simp only [add_sub_cancel_right]
  have hR := integrable_rpow_neg_three_halves hy
  have hxR : Integrable fun x : ℝ => x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
    (integrable_abs_mul_rpow hy).mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)])
  have e : ∀ x : ℝ, (x + c) * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * (x + c)) =
      Real.cos (k * c) * (x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x)) -
        Real.sin (k * c) * (x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x)) +
      c * Real.cos (k * c) * ((x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x)) -
        c * Real.sin (k * c) * ((x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x)) := by
    intro x
    rw [mul_add, Real.cos_add]
    ring
  simp_rw [e]
  have hb : ∀ (g : ℝ → ℝ), Continuous g → (∀ x, |g x| ≤ 1) → ∀ (h : ℝ → ℝ), Integrable h →
      Integrable fun x => h x * g x := fun g hg hg1 h hh =>
    hh.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hg1 x)
  have hcos : Continuous fun x : ℝ => Real.cos (k * x) := by fun_prop
  have hsin : Continuous fun x : ℝ => Real.sin (k * x) := by fun_prop
  have i1 : Integrable fun x : ℝ => x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) :=
    hb _ hcos (fun x => Real.abs_cos_le_one _) _ hxR
  have i2 : Integrable fun x : ℝ => x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x) :=
    hb _ hsin (fun x => Real.abs_sin_le_one _) _ hxR
  have i3 : Integrable fun x : ℝ => (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) :=
    hb _ hcos (fun x => Real.abs_cos_le_one _) _ hR
  have i4 : Integrable fun x : ℝ => (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x) :=
    hb _ hsin (fun x => Real.abs_sin_le_one _) _ hR
  have i12 : Integrable fun x : ℝ =>
      Real.cos (k * c) * (x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x)) -
        Real.sin (k * c) * (x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x)) :=
    (i1.const_mul _).sub (i2.const_mul _)
  have i123 : Integrable fun x : ℝ =>
      Real.cos (k * c) * (x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x)) -
        Real.sin (k * c) * (x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.sin (k * x)) +
      c * Real.cos (k * c) * ((x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x)) :=
    i12.add (i3.const_mul _)
  rw [integral_sub i123 (i4.const_mul _), integral_add i12 (i3.const_mul _),
    integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_mul_rpow_cos_eq_zero,
    integral_mul_rpow_sin_eq_kMoment hy hk, integral_rpow_mul_cos_eq_kMoment hy hk,
    integral_rpow_mul_sin_eq_zero]
  ring

/-- **Cosine moment of the arc pair slope.** -/
theorem integral_arcPairSlope_mul_cos {y k : ℝ} (hy : 0 < y) (hk : 0 < k) (c : ℝ) :
    ∫ x : ℝ, x * (((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) -
        ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ)) * Real.cos (k * x) =
      4 * (k * c / y * kMoment 1 (k * y) * Real.cos (k * c) -
        k * kMoment 0 (k * y) * Real.sin (k * c)) := by
  have hR := integrable_rpow_neg_three_halves hy
  have hint : ∀ d : ℝ, Integrable fun x : ℝ =>
      x * ((x - d) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) := by
    intro d
    have hx0 : Integrable fun x : ℝ => x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
      (integrable_abs_mul_rpow hy).mono' (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)])
    have h1 : Integrable fun x : ℝ => (x - d) * ((x - d) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
      hx0.comp_sub_right d
    have h2 : Integrable fun x : ℝ => d * ((x - d) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
      (hR.comp_sub_right d).const_mul d
    refine ((h1.add h2).mul_bdd (by fun_prop : Continuous fun x : ℝ =>
      Real.cos (k * x)).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have e : ∀ x : ℝ, x * (((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) -
      ((x + c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ)) * Real.cos (k * x) =
      x * ((x - c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) -
        x * ((x - -c) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) * Real.cos (k * x) := by
    intro x; rw [sub_neg_eq_add]; ring
  simp_rw [e]
  rw [integral_sub (hint c) (hint (-c)), integral_mul_rpow_shift_cos hy hk,
    integral_mul_rpow_shift_cos hy hk]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg]
  ring

end

end RHTower
