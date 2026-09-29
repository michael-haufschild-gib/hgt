import GaloisForLFunctions.HTGeometry.PhaseCoherenceIntegral
import GaloisForLFunctions.HTGeometry.CubicWallHodgeBetaFlux

/-!
# The Cayley contrast law of an exponential clock pair

For two independent unit exponential clocks `x, y` the Cayley contrast `δ = (x - y)/(x + y)` is
uniform on `(-1, 1)`:

`∬ φ(δ(x, y)) μ(dx) μ(dy) = ½ ∫₋₁¹ φ(v) dv`

for every measurable `φ` bounded on `(-1, 1)`.  The ratio substitution `y = xt` and the radial
integral `∫₀^∞ x e^{-(1+t)x} dx = (1 + t)^{-2}` reduce the pair integral to
`∫₀^∞ φ((1 - t)/(1 + t)) (1 + t)^{-2} dt`, and the Cayley substitution `t = (1 - v)/(1 + v)`
turns it into `½ ∫₋₁¹ φ`.

With `λ = δ²`, the cubic coherence `κ = 8(xy)^{3/2}/(x + y)³ = (1 - λ)^{3/2}` and the Hodge
collision
amplitude `Ω_H = √(105/8) δ(1 - δ²) = √(105/8) [δ/√(1 - λ)] κ`:

* `∬ Ω_H² = 1`, and the `λ`-law of `Ω_H² μ⊗μ` is `Beta(3/2, 3)`;
* the `λ`-law of `κ² μ⊗μ/(16/35)` is `Beta(1/2, 4)`, with density `(35/32) a^{-1/2}(1 - a)³`;
* `Ω_H² = (105/8) [λ/(1 - λ)] κ²`, and the `Beta(3/2, 3)` density is `6 a/(1 - a)` times the
  `Beta(1/2, 4)` density.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_contrast : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-! ## The radial integral -/

theorem integrableOn_id_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(c * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := c)
    (by norm_num) (by norm_num) hc
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Real.rpow_one]
  ring_nf

/-- `(x, t) ↦ x e^{-(1+t)x}` is integrable on the open quadrant. -/
theorem integrable_radial_prod :
    Integrable (fun p : ℝ × ℝ => p.1 * Real.exp (-((1 + p.2) * p.1)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * Real.exp (-((1 + p.2) * p.1)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 * Real.exp (-((1 + p.2) * p.1)))
      |>.aestronglyMeasurable
  rw [integrable_prod_iff' hm]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    exact integrableOn_id_mul_exp_neg_mul (by linarith)
  · have hval : (fun t => ∫ x, ‖x * Real.exp (-((1 + t) * x))‖ ∂(volume.restrict (Ioi (0 : ℝ))))
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => (1 + t) ^ (-(2 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← integral_x_mul_exp_parameter (le_of_lt ht)]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hx) (Real.exp_pos _).le)]
    refine Integrable.congr ?_ hval.symm
    refine integrable_inv_one_add_sq.restrict.mono'
      (by fun_prop : Measurable fun t : ℝ => (1 + t) ^ (-(2 : ℝ))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.rpow_neg (by linarith), Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (by nlinarith)

/-! ## The uniform contrast law -/

theorem measurable_cayleyContrast : Measurable fun z : ℝ × ℝ => cayleyContrast z.1 z.2 := by
  unfold cayleyContrast
  fun_prop

/-- Both clocks are almost surely positive. -/
theorem ae_pos_expPair :
    ∀ᵐ z ∂((expMeasure 1).prod (expMeasure 1)), 0 < z.1 ∧ 0 < z.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_pos_expMeasure_one,
    Measure.quasiMeasurePreserving_snd.ae ae_pos_expMeasure_one] with z h1 h2
  exact ⟨h1, h2⟩

theorem cayleyContrast_mem_Ioo {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cayleyContrast x y ∈ Ioo (-1 : ℝ) 1 := by
  rw [cayleyContrast]
  constructor
  · rw [lt_div_iff₀ (by linarith)]
    linarith
  · rw [div_lt_one (by linarith)]
    linarith

theorem cayleyContrast_mul_right {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    cayleyContrast x (x * t) = (1 - t) / (1 + t) := by
  rw [cayleyContrast]
  have h1 : (1 : ℝ) + t ≠ 0 := by positivity
  field_simp

/-- **The uniform contrast law.**  `∬ φ(δ) dμ dμ = ½ ∫₋₁¹ φ` for `φ` bounded on `(-1, 1)`. -/
theorem integral_cayleyContrast_prod {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ v ∈ Ioo (-1 : ℝ) 1, |φ v| ≤ C) :
    ∫ z, φ (cayleyContrast z.1 z.2) ∂((expMeasure 1).prod (expMeasure 1))
      = 1 / 2 * ∫ v in Ioo (-1 : ℝ) 1, φ v := by
  have hint : Integrable (fun z : ℝ × ℝ => φ (cayleyContrast z.1 z.2))
      ((expMeasure 1).prod (expMeasure 1)) := by
    refine (integrable_const C).mono' (hφ.comp measurable_cayleyContrast).aestronglyMeasurable ?_
    filter_upwards [ae_pos_expPair] with z hz
    rw [Real.norm_eq_abs]
    exact hC _ (cayleyContrast_mem_Ioo hz.1 hz.2)
  have hinner : ∀ x ∈ Ioi (0 : ℝ), Real.exp (-x) • ∫ y, φ (cayleyContrast x y) ∂(expMeasure 1)
      = ∫ t in Ioi (0 : ℝ), x * Real.exp (-((1 + t) * x)) * φ ((1 - t) / (1 + t)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [integral_expMeasure_one]
    have h := integral_comp_mul_left_Ioi
      (fun y : ℝ => Real.exp (-y) • φ (cayleyContrast x y)) 0 hx0
    simp only [mul_zero] at h
    rw [show (∫ y in Ioi (0 : ℝ), Real.exp (-y) • φ (cayleyContrast x y))
        = x • ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) • φ (cayleyContrast x (x * t)) by
      rw [h, smul_smul, mul_inv_cancel₀ hx0.ne', one_smul], smul_smul, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [cayleyContrast_mul_right hx0 ht, smul_eq_mul, smul_eq_mul]
    have hexp : Real.exp (-x) * Real.exp (-(x * t)) = Real.exp (-((1 + t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  have hswap : Integrable (Function.uncurry fun x t : ℝ =>
      x * Real.exp (-((1 + t) * x)) * φ ((1 - t) / (1 + t)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_radial_prod.mul_const C).mono' ?_ ?_
    · exact (by fun_prop : Measurable (Function.uncurry fun x t : ℝ =>
        x * Real.exp (-((1 + t) * x)) * φ ((1 - t) / (1 + t)))).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
      have hx : (0 : ℝ) < p.1 := hp.1
      have ht : (0 : ℝ) < p.2 := hp.2
      have hc : (1 - p.2) / (1 + p.2) ∈ Ioo (-1 : ℝ) 1 := by
        rw [← cayleyContrast_mul_right one_pos ht, one_mul]
        exact cayleyContrast_mem_Ioo one_pos ht
      show ‖p.1 * Real.exp (-((1 + p.2) * p.1)) * φ ((1 - p.2) / (1 + p.2))‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hx.le (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_left (hC _ hc) (mul_nonneg hx.le (Real.exp_pos _).le)
  have hrad : ∀ t ∈ Ioi (0 : ℝ),
      ∫ x in Ioi (0 : ℝ), x * Real.exp (-((1 + t) * x)) * φ ((1 - t) / (1 + t))
        = φ ((1 - t) / (1 + t)) / (1 + t) ^ 2 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [integral_mul_const, integral_x_mul_exp_parameter ht0.le, Real.rpow_neg (by linarith),
      Real.rpow_two, inv_mul_eq_div]
  rw [integral_prod _ hint, integral_expMeasure_one,
    setIntegral_congr_fun measurableSet_Ioi hinner, integral_integral_swap hswap,
    setIntegral_congr_fun measurableSet_Ioi hrad, integral_Ioi_eq_cayley, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have hv1 : (1 : ℝ) + v ≠ 0 := (show (0 : ℝ) < 1 + v by linarith [hv.1]).ne'
  have h1 : 1 + (1 - v) / (1 + v) = 2 / (1 + v) := by field_simp; ring
  have h2 : (1 - (1 - v) / (1 + v)) / (1 + (1 - v) / (1 + v)) = v := by
    rw [h1]
    field_simp
    ring
  rw [h2, h1]
  field_simp

/-! ## Even integrands and the square substitution -/

theorem intervalIntegrable_of_integrableOn_Ioo {h : ℝ → ℝ} {a b c d : ℝ}
    (hi : IntegrableOn h (Ioo a b)) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable h volume c d := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcd,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hi.mono_set (Ioo_subset_Ioo hac hdb)

/-- `∫₋₁¹ h = 2 ∫₀¹ h` for an even integrable `h`. -/
theorem integral_Ioo_of_even {h : ℝ → ℝ} (hi : IntegrableOn h (Ioo (-1) 1))
    (heven : ∀ v, h (-v) = h v) :
    ∫ v in Ioo (-1 : ℝ) 1, h v = 2 * ∫ v in Ioo (0 : ℝ) 1, h v := by
  have hL : ∫ v in Ioo (-1 : ℝ) 1, h v = ∫ v in (-1 : ℝ)..1, h v := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  have hR : ∫ v in Ioo (0 : ℝ) 1, h v = ∫ v in (0 : ℝ)..1, h v := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hL, hR, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (intervalIntegrable_of_integrableOn_Ioo hi le_rfl (by norm_num) (by norm_num))
      (intervalIntegrable_of_integrableOn_Ioo hi (by norm_num) (by norm_num) le_rfl)]
  have hneg : ∫ v in (-1 : ℝ)..0, h v = ∫ v in (0 : ℝ)..1, h v := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) h
    simp only [heven, neg_zero] at this
    exact this.symm
  rw [hneg]
  ring

theorem image_sq_Ioo : (fun v : ℝ => v ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
  ext a
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨by nlinarith [hv.1], by nlinarith [hv.1, hv.2]⟩
  · intro ha
    refine ⟨Real.sqrt a, ⟨Real.sqrt_pos.mpr ha.1, ?_⟩, Real.sq_sqrt ha.1.le⟩
    rw [Real.sqrt_lt' one_pos, one_pow]
    exact ha.2

/-- `∫₀¹ g(a) da = ∫₀¹ 2v g(v²) dv`. -/
theorem integral_Ioo_comp_sq (g : ℝ → ℝ) :
    ∫ a in Ioo (0 : ℝ) 1, g a = ∫ v in Ioo (0 : ℝ) 1, 2 * v * g (v ^ 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun v : ℝ => v ^ 2)
    (f' := fun v => 2 * v) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun v _ => by simpa using (hasDerivAt_pow 2 v).hasDerivWithinAt)
    (fun v hv w hw h => (pow_left_inj₀ hv.1.le hw.1.le two_ne_zero).mp h) g
  rw [image_sq_Ioo] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  rw [smul_eq_mul, abs_of_pos (by linarith [hv.1])]

/-! ## The Hodge collision state -/

/-- The Hodge collision amplitude `Ω_H = √(105/8) δ(1 - δ²)` as a function of the contrast. -/
def hodgeCollisionAmplitude (v : ℝ) : ℝ := Real.sqrt (105 / 8) * (v * (1 - v ^ 2))

theorem hodgeCollisionAmplitude_neg (v : ℝ) :
    hodgeCollisionAmplitude (-v) = -hodgeCollisionAmplitude v := by
  rw [hodgeCollisionAmplitude, hodgeCollisionAmplitude]
  ring

/-- `Ω_H` vanishes on the equal-clock diagonal. -/
theorem hodgeCollisionAmplitude_diagonal (x : ℝ) :
    hodgeCollisionAmplitude (cayleyContrast x x) = 0 := by
  rw [cayleyContrast, sub_self, zero_div, hodgeCollisionAmplitude]
  ring

theorem hodgeCollisionAmplitude_sq (v : ℝ) :
    hodgeCollisionAmplitude v ^ 2 = 105 / 8 * (v ^ 2 * (1 - v ^ 2) ^ 2) := by
  rw [hodgeCollisionAmplitude, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem hodgeCollisionAmplitude_sq_le {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) :
    hodgeCollisionAmplitude v ^ 2 ≤ 105 / 8 := by
  rw [hodgeCollisionAmplitude_sq]
  have h1 : v ^ 2 < 1 := by nlinarith [hv.1, hv.2]
  have h2 : 0 ≤ 1 - v ^ 2 := by linarith
  have h3 : v ^ 2 * (1 - v ^ 2) ^ 2 ≤ 1 := by
    have : (1 - v ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg v]
    nlinarith [sq_nonneg v]
  linarith

/-- **(CCRHD.1).**  `λ + g² = 1` and `κ = g³ = (1 - λ)^{3/2}` on the open quadrant. -/
theorem cayley_pair_identities {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cayleyContrast x y ^ 2 + cayleyCoherence x y ^ 2 = 1 ∧
      wallCubicKernel x y = cayleyCoherence x y ^ 3 ∧
      wallCubicKernel x y = Real.sqrt (1 - cayleyContrast x y ^ 2) ^ 3 := by
  have h1 := cayleyContrast_sq_add_cayleyCoherence_sq hx.le hy.le (by linarith)
  have h2 : wallCubicKernel x y = cayleyCoherence x y ^ 3 := by
    rw [wallCubicKernel, routePPrimitiveGammaJuliaStokesWallCubicKernel,
      cubicKernel_eq_cayleyCoherence_pow y hx.le]
  refine ⟨h1, h2, ?_⟩
  have hg : 0 ≤ cayleyCoherence x y := by
    rw [cayleyCoherence]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith)
  rw [h2, show 1 - cayleyContrast x y ^ 2 = cayleyCoherence x y ^ 2 by linarith,
    Real.sqrt_sq hg]

/-- **(CCRHD.2).**  `√(105/8) [δ/√(1 - λ)] κ = √(105/8) δ(1 - δ²)`: the singular factor cancels one
half-power of the cubic coherence. -/
theorem hodgeCollisionAmplitude_eq_transgression {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt (105 / 8) * (cayleyContrast x y / Real.sqrt (1 - cayleyContrast x y ^ 2) *
        wallCubicKernel x y)
      = hodgeCollisionAmplitude (cayleyContrast x y) := by
  obtain ⟨-, -, h3⟩ := cayley_pair_identities hx hy
  have hmem := cayleyContrast_mem_Ioo hx hy
  have hpos : 0 < 1 - cayleyContrast x y ^ 2 := by nlinarith [hmem.1, hmem.2]
  have hs : 0 < Real.sqrt (1 - cayleyContrast x y ^ 2) := Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have key : cayleyContrast x y / Real.sqrt (1 - cayleyContrast x y ^ 2) *
      Real.sqrt (1 - cayleyContrast x y ^ 2) ^ 3
      = cayleyContrast x y * Real.sqrt (1 - cayleyContrast x y ^ 2) ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_iff hs.ne']
    ring
  rw [h3, key, hsq, hodgeCollisionAmplitude]

/-- **Theorem CCRHD-A, integral form.**  `∬ Ω_H² F(λ) dμ dμ = ∫ F dBeta(3/2, 3)` for every
bounded measurable `F`. -/
theorem integral_hodgeCollision_sq_mul {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ a ∈ Ico (0 : ℝ) 1, |F a| ≤ C) :
    ∫ z, hodgeCollisionAmplitude (cayleyContrast z.1 z.2) ^ 2 * F (cayleyContrast z.1 z.2 ^ 2)
        ∂((expMeasure 1).prod (expMeasure 1))
      = ∫ a, F a ∂phaseBetaLaw := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 ⟨le_rfl, zero_lt_one⟩)
  have hφ : Measurable fun v => hodgeCollisionAmplitude v ^ 2 * F (v ^ 2) := by
    unfold hodgeCollisionAmplitude
    fun_prop
  have hbound : ∀ v ∈ Ioo (-1 : ℝ) 1, |hodgeCollisionAmplitude v ^ 2 * F (v ^ 2)| ≤ 105 / 8 * C :=
    fun v hv => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (hodgeCollisionAmplitude_sq_le hv)
        (hC _ ⟨sq_nonneg v, by nlinarith [hv.1, hv.2]⟩) (abs_nonneg _) (by norm_num)
  have hi : IntegrableOn (fun v => hodgeCollisionAmplitude v ^ 2 * F (v ^ 2)) (Ioo (-1) 1) :=
    (integrable_const (105 / 8 * C)).mono' hφ.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo fun v hv => by
        rw [Real.norm_eq_abs]; exact hbound v hv)
  rw [integral_cayleyContrast_prod hφ hbound,
    integral_Ioo_of_even hi fun v => by rw [hodgeCollisionAmplitude_neg, neg_sq, neg_sq],
    integral_phaseBetaLaw, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioo_comp_sq (fun a => phaseBetaDensity a * F a)]
  simp_rw [hodgeCollisionAmplitude_sq]
  rw [← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  simp only [phaseBetaDensity]
  rw [Real.sqrt_sq hv.1.le]
  ring

/-- **Theorem CCRHD-A.**  `∬ Ω_H² dμ dμ = 1`. -/
theorem integral_hodgeCollision_sq :
    ∫ z, hodgeCollisionAmplitude (cayleyContrast z.1 z.2) ^ 2
        ∂((expMeasure 1).prod (expMeasure 1)) = 1 := by
  have h := integral_hodgeCollision_sq_mul (F := fun _ => (1 : ℝ)) measurable_const
    (C := 1) (fun _ _ => by norm_num)
  simp only [mul_one, integral_const, smul_eq_mul] at h
  rw [h, probReal_univ]

/-- **Theorem CCRHD-A, law form.**  The contrast square `λ` has law `Beta(3/2, 3)` under
`Ω_H² μ⊗μ`. -/
theorem map_hodgeCollision_eq_phaseBetaLaw :
    Measure.map (fun z : ℝ × ℝ => cayleyContrast z.1 z.2 ^ 2)
      (((expMeasure 1).prod (expMeasure 1)).withDensity fun z =>
        ENNReal.ofReal (hodgeCollisionAmplitude (cayleyContrast z.1 z.2) ^ 2))
      = phaseBetaLaw := by
  have hlam : Measurable fun z : ℝ × ℝ => cayleyContrast z.1 z.2 ^ 2 :=
    measurable_cayleyContrast.pow_const 2
  have hA : Measurable fun z : ℝ × ℝ => hodgeCollisionAmplitude (cayleyContrast z.1 z.2) ^ 2 := by
    unfold hodgeCollisionAmplitude
    exact (by fun_prop : Measurable fun v : ℝ => (Real.sqrt (105 / 8) * (v * (1 - v ^ 2))) ^ 2).comp
      measurable_cayleyContrast
  ext s hs
  rw [Measure.map_apply hlam hs, withDensity_apply _ (hlam hs)]
  have hF : Measurable (s.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hs
  have h := integral_hodgeCollision_sq_mul hF (C := 1) fun a _ => by
    by_cases ha : a ∈ s <;> simp [ha]
  have hint : Integrable (fun z : ℝ × ℝ => hodgeCollisionAmplitude (cayleyContrast z.1 z.2) ^ 2 *
      s.indicator (fun _ => (1 : ℝ)) (cayleyContrast z.1 z.2 ^ 2))
      ((expMeasure 1).prod (expMeasure 1)) := by
    refine (integrable_const (105 / 8 : ℝ)).mono' (hA.mul (hF.comp hlam)).aestronglyMeasurable ?_
    filter_upwards [ae_pos_expPair] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    refine (mul_le_of_le_one_right (sq_nonneg _) ?_).trans
      (hodgeCollisionAmplitude_sq_le (cayleyContrast_mem_Ioo hz.1 hz.2))
    by_cases ha : cayleyContrast z.1 z.2 ^ 2 ∈ s <;> simp [ha]
  have hL := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => by
    exact mul_nonneg (sq_nonneg _) (by by_cases ha : cayleyContrast z.1 z.2 ^ 2 ∈ s <;> simp [ha]))
  have hR : ∫ a, s.indicator (fun _ => (1 : ℝ)) a ∂phaseBetaLaw = phaseBetaLaw.real s := by
    rw [integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one]
  rw [h, hR, ofReal_measureReal (measure_ne_top _ _)] at hL
  rw [hL, ← lintegral_indicator (hlam hs)]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ (fun z : ℝ × ℝ => cayleyContrast z.1 z.2 ^ 2) ⁻¹' s
  · rw [indicator_of_mem hz, indicator_of_mem (show cayleyContrast z.1 z.2 ^ 2 ∈ s from hz),
      mul_one]
  · rw [indicator_of_notMem hz,
      indicator_of_notMem (show cayleyContrast z.1 z.2 ^ 2 ∉ s from hz), mul_zero,
      ENNReal.ofReal_zero]

/-! ## The raw cubic law and its size bias -/

/-- The `Beta(1/2, 4)` density `(35/32) a^{-1/2}(1 - a)³` on `(0, 1)`. -/
def cubicContrastDensity (a : ℝ) : ℝ := 35 / 32 * ((1 - a) ^ 3 / Real.sqrt a)

/-- `∫₀¹ ρ(a) F(a) da = (35/16) ∫₀¹ (1 - v²)³ F(v²) dv` for the `Beta(1/2, 4)` density `ρ`. -/
theorem integral_cubicContrastDensity_mul (F : ℝ → ℝ) :
    ∫ a in Ioo (0 : ℝ) 1, cubicContrastDensity a * F a
      = 35 / 16 * ∫ v in Ioo (0 : ℝ) 1, (1 - v ^ 2) ^ 3 * F (v ^ 2) := by
  rw [integral_Ioo_comp_sq, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  rw [cubicContrastDensity, Real.sqrt_sq hv.1.le]
  have hv0 : v ≠ 0 := hv.1.ne'
  field_simp
  ring

theorem integral_cubicContrastDensity : ∫ a in Ioo (0 : ℝ) 1, cubicContrastDensity a = 1 := by
  have h := integral_cubicContrastDensity_mul (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have h0 := integral_pow_mul_one_sub_sq_cube 0
  simp only [mul_zero, pow_zero, one_mul, Nat.cast_zero] at h0
  rw [h0]
  norm_num

/-- **(CCRHD.4), raw law.**  `∬ κ² F(λ) dμ dμ = (16/35) ∫₀¹ F dBeta(1/2, 4)`. -/
theorem integral_wallCubicKernel_sq_mul {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ a ∈ Ico (0 : ℝ) 1, |F a| ≤ C) :
    ∫ z, wallCubicKernel z.1 z.2 ^ 2 * F (cayleyContrast z.1 z.2 ^ 2)
        ∂((expMeasure 1).prod (expMeasure 1))
      = 16 / 35 * ∫ a in Ioo (0 : ℝ) 1, cubicContrastDensity a * F a := by
  have hpt : (fun z : ℝ × ℝ => wallCubicKernel z.1 z.2 ^ 2 * F (cayleyContrast z.1 z.2 ^ 2))
      =ᵐ[(expMeasure 1).prod (expMeasure 1)]
        fun z => (1 - cayleyContrast z.1 z.2 ^ 2) ^ 3 * F (cayleyContrast z.1 z.2 ^ 2) := by
    filter_upwards [ae_pos_expPair] with z hz
    obtain ⟨-, -, h3⟩ := cayley_pair_identities hz.1 hz.2
    have hmem := cayleyContrast_mem_Ioo hz.1 hz.2
    rw [h3, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul,
      Real.sq_sqrt (by nlinarith [hmem.1, hmem.2])]
  have hφ : Measurable fun v : ℝ => (1 - v ^ 2) ^ 3 * F (v ^ 2) := by fun_prop
  have hbound : ∀ v ∈ Ioo (-1 : ℝ) 1, |(1 - v ^ 2) ^ 3 * F (v ^ 2)| ≤ C := fun v hv => by
    have h0 : 0 ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
    have h1 : (1 - v ^ 2) ^ 3 ≤ 1 := pow_le_one₀ h0 (by nlinarith [sq_nonneg v])
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 3)]
    exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans
      (hC _ ⟨sq_nonneg v, by nlinarith [hv.1, hv.2]⟩)
  have hi : IntegrableOn (fun v : ℝ => (1 - v ^ 2) ^ 3 * F (v ^ 2)) (Ioo (-1) 1) :=
    (integrable_const C).mono' hφ.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo fun v hv => by
        rw [Real.norm_eq_abs]; exact hbound v hv)
  rw [integral_congr_ae hpt,
    integral_cayleyContrast_prod (φ := fun v => (1 - v ^ 2) ^ 3 * F (v ^ 2)) hφ hbound,
    integral_Ioo_of_even hi fun v => by simp only [neg_sq],
    integral_cubicContrastDensity_mul]
  ring

/-- **(CCRHD.4), transgression.**  `Ω_H² = (105/8) [λ/(1 - λ)] κ²` on the open quadrant. -/
theorem hodgeCollisionAmplitude_sq_eq_sizeBias {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hodgeCollisionAmplitude (cayleyContrast x y) ^ 2
      = 105 / 8 * (cayleyContrast x y ^ 2 / (1 - cayleyContrast x y ^ 2) *
          wallCubicKernel x y ^ 2) := by
  obtain ⟨-, -, h3⟩ := cayley_pair_identities hx hy
  have hmem := cayleyContrast_mem_Ioo hx hy
  have hpos : 0 < 1 - cayleyContrast x y ^ 2 := by nlinarith [hmem.1, hmem.2]
  rw [h3, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hpos.le,
    hodgeCollisionAmplitude_sq]
  field_simp

/-- **(CCRHD.4), size bias.**  `Beta(3/2, 3)` density `= 6 a/(1 - a) ×` `Beta(1/2, 4)` density. -/
theorem phaseBetaDensity_eq_sizeBias {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    phaseBetaDensity a = 6 * (a / (1 - a)) * cubicContrastDensity a := by
  have h1 : 1 - a ≠ 0 := (sub_pos.mpr ha.2).ne'
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha.1).ne'
  rw [phaseBetaDensity, cubicContrastDensity]
  have hr : 6 * (a / (1 - a)) * (35 / 32 * ((1 - a) ^ 3 / Real.sqrt a))
      = 105 / 16 * (a / Real.sqrt a * (1 - a) ^ 2) := by
    field_simp
    ring
  rw [hr, Real.div_sqrt]

end GaloisForLFunctions.HTGeometry
