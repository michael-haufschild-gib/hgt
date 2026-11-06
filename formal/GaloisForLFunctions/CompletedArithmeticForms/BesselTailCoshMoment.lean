import GaloisForLFunctions.CompletedArithmeticForms.BesselOrderCoshMoment
import GaloisForLFunctions.CompletedArithmeticForms.BesselWeightedTail

/-!
# Positive frequency averages of weighted Bessel tails

A separable exponential majorant justifies frequency/radius interchange.
Cosh averaging converts the actual first-atom tail into an explicit real
exponential profile.
-/

set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open RHTower
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

private theorem stronglyMeasurable_bessel_radial_order :
    StronglyMeasurable (fun z : ℝ × ℝ =>
      modifiedBesselKOrder (2 * z.1) ((z.2 : ℂ) * I)) := by
  have hm : StronglyMeasurable (fun z : (ℝ × ℝ) × ℝ =>
      besselOrderKernel (2 * z.1.1) ((z.1.2 : ℂ) * I) z.2) := by
    apply Continuous.stronglyMeasurable
    unfold besselOrderKernel
    fun_prop
  exact hm.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

private def radialOrderCoshCost (θ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-Real.cos θ * Real.cosh t)

private theorem radialOrderCoshCost_nonneg (θ : ℝ) : 0 ≤ radialOrderCoshCost θ :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- A separable exponential majorant retains decay in both argument and order. -/
private theorem norm_cosh_bessel_radial_le {u η θ : ℝ}
    (hu : 1 ≤ u) (hη : 0 ≤ η) (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi / 2) (τ : ℝ) :
    ‖Real.cosh (η * τ) * (modifiedBesselKOrder (2 * u) ((τ : ℂ) * I)).re‖ ≤
      radialOrderCoshCost θ * Real.exp (-Real.cos θ * u) *
        Real.exp (-(θ - η) * |τ|) := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have he : modifiedBesselKOrder (2 * u) (((|τ| : ℝ) : ℂ) * I) =
      modifiedBesselKOrder (2 * u) ((τ : ℂ) * I) := by
    by_cases ht : 0 ≤ τ
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), Complex.ofReal_neg, neg_mul,
        modifiedBesselKOrder_neg]
  have hB := norm_modifiedBesselKOrder_I_mul_le_shifted (by positivity : 0 < 2 * u)
    |τ| hθ0 hθ
  rw [he] at hB
  have hI : (∫ t in Ioi (0 : ℝ), Real.exp (-(2 * u * Real.cos θ) * Real.cosh t)) ≤
      Real.exp (-Real.cos θ * u) * radialOrderCoshCost θ := by
    rw [radialOrderCoshCost, ← integral_const_mul]
    apply setIntegral_mono_on
      (integrableOn_exp_neg_mul_cosh_Ioi (by positivity))
      ((integrableOn_exp_neg_mul_cosh_Ioi hc).const_mul _) measurableSet_Ioi
    intro t ht
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_nonneg (sub_nonneg.mpr hu) (Real.cosh_pos t).le
    have h2 := mul_nonneg hu0.le (sub_nonneg.mpr (Real.one_le_cosh t))
    have h3 := mul_nonneg hc.le (add_nonneg h1 h2)
    nlinarith only [h3]
  have hC : Real.cosh (η * τ) ≤ Real.exp (η * |τ|) := by
    rw [Real.cosh_eq]
    have h1 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self τ) hη)
    have h2 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (neg_le_abs τ) hη)
    rw [mul_neg] at h2
    linarith only [h1, h2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.cosh_pos _)]
  calc
    _ ≤ Real.exp (η * |τ|) *
        (Real.exp (-|τ| * θ) *
          (Real.exp (-Real.cos θ * u) * radialOrderCoshCost θ)) :=
      mul_le_mul hC ((Complex.abs_re_le_norm _).trans
        (hB.trans (mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le)))
        (abs_nonneg _) (Real.exp_pos _).le
    _ = (Real.exp (η * |τ|) * Real.exp (-|τ| * θ)) *
        Real.exp (-Real.cos θ * u) * radialOrderCoshCost θ := by ring
    _ = _ := by
      have he : Real.exp (η * |τ|) * Real.exp (-|τ| * θ) =
          Real.exp (-(θ - η) * |τ|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring

private theorem integrable_joint_cosh_bessel_power {p q η θ : ℝ}
    (hp : -1 < p) (hq : 1 ≤ q) (hη : 0 ≤ η) (hηθ : η < θ)
    (hθ : θ < Real.pi / 2) :
    Integrable (fun z : ℝ × ℝ => z.1 ^ p *
      (Real.cosh (η * z.2) * (modifiedBesselKOrder (2 * z.1) ((z.2 : ℂ) * I)).re))
      ((volume.restrict (Ioi q)).prod volume) := by
  have hθ0 : 0 ≤ θ := hη.trans hηθ.le
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hU : IntegrableOn (fun u : ℝ => u ^ p * Real.exp (-Real.cos θ * u)) (Ioi q) := by
    have ht := integrableOn_rpow_mul_exp_neg_mul_rpow hp (show (1 : ℝ) ≤ 1 from le_rfl) hc
    simp only [Real.rpow_one] at ht
    exact ht.mono_set (fun u hu => zero_lt_one.trans_le (hq.trans hu.le))
  have hT : Integrable (fun τ : ℝ => Real.exp (-(θ - η) * |τ|)) := by
    simpa only [neg_mul] using integrable_exp_neg_mul_abs' (sub_pos.mpr hηθ)
  have hm := ((hU.const_mul (radialOrderCoshCost θ)).mul_prod hT)
  have hk := stronglyMeasurable_bessel_radial_order
  have hmeas := (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1 ^ p)).mul
    ((by fun_prop : Measurable (fun z : ℝ × ℝ => Real.cosh (η * z.2))).mul
      (Complex.measurable_re.comp hk.measurable))
  apply hm.mono' hmeas.aestronglyMeasurable
  have hqae : ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioi q)).prod volume), q < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hqae] with z hz
  have hu : 1 ≤ z.1 := hq.trans hz.le
  have hun : 0 ≤ z.1 ^ p := Real.rpow_nonneg (zero_le_one.trans hu) _
  change ‖z.1 ^ p * (Real.cosh (η * z.2) *
    (modifiedBesselKOrder (2 * z.1) ((z.2 : ℂ) * I)).re)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hun]
  have hb := mul_le_mul_of_nonneg_left
    (norm_cosh_bessel_radial_le hu hη hθ0 hθ z.2) hun
  convert hb using 1 <;> ring

private theorem cosh_mul_besselPowerTail_eq_integral (p q η τ : ℝ) :
    Real.cosh (η * τ) * besselPowerTail p (τ / 2) q =
      ∫ u in Ioi q, u ^ p *
        (Real.cosh (η * τ) * (modifiedBesselKOrder (2 * u) ((τ : ℂ) * I)).re) := by
  rw [besselPowerTail, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [besselRadialValue, show 2 * (τ / 2) = τ by ring]
  ring

/-- Every subcritical cosh moment of a power tail converges absolutely. -/
theorem integrable_cosh_besselPowerTail {p q η : ℝ}
    (hp : -1 < p) (hq : 1 ≤ q) (hη0 : 0 ≤ η) (hη : η < Real.pi / 2) :
    Integrable (fun τ : ℝ => Real.cosh (η * τ) * besselPowerTail p (τ / 2) q) := by
  let θ : ℝ := (η + Real.pi / 2) / 2
  have hηθ : η < θ := by dsimp only [θ]; linarith only [hη]
  have hθ : θ < Real.pi / 2 := by dsimp only [θ]; linarith only [hη]
  have hF := integrable_joint_cosh_bessel_power hp hq hη0 hηθ hθ
  have hi := hF.integral_prod_right
  exact hi.congr (Filter.Eventually.of_forall fun τ =>
    (cosh_mul_besselPowerTail_eq_integral p q η τ).symm)

/-- Frequency averaging changes the complete power tail into an ordinary exponential tail. -/
theorem integral_cosh_besselPowerTail {p q η : ℝ}
    (hp : -1 < p) (hq : 1 ≤ q) (hη0 : 0 ≤ η) (hη : η < Real.pi / 2) :
    (∫ τ : ℝ, Real.cosh (η * τ) * besselPowerTail p (τ / 2) q) =
      Real.pi * ∫ u in Ioi q, u ^ p * Real.exp (-2 * Real.cos η * u) := by
  let θ : ℝ := (η + Real.pi / 2) / 2
  have hηθ : η < θ := by dsimp only [θ]; linarith only [hη]
  have hθ : θ < Real.pi / 2 := by dsimp only [θ]; linarith only [hη]
  have hF := integrable_joint_cosh_bessel_power hp hq hη0 hηθ hθ
  simp_rw [cosh_mul_besselPowerTail_eq_integral]
  rw [← integral_integral_swap hF, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change q < u at hu
  have hu0 : 0 < 2 * u := by linarith only [hq, hu]
  change (∫ y : ℝ, u ^ p * (Real.cosh (η * y) *
    (modifiedBesselKOrder (2 * u) ((y : ℂ) * I)).re)) =
    Real.pi * (u ^ p * Real.exp (-2 * Real.cos η * u))
  rw [integral_const_mul, integral_cosh_besselOrder hu0 hη0 hη]
  rw [show -(2 * u) * Real.cos η = -2 * Real.cos η * u by ring]
  ring

/-- The real exponential profile produced by positive frequency averaging. -/
def besselFirstAtomExponentialTail (c q : ℝ) : ℝ :=
  4 * (∫ u in Ioi q, u ^ (7 / 2 : ℝ) * Real.exp (-2 * c * u)) -
    6 * (∫ u in Ioi q, u ^ (3 / 2 : ℝ) * Real.exp (-2 * c * u)) -
    6 * q ^ (5 / 2 : ℝ) * Real.exp (-2 * c * q)

/-- The complete signed first-atom density has every subcritical cosh moment. -/
theorem integrable_cosh_besselFirstAtomTailDensity {q η : ℝ}
    (hq : 1 ≤ q) (hη0 : 0 ≤ η) (hη : η < Real.pi / 2) :
    Integrable (fun τ : ℝ => Real.cosh (η * τ) * besselFirstAtomTailDensity (τ / 2) q) := by
  have h7 := integrable_cosh_besselPowerTail (by norm_num : (-1 : ℝ) < 7 / 2) hq hη0 hη
  have h3 := integrable_cosh_besselPowerTail (by norm_num : (-1 : ℝ) < 3 / 2) hq hη0 hη
  have hK := integrable_cosh_besselOrder (by linarith only [hq] : 0 < 2 * q) hη0 hη
  apply (((h7.const_mul 4).sub (h3.const_mul 6)).sub
    (hK.const_mul (6 * q ^ (5 / 2 : ℝ)))).congr
  filter_upwards with τ
  simp only [Pi.sub_apply, besselFirstAtomTailDensity, besselRadialValue,
    show 2 * (τ / 2) = τ by ring]
  ring

/-- Positive frequency averaging removes all Bessel-order oscillation from the actual radial density. -/
theorem integral_cosh_besselFirstAtomTailDensity {q η : ℝ}
    (hq : 1 ≤ q) (hη0 : 0 ≤ η) (hη : η < Real.pi / 2) :
    (∫ τ : ℝ, Real.cosh (η * τ) * besselFirstAtomTailDensity (τ / 2) q) =
      Real.pi * besselFirstAtomExponentialTail (Real.cos η) q := by
  have h7 := integrable_cosh_besselPowerTail (by norm_num : (-1 : ℝ) < 7 / 2) hq hη0 hη
  have h3 := integrable_cosh_besselPowerTail (by norm_num : (-1 : ℝ) < 3 / 2) hq hη0 hη
  have hK := integrable_cosh_besselOrder (by linarith only [hq] : 0 < 2 * q) hη0 hη
  have he (τ : ℝ) : Real.cosh (η * τ) * besselFirstAtomTailDensity (τ / 2) q =
      4 * (Real.cosh (η * τ) * besselPowerTail (7 / 2) (τ / 2) q) -
        6 * (Real.cosh (η * τ) * besselPowerTail (3 / 2) (τ / 2) q) -
        (6 * q ^ (5 / 2 : ℝ)) *
          (Real.cosh (η * τ) * (modifiedBesselKOrder (2 * q) ((τ : ℂ) * I)).re) := by
    simp only [besselFirstAtomTailDensity, besselRadialValue, show 2 * (τ / 2) = τ by ring]
    ring
  simp_rw [he]
  have hsub := integral_sub ((h7.const_mul (4 : ℝ)).sub (h3.const_mul (6 : ℝ)))
    (hK.const_mul (6 * q ^ (5 / 2 : ℝ)))
  have hdiff := integral_sub (h7.const_mul (4 : ℝ)) (h3.const_mul (6 : ℝ))
  simp only [Pi.sub_apply] at hsub hdiff
  rw [hsub, hdiff,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cosh_besselPowerTail (by norm_num : (-1 : ℝ) < 7 / 2) hq hη0 hη,
    integral_cosh_besselPowerTail (by norm_num : (-1 : ℝ) < 3 / 2) hq hη0 hη,
    integral_cosh_besselOrder (by linarith only [hq] : 0 < 2 * q) hη0 hη]
  rw [show -(2 * q) * Real.cos η = -2 * Real.cos η * q by ring]
  unfold besselFirstAtomExponentialTail
  ring

end GaloisForLFunctions.CompletedArithmeticForms
