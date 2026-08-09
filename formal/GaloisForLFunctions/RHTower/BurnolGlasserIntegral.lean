import Mathlib

/-!
# The Glasser evaluation of the square-root subordination integral

`∫₀^∞ exp(-t² - b²/t²) dt = (√π/2) e^{-2b}` for `b ≥ 0`.

Two changes of variables reduce it to the Gaussian integral.  The reciprocal map `t ↦ b/t` is an
involution of the positive ray with Jacobian `b/t²`, so the two halves

`S = ∫₀^∞ e^{-t²-b²/t²} dt`,   `T = ∫₀^∞ (b/t²) e^{-t²-b²/t²} dt`

are equal.  The Glasser map `t ↦ t - b/t` carries the positive ray onto the whole line with
Jacobian `1 + b/t²` and satisfies `(t - b/t)² + 2b = t² + b²/t²`, so `S + T = √π e^{-2b}`.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## The reciprocal involution -/

theorem burnolReciprocal_image {b : ℝ} (hb : 0 < b) :
    (fun t : ℝ => b / t) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact div_pos hb ht
  · intro hu
    exact ⟨b / u, div_pos hb hu, by field_simp⟩

theorem hasDerivAt_burnolConstDiv {b t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => b / s) (-(b / t ^ 2)) t := by
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht
  refine (hinv.const_mul b).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · rw [div_eq_mul_inv]
    ring
  · filter_upwards with s
    rw [div_eq_mul_inv]

theorem hasDerivWithinAt_burnolReciprocal {b t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s : ℝ => b / s) (-(b / t ^ 2)) (Ioi 0) t :=
  (hasDerivAt_burnolConstDiv (ne_of_gt ht)).hasDerivWithinAt

theorem burnolReciprocal_injOn {b : ℝ} (hb : 0 < b) :
    Set.InjOn (fun t : ℝ => b / t) (Ioi 0) := by
  have hanti : StrictAntiOn (fun t : ℝ => b / t) (Ioi 0) := by
    intro x hx y hy hxy
    exact div_lt_div_of_pos_left hb hx hxy
  exact hanti.injOn

/-! ## The Glasser map -/

theorem burnolGlasser_image {b : ℝ} (hb : 0 < b) :
    (fun t : ℝ => t - b / t) '' Ioi 0 = Set.univ := by
  ext v
  refine ⟨fun _ => Set.mem_univ v, fun _ => ?_⟩
  have hD : (0 : ℝ) < v ^ 2 + 4 * b := by positivity
  set r : ℝ := Real.sqrt (v ^ 2 + 4 * b) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hD
  have hr2 : r ^ 2 = v ^ 2 + 4 * b := Real.sq_sqrt hD.le
  have hrv : |v| < r := by
    have h1 : |v| = Real.sqrt (v ^ 2) := (Real.sqrt_sq_eq_abs v).symm
    rw [h1, hr]
    exact Real.sqrt_lt_sqrt (sq_nonneg v) (by linarith)
  have htpos : (0 : ℝ) < (v + r) / 2 := by
    have : -r < v := by
      rcases abs_lt.mp hrv with ⟨h1, _⟩
      linarith
    linarith
  refine ⟨(v + r) / 2, htpos, ?_⟩
  have hb2 : b = ((v + r) / 2) ^ 2 - v * ((v + r) / 2) := by nlinarith [hr2]
  have hvrpos : (0 : ℝ) < v + r := by linarith
  show (v + r) / 2 - b / ((v + r) / 2) = v
  rw [hb2]
  field_simp
  ring

theorem hasDerivWithinAt_burnolGlasser {b t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s : ℝ => s - b / s) (1 + b / t ^ 2) (Ioi 0) t := by
  have h1 : HasDerivAt (fun s : ℝ => b / s) (-(b / t ^ 2)) t :=
    hasDerivAt_burnolConstDiv (ne_of_gt ht)
  have h : HasDerivAt (fun s : ℝ => s - b / s) (1 + b / t ^ 2) t := by
    refine ((hasDerivAt_id t).sub h1).congr_deriv ?_
    ring
  exact h.hasDerivWithinAt

theorem burnolGlasser_strictMonoOn {b : ℝ} (hb : 0 < b) :
    StrictMonoOn (fun t : ℝ => t - b / t) (Ioi 0) := by
  intro x hx y hy hxy
  have hdiv : b / y < b / x := div_lt_div_of_pos_left hb hx hxy
  simp only
  linarith

theorem burnolGlasser_injOn {b : ℝ} (hb : 0 < b) :
    Set.InjOn (fun t : ℝ => t - b / t) (Ioi 0) :=
  (burnolGlasser_strictMonoOn hb).injOn

theorem burnolGlasser_sq {b t : ℝ} (ht : t ≠ 0) :
    (t - b / t) ^ 2 + 2 * b = t ^ 2 + b ^ 2 / t ^ 2 := by
  field_simp
  ring

/-! ## The evaluation -/

/-- The square-root subordination integrand. -/
def burnolGlasserIntegrand (b t : ℝ) : ℝ := Real.exp (-(t ^ 2) - b ^ 2 / t ^ 2)

theorem burnolGlasserIntegrand_pos (b t : ℝ) : 0 < burnolGlasserIntegrand b t :=
  Real.exp_pos _

theorem continuousOn_burnolGlasserIntegrand (b : ℝ) :
    ContinuousOn (burnolGlasserIntegrand b) (Ioi 0) := by
  refine Real.continuous_exp.comp_continuousOn ?_
  refine ContinuousOn.sub ((continuous_pow 2).continuousOn.neg) ?_
  exact continuousOn_const.div (continuous_pow 2).continuousOn
    (fun t ht => pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < t from ht)))

theorem integrableOn_burnolGlasserIntegrand (b : ℝ) :
    IntegrableOn (burnolGlasserIntegrand b) (Ioi 0) volume := by
  have hmeas : AEStronglyMeasurable (burnolGlasserIntegrand b) (volume.restrict (Ioi 0)) :=
    (continuousOn_burnolGlasserIntegrand b).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos).restrict) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : (0 : ℝ) < t := ht
  rw [Real.norm_of_nonneg (burnolGlasserIntegrand_pos b t).le, burnolGlasserIntegrand]
  refine Real.exp_le_exp.mpr ?_
  have hnn : (0 : ℝ) ≤ b ^ 2 / t ^ 2 := by positivity
  nlinarith [hnn]

theorem burnolGlasserIntegrand_reciprocal {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    burnolGlasserIntegrand b (b / t) = burnolGlasserIntegrand b t := by
  rw [burnolGlasserIntegrand, burnolGlasserIntegrand]
  congr 1
  field_simp
  ring

/-- **The reciprocal involution equates the two halves.** -/
theorem burnolGlasser_reciprocal_integral {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), burnolGlasserIntegrand b t) =
      ∫ t in Ioi (0 : ℝ), (b / t ^ 2) * burnolGlasserIntegrand b t := by
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => b / t) (f' := fun t : ℝ => -(b / t ^ 2)) (s := Ioi (0 : ℝ))
    measurableSet_Ioi (fun t ht => hasDerivWithinAt_burnolReciprocal ht)
    (burnolReciprocal_injOn hb) (burnolGlasserIntegrand b)
  rw [burnolReciprocal_image hb] at hcov
  rw [hcov]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have htpos : (0 : ℝ) < t := ht
  rw [smul_eq_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < b / t ^ 2),
    burnolGlasserIntegrand_reciprocal hb htpos]

theorem integrableOn_burnolGlasserWeighted {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (b / t ^ 2) * burnolGlasserIntegrand b t) (Ioi 0) volume := by
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun t : ℝ => b / t) (f' := fun t : ℝ => -(b / t ^ 2)) (s := Ioi (0 : ℝ))
    measurableSet_Ioi (fun t ht => hasDerivWithinAt_burnolReciprocal ht)
    (burnolReciprocal_injOn hb) (burnolGlasserIntegrand b)
  rw [burnolReciprocal_image hb] at hiff
  have h := hiff.mp (integrableOn_burnolGlasserIntegrand b)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have htpos : (0 : ℝ) < t := ht
  show |(-(b / t ^ 2))| • burnolGlasserIntegrand b (b / t) =
    b / t ^ 2 * burnolGlasserIntegrand b t
  rw [smul_eq_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < b / t ^ 2),
    burnolGlasserIntegrand_reciprocal hb htpos]

/-- **The Glasser evaluation.** -/
theorem burnolGlasser_integral {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), burnolGlasserIntegrand b t) =
      Real.sqrt π / 2 * Real.exp (-(2 * b)) := by
  have hgauss : (∫ v : ℝ, Real.exp (-(v ^ 2) - 2 * b)) = Real.sqrt π * Real.exp (-(2 * b)) := by
    have hsplit : ∀ v : ℝ, Real.exp (-(v ^ 2) - 2 * b) =
        Real.exp (-(2 * b)) * Real.exp (-1 * v ^ 2) := by
      intro v
      rw [← Real.exp_add]
      congr 1
      ring
    rw [funext hsplit, MeasureTheory.integral_const_mul, integral_gaussian]
    rw [div_one]
    ring
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => t - b / t) (f' := fun t : ℝ => 1 + b / t ^ 2) (s := Ioi (0 : ℝ))
    measurableSet_Ioi (fun t ht => hasDerivWithinAt_burnolGlasser ht)
    (burnolGlasser_injOn hb) (fun v : ℝ => Real.exp (-(v ^ 2) - 2 * b))
  rw [burnolGlasser_image hb, Measure.restrict_univ] at hcov
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      |1 + b / t ^ 2| • Real.exp (-((t - b / t) ^ 2) - 2 * b) =
        burnolGlasserIntegrand b t + (b / t ^ 2) * burnolGlasserIntegrand b t := by
    intro t ht
    have htpos : (0 : ℝ) < t := ht
    have hexp : -((t - b / t) ^ 2) - 2 * b = -(t ^ 2) - b ^ 2 / t ^ 2 := by
      have := burnolGlasser_sq (b := b) (ne_of_gt htpos)
      linarith
    rw [smul_eq_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + b / t ^ 2), hexp,
      ← burnolGlasserIntegrand]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
    integral_add (integrableOn_burnolGlasserIntegrand b) (integrableOn_burnolGlasserWeighted hb),
    ← burnolGlasser_reciprocal_integral hb] at hcov
  rw [hgauss] at hcov
  linarith [hcov]

/-! ## The square-root subordination identity -/

/-- The subordination integrand `s^{-3/2} e^{-y²/(4s)} e^{-sλ}`. -/
def burnolSubordinationIntegrand (y lam s : ℝ) : ℝ :=
  s ^ (-(3 : ℝ) / 2) * Real.exp (-(y ^ 2 / (4 * s))) * Real.exp (-(s * lam))

theorem burnolRpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 : ℝ) / 2) = ((Real.sqrt x)⁻¹) ^ 3 := by
  have hs : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  have h1 : ((Real.sqrt x)⁻¹) ^ 3 = ((Real.sqrt x) ^ 3)⁻¹ := by rw [inv_pow]
  have h2 : (Real.sqrt x) ^ 3 = x ^ ((3 : ℝ) / 2) := by
    rw [hs, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) 3, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  rw [h1, h2, ← Real.rpow_neg hx.le]
  congr 1
  ring

theorem burnolSubordinationScale_image {y : ℝ} (hy : 0 < y) :
    (fun t : ℝ => y ^ 2 / (4 * t ^ 2)) '' Ioi 0 = Ioi 0 := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htpos : (0 : ℝ) < t := ht
    show (0 : ℝ) < y ^ 2 / (4 * t ^ 2)
    positivity
  · intro hs
    have hspos : (0 : ℝ) < s := hs
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hspos.le
    have hsqrtpos : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hspos
    refine ⟨y / (2 * Real.sqrt s), ?_, ?_⟩
    · show (0 : ℝ) < y / (2 * Real.sqrt s)
      positivity
    show y ^ 2 / (4 * (y / (2 * Real.sqrt s)) ^ 2) = s
    rw [div_pow]
    field_simp
    linarith [hsq]

theorem burnolSubordinationScale_injOn {y : ℝ} (hy : 0 < y) :
    Set.InjOn (fun t : ℝ => y ^ 2 / (4 * t ^ 2)) (Ioi 0) := by
  have hanti : StrictAntiOn (fun t : ℝ => y ^ 2 / (4 * t ^ 2)) (Ioi 0) := by
    intro u hu v hv huv
    have hupos : (0 : ℝ) < u := hu
    have hvpos : (0 : ℝ) < v := hv
    have hlt : 4 * u ^ 2 < 4 * v ^ 2 := by nlinarith
    exact div_lt_div_of_pos_left (by positivity) (by positivity) hlt
  exact hanti.injOn

theorem hasDerivWithinAt_burnolSubordinationScale {y t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s : ℝ => y ^ 2 / (4 * s ^ 2))
      (-(y ^ 2 / (2 * t ^ 3))) (Ioi 0) t := by
  have hden : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (4 * (2 * t)) t :=
    ((hasDerivAt_pow 2 t).const_mul (4 : ℝ)).congr_deriv (by ring)
  have hne : (4 : ℝ) * t ^ 2 ≠ 0 := by positivity
  have h := (hasDerivAt_const t (y ^ 2)).div hden hne
  refine (h.congr_deriv ?_).hasDerivWithinAt
  field_simp
  ring

/-- **The square-root subordination identity.** -/
theorem burnolPoissonSubordination {y lam : ℝ} (hy : 0 < y) (hlam : 0 < lam) :
    Real.exp (-(y * Real.sqrt lam)) =
      y / (2 * Real.sqrt π) * ∫ s in Ioi (0 : ℝ), burnolSubordinationIntegrand y lam s := by
  have hpi : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  set b : ℝ := y * Real.sqrt lam / 2 with hbdef
  have hbpos : 0 < b := by
    have : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    rw [hbdef]
    positivity
  have hb2 : b ^ 2 = y ^ 2 * lam / 4 := by
    rw [hbdef]
    have hsq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    field_simp
    linarith [hsq]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => y ^ 2 / (4 * t ^ 2)) (f' := fun t : ℝ => -(y ^ 2 / (2 * t ^ 3)))
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t ht => hasDerivWithinAt_burnolSubordinationScale ht)
    (burnolSubordinationScale_injOn hy) (burnolSubordinationIntegrand y lam)
  rw [burnolSubordinationScale_image hy] at hcov
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      |(-(y ^ 2 / (2 * t ^ 3)))| • burnolSubordinationIntegrand y lam (y ^ 2 / (4 * t ^ 2)) =
        (4 / y) * burnolGlasserIntegrand b t := by
    intro t ht
    have htpos : (0 : ℝ) < t := ht
    have hxpos : (0 : ℝ) < y ^ 2 / (4 * t ^ 2) := by positivity
    have hsqrtx : Real.sqrt (y ^ 2 / (4 * t ^ 2)) = y / (2 * t) := by
      have hrw : y ^ 2 / (4 * t ^ 2) = (y / (2 * t)) ^ 2 := by
        field_simp
        ring
      rw [hrw, Real.sqrt_sq (by positivity)]
    have hpow : (y ^ 2 / (4 * t ^ 2)) ^ (-(3 : ℝ) / 2) = 8 * t ^ 3 / y ^ 3 := by
      rw [burnolRpow_neg_three_halves hxpos, hsqrtx]
      field_simp
      ring
    have hexp1 : -(y ^ 2 / (4 * (y ^ 2 / (4 * t ^ 2)))) = -(t ^ 2) := by
      field_simp
    have hexp2 : -(y ^ 2 / (4 * t ^ 2) * lam) = -(b ^ 2 / t ^ 2) := by
      rw [hb2]
      field_simp
    rw [smul_eq_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < y ^ 2 / (2 * t ^ 3)),
      burnolSubordinationIntegrand, hpow, hexp1, hexp2, burnolGlasserIntegrand,
      show (-(t ^ 2) - b ^ 2 / t ^ 2 : ℝ) = -(t ^ 2) + -(b ^ 2 / t ^ 2) by ring, Real.exp_add]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, MeasureTheory.integral_const_mul,
    burnolGlasser_integral hbpos] at hcov
  rw [hcov, hbdef]
  have hyne : y ≠ 0 := ne_of_gt hy
  have hpine : Real.sqrt π ≠ 0 := ne_of_gt hpi
  rw [show (2 : ℝ) * (y * Real.sqrt lam / 2) = y * Real.sqrt lam by ring]
  field_simp
  ring

end RHTower
