import GaloisForLFunctions.RHTower.BesselJZeroODE

/-!
# The Liouville–Green normal form of the order-zero Bessel equation

Bessel's equation `y'' + y'/u + y = 0` has a first-order term, which obstructs comparison with a
sinusoid.  The substitution `w = sqrt u * y` removes it exactly:

`w'' + (1 + 1/(4u²)) w = 0`.

So `w` solves a harmonic oscillator perturbed by `1/(4u²)`, which is integrable at infinity.  That is
the starting point of the sharp asymptotic `J_0(u) = sqrt(2/(pi u)) cos(u - pi/4) + O(u^{-3/2})`:
the leading cosine is the unperturbed solution and the perturbation is what the error term measures.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The normal-form solution `sqrt u * J_0(u)`. -/
def besselNormalForm (u : ℝ) : ℝ := Real.sqrt u * besselJ0 u

/-- Its derivative. -/
def besselNormalFormDeriv (u : ℝ) : ℝ :=
  besselJ0 u / (2 * Real.sqrt u) + Real.sqrt u * besselJ0Deriv u

/-- Its second derivative. -/
def besselNormalFormSecond (u : ℝ) : ℝ :=
  -(besselJ0 u / (4 * u * Real.sqrt u)) + besselJ0Deriv u / Real.sqrt u
    + Real.sqrt u * besselJ0SecondDeriv u

theorem hasDerivAt_besselNormalForm {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselNormalForm (besselNormalFormDeriv u) u := by
  have hne : u ≠ 0 := ne_of_gt hu
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt u)) u := Real.hasDerivAt_sqrt hne
  have h := hsq.mul (hasDerivAt_besselJ0 u)
  have hval : 1 / (2 * Real.sqrt u) * besselJ0 u + Real.sqrt u * besselJ0Deriv u
      = besselNormalFormDeriv u := by
    rw [besselNormalFormDeriv]
    ring
  rw [hval] at h
  exact h

theorem hasDerivAt_besselNormalFormDeriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselNormalFormDeriv (besselNormalFormSecond u) u := by
  have hne : u ≠ 0 := ne_of_gt hu
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt u)) u := Real.hasDerivAt_sqrt hne
  -- the first summand
  have hden : HasDerivAt (fun v : ℝ => 2 * Real.sqrt v) (2 * (1 / (2 * Real.sqrt u))) u :=
    hsq.const_mul 2
  have hdenne : 2 * Real.sqrt u ≠ 0 := by positivity
  have h1 : HasDerivAt (fun v : ℝ => besselJ0 v / (2 * Real.sqrt v))
      ((besselJ0Deriv u * (2 * Real.sqrt u)
        - besselJ0 u * (2 * (1 / (2 * Real.sqrt u)))) / (2 * Real.sqrt u) ^ (2 : ℕ)) u :=
    (hasDerivAt_besselJ0 u).div hden hdenne
  -- the second summand
  have h2 : HasDerivAt (fun v : ℝ => Real.sqrt v * besselJ0Deriv v)
      (1 / (2 * Real.sqrt u) * besselJ0Deriv u + Real.sqrt u * besselJ0SecondDeriv u) u :=
    hsq.mul (hasDerivAt_besselJ0Deriv u)
  have h := h1.add h2
  have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hval : (besselJ0Deriv u * (2 * Real.sqrt u)
        - besselJ0 u * (2 * (1 / (2 * Real.sqrt u)))) / (2 * Real.sqrt u) ^ (2 : ℕ)
      + (1 / (2 * Real.sqrt u) * besselJ0Deriv u + Real.sqrt u * besselJ0SecondDeriv u)
      = besselNormalFormSecond u := by
    rw [besselNormalFormSecond]
    field_simp
    linear_combination (4 * besselJ0 u) * hss
  rw [hval] at h
  exact h

/-- **The normal form.**  The first-order term is gone and the potential is `1 + 1/(4u²)`. -/
theorem besselNormalForm_ode {u : ℝ} (hu : 0 < u) :
    besselNormalFormSecond u + (1 + 1 / (4 * u ^ (2 : ℕ))) * besselNormalForm u = 0 := by
  have hne : u ≠ 0 := ne_of_gt hu
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hode := besselJ0_ode hne
  have hJ2 : besselJ0SecondDeriv u = -(besselJ0Deriv u / u) - besselJ0 u := by linarith [hode]
  rw [besselNormalFormSecond, besselNormalForm, hJ2]
  field_simp
  linear_combination (besselJ0 u - 4 * u * besselJ0Deriv u) * hss

/-- The oscillator energy of the normal form. -/
def besselEnergy (u : ℝ) : ℝ := besselNormalForm u ^ (2 : ℕ) + besselNormalFormDeriv u ^ (2 : ℕ)

theorem besselEnergy_nonneg (u : ℝ) : 0 ≤ besselEnergy u := by
  rw [besselEnergy]
  positivity

/-- **The energy is almost conserved.**  Its derivative is the perturbation `1/(4u²)` times a
product of the solution and its derivative -- there is no unperturbed contribution at all. -/
theorem hasDerivAt_besselEnergy {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselEnergy
      (-(2 * (1 / (4 * u ^ (2 : ℕ))) * (besselNormalForm u * besselNormalFormDeriv u))) u := by
  have hw := hasDerivAt_besselNormalForm hu
  have hw' := hasDerivAt_besselNormalFormDeriv hu
  have h1 : HasDerivAt (fun v : ℝ => besselNormalForm v ^ (2 : ℕ))
      (2 * besselNormalForm u * besselNormalFormDeriv u) u := by
    have h := hw.pow 2
    have hv : ((2 : ℕ) : ℝ) * besselNormalForm u ^ (2 - 1) * besselNormalFormDeriv u
        = 2 * besselNormalForm u * besselNormalFormDeriv u := by norm_num
    rw [hv] at h
    exact h
  have h2 : HasDerivAt (fun v : ℝ => besselNormalFormDeriv v ^ (2 : ℕ))
      (2 * besselNormalFormDeriv u * besselNormalFormSecond u) u := by
    have h := hw'.pow 2
    have hv : ((2 : ℕ) : ℝ) * besselNormalFormDeriv u ^ (2 - 1) * besselNormalFormSecond u
        = 2 * besselNormalFormDeriv u * besselNormalFormSecond u := by norm_num
    rw [hv] at h
    exact h
  have h := h1.add h2
  have hode := besselNormalForm_ode hu
  have hval : 2 * besselNormalForm u * besselNormalFormDeriv u
      + 2 * besselNormalFormDeriv u * besselNormalFormSecond u
      = -(2 * (1 / (4 * u ^ (2 : ℕ))) * (besselNormalForm u * besselNormalFormDeriv u)) := by
    have hsec : besselNormalFormSecond u
        = -((1 + 1 / (4 * u ^ (2 : ℕ))) * besselNormalForm u) := by linarith [hode]
    rw [hsec]
    ring
  rw [hval] at h
  exact h

/-- **The differential inequality.**  The energy's logarithmic derivative is bounded by the
perturbation, by the arithmetic–geometric mean inequality. -/
theorem abs_deriv_besselEnergy_le {u : ℝ} (hu : 0 < u) :
    |-(2 * (1 / (4 * u ^ (2 : ℕ))) * (besselNormalForm u * besselNormalFormDeriv u))|
      ≤ 1 / (4 * u ^ (2 : ℕ)) * besselEnergy u := by
  have hq : (0 : ℝ) < 1 / (4 * u ^ (2 : ℕ)) := by positivity
  have hamgm : 2 * |besselNormalForm u| * |besselNormalFormDeriv u|
      ≤ besselNormalForm u ^ (2 : ℕ) + besselNormalFormDeriv u ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (|besselNormalForm u| - |besselNormalFormDeriv u|),
      sq_abs (besselNormalForm u), sq_abs (besselNormalFormDeriv u)]
  rw [abs_neg, abs_mul, abs_mul, abs_of_pos hq, besselEnergy,
    abs_mul (besselNormalForm u) (besselNormalFormDeriv u)]
  have habs : |(2 : ℝ)| = 2 := by norm_num
  rw [habs]
  nlinarith [hamgm, hq.le]


theorem hasDerivAt_inv_four_mul {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun w : ℝ => 1 / (4 * w)) (-(1 / (4 * v ^ (2 : ℕ)))) v := by
  have h := (hasDerivAt_inv hv).const_mul (1 / 4 : ℝ)
  have hfun : (fun w : ℝ => 1 / 4 * w⁻¹) = fun w : ℝ => 1 / (4 * w) := by
    funext w
    rw [one_div, one_div, mul_inv_rev]
    ring
  rw [hfun] at h
  have hval : (1 : ℝ) / 4 * -(v ^ (2 : ℕ))⁻¹ = -(1 / (4 * v ^ (2 : ℕ))) := by
    field_simp
  rwa [hval] at h

/-- **Grönwall for the energy.**  The perturbation is integrable, so the energy is trapped between
two multiples of its value at any base point. -/
theorem besselEnergy_le_exp {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    besselEnergy u ≤ besselEnergy a * Real.exp (1 / (4 * a) - 1 / (4 * u)) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  set G : ℝ → ℝ := fun v : ℝ => besselEnergy v * Real.exp (1 / (4 * v)) with hGdef
  have hGd : ∀ v : ℝ, 0 < v → HasDerivAt G
      (-(2 * (1 / (4 * v ^ (2 : ℕ))) * (besselNormalForm v * besselNormalFormDeriv v))
          * Real.exp (1 / (4 * v))
        + besselEnergy v * (Real.exp (1 / (4 * v)) * -(1 / (4 * v ^ (2 : ℕ))))) v := by
    intro v hv
    have hexp : HasDerivAt (fun w : ℝ => Real.exp (1 / (4 * w)))
        (Real.exp (1 / (4 * v)) * -(1 / (4 * v ^ (2 : ℕ)))) v :=
      (hasDerivAt_inv_four_mul (ne_of_gt hv)).exp
    exact (hasDerivAt_besselEnergy hv).mul hexp
  have hnonpos : ∀ v ∈ Set.Ioo a u, deriv G v ≤ 0 := by
    intro v hv
    have hv0 : 0 < v := lt_trans ha hv.1
    have hE0 : 0 ≤ besselEnergy v := besselEnergy_nonneg v
    have hq : (0 : ℝ) < 1 / (4 * v ^ (2 : ℕ)) := by positivity
    have hbound := abs_deriv_besselEnergy_le hv0
    have hle : -(2 * (1 / (4 * v ^ (2 : ℕ))) * (besselNormalForm v * besselNormalFormDeriv v))
        ≤ 1 / (4 * v ^ (2 : ℕ)) * besselEnergy v :=
      le_trans (le_abs_self _) hbound
    have hexppos : 0 < Real.exp (1 / (4 * v)) := Real.exp_pos _
    rw [(hGd v hv0).deriv]
    nlinarith [hle, hexppos, hE0, hq]
  have hcont : ContinuousOn G (Set.Icc a u) :=
    fun v hv => ((hGd v (lt_of_lt_of_le ha hv.1)).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Set.Icc a u)) := by
    rw [interior_Icc]
    exact fun v hv => ((hGd v (lt_trans ha hv.1)).differentiableAt).differentiableWithinAt
  have hanti : AntitoneOn G (Set.Icc a u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a u) hcont hdiff
    rw [interior_Icc]
    exact hnonpos
  have hle := hanti (Set.left_mem_Icc.mpr hau) (Set.right_mem_Icc.mpr hau) hau
  rw [hGdef] at hle
  simp only at hle
  have hexpu : (0 : ℝ) < Real.exp (1 / (4 * u)) := Real.exp_pos _
  have hsplit : Real.exp (1 / (4 * a))
      = Real.exp (1 / (4 * a) - 1 / (4 * u)) * Real.exp (1 / (4 * u)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit] at hle
  exact le_of_mul_le_mul_right (by linarith [hle]) hexpu


/-- **The energy method reproduces the envelope.**  The normal-form solution is bounded on
`[a, infinity)` by the square root of its energy budget at `a`, so `J_0` decays like `u^{-1/2}` with
a constant that is a genuine invariant of the equation rather than an artefact of the estimate. -/
theorem abs_besselNormalForm_le {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    |besselNormalForm u| ≤ Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hE := besselEnergy_le_exp ha hau
  have hEa : 0 ≤ besselEnergy a := besselEnergy_nonneg a
  have hsq : besselNormalForm u ^ (2 : ℕ) ≤ besselEnergy u := by
    rw [besselEnergy]
    nlinarith [sq_nonneg (besselNormalFormDeriv u)]
  have hexp1 : Real.exp (1 / (4 * a) - 1 / (4 * u)) ≤ Real.exp (1 / (4 * a)) := by
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) < 1 / (4 * u) := by positivity
    linarith
  have hchain : besselNormalForm u ^ (2 : ℕ) ≤ besselEnergy a * Real.exp (1 / (4 * a)) := by
    have hstep : besselEnergy a * Real.exp (1 / (4 * a) - 1 / (4 * u))
        ≤ besselEnergy a * Real.exp (1 / (4 * a)) :=
      mul_le_mul_of_nonneg_left hexp1 hEa
    linarith [hsq, hE, hstep]
  have hnn : (0 : ℝ) ≤ besselEnergy a * Real.exp (1 / (4 * a)) := by positivity
  have h := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq_eq_abs] at h


/-- The cosine coefficient of the normal-form solution against the unperturbed basis. -/
def besselCosCoeff (u : ℝ) : ℝ :=
  besselNormalForm u * Real.cos u - besselNormalFormDeriv u * Real.sin u

/-- The sine coefficient. -/
def besselSinCoeff (u : ℝ) : ℝ :=
  besselNormalForm u * Real.sin u + besselNormalFormDeriv u * Real.cos u

/-- **The exact two-branch representation.**  No approximation: the coefficients are defined so that
this is an identity, and the content is that they are almost constant. -/
theorem besselNormalForm_eq_coeff (u : ℝ) :
    besselNormalForm u = besselCosCoeff u * Real.cos u + besselSinCoeff u * Real.sin u := by
  rw [besselCosCoeff, besselSinCoeff]
  have h := Real.sin_sq_add_cos_sq u
  linear_combination (-besselNormalForm u) * h

/-- **The cosine coefficient moves only through the perturbation.** -/
theorem hasDerivAt_besselCosCoeff {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselCosCoeff
      (1 / (4 * u ^ (2 : ℕ)) * besselNormalForm u * Real.sin u) u := by
  have hw := hasDerivAt_besselNormalForm hu
  have hw' := hasDerivAt_besselNormalFormDeriv hu
  have hc : HasDerivAt Real.cos (-Real.sin u) u := Real.hasDerivAt_cos u
  have hs : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
  have h := (hw.mul hc).sub (hw'.mul hs)
  have hode := besselNormalForm_ode hu
  have hsec : besselNormalFormSecond u
      = -((1 + 1 / (4 * u ^ (2 : ℕ))) * besselNormalForm u) := by linarith [hode]
  have hval : besselNormalFormDeriv u * Real.cos u + besselNormalForm u * -Real.sin u
      - (besselNormalFormSecond u * Real.sin u + besselNormalFormDeriv u * Real.cos u)
      = 1 / (4 * u ^ (2 : ℕ)) * besselNormalForm u * Real.sin u := by
    rw [hsec]
    ring
  rw [hval] at h
  exact h

/-- **The sine coefficient likewise.** -/
theorem hasDerivAt_besselSinCoeff {u : ℝ} (hu : 0 < u) :
    HasDerivAt besselSinCoeff
      (-(1 / (4 * u ^ (2 : ℕ)) * besselNormalForm u * Real.cos u)) u := by
  have hw := hasDerivAt_besselNormalForm hu
  have hw' := hasDerivAt_besselNormalFormDeriv hu
  have hc : HasDerivAt Real.cos (-Real.sin u) u := Real.hasDerivAt_cos u
  have hs : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
  have h := (hw.mul hs).add (hw'.mul hc)
  have hode := besselNormalForm_ode hu
  have hsec : besselNormalFormSecond u
      = -((1 + 1 / (4 * u ^ (2 : ℕ))) * besselNormalForm u) := by linarith [hode]
  have hval : besselNormalFormDeriv u * Real.sin u + besselNormalForm u * Real.cos u
      + (besselNormalFormSecond u * Real.cos u + besselNormalFormDeriv u * -Real.sin u)
      = -(1 / (4 * u ^ (2 : ℕ)) * besselNormalForm u * Real.cos u) := by
    rw [hsec]
    ring
  rw [hval] at h
  exact h


theorem hasDerivAt_neg_inv_four_mul {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun w : ℝ => -(1 / (4 * w))) (1 / (4 * v ^ (2 : ℕ))) v := by
  have h := (hasDerivAt_inv_four_mul hv).neg
  rwa [neg_neg] at h

theorem intervalIntegrable_inv_four_sq {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    IntervalIntegrable (fun v : ℝ => 1 / (4 * v ^ (2 : ℕ))) MeasureTheory.volume a u := by
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.div (continuousOn_const.mul (continuousOn_pow 2)) ?_
  intro v hv
  rw [Set.uIcc_of_le hau] at hv
  have : (0 : ℝ) < v := lt_of_lt_of_le ha hv.1
  positivity

/-- The perturbation's tail mass. -/
theorem integral_inv_four_sq {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    (∫ v in a..u, 1 / (4 * v ^ (2 : ℕ))) = 1 / (4 * a) - 1 / (4 * u) := by
  have hpos : ∀ v ∈ Set.uIcc a u, v ≠ 0 := by
    intro v hv
    rw [Set.uIcc_of_le hau] at hv
    exact ne_of_gt (lt_of_lt_of_le ha hv.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hasDerivAt_neg_inv_four_mul (hpos v hv))
    (intervalIntegrable_inv_four_sq ha hau)
  rw [h]
  ring

/-- **The coefficients move by at most the perturbation's tail mass times the amplitude.** -/
theorem abs_besselCoeff_sub_le {a u M : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hM : ∀ v ∈ Set.Icc a u, |besselNormalForm v| ≤ M) :
    |besselCosCoeff u - besselCosCoeff a| ≤ M * (1 / (4 * a) - 1 / (4 * u))
      ∧ |besselSinCoeff u - besselSinCoeff a| ≤ M * (1 / (4 * a) - 1 / (4 * u)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ⟨le_rfl, hau⟩)
  have hpos : ∀ v ∈ Set.uIcc a u, 0 < v := by
    intro v hv
    rw [Set.uIcc_of_le hau] at hv
    exact lt_of_lt_of_le ha hv.1
  have hwc : ContinuousOn besselNormalForm (Set.uIcc a u) :=
    fun v hv => ((hasDerivAt_besselNormalForm (hpos v hv)).continuousAt).continuousWithinAt
  have hqc : ContinuousOn (fun v : ℝ => 1 / (4 * v ^ (2 : ℕ))) (Set.uIcc a u) := by
    refine continuousOn_const.div (continuousOn_const.mul (continuousOn_pow 2)) ?_
    intro v hv
    have := hpos v hv
    positivity
  have hmaj : IntervalIntegrable (fun v : ℝ => M * (1 / (4 * v ^ (2 : ℕ))))
      MeasureTheory.volume a u := (intervalIntegrable_inv_four_sq ha hau).const_mul M
  have hmajval : (∫ v in a..u, M * (1 / (4 * v ^ (2 : ℕ)))) = M * (1 / (4 * a) - 1 / (4 * u)) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_four_sq ha hau]
  constructor
  · have hint : IntervalIntegrable
        (fun v : ℝ => 1 / (4 * v ^ (2 : ℕ)) * besselNormalForm v * Real.sin v)
        MeasureTheory.volume a u :=
      ((hqc.mul hwc).mul Real.continuous_sin.continuousOn).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hasDerivAt_besselCosCoeff (hpos v hv)) hint
    rw [← hftc]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs
      (μ := MeasureTheory.volume) hau) ?_
    have hmono : (∫ v in a..u, |1 / (4 * v ^ (2 : ℕ)) * besselNormalForm v * Real.sin v|)
        ≤ ∫ v in a..u, M * (1 / (4 * v ^ (2 : ℕ))) := by
      refine intervalIntegral.integral_mono_on hau hint.abs hmaj fun v hv => ?_
      have hv0 : (0 : ℝ) < v := lt_of_lt_of_le ha hv.1
      have hq0 : (0 : ℝ) < 1 / (4 * v ^ (2 : ℕ)) := by positivity
      rw [abs_mul, abs_mul, abs_of_pos hq0]
      have hsin := Real.abs_sin_le_one v
      have hw := hM v hv
      calc 1 / (4 * v ^ (2 : ℕ)) * |besselNormalForm v| * |Real.sin v|
          ≤ 1 / (4 * v ^ (2 : ℕ)) * M * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hw hq0.le) hsin (abs_nonneg _)
              (by positivity)
        _ = M * (1 / (4 * v ^ (2 : ℕ))) := by ring
    rwa [hmajval] at hmono
  · have hint : IntervalIntegrable
        (fun v : ℝ => -(1 / (4 * v ^ (2 : ℕ)) * besselNormalForm v * Real.cos v))
        MeasureTheory.volume a u :=
      (((hqc.mul hwc).mul Real.continuous_cos.continuousOn).neg).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hasDerivAt_besselSinCoeff (hpos v hv)) hint
    rw [← hftc]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs
      (μ := MeasureTheory.volume) hau) ?_
    have hmono : (∫ v in a..u, |-(1 / (4 * v ^ (2 : ℕ)) * besselNormalForm v * Real.cos v)|)
        ≤ ∫ v in a..u, M * (1 / (4 * v ^ (2 : ℕ))) := by
      refine intervalIntegral.integral_mono_on hau hint.abs hmaj fun v hv => ?_
      have hv0 : (0 : ℝ) < v := lt_of_lt_of_le ha hv.1
      have hq0 : (0 : ℝ) < 1 / (4 * v ^ (2 : ℕ)) := by positivity
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos hq0]
      have hcos := Real.abs_cos_le_one v
      have hw := hM v hv
      calc 1 / (4 * v ^ (2 : ℕ)) * |besselNormalForm v| * |Real.cos v|
          ≤ 1 / (4 * v ^ (2 : ℕ)) * M * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hw hq0.le) hcos (abs_nonneg _)
              (by positivity)
        _ = M * (1 / (4 * v ^ (2 : ℕ))) := by ring
    rwa [hmajval] at hmono


/-- **The sharp asymptotic.**  On `[a, infinity)` the normal-form solution equals a *fixed* sinusoid
-- the one determined by its coefficients at `a` -- up to an error controlled by the perturbation's
tail mass.  Since that mass is `1/(4a) - 1/(4u) <= 1/(4a)`, the error is `O(1/a)` uniformly in `u`. -/
theorem abs_besselNormalForm_sub_fixed_le {a u M : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hM : ∀ v ∈ Set.Icc a u, |besselNormalForm v| ≤ M) :
    |besselNormalForm u
        - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u)|
      ≤ 2 * M * (1 / (4 * a) - 1 / (4 * u)) := by
  obtain ⟨hA, hB⟩ := abs_besselCoeff_sub_le ha hau hM
  have hrep := besselNormalForm_eq_coeff u
  have hsplit : besselNormalForm u
      - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u)
      = (besselCosCoeff u - besselCosCoeff a) * Real.cos u
        + (besselSinCoeff u - besselSinCoeff a) * Real.sin u := by
    rw [hrep]
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |(besselCosCoeff u - besselCosCoeff a) * Real.cos u|
      ≤ M * (1 / (4 * a) - 1 / (4 * u)) := by
    rw [abs_mul]
    calc |besselCosCoeff u - besselCosCoeff a| * |Real.cos u|
        ≤ M * (1 / (4 * a) - 1 / (4 * u)) * 1 :=
          mul_le_mul hA (Real.abs_cos_le_one u) (abs_nonneg _)
            (le_trans (abs_nonneg _) hA)
      _ = M * (1 / (4 * a) - 1 / (4 * u)) := by ring
  have h2 : |(besselSinCoeff u - besselSinCoeff a) * Real.sin u|
      ≤ M * (1 / (4 * a) - 1 / (4 * u)) := by
    rw [abs_mul]
    calc |besselSinCoeff u - besselSinCoeff a| * |Real.sin u|
        ≤ M * (1 / (4 * a) - 1 / (4 * u)) * 1 :=
          mul_le_mul hB (Real.abs_sin_le_one u) (abs_nonneg _)
            (le_trans (abs_nonneg _) hB)
      _ = M * (1 / (4 * a) - 1 / (4 * u)) := by ring
  linarith [h1, h2]


/-- **The coefficient pair carries exactly the energy.**  The two-branch amplitude is not an
auxiliary quantity: its square is the conserved-up-to-perturbation energy. -/
theorem besselCoeff_sq_add (a : ℝ) :
    besselCosCoeff a ^ (2 : ℕ) + besselSinCoeff a ^ (2 : ℕ) = besselEnergy a := by
  rw [besselCosCoeff, besselSinCoeff, besselEnergy]
  have h := Real.sin_sq_add_cos_sq a
  nlinarith [h, sq_nonneg (besselNormalForm a), sq_nonneg (besselNormalFormDeriv a)]

/-- **The asymptotic with every hypothesis discharged.** -/
theorem abs_besselNormalForm_sub_fixed_le' {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    |besselNormalForm u
        - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u)|
      ≤ 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
        * (1 / (4 * a) - 1 / (4 * u)) :=
  abs_besselNormalForm_sub_fixed_le ha hau
    (fun _ hv => abs_besselNormalForm_le ha hv.1)

/-- **The sharp asymptotic for `J_0` itself.**  The two-branch form with an explicit remainder and
no free constant. -/
theorem abs_besselJ0_sub_fixed_le {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    |besselJ0 u
        - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u) / Real.sqrt u|
      ≤ 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
        * (1 / (4 * a) - 1 / (4 * u)) / Real.sqrt u := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hbase := abs_besselNormalForm_sub_fixed_le' ha hau
  have hrw : besselJ0 u
      - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u) / Real.sqrt u
      = (besselNormalForm u
          - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u)) / Real.sqrt u := by
    rw [besselNormalForm]
    field_simp
  rw [hrw, abs_div, abs_of_pos hsu]
  gcongr


/-- Each branch amplitude is bounded by the root energy. -/
theorem abs_besselCoeff_le_sqrt_energy (u : ℝ) :
    |besselCosCoeff u| ≤ Real.sqrt (besselEnergy u)
      ∧ |besselSinCoeff u| ≤ Real.sqrt (besselEnergy u) := by
  have hsum := besselCoeff_sq_add u
  constructor
  · have hle : besselCosCoeff u ^ (2 : ℕ) ≤ besselEnergy u := by
      nlinarith [sq_nonneg (besselSinCoeff u), hsum]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h
  · have hle : besselSinCoeff u ^ (2 : ℕ) ≤ besselEnergy u := by
      nlinarith [sq_nonneg (besselCosCoeff u), hsum]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h

/-- The branch amplitudes are bounded on `[a, infinity)` by the energy budget at `a`. -/
theorem abs_besselCoeff_le_base {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    |besselCosCoeff u| ≤ Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
      ∧ |besselSinCoeff u| ≤ Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := by
  have hE := besselEnergy_le_exp ha hau
  have hEa : 0 ≤ besselEnergy a := besselEnergy_nonneg a
  have hexp1 : Real.exp (1 / (4 * a) - 1 / (4 * u)) ≤ Real.exp (1 / (4 * a)) := by
    refine Real.exp_le_exp.mpr ?_
    have hu : 0 < u := lt_of_lt_of_le ha hau
    have : (0 : ℝ) < 1 / (4 * u) := by positivity
    linarith
  have hchain : besselEnergy u ≤ besselEnergy a * Real.exp (1 / (4 * a)) := by
    have hstep : besselEnergy a * Real.exp (1 / (4 * a) - 1 / (4 * u))
        ≤ besselEnergy a * Real.exp (1 / (4 * a)) :=
      mul_le_mul_of_nonneg_left hexp1 hEa
    linarith [hE, hstep]
  obtain ⟨hA, hB⟩ := abs_besselCoeff_le_sqrt_energy u
  exact ⟨le_trans hA (Real.sqrt_le_sqrt hchain), le_trans hB (Real.sqrt_le_sqrt hchain)⟩

/-- The branch amplitudes' derivatives decay like the perturbation. -/
theorem abs_deriv_besselCoeff_le_base {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    |1 / (4 * u ^ (2 : ℕ)) * besselNormalForm u * Real.sin u|
        ≤ 1 / (4 * u ^ (2 : ℕ)) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
      ∧ |-(1 / (4 * u ^ (2 : ℕ)) * besselNormalForm u * Real.cos u)|
        ≤ 1 / (4 * u ^ (2 : ℕ)) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hq : (0 : ℝ) < 1 / (4 * u ^ (2 : ℕ)) := by positivity
  have hw := abs_besselNormalForm_le ha hau
  constructor
  · rw [abs_mul, abs_mul, abs_of_pos hq]
    calc 1 / (4 * u ^ (2 : ℕ)) * |besselNormalForm u| * |Real.sin u|
        ≤ 1 / (4 * u ^ (2 : ℕ)) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hq.le) (Real.abs_sin_le_one u)
            (abs_nonneg _) (by positivity)
      _ = 1 / (4 * u ^ (2 : ℕ)) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := by ring
  · rw [abs_neg, abs_mul, abs_mul, abs_of_pos hq]
    calc 1 / (4 * u ^ (2 : ℕ)) * |besselNormalForm u| * |Real.cos u|
        ≤ 1 / (4 * u ^ (2 : ℕ)) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hq.le) (Real.abs_cos_le_one u)
            (abs_nonneg _) (by positivity)
      _ = 1 / (4 * u ^ (2 : ℕ)) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := by ring


end GaloisForLFunctions.RHTower
