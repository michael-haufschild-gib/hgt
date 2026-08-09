import Mathlib

/-!
# Coefficients of a perturbed harmonic oscillator

For a solution of

```text
w'' + (1 + q(u)) w = 0,        |q(u)| ≤ κ/u²,
```

the energy `E = w² + (w')²` obeys `E' = -2 q w w'`, so `|E'| ≤ |q| E` by the arithmetic–geometric
mean inequality and `E(u) exp(κ/u)` is antitone.  The energy is therefore trapped by its value at
any base point, and the coefficients

```text
A = w cos u - w' sin u,       B = w sin u + w' cos u
```

of the exact representation `w = A cos u + B sin u` satisfy `A' = q w sin u`, `B' = -q w cos u`.
Both are bounded by the square root of the energy budget, and both drift at rate `κ/u²`.

Nothing here is specific to any particular equation: only the two bounds on `q` and the ODE are
used.  The `1/u²` decay of the perturbation is what makes the drift integrable, and that is the
whole mechanism behind an `O(1/u)` relative error rather than a fractional-power loss.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

variable {w Dw DDw q : ℝ → ℝ}

/-- The oscillator energy. -/
def oscEnergy (w Dw : ℝ → ℝ) (u : ℝ) : ℝ := w u ^ 2 + Dw u ^ 2

theorem oscEnergy_nonneg (w Dw : ℝ → ℝ) (u : ℝ) : 0 ≤ oscEnergy w Dw u := by
  rw [oscEnergy]
  positivity

/-- **The energy is almost conserved.**  Its derivative is the perturbation times a product of the
solution and its derivative; the unperturbed contribution cancels exactly. -/
theorem hasDerivAt_oscEnergy {u : ℝ}
    (hw : HasDerivAt w (Dw u) u) (hDw : HasDerivAt Dw (DDw u) u)
    (hode : DDw u + (1 + q u) * w u = 0) :
    HasDerivAt (oscEnergy w Dw) (-(2 * q u * (w u * Dw u))) u := by
  have h1 : HasDerivAt (fun v : ℝ => w v ^ 2) (2 * w u * Dw u) u := by
    have h := hw.pow 2
    have hv : ((2 : ℕ) : ℝ) * w u ^ (2 - 1) * Dw u = 2 * w u * Dw u := by norm_num
    rw [hv] at h
    exact h
  have h2 : HasDerivAt (fun v : ℝ => Dw v ^ 2) (2 * Dw u * DDw u) u := by
    have h := hDw.pow 2
    have hv : ((2 : ℕ) : ℝ) * Dw u ^ (2 - 1) * DDw u = 2 * Dw u * DDw u := by norm_num
    rw [hv] at h
    exact h
  have h := h1.add h2
  have hval : 2 * w u * Dw u + 2 * Dw u * DDw u = -(2 * q u * (w u * Dw u)) := by
    have hsec : DDw u = -((1 + q u) * w u) := by linarith
    rw [hsec]
    ring
  rw [hval] at h
  exact h

/-- **The differential inequality**, by the arithmetic–geometric mean inequality. -/
theorem abs_deriv_oscEnergy_le {u κ : ℝ} (hu : 0 < u) (hκ : 0 ≤ κ)
    (hq : |q u| ≤ κ / u ^ 2) :
    |-(2 * q u * (w u * Dw u))| ≤ κ / u ^ 2 * oscEnergy w Dw u := by
  have hamgm : 2 * |w u| * |Dw u| ≤ w u ^ 2 + Dw u ^ 2 := by
    nlinarith [sq_nonneg (|w u| - |Dw u|), sq_abs (w u), sq_abs (Dw u)]
  rw [abs_neg, abs_mul, abs_mul, oscEnergy, abs_mul (w u) (Dw u)]
  have habs : |(2 : ℝ)| = 2 := by norm_num
  rw [habs]
  have hnn : (0 : ℝ) ≤ |w u| * |Dw u| := by positivity
  calc 2 * |q u| * (|w u| * |Dw u|) ≤ 2 * (κ / u ^ 2) * (|w u| * |Dw u|) := by
        have := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith [hnn]
    _ ≤ κ / u ^ 2 * (w u ^ 2 + Dw u ^ 2) := by
        have hκu : (0 : ℝ) ≤ κ / u ^ 2 := by positivity
        nlinarith [hamgm, hκu]

theorem hasDerivAt_const_div {κ v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun t : ℝ => κ / t) (-(κ / v ^ 2)) v := by
  have h := (hasDerivAt_inv hv).const_mul κ
  have hfun : (fun t : ℝ => κ * t⁻¹) = fun t : ℝ => κ / t := by
    funext t
    rw [div_eq_mul_inv]
  rw [hfun] at h
  have hval : κ * -(v ^ 2)⁻¹ = -(κ / v ^ 2) := by field_simp
  rwa [hval] at h

/-- **Grönwall for the energy.**  An integrable perturbation traps the energy between two multiples
of its value at any base point. -/
theorem oscEnergy_le_exp {a u κ : ℝ} (ha : 0 < a) (hau : a ≤ u) (hκ : 0 ≤ κ)
    (hw : ∀ v : ℝ, 0 < v → HasDerivAt w (Dw v) v)
    (hDw : ∀ v : ℝ, 0 < v → HasDerivAt Dw (DDw v) v)
    (hode : ∀ v : ℝ, 0 < v → DDw v + (1 + q v) * w v = 0)
    (hq : ∀ v : ℝ, 0 < v → |q v| ≤ κ / v ^ 2) :
    oscEnergy w Dw u ≤ oscEnergy w Dw a * Real.exp (κ / a - κ / u) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  set G : ℝ → ℝ := fun v : ℝ => oscEnergy w Dw v * Real.exp (κ / v) with hGdef
  have hGd : ∀ v : ℝ, 0 < v → HasDerivAt G
      (-(2 * q v * (w v * Dw v)) * Real.exp (κ / v)
        + oscEnergy w Dw v * (Real.exp (κ / v) * -(κ / v ^ 2))) v := by
    intro v hv
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (κ / t))
        (Real.exp (κ / v) * -(κ / v ^ 2)) v :=
      (hasDerivAt_const_div (ne_of_gt hv)).exp
    exact (hasDerivAt_oscEnergy (hw v hv) (hDw v hv) (hode v hv)).mul hexp
  have hnonpos : ∀ v ∈ Set.Ioo a u, deriv G v ≤ 0 := by
    intro v hv
    have hv0 : 0 < v := lt_trans ha hv.1
    have hE0 : 0 ≤ oscEnergy w Dw v := oscEnergy_nonneg w Dw v
    have hκv : (0 : ℝ) ≤ κ / v ^ 2 := by positivity
    have hbound := abs_deriv_oscEnergy_le (w := w) (Dw := Dw) hv0 hκ (hq v hv0)
    have hle : -(2 * q v * (w v * Dw v)) ≤ κ / v ^ 2 * oscEnergy w Dw v :=
      le_trans (le_abs_self _) hbound
    have hexppos : 0 < Real.exp (κ / v) := Real.exp_pos _
    rw [(hGd v hv0).deriv]
    nlinarith [hle, hexppos, hE0, hκv]
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
  have hexpu : (0 : ℝ) < Real.exp (κ / u) := Real.exp_pos _
  have hsplit : Real.exp (κ / a) = Real.exp (κ / a - κ / u) * Real.exp (κ / u) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit] at hle
  exact le_of_mul_le_mul_right (by linarith [hle]) hexpu

/-- The cosine coefficient against the unperturbed basis. -/
def oscCosCoeff (w Dw : ℝ → ℝ) (u : ℝ) : ℝ := w u * Real.cos u - Dw u * Real.sin u

/-- The sine coefficient. -/
def oscSinCoeff (w Dw : ℝ → ℝ) (u : ℝ) : ℝ := w u * Real.sin u + Dw u * Real.cos u

/-- **The exact two-branch representation.**  An identity, not an approximation; the content is
that the coefficients are almost constant. -/
theorem osc_eq_coeff (w Dw : ℝ → ℝ) (u : ℝ) :
    w u = oscCosCoeff w Dw u * Real.cos u + oscSinCoeff w Dw u * Real.sin u := by
  rw [oscCosCoeff, oscSinCoeff]
  linear_combination (-(w u)) * Real.sin_sq_add_cos_sq u

/-- The coefficients carry exactly the energy. -/
theorem oscCoeff_sq_add (w Dw : ℝ → ℝ) (u : ℝ) :
    oscCosCoeff w Dw u ^ 2 + oscSinCoeff w Dw u ^ 2 = oscEnergy w Dw u := by
  rw [oscCosCoeff, oscSinCoeff, oscEnergy]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem hasDerivAt_oscCosCoeff {u : ℝ}
    (hw : HasDerivAt w (Dw u) u) (hDw : HasDerivAt Dw (DDw u) u)
    (hode : DDw u + (1 + q u) * w u = 0) :
    HasDerivAt (oscCosCoeff w Dw) (q u * w u * Real.sin u) u := by
  have hc : HasDerivAt Real.cos (-Real.sin u) u := Real.hasDerivAt_cos u
  have hs : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
  have h := (hw.mul hc).sub (hDw.mul hs)
  have hval : Dw u * Real.cos u + w u * -Real.sin u
      - (DDw u * Real.sin u + Dw u * Real.cos u) = q u * w u * Real.sin u := by
    have hsec : DDw u = -((1 + q u) * w u) := by linarith
    rw [hsec]
    ring
  rw [hval] at h
  exact h

theorem hasDerivAt_oscSinCoeff {u : ℝ}
    (hw : HasDerivAt w (Dw u) u) (hDw : HasDerivAt Dw (DDw u) u)
    (hode : DDw u + (1 + q u) * w u = 0) :
    HasDerivAt (oscSinCoeff w Dw) (-(q u * w u * Real.cos u)) u := by
  have hc : HasDerivAt Real.cos (-Real.sin u) u := Real.hasDerivAt_cos u
  have hs : HasDerivAt Real.sin (Real.cos u) u := Real.hasDerivAt_sin u
  have h := (hw.mul hs).add (hDw.mul hc)
  have hval : Dw u * Real.sin u + w u * Real.cos u
      + (DDw u * Real.cos u + Dw u * -Real.sin u) = -(q u * w u * Real.cos u) := by
    have hsec : DDw u = -((1 + q u) * w u) := by linarith
    rw [hsec]
    ring
  rw [hval] at h
  exact h

/-- **The energy method gives the envelope.**  The solution is bounded on `[a, ∞)` by the square
root of its energy budget at `a`. -/
theorem abs_osc_le {a u κ : ℝ} (ha : 0 < a) (hau : a ≤ u) (hκ : 0 ≤ κ)
    (hw : ∀ v : ℝ, 0 < v → HasDerivAt w (Dw v) v)
    (hDw : ∀ v : ℝ, 0 < v → HasDerivAt Dw (DDw v) v)
    (hode : ∀ v : ℝ, 0 < v → DDw v + (1 + q v) * w v = 0)
    (hq : ∀ v : ℝ, 0 < v → |q v| ≤ κ / v ^ 2) :
    |w u| ≤ Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a)) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hE := oscEnergy_le_exp (q := q) (DDw := DDw) ha hau hκ hw hDw hode hq
  have hEa : 0 ≤ oscEnergy w Dw a := oscEnergy_nonneg w Dw a
  have hsq : w u ^ 2 ≤ oscEnergy w Dw u := by
    rw [oscEnergy]
    nlinarith [sq_nonneg (Dw u)]
  have hexp1 : Real.exp (κ / a - κ / u) ≤ Real.exp (κ / a) := by
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ κ / u := by positivity
    linarith
  have hchain : w u ^ 2 ≤ oscEnergy w Dw a * Real.exp (κ / a) := by
    have hstep : oscEnergy w Dw a * Real.exp (κ / a - κ / u)
        ≤ oscEnergy w Dw a * Real.exp (κ / a) := mul_le_mul_of_nonneg_left hexp1 hEa
    linarith [hsq, hE, hstep]
  have h := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq_eq_abs] at h

/-- **Both coefficients are bounded by the energy budget.** -/
theorem abs_oscCoeff_le_base {a u κ : ℝ} (ha : 0 < a) (hau : a ≤ u) (hκ : 0 ≤ κ)
    (hw : ∀ v : ℝ, 0 < v → HasDerivAt w (Dw v) v)
    (hDw : ∀ v : ℝ, 0 < v → HasDerivAt Dw (DDw v) v)
    (hode : ∀ v : ℝ, 0 < v → DDw v + (1 + q v) * w v = 0)
    (hq : ∀ v : ℝ, 0 < v → |q v| ≤ κ / v ^ 2) :
    |oscCosCoeff w Dw u| ≤ Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a))
      ∧ |oscSinCoeff w Dw u| ≤ Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a)) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hE := oscEnergy_le_exp (q := q) (DDw := DDw) ha hau hκ hw hDw hode hq
  have hEa : 0 ≤ oscEnergy w Dw a := oscEnergy_nonneg w Dw a
  have hexp1 : Real.exp (κ / a - κ / u) ≤ Real.exp (κ / a) := by
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ κ / u := by positivity
    linarith
  have hbud : oscEnergy w Dw u ≤ oscEnergy w Dw a * Real.exp (κ / a) := by
    have hstep : oscEnergy w Dw a * Real.exp (κ / a - κ / u)
        ≤ oscEnergy w Dw a * Real.exp (κ / a) := mul_le_mul_of_nonneg_left hexp1 hEa
    linarith [hE, hstep]
  have hsum := oscCoeff_sq_add w Dw u
  constructor
  · have hle : oscCosCoeff w Dw u ^ 2 ≤ oscEnergy w Dw a * Real.exp (κ / a) := by
      nlinarith [sq_nonneg (oscSinCoeff w Dw u), hsum, hbud]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h
  · have hle : oscSinCoeff w Dw u ^ 2 ≤ oscEnergy w Dw a * Real.exp (κ / a) := by
      nlinarith [sq_nonneg (oscCosCoeff w Dw u), hsum, hbud]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h

/-- **Both coefficients drift at rate `κ/u²`.**  This is the integrable drift that makes the
representation asymptotic with relative error `O(1/u)`. -/
theorem abs_deriv_oscCoeff_le_base {a u κ : ℝ} (ha : 0 < a) (hau : a ≤ u) (hκ : 0 ≤ κ)
    (hw : ∀ v : ℝ, 0 < v → HasDerivAt w (Dw v) v)
    (hDw : ∀ v : ℝ, 0 < v → HasDerivAt Dw (DDw v) v)
    (hode : ∀ v : ℝ, 0 < v → DDw v + (1 + q v) * w v = 0)
    (hq : ∀ v : ℝ, 0 < v → |q v| ≤ κ / v ^ 2) :
    |q u * w u * Real.sin u|
        ≤ κ / u ^ 2 * Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a))
      ∧ |-(q u * w u * Real.cos u)|
        ≤ κ / u ^ 2 * Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a)) := by
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hκu : (0 : ℝ) ≤ κ / u ^ 2 := by positivity
  have hwb := abs_osc_le (q := q) (DDw := DDw) ha hau hκ hw hDw hode hq
  have hqb := hq u hu
  have hM : (0 : ℝ) ≤ Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a)) := Real.sqrt_nonneg _
  have hmain : ∀ T : ℝ, |T| ≤ 1 → |q u * w u * T|
      ≤ κ / u ^ 2 * Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a)) := by
    intro T hT
    rw [abs_mul, abs_mul]
    calc |q u| * |w u| * |T|
        ≤ (κ / u ^ 2) * Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a)) * 1 := by
          exact mul_le_mul (mul_le_mul hqb hwb (abs_nonneg _) hκu) hT (abs_nonneg _)
            (by positivity)
      _ = κ / u ^ 2 * Real.sqrt (oscEnergy w Dw a * Real.exp (κ / a)) := by ring
  refine ⟨hmain _ (Real.abs_sin_le_one u), ?_⟩
  rw [abs_neg]
  exact hmain _ (Real.abs_cos_le_one u)

end GaloisForLFunctions.HTGeometry
