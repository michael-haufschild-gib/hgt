import Mathlib

/-!
# A perturbed oscillator in a general phase parameterization

The energy method for `w'' + (1 + q) w = 0` needs no privileged variable.  If `φ` is an increasing
phase and derivatives with respect to `φ` are written `Dw = w'/φ'`, `DDw = (Dw)'/φ'`, the same
three facts hold with `φ'` decorating each derivative:

```text
E = w² + (Dw)²,        E' = -2 φ' q w Dw,
A = w cos φ - Dw sin φ,   A' =  φ' q w sin φ,
B = w sin φ + Dw cos φ,   B' = -φ' q w cos φ.
```

If the perturbation obeys `|q| ≤ κ/φ²` then `E exp(κ/φ)` is antitone, because the drift integrates
to `∫ φ' κ/φ² = κ/φ`.

Working in the phase parameterization rather than in the phase variable avoids inverting `φ`
altogether: every statement is about functions of the original variable, and the change of
variables never has to be performed.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

variable {w Dw DDw q φ Dφ : ℝ → ℝ}

/-- The oscillator energy in a phase parameterization. -/
def phaseEnergy (w Dw : ℝ → ℝ) (x : ℝ) : ℝ := w x ^ 2 + Dw x ^ 2

theorem phaseEnergy_nonneg (w Dw : ℝ → ℝ) (x : ℝ) : 0 ≤ phaseEnergy w Dw x := by
  rw [phaseEnergy]
  positivity

/-- **The energy is almost conserved.**  The unperturbed contribution cancels exactly; what is left
is the perturbation times the phase speed. -/
theorem hasDerivAt_phaseEnergy {x : ℝ}
    (hw : HasDerivAt w (Dφ x * Dw x) x) (hDw : HasDerivAt Dw (Dφ x * DDw x) x)
    (hode : DDw x + (1 + q x) * w x = 0) :
    HasDerivAt (phaseEnergy w Dw) (-(2 * Dφ x * q x * (w x * Dw x))) x := by
  have h1 : HasDerivAt (fun v : ℝ => w v ^ 2) (2 * w x * (Dφ x * Dw x)) x := by
    have h := hw.pow 2
    have hv : ((2 : ℕ) : ℝ) * w x ^ (2 - 1) * (Dφ x * Dw x)
        = 2 * w x * (Dφ x * Dw x) := by norm_num
    rw [hv] at h
    exact h
  have h2 : HasDerivAt (fun v : ℝ => Dw v ^ 2) (2 * Dw x * (Dφ x * DDw x)) x := by
    have h := hDw.pow 2
    have hv : ((2 : ℕ) : ℝ) * Dw x ^ (2 - 1) * (Dφ x * DDw x)
        = 2 * Dw x * (Dφ x * DDw x) := by norm_num
    rw [hv] at h
    exact h
  have h := h1.add h2
  have hval : 2 * w x * (Dφ x * Dw x) + 2 * Dw x * (Dφ x * DDw x)
      = -(2 * Dφ x * q x * (w x * Dw x)) := by
    have hsec : DDw x = -((1 + q x) * w x) := by linarith
    rw [hsec]
    ring
  rw [hval] at h
  exact h

/-- **The differential inequality**, by the arithmetic–geometric mean inequality. -/
theorem abs_deriv_phaseEnergy_le {x κ : ℝ} (hDφ : 0 ≤ Dφ x)
    (hq : |q x| ≤ κ / φ x ^ 2) :
    |-(2 * Dφ x * q x * (w x * Dw x))| ≤ Dφ x * (κ / φ x ^ 2) * phaseEnergy w Dw x := by
  have hamgm : 2 * |w x| * |Dw x| ≤ w x ^ 2 + Dw x ^ 2 := by
    nlinarith [sq_nonneg (|w x| - |Dw x|), sq_abs (w x), sq_abs (Dw x)]
  have hκ : (0 : ℝ) ≤ κ / φ x ^ 2 := le_trans (abs_nonneg _) hq
  rw [abs_neg, abs_mul, abs_mul, abs_mul, phaseEnergy, abs_mul (w x) (Dw x),
    abs_of_nonneg hDφ]
  have habs : |(2 : ℝ)| = 2 := by norm_num
  rw [habs]
  have hnn : (0 : ℝ) ≤ |w x| * |Dw x| := by positivity
  calc 2 * Dφ x * |q x| * (|w x| * |Dw x|)
      ≤ 2 * Dφ x * (κ / φ x ^ 2) * (|w x| * |Dw x|) := by
        have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2 * Dφ x)
        nlinarith [hnn]
    _ ≤ Dφ x * (κ / φ x ^ 2) * (w x ^ 2 + Dw x ^ 2) := by
        nlinarith [hamgm, mul_nonneg hDφ hκ]

/-- The cosine coefficient against the unperturbed basis in the phase. -/
def phaseCosCoeff (w Dw φ : ℝ → ℝ) (x : ℝ) : ℝ := w x * Real.cos (φ x) - Dw x * Real.sin (φ x)

/-- The sine coefficient. -/
def phaseSinCoeff (w Dw φ : ℝ → ℝ) (x : ℝ) : ℝ := w x * Real.sin (φ x) + Dw x * Real.cos (φ x)

/-- **The exact two-branch representation.** -/
theorem phase_eq_coeff (w Dw φ : ℝ → ℝ) (x : ℝ) :
    w x = phaseCosCoeff w Dw φ x * Real.cos (φ x)
      + phaseSinCoeff w Dw φ x * Real.sin (φ x) := by
  rw [phaseCosCoeff, phaseSinCoeff]
  linear_combination (-(w x)) * Real.sin_sq_add_cos_sq (φ x)

/-- The coefficients carry exactly the energy. -/
theorem phaseCoeff_sq_add (w Dw φ : ℝ → ℝ) (x : ℝ) :
    phaseCosCoeff w Dw φ x ^ 2 + phaseSinCoeff w Dw φ x ^ 2 = phaseEnergy w Dw x := by
  rw [phaseCosCoeff, phaseSinCoeff, phaseEnergy]
  nlinarith [Real.sin_sq_add_cos_sq (φ x)]

theorem hasDerivAt_phaseCosCoeff {x : ℝ}
    (hφ : HasDerivAt φ (Dφ x) x)
    (hw : HasDerivAt w (Dφ x * Dw x) x) (hDw : HasDerivAt Dw (Dφ x * DDw x) x)
    (hode : DDw x + (1 + q x) * w x = 0) :
    HasDerivAt (phaseCosCoeff w Dw φ) (Dφ x * q x * w x * Real.sin (φ x)) x := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (φ t)) (-Real.sin (φ x) * Dφ x) x :=
    (Real.hasDerivAt_cos (φ x)).comp x hφ
  have hs : HasDerivAt (fun t : ℝ => Real.sin (φ t)) (Real.cos (φ x) * Dφ x) x :=
    (Real.hasDerivAt_sin (φ x)).comp x hφ
  have h := (hw.mul hc).sub (hDw.mul hs)
  have hval : Dφ x * Dw x * Real.cos (φ x) + w x * (-Real.sin (φ x) * Dφ x)
      - (Dφ x * DDw x * Real.sin (φ x) + Dw x * (Real.cos (φ x) * Dφ x))
      = Dφ x * q x * w x * Real.sin (φ x) := by
    have hsec : DDw x = -((1 + q x) * w x) := by linarith
    rw [hsec]
    ring
  rw [hval] at h
  exact h

theorem hasDerivAt_phaseSinCoeff {x : ℝ}
    (hφ : HasDerivAt φ (Dφ x) x)
    (hw : HasDerivAt w (Dφ x * Dw x) x) (hDw : HasDerivAt Dw (Dφ x * DDw x) x)
    (hode : DDw x + (1 + q x) * w x = 0) :
    HasDerivAt (phaseSinCoeff w Dw φ) (-(Dφ x * q x * w x * Real.cos (φ x))) x := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (φ t)) (-Real.sin (φ x) * Dφ x) x :=
    (Real.hasDerivAt_cos (φ x)).comp x hφ
  have hs : HasDerivAt (fun t : ℝ => Real.sin (φ t)) (Real.cos (φ x) * Dφ x) x :=
    (Real.hasDerivAt_sin (φ x)).comp x hφ
  have h := (hw.mul hs).add (hDw.mul hc)
  have hval : Dφ x * Dw x * Real.sin (φ x) + w x * (Real.cos (φ x) * Dφ x)
      + (Dφ x * DDw x * Real.cos (φ x) + Dw x * (-Real.sin (φ x) * Dφ x))
      = -(Dφ x * q x * w x * Real.cos (φ x)) := by
    have hsec : DDw x = -((1 + q x) * w x) := by linarith
    rw [hsec]
    ring
  rw [hval] at h
  exact h

/-- **Grönwall in the phase parameterization.**  The drift integrates to `κ/φ`, so `E exp(κ/φ)` is
antitone and the energy is trapped by its value at the base point. -/
theorem phaseEnergy_le_exp {a b κ : ℝ} (hab : a ≤ b)
    (hφd : ∀ x : ℝ, a ≤ x → HasDerivAt φ (Dφ x) x)
    (hφpos : ∀ x : ℝ, a ≤ x → 0 < φ x)
    (hDφ : ∀ x : ℝ, a ≤ x → 0 ≤ Dφ x)
    (hw : ∀ x : ℝ, a ≤ x → HasDerivAt w (Dφ x * Dw x) x)
    (hDw : ∀ x : ℝ, a ≤ x → HasDerivAt Dw (Dφ x * DDw x) x)
    (hode : ∀ x : ℝ, a ≤ x → DDw x + (1 + q x) * w x = 0)
    (hq : ∀ x : ℝ, a ≤ x → |q x| ≤ κ / φ x ^ 2) :
    phaseEnergy w Dw b ≤ phaseEnergy w Dw a * Real.exp (κ / φ a - κ / φ b) := by
  set G : ℝ → ℝ := fun x : ℝ => phaseEnergy w Dw x * Real.exp (κ / φ x) with hGdef
  have hGd : ∀ x : ℝ, a ≤ x → HasDerivAt G
      (-(2 * Dφ x * q x * (w x * Dw x)) * Real.exp (κ / φ x)
        + phaseEnergy w Dw x * (Real.exp (κ / φ x) * ((0 * φ x - κ * Dφ x) / φ x ^ 2))) x := by
    intro x hx
    have hne : φ x ≠ 0 := ne_of_gt (hφpos x hx)
    have hdiv : HasDerivAt (fun t : ℝ => κ / φ t) ((0 * φ x - κ * Dφ x) / φ x ^ 2) x :=
      (hasDerivAt_const x κ).div (hφd x hx) hne
    exact (hasDerivAt_phaseEnergy (hw x hx) (hDw x hx) (hode x hx)).mul hdiv.exp
  have hnonpos : ∀ x ∈ Set.Ioo a b, deriv G x ≤ 0 := by
    intro x hx
    have hxa : a ≤ x := le_of_lt hx.1
    have hE0 : 0 ≤ phaseEnergy w Dw x := phaseEnergy_nonneg w Dw x
    have hφ0 : 0 < φ x := hφpos x hxa
    have hD0 : 0 ≤ Dφ x := hDφ x hxa
    have hbound := abs_deriv_phaseEnergy_le (w := w) (Dw := Dw) (q := q) (φ := φ) hD0 (hq x hxa)
    have hle : -(2 * Dφ x * q x * (w x * Dw x)) ≤ Dφ x * (κ / φ x ^ 2) * phaseEnergy w Dw x :=
      le_trans (le_abs_self _) hbound
    have hexppos : 0 < Real.exp (κ / φ x) := Real.exp_pos _
    have hne : φ x ≠ 0 := ne_of_gt hφ0
    have hval : (0 * φ x - κ * Dφ x) / φ x ^ 2 = -(Dφ x * (κ / φ x ^ 2)) := by
      field_simp
      ring
    rw [(hGd x hxa).deriv, hval]
    nlinarith [hle, hexppos, hE0]
  have hcont : ContinuousOn G (Set.Icc a b) :=
    fun x hx => ((hGd x hx.1).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Set.Icc a b)) := by
    rw [interior_Icc]
    exact fun x hx => ((hGd x (le_of_lt hx.1)).differentiableAt).differentiableWithinAt
  have hanti : AntitoneOn G (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff
    rw [interior_Icc]
    exact hnonpos
  have hle := hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  rw [hGdef] at hle
  simp only at hle
  have hexpb : (0 : ℝ) < Real.exp (κ / φ b) := Real.exp_pos _
  have hsplit : Real.exp (κ / φ a) = Real.exp (κ / φ a - κ / φ b) * Real.exp (κ / φ b) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit] at hle
  exact le_of_mul_le_mul_right (by linarith [hle]) hexpb

/-- **The envelope.** -/
theorem abs_phase_le {a b κ : ℝ} (hab : a ≤ b) (hκ : 0 ≤ κ)
    (hφd : ∀ x : ℝ, a ≤ x → HasDerivAt φ (Dφ x) x)
    (hφpos : ∀ x : ℝ, a ≤ x → 0 < φ x)
    (hDφ : ∀ x : ℝ, a ≤ x → 0 ≤ Dφ x)
    (hw : ∀ x : ℝ, a ≤ x → HasDerivAt w (Dφ x * Dw x) x)
    (hDw : ∀ x : ℝ, a ≤ x → HasDerivAt Dw (Dφ x * DDw x) x)
    (hode : ∀ x : ℝ, a ≤ x → DDw x + (1 + q x) * w x = 0)
    (hq : ∀ x : ℝ, a ≤ x → |q x| ≤ κ / φ x ^ 2) :
    |w b| ≤ Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a)) := by
  have hE := phaseEnergy_le_exp (w := w) (Dw := Dw) (DDw := DDw) (q := q) (φ := φ) (Dφ := Dφ)
    hab hφd hφpos hDφ hw hDw hode hq
  have hEa : 0 ≤ phaseEnergy w Dw a := phaseEnergy_nonneg w Dw a
  have hsq : w b ^ 2 ≤ phaseEnergy w Dw b := by
    rw [phaseEnergy]
    nlinarith [sq_nonneg (Dw b)]
  have hexp1 : Real.exp (κ / φ a - κ / φ b) ≤ Real.exp (κ / φ a) := by
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ κ / φ b := div_nonneg hκ (hφpos b hab).le
    linarith
  have hchain : w b ^ 2 ≤ phaseEnergy w Dw a * Real.exp (κ / φ a) := by
    have hstep : phaseEnergy w Dw a * Real.exp (κ / φ a - κ / φ b)
        ≤ phaseEnergy w Dw a * Real.exp (κ / φ a) := mul_le_mul_of_nonneg_left hexp1 hEa
    linarith [hsq, hE, hstep]
  have h := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq_eq_abs] at h

/-- **Both coefficients are bounded by the energy budget.** -/
theorem abs_phaseCoeff_le_base {a b κ : ℝ} (hab : a ≤ b) (hκ : 0 ≤ κ)
    (hφd : ∀ x : ℝ, a ≤ x → HasDerivAt φ (Dφ x) x)
    (hφpos : ∀ x : ℝ, a ≤ x → 0 < φ x)
    (hDφ : ∀ x : ℝ, a ≤ x → 0 ≤ Dφ x)
    (hw : ∀ x : ℝ, a ≤ x → HasDerivAt w (Dφ x * Dw x) x)
    (hDw : ∀ x : ℝ, a ≤ x → HasDerivAt Dw (Dφ x * DDw x) x)
    (hode : ∀ x : ℝ, a ≤ x → DDw x + (1 + q x) * w x = 0)
    (hq : ∀ x : ℝ, a ≤ x → |q x| ≤ κ / φ x ^ 2) :
    |phaseCosCoeff w Dw φ b| ≤ Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a))
      ∧ |phaseSinCoeff w Dw φ b| ≤ Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a)) := by
  have hE := phaseEnergy_le_exp (w := w) (Dw := Dw) (DDw := DDw) (q := q) (φ := φ) (Dφ := Dφ)
    hab hφd hφpos hDφ hw hDw hode hq
  have hEa : 0 ≤ phaseEnergy w Dw a := phaseEnergy_nonneg w Dw a
  have hexp1 : Real.exp (κ / φ a - κ / φ b) ≤ Real.exp (κ / φ a) := by
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ κ / φ b := div_nonneg hκ (hφpos b hab).le
    linarith
  have hbud : phaseEnergy w Dw b ≤ phaseEnergy w Dw a * Real.exp (κ / φ a) := by
    have hstep : phaseEnergy w Dw a * Real.exp (κ / φ a - κ / φ b)
        ≤ phaseEnergy w Dw a * Real.exp (κ / φ a) := mul_le_mul_of_nonneg_left hexp1 hEa
    linarith [hE, hstep]
  have hsum := phaseCoeff_sq_add w Dw φ b
  constructor
  · have hle : phaseCosCoeff w Dw φ b ^ 2 ≤ phaseEnergy w Dw a * Real.exp (κ / φ a) := by
      nlinarith [sq_nonneg (phaseSinCoeff w Dw φ b), hsum, hbud]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h
  · have hle : phaseSinCoeff w Dw φ b ^ 2 ≤ phaseEnergy w Dw a * Real.exp (κ / φ a) := by
      nlinarith [sq_nonneg (phaseCosCoeff w Dw φ b), hsum, hbud]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs] at h

/-- **Both coefficients drift at rate `φ' κ/φ²`.** -/
theorem abs_deriv_phaseCoeff_le_base {a b κ : ℝ} (hab : a ≤ b) (hκ : 0 ≤ κ)
    (hφd : ∀ x : ℝ, a ≤ x → HasDerivAt φ (Dφ x) x)
    (hφpos : ∀ x : ℝ, a ≤ x → 0 < φ x)
    (hDφ : ∀ x : ℝ, a ≤ x → 0 ≤ Dφ x)
    (hw : ∀ x : ℝ, a ≤ x → HasDerivAt w (Dφ x * Dw x) x)
    (hDw : ∀ x : ℝ, a ≤ x → HasDerivAt Dw (Dφ x * DDw x) x)
    (hode : ∀ x : ℝ, a ≤ x → DDw x + (1 + q x) * w x = 0)
    (hq : ∀ x : ℝ, a ≤ x → |q x| ≤ κ / φ x ^ 2) :
    |Dφ b * q b * w b * Real.sin (φ b)|
        ≤ Dφ b * (κ / φ b ^ 2) * Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a))
      ∧ |-(Dφ b * q b * w b * Real.cos (φ b))|
        ≤ Dφ b * (κ / φ b ^ 2) * Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a)) := by
  have hwb := abs_phase_le (w := w) (Dw := Dw) (DDw := DDw) (q := q) (φ := φ) (Dφ := Dφ)
    hab hκ hφd hφpos hDφ hw hDw hode hq
  have hqb := hq b hab
  have hD0 : 0 ≤ Dφ b := hDφ b hab
  have hκb : (0 : ℝ) ≤ κ / φ b ^ 2 := le_trans (abs_nonneg _) hqb
  have hM : (0 : ℝ) ≤ Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a)) := Real.sqrt_nonneg _
  have hmain : ∀ T : ℝ, |T| ≤ 1 → |Dφ b * q b * w b * T|
      ≤ Dφ b * (κ / φ b ^ 2) * Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a)) := by
    intro T hT
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hD0]
    calc Dφ b * |q b| * |w b| * |T|
        ≤ Dφ b * (κ / φ b ^ 2) * Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a)) * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hqb hD0) hwb
            (abs_nonneg _) (by positivity)) hT (abs_nonneg _) (by positivity)
      _ = Dφ b * (κ / φ b ^ 2)
          * Real.sqrt (phaseEnergy w Dw a * Real.exp (κ / φ a)) := by ring
  refine ⟨hmain _ (Real.abs_sin_le_one (φ b)), ?_⟩
  rw [abs_neg]
  exact hmain _ (Real.abs_cos_le_one (φ b))

end GaloisForLFunctions.HTGeometry
