import Mathlib

/-!
# Rotating quadratic action, positive erasure, and the metaplectic history

The one-parameter family of quadratic actions `S_θ(z) = ½ e^{iθ} z²` has a critical locus, a
positive Hessian shadow and an unoriented steepest-descent line that are all `2π`-periodic in `θ`,
while the oriented line and the Gaussian amplitude reverse sign after one loop and close only after
two.  The missing datum is exactly the square-root lift of a loop in the space of nondegenerate
quadratic laws.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section MetaplecticAction

/-- The rotating quadratic action, equation (1). -/
noncomputable def rotatingAction (θ : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * z ^ (2 : ℕ)

/-- The oriented steepest-descent line, equation (2). -/
noncomputable def descentLine (θ : ℝ) (y : ℝ) : ℂ :=
  Complex.exp ((-(θ / 2) : ℂ) * Complex.I) * y

/-- The complex Hessian of the rotating action. -/
noncomputable def rotatingHessian (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem rotatingHessian_ne_zero (θ : ℝ) : rotatingHessian θ ≠ 0 :=
  Complex.exp_ne_zero _

/-! ### Clause 1 — the critical locus -/

theorem rotatingAction_hasDerivAt (θ : ℝ) (z : ℂ) :
    HasDerivAt (rotatingAction θ) (rotatingHessian θ * z) z := by
  have h : HasDerivAt (fun z : ℂ => z ^ (2 : ℕ)) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z)
  have h2 := h.const_mul ((1 / 2 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  have hcoe : (1 / 2 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * (2 * z)
      = rotatingHessian θ * z := by
    rw [rotatingHessian]; ring
  rw [hcoe] at h2
  exact h2

theorem deriv_rotatingAction (θ : ℝ) (z : ℂ) :
    deriv (rotatingAction θ) z = rotatingHessian θ * z :=
  (rotatingAction_hasDerivAt θ z).deriv

/-- **Clause 1.**  The critical locus of the rotating action is the origin, for every `θ`. -/
theorem crit_rotatingAction (θ : ℝ) :
    {z : ℂ | deriv (rotatingAction θ) z = 0} = {0} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, deriv_rotatingAction]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (rotatingHessian_ne_zero θ)
    · exact h1
  · intro h
    rw [h, mul_zero]

/-! ### Clause 2 — the Hessian and its positive Gram shadow -/

theorem deriv_rotatingAction_eq (θ : ℝ) :
    deriv (rotatingAction θ) = fun z : ℂ => rotatingHessian θ * z :=
  funext (deriv_rotatingAction θ)

/-- **Clause 2, first half.**  The second derivative is the constant `e^{iθ}`. -/
theorem secondDeriv_rotatingAction (θ : ℝ) (z : ℂ) :
    deriv (deriv (rotatingAction θ)) z = rotatingHessian θ := by
  rw [deriv_rotatingAction_eq]
  simp

/-- **Clause 2, second half.**  The positive Gram shadow of the Hessian is identically one, so it
carries no information about `θ`. -/
theorem rotatingHessian_gram (θ : ℝ) :
    (starRingEnd ℂ) (rotatingHessian θ) * rotatingHessian θ = 1 := by
  rw [rotatingHessian, ← Complex.exp_conj, ← Complex.exp_add]
  have hc : (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc, neg_add_cancel, Complex.exp_zero]

theorem rotatingHessian_norm (θ : ℝ) : ‖rotatingHessian θ‖ = 1 := by
  rw [rotatingHessian]
  have : ((θ : ℂ) * Complex.I) = ((θ : ℝ) : ℂ) * Complex.I := rfl
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-! ### Clause 3 — the line is a steepest-descent cycle -/

/-- **Clause 3.**  Along the oriented line the action is the real Gaussian exponent `y²/2`. -/
theorem rotatingAction_descentLine (θ : ℝ) (y : ℝ) :
    rotatingAction θ (descentLine θ y) = ((y ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  rw [rotatingAction, descentLine, mul_pow, ← Complex.exp_nat_mul]
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((2 : ℕ) * ((-(θ / 2) : ℂ) * Complex.I))
      = 1 := by
    rw [← Complex.exp_add]
    have : (θ : ℂ) * Complex.I + (2 : ℕ) * ((-(θ / 2) : ℂ) * Complex.I) = 0 := by
      push_cast
      ring
    rw [this, Complex.exp_zero]
  calc (1 / 2 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        * (Complex.exp ((2 : ℕ) * ((-(θ / 2) : ℂ) * Complex.I)) * (y : ℂ) ^ (2 : ℕ))
      = (1 / 2 : ℂ)
        * (Complex.exp ((θ : ℂ) * Complex.I)
            * Complex.exp ((2 : ℕ) * ((-(θ / 2) : ℂ) * Complex.I))) * (y : ℂ) ^ (2 : ℕ) := by ring
    _ = ((y ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by rw [hexp]; push_cast; ring

/-- The oriented parametrization has constant derivative `e^{-iθ/2}`; the amplitude below really is
the pullback line integral along it. -/
theorem descentLine_hasDerivAt (θ : ℝ) (y : ℝ) :
    HasDerivAt (descentLine θ) (Complex.exp ((-(θ / 2) : ℂ) * Complex.I)) y := by
  have h : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 y := Complex.ofRealCLM.hasDerivAt
  have h2 := h.const_mul (Complex.exp ((-(θ / 2) : ℂ) * Complex.I))
  rw [mul_one] at h2
  exact h2

/-! ### Clause 4 — the oriented Gaussian amplitude -/

/-- The oriented Gaussian amplitude, equation (3), as the pullback of `e^{-S}dz` along the oriented
parametrization. -/
noncomputable def thimbleAmplitude (θ : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (-(rotatingAction θ (descentLine θ y)))
    * Complex.exp ((-(θ / 2) : ℂ) * Complex.I)

theorem gaussian_integral_half : ∫ y : ℝ, Real.exp (-(y ^ (2 : ℕ) / 2)) = Real.sqrt (2 * Real.pi) := by
  have hfun : (fun y : ℝ => Real.exp (-(y ^ (2 : ℕ) / 2)))
      = fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y ^ (2 : ℕ)) := by
    funext y; ring_nf
  rw [hfun, integral_gaussian]
  congr 1
  ring

/-- **Clause 4.**  `Z(θ) = √(2π) e^{-iθ/2}`. -/
theorem thimbleAmplitude_eq (θ : ℝ) :
    thimbleAmplitude θ
      = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp ((-(θ / 2) : ℂ) * Complex.I) := by
  rw [thimbleAmplitude]
  have hfun : (fun y : ℝ => Complex.exp (-(rotatingAction θ (descentLine θ y)))
        * Complex.exp ((-(θ / 2) : ℂ) * Complex.I))
      = fun y : ℝ => ((Real.exp (-(y ^ (2 : ℕ) / 2)) : ℝ) : ℂ)
        * Complex.exp ((-(θ / 2) : ℂ) * Complex.I) := by
    funext y
    rw [rotatingAction_descentLine, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hfun, integral_mul_const, integral_complex_ofReal, gaussian_integral_half]

theorem thimbleAmplitude_ne_zero (θ : ℝ) : thimbleAmplitude θ ≠ 0 := by
  rw [thimbleAmplitude_eq]
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  have : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast ne_of_gt this

/-! ### Clause 5 — what is `2π`-periodic and what is not -/

theorem rotatingAction_periodic (θ : ℝ) (z : ℂ) :
    rotatingAction (θ + 2 * Real.pi) z = rotatingAction θ z := by
  rw [rotatingAction, rotatingAction]
  congr 2
  have : ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem rotatingHessian_periodic (θ : ℝ) :
    rotatingHessian (θ + 2 * Real.pi) = rotatingHessian θ := by
  have h := rotatingAction_periodic θ 1
  rw [rotatingAction, rotatingAction] at h
  simpa [rotatingHessian] using h

theorem crit_periodic (θ : ℝ) :
    {z : ℂ | deriv (rotatingAction (θ + 2 * Real.pi)) z = 0}
      = {z : ℂ | deriv (rotatingAction θ) z = 0} := by
  rw [crit_rotatingAction, crit_rotatingAction]

/-- **Clause 5, equation (4) second half.**  The oriented parametrization reverses after one
loop. -/
theorem descentLine_add_two_pi (θ : ℝ) (y : ℝ) :
    descentLine (θ + 2 * Real.pi) y = -descentLine θ y := by
  rw [descentLine, descentLine]
  have hsplit : (-(((θ + 2 * Real.pi : ℝ) : ℂ) / 2)) * Complex.I
      = (-((θ : ℂ) / 2)) * Complex.I + ((Real.pi : ℝ) : ℂ) * Complex.I * (-1) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  have hpi : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I * (-1)) = -1 := by
    rw [mul_neg_one, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [hpi]
  ring

/-- The *unoriented* line is `2π`-periodic: only the orientation moves. -/
theorem descentLine_range_add_two_pi (θ : ℝ) :
    Set.range (descentLine (θ + 2 * Real.pi)) = Set.range (descentLine θ) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨-y, ?_⟩
    rw [descentLine_add_two_pi, descentLine, descentLine]
    push_cast
    ring
  · rintro ⟨y, rfl⟩
    refine ⟨-y, ?_⟩
    rw [descentLine_add_two_pi, descentLine, descentLine]
    push_cast
    ring

/-- **Clause 5, equation (4) first half.**  The oriented amplitude changes sign after one loop. -/
theorem thimbleAmplitude_add_two_pi (θ : ℝ) :
    thimbleAmplitude (θ + 2 * Real.pi) = -thimbleAmplitude θ := by
  rw [thimbleAmplitude_eq, thimbleAmplitude_eq]
  have hsplit : (-(((θ + 2 * Real.pi : ℝ) : ℂ) / 2)) * Complex.I
      = (-((θ : ℂ) / 2)) * Complex.I + ((Real.pi : ℝ) : ℂ) * Complex.I * (-1) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  have hpi : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I * (-1)) = -1 := by
    rw [mul_neg_one, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [hpi]
  ring

/-! ### Clause 6 — the oriented history closes only after `4π` -/

theorem thimbleAmplitude_add_four_pi (θ : ℝ) :
    thimbleAmplitude (θ + 4 * Real.pi) = thimbleAmplitude θ := by
  have h1 : θ + 4 * Real.pi = (θ + 2 * Real.pi) + 2 * Real.pi := by ring
  rw [h1, thimbleAmplitude_add_two_pi, thimbleAmplitude_add_two_pi, neg_neg]

theorem thimbleAmplitude_add_two_pi_ne (θ : ℝ) :
    thimbleAmplitude (θ + 2 * Real.pi) ≠ thimbleAmplitude θ := by
  rw [thimbleAmplitude_add_two_pi]
  intro hcon
  have h2 : (2 : ℂ) * thimbleAmplitude θ = 0 := by linear_combination -hcon
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact thimbleAmplitude_ne_zero θ h

/-- **The theorem.**  The action, the critical locus, the positive Hessian shadow and the unoriented
line are all `2π`-periodic, while the oriented parametrization and the Gaussian amplitude reverse
after one loop and close only after two.  Neither the critical locus nor the positive Gram shadow of
the Hessian determines the oriented cycle or its amplitude. -/
theorem positive_shadow_does_not_determine_orientation (θ : ℝ) :
    (∀ z : ℂ, rotatingAction (θ + 2 * Real.pi) z = rotatingAction θ z) ∧
      {z : ℂ | deriv (rotatingAction (θ + 2 * Real.pi)) z = 0}
        = {z : ℂ | deriv (rotatingAction θ) z = 0} ∧
      (starRingEnd ℂ) (rotatingHessian (θ + 2 * Real.pi)) * rotatingHessian (θ + 2 * Real.pi)
        = (starRingEnd ℂ) (rotatingHessian θ) * rotatingHessian θ ∧
      Set.range (descentLine (θ + 2 * Real.pi)) = Set.range (descentLine θ) ∧
      (∀ y : ℝ, descentLine (θ + 2 * Real.pi) y = -descentLine θ y) ∧
      thimbleAmplitude (θ + 2 * Real.pi) = -thimbleAmplitude θ ∧
      thimbleAmplitude (θ + 2 * Real.pi) ≠ thimbleAmplitude θ ∧
      thimbleAmplitude (θ + 4 * Real.pi) = thimbleAmplitude θ :=
  ⟨rotatingAction_periodic θ, crit_periodic θ,
    by rw [rotatingHessian_gram, rotatingHessian_gram],
    descentLine_range_add_two_pi θ, descentLine_add_two_pi θ,
    thimbleAmplitude_add_two_pi θ, thimbleAmplitude_add_two_pi_ne θ,
    thimbleAmplitude_add_four_pi θ⟩

end MetaplecticAction

end GaloisForLFunctions.HTGeometry
