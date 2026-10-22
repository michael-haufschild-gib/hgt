import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalHingeBoundaryTailGreenLaw

/-!
# Suzuki causal Weil--Robin Green identity

Two source-level integrations by parts convert Suzuki's one-sided screw exterior into the causal
exterior of the completed Weil distribution `K = -g''` plus one Robin boundary current.  The
universal `z^(2 : ℕ)` in centered Xi projective denominator cancels the screw primitive exactly:

`z^(2 : ℕ) R_g = exp(I*a*z) * (I*z*U(a) - U'(a)) + E_K`.

This module formalizes denominator-matching algebra, exact recovery of delayed-hinge boundary--tail
law, and compound-denominator connector.  Analytic integrations and distributional source
identification are proved on paper.  No RH premise, positivity hypothesis, estimate, numerical
computation, or Xi-zero data is used.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Denominator-matched Robin reconstruction -/

/-- Closed form obtained from two integrations by parts before multiplying by `z^(2 : ℕ)`.  `U` and
`Uprime` are right endpoint convolution jets; `weilExterior` is causal exterior transform of
`K=-g''`. -/
def suzukiCausalWeilRobinReconstruction
    (a : ℝ) (U Uprime weilExterior z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (a : ℂ)) *
      (-U / (Complex.I * z) + Uprime / (Complex.I * z) ^ (2 : ℕ)) -
    weilExterior / (Complex.I * z) ^ (2 : ℕ)

/-- **Causal Weil--Robin Green identity, algebraic core.**  Multiplication by `z^(2 : ℕ)` removes both
primitive denominators and leaves exactly Robin current plus completed Weil exterior. -/
theorem z_sq_mul_suzukiCausalWeilRobinReconstruction
    (a : ℝ) (U Uprime weilExterior z : ℂ) (hz : z ≠ 0) :
    z ^ (2 : ℕ) * suzukiCausalWeilRobinReconstruction a U Uprime weilExterior z =
      Complex.exp (Complex.I * z * (a : ℂ)) *
          (Complex.I * z * U - Uprime) + weilExterior := by
  simp only [suzukiCausalWeilRobinReconstruction]
  field_simp [hz, Complex.I_ne_zero]
  norm_num [pow_two]
  ring

/-- The completed Weil exterior is uniquely determined after screw exterior and endpoint Robin
jets are fixed. -/
theorem suzukiCausalWeilRobinExterior_unique
    (a : ℝ) (U Uprime E₁ E₂ z : ℂ) (hz : z ≠ 0)
    (h : suzukiCausalWeilRobinReconstruction a U Uprime E₁ z =
      suzukiCausalWeilRobinReconstruction a U Uprime E₂ z) :
    E₁ = E₂ := by
  have hscaled := congrArg (fun w : ℂ => z ^ (2 : ℕ) * w) h
  change z ^ (2 : ℕ) * suzukiCausalWeilRobinReconstruction a U Uprime E₁ z =
    z ^ (2 : ℕ) * suzukiCausalWeilRobinReconstruction a U Uprime E₂ z at hscaled
  rw [z_sq_mul_suzukiCausalWeilRobinReconstruction a U Uprime E₁ z hz,
    z_sq_mul_suzukiCausalWeilRobinReconstruction a U Uprime E₂ z hz] at hscaled
  exact add_left_cancel hscaled

/-! ## Exact delayed-hinge recovery -/

/-- Distributional specialization `K=-delta_ell`: the Weil exterior is the negative delayed
upper Fourier tail. -/
def suzukiDelayedHingeWeilExterior
    (ell : ℝ) (Whigh z : ℂ) : ℂ :=
  -Complex.exp (Complex.I * z * (ell : ℂ)) * Whigh

/-- The Robin reconstruction with hinge endpoint moments equals the already proved hinge
boundary--tail exterior. -/
theorem suzukiCausalWeilRobinReconstruction_delayedHinge
    (a ell : ℝ) (Whigh A B z : ℂ) (hz : z ≠ 0) :
    suzukiCausalWeilRobinReconstruction a A B
        (suzukiDelayedHingeWeilExterior ell Whigh z) z =
      -Complex.exp (Complex.I * z * (ell : ℂ)) * Whigh / z ^ (2 : ℕ) -
        Complex.exp (Complex.I * z * (a : ℂ)) *
          (A / (Complex.I * z) + B / z ^ (2 : ℕ)) := by
  simp only [suzukiCausalWeilRobinReconstruction, suzukiDelayedHingeWeilExterior]
  field_simp [hz, Complex.I_ne_zero]
  norm_num [pow_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Hinge compatibility square.**  Multiplying exact boundary--tail law by `z^(2 : ℕ)` gives Robin
current `exp(I*a*z)(I*z*A-B)` plus distributional Weil exterior
`-exp(I*z*ell)Whigh`. -/
theorem z_sq_mul_suzukiDelayedHingeExteriorFromCut_eq_weilRobin
    (a ell : ℝ) (Wlow Whigh A B z : ℂ) (hz : z ≠ 0) :
    z ^ (2 : ℕ) * suzukiDelayedHingeExteriorFromCut a ell Wlow Whigh A B z =
      Complex.exp (Complex.I * z * (a : ℂ)) *
          (Complex.I * z * A - B) +
        suzukiDelayedHingeWeilExterior ell Whigh z := by
  rw [suzukiDelayedHingeExteriorFromCut_eq_boundaryTail a ell Wlow Whigh A B z hz]
  simp only [suzukiDelayedHingeWeilExterior]
  field_simp [hz, Complex.I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Compound denominator connector -/

/-- The channel already assembled after `z^(2 : ℕ)` denominator cancellation. -/
def suzukiCausalWeilRobinCompletedChannel
    (a : ℝ) (U Uprime weilExterior z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (a : ℂ)) *
      (Complex.I * z * U - Uprime) + weilExterior

/-- Centered Xi denominator `z^(2 : ℕ)*Xi` converts screw exterior into `Xi` times completed
Weil--Robin channel. -/
theorem suzukiXiDenominator_mul_weilRobinReconstruction
    (a : ℝ) (U Uprime weilExterior Xi z : ℂ) (hz : z ≠ 0) :
    (z ^ (2 : ℕ) * Xi) * suzukiCausalWeilRobinReconstruction a U Uprime weilExterior z =
      Xi * suzukiCausalWeilRobinCompletedChannel a U Uprime weilExterior z := by
  rw [show (z ^ (2 : ℕ) * Xi) * suzukiCausalWeilRobinReconstruction
      a U Uprime weilExterior z =
      Xi * (z ^ (2 : ℕ) * suzukiCausalWeilRobinReconstruction
        a U Uprime weilExterior z) by ring,
    z_sq_mul_suzukiCausalWeilRobinReconstruction a U Uprime weilExterior z hz]
  rfl

/-- Exact connector in full compound denominator `P*(z^(2 : ℕ)*Xi)`.  No characteristic division is
used. -/
theorem suzukiCompoundDenominator_mul_weilRobinReconstruction
    (a : ℝ) (U Uprime weilExterior P Xi z : ℂ) (hz : z ≠ 0) :
    (P * (z ^ (2 : ℕ) * Xi)) *
        suzukiCausalWeilRobinReconstruction a U Uprime weilExterior z =
      P * Xi * suzukiCausalWeilRobinCompletedChannel a U Uprime weilExterior z := by
  rw [show (P * (z ^ (2 : ℕ) * Xi)) *
      suzukiCausalWeilRobinReconstruction a U Uprime weilExterior z =
      P * ((z ^ (2 : ℕ) * Xi) *
        suzukiCausalWeilRobinReconstruction a U Uprime weilExterior z) by ring,
    suzukiXiDenominator_mul_weilRobinReconstruction
      a U Uprime weilExterior Xi z hz]
  ring

end

end RHTower
