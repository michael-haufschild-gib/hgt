import GaloisForLFunctions.RHTower.SuzukiLatticeCarrierWeight
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The radial exponential carrier has a Hatano–Nelson symbol

Conjugating the nearest-neighbour adjacency by the radial exponential weight multiplies the two
shifts by `e^{±κ}`, so on the far positive half-line the symbol is

`λ_κ(θ) = e^{κ + iθ} + e^{-κ - iθ} = 2 cosh κ cos θ + 2i sinh κ sin θ`,

the Hatano–Nelson ellipse.  Its imaginary part is `2 sinh κ sin θ`, which is nonzero at the quarter
turn whenever the weight is nontrivial — so the symbol leaves the real axis and the conjugated
group cannot be polynomially bounded on both time directions.

The same computation for a finite prime-power adjacency gives the imaginary part
`2 ∑ c_q sinh(κ|q|₁) sin⟨q, θ⟩`: every step with positive coefficient and nonzero length
contributes, and the contributions have distinct Fourier characters.
-/

open Complex Real

noncomputable section

namespace RHTower

/-! ## The single-step symbol -/

/-- The Hatano–Nelson symbol of one weighted step. -/
def hatanoNelsonSymbol (κ θ : ℝ) : ℂ :=
  Complex.exp ((κ : ℂ) + Complex.I * (θ : ℂ)) + Complex.exp (-(κ : ℂ) - Complex.I * (θ : ℂ))

/-- **`(21)`: the symbol traces the Hatano–Nelson ellipse.** -/
theorem hatanoNelsonSymbol_eq (κ θ : ℝ) :
    hatanoNelsonSymbol κ θ
      = (2 * Real.cosh κ * Real.cos θ : ℝ) + Complex.I * (2 * Real.sinh κ * Real.sin θ : ℝ) := by
  have h1 : Complex.exp ((κ : ℂ) + Complex.I * (θ : ℂ))
      = (Real.exp κ : ℂ) * (Complex.cos (θ : ℂ) + Complex.I * Complex.sin (θ : ℂ)) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I from by ring, Complex.exp_mul_I]
    ring
  have h2 : Complex.exp (-(κ : ℂ) - Complex.I * (θ : ℂ))
      = (Real.exp (-κ) : ℂ) * (Complex.cos (θ : ℂ) - Complex.I * Complex.sin (θ : ℂ)) := by
    rw [show -(κ : ℂ) - Complex.I * (θ : ℂ) = ((-κ : ℝ) : ℂ) + (-(θ : ℂ)) * Complex.I from by
      push_cast; ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hatanoNelsonSymbol, h1, h2]
  have hcos : Complex.cos (θ : ℂ) = ((Real.cos θ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos]
  have hsin : Complex.sin (θ : ℂ) = ((Real.sin θ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin]
  rw [hcos, hsin]
  have hch : Real.cosh κ = (Real.exp κ + Real.exp (-κ)) / 2 := Real.cosh_eq κ
  have hsh : Real.sinh κ = (Real.exp κ - Real.exp (-κ)) / 2 := Real.sinh_eq κ
  rw [hch, hsh]
  push_cast
  ring

/-- The imaginary part of the symbol. -/
theorem hatanoNelsonSymbol_im (κ θ : ℝ) :
    (hatanoNelsonSymbol κ θ).im = 2 * Real.sinh κ * Real.sin θ := by
  rw [hatanoNelsonSymbol_eq, Complex.add_im, Complex.ofReal_im, zero_add,
    Complex.I_mul_im, Complex.ofReal_re]

/-- **`(22)`: at the quarter turn the symbol is purely imaginary and nonzero.** -/
theorem hatanoNelsonSymbol_quarter (κ : ℝ) :
    hatanoNelsonSymbol κ (Real.pi / 2) = Complex.I * (2 * Real.sinh κ : ℝ) := by
  rw [hatanoNelsonSymbol_eq, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

/-- A nontrivial radial weight pushes the symbol off the real axis. -/
theorem hatanoNelsonSymbol_im_ne_zero {κ : ℝ} (hκ : 0 < κ) :
    (hatanoNelsonSymbol κ (Real.pi / 2)).im ≠ 0 := by
  rw [hatanoNelsonSymbol_im, Real.sin_pi_div_two, mul_one]
  have hsh : 0 < Real.sinh κ := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-κ) < Real.exp κ := Real.exp_lt_exp.mpr (by linarith)
    linarith
  positivity

/-! ## The finite prime-power symbol -/

/-- The symbol of a finite weighted prime-power adjacency. -/
def primeStepSymbol {ι : Type*} [Fintype ι] (c₀ : ℝ) (Q : Finset (ι → ℤ))
    (c : (ι → ℤ) → ℝ) (κ : ℝ) (θ : ι → ℝ) : ℂ :=
  (c₀ : ℂ) + ∑ q ∈ Q, (c q : ℂ) *
    (Complex.exp ((κ * (latticeL1 q : ℝ) : ℝ) + Complex.I * ((∑ i, (q i : ℝ) * θ i : ℝ) : ℂ))
      + Complex.exp (-((κ * (latticeL1 q : ℝ) : ℝ) : ℂ)
        - Complex.I * ((∑ i, (q i : ℝ) * θ i : ℝ) : ℂ)))

/-- **`(24)`: the imaginary part of the finite symbol is the weighted sine polynomial.** -/
theorem primeStepSymbol_im {ι : Type*} [Fintype ι] (c₀ : ℝ) (Q : Finset (ι → ℤ))
    (c : (ι → ℤ) → ℝ) (κ : ℝ) (θ : ι → ℝ) :
    (primeStepSymbol c₀ Q c κ θ).im
      = ∑ q ∈ Q, c q * (2 * Real.sinh (κ * (latticeL1 q : ℝ))
          * Real.sin (∑ i, (q i : ℝ) * θ i)) := by
  rw [primeStepSymbol]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hsym := hatanoNelsonSymbol_eq (κ * (latticeL1 q : ℝ)) (∑ i, (q i : ℝ) * θ i)
  rw [hatanoNelsonSymbol] at hsym
  rw [Complex.im_ofReal_mul, hsym, Complex.add_im, Complex.ofReal_im, zero_add,
    Complex.I_mul_im, Complex.ofReal_re]

end RHTower
