import GaloisForLFunctions.HTGeometry.BohrMeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A differentially algebraic function that is not recurrent

`sin(s e^s)` is differentially algebraic over `ℂ(s)`: eliminating `e^s` and `cos(s e^s)` from the
first two derivatives leaves the second-order polynomial relation

`(1+s)(1 − y²) y″ − (2+s)(1 − y²) y′ + (1+s) y (y′)² = 0`,

which holds at every point of the plane.  Yet on every vertical line the function is unbounded — at
the parameters `t = 2πn` the argument `s e^s` has imaginary part `2πn e^σ` — so it is not Bohr almost
periodic there.

Differential algebraicity, finite order and zero density therefore do not imply the recurrence
hypothesis of the finite-phase law; that hypothesis is load-bearing.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- The function `sin(s e^s)`. -/
noncomputable def sinExp (s : ℂ) : ℂ := Complex.sin (s * Complex.exp s)

/-- Its restriction to the vertical line `Re s = σ`. -/
noncomputable def sinExpLine (σ t : ℝ) : ℂ := sinExp ((σ : ℂ) + (t : ℂ) * Complex.I)

theorem hasDerivAt_mul_exp (s : ℂ) :
    HasDerivAt (fun z : ℂ => z * Complex.exp z) (Complex.exp s * (1 + s)) s := by
  have h := (hasDerivAt_id s).mul (Complex.hasDerivAt_exp s)
  refine h.congr_deriv ?_
  simp only [id_eq]
  ring

theorem hasDerivAt_sinExp (s : ℂ) :
    HasDerivAt sinExp
      (Complex.cos (s * Complex.exp s) * (Complex.exp s * (1 + s))) s :=
  (Complex.hasDerivAt_sin _).comp s (hasDerivAt_mul_exp s)

theorem deriv_sinExp :
    deriv sinExp = fun s : ℂ => Complex.cos (s * Complex.exp s) * (Complex.exp s * (1 + s)) := by
  funext s
  exact (hasDerivAt_sinExp s).deriv

theorem hasDerivAt_deriv_sinExp (s : ℂ) :
    HasDerivAt (deriv sinExp)
      (-Complex.sin (s * Complex.exp s) * (Complex.exp s * (1 + s)) ^ 2
        + Complex.cos (s * Complex.exp s) * (Complex.exp s * (2 + s))) s := by
  rw [deriv_sinExp]
  have hcos : HasDerivAt (fun z : ℂ => Complex.cos (z * Complex.exp z))
      (-Complex.sin (s * Complex.exp s) * (Complex.exp s * (1 + s))) s :=
    (Complex.hasDerivAt_cos _).comp s (hasDerivAt_mul_exp s)
  have hlin : HasDerivAt (fun z : ℂ => Complex.exp z * (1 + z))
      (Complex.exp s * (2 + s)) s := by
    have h := (Complex.hasDerivAt_exp s).mul ((hasDerivAt_const s (1 : ℂ)).add (hasDerivAt_id s))
    refine h.congr_deriv ?_
    simp only [Pi.add_apply, id_eq]
    ring
  refine (hcos.mul hlin).congr_deriv ?_
  ring

theorem deriv_deriv_sinExp (s : ℂ) :
    deriv (deriv sinExp) s
      = -Complex.sin (s * Complex.exp s) * (Complex.exp s * (1 + s)) ^ 2
        + Complex.cos (s * Complex.exp s) * (Complex.exp s * (2 + s)) :=
  (hasDerivAt_deriv_sinExp s).deriv

/-- **`sin(s e^s)` is differentially algebraic over `ℂ(s)`.**  The relation is polynomial in the jet
with rational coefficients, and holds at every point. -/
theorem sinExp_differentialAlgebraic (s : ℂ) :
    (1 + s) * (1 - sinExp s ^ 2) * deriv (deriv sinExp) s
        - (2 + s) * (1 - sinExp s ^ 2) * deriv sinExp s
        + (1 + s) * sinExp s * (deriv sinExp s) ^ 2 = 0 := by
  have hpy : 1 - Complex.sin (s * Complex.exp s) ^ 2 = Complex.cos (s * Complex.exp s) ^ 2 := by
    have := Complex.sin_sq_add_cos_sq (s * Complex.exp s)
    linear_combination -this
  rw [deriv_deriv_sinExp, deriv_sinExp, sinExp, hpy]
  ring

/-- A lower bound for the modulus of the complex sine in terms of its imaginary part. -/
theorem norm_sin_ge (z : ℂ) : (Real.exp z.im - Real.exp (-z.im)) / 2 ≤ ‖Complex.sin z‖ := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h3 := norm_sub_norm_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  rw [h1, h2] at h3
  have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hn2]
  linarith

/-- At the sample parameters `t = 2πn` the exponential returns to a real value. -/
theorem exp_line_sample (σ : ℝ) (n : ℕ) :
    Complex.exp ((σ : ℂ) + ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)
      = ((Real.exp σ : ℝ) : ℂ) := by
  rw [Complex.exp_add, Complex.ofReal_exp]
  have hkey : ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I
      = ((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hkey, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem im_sample_argument (σ : ℝ) (n : ℕ) :
    (((σ : ℂ) + ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)
      * Complex.exp ((σ : ℂ) + ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)).im
      = 2 * Real.pi * n * Real.exp σ := by
  rw [exp_line_sample]
  have hsplit : ((σ : ℂ) + ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I) * ((Real.exp σ : ℝ) : ℂ)
      = ((σ * Real.exp σ : ℝ) : ℂ)
        + ((2 * Real.pi * n * Real.exp σ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The line restriction is unbounded.**  Its modulus at `t = 2πn` grows at least like `πn e^σ`. -/
theorem exists_norm_sinExpLine_gt (σ : ℝ) (C : ℝ) : ∃ t : ℝ, C < ‖sinExpLine σ t‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (Real.pi * Real.exp σ))
  refine ⟨2 * Real.pi * n, ?_⟩
  set y : ℝ := 2 * Real.pi * n * Real.exp σ with hy
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp : 0 < Real.exp σ := Real.exp_pos σ
  have hy0 : 0 ≤ y := by positivity
  have hlow : y / 2 ≤ (Real.exp y - Real.exp (-y)) / 2 := by
    have h1 : 1 + y ≤ Real.exp y := Real.add_one_le_exp y |>.trans_eq' (by ring)
    have h2 : Real.exp (-y) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    linarith
  have hbound : y / 2 ≤ ‖sinExpLine σ (2 * Real.pi * n)‖ := by
    refine le_trans hlow ?_
    have h := norm_sin_ge (((σ : ℂ) + ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)
      * Complex.exp ((σ : ℂ) + ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I))
    rwa [im_sample_argument σ n, ← hy] at h
  refine lt_of_lt_of_le ?_ hbound
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < Real.pi * Real.exp σ)] at hn
  rw [hy]
  nlinarith [hn, hpi, hexp]

theorem continuous_sinExpLine (σ : ℝ) : Continuous (sinExpLine σ) := by
  unfold sinExpLine sinExp
  fun_prop

/-- **Differential algebraicity does not imply recurrence.**  `sin(s e^s)` is not Bohr almost
periodic on any vertical line. -/
theorem not_isBohrAlmostPeriodic_sinExpLine (σ : ℝ) :
    ¬ HTGeometry.IsBohrAlmostPeriodic (sinExpLine σ) := by
  intro hap
  obtain ⟨C, hC⟩ := exists_bound_of_isBohrAlmostPeriodic (continuous_sinExpLine σ) hap
  obtain ⟨t, ht⟩ := exists_norm_sinExpLine_gt σ C
  exact absurd (hC t) (not_le_of_gt ht)

end GaloisForLFunctions
