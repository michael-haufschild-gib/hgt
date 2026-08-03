import GaloisForLFunctions.RHTower.Sieve.MultiplicativeDistance

/-!
# The Euler product is damped by the distance

The elementary bound behind Halász's mechanism is

`‖1 + z‖ ≤ exp(Re z + ‖z‖²)`,

which holds for **every** complex `z` with no smallness hypothesis: squaring, the left side is
`1 + 2 Re z + ‖z‖²`, which is at most `1 + 2 Re z + 2‖z‖²`, and `1 + u ≤ exp u`.

Taken over a finite set of primes with `z_p = f(p) p^{-it}/p` this reads

`∏_{p ∈ P} ‖1 + f(p) p^{-it}/p‖ ≤ exp(∑_{p ∈ P} 1/p + ∑_{p ∈ P} 1/p² - D(f,t;P)²)`,

because `∑_p Re(z_p) = ∑_p 1/p - D(f,t;P)²` by the definition of the distance.  So the Euler product
is smaller than its trivial size by `exp(-D²)`: a multiplicative function far from every character
has a small product, and the distance is exactly the exponential rate.  This is the structural
reason Halász's theorem is stated in terms of `D`.
-/

namespace RHTower.Sieve

open Finset

/-- **`‖1 + z‖ ≤ exp(Re z + ‖z‖²)`, for every `z`.** -/
theorem norm_one_add_le_exp (z : ℂ) : ‖1 + z‖ ≤ Real.exp (z.re + ‖z‖ ^ 2) := by
  have h1 : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    ring
  have hlin : 2 * z.re + 2 * ‖z‖ ^ 2 + 1 ≤ Real.exp (2 * z.re + 2 * ‖z‖ ^ 2) :=
    Real.add_one_le_exp _
  have hsq : Real.exp (z.re + ‖z‖ ^ 2) ^ 2 = Real.exp (2 * z.re + 2 * ‖z‖ ^ 2) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hz2 : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hle : ‖1 + z‖ ^ 2 ≤ Real.exp (z.re + ‖z‖ ^ 2) ^ 2 := by rw [hsq]; linarith
  have h2 := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (Real.exp_nonneg _)] at h2

/-- The product form. -/
theorem prod_norm_one_add_le_exp {ι : Type*} (P : Finset ι) (z : ι → ℂ) :
    ∏ p ∈ P, ‖1 + z p‖ ≤ Real.exp (∑ p ∈ P, ((z p).re + ‖z p‖ ^ 2)) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => norm_one_add_le_exp (z p)

/-- The real part of a real multiple. -/
theorem re_ofReal_mul (c : ℝ) (w : ℂ) : (((c : ℂ)) * w).re = c * w.re := by
  simp [Complex.mul_re]

/-- The norm of a real multiple. -/
theorem norm_ofReal_mul (c : ℝ) (w : ℂ) : ‖((c : ℂ)) * w‖ = |c| * ‖w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The distance is the deficit of the real parts against `∑ 1/p`. -/
theorem sum_re_eq_sub_mulDistSq (f : ℕ → ℂ) (t : ℝ) (P : Finset ℕ) :
    ∑ p ∈ P, (((1 / (p : ℝ) : ℝ) : ℂ)
        * (f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I))).re
      = (∑ p ∈ P, 1 / (p : ℝ)) - mulDistSq f t P := by
  rw [mulDistSq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [re_ofReal_mul]
  ring

/-- **The Euler product is damped by the squared distance.** -/
theorem prod_euler_factor_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 0 < p) :
    ∏ p ∈ P, ‖1 + ((1 / (p : ℝ) : ℝ) : ℂ)
        * (f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I))‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - mulDistSq f t P) := by
  set z : ℕ → ℂ := fun p => ((1 / (p : ℝ) : ℝ) : ℂ)
    * (f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)) with hzdef
  have hnorm : ∀ p ∈ P, ‖z p‖ ^ 2 ≤ 1 / (p : ℝ) ^ 2 := by
    intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    have hw : ‖f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hf p
    have hzp : ‖z p‖ ≤ 1 / (p : ℝ) := by
      rw [hzdef]
      simp only
      rw [norm_ofReal_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
      calc 1 / (p : ℝ) * ‖f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)‖
          ≤ 1 / (p : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hw (by positivity)
        _ = 1 / (p : ℝ) := by ring
    have h0 : (0 : ℝ) ≤ ‖z p‖ := norm_nonneg _
    calc ‖z p‖ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ h0 hzp 2
      _ = 1 / (p : ℝ) ^ 2 := by rw [div_pow, one_pow]
  refine le_trans (prod_norm_one_add_le_exp P z) ?_
  refine Real.exp_le_exp.mpr ?_
  rw [Finset.sum_add_distrib, sum_re_eq_sub_mulDistSq f t P]
  have := Finset.sum_le_sum hnorm
  linarith

end RHTower.Sieve
