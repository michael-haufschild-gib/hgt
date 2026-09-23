import GaloisForLFunctions.HTGeometry.HermiteOrthogonality

/-!
# Origin values of the normalized self-dual Hermite functions

The Hermite functions `h_n = p_n · e^{−πx²}` adapted to the self-dual Gaussian obey the Appell law
`p_{n+1}' = 2(n+1) p_n`, which turns the defining step `p_{n+1} = 2X p_n − p_n'/(2π)` into the
two-step origin recursion

```text
p_{n+2}(0) = −((n+1)/π) p_n(0) ,     p_0(0) = 1 ,  p_1(0) = 0 .
```

Their `L²` masses come from the oscillator recursion `⟨h_{n+1}, h_{n+1}⟩ = ((n+1)/π)⟨h_n, h_n⟩`
started at the Gauss integral `⟨h_0, h_0⟩ = 1/√2`, giving `‖h_n‖² = n!/(πⁿ√2)`.

Dividing one by the square root of the other gives the value at the origin of the `n`-th member of
the orthonormal Hermite basis.  Its square is a rational multiple of `√2` with all powers of `π`
cancelled:

```text
n = 0 : √2 ,   n = 2 : √2/2 ,   n = 4 : 3√2/8 ,   n = 6 : 5√2/16 .
```
-/

open Polynomial MeasureTheory

open scoped Real

noncomputable section

namespace GaloisForLFunctions

/-! ## The Appell law -/

theorem polyC_two : (Polynomial.C (2 : ℝ)) = 2 := map_ofNat Polynomial.C 2

/-- **Appell law for the self-dual Hermite polynomials**: `p_{n+1}' = 2(n+1) p_n`. -/
theorem derivative_hermitePoly_succ (n : ℕ) :
    Polynomial.derivative (hermitePoly (n + 1))
      = Polynomial.C (2 * ((n : ℝ) + 1)) * hermitePoly n := by
  induction n with
  | zero =>
    rw [hermitePoly_succ, hermiteStep, hermitePoly_zero]
    simp [polyC_two]
  | succ m ih =>
    have hstep : hermitePoly (m + 1)
        = 2 * Polynomial.X * hermitePoly m
          - Polynomial.C (1 / (2 * π)) * Polynomial.derivative (hermitePoly m) := by
      rw [hermitePoly_succ, hermiteStep]
    have hC : Polynomial.C (2 * (((m : ℕ) : ℝ) + 1 + 1))
        = Polynomial.C (2 * ((m : ℝ) + 1)) + 2 := by
      simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1, polyC_two]
      ring
    rw [hermitePoly_succ (m + 1), hermiteStep, derivative_sub, derivative_mul, derivative_mul,
      ih, Polynomial.derivative_C_mul, Polynomial.derivative_C_mul]
    simp only [Polynomial.derivative_X, Polynomial.derivative_ofNat, mul_one, zero_mul, zero_add]
    push_cast
    rw [hC, hstep]
    ring

/-! ## Values at the origin -/

theorem eval_zero_hermitePoly_zero : (hermitePoly 0).eval 0 = 1 := by
  rw [hermitePoly_zero]
  simp

theorem eval_zero_hermitePoly_one : (hermitePoly 1).eval 0 = 0 := by
  rw [hermitePoly_succ, hermiteStep, hermitePoly_zero]
  simp

/-- The two-step origin recursion. -/
theorem eval_zero_hermitePoly_add_two (n : ℕ) :
    (hermitePoly (n + 2)).eval 0 = -(((n : ℝ) + 1) / π) * (hermitePoly n).eval 0 := by
  have hstep : hermitePoly (n + 2)
      = 2 * Polynomial.X * hermitePoly (n + 1)
        - Polynomial.C (1 / (2 * π)) * Polynomial.derivative (hermitePoly (n + 1)) := by
    rw [hermitePoly_succ, hermiteStep]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [hstep, derivative_hermitePoly_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, mul_zero, zero_mul, zero_sub]
  field_simp

theorem eval_zero_hermitePoly_two : (hermitePoly 2).eval 0 = -(1 / π) := by
  have h := eval_zero_hermitePoly_add_two 0
  rw [eval_zero_hermitePoly_zero] at h
  rw [show (2 : ℕ) = 0 + 2 from rfl, h]
  norm_num

theorem eval_zero_hermitePoly_four : (hermitePoly 4).eval 0 = 3 / π ^ (2 : ℕ) := by
  have h := eval_zero_hermitePoly_add_two 2
  rw [eval_zero_hermitePoly_two] at h
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [show (4 : ℕ) = 2 + 2 from rfl, h]
  push_cast
  field_simp
  ring

theorem eval_zero_hermitePoly_six : (hermitePoly 6).eval 0 = -(15 / π ^ (3 : ℕ)) := by
  have h := eval_zero_hermitePoly_add_two 4
  rw [eval_zero_hermitePoly_four] at h
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [show (6 : ℕ) = 4 + 2 from rfl, h]
  push_cast
  field_simp
  ring

/-! ## `L²` masses -/

/-- The exact `L²` mass of the `n`-th self-dual Hermite function: `n!/(πⁿ√2)`. -/
theorem schwartzPair_hermiteSchwartz_self_eq (n : ℕ) :
    schwartzPair (hermiteSchwartz n) (hermiteSchwartz n)
      = ((((Nat.factorial n : ℝ)) / ((π : ℝ) ^ n * Real.sqrt 2) : ℝ) : ℂ) := by
  induction n with
  | zero =>
    rw [hermiteSchwartz_zero, schwartzPair_gaussianSchwartz_self]
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hhalf : (π : ℝ) / (2 * π) = 2⁻¹ := by field_simp
    have hval : Real.sqrt ((π : ℝ) / (2 * π)) = (Real.sqrt 2)⁻¹ := by
      rw [hhalf, Real.sqrt_inv]
    rw [hval]
    norm_num
  | succ n ih =>
    rw [schwartzPair_hermiteSchwartz_self_succ, ih]
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hpic : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    have hs2c : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs2
    have hpowc : ((π : ℂ)) ^ n ≠ 0 := pow_ne_zero _ hpic
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The squared `L²` norm of the `n`-th self-dual Hermite function. -/
theorem norm_hermiteSchwartz_toLp_sq (n : ℕ) :
    ‖(hermiteSchwartz n).toLp 2 volume‖ ^ (2 : ℕ)
      = (Nat.factorial n : ℝ) / ((π : ℝ) ^ n * Real.sqrt 2) := by
  have hinner : inner ℂ ((hermiteSchwartz n).toLp 2 volume) ((hermiteSchwartz n).toLp 2 volume)
      = ((‖(hermiteSchwartz n).toLp 2 volume‖ : ℂ)) ^ (2 : ℕ) :=
    inner_self_eq_norm_sq_to_K _
  rw [inner_hermiteSchwartz_toLp, schwartzPair_hermiteSchwartz_self_eq] at hinner
  have : ((((Nat.factorial n : ℝ)) / ((π : ℝ) ^ n * Real.sqrt 2) : ℝ) : ℂ)
      = ((‖(hermiteSchwartz n).toLp 2 volume‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [hinner]
    push_cast
    ring
  exact_mod_cast this.symm

theorem norm_hermiteSchwartz_toLp_pos (n : ℕ) :
    0 < ‖(hermiteSchwartz n).toLp 2 volume‖ :=
  norm_pos_iff.mpr (hermiteSchwartz_toLp_ne_zero n)

/-! ## The origin value of the orthonormal Hermite basis -/

/-- The value at the origin of the `n`-th member of the orthonormal Hermite basis. -/
def hermiteOriginValue (n : ℕ) : ℝ :=
  (hermitePoly n).eval 0 / ‖(hermiteSchwartz n).toLp 2 volume‖

/-- The squared origin value, with every power of `π` still visible. -/
theorem hermiteOriginValue_sq (n : ℕ) :
    hermiteOriginValue n ^ (2 : ℕ)
      = ((hermitePoly n).eval 0) ^ (2 : ℕ) * ((π : ℝ) ^ n * Real.sqrt 2) / (Nat.factorial n : ℝ) := by
  have hnorm := norm_hermiteSchwartz_toLp_sq n
  have hpos := norm_hermiteSchwartz_toLp_pos n
  have hfact : ((Nat.factorial n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hermiteOriginValue, div_pow, hnorm]
  field_simp

theorem hermiteOriginValue_sq_zero : hermiteOriginValue 0 ^ (2 : ℕ) = Real.sqrt 2 := by
  rw [hermiteOriginValue_sq, eval_zero_hermitePoly_zero]
  norm_num

theorem hermiteOriginValue_sq_two : hermiteOriginValue 2 ^ (2 : ℕ) = Real.sqrt 2 / 2 := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [hermiteOriginValue_sq, eval_zero_hermitePoly_two]
  norm_num [Nat.factorial]

theorem hermiteOriginValue_sq_four : hermiteOriginValue 4 ^ (2 : ℕ) = 3 * Real.sqrt 2 / 8 := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [hermiteOriginValue_sq, eval_zero_hermitePoly_four]
  norm_num [Nat.factorial]
  field_simp
  ring

theorem hermiteOriginValue_sq_six : hermiteOriginValue 6 ^ (2 : ℕ) = 5 * Real.sqrt 2 / 16 := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [hermiteOriginValue_sq, eval_zero_hermitePoly_six]
  norm_num [Nat.factorial]
  field_simp
  ring

end GaloisForLFunctions

end
