import GaloisForLFunctions.RHTower.EstermannPrincipalPart
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The Mellin integrand of Estermann's zeta and its residue

The exponentially smoothed Perron integrand is `x^{-s} Γ(s) D(s, a/q)`.  Multiplying by `(s-1)²`
removes its only pole in the right half plane:

```text
x^{-s} Γ(s) D(s, a/q) = N(s)/(s-1)²,   N(s) = x^{-s} Γ(s) · (s-1)² D(s, a/q),
```

with `N` holomorphic on `Re s > 0`.  The residue of the integrand at `s = 1` is `N'(1)`, and the
three factors contribute `-log x`, `Γ'(1) = -γ` and the Estermann residue `(2γ - 2 log q)/q`:

```text
N'(1) = (γ - log x - 2 log q)/(q x).
```

With `x = 1/X` this is `(X/q)(log(X/q²) + γ)` — the main term of the smoothed twisted divisor sum.
-/

open Complex

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Replace the derivative value by an equal one. -/
private theorem hasDerivAt_of_eq' {f : ℂ → ℂ} {u v x : ℂ} (h : HasDerivAt f u x) (huv : u = v) :
    HasDerivAt f v x := huv ▸ h

/-- The pole-cleared Mellin integrand `x^{-s} Γ(s) (s-1)² D(s, a/q)`. -/
def estermannMellinNumerator (q : ℕ) [NeZero q] (a : ZMod q) (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (-s) * Complex.Gamma s * estermannEntire q a s

/-- **The numerator is holomorphic on the right half plane.** -/
theorem differentiableOn_estermannMellinNumerator (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    DifferentiableOn ℂ (estermannMellinNumerator q ((a : ZMod q)) x) {z : ℂ | 0 < z.re} := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
  · exact differentiable_const_cpow_neg hx0 z
  · refine Complex.differentiableAt_Gamma z (fun m hm => ?_)
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hzre : 0 < z.re := hz
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  · exact differentiable_estermannEntire a z

/-- **The numerator clears the pole.** -/
theorem estermannMellinNumerator_div (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (x : ℝ) {s : ℂ}
    (hs : s ≠ 1) :
    estermannMellinNumerator q ((a : ZMod q)) x s / (s - 1) ^ 2
      = (x : ℂ) ^ (-s) * Complex.Gamma s * estermannZeta q ((a : ZMod q)) s := by
  have hne : (s - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs)
  rw [estermannMellinNumerator, estermannEntire_eq _ hs]
  field_simp

/-- `Γ'(1) = -γ`. -/
theorem deriv_Gamma_one : deriv Complex.Gamma 1 = -(Real.eulerMascheroniConstant : ℂ) := by
  have h := Complex.digamma_one
  rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_one, div_one] at h
  exact h

/-- **The residue of the smoothed Mellin integrand at `s = 1`.** -/
theorem deriv_estermannMellinNumerator_one (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    deriv (estermannMellinNumerator q ((a : ZMod q)) x) 1
      = ((q : ℂ) * (x : ℂ))⁻¹ *
        ((Real.eulerMascheroniConstant : ℂ) - (Real.log x : ℂ) - 2 * Complex.log (q : ℂ)) := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hq0 : ((q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hlogx : Complex.log ((x : ℝ) : ℂ) = ((Real.log x : ℝ) : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  -- the three factors
  have hneg : HasDerivAt (fun s : ℂ => -s) (-1) 1 := (hasDerivAt_id (1 : ℂ)).neg
  have hcpn : HasDerivAt (fun y : ℂ => ((x : ℝ) : ℂ) ^ y)
      (((x : ℝ) : ℂ) ^ (-(1 : ℂ)) * Complex.log ((x : ℝ) : ℂ)) (-(1 : ℂ)) :=
    (hasStrictDerivAt_const_cpow (Or.inl hx0)).hasDerivAt
  have hu : HasDerivAt (fun s : ℂ => ((x : ℝ) : ℂ) ^ (-s))
      (((x : ℝ) : ℂ)⁻¹ * (Real.log x : ℂ) * (-1)) 1 :=
    hasDerivAt_of_eq' (hcpn.comp 1 hneg) (by rw [Complex.cpow_neg_one, hlogx])
  have hv : HasDerivAt Complex.Gamma (-(Real.eulerMascheroniConstant : ℂ)) 1 := by
    have hd : DifferentiableAt ℂ Complex.Gamma 1 := by
      refine Complex.differentiableAt_Gamma 1 (fun m hm => ?_)
      have hre := congrArg Complex.re hm
      simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h := hd.hasDerivAt
    rwa [deriv_Gamma_one] at h
  have hw := hasDerivAt_estermannEntire_one a
  have htot := ((hu.mul hv).mul hw)
  refine (hasDerivAt_of_eq' htot ?_).deriv
  simp only [Pi.mul_apply, Complex.cpow_neg_one, Complex.Gamma_one, estermannEntire_one]
  field_simp
  ring

end

end RHTower
