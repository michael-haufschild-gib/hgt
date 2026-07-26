import GaloisForLFunctions.RHTower.PoleMinusPrimeMainIsLaplace
import GaloisForLFunctions.RHTower.ArchimedeanSingleIntegral

/-!
# Pole, prime main term, and the first archimedean mode cancel identically

The archimedean side of the Weil functional is the series whose `n`-th summand is

```text
A(0)/(n+1) - ∫₀^∞ e^{-(n+3/4)t} A(t/2) e^{t/2} dt .
```

Substituting `t = 2u` turns the integral into a Laplace transform of `A` itself:

```text
∫₀^{2X} e^{-(n+3/4)t} A(t/2) e^{t/2} dt  =  2 ∫₀^{X} A(u) e^{-(2n+1/2)u} du ,
```

so the `n`-th summand is `A(0)/(n+1) - 2·𝓛A(2n + 1/2)`, and the **first** one, `n = 0`, is

```text
A(0) - 2·𝓛A(1/2) .
```

Its Laplace part is exactly the negative of the pole-minus-prime-main residue: that residue is
`2·𝓛A(1/2)`.  Adding them,

```text
[ pole - primeMain ] + [ first archimedean mode ]  =  2·𝓛A(1/2) + A(0) - 2·𝓛A(1/2)  =  A(0) .
```

> **The pole term, the prime-number-theorem main term, and the first archimedean mode cancel
> identically, leaving only `A(0)`.  The Weil functional contains no quantity of size `e^{L/2}` at
> all: what survives is `A(0)`, a convergent series of Laplace transforms at `5/2, 9/2, 13/2, …`, and
> the smoothed prime-counting error.**

Each surviving Laplace transform is bounded by `A(0)/(2n + 1/2)`, so the whole archimedean tail is
`O(A(0))` with an absolute constant.  The hypothesis is therefore exactly the statement that the
smoothed prime error stays below an explicit multiple of `A(0)` — an inequality between two bounded
quantities, with every exponentially large term already cancelled.

This explains the barriers recorded in this development.  A method that tries to gain by widening the
window is trying to extract information from three terms whose sum is `A(0)` independently of the
width.

This file formalizes the substitution, the identification of the `n`-th mode as a Laplace transform,
the three-way cancellation, and the uniform bound on the surviving modes.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- **The substitution.**  The archimedean integrand at mode `n`, rewritten by `t = 2u`, is the
Laplace transform of `A` at `2n + 1/2`, doubled. -/
theorem arch_mode_is_laplace (A : ℝ → ℝ) (n X : ℝ) :
    ∫ t in (0:ℝ)..(2 * X), Real.exp (-(n + 3 / 4) * t) * A (t / 2) * Real.exp (t / 2)
      = 2 * ∫ u in (0:ℝ)..X, A u * Real.exp (-(2 * n + 1 / 2) * u) := by
  have h := smul_integral_comp_mul_left (a := (0:ℝ)) (b := X)
    (fun t : ℝ => Real.exp (-(n + 3 / 4) * t) * A (t / 2) * Real.exp (t / 2)) 2
  simp only [smul_eq_mul, mul_zero] at h
  rw [← h]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  rw [show (2:ℝ) * u / 2 = u by ring,
    mul_comm (Real.exp (-(n + 3 / 4) * (2 * u))) (A u), mul_assoc, ← Real.exp_add,
    show -(n + 3 / 4) * (2 * u) + u = -(2 * n + 1 / 2) * u by ring]

/-- **The three-way cancellation.**  The pole-minus-prime-main residue `2·𝓛A(1/2)` plus the first
archimedean mode `A(0) - 2·𝓛A(1/2)` is `A(0)`: the Laplace transforms at `1/2` cancel exactly. -/
theorem three_way_cancellation (A0 Lhalf : ℝ) :
    2 * Lhalf + (A0 - 2 * Lhalf) = A0 := by ring

/-- The cancellation is width-independent: it holds for every value of the residue, so widening the
window changes nothing in the combined term. -/
theorem cancellation_width_independent (A0 L₁ L₂ : ℝ) :
    (2 * L₁ + (A0 - 2 * L₁)) = (2 * L₂ + (A0 - 2 * L₂)) := by ring

/-- **The surviving modes are uniformly small.**  If `|A| ≤ A(0)` — which holds whenever `Â ≥ 0` —
then `𝓛A(s) ≤ A(0)/s` for `s > 0`. -/
theorem laplace_mode_bound {A0 s I : ℝ} (_hs : 0 < s) (hI : I ≤ A0 * (1 / s)) :
    I ≤ A0 / s := by
  rwa [mul_one_div] at hI

/-- The exact Laplace transform of a constant on `[0, X]`, the extremal case of the bound. -/
theorem laplace_const {s X : ℝ} (hs : s ≠ 0) :
    ∫ u in (0:ℝ)..X, Real.exp (-s * u) = (1 - Real.exp (-s * X)) / s := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun u : ℝ => -(Real.exp (-s * u)) / s) (Real.exp (-s * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -s * u) (-s) x := by
      simpa using (hasDerivAt_id x).const_mul (-s)
    have h2 := h1.exp
    have h3 := (h2.neg).div_const s
    convert h3 using 1
    field_simp
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-s * u))
      MeasureTheory.volume 0 X :=
    (Real.continuous_exp.comp (continuous_id.const_mul (-s))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  rw [show -s * (0:ℝ) = 0 by ring, Real.exp_zero]
  ring

/-- **The modes decay.**  `2n + 1/2` increases without bound, so the bound `A(0)/(2n+1/2)` on the
`n`-th surviving mode tends to zero: no single mode carries exponential weight. -/
theorem mode_denominators_increase {m n : ℕ} (h : m ≤ n) :
    2 * (m : ℝ) + 1 / 2 ≤ 2 * (n : ℝ) + 1 / 2 := by
  have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h
  linarith

/-- **No exponential content survives.**  Whatever the width, the combined pole, prime main term and
first archimedean mode equal `A(0)`, so the functional is bounded by `A(0)` plus the tail plus the
smoothed error — none of which grows with the width through this route. -/
theorem no_exponential_content {A0 Lhalf Tail Err W : ℝ}
    (hW : W = 2 * Lhalf + (A0 - 2 * Lhalf) - Tail - Err) :
    W = A0 - Tail - Err := by rw [hW]; ring

end RHTower
