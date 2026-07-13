import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination
import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# Harmonic-oscillator eigenfunctions and the prolate quasi-eigenvalue ladder

The probabilists' Hermite polynomials `He_n` satisfy the Appell law `He_{n+1}' = (n+1)·He_n` and
hence the Hermite differential equation `He_n'' = X·He_n' − n·He_n`; both are derived here from
the defining recurrence `He_{n+1} = X·He_n − He_n'`.  Multiplying by the Gaussian weight gives
the oscillator eigenfunctions: `probHermiteFun n = He_n(x)·e^(−x²/4)` satisfies
`ψ'' = (x²/4 − n − 1/2)·ψ`, and the physicists' rescaling
`hermiteFun n = He_n(√2·x)·e^(−x²/2)` is an exact eigenfunction of the Hermite action
`ψ'' − x²ψ` with eigenvalue `−(2n+1)` (`hermiteSLAction_hermiteFun`).

Feeding this ladder through the exact prolate→Hermite scaling identity shows that the rescaled
Hermite functions are quasi-eigenfunctions of the prolate Sturm–Liouville action at bandwidth
`c`: the action returns exactly `−(2n+1)·c` times the function plus an explicit lower-order
defect (`prolateSLAction_hermiteFun`).  This is the differential-operator layer of the prolate
spectral ladder: at large bandwidth the prolate spectrum organizes along the oscillator ladder
`−(2n+1)·c` with corrections of relative size `1/c`.
-/

open Polynomial Filter Real

namespace RHTower

/-- Appell law for the probabilists' Hermite polynomials: `He_{n+1}' = (n+1)·He_n`. -/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = ((n : Polynomial ℤ) + 1) * hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ m ih =>
    rw [hermite_succ (m + 1), derivative_sub, derivative_mul, derivative_X, ih,
      derivative_mul]
    have hd : derivative ((m : Polynomial ℤ) + 1) = 0 := by simp
    rw [hd, zero_mul, zero_add]
    have hs := hermite_succ m
    push_cast
    linear_combination (-(m : Polynomial ℤ) - 1) * hs

/-- The Hermite differential equation `He_n'' = X·He_n' − n·He_n`. -/
theorem hermite_oscillator_ode (n : ℕ) :
    derivative (derivative (hermite n))
      = X * derivative (hermite n) - (n : Polynomial ℤ) * hermite n := by
  cases n with
  | zero => simp [hermite_zero]
  | succ m =>
    rw [derivative_hermite_succ m, derivative_mul]
    have hd : derivative ((m : Polynomial ℤ) + 1) = 0 := by simp
    rw [hd, zero_mul, zero_add]
    have hs := hermite_succ m
    push_cast
    linear_combination ((m : Polynomial ℤ) + 1) * hs

/-- Probabilists' Hermite function `He_n(x)·e^(−x²/4)`. -/
noncomputable def probHermiteFun (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (hermite n) * Real.exp (-(x ^ 2 / 4))

/-- Derivative of the Gaussian weight `e^(−x²/4)`. -/
theorem hasDerivAt_quarterGauss (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 4)))
      (-(x / 2) * Real.exp (-(x ^ 2 / 4))) x := by
  have h : HasDerivAt (fun y : ℝ => -(y ^ 2 / 4)) (-(x / 2)) x := by
    have h0 := ((hasDerivAt_pow 2 x).div_const 4).neg
    have e2 : -(((2 : ℕ) : ℝ) * x ^ (2 - 1) / 4) = -(x / 2) := by push_cast; ring
    rw [e2] at h0
    exact h0
  have h2 := h.exp
  rw [mul_comm] at h2
  exact h2

/-- First derivative of the probabilists' Hermite function:
`ψ_n' = He_n'·e^(−x²/4) − (x/2)·ψ_n`. -/
theorem hasDerivAt_probHermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (probHermiteFun n)
      (Polynomial.aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 4))
        - x / 2 * probHermiteFun n x) x := by
  have h := (Polynomial.hasDerivAt_aeval (𝕜 := ℝ) (hermite n) x).mul
    (hasDerivAt_quarterGauss x)
  have hval : Polynomial.aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 4))
        - x / 2 * probHermiteFun n x
      = Polynomial.aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 4))
        + Polynomial.aeval x (hermite n) * (-(x / 2) * Real.exp (-(x ^ 2 / 4))) := by
    unfold probHermiteFun; ring
  rw [hval]
  exact h

theorem deriv_probHermiteFun (n : ℕ) :
    deriv (probHermiteFun n) = fun x =>
      Polynomial.aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 4))
        - x / 2 * probHermiteFun n x :=
  funext fun x => (hasDerivAt_probHermiteFun n x).deriv

/-- Oscillator equation for the probabilists' Hermite function:
`ψ_n'' = (x²/4 − n − 1/2)·ψ_n`. -/
theorem deriv2_probHermiteFun (n : ℕ) (x : ℝ) :
    deriv (deriv (probHermiteFun n)) x
      = (x ^ 2 / 4 - n - 1 / 2) * probHermiteFun n x := by
  rw [deriv_probHermiteFun n]
  have h1 : HasDerivAt
      (fun y : ℝ => Polynomial.aeval y (derivative (hermite n)) * Real.exp (-(y ^ 2 / 4)))
      (Polynomial.aeval x (derivative (derivative (hermite n))) * Real.exp (-(x ^ 2 / 4))
        + Polynomial.aeval x (derivative (hermite n))
          * (-(x / 2) * Real.exp (-(x ^ 2 / 4)))) x :=
    (Polynomial.hasDerivAt_aeval (𝕜 := ℝ) (derivative (hermite n)) x).mul
      (hasDerivAt_quarterGauss x)
  have h2 : HasDerivAt (fun y : ℝ => y / 2 * probHermiteFun n y)
      ((1 : ℝ) / 2 * probHermiteFun n x
        + x / 2 * (Polynomial.aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 4))
          - x / 2 * probHermiteFun n x)) x :=
    ((hasDerivAt_id x).div_const 2).mul (hasDerivAt_probHermiteFun n x)
  have h : HasDerivAt
      (fun y : ℝ => Polynomial.aeval y (derivative (hermite n)) * Real.exp (-(y ^ 2 / 4))
        - y / 2 * probHermiteFun n y)
      ((Polynomial.aeval x (derivative (derivative (hermite n))) * Real.exp (-(x ^ 2 / 4))
        + Polynomial.aeval x (derivative (hermite n)) * (-(x / 2) * Real.exp (-(x ^ 2 / 4))))
        - ((1 : ℝ) / 2 * probHermiteFun n x
          + x / 2 * (Polynomial.aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 4))
            - x / 2 * probHermiteFun n x))) x := h1.sub h2
  rw [h.deriv]
  have heval : Polynomial.aeval x (derivative (derivative (hermite n)))
      = x * Polynomial.aeval x (derivative (hermite n))
        - n * Polynomial.aeval x (hermite n) := by
    rw [hermite_oscillator_ode]
    simp [map_sub, map_mul, map_natCast, Polynomial.aeval_X]
  rw [heval]
  unfold probHermiteFun
  ring

/-- Physicists' Hermite function `He_n(√2·x)·e^(−x²/2)`: the `n`-th harmonic-oscillator
eigenfunction. -/
noncomputable def hermiteFun (n : ℕ) (x : ℝ) : ℝ := probHermiteFun n (Real.sqrt 2 * x)

/-- Second derivative of the physicists' Hermite function:
`φ_n'' = (x² − 2n − 1)·φ_n`. -/
theorem deriv2_hermiteFun (n : ℕ) (x : ℝ) :
    deriv (deriv (hermiteFun n)) x = (x ^ 2 - 2 * n - 1) * hermiteFun n x := by
  have hL : deriv (deriv (hermiteFun n)) x
      = 2 * deriv (deriv (probHermiteFun n)) (Real.sqrt 2 * x) :=
    deriv2_sqrtScale (by norm_num : (0 : ℝ) ≤ 2) (probHermiteFun n) x
  rw [hL, deriv2_probHermiteFun]
  have h2 : (Real.sqrt 2 * x) ^ 2 = 2 * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2]
  have hval : probHermiteFun n (Real.sqrt 2 * x) = hermiteFun n x := rfl
  rw [hval]
  ring

/-- **Harmonic-oscillator eigenvalue ladder.**  The `n`-th Hermite function is an exact
eigenfunction of the Hermite action `ψ'' − x²ψ` with eigenvalue `−(2n+1)`. -/
theorem hermiteSLAction_hermiteFun (n : ℕ) (x : ℝ) :
    hermiteSLAction (hermiteFun n) x = -(2 * n + 1) * hermiteFun n x := by
  unfold hermiteSLAction
  rw [deriv2_hermiteFun]
  ring

/-- **Hermite functions are prolate quasi-eigenfunctions.**  Under the Hermite rescaling the
prolate Sturm–Liouville action at bandwidth `c` returns the exact oscillator ladder value
`−(2n+1)·c` times the Hermite function, plus a `c`-independent defect expressed through the
Hermite function and its first derivative.  Dividing by `c`, the prolate spectrum organizes
along the ladder `−(2n+1)·c` with relative corrections `O(1/c)`. -/
theorem prolateSLAction_hermiteFun {c : ℝ} (hc : 0 < c) (n : ℕ) (ξ : ℝ) :
    prolateSLAction c (fun y => hermiteFun n (Real.sqrt c * y)) (ξ / Real.sqrt c)
      = -(2 * n + 1) * c * hermiteFun n ξ
        - ξ ^ 2 * (ξ ^ 2 - 2 * n - 1) * hermiteFun n ξ
        - 2 * ξ * deriv (hermiteFun n) ξ := by
  rw [prolateSLAction_sqrtScale hc (hermiteFun n) ξ]
  rw [hermiteSLAction_hermiteFun, deriv2_hermiteFun]
  ring

end RHTower
