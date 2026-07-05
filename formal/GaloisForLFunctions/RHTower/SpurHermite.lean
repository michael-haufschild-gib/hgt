/-
Lemma W of the MWM lane (doc 25 §3; task #143): the Hermite equilibrium-energy identity.

At every critical point `k` of the probabilists' Hermite polynomial `hermite m` (m ≥ 2),
`He_m''(k) = −m·He_m(k)` with `He_m(k) ≠ 0` — so the electrostatic energy `−He_m''/He_m`
at every Hermite equilibrium equals `m`, the number of charges. This is the universal
cluster constant of the tracking-clearance theorem (doc 25 Thm B): an m-fold carrier zero
splits into the `He_m` configuration and every cluster critical point carries margin
`|x*−τ|²·d/(m·x*²)`.

Supporting API absent from mathlib:
* `derivative_hermite` — the Appell identity `He_{n+1}' = (n+1)·He_n`;
* `hermite_rec` — the three-term recurrence `He_{n+2} = X·He_{n+1} − (n+1)·He_n`;
* `aeval_hermite_ne_zero_of_succ` — adjacent Hermite polynomials share no real zero.
-/
import Mathlib

namespace RHTower

open Polynomial

/-- **Appell identity** for the probabilists' Hermite polynomials:
`He_{n+1}' = (n+1) · He_n`. -/
theorem derivative_hermite (n : ℕ) :
    derivative (hermite (n + 1)) = (((n : ℤ[X])) + 1) * hermite n := by
  induction n with
  | zero => simp [hermite_succ, hermite_zero]
  | succ n ih =>
      have hstep : derivative (hermite n) = X * hermite n - hermite (n + 1) := by
        rw [hermite_succ n]; ring
      rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
        derivative_mul, hstep]
      have hd : derivative (((n : ℤ[X])) + 1) = 0 := by
        simp
      rw [hd, zero_mul, zero_add]
      push_cast
      ring

/-- **Three-term recurrence**: `He_{n+2} = X·He_{n+1} − (n+1)·He_n`. -/
theorem hermite_rec (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - (((n : ℤ[X])) + 1) * hermite n := by
  rw [show n + 2 = n + 1 + 1 from rfl, hermite_succ (n + 1), derivative_hermite n]

/-- Probabilists' Hermite ODE over `ℤ[X]`: `Heₙ'' - X Heₙ' + n Heₙ = 0`. -/
theorem hermite_ode (n : ℕ) :
    derivative (derivative (hermite n)) - X * derivative (hermite n)
      + (((n : ℤ[X])) * hermite n) = 0 := by
  have h := derivative_hermite n
  rw [Polynomial.hermite_succ] at h
  rw [derivative_sub, derivative_mul, derivative_X] at h
  have h1 : X * derivative (Polynomial.hermite n)
      - derivative (derivative (Polynomial.hermite n)) =
        ((n : ℤ[X])) * Polynomial.hermite n := by
    calc
      X * derivative (Polynomial.hermite n) - derivative (derivative (Polynomial.hermite n))
          = (1 * Polynomial.hermite n + X * derivative (Polynomial.hermite n)
              - derivative (derivative (Polynomial.hermite n))) - Polynomial.hermite n := by
            ring
      _ = (((n : ℤ[X])) + 1) * Polynomial.hermite n - Polynomial.hermite n := by rw [h]
      _ = ((n : ℤ[X])) * Polynomial.hermite n := by ring
  rw [← h1]
  ring

/-- Real-evaluation form of the probabilists' Hermite ODE. -/
theorem aeval_hermite_ode (n : ℕ) (x : ℝ) :
    (aeval x (derivative (derivative (hermite n))) : ℝ)
      - x * (aeval x (derivative (hermite n)) : ℝ)
      + (n : ℝ) * (aeval x (hermite n) : ℝ) = 0 := by
  have h := congrArg (fun p : Polynomial ℤ => (aeval x p : ℝ)) (hermite_ode n)
  simpa only [map_add, map_sub, map_mul, map_natCast, aeval_X, map_zero] using h

/-- Gaussian derivative representation of the even probabilists' Hermite polynomial. -/
theorem aeval_hermite_even_gaussian_factor (d : ℕ) (x : ℝ) :
    (aeval x (hermite (2 * d)) : ℝ) =
      (-1 : ℝ) ^ (2 * d) *
        deriv^[2 * d] (fun y => Real.exp (-(y ^ 2 / 2))) x * Real.exp (x ^ 2 / 2) := by
  simpa using Polynomial.hermite_eq_deriv_gaussian' (2 * d) x

/-- Even-order Gaussian derivative representation with the sign removed. -/
theorem aeval_hermite_even_gaussian_factor_even (d : ℕ) (x : ℝ) :
    (aeval x (hermite (2 * d)) : ℝ) =
      deriv^[2 * d] (fun y => Real.exp (-(y ^ 2 / 2))) x * Real.exp (x ^ 2 / 2) := by
  rw [aeval_hermite_even_gaussian_factor]
  simp

/-- Adjacent Hermite polynomials share no real zero: a real zero of `He_{m+1}`
is never a zero of `He_m` (descent through the recurrence to `He_0 = 1`). -/
theorem aeval_hermite_ne_zero_of_succ {k : ℝ} :
    ∀ m : ℕ, aeval k (hermite (m + 1)) = 0 → aeval k (hermite m) ≠ 0 := by
  intro m
  induction m with
  | zero => simp [hermite_zero]
  | succ m ih =>
      intro h2 h1
      have hrec := congrArg (aeval k) (hermite_rec m)
      rw [h2, map_sub, map_mul, map_mul, h1, mul_zero, zero_sub] at hrec
      have hprod : (aeval k) (((m : ℤ[X])) + 1) * (aeval k) (hermite m) = 0 := by
        linarith [hrec]
      have hC : (aeval k) (((m : ℤ[X])) + 1) ≠ 0 := by
        simp only [map_add, map_one, map_natCast]
        positivity
      exact ih h1 ((mul_eq_zero.mp hprod).resolve_left hC)

/-- **Lemma W (division-free form).** At every real critical point `k` of `He_m`
(`m ≥ 2`): `He_m''(k) = −m · He_m(k)`, and `He_m(k) ≠ 0`. -/
theorem hermite_equilibrium_energy {k : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hcrit : aeval k (derivative (hermite m)) = 0) :
    aeval k (derivative (derivative (hermite m))) = -(m : ℝ) * aeval k (hermite m) ∧
      aeval k (hermite m) ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hcrit' : aeval k (derivative (hermite (n + 1 + 1))) = 0 := hcrit
  -- the critical point is a zero of He_{n+1}
  have hzero : aeval k (hermite (n + 1)) = 0 := by
    have h := congrArg (aeval k) (derivative_hermite (n + 1))
    rw [hcrit', map_mul] at h
    have hC : (aeval k) ((((n + 1 : ℕ) : ℤ[X])) + 1) ≠ 0 := by
      simp only [map_add, map_one, map_natCast]
      positivity
    exact (mul_eq_zero.mp h.symm).resolve_left hC
  -- He_{n+2}(k) ≠ 0 by the adjacency descent
  have hne : aeval k (hermite (n + 2)) ≠ 0 := by
    intro h0
    exact aeval_hermite_ne_zero_of_succ (n + 1) h0 hzero
  refine ⟨?_, hne⟩
  -- second derivative: He_{n+2}'' = (n+2)(n+1)·He_n
  have hdd : derivative (derivative (hermite (n + 2))) =
      (((n : ℤ[X])) + 2) * ((((n : ℤ[X])) + 1) * hermite n) := by
    have h1 : derivative (hermite (n + 2)) =
        ((((n + 1 : ℕ) : ℤ[X])) + 1) * hermite (n + 1) := derivative_hermite (n + 1)
    rw [h1, derivative_mul, derivative_hermite n]
    have hd : derivative ((((n + 1 : ℕ) : ℤ[X])) + 1) = 0 := by simp
    rw [hd, zero_mul, zero_add]
    push_cast
    ring
  -- the recurrence at k: He_{n+2}(k) = −(n+1)·He_n(k)
  have hrec := congrArg (aeval k) (hermite_rec n)
  rw [map_sub, map_mul, map_mul, hzero, mul_zero, zero_sub] at hrec
  -- assemble
  rw [congrArg (aeval k) hdd, map_mul, map_mul, hrec]
  simp only [map_add, map_one, map_natCast, map_ofNat]
  push_cast
  ring

/-- **Lemma W.** The electrostatic energy `−He_m''/He_m` at every real critical point of
`He_m` equals `m` — the Hermite equilibrium energy is the charge count (doc 25 §3). -/
theorem hermite_energy_eq_charge {k : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hcrit : aeval k (derivative (hermite m)) = 0) :
    -(aeval k (derivative (derivative (hermite m)))) / aeval k (hermite m) = (m : ℝ) := by
  obtain ⟨hval, hne⟩ := hermite_equilibrium_energy hm hcrit
  rw [hval]
  field_simp

end RHTower
