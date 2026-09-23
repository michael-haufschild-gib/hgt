import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# First-order Krein realization of transport moments

A difference of endpoint moments is the integral of a first-order jet product.  The two jet
components carry the exchange form, so the transport kernel is an exact indefinite Gram before
either endpoint is contracted.

This is a reusable fundamental-theorem-of-calculus factorization, not a new source theorem.
-/

namespace HTGeometry

noncomputable section

/-- First-order two-channel lift of the monomial jet `t^(i+1)`. -/
def transportDiracJet (i : ℕ) (t : ℝ) : ℝ × ℝ :=
  (((i + 1 : ℕ) : ℝ) * t ^ i, t ^ (i + 1))

/-- The exchange form on a two-channel first-order lift. -/
def exchangePair (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.2 + u.2 * v.1

/-- The exchange pairing of two first-order monomial lifts is the derivative of their product. -/
theorem exchangePair_transportDiracJet (i j : ℕ) (t : ℝ) :
    exchangePair (transportDiracJet i t) (transportDiracJet j t) =
      (((i + j + 2 : ℕ) : ℝ) * t ^ (i + j + 1)) := by
  have h₁ : t ^ i * t ^ (j + 1) = t ^ (i + j + 1) := by
    rw [← pow_add]
    congr 1
  have h₂ : t ^ (i + 1) * t ^ j = t ^ (i + j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [exchangePair, transportDiracJet]
  calc
    ((i + 1 : ℕ) : ℝ) * t ^ i * t ^ (j + 1) +
        t ^ (i + 1) * (((j + 1 : ℕ) : ℝ) * t ^ j) =
      (((i + 1 : ℕ) : ℝ)) * (t ^ i * t ^ (j + 1)) +
        (((j + 1 : ℕ) : ℝ)) * (t ^ (i + 1) * t ^ j) := by ring
    _ = _ := by rw [h₁, h₂]; push_cast; ring

/-- **Dirac--Stokes transport law.**  Integrating the exchange Gram along one oriented edge is
exactly the difference of its endpoint moments. -/
theorem intervalIntegral_exchangePair_transportDiracJet
    (i j : ℕ) (x y : ℝ) :
    (∫ t in x..y, exchangePair (transportDiracJet i t) (transportDiracJet j t)) =
      y ^ (i + j + 2) - x ^ (i + j + 2) := by
  let F : ℝ → ℝ := fun t => t ^ (i + j + 2)
  let dF : ℝ → ℝ := fun t => (((i + j + 2 : ℕ) : ℝ) * t ^ (i + j + 1))
  have hF (t : ℝ) : HasDerivAt F (dF t) t := by
    dsimp only [F, dF]
    convert! (hasDerivAt_id t).pow (i + j + 2) using 1
    all_goals
      simp only [id_eq]
      push_cast
      ring
  have hderiv : deriv F = dF := by
    funext t
    exact (hF t).deriv
  have hfund := intervalIntegral.integral_deriv_eq_sub'
    F hderiv (fun t _ => (hF t).differentiableAt) (by
      dsimp only [dF]
      fun_prop : ContinuousOn dF (Set.uIcc x y))
  rw [show (fun t => exchangePair (transportDiracJet i t) (transportDiracJet j t)) =
      dF by
    funext t
    exact exchangePair_transportDiracJet i j t]
  simpa only [F] using hfund

/-- The exchange form is one positive square minus one negative square. -/
theorem exchangePair_diagonalize (u v : ℝ × ℝ) :
    exchangePair u v =
      ((u.1 + u.2) * (v.1 + v.2) - (u.1 - u.2) * (v.1 - v.2)) / 2 := by
  simp only [exchangePair]
  ring

/-- Positive Hilbert majorant integrand for the first-order lift. -/
def transportDiracMajorant (i : ℕ) (t : ℝ) : ℝ :=
  (((i + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * t ^ (2 * i) + t ^ (2 * i + 2)

theorem intervalIntegral_transportDiracMajorant (i : ℕ) (x y : ℝ) :
    (∫ t in x..y, transportDiracMajorant i t) =
      (((i + 1 : ℕ) : ℝ) ^ (2 : ℕ)) *
          (y ^ (2 * i + 1) - x ^ (2 * i + 1)) / ((2 * i + 1 : ℕ) : ℝ) +
        (y ^ (2 * i + 3) - x ^ (2 * i + 3)) / ((2 * i + 3 : ℕ) : ℝ) := by
  simp only [transportDiracMajorant]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    push_cast
    ring
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

end

end HTGeometry
