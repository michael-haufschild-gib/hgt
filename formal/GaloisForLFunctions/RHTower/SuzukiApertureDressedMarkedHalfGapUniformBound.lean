import GaloisForLFunctions.RHTower.SuzukiApertureDressedMarkedCompoundCofinal

/-!
# Uniform cofinal bound for Suzuki's dressed marked halfgap debt

Pointwise summability of the aperture-dressed marked completion does not by itself control a
cofinal Ward residual: its total mass could still grow with observer aperture or spectral height.
The all-prime wall majorant is in fact independent of both variables.  This module exposes the
resulting exact total-mass identity and the uniform ceiling

`total halfgap debt ≤ C(h) * (r - m*s)^(2 : ℕ)`,

where `C(h)` is one fixed convergent prime-log square sum.  Consequently the marked halfgap
channel cannot make the rectangular Ward residual escape to negative infinity at fixed source
scale.  Remaining RH-bearing work is the source occurrence and Schur comparison of the actual
Robin--Gamma--holonomy trace with the completed negative-light Gram; it is not halfgap
summability or cofinal growth.

No RH premise, Xi-zero hypothesis, computation, or asymptotic interchange is used.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact total-mass law: complete dressed marked halfgap debt is wall mass times the single
centered rank-one square. -/
theorem tsum_suzukiCriticalApertureDressedMarkedRootedCompletion_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t m d r s : ℝ) :
    (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedMarkedRootedCompletion
        h a t m d r s pe) =
      (∑' pe : Nat.Primes × ℕ,
        Complex.normSq
          (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2)) *
        (r - m * s) ^ (2 : ℕ) := by
  have hs :=
    summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  rw [show (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedMarkedRootedCompletion
        h a t m d r s pe) =
      ∑' pe : Nat.Primes × ℕ,
        Complex.normSq
          (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) *
          (r - m * s) ^ (2 : ℕ) by
      apply tsum_congr
      intro pe
      exact suzukiCriticalApertureDressedMarkedRootedCompletion_eq
        h a t m d r s pe]
  exact hs.tsum_mul_right ((r - m * s) ^ (2 : ℕ))

/-- Uniform cofinal ceiling.  Right side is independent of observer aperture `a`, spectral
height `t`, and halfgap coordinate `d`. -/
theorem tsum_suzukiCriticalApertureDressedMarkedRootedCompletion_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t m d r s : ℝ) :
    (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedMarkedRootedCompletion
        h a t m d r s pe) ≤
      (2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹)) *
        (r - m * s) ^ (2 : ℕ) := by
  rw [tsum_suzukiCriticalApertureDressedMarkedRootedCompletion_eq
    hh ha t m d r s]
  exact mul_le_mul_of_nonneg_right
    (tsum_normSq_suzukiCriticalApertureBoundaryAtom_allPrime_le hh ha t)
    (sq_nonneg _)

end


end RHTower
