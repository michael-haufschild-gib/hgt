import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite Euler q-Gamma process identities

This module formalizes the unconditional finite source core of the Euler q-Gamma process:

* exact translation-ladder telescoping with its terminal escape factor;
* the additive Cartier-order boundary with its terminal remainder; and
* the genus-one local and finite-product exchange that removes the first activation term.

No analytic continuation, convergence premise, zeta-zero premise, or added axiom is used.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The genus-one primary factor used by the finite Euler-process renormalization. -/
def eulerProcessGenusOneFactor (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

/-- The local first-activation counterterm. In the q-Gamma realization, `q` is the local
nome and `x = q^(1+s)` is its intervened value. -/
def eulerQGammaFirstActivation (q x s : ℂ) : ℂ :=
  q * (s - 1) + x

/-- Exact local exchange between the raw q-Gamma shift factor and its genus-one
renormalization. The cross-multiplied statement is unconditional, including singular
values `q = 1` and `x = 1`. -/
theorem eulerQGamma_genusOne_local_exchange (q x : ℂ) :
    (1 - x) * Complex.exp (-q + (1 - q) * x) * eulerProcessGenusOneFactor q =
      (1 - q) * eulerProcessGenusOneFactor x * Complex.exp (-q * x) := by
  unfold eulerProcessGenusOneFactor
  calc
    (1 - x) * Complex.exp (-q + (1 - q) * x) * ((1 - q) * Complex.exp q) =
        (1 - q) * (1 - x) *
          (Complex.exp (-q + (1 - q) * x) * Complex.exp q) := by ring_nf
    _ = (1 - q) * (1 - x) * Complex.exp ((-q + (1 - q) * x) + q) := by
      rw [← Complex.exp_add]
    _ = (1 - q) * (1 - x) * Complex.exp (x + (-q * x)) := by
      congr 1
      ring_nf
    _ = (1 - q) * ((1 - x) * Complex.exp x) * Complex.exp (-q * x) := by
      rw [Complex.exp_add]
      ring_nf

/-- Finite local-to-global composition of the genus-one exchange. -/
theorem eulerQGamma_genusOne_finite_exchange
    {α : Type*} (I : Finset α) (q x : α → ℂ) :
    (∏ i ∈ I,
        ((1 - x i) * Complex.exp (-q i + (1 - q i) * x i) *
          eulerProcessGenusOneFactor (q i))) =
      ∏ i ∈ I,
        ((1 - q i) * eulerProcessGenusOneFactor (x i) *
          Complex.exp (-q i * x i)) := by
  apply Finset.prod_congr rfl
  intro i hi
  exact eulerQGamma_genusOne_local_exchange (q i) (x i)

/-- A finite Euler response ladder. -/
def finiteEulerResponseLadder {R : Type*} [CommMonoid R]
    (a : ℕ → R) (N : ℕ) : R :=
  ∏ k ∈ Finset.range N, a k

/-- Exact finite translation telescope. The uncancelled terminal factor is retained, so the
identity has no convergence or nonvanishing assumptions. -/
theorem finiteEulerResponseLadder_shift_mul_source
    {R : Type*} [CommMonoid R] (a : ℕ → R) (N : ℕ) :
    finiteEulerResponseLadder (fun k ↦ a (k + 1)) N * a 0 =
      finiteEulerResponseLadder a (N + 1) := by
  induction N with
  | zero => simp [finiteEulerResponseLadder]
  | succ N ih =>
      simp only [finiteEulerResponseLadder, Finset.prod_range_succ] at ih ⊢
      calc
        ((∏ k ∈ Finset.range N, a (k + 1)) * a (N + 1)) * a 0 =
            ((∏ k ∈ Finset.range N, a (k + 1)) * a 0) * a (N + 1) := by
              ac_rfl
        _ = ((∏ k ∈ Finset.range N, a k) * a N) * a (N + 1) := by rw [ih]

/-- Additive divisor order of a finite Euler ladder. -/
def finiteEulerDivisorOrder (d : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range N, d k

/-- Exact finite Cartier boundary: translated ladder minus original ladder equals terminal
escape minus source divisor. -/
theorem finiteEulerDivisorOrder_translation_boundary
    (d : ℕ → ℤ) (N : ℕ) :
    finiteEulerDivisorOrder (fun k ↦ d (k + 1)) N -
        finiteEulerDivisorOrder d N =
      d N - d 0 := by
  induction N with
  | zero => simp [finiteEulerDivisorOrder]
  | succ N ih =>
      simp only [finiteEulerDivisorOrder, Finset.sum_range_succ] at ih ⊢
      omega

end

end GaloisForLFunctions.HTGeometry
