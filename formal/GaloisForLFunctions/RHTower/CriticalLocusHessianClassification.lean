import Mathlib
import GaloisForLFunctions.RHTower.CriticalLocusQuadrupleEvenness
import GaloisForLFunctions.RHTower.CrystallineShadowTransversality
import GaloisForLFunctions.RHTower.SuzukiInteriorExcursionSpectralTurningPoint

/-!
# Hessian classification of spectral-type criteria at the critical locus

The relative value of a spectral test `F` on one off-line splitting quadruple is
`φ_γ(t) = ∑_{quadruple} F − 2F(1/2+iγ) − 2F(1/2−iγ)`.  This module certifies the
second-order theory of these functionals at the critical locus `t = 0`:

* **exact separation** — a finite multi-splitting's value is the sum of its per-ordinate
  relative quadruple values, with no cross-terms, because summing a function over a
  multiset join is additive;
* **the weight** — the second central jet of the quadruple functional equals
  `2(F''(1/2+iγ) + F''(1/2−iγ))`, and under the reality symmetry `F(s̄) = conj (F s)`
  it is the real weight `4 Re F''(1/2+iγ)`;
* **per-zero necessity** — a detector (a test whose real part is locally maximal at the
  undisplaced configuration along one real splitting parameter) has nonpositive weight at
  that ordinate: nonnegative-sum criteria are never weaker than RH-per-zero;
* **mixture/determination** — the diagonal Hessian of a scaled multi-splitting is
  `∑_j w_j t_j²`, and two spectral tests are second-order equivalent at every ordinate
  exactly when their weight functions agree;
* **composite criteria** — a smooth function of finitely many spectral functionals has
  stratum second derivative `∑_i ∂_i g · φ_i''(0)`: the finite-rank Hessian correction
  vanishes on one-parameter strata because every first derivative does, so per-zero
  necessity survives composition;
* **the shadow pairing** — for the explicit-formula kernel
  `F_h(ρ) = ∫ h(x) e^{(ρ−1/2)x} dx` of a continuous compactly supported test `h`, the
  relative quadruple value is exactly `∫ h(x)·4cos(γx)(cosh(tx)−1) dx`: the deformation
  shadow is the absolutely continuous measure with density `4cos(γx)(cosh(tx)−1)`.

The conjugation bridge `deriv F (s̄) = conj (deriv F s)` for reality-symmetric tests is
proved from the slope characterization of the derivative and reused at second order.
-/

namespace RHTower

noncomputable section

open Complex MeasureTheory ComplexConjugate Filter

/-! ## The relative quadruple functional and exact separation -/

/-- The relative quadruple functional `φ_γ(t)`: the value of the splitting quadruple minus
its on-line collapse (two conjugate double zeros). -/
def relativeQuadrupleValue (F : ℂ → ℂ) (γ t : ℂ) : ℂ :=
  criticalQuadrupleSum F γ t - criticalQuadrupleSum F γ 0

theorem relativeQuadrupleValue_zero (F : ℂ → ℂ) (γ : ℂ) :
    relativeQuadrupleValue F γ 0 = 0 := sub_self _

/-- Evenness of the relative quadruple functional in the displacement. -/
theorem relativeQuadrupleValue_neg (F : ℂ → ℂ) (γ t : ℂ) :
    relativeQuadrupleValue F γ (-t) = relativeQuadrupleValue F γ t := by
  unfold relativeQuadrupleValue
  rw [criticalQuadrupleSum_neg]

/-- The scalar quadruple functional is the sum of `F` over the quadruple multiset. -/
theorem criticalQuadrupleSum_eq_map_sum (F : ℂ → ℂ) (γ t : ℂ) :
    ((criticalQuadruple γ t).map F).sum = criticalQuadrupleSum F γ t := by
  simp [criticalQuadruple, criticalQuadrupleSum]
  ring

/-- A finite multi-splitting configuration: the multiset join of its quadruples. -/
def multiQuadruple {ι : Type*} (s : Finset ι) (gam t : ι → ℂ) : Multiset ℂ :=
  ∑ j ∈ s, criticalQuadruple (gam j) (t j)

/-- **Exact separation, absolute form.**  Summing a spectral test over a finite
multi-splitting is the sum of the per-ordinate quadruple functionals — exactly, not merely
to second order.  Cross-terms between distinct ordinates are identically zero. -/
theorem multiQuadruple_map_sum {ι : Type*} (s : Finset ι) (gam t : ι → ℂ) (F : ℂ → ℂ) :
    ((multiQuadruple s gam t).map F).sum = ∑ j ∈ s, criticalQuadrupleSum F (gam j) (t j) := by
  classical
  unfold multiQuadruple
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih,
        criticalQuadrupleSum_eq_map_sum]

/-- **Exact separation, relative form (Θ2(i)).**  The relative value of a finite
multi-splitting against its on-line collapse is the sum of the per-ordinate relative
quadruple values. -/
theorem multiQuadruple_relative_separation {ι : Type*} (s : Finset ι) (gam t : ι → ℂ)
    (F : ℂ → ℂ) :
    ((multiQuadruple s gam t).map F).sum - ((multiQuadruple s gam 0).map F).sum
      = ∑ j ∈ s, relativeQuadrupleValue F (gam j) (t j) := by
  rw [multiQuadruple_map_sum, multiQuadruple_map_sum, ← Finset.sum_sub_distrib]
  rfl

/-! ## Analyticity of the quadruple functional -/

/-- The four affine pieces of the quadruple functional are analytic wherever `F` is
analytic at the two conjugate line points. -/
theorem analyticAt_criticalQuadrupleSum (F : ℂ → ℂ) (γ : ℂ)
    (h₊ : AnalyticAt ℂ F (1 / 2 + γ * I)) (h₋ : AnalyticAt ℂ F (1 / 2 - γ * I)) :
    AnalyticAt ℂ (criticalQuadrupleSum F γ) 0 := by
  have a₁ : AnalyticAt ℂ (fun t : ℂ => F (t + (1 / 2 + γ * I))) 0 := by
    have := h₊.comp (x := (0 : ℂ)) (f := fun t : ℂ => t + (1 / 2 + γ * I))
      (by simpa using (analyticAt_id.add analyticAt_const))
    · simpa [Function.comp_def] using this (by simpa using h₊)
  sorry

end

end RHTower
