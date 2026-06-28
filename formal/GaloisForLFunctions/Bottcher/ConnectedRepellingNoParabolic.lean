/-
# Connected repelling event route with no-multiplier-one separability input

This is a thin hRigid-facing wrapper around `ConnectedRepellingEventual`: it removes the abstract
frequent-separability clause by proving it from the concrete dynamical condition that the selected
periods have no multiplier-`1` fixed points.
-/
import GaloisForLFunctions.Bottcher.ConnectedRepellingEventual
import GaloisForLFunctions.Bottcher.FixedPointSeparable

open Polynomial Finset Filter Topology

namespace Bottcher

/-- The frequent no-multiplier-one selector feeds the current bounded denominator witness selector. -/
theorem exists_period_denominator_of_frequently_multiplier_ne_one_eventually_nonStrong_subset_of_bounded_denominator_witness
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (E : Finset ℂ) (M : ℕ)
    (hmul : ∃ᶠ p : ℕ in atTop, 1 ≤ p ∧
      ∀ z : ℂ, (fixedPointPoly c p).IsRoot z →
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ))
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hdenom : ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) :
    ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
      1 ≤ p ∧ (fixedPointPoly c p).Separable ∧ e ≠ 0 ∧
      (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
      squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card < 2 ^ p := by
  exact
    exists_period_denominator_of_frequently_separable_eventually_nonStrong_subset_of_bounded_denominator_witness
      c P E M
      (frequently_fixedPointPoly_separable_of_frequently_multiplier_ne_one c hmul)
      hE hdenom

/-- **No-parabolic bounded-denominator input for absolute connected `φ_c` transcendence.**

For each minimal relation the callback now supplies frequent periods where every fixed point of
`f_c^[p]` has multiplier different from `1`, instead of directly proving
`(fixedPointPoly c p).Separable`.  `FixedPointSeparable` turns that dynamic condition into the
separability required by the existing event selector. -/
theorem phiMero_transcendental_of_repelling_frequently_multiplier_ne_one_denominatorWitnessBound_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (M : ℕ),
          (∃ᶠ p : ℕ in atTop, 1 ≤ p ∧
            ∀ z : ℂ, (fixedPointPoly c p).IsRoot z →
              (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) ∧
          (∀ᶠ p : ℕ in atTop,
            ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
              e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_frequently_separable_denominatorWitnessBound_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, M, hmul, hE, hdenom⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact ⟨E, M,
    frequently_fixedPointPoly_separable_of_frequently_multiplier_ne_one c hmul,
    hE, hdenom⟩

end Bottcher
