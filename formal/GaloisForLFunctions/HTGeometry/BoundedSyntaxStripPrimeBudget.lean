import GaloisForLFunctions.HTGeometry.AutonomousCarrierRegularity
import GaloisForLFunctions.HTGeometry.BoundedSyntaxPrimeCapacity

/-!
# The prime budget of a bounded-syntax almost-periodic carrier

A holomorphic uniformly almost-periodic function on a vertical strip satisfying there a nonzero
autonomous algebraic differential equation of exact order `n` has frequency group of rational rank
at most `2n`.  Retaining `π N` rationally independent prime directions therefore costs
`π N ≤ 2 n`, and since the prime-counting function is unbounded no bounded-syntax family can carry
a cofinal prime module.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **The prime budget of a bounded-syntax carrier.**  A strip carrier with an exact-order-`n`
autonomous annihilator whose frequency group retains `π N` independent prime directions obeys
`π N ≤ 2 n`. -/
theorem primeCounting_le_two_mul_of_stripAnnihilator
    {σ r ρ : ℝ} {n : ℕ} {F : ℂ → ℂ} {R : ℝ} {N : ℕ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      Q.natDegree ≠ 0)
    (hprime : (Nat.primeCounting N : Cardinal) ≤ Module.rank ℤ (bohrHullFrequencies f)) :
    Nat.primeCounting N ≤ 2 * n :=
  primeCounting_le_two_mul N n hprime
    (rank_bohrHullFrequencies_le_of_stripAnnihilator hr hρ hrρ hF hap hf hn hex horder)

end GaloisForLFunctions.HTGeometry
