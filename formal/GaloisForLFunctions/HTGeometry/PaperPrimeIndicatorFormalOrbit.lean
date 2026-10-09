import GaloisForLFunctions.HTGeometry.PaperArithmeticFormalFlows
import GaloisForLFunctions.HTGeometry.CofinitePacketVandermonde

/-!
# A native infinite-prime packet with finite orbits for every prime clock

The corpus's prime indicator has derivative one for every prime derivation.
It lies in every prime's terminating core, but in no finite-prime polynomial
chart. Its logarithmic flow, in contrast, is genuinely nonpolynomial.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every native prime derivative reads the same infinite-prime packet as an exact coordinate. -/
theorem paperPrimeIndicator_primeDeriv (q : Nat.Primes) :
    primeDeriv (q : ℕ) primeIndicatorProfile = 1 := by
  have hs : ∀ n, primeIndicatorProfile n ≠ 0 → n.Prime := by
    intro n hn
    by_contra h
    exact hn (by simp [h])
  simpa [q.property] using
    primeDeriv_prime_supported (q : ℕ) q.property primeIndicatorProfile hs

/-- Each global prime flow gives the same exact linear motion of this native packet. -/
theorem paperPrimeIndicator_formal_prime_orbit (q : Nat.Primes) :
    paperArithmeticPrimeFormalFlow q primeIndicatorProfile =
      PowerSeries.C primeIndicatorProfile + PowerSeries.X := by
  let D := primeArithmeticDerivation (q : ℕ) q.property
  have hfirst : D primeIndicatorProfile = 1 := by
    simp [D, primeArithmeticDerivation_apply, paperPrimeIndicator_primeDeriv]
  have htwo : D (D primeIndicatorProfile) = 0 := by rw [hfirst]; simp
  change paperFormalExponential D primeIndicatorProfile = _
  rw [paperFormalExponential_linear_on D _ htwo, hfirst]
  simp

/-- Simultaneous prime termination permits this profile with infinitely many active primes. -/
theorem paperPrimeIndicator_mem_every_terminatingCore (q : Nat.Primes) :
    primeIndicatorProfile ∈
      paperTerminatingCore (primeArithmeticDerivation (q : ℕ) q.property) := by
  apply (paperTerminatingCore_mem_iff _ _).mpr
  refine ⟨2, ?_⟩
  change primeArithmeticDerivation (q : ℕ) q.property
    (primeArithmeticDerivation (q : ℕ) q.property primeIndicatorProfile) = 0
  have h : primeArithmeticDerivation (q : ℕ) q.property primeIndicatorProfile = 1 := by
    simp [primeArithmeticDerivation_apply, paperPrimeIndicator_primeDeriv]
  rw [h]
  simp

/-- No finite-prime chart contains this simultaneously terminating native input. -/
theorem paperPrimeIndicator_not_mem_finite_chart (S : Finset Nat.Primes) :
    primeIndicatorProfile ∉ paperPrimePolynomialAlgebra S := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset S
  intro hmem
  have h := paperPrimePolynomialAlgebra_primeDeriv_outside S q
    ⟨primeIndicatorProfile, hmem⟩ hq
  change primeDeriv (q : ℕ) primeIndicatorProfile = 0 at h
  rw [paperPrimeIndicator_primeDeriv] at h
  exact one_ne_zero h

/-- Every finite-prime chart lies in every prime core, including primes absent from that chart. -/
theorem paperPrimePolynomialAlgebra_le_every_terminatingCore (S : Finset Nat.Primes)
    (q : Nat.Primes) :
    paperPrimePolynomialAlgebra S ≤
      paperTerminatingCore (primeArithmeticDerivation (q : ℕ) q.property) := by
  classical
  by_cases hq : q ∈ S
  · exact paperPrimePolynomialAlgebra_le_terminatingCore S ⟨q, hq⟩
  · intro f hf
    apply (paperTerminatingCore_mem_iff _ _).mpr
    refine ⟨1, ?_⟩
    exact paperPrimePolynomialAlgebra_primeDeriv_outside S q ⟨f, hf⟩ hq

/-- The very same packet has an infinite logarithmic orbit, separating the two native clocks. -/
theorem paperPrimeIndicator_log_orbit_not_polynomial :
    ¬ ∃ P : Polynomial (ArithmeticFunction ℂ),
      paperArithmeticLogFormalFlow primeIndicatorProfile =
        (P : PowerSeries (ArithmeticFunction ℂ)) := by
  rw [paperArithmeticLogFormalFlow_polynomial_iff]
  intro h
  have h1 : primeIndicatorProfile 1 = 0 := by simp [Nat.not_prime_one]
  rw [h1, zero_smul] at h
  have h2 := congrArg (fun f : ArithmeticFunction ℂ => f 2) h
  simp [Nat.prime_two] at h2

end

end GaloisForLFunctions.HTGeometry
