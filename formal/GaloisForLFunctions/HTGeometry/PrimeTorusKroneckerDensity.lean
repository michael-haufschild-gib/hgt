import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier

/-!
# The prime diagonal flow is dense in the aperture torus

The finite-aperture carrier law reads the cutoff Euler product `∏_{p ≤ N} (1 - p^{-σ-it})^{-1}` as an
observable of the prime torus `T^{π(N)}`, and needs the arithmetic translation orbit to be *dense* in
that torus: the phases `p^{it}`, `p ≤ N`, can be steered simultaneously to any prescribed values.
Unique factorization makes the coordinate log-frequencies `{log p : p ≤ N}` rationally independent,
so Kronecker's approximation theorem applies verbatim.

This replaces the density assertion of the carrier law by a theorem.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- The character `t ↦ e^{i t log n}` is the phase `n^{it}`. -/
theorem expChar_log_eq_cpow {n : ℕ} (hn : 0 < n) (t : ℝ) :
    expChar (Real.log n) t = (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hne : ((n : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hn.ne'
  rw [Complex.cpow_def_of_ne_zero hne, expChar, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- **Kronecker density of the prime diagonal flow.**  For every aperture `N`, every prescribed phase
vector on the primes `p ≤ N` and every tolerance, some real time steers all the phases `p^{it}`
simultaneously into the prescribed neighbourhood. -/
theorem primeTorus_kronecker_dense (N : ℕ) (θ : primesLE N → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ∀ p : primesLE N,
      ‖expChar (Real.log ((p : Nat.Primes) : ℕ)) t
        - Complex.exp ((θ p : ℝ) * Complex.I)‖ < ε :=
  kronecker_approx (primeAperture_linearIndependent N) θ hε

/-- The same statement written with the arithmetic phases `p^{it}` themselves. -/
theorem primeTorus_cpow_dense (N : ℕ) (θ : primesLE N → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ∀ p : primesLE N,
      ‖(((p : Nat.Primes) : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)
        - Complex.exp ((θ p : ℝ) * Complex.I)‖ < ε := by
  obtain ⟨t, ht⟩ := primeTorus_kronecker_dense N θ hε
  refine ⟨t, fun p => ?_⟩
  have hp : 0 < ((p : Nat.Primes) : ℕ) := (p : Nat.Primes).2.pos
  rw [← expChar_log_eq_cpow hp t]
  exact ht p

end

end GaloisForLFunctions
