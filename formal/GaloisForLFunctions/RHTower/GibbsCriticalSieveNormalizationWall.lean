import GaloisForLFunctions.HTGeometry.PrimeSieveTransitionSize
import GaloisForLFunctions.RHTower.GibbsCriticalDissipationAntiscaleResonance

/-!
# Critical Gibbs/sieve normalization wall

At the surviving critical Mellin-energy endpoint `r = 1`, the Gibbs Euler baseline grows by
`prod_p (1 + p⁻¹)`.  Multiplication by the coprime-sieve density `prod_p (1 - p⁻¹)` removes exactly
the nonsummable first-order layer and leaves `prod_p (1 - p⁻²)`, the second sieved trace relative
to its unsieved value.  Along every prime exhaustion this regular factor has a finite nonzero
limit.

This is a normalization theorem, not a Möbius-cancellation theorem.  Dividing back by the sieve
density restores the full first-order growth, so Hilbert--Schmidt convergence of the regular layer
cannot by itself control the normalized Route E current.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower.GibbsGas

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Euler inflation factor in the surviving critical Mellin-energy channel `r = 1`. -/
def gibbsCriticalEulerBaseline (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P, (1 + ((p : ℕ) : ℝ)⁻¹)

/-- Multiplication by the prime-sieve density removes exactly the singular first-order part of
the critical Gibbs Euler baseline, leaving the square-summable Euler factor. -/
theorem sieveDensity_mul_gibbsCriticalEulerBaseline (P : Finset Nat.Primes) :
    sieveDensity P * gibbsCriticalEulerBaseline P =
      ∏ p ∈ P, (1 - ((((p : ℕ) : ℝ) ^ (2 : ℕ))⁻¹)) := by
  rw [sieveDensity, gibbsCriticalEulerBaseline, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hp0 : ((p : ℕ) : ℝ) ≠ 0 := hpR.ne'
  field_simp [hp0]
  ring

/-- The sieve-normalized critical Gibbs baseline is exactly the second sieved trace relative to its
unsieved value.  This identifies the remaining factor as the Hilbert--Schmidt regular layer. -/
theorem sieveTrace_empty_two_mul_criticalNormalization (P : Finset Nat.Primes) :
    sieveTrace ∅ 2 * (sieveDensity P * gibbsCriticalEulerBaseline P) = sieveTrace P 2 := by
  rw [sieveTrace_eq_mul_prod (by norm_num : 1 < 2) P,
    sieveTrace_eq_mul_prod (by norm_num : 1 < 2) ∅,
    Finset.prod_empty, mul_one, sieveDensity_mul_gibbsCriticalEulerBaseline]

/-- Along every prime exhaustion, the sieve-normalized critical Gibbs baseline has a finite nonzero
limit: the reciprocal of the unsieved second trace. -/
theorem tendsto_criticalSieveNormalization (e : ℕ ≃ Nat.Primes) :
    Tendsto
      (fun n => sieveDensity (sievePrefix e n) *
        gibbsCriticalEulerBaseline (sievePrefix e n))
      atTop (𝓝 (sieveTrace ∅ 2)⁻¹) := by
  have htrace := tendsto_sieveTrace_sievePrefix e (k := 2) (by norm_num : 1 < 2)
  have hscaled : Tendsto
      (fun n => (sieveTrace ∅ 2)⁻¹ * sieveTrace (sievePrefix e n) 2)
      atTop (𝓝 ((sieveTrace ∅ 2)⁻¹ * 1)) := htrace.const_mul _
  have hne : sieveTrace ∅ 2 ≠ 0 := (sieveTrace_empty_pos (by norm_num : 1 < 2)).ne'
  have hfun :
      (fun n => sieveDensity (sievePrefix e n) *
        gibbsCriticalEulerBaseline (sievePrefix e n)) =
      (fun n => (sieveTrace ∅ 2)⁻¹ * sieveTrace (sievePrefix e n) 2) := by
    funext n
    calc
      sieveDensity (sievePrefix e n) * gibbsCriticalEulerBaseline (sievePrefix e n) =
          (sieveTrace ∅ 2)⁻¹ *
            (sieveTrace ∅ 2 * (sieveDensity (sievePrefix e n) *
              gibbsCriticalEulerBaseline (sievePrefix e n))) := by field_simp [hne]
      _ = (sieveTrace ∅ 2)⁻¹ * sieveTrace (sievePrefix e n) 2 := by
        rw [sieveTrace_empty_two_mul_criticalNormalization]
  rw [hfun]
  simpa using hscaled

/-- Equivalently, raw critical Euler growth is reciprocal sieve-density growth times the regular
second-trace ratio.  Thus removing the density and then restoring source-normal mass restores the
whole first-order divergence. -/
theorem gibbsCriticalEulerBaseline_eq_sieveTrace_div (P : Finset Nat.Primes) :
    gibbsCriticalEulerBaseline P =
      sieveTrace P 2 / (sieveTrace ∅ 2 * sieveDensity P) := by
  have htrace : sieveTrace ∅ 2 ≠ 0 := (sieveTrace_empty_pos (by norm_num : 1 < 2)).ne'
  have hdensity : sieveDensity P ≠ 0 := (sieveDensity_pos P).ne'
  apply (eq_div_iff (mul_ne_zero htrace hdensity)).2
  calc
    gibbsCriticalEulerBaseline P * (sieveTrace ∅ 2 * sieveDensity P) =
        sieveTrace ∅ 2 * (sieveDensity P * gibbsCriticalEulerBaseline P) := by ring
    _ = sieveTrace P 2 := sieveTrace_empty_two_mul_criticalNormalization P

end

end RHTower.GibbsGas
