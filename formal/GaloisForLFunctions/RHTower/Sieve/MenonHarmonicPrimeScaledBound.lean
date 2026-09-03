import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeAbel
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockScaledBound

/-!
# Scaled Route-T bound for Menon's harmonic prime block

The corpus's scaled twisted-prime envelope controls every ordinary prefix. Reciprocal Abel
summation therefore places the same envelope over the harmonic prime polynomial, divided by the
prime interval's left endpoint.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The scaled Route-T prime estimate on the critical line `Re s = 1`. -/
theorem exists_norm_harmonicPrimeBlockPoly_scaled_le :
    ∃ A delta Ctot τ₀ : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (B : Finset ℕ) (a b : ℕ) (D w : ℝ), 1 ≤ a → a ≤ b →
        (∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b)) → 1 ≤ D →
        τ₀ ≤ |(-(2 * Real.pi * w))| →
        ‖harmonicPrimeBlockPoly B w‖
          ≤ ((4 / Real.log 2)
            * (scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max (b : ℝ) 1)
              + 7 * Real.exp 9)) / ((a + 1 : ℕ) : ℝ) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_primeBlockPoly_scaled_le
  refine ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, ?_⟩
  intro B a b D w ha hab hB hD hτ
  let E : ℝ := (4 / Real.log 2) *
    (scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max (b : ℝ) 1)
      + 7 * Real.exp 9)
  have hprefix : ∀ m : ℕ, a + 1 ≤ m → m ≤ b + 1 →
      ‖primeBlockPoly (primesRange a (m - 1)) w‖ ≤ E := by
    intro m ham hmb
    have haend : a ≤ m - 1 := by omega
    have hbase := hbound (primesRange a (m - 1)) a (m - 1) D w ha haend
      (fun p => mem_primesRange) hD hτ
    have hD0 : 0 < D := by linarith
    have hτ1 : (1 : ℝ) ≤ |(-(2 * Real.pi * w))| := by linarith
    have hN1 : (1 : ℝ) ≤ max (((m - 1 : ℕ) : ℝ)) 1 := le_max_right _ _
    have horder : max (((m - 1 : ℕ) : ℝ)) 1 ≤ max (b : ℝ) 1 := by
      have hcast : (((m - 1 : ℕ) : ℝ)) ≤ (b : ℝ) := by
        exact_mod_cast (by omega : m - 1 ≤ b)
      exact max_le_max hcast le_rfl
    have hmono := scaledTwistEnvelope_mono
      (A := A) (delta := delta) (Ctot := Ctot) (D := D)
      (τ := -(2 * Real.pi * w)) hCtot.le hD0 hτ1 hN1 horder
    have hadd :
        scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w))
            (max (((m - 1 : ℕ) : ℝ)) 1) + 7 * Real.exp 9
          ≤ scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w))
              (max (b : ℝ) 1) + 7 * Real.exp 9 := by
      linarith
    have hfac : 0 ≤ 4 / Real.log 2 := by positivity
    exact hbase.trans (mul_le_mul_of_nonneg_left hadd hfac)
  exact norm_harmonicPrimeBlockPoly_le_of_prefix hab hB w hprefix

end

end RHTower.Sieve
