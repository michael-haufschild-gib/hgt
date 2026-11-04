import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineResidues
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.WeightedPrimeProgressions

/-!
# Prime reciprocal weights in an affine congruence

A coefficient coprime to the prime modulus converts the affine congruence
into one residue class. The progression estimate then depends only on the
modulus and logarithmic width, uniformly in the affine target.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence

/-- An invertible affine multiplier preserves the uniform reciprocal prime bound. -/
theorem exists_weighted_affine_prime_upper :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X b d : ℕ, p.Prime → p₀ ≤ p → p ^ 2 ≤ H → H ≤ X →
      p.Coprime b →
      (∑ k ∈ (Icc H X).filter (fun k => k.Prime ∧ b * k ≡ d [MOD p]),
        Real.log k / (k : ℝ)) ≤
          (1026 / (p : ℝ)) * (1 + Real.log X - Real.log H) := by
  obtain ⟨p₀, hp₀, hbound⟩ := exists_weighted_prime_progression_upper
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X b d hp hpp hpH hHX hpb
  obtain ⟨r, _, hr⟩ := exists_multiplier_residue (b := d) hpb
  have hset : (Icc H X).filter (fun k => k.Prime ∧ b * k ≡ d [MOD p]) =
      (Icc H X).filter (fun k => k.Prime ∧ k ≡ r [MOD p]) := by
    apply filter_congr
    intro k _
    rw [hr k]
  rw [hset]
  exact hbound p H X r hp hpp hpH hHX

#print axioms exists_weighted_affine_prime_upper

end GaloisForLFunctions.BezoutValuationIncidence
