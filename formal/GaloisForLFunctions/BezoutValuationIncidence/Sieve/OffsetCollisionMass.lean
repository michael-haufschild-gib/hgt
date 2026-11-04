import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineCollisionMass

/-!
# Affine collision mass summed over a finite offset strip

Each nonzero offset is a unit modulo the larger source prime. Summing the
uniform collision-row estimate costs only the number of offsets, while
the prime-progression gain and full proper-power remainder are preserved.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- Finite offset strips retain the reciprocal-prime collision gain. -/
theorem exists_offset_collision_mass_upper :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X Y l : ℕ,
      p.Prime → p₀ ≤ p → p ^ 2 ≤ H → H ≤ X →
      ∀ (I : Finset ℕ) (b : ℕ → ℕ), (∀ h ∈ I, p.Coprime (b h)) →
      ∀ j ∈ I, ∀ (f : ℕ → ℕ → ℝ) (U : ℝ), 0 ≤ U →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ I, |f k h| ≤ U) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ I, f k h ≠ 0 → k ∈ Icc H X) →
      (∑ h ∈ I, ∑ k ∈ (Icc 1 Y).filter (fun k => p.Coprime k ∧
          multiplierResidue p k (b h) ≡ multiplierResidue p l (b j) [MOD p]),
        (vonMangoldt k / (k : ℝ)) * f k h) ≤
        (I.card : ℝ) * U * ((1026 / (p : ℝ)) * (1 + Real.log X - Real.log H) +
          576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
  obtain ⟨p₀, hp₀, hbound⟩ := exists_affine_collision_mass_upper_unit_offsets
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X Y l hp hpp hpH hHX I b hb j hj f U hU hf hsupp
  calc
    _ ≤ ∑ h ∈ I, U * ((1026 / (p : ℝ)) * (1 + Real.log X - Real.log H) +
        576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
      apply sum_le_sum
      intro h hh
      exact hbound p H X Y l (b h) (b j) hp hpp hpH hHX (hb h hh) (hb j hj)
        (fun k => f k h) U hU (fun k hk => hf k hk h hh) (fun k hk => hsupp k hk h hh)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

#print axioms exists_offset_collision_mass_upper

end GaloisForLFunctions.BezoutValuationIncidence
