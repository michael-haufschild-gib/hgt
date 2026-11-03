import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.AllPrimeLewisCarrier
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckePrimitiveBoundaryPartition

/-!
# Prime Hecke boundary evaluation on the complete Lewis carrier

The primitive finite suffix partition and the equal-row-sum bases determine the
boundary evaluation of every completed Lewis carrier element.
-/

set_option autoImplicit false
noncomputable section
open Complex Set
open GaloisForLFunctions RenormalizedIntersectionTheory MayerCoding MayerScatteringCore

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


/-- Evaluation at `1` is the prime Hecke eigenfunctional on every physical
solution of the Lewis three-term equation; inversion symmetry is unnecessary. -/
theorem lewisHeckeOperator_at_one_of_farey_fixed {p : ℕ} [Fact p.Prime]
    (s : ℂ) (g : ℝ → ℂ) (hg : ∀ a : ℝ, 0 < a → lewisFarey s g a = g a) :
    lewisHeckeOperator p s g 1 = (1 + (p : ℂ) ^ (1 - 2 * s)) * g 1 := by
  classical
  have hp : p.Prime := Fact.out
  let Φ : ℕ × ℕ → ℂ := fun v => lewisHomogeneousValue s g (v.1 : ℝ) (v.2 : ℝ)
  have hΦ : ∀ r t : ℕ, 0 < r → 0 < t → Φ (r, t) = Φ (r + t, t) + Φ (r, r + t) := by
    intro r t hr ht
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    simpa only [Φ, Nat.cast_add] using lewisHomogeneousValue_farey s g hg hrR htR
  have hs := sum_primeHecke_of_harmonic hp Φ hΦ
  have hsum : lewisHeckeOperator p s g 1 = ∑ A ∈ naturalHeckeSet p, Φ (heckeRowPair A) := by
    rw [lewisHeckeOperator_eq_matrixSum]
    apply Finset.sum_congr rfl
    intro A hA
    simp only [lewisMatrixValue, Φ, heckeRowPair, Nat.cast_add, mul_one]
  have h1 : Φ (1, 1) = g 1 := by norm_num [Φ, lewisHomogeneousValue]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpp : Φ (p, p) = (p : ℂ) ^ (-(2 * s)) * Φ (1, 1) := by
    simpa only [Φ, Nat.cast_one, mul_one, Complex.ofReal_natCast] using
      (lewisHomogeneousValue_scale s g (x := 1) hpR one_pos)
  rw [hsum, hs, hpp, h1, ← mul_assoc, natCast_mul_cpow_neg hp.ne_zero (2 * s)]
  ring

/-- The prime boundary eigenfunctional holds on the entire completed source carrier. -/
theorem mayerCompletedLewisCarrier_prime_at_one {p : ℕ} [Fact p.Prime]
    {s : ℂ} {g : ℝ → ℂ} (hg : g ∈ mayerCompletedLewisCarrier s) :
    lewisHeckeOperator p s g 1 = (1 + (p : ℂ) ^ (1 - 2 * s)) * g 1 :=
  lewisHeckeOperator_at_one_of_farey_fixed s g hg.2

#print axioms lewisHeckeOperator_at_one_of_farey_fixed
#print axioms mayerCompletedLewisCarrier_prime_at_one

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
