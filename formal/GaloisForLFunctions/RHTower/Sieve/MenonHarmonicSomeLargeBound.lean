import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicAllSmallBound
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyMoment

/-!
# Menon's harmonic some-large Ramaré bound

On the complementary frequency set, every harmonic prime block still has its exact reciprocal
prime-mass envelope.  This gives a closed reciprocal-HM estimate for the entire Ramaré ladder;
`MenonHarmonicFrequencyMoment` independently supplies the power-moment bound for this set's measure.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The exact reciprocal prime mass is a pointwise envelope for a harmonic prime block. -/
theorem norm_harmonicPrimeBlockPoly_le_mass
    {B : Finset ℕ} (hBprime : ∀ p ∈ B, p.Prime) (w : ℝ) :
    ‖harmonicPrimeBlockPoly B w‖ ≤ harmonicPrimeMass B := by
  rw [harmonicPrimeBlockPoly, harmonicPrimeMass]
  refine (norm_sum_le B (fun p => harmonicMoebiusPhase w p)).trans_eq ?_
  refine Finset.sum_congr rfl fun p hp => ?_
  exact norm_harmonicMoebiusPhase_prime (hBprime p hp) w

/-- Complete geometric-ladder bound on Menon's harmonic some-large frequency set.  No unproved
frequency estimate is assumed: the prime factor is bounded by its literal reciprocal mass. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_someLarge
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    (∫ w in menonHarmonicSomeBlockLarge P Q eta L V W,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j))
            (menonHarmonicSomeBlockLarge P Q eta L V W) j := by
  classical
  let E : Set ℝ := menonHarmonicSomeBlockLarge P Q eta L V W
  have hEm : MeasurableSet E :=
    measurableSet_menonHarmonicSomeBlockLarge P Q eta L V W
  have hEs : E ⊆ Set.Icc (-W) W := fun _ hw => hw.1
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange)
  rw [Finset.card_range] at hsplit
  refine hsplit.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L))
  refine Finset.sum_le_sum fun j hj => ?_
  have hBprime : ∀ p ∈ geomBlock P Q (1 + eta) j, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hblock := setIntegral_normSq_harmonicRamareBlock_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    hA₀ hQ heta hW j hPprime (hleft j hj) (hright j hj) hEm hEs
    (fun w _ => norm_harmonicPrimeBlockPoly_le_mass hBprime w)
  simpa [E, menonHarmonicAllSmallBlockCost] using hblock

end

end RHTower.Sieve
