import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBlockLevelSplit

/-!
# Menon's ladder receiver: the mass split over the blocks, the level split inside each

This is the assembly of the two corrections built above.

* The ladder is split at the blocks' own harmonic masses, so the split costs
  `∑_{p ∈ P} 1/p`, not the number of blocks.
* Inside each block the prime factor is never replaced by a supremum on the whole window; it is
  split into dyadic levels, so every level above the base `V₀ j` is charged to the measure of its
  own level set — which is exactly what a large-values estimate bounds.

Both the base level and the number of levels are free per block, so a schedule can choose them.
Nothing is assumed: the cofactor replacement error is the corpus's exact
`harmonicRamareCofactorPoly` discrepancy, retained term by term.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The complete harmonic Ramare ladder: mass split outside, level split inside.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_levelSplit_mass
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    (V₀ : ℕ → ℝ) (hV₀ : ∀ j ∈ Finset.range L, 0 < V₀ j)
    (J : ℕ → ℕ)
    (hJ : ∀ j ∈ Finset.range L,
      harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ (J j) * V₀ j)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass P * ∑ j ∈ Finset.range L,
          (2 * (V₀ j ^ (2 : ℕ) *
                (∫ w in E, ‖logPoly (harmonicRamareCofactorCoeff P)
                  (harmonicGeomCofactorBlock A₀ B₀ Q eta j) w‖ ^ (2 : ℕ))
              + ∑ i ∈ Finset.range (J j),
                  (2 ^ (i + 1) * V₀ j) ^ (2 : ℕ)
                    * ∫ w in E ∩ {w | 2 ^ i * V₀ j ≤
                          ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖},
                        ‖logPoly (harmonicRamareCofactorCoeff P)
                          (harmonicGeomCofactorBlock A₀ B₀ Q eta j) w‖ ^ (2 : ℕ))
            + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) *
                ∑ p ∈ geomBlock P Q (1 + eta) j, (1 / (p : ℝ)) *
                  (∫ w in E, ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w
                    - logPoly (harmonicRamareCofactorCoeff P)
                        (harmonicGeomCofactorBlock A₀ B₀ Q eta j) w‖ ^ (2 : ℕ)))
          / harmonicPrimeMass (geomBlock P Q (1 + eta) j) := by
  classical
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange) hmass
  have hPmass : (0 : ℝ) ≤ harmonicPrimeMass P :=
    Finset.sum_nonneg fun p _ => by positivity
  refine hsplit.trans (mul_le_mul_of_nonneg_left ?_ hPmass)
  refine Finset.sum_le_sum fun j hj => ?_
  refine div_le_div_of_nonneg_right ?_ (hmass j hj).le
  exact setIntegral_normSq_harmonicRamareBlock_le_levelSplit
    (harmonicGeomCofactorBlock A₀ B₀ Q eta j)
    (fun p hp => hPprime p (geomBlock_subset P Q (1 + eta) j hp))
    hEm hEs (hV₀ j hj) (hJ j hj)

end

end RHTower.Sieve
