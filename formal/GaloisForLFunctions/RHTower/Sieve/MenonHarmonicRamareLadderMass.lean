import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderWeighted

/-!
# The harmonic ladder split at its blocks' own harmonic masses

The weighted split of `MenonHarmonicRamareLadderWeighted` costs `∑_i 1/v_i` for weights of the
user's choosing.  Choosing `v_i = 1/(harmonic mass of block i)` makes that cost exactly the
**total harmonic mass of the designated prime range** — `∑_{p ∈ P} 1/p`, which along every
schedule the ladder uses is `O(log log log x)`, whereas the block count is a large power of
`log x`.

This is the split the quantitative assembly has to use.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The harmonic mass of a disjoint union is the sum of the blocks' harmonic masses. -/
theorem harmonicPrimeMass_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) :
    harmonicPrimeMass (I.biUnion B) = ∑ i ∈ I, harmonicPrimeMass (B i) := by
  classical
  rw [harmonicPrimeMass, Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **The harmonic Ramare block split at the blocks' own masses.**  The split costs the total
harmonic mass of the designated prime range, not the number of blocks. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_blocks_mass
    {P s : Finset ℕ} {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P)
    (hmass : ∀ i ∈ I, 0 < harmonicPrimeMass (B i)) :
    (∫ w in E, ‖harmonicRamareBilinear P s w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ i ∈ I,
          (∫ w in E, ‖harmonicRamareBlock P s (B i) w‖ ^ 2) / harmonicPrimeMass (B i) := by
  classical
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_blocks_weighted
    (P := P) (s := s) (W := W) hEm hEs I B hdisj hcover
    (fun i => 1 / harmonicPrimeMass (B i))
    (fun i hi => div_pos one_pos (hmass i hi))
  have h1 : (∑ i ∈ I, 1 / (1 / harmonicPrimeMass (B i))) = harmonicPrimeMass P := by
    rw [← hcover, harmonicPrimeMass_biUnion I B hdisj]
    exact Finset.sum_congr rfl fun i _ => one_div_one_div _
  refine hbase.trans (le_of_eq ?_)
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_div, inv_mul_eq_div]

/-- **The hybrid geometric ladder split at the blocks' own masses.** -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_min_mass
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V : ℕ → ℝ)
    (hmass : ∀ j ∈ Finset.range L,
      0 < harmonicPrimeMass (geomBlock P Q (1 + eta) j))
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V j) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ harmonicPrimeMass P * ∑ j ∈ Finset.range L,
          min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j) E j)
            (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j)
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
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_min
    hA₀ hQ heta hW j hPprime (hleft j hj) (hright j hj) (htop j hj) hEm hEs
    (hprime j hj)

end

end RHTower.Sieve
