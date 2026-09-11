import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderSwapped

/-!
# The harmonic ladder split at its own masses

`setIntegral_normSq_harmonicRamareBilinear_le_blocks` splits the harmonic Ramare bilinear form
over a ladder of prime blocks at the cost of the *number* of blocks.  Along the schedules the
ladder actually uses, that number is a large power of `log x`, while the blocks' own masses sum to
only `log log log x`; the split alone therefore puts the assembled bound many logarithms above the
trivial one, whatever per-block receiver is used.

`Sieve/HarmonicCauchySchwarz.normSq_sum_le_weighted` is the fix, and its own docstring says so,
but it was only ever applied *inside* a block (over the primes of that block, with weight `p`).
This file applies it to the block split itself, so that the split costs `∑_i 1/v_i` for weights of
the user's choosing — at `v_i = 1/m_i` the total harmonic mass of the ladder, not its length.

The hybrid per-block receiver of `MenonHarmonicRamareLadderSwapped` is then inserted under that
weighted split.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The harmonic Ramare block split at arbitrary positive weights.**  The unweighted form pays
the number of blocks; this one pays `∑_i 1/v_i`. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_blocks_weighted
    {P s : Finset ℕ} {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P)
    (v : ι → ℝ) (hv : ∀ i ∈ I, 0 < v i) :
    (∫ w in E, ‖harmonicRamareBilinear P s w‖ ^ 2)
      ≤ (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i *
          ∫ w in E, ‖harmonicRamareBlock P s (B i) w‖ ^ 2 := by
  classical
  have hpt : ∀ w : ℝ, ‖harmonicRamareBilinear P s w‖ ^ 2
      ≤ (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i * ‖harmonicRamareBlock P s (B i) w‖ ^ 2 := by
    intro w
    rw [harmonicRamareBilinear_eq_sum_blocks w I B hdisj hcover]
    exact normSq_sum_le_weighted I v hv (fun i => harmonicRamareBlock P s (B i) w)
  have hcont : Continuous fun w : ℝ => ‖harmonicRamareBilinear P s w‖ ^ 2 := by
    refine (continuous_finsetSum P fun p _ => ?_).norm.pow 2
    exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)
  have hcontB : ∀ i : ι, Continuous fun w : ℝ =>
      ‖harmonicRamareBlock P s (B i) w‖ ^ 2 := fun i =>
    ((continuous_harmonicRamareBlock P s (B i)).norm).pow 2
  have hcontS : Continuous fun w : ℝ =>
      (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i * ‖harmonicRamareBlock P s (B i) w‖ ^ 2 :=
    (continuous_finsetSum I fun i _ => (hcontB i).const_mul _).const_mul _
  have hint1 : IntegrableOn (fun w : ℝ => ‖harmonicRamareBilinear P s w‖ ^ 2) E volume :=
    (hcont.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hint2 : IntegrableOn (fun w : ℝ =>
      (∑ i ∈ I, 1 / v i) * ∑ i ∈ I, v i * ‖harmonicRamareBlock P s (B i) w‖ ^ 2) E volume :=
    (hcontS.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hint1 hint2 hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum I fun i _ =>
    (((hcontB i).const_mul (v i)).integrableOn_Icc (a := -W) (b := W)).mono_set hEs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]

/-- **The hybrid geometric ladder under the weighted split.**  Every block still takes the better
of the two receivers; the split now costs `∑_j 1/v_j` instead of the block count. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_min_weighted
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V v : ℕ → ℝ) (hv : ∀ j ∈ Finset.range L, 0 < v j)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    (htop : ∀ j ∈ Finset.range L, 1 ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V j) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ (∑ j ∈ Finset.range L, 1 / v j) * ∑ j ∈ Finset.range L, v j *
          min (menonHarmonicAllSmallBlockCost P A₀ B₀ Q eta W (V j) E j)
            (menonHarmonicSwappedBlockCost P A₀ B₀ Q eta W E j) := by
  classical
  have hr : 1 ≤ 1 + eta := by linarith
  have hsplit := setIntegral_normSq_harmonicRamareBilinear_le_blocks_weighted
    (P := P) (s := Finset.Icc A₀ B₀) (W := W) hEm hEs
    (Finset.range L) (geomBlock P Q (1 + eta))
    (geomBlock_pairwiseDisjoint P hQ hr L)
    (geomBlock_biUnion_eq P Q (1 + eta) hL hPrange) v hv
  have hweight : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, 1 / v j :=
    Finset.sum_nonneg fun j hj => le_of_lt (div_pos one_pos (hv j hj))
  refine hsplit.trans (mul_le_mul_of_nonneg_left ?_ hweight)
  refine Finset.sum_le_sum fun j hj => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hv j hj).le
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_min
    hA₀ hQ heta hW j hPprime (hleft j hj) (hright j hj) (htop j hj) hEm hEs
    (hprime j hj)

end

end RHTower.Sieve
