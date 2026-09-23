import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBlockLevelSplitHM
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyMomentAssembly

/-!
# The level sets of the harmonic level split, measured by the moment method

`MenonHarmonicBlockLevelSplitHM` leaves exactly one free scalar on each dyadic level: the measure
of that level's set.  The corpus already owns the moment bound for the literal harmonic
block-large set (`volume_menonHarmonicBlockLarge_pow_le_local`), at the block's own upper endpoint
and at any moment order `k`.  This file transports it to the level sets of an arbitrary measurable
ambient set and substitutes it into the level split, producing a per-block estimate with **no free
measure at all**.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- A level set inside the window is contained in the literal block-large set. -/
theorem harmonicBlockLevelSet_subset_blockLarge
    {P : Finset ℕ} {Q eta V W : ℝ} (j : ℕ)
    {E : Set ℝ} (hEs : E ⊆ Set.Icc (-W) W) :
    harmonicBlockLevelSet (geomBlock P Q (1 + eta) j) E V
      ⊆ menonHarmonicBlockLarge P Q eta (fun _ => V) W j := by
  intro w hw
  exact ⟨hEs hw.1, hw.2⟩

/-- **The measure of a level set, from the moment method at the block's own endpoint.** -/
theorem volume_harmonicBlockLevelSet_le_localMoment
    (k : ℕ) (hk : 1 ≤ k) {P : Finset ℕ} {Q eta V W : ℝ} (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 0 ≤ W) (hV : 0 < V)
    {E : Set ℝ} (hEs : E ⊆ Set.Icc (-W) W) :
    volume.real (harmonicBlockLevelSet (geomBlock P Q (1 + eta) j) E V)
      ≤ menonHarmonicLocalBlockMomentCost k Q eta W j / V ^ (2 * k) := by
  have hfin : volume (menonHarmonicBlockLarge P Q eta (fun _ => V) W j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun w hw => hw.1))
    simp [Real.volume_Icc]
  have hmono : volume.real (harmonicBlockLevelSet (geomBlock P Q (1 + eta) j) E V)
      ≤ volume.real (menonHarmonicBlockLarge P Q eta (fun _ => V) W j) :=
    measureReal_mono (harmonicBlockLevelSet_subset_blockLarge j hEs) hfin
  have hmoment := volume_menonHarmonicBlockLarge_pow_le_local k hk (P := P) (Q := Q)
    (eta := eta) (V := V) (W := W) j hPprime hQ heta hW hV.le
  have hVpow : (0 : ℝ) < V ^ (2 * k) := by positivity
  rw [le_div_iff₀ hVpow]
  calc
    volume.real (harmonicBlockLevelSet (geomBlock P Q (1 + eta) j) E V) * V ^ (2 * k)
        ≤ volume.real (menonHarmonicBlockLarge P Q eta (fun _ => V) W j) * V ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hmono hVpow.le
    _ = V ^ (2 * k) * volume.real (menonHarmonicBlockLarge P Q eta (fun _ => V) W j) := by
          ring
    _ ≤ menonHarmonicLocalBlockMomentCost k Q eta W j := hmoment

/-- **One harmonic block product with every level measured.**  No free measure remains on any
dyadic level: each is replaced by its own moment budget at order `k`. -/
theorem setIntegral_normSq_harmonicBlockProduct_levelSplit_moment
    (P : Finset ℕ) {D : Finset ℕ} {L' N : ℕ} {Q eta W : ℝ} (j k : ℕ) (hk : 1 ≤ k)
    (hPprime : ∀ p ∈ P, p.Prime) (hQ : 0 < Q) (heta : 0 ≤ eta)
    (hL' : 1 ≤ L') (hN : 1 ≤ N) (hD : D ⊆ Finset.Icc L' N)
    (hW : 1 ≤ W) {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ}
    (hJ : harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ J * V₀) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w
        * logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
            (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
              * ((1 / (L' : ℝ)) ^ (2 : ℕ) * (D.card : ℝ))))
        + ∑ i ∈ Finset.range J,
            (2 ^ (i + 1) * V₀) ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
              (hmMassRecip N (2 * Real.pi * W)
                  (2 * Real.pi *
                    (menonHarmonicLocalBlockMomentCost k Q eta W j
                      / (2 ^ i * V₀) ^ (2 * k)))
                * ((1 / (L' : ℝ)) ^ (2 : ℕ) * (D.card : ℝ)))) := by
  classical
  have hT : (1 : ℝ) ≤ 2 * Real.pi * W := by nlinarith [Real.pi_gt_three]
  have hbase := setIntegral_normSq_harmonicBlockProduct_levelSplit_HM
    P (B := geomBlock P Q (1 + eta) j) (D := D) (L' := L') (N := N)
    (fun p hp => hPprime p (geomBlock_subset P Q (1 + eta) j hp))
    hL' hN hD hW hEm hEs hV₀ hJ
  refine hbase.trans (add_le_add le_rfl ?_)
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine hmMassRecip_mono_volume _ hT ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact volume_harmonicBlockLevelSet_le_localMoment k hk j hPprime hQ heta
    (by linarith) (by positivity) hEs

end

end RHTower.Sieve
