import GaloisForLFunctions.RHTower.Sieve.Section4BlockFull

/-!
# The set on which every ladder block is small

Matomäki–Radziwiłł's frequency partition replaces a *proved* pointwise bound for the narrow prime
polynomials by the *definition* of the set on which they are small.  In the corpus's normalisation
that set is

```text
   𝒯 = {w : |w| ≤ W  and  ‖primeBlockPoly (geomBlock Q R (1+η) k) w‖ ≤ V_k  for every k < L} ,
```

and on it the hypothesis `hVk` of `Sieve/Section4QSide.setIntegral_normSq_omegaWeighted_le_blocks`
is discharged by membership alone: no zero-free region, no Route-T saving, no analytic input at all
enters the long ladder there.  The whole analytic burden moves to the complement, which is covered
by the `L` single-block exceptional sets of `Sieve/Section4BlockFull`, so its measure is bounded by
their sum — and each of those is what the moment method
(`Sieve/PrimePowerSupport.volume_largeValues_pow_symm_le_of_prime_support`) controls.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The frequencies at which **every** block of the ladder obeys its prescribed bound. -/
def allBlocksSmall (Q : Finset ℕ) (R η : ℝ) (L : ℕ) (Vk : ℕ → ℝ) (W : ℝ) : Set ℝ :=
  Set.Icc (-W) W ∩ ⋂ k ∈ Finset.range L,
    {w : ℝ | ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ Vk k}

theorem measurableSet_allBlocksSmall (Q : Finset ℕ) (R η : ℝ) (L : ℕ) (Vk : ℕ → ℝ) (W : ℝ) :
    MeasurableSet (allBlocksSmall Q R η L Vk W) := by
  refine measurableSet_Icc.inter ?_
  refine MeasurableSet.biInter (Finset.range L).countable_toSet fun k _ => ?_
  exact measurableSet_le
    ((continuous_primeBlockPoly (geomBlock Q R (1 + η) k)).norm).measurable measurable_const

theorem allBlocksSmall_subset (Q : Finset ℕ) (R η : ℝ) (L : ℕ) (Vk : ℕ → ℝ) (W : ℝ) :
    allBlocksSmall Q R η L Vk W ⊆ Set.Icc (-W) W := fun _ hw => hw.1

theorem norm_primeBlockPoly_le_of_mem_allBlocksSmall {Q : Finset ℕ} {R η : ℝ} {L : ℕ}
    {Vk : ℕ → ℝ} {W : ℝ} {k : ℕ} (hk : k ∈ Finset.range L) {w : ℝ}
    (hw : w ∈ allBlocksSmall Q R η L Vk W) :
    ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ ≤ Vk k := by
  have h := hw.2
  rw [Set.mem_iInter₂] at h
  exact h k hk

/-- **The long ladder over the all-small set.**  The pointwise hypothesis of the §4 long-prime
estimate is discharged by membership, so the bound holds with no analytic input on that set. -/
theorem setIntegral_normSq_omegaWeighted_le_blocks_allSmall {Q : Finset ℕ} {A₁ B₁ : ℕ}
    {R η W : ℝ} (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hQrange : ∀ q ∈ Q, R < (q : ℝ) ∧ (q : ℝ) ≤ R * (1 + η) ^ L)
    (v : ℕ → ℝ) (hv : ∀ k ∈ Finset.range L, 0 < v k) (Vk Ik : ℕ → ℝ)
    (hIk : ∀ k ∈ Finset.range L,
      (∫ w in allBlocksSmall Q R η L Vk W,
          ‖logPoly moebiusCoeff (geomCofactorBlockAt A₁ B₁ R η k) w‖ ^ (2 : ℕ)) ≤ Ik k) :
    (∫ w in allBlocksSmall Q R η L Vk W,
        ‖omegaWeightedMoebiusPoly Q (Finset.Icc A₁ B₁) w‖ ^ (2 : ℕ))
      ≤ 2 * ((∑ k ∈ Finset.range L, 1 / v k)
            * ∑ k ∈ Finset.range L, v k * (Vk k ^ (2 : ℕ) * Ik k))
        + 2 * ∫ w in allBlocksSmall Q R η L Vk W,
            ‖ladderProductDefect Q A₁ B₁ R η L w‖ ^ (2 : ℕ) :=
  setIntegral_normSq_omegaWeighted_le_blocks hR hη hL hQprime hQrange v hv Vk Ik
    (measurableSet_allBlocksSmall Q R η L Vk W) (allBlocksSmall_subset Q R η L Vk W)
    (fun _k hk _w hw => norm_primeBlockPoly_le_of_mem_allBlocksSmall hk hw) hIk

/-- The complement of the all-small set inside the window. -/
def someBlockLarge (Q : Finset ℕ) (R η : ℝ) (L : ℕ) (Vk : ℕ → ℝ) (W : ℝ) : Set ℝ :=
  Set.Icc (-W) W \ allBlocksSmall Q R η L Vk W

/-- **The complement is covered by the single-block exceptional sets.** -/
theorem someBlockLarge_subset (Q : Finset ℕ) (R η : ℝ) (L : ℕ) (Vk : ℕ → ℝ) (W : ℝ) :
    someBlockLarge Q R η L Vk W
      ⊆ ⋃ k ∈ Finset.range L, shortExceptional (geomBlock Q R (1 + η) k) W (Vk k) := by
  intro w hw
  have hwIcc : w ∈ Set.Icc (-W) W := hw.1
  have hnot : w ∉ allBlocksSmall Q R η L Vk W := hw.2
  have hex : ∃ k ∈ Finset.range L, Vk k < ‖primeBlockPoly (geomBlock Q R (1 + η) k) w‖ := by
    by_contra hcon
    refine hnot ⟨hwIcc, ?_⟩
    rw [Set.mem_iInter₂]
    intro k hk
    by_contra hk2
    exact hcon ⟨k, hk, lt_of_not_ge hk2⟩
  obtain ⟨k, hk, hklarge⟩ := hex
  rw [Set.mem_iUnion₂]
  exact ⟨k, hk, ⟨hwIcc, hklarge.le⟩⟩

/-- **The measure of the complement is at most the sum of the single-block exceptional measures.** -/
theorem volume_someBlockLarge_le (Q : Finset ℕ) (R η : ℝ) (L : ℕ) (Vk : ℕ → ℝ) (W : ℝ) :
    volume (someBlockLarge Q R η L Vk W)
      ≤ ∑ k ∈ Finset.range L, volume (shortExceptional (geomBlock Q R (1 + η) k) W (Vk k)) := by
  refine le_trans (measure_mono (someBlockLarge_subset Q R η L Vk W)) ?_
  exact measure_biUnion_finset_le _ _

end

end RHTower.Sieve
