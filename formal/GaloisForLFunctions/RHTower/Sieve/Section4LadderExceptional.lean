import GaloisForLFunctions.RHTower.Sieve.Section4AllBlocksSmall
import GaloisForLFunctions.RHTower.Sieve.Section4ExceptionalCofactor

/-!
# The cofactor over the exceptional set of the whole ladder

`Sieve/Section4ExceptionalCofactor` bounds the mean square of the innermost cofactor over the
exceptional set of **one** prime block.  Matomäki–Radziwiłł's partition needs the exceptional set of
the whole ladder — the frequencies at which *some* block fails to be small — because the
complementary set `allBlocksSmall` is where the pointwise hypothesis becomes free.

Its Dirichlet-variable form is the finite union of the single-block exceptional sets, so Lemma 2.5
applies term by term and Lemma 2.6 applies to the union: the measure is at most the sum of the
`L` moment-method bounds, and the Halász–Montgomery estimate consumes that sum.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The Dirichlet-variable exceptional set of the whole ladder. -/
def ladderExceptionalD (Q : Finset ℕ) (R η : ℝ) (L NA : ℕ) (Vk : ℕ → ℝ) (T : ℝ) : Set ℝ :=
  ⋃ k ∈ Finset.range L,
    blockExceptional (geomBlock Q R (1 + η) k) moebiusCoeff NA T (Vk k)

theorem measurableSet_ladderExceptionalD (Q : Finset ℕ) (R η : ℝ) (L NA : ℕ) (Vk : ℕ → ℝ)
    (T : ℝ) : MeasurableSet (ladderExceptionalD Q R η L NA Vk T) := by
  refine MeasurableSet.biUnion (Finset.range L).countable_toSet fun k _ => ?_
  exact measurableSet_blockExceptional _ _ _ _ _

theorem ladderExceptionalD_subset (Q : Finset ℕ) (R η : ℝ) (L NA : ℕ) (Vk : ℕ → ℝ) (T : ℝ) :
    ladderExceptionalD Q R η L NA Vk T ⊆ Set.Icc (-T) T := by
  intro w hw
  rw [ladderExceptionalD, Set.mem_iUnion₂] at hw
  obtain ⟨k, _, hk⟩ := hw
  exact blockExceptional_subset _ _ _ _ _ hk

/-- **Lemma 2.5 for the whole ladder.**  The measure of the ladder's exceptional set is at most the
sum of the `L` single-block moment bounds. -/
theorem measureReal_ladderExceptionalD_le {Q : Finset ℕ} {R η : ℝ} {L NA k' : ℕ} {Vk : ℕ → ℝ}
    {T : ℝ} (hQprime : ∀ q ∈ Q, q.Prime) (hk' : 1 ≤ k') (hT : 0 ≤ T)
    (hV : ∀ k ∈ Finset.range L, 0 < Vk k) :
    volume.real (ladderExceptionalD Q R η L NA Vk T)
      ≤ ∑ k ∈ Finset.range L,
          2 * ((T + 4 * ((NA ^ k' : ℕ) : ℝ) * (1 + Real.log ((NA ^ k' : ℕ) : ℝ)))
              * ((k' : ℝ) ^ k' * (((geomBlock Q R (1 + η) k).card : ℕ) : ℝ) ^ k'))
            / Vk k ^ (2 * k') := by
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine Finset.sum_le_sum fun k hk => ?_
  refine volume_blockExceptional_le (B := geomBlock Q R (1 + η) k) ?_ hk' hT (hV k hk)
  intro p hp
  exact hQprime p (geomBlock_subset (P := Q) (Q := R) (r := 1 + η) (j := k) hp)

/-- The ladder's exceptional set in the Gallagher variable is contained in the scaled preimage. -/
theorem someBlockLarge_subset_preimage {Q : Finset ℕ} {R η : ℝ} {L NA : ℕ} {Vk : ℕ → ℝ} {W : ℝ}
    (hB : ∀ k ∈ Finset.range L, geomBlock Q R (1 + η) k ⊆ Finset.Icc 1 NA) :
    someBlockLarge Q R η L Vk W
      ⊆ (fun v : ℝ => 2 * Real.pi * v) ⁻¹'
          (ladderExceptionalD Q R η L NA Vk (2 * Real.pi * W)) := by
  intro w hw
  obtain ⟨k, hk, hkw⟩ := Set.mem_iUnion₂.1 (someBlockLarge_subset Q R η L Vk W hw)
  have hpre := shortExceptional_eq_preimage (hB k hk) W (Vk k)
  rw [hpre] at hkw
  refine Set.mem_preimage.2 ?_
  rw [ladderExceptionalD, Set.mem_iUnion₂]
  exact ⟨k, hk, hkw⟩

/-- **The innermost cofactor over the ladder's exceptional set.**  Halász–Montgomery on the union,
with Lemma 2.5 substituted term by term. -/
theorem setIntegral_normSq_logPoly_someBlockLarge_le (a : ℕ → ℂ) {Q D : Finset ℕ} {R η : ℝ}
    {L NA ND k' : ℕ} {Vk : ℕ → ℝ} {W Ω : ℝ}
    (hQprime : ∀ q ∈ Q, q.Prime) (hB : ∀ k ∈ Finset.range L, geomBlock Q R (1 + η) k ⊆ Finset.Icc 1 NA)
    (hND : 1 ≤ ND) (hD : D ⊆ Finset.Icc 1 ND) (hk' : 1 ≤ k') (hW : 0 ≤ W)
    (hV : ∀ k ∈ Finset.range L, 0 < Vk k) (hΩ : 0 ≤ Ω) (ha : ∀ n, ‖a n‖ ≤ Ω) :
    (∫ w in someBlockLarge Q R η L Vk W, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * ((2 * (ND : ℝ)
            + (((Nat.log 2 ND : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
                + 3072 * (ND : ℝ))
              * ∑ k ∈ Finset.range L,
                  2 * (((2 * Real.pi * W)
                      + 4 * ((NA ^ k' : ℕ) : ℝ) * (1 + Real.log ((NA ^ k' : ℕ) : ℝ)))
                    * ((k' : ℝ) ^ k' * (((geomBlock Q R (1 + η) k).card : ℕ) : ℝ) ^ k'))
                    / Vk k ^ (2 * k'))
          * (Ω ^ 2 * (D.card : ℝ))) := by
  classical
  have hT0 : (0 : ℝ) ≤ 2 * Real.pi * W := by positivity
  have hSm := measurableSet_ladderExceptionalD Q R η L NA Vk (2 * Real.pi * W)
  have hSs := ladderExceptionalD_subset Q R η L NA Vk (2 * Real.pi * W)
  have hcont : Continuous fun w : ℝ => ‖logPoly a D w‖ ^ 2 :=
    (((continuous_logPoly a D).norm).pow 2)
  have hmono : (∫ w in someBlockLarge Q R η L Vk W, ‖logPoly a D w‖ ^ 2)
      ≤ ∫ w in (fun v : ℝ => 2 * Real.pi * v) ⁻¹'
          (ladderExceptionalD Q R η L NA Vk (2 * Real.pi * W)), ‖logPoly a D w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set ?_ ?_
      (Filter.Eventually.of_forall (someBlockLarge_subset_preimage hB))
    · refine (hcont.integrableOn_Icc (a := -W) (b := W)).mono_set ?_
      intro v hv
      have hvs : 2 * Real.pi * v ∈ Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W) := hSs hv
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      constructor
      · nlinarith [hvs.1, hpi]
      · nlinarith [hvs.2, hpi]
    · exact Filter.Eventually.of_forall fun w => by positivity
  refine hmono.trans ?_
  refine (setIntegral_normSq_logPoly_le_HM a hND hD hSm hSs hΩ ha).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hC0 : (0 : ℝ) ≤ ((Nat.log 2 ND : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
      + 3072 * (ND : ℝ) := by positivity
  have hvol := measureReal_ladderExceptionalD_le (Q := Q) (R := R) (η := η) (L := L) (NA := NA)
    (k' := k') (Vk := Vk) (T := 2 * Real.pi * W) hQprime hk' hT0 hV
  nlinarith [mul_le_mul_of_nonneg_left hvol hC0]

end

end RHTower.Sieve
