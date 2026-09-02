import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownSupport

/-!
# Integral coefficient energy of the Matomäki--Teräväinen prime amplifier

The prime amplifier has literal zero-one coefficients before powering.  Consequently every
powered coefficient is the natural cardinality of its prime-product fibre.  In particular, each
nonzero coefficient contributes at least one unit to squared coefficient energy, so support
cardinality is controlled by the exact energy of every Watt block.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The literal prime indicator equals one on its declared support. -/
theorem mtTypeIPrimeCoeff_eq_one_of_mem
    {P : ℕ} {j : Fin (2 * P)}
    (hj : j ∈ mtTypeIPrimeCoeffSupport P) :
    mtTypeIPrimeCoeff P j = 1 := by
  rw [mem_mtTypeIPrimeCoeffSupport] at hj
  rw [mtTypeIPrimeCoeff]
  split
  next h => rfl
  next h =>
    exfalso
    apply hj
    rw [mtTypeIPrimeCoeff, if_neg h]

/-- Every powered prime-amplifier coefficient is exactly its supported ordered-fibre count. -/
theorem convPow_mtTypeIPrimeCoeff_eq_powFibreOn_card
    (P ell : ℕ) (j : Fin ((2 * P) ^ ell)) :
    convPow (2 * P) ell (mtTypeIPrimeCoeff P) j =
      ((powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card : ℂ) := by
  classical
  have hconv :
      convPow (2 * P) ell (mtTypeIPrimeCoeff P) j =
        ∑ p ∈ powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j,
          ∏ i : Fin ell, mtTypeIPrimeCoeff P (p i) := by
    rw [convPow, powFibreOn]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro p _ hne i
    exact mem_mtTypeIPrimeCoeffSupport.mpr
      ((Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i))
  rw [hconv]
  calc
    (∑ p ∈ powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j,
        ∏ i : Fin ell, mtTypeIPrimeCoeff P (p i)) =
        ∑ _p ∈ powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j,
          (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.prod_eq_one
      intro i hi
      apply mtTypeIPrimeCoeff_eq_one_of_mem
      rw [powFibreOn, Finset.mem_filter] at hp
      exact hp.2 i
    _ = ((powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card : ℂ) := by
      simp

/-- A nonzero block coefficient contributes at least one unit of squared energy. -/
theorem one_le_normSq_mtTypeIPrimeRaisedCoeff_of_mem_blockSupport
    {P ell B m : ℕ}
    (hm : m ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B) :
    (1 : ℝ) ≤ ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 := by
  let m' : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B) := ⟨m, hm⟩
  let j := mtTypeIPrimeRaisedBlockSupportIndex P ell B m'
  have hj := mtTypeIPrimeRaisedBlockSupportIndex_spec P ell B m'
  have hjm : (j : ℕ) + 1 = m := by
    simpa only [j, m'] using hj.2
  have hcoeff : mtTypeIPrimeRaisedCoeff P ell m =
      ((powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card : ℂ) := by
    rw [mtTypeIPrimeRaisedCoeff, ← hjm, anchoredCoeff_add_one]
    exact convPow_mtTypeIPrimeCoeff_eq_powFibreOn_card P ell j
  have hcardne :
      (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card ≠ 0 := by
    intro hzero
    apply hj.1
    rw [convPow_mtTypeIPrimeCoeff_eq_powFibreOn_card, hzero]
    simp
  have hcard : 1 ≤
      (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card :=
    Nat.one_le_iff_ne_zero.mpr hcardne
  have hcardR : (1 : ℝ) ≤
      ((powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card : ℝ) := by
    exact_mod_cast hcard
  rw [hcoeff]
  have hnorm :
      ‖((powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card : ℂ)‖ =
        ((powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card : ℝ) := by
    norm_num
  rw [hnorm]
  nlinarith

/-- Exact block support is at most exact block coefficient energy. -/
theorem card_mtTypeIPrimeRaisedBlockSupportPNat_le_energy
    (P ell B : ℕ) :
    ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) ≤
      ∑ m ∈ Finset.Ioc B (2 * B),
        ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 := by
  rw [card_mtTypeIPrimeRaisedBlockSupportPNat]
  calc
    ((mtTypeIPrimeRaisedBlockSupportNat P ell B).card : ℝ) =
        ∑ _m ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B, (1 : ℝ) := by
      simp
    _ ≤ ∑ m ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B,
        ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 := by
      exact Finset.sum_le_sum fun m hm =>
        one_le_normSq_mtTypeIPrimeRaisedCoeff_of_mem_blockSupport hm
    _ ≤ ∑ m ∈ Finset.Ioc B (2 * B),
        ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun m _ _ => sq_nonneg _)

/-- A Watt block contains at most its interval length many nonzero anchors. -/
theorem card_mtTypeIPrimeRaisedBlockSupportPNat_le_length
    (P ell B : ℕ) :
    (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card ≤ B := by
  rw [card_mtTypeIPrimeRaisedBlockSupportPNat]
  calc
    (mtTypeIPrimeRaisedBlockSupportNat P ell B).card ≤
        (Finset.Ioc B (2 * B)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = B := by
      rw [Nat.card_Ioc]
      omega

end

end RHTower.Sieve
