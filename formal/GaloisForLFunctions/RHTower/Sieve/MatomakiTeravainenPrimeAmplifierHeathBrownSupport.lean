import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierFactorialEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierSparseMass
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueLemma34

/-!
# Heath--Brown support for a Matomäki--Teräväinen amplifier block

This packages one literal Watt block as a finite set of positive integers and normalizes its
coefficients by the sharp factorial pointwise bound.  All support and boundedness conditions of
Heath--Brown's sparse factor are then intrinsic.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Natural support of one literal raised-prime Watt block. -/
def mtTypeIPrimeRaisedBlockSupportNat (P ell B : ℕ) : Finset ℕ :=
  (Finset.Ioc B (2 * B)).filter fun m => mtTypeIPrimeRaisedCoeff P ell m ≠ 0

/-- A supported natural anchor, bundled as a positive integer. -/
def mtTypeIPrimeRaisedBlockAnchor
    (P ell B : ℕ) (m : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B)) : PNat :=
  ⟨m.1, by
    have hm := m.property
    change m.1 ∈ (Finset.Ioc B (2 * B)).filter
      (fun n => mtTypeIPrimeRaisedCoeff P ell n ≠ 0) at hm
    rw [Finset.mem_filter] at hm
    have hBm := (Finset.mem_Ioc.mp hm.1).1
    omega⟩

theorem mtTypeIPrimeRaisedBlockAnchor_injective (P ell B : ℕ) :
    Function.Injective (mtTypeIPrimeRaisedBlockAnchor P ell B) := by
  intro m n hmn
  exact Subtype.ext (congrArg (fun q : PNat => (q : ℕ)) hmn)

/-- Embedding of natural block support into positive integers. -/
def mtTypeIPrimeRaisedBlockAnchorEmbedding (P ell B : ℕ) :
    ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B) ↪ PNat :=
  ⟨mtTypeIPrimeRaisedBlockAnchor P ell B,
    mtTypeIPrimeRaisedBlockAnchor_injective P ell B⟩

/-- Positive-integer support consumed by Heath--Brown's sparse mean-value theorem. -/
def mtTypeIPrimeRaisedBlockSupportPNat (P ell B : ℕ) : Finset PNat :=
  (mtTypeIPrimeRaisedBlockSupportNat P ell B).attach.map
    (mtTypeIPrimeRaisedBlockAnchorEmbedding P ell B)

theorem card_mtTypeIPrimeRaisedBlockSupportPNat (P ell B : ℕ) :
    (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card =
      (mtTypeIPrimeRaisedBlockSupportNat P ell B).card := by
  simp [mtTypeIPrimeRaisedBlockSupportPNat]

@[simp] theorem mem_mtTypeIPrimeRaisedBlockSupportPNat
    {P ell B : ℕ} {m : PNat} :
    m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B ↔
      (m : ℕ) ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B := by
  constructor
  · intro hm
    rw [mtTypeIPrimeRaisedBlockSupportPNat, Finset.mem_map] at hm
    obtain ⟨n, _hn, hnm⟩ := hm
    have hval := congrArg (fun q : PNat => (q : ℕ)) hnm
    dsimp only [mtTypeIPrimeRaisedBlockAnchorEmbedding,
      mtTypeIPrimeRaisedBlockAnchor] at hval
    change (m : ℕ) ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B
    rw [← hval]
    exact n.property
  · intro hm
    let n : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B) := ⟨m, hm⟩
    rw [mtTypeIPrimeRaisedBlockSupportPNat, Finset.mem_map]
    refine ⟨n, by simp only [Finset.mem_attach], ?_⟩
    apply Subtype.ext
    rfl

theorem mtTypeIPrimeRaisedBlockSupportPNat_lower
    {P ell B : ℕ} {m : PNat}
    (hm : m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B) :
    B < (m : ℕ) := by
  rw [mem_mtTypeIPrimeRaisedBlockSupportPNat,
    mtTypeIPrimeRaisedBlockSupportNat, Finset.mem_filter] at hm
  exact (Finset.mem_Ioc.mp hm.1).1

theorem mtTypeIPrimeRaisedBlockSupportPNat_upper
    {P ell B : ℕ} {m : PNat}
    (hm : m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B) :
    (m : ℕ) ≤ 2 * B := by
  rw [mem_mtTypeIPrimeRaisedBlockSupportPNat,
    mtTypeIPrimeRaisedBlockSupportNat, Finset.mem_filter] at hm
  exact (Finset.mem_Ioc.mp hm.1).2

/-- Chosen complete-vector index named by a nonzero anchored block coefficient. -/
noncomputable def mtTypeIPrimeRaisedBlockSupportIndex
    (P ell B : ℕ) (m : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B)) :
    Fin ((2 * P) ^ ell) :=
  Classical.choose (anchoredCoeff_ne_zero_support (by
    have hm := m.property
    change m.1 ∈ (Finset.Ioc B (2 * B)).filter
      (fun n => mtTypeIPrimeRaisedCoeff P ell n ≠ 0) at hm
    rw [Finset.mem_filter] at hm
    simpa only [mtTypeIPrimeRaisedCoeff] using hm.2))

theorem mtTypeIPrimeRaisedBlockSupportIndex_spec
    (P ell B : ℕ) (m : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B)) :
    convPow (2 * P) ell (mtTypeIPrimeCoeff P)
        (mtTypeIPrimeRaisedBlockSupportIndex P ell B m) ≠ 0 ∧
      ((mtTypeIPrimeRaisedBlockSupportIndex P ell B m : ℕ) + 1) = m :=
  Classical.choose_spec (anchoredCoeff_ne_zero_support (by
    have hm := m.property
    change m.1 ∈ (Finset.Ioc B (2 * B)).filter
      (fun n => mtTypeIPrimeRaisedCoeff P ell n ≠ 0) at hm
    rw [Finset.mem_filter] at hm
    simpa only [mtTypeIPrimeRaisedCoeff] using hm.2))

/-- Block support injects into the complete nonzero support. -/
def mtTypeIPrimeRaisedBlockSupportEmbedding (P ell B : ℕ) :
    ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B) ↪
      ↑(mtTypeIPrimeRaisedSupport P ell) :=
  { toFun := fun m =>
      ⟨mtTypeIPrimeRaisedBlockSupportIndex P ell B m,
        mem_mtTypeIPrimeRaisedSupport.mpr
          (mtTypeIPrimeRaisedBlockSupportIndex_spec P ell B m).1⟩
    inj' := by
      intro m n hmn
      apply Subtype.ext
      have hidx := congrArg
        (fun q : ↑(mtTypeIPrimeRaisedSupport P ell) => ((q.1 : ℕ) + 1)) hmn
      rw [(mtTypeIPrimeRaisedBlockSupportIndex_spec P ell B m).2,
        (mtTypeIPrimeRaisedBlockSupportIndex_spec P ell B n).2] at hidx
      exact hidx }

/-- Every literal block has no more support than the complete powered amplifier. -/
theorem card_mtTypeIPrimeRaisedBlockSupportPNat_le (P ell B : ℕ) :
    (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card ≤
      (mtTypeIPrimeRaisedSupport P ell).card := by
  rw [card_mtTypeIPrimeRaisedBlockSupportPNat]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_embedding
    (mtTypeIPrimeRaisedBlockSupportEmbedding P ell B)

/-- Factorial-normalized coefficient used in Heath--Brown's sparse factor. -/
def mtTypeIPrimeRaisedNormalizedCoeff (P ell : ℕ) (m : ℕ) : ℂ :=
  ((ell.factorial : ℂ)⁻¹) * mtTypeIPrimeRaisedCoeff P ell m

/-- Sharp factorial normalization makes every sparse coefficient unit-bounded. -/
theorem norm_mtTypeIPrimeRaisedNormalizedCoeff_le_one
    (P ell m : ℕ) :
    ‖mtTypeIPrimeRaisedNormalizedCoeff P ell m‖ ≤ 1 := by
  have hfac : (0 : ℝ) < ell.factorial := by
    exact_mod_cast Nat.factorial_pos ell
  have hcoeff := norm_mtTypeIPrimeRaisedCoeff_le_factorial P ell m
  calc
    ‖mtTypeIPrimeRaisedNormalizedCoeff P ell m‖ =
        (ell.factorial : ℝ)⁻¹ * ‖mtTypeIPrimeRaisedCoeff P ell m‖ := by
      simp [mtTypeIPrimeRaisedNormalizedCoeff, norm_inv]
    _ ≤ (ell.factorial : ℝ)⁻¹ * (ell.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = 1 := inv_mul_cancel₀ hfac.ne'

/-- The normalized Heath--Brown sparse factor is exactly the corresponding Watt block. -/
theorem heathBrownSparseOneLineFactor_mtTypeIPrimeRaised_eq
    (P ell B : ℕ) (t : ℝ) :
    heathBrownSparseOneLineFactor
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
        (mtTypeIPrimeRaisedNormalizedCoeff P ell) t =
      ((ell.factorial : ℂ)⁻¹) *
        mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t := by
  change heathBrownSparseOneLineFactor
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
        (mtTypeIPrimeRaisedNormalizedCoeff P ell) t =
      ((ell.factorial : ℂ)⁻¹) *
        mtWattCoefficientBlock
          (anchoredCoeff ((2 * P) ^ ell)
            (convPow (2 * P) ell (mtTypeIPrimeCoeff P))) B t
  rw [mtWattCoefficientBlock_eq_sum_anchoredDirichletTerm_Ioc]
  rw [heathBrownSparseOneLineFactor, mtTypeIPrimeRaisedBlockSupportPNat,
    Finset.sum_map, Finset.mul_sum]
  trans ∑ m ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B,
      ((ell.factorial : ℂ)⁻¹) *
        anchoredDirichletTerm ((2 * P) ^ ell)
          (convPow (2 * P) ell (mtTypeIPrimeCoeff P)) 1 t m
  · refine Finset.sum_bij (fun m _hm => (m : ℕ)) ?_ ?_ ?_ ?_
    · intro m hm
      exact m.property
    · intro m₁ hm₁ m₂ hm₂ heq
      exact Subtype.ext heq
    · intro n hn
      refine ⟨⟨n, hn⟩, by simp only [Finset.mem_attach], rfl⟩
    · intro m hm
      change mtTypeIPrimeRaisedNormalizedCoeff P ell (m : ℕ) *
          (((1 / ((m : ℕ) : ℝ) : ℝ)) : ℂ) *
            heathBrownDirichletPhase (mtTypeIPrimeRaisedBlockAnchor P ell B m) t = _
      rw [mtTypeIPrimeRaisedNormalizedCoeff, anchoredDirichletTerm,
        ← mtTypeIPrimeRaisedCoeff, Real.rpow_neg_one,
        heathBrownDirichletPhase, mtTypeIPrimeRaisedBlockAnchor]
      simp only [PNat.mk_coe]
      push_cast
      ring_nf
  · apply Finset.sum_subset
    · intro m hm
      rw [mtTypeIPrimeRaisedBlockSupportNat, Finset.mem_filter] at hm
      exact hm.1
    · intro m hmIoc hmSupport
      have hzero : mtTypeIPrimeRaisedCoeff P ell m = 0 := by
        by_contra hne
        apply hmSupport
        rw [mtTypeIPrimeRaisedBlockSupportNat, Finset.mem_filter]
        exact ⟨hmIoc, hne⟩
      have hanchored :
          anchoredCoeff ((2 * P) ^ ell)
            (convPow (2 * P) ell (mtTypeIPrimeCoeff P)) m = 0 := by
        simpa only [mtTypeIPrimeRaisedCoeff] using hzero
      rw [anchoredDirichletTerm, hanchored]
      simp

/-- Factorial-weighted support bound for every literal Watt block. -/
theorem factorial_mul_card_mtTypeIPrimeRaisedBlockSupportPNat_le
    (P ell B : ℕ) :
    ell.factorial * (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card ≤
      ((mtTypeIPrimeCoeffSupport P).card + ell) ^ ell := by
  exact (Nat.mul_le_mul_left ell.factorial
    (card_mtTypeIPrimeRaisedBlockSupportPNat_le P ell B)).trans
      (factorial_mul_card_mtTypeIPrimeRaisedSupport_le P ell)

/-- Brun--Titchmarsh envelope for factorial-weighted support of every literal block. -/
theorem factorial_mul_card_mtTypeIPrimeRaisedBlockSupportPNat_le_bt
    (P ell B : ℕ) {z : ℝ} (hz : 1 < z) :
    ((ell.factorial *
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℕ) : ℝ) ≤
      (2 * (P : ℝ) / Real.log z + 6 * z * (1 + Real.log z) ^ 3 + 1 + ell) ^ ell := by
  have hcard := card_mtTypeIPrimeRaisedBlockSupportPNat_le P ell B
  have hmul :
      ell.factorial * (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card ≤
        ell.factorial * (mtTypeIPrimeRaisedSupport P ell).card :=
    Nat.mul_le_mul_left ell.factorial hcard
  have hcast :
      ((ell.factorial *
          (mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℕ) : ℝ) ≤
        ((ell.factorial *
          (mtTypeIPrimeRaisedSupport P ell).card : ℕ) : ℝ) := by
    exact_mod_cast hmul
  exact hcast.trans
    (factorial_mul_card_mtTypeIPrimeRaisedSupport_le_bt P ell hz)

end

end RHTower.Sieve
