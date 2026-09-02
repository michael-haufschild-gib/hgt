import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierIntegralEnergy
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBounded

/-!
# Layer cake for the powered Matomäki--Teräväinen prime amplifier

Every coefficient of the powered prime amplifier is a nonnegative integer: the cardinality of an
ordered prime-product fibre.  This module decomposes a literal Watt block into unit-coefficient
threshold layers.  Unlike factorial normalization, the decomposition retains the exact first
coefficient mass and therefore preserves the powered block denominator in later moment estimates.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Natural multiplicity of a supported coefficient in one literal Watt block. -/
def mtTypeIPrimeRaisedBlockMultiplicity (P ell B : ℕ) (m : PNat) : ℕ :=
  if hm : (m : ℕ) ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B then
    (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P)
      (mtTypeIPrimeRaisedBlockSupportIndex P ell B ⟨(m : ℕ), hm⟩)).card
  else 0

/-- On block support, the complex coefficient is the cast of its natural multiplicity. -/
theorem mtTypeIPrimeRaisedCoeff_eq_blockMultiplicity
    {P ell B : ℕ} {m : PNat}
    (hm : m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B) :
    mtTypeIPrimeRaisedCoeff P ell (m : ℕ) =
      (mtTypeIPrimeRaisedBlockMultiplicity P ell B m : ℂ) := by
  have hmNat : (m : ℕ) ∈ mtTypeIPrimeRaisedBlockSupportNat P ell B :=
    mem_mtTypeIPrimeRaisedBlockSupportPNat.mp hm
  let m' : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B) := ⟨(m : ℕ), hmNat⟩
  let j : Fin ((2 * P) ^ ell) := mtTypeIPrimeRaisedBlockSupportIndex P ell B m'
  have hj := mtTypeIPrimeRaisedBlockSupportIndex_spec P ell B m'
  have hjm : (j : ℕ) + 1 = (m : ℕ) := by
    simpa only [j, m'] using hj.2
  rw [mtTypeIPrimeRaisedBlockMultiplicity, dif_pos hmNat]
  change mtTypeIPrimeRaisedCoeff P ell (m : ℕ) =
    ((powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card : ℂ)
  rw [mtTypeIPrimeRaisedCoeff, ← hjm, anchoredCoeff_add_one]
  exact convPow_mtTypeIPrimeCoeff_eq_powFibreOn_card P ell j

/-- Every block multiplicity is at most the sharp factorial fibre bound. -/
theorem mtTypeIPrimeRaisedBlockMultiplicity_le_factorial
    (P ell B : ℕ) (m : PNat) :
    mtTypeIPrimeRaisedBlockMultiplicity P ell B m ≤ ell.factorial := by
  by_cases hm : m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B
  · have hcoeff := norm_mtTypeIPrimeRaisedCoeff_le_factorial P ell (m : ℕ)
    rw [mtTypeIPrimeRaisedCoeff_eq_blockMultiplicity hm] at hcoeff
    have hreal : (mtTypeIPrimeRaisedBlockMultiplicity P ell B m : ℝ) ≤
        (ell.factorial : ℝ) := by simpa using hcoeff
    exact_mod_cast hreal
  · have hmNat : (m : ℕ) ∉ mtTypeIPrimeRaisedBlockSupportNat P ell B := by
      simpa only [mem_mtTypeIPrimeRaisedBlockSupportPNat] using hm
    rw [mtTypeIPrimeRaisedBlockMultiplicity, dif_neg hmNat]
    exact Nat.zero_le _

/-- The `j`th unit-coefficient threshold layer of one powered-prime Watt block. -/
def mtTypeIPrimeRaisedBlockLayer (P ell B j : ℕ) : Finset PNat :=
  (mtTypeIPrimeRaisedBlockSupportPNat P ell B).filter fun m =>
    j < mtTypeIPrimeRaisedBlockMultiplicity P ell B m

theorem mtTypeIPrimeRaisedBlockLayer_subset (P ell B j : ℕ) :
    mtTypeIPrimeRaisedBlockLayer P ell B j ⊆
      mtTypeIPrimeRaisedBlockSupportPNat P ell B :=
  Finset.filter_subset _ _

theorem mtTypeIPrimeRaisedBlockLayer_upper
    {P ell B j : ℕ} {m : PNat}
    (hm : m ∈ mtTypeIPrimeRaisedBlockLayer P ell B j) :
    (m : ℕ) ≤ 2 * B :=
  mtTypeIPrimeRaisedBlockSupportPNat_upper
    (mtTypeIPrimeRaisedBlockLayer_subset P ell B j hm)

private theorem sum_range_indicator_mul
    {R : Type*} [CommSemiring R] (L b : ℕ) (hb : b ≤ L) (x : R) :
    ∑ j ∈ Finset.range L, (if j < b then x else 0) = (b : R) * x := by
  have hfilter : (Finset.range L).filter (fun j => j < b) = Finset.range b := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter (s := Finset.range L) (fun j => j < b) (fun _ => x)]
  rw [hfilter]
  simp

/-- Generic finite threshold-layer identity. -/
private theorem sum_layers_eq_sum_multiplicity_mul
    {α R : Type*} [DecidableEq α] [CommSemiring R]
    (A : Finset α) (b : α → ℕ) (L : ℕ)
    (hb : ∀ m ∈ A, b m ≤ L) (f : α → R) :
    ∑ j ∈ Finset.range L, ∑ m ∈ A.filter (fun m => j < b m), f m =
      ∑ m ∈ A, (b m : R) * f m := by
  classical
  calc
    ∑ j ∈ Finset.range L, ∑ m ∈ A.filter (fun m => j < b m), f m =
        ∑ j ∈ Finset.range L, ∑ m ∈ A, (if j < b m then f m else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_filter (s := A) (fun m => j < b m) f
    _ = ∑ m ∈ A, ∑ j ∈ Finset.range L, (if j < b m then f m else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ A, (b m : R) * f m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sum_range_indicator_mul L (b m) (hb m hm) (f m)

/-- Exact layer decomposition of the powered-prime sparse factor. -/
theorem sum_heathBrownSparseFactor_blockLayer_eq
    (P ell B : ℕ) (t : ℝ) :
    ∑ j ∈ Finset.range ell.factorial,
        heathBrownSparseFactor (mtTypeIPrimeRaisedBlockLayer P ell B j)
          (fun _ => (1 : Circle)) t =
      heathBrownBoundedSparseFactor
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
        (mtTypeIPrimeRaisedCoeff P ell) t := by
  rw [heathBrownBoundedSparseFactor]
  simp only [heathBrownSparseFactor, Circle.coe_one, one_mul,
    mtTypeIPrimeRaisedBlockLayer]
  rw [sum_layers_eq_sum_multiplicity_mul
    (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
    (mtTypeIPrimeRaisedBlockMultiplicity P ell B) ell.factorial
    (fun m _hm => mtTypeIPrimeRaisedBlockMultiplicity_le_factorial P ell B m)
    (fun m => heathBrownDirichletPhase m t)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mtTypeIPrimeRaisedCoeff_eq_blockMultiplicity hm]

/-- Exact layer decomposition after retaining the reciprocal one-line weight. -/
theorem sum_heathBrownSparseOneLineFactor_blockLayer_eq
    (P ell B : ℕ) (t : ℝ) :
    ∑ j ∈ Finset.range ell.factorial,
        heathBrownSparseOneLineFactor (mtTypeIPrimeRaisedBlockLayer P ell B j)
          (fun _ => (1 : ℂ)) t =
      heathBrownSparseOneLineFactor
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
        (mtTypeIPrimeRaisedCoeff P ell) t := by
  simp only [heathBrownSparseOneLineFactor, one_mul,
    mtTypeIPrimeRaisedBlockLayer]
  rw [sum_layers_eq_sum_multiplicity_mul
    (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
    (mtTypeIPrimeRaisedBlockMultiplicity P ell B) ell.factorial
    (fun m _hm => mtTypeIPrimeRaisedBlockMultiplicity_le_factorial P ell B m)
    (fun m => ((((1 / ((m : ℕ) : ℝ)) : ℝ)) : ℂ) *
      heathBrownDirichletPhase m t)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mtTypeIPrimeRaisedCoeff_eq_blockMultiplicity hm]
  ring

/-- The unnormalized one-line sparse factor is the literal Watt coefficient block. -/
theorem heathBrownSparseOneLineFactor_mtTypeIPrimeRaised_unnormalized_eq
    (P ell B : ℕ) (t : ℝ) :
    heathBrownSparseOneLineFactor
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
        (mtTypeIPrimeRaisedCoeff P ell) t =
      mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t := by
  have hscale :
      heathBrownSparseOneLineFactor
          (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
          (mtTypeIPrimeRaisedNormalizedCoeff P ell) t =
        ((ell.factorial : ℂ)⁻¹) *
          heathBrownSparseOneLineFactor
            (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
            (mtTypeIPrimeRaisedCoeff P ell) t := by
    rw [heathBrownSparseOneLineFactor, heathBrownSparseOneLineFactor,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [mtTypeIPrimeRaisedNormalizedCoeff]
    ring
  have hnormalized :=
    heathBrownSparseOneLineFactor_mtTypeIPrimeRaised_eq P ell B t
  rw [hscale] at hnormalized
  have hfac : (ell.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ell
  exact mul_left_cancel₀ (inv_ne_zero hfac) hnormalized

/-- Total cardinality of all threshold layers is the block's exact coefficient mass. -/
theorem sum_card_mtTypeIPrimeRaisedBlockLayer_eq
    (P ell B : ℕ) :
    ∑ j ∈ Finset.range ell.factorial,
        (mtTypeIPrimeRaisedBlockLayer P ell B j).card =
      ∑ m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B,
        mtTypeIPrimeRaisedBlockMultiplicity P ell B m := by
  simpa [mtTypeIPrimeRaisedBlockLayer] using
    (sum_layers_eq_sum_multiplicity_mul
      (R := ℕ) (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
      (mtTypeIPrimeRaisedBlockMultiplicity P ell B) ell.factorial
      (fun m _hm => mtTypeIPrimeRaisedBlockMultiplicity_le_factorial P ell B m)
      (fun _ => 1))

/-- The chosen complete-vector indices of a block are distinct. -/
def mtTypeIPrimeRaisedBlockIndexEmbeddingFin (P ell B : ℕ) :
    ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B) ↪ Fin ((2 * P) ^ ell) :=
  { toFun := mtTypeIPrimeRaisedBlockSupportIndex P ell B
    inj' := by
      intro m n hmn
      apply Subtype.ext
      have hval := congrArg (fun j : Fin ((2 * P) ^ ell) => (j : ℕ) + 1) hmn
      rw [(mtTypeIPrimeRaisedBlockSupportIndex_spec P ell B m).2,
        (mtTypeIPrimeRaisedBlockSupportIndex_spec P ell B n).2] at hval
      exact hval }

/-- Support-filtered product fibres partition all supported ordered tuples. -/
private theorem sum_card_powFibreOn_eq_card_pow
    (N ell : ℕ) (S : Finset (Fin N)) :
    ∑ j : Fin (N ^ ell), (powFibreOn N ell S j).card = S.card ^ ell := by
  classical
  let sSet : Finset (Fin ell → Fin N) :=
    (Finset.univ : Finset (Fin ell → Fin N)).filter fun p =>
      ∀ i : Fin ell, p i ∈ S
  have hfibre : ∀ j : Fin (N ^ ell),
      powFibreOn N ell S j = sSet.filter (fun p => powIdx p = j) := by
    intro j
    simp only [powFibreOn, sSet]
    exact Finset.filter_comm _ _ _
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := sSet) (t := (Finset.univ : Finset (Fin (N ^ ell))))
    (g := fun p => powIdx p) (f := fun _p => (1 : ℕ))
    (fun p _ => Finset.mem_univ _)
  have hsum : ∑ j : Fin (N ^ ell), (powFibreOn N ell S j).card = sSet.card := by
    simp_rw [hfibre]
    simpa using hpartition
  let e : (Fin ell → ↑S) ↪ (Fin ell → Fin N) :=
    { toFun := fun p i => (p i : Fin N)
      inj' := by
        intro p q hpq
        funext i
        apply Subtype.ext
        exact congrFun hpq i }
  have hmap : (Finset.univ : Finset (Fin ell → ↑S)).map e = sSet := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_map] at hp
      obtain ⟨q, _hq, rfl⟩ := hp
      simp only [sSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun i => (q i).property⟩
    · intro hp
      simp only [sSet, Finset.mem_filter] at hp
      let q : Fin ell → ↑S := fun i => ⟨p i, hp.2 i⟩
      rw [Finset.mem_map]
      refine ⟨q, Finset.mem_univ _, ?_⟩
      funext i
      rfl
  have hcard : sSet.card = S.card ^ ell := by
    rw [← hmap, Finset.card_map, Finset.card_univ]
    simp
  exact hsum.trans hcard

/-- Exact coefficient mass of a block is at most the complete ordered-prime tuple mass. -/
theorem sum_mtTypeIPrimeRaisedBlockMultiplicity_le_card_pow
    (P ell B : ℕ) :
    ∑ m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B,
        mtTypeIPrimeRaisedBlockMultiplicity P ell B m ≤
      (mtTypeIPrimeCoeffSupport P).card ^ ell := by
  classical
  let e := mtTypeIPrimeRaisedBlockIndexEmbeddingFin P ell B
  let image : Finset (Fin ((2 * P) ^ ell)) :=
    (mtTypeIPrimeRaisedBlockSupportNat P ell B).attach.map e
  have hsupportSum :
      ∑ m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B,
          mtTypeIPrimeRaisedBlockMultiplicity P ell B m =
        ∑ m : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B),
          (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P)
            (mtTypeIPrimeRaisedBlockSupportIndex P ell B m)).card := by
    refine Finset.sum_bij
      (fun m hm =>
        (⟨(m : ℕ), mem_mtTypeIPrimeRaisedBlockSupportPNat.mp hm⟩ :
          ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B))) ?_ ?_ ?_ ?_
    · intro m hm
      exact Finset.mem_univ _
    · intro m₁ hm₁ m₂ hm₂ heq
      apply Subtype.ext
      exact congrArg
        (fun x : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B) => (x : ℕ)) heq
    · intro m hm
      let p : PNat := ⟨m, (mtTypeIPrimeRaisedBlockAnchor P ell B m).property⟩
      refine ⟨p, ?_, ?_⟩
      · exact mem_mtTypeIPrimeRaisedBlockSupportPNat.mpr m.property
      · apply Subtype.ext
        rfl
    · intro m hm
      rw [mtTypeIPrimeRaisedBlockMultiplicity,
        dif_pos (mem_mtTypeIPrimeRaisedBlockSupportPNat.mp hm)]
  have himage :
      (∑ m : ↑(mtTypeIPrimeRaisedBlockSupportNat P ell B),
          (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P)
            (mtTypeIPrimeRaisedBlockSupportIndex P ell B m)).card) =
        ∑ j ∈ image,
          (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card := by
    simp only [image]
    rw [Finset.sum_map, Finset.attach_eq_univ]
    rfl
  have hsubset : image ⊆ (Finset.univ : Finset (Fin ((2 * P) ^ ell))) :=
    fun j hj => Finset.mem_univ j
  calc
    ∑ m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B,
        mtTypeIPrimeRaisedBlockMultiplicity P ell B m =
      ∑ j ∈ image,
        (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card :=
      hsupportSum.trans himage
    _ ≤ ∑ j : Fin ((2 * P) ^ ell),
        (powFibreOn (2 * P) ell (mtTypeIPrimeCoeffSupport P) j).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
    _ = (mtTypeIPrimeCoeffSupport P).card ^ ell :=
      sum_card_powFibreOn_eq_card_pow (2 * P) ell (mtTypeIPrimeCoeffSupport P)

/-- Total layer mass is at most the paper's raised prime length `P^ell`. -/
theorem sum_card_mtTypeIPrimeRaisedBlockLayer_le
    (P ell B : ℕ) :
    ∑ j ∈ Finset.range ell.factorial,
        (mtTypeIPrimeRaisedBlockLayer P ell B j).card ≤ P ^ ell := by
  rw [sum_card_mtTypeIPrimeRaisedBlockLayer_eq]
  exact (sum_mtTypeIPrimeRaisedBlockMultiplicity_le_card_pow P ell B).trans
    (Nat.pow_le_pow_left (card_mtTypeIPrimeCoeffSupport_le P) ell)

end

end RHTower.Sieve
