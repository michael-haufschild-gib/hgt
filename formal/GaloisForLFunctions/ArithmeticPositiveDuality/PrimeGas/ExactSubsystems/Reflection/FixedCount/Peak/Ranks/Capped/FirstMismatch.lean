import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Capped.Coordinates
import GaloisForLFunctions.Core

/-! # Exact depth of the first asymmetric excitation at intermediate capacity -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped

open Finset

variable (S : Finset Nat.Primes) (hs : S.card = 3)

private theorem ordered_e : StrictMono (e S hs) := by
  intro i j h
  exact energy_inc (S := S) (i := i.val) (j := j.val) (hi := by omega) (hj := by omega) h

theorem lowerGap_pos : 0 < lowerGap S hs :=
  sub_pos.mpr (ordered_e S hs (show (0:Fin 3) < 1 by omega))

theorem upperGap_pos : 0 < upperGap S hs :=
  sub_pos.mpr (ordered_e S hs (show (1:Fin 3) < 2 by omega))

/-- Distinct transfer counts have distinct energies by integral independence of prime logarithms. -/
theorem height_injective : Function.Injective (height (lowerGap S hs) (upperGap S hs)) := by
  intro v w he
  let A : ℤ := (v.1 : ℤ)-w.1
  let B : ℤ := (v.2 : ℤ)-w.2
  let c : Fin 3 → ℤ := ![-A,A-B,B]
  have li : LinearIndependent ℤ (e S hs) := logPrime_linearIndependent_int.comp
    (fun i : Fin 3 => (species S hs i).val) (Subtype.val_injective.comp (species S hs).injective)
  have hz : ∑ i, c i • e S hs i = 0 := by
    simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,zsmul_eq_mul]
    change ((-A : ℤ) : ℝ)*e S hs 0 + (((A-B : ℤ) : ℝ)*e S hs 1 + (B : ℝ)*e S hs 2) = 0
    dsimp only [A,B]
    push_cast
    unfold height lowerGap upperGap at he
    linarith only [he]
  have h := Fintype.linearIndependent_iff.mp li c hz
  have hx : -A = 0 := h 0
  have hy : B = 0 := h 2
  apply Prod.ext <;> dsimp only [A,B] at hx hy <;> omega

private theorem band_minimum {k l : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : IsLeast (band k l a b) 0 := by
  constructor
  · exact ⟨(0,0),by simp [Allowed],by simp [height]⟩
  · rintro z ⟨v,_,rfl⟩
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) ha.le) (mul_nonneg (Nat.cast_nonneg _) hb.le)

theorem extrema (k l : ℕ) :
    IsLeast (Set.range (fun x : Sector S k l => energy (level x))) (lowerEnergy S hs k l) ∧
    IsGreatest (Set.range (fun x : Sector S k l => energy (level x))) (upperEnergy S hs k l) := by
  have lo : IsLeast (lowerSpectrum S hs k l) 0 := by
    rw [lowerSpectrum_eq]; exact band_minimum (lowerGap_pos S hs) (upperGap_pos S hs)
  have hi : IsLeast (upperSpectrum S hs k l) 0 := by
    rw [upperSpectrum_eq]; exact band_minimum (lowerGap_pos S hs) (upperGap_pos S hs)
  obtain ⟨x,hx⟩ := lo.1
  obtain ⟨y,hy⟩ := hi.1
  refine ⟨⟨⟨x,sub_eq_zero.mp hx⟩,?_⟩,⟨⟨y,(sub_eq_zero.mp hy).symm⟩,?_⟩⟩
  · rintro _ ⟨z,rfl⟩
    exact sub_nonneg.mp (lo.2 (Set.mem_range_self z))
  · rintro _ ⟨z,rfl⟩
    exact sub_nonneg.mp (hi.2 (Set.mem_range_self z))

/-- With unequal middle filling and vacancy the cheaper transfer first distinguishes the
opposite spectral edges after exactly one more than the smaller middle population. -/
theorem first_unpaired_energy (k l : ℕ) (h : k ≠ l) :
    IsLeast (mismatch (lowerSpectrum S hs k l) (upperSpectrum S hs k l))
      (threshold k l (lowerGap S hs) (upperGap S hs)) := by
  rw [lowerSpectrum_eq,upperSpectrum_eq]
  exact first_mismatch h (lowerGap_pos S hs) (upperGap_pos S hs) (height_injective S hs)

theorem edge_spectra_equal_iff (k l : ℕ) :
    lowerSpectrum S hs k l = upperSpectrum S hs k l ↔ k = l := by
  constructor
  · intro he
    by_contra h
    have hw := (first_unpaired_energy S hs k l h).1
    simp only [he,mismatch,Set.sdiff_self,Set.union_self,Set.mem_empty_iff_false] at hw
  · rintro rfl
    rw [lowerSpectrum_eq,upperSpectrum_eq]

/-- An explicit increasing ladder of shared energies below the first mismatch. -/
theorem common_ladder (k l : ℕ) :
    ∃ f : Fin (min k l+1) → ℝ, StrictMono f ∧ ∀ i,
      f i ∈ lowerSpectrum S hs k l ∩ upperSpectrum S hs k l ∧
      f i < threshold k l (lowerGap S hs) (upperGap S hs) := by
  let a := lowerGap S hs
  let b := upperGap S hs
  have hm : 0 < min a b := lt_min (lowerGap_pos S hs) (upperGap_pos S hs)
  refine ⟨fun i => (i.val : ℝ)*min a b,fun i j hij => mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij) hm,?_⟩
  intro i
  have ht : (i.val : ℝ)*min a b < threshold k l a b :=
    mul_lt_mul_of_pos_right (Nat.cast_lt.mpr i.isLt) hm
  have hk := min_le_left k l
  have hl := min_le_right k l
  have mem : (i.val : ℝ)*min a b ∈ band k l a b := by
    rcases le_total a b with h | h
    · refine ⟨(i.val,0),by unfold Allowed; dsimp; omega,?_⟩
      simp only [height,Nat.cast_zero,zero_mul,add_zero,min_eq_left h]
    · refine ⟨(0,i.val),by unfold Allowed; dsimp; omega,?_⟩
      simp only [height,Nat.cast_zero,zero_mul,zero_add,min_eq_right h]
  rw [lowerSpectrum_eq,upperSpectrum_eq]
  exact ⟨⟨mem,(band_agrees_below k l (lowerGap_pos S hs) (upperGap_pos S hs) ht).mp mem⟩,ht⟩

#print axioms height_injective
#print axioms extrema
#print axioms first_unpaired_energy
#print axioms edge_spectra_equal_iff
#print axioms common_ladder

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped
