import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Finset.Max

/-!
# The sharp harmonic price of a finite weak first moment

The weak trace estimate underlying Ponge and Tian's spectral counting
(arXiv:2605.25591) has a finite version with exact constant H_n.
One observed level captures at least 1/H_n of the full mass. Keeping
ties in the superlevel count avoids choosing an ordering of equal values.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.FiniteWeakMoment

/-- Weak first moment at one observed height. -/
def levelMass {α : Type*} (s : Finset α) (f : α → ℝ) (i : α) : ℝ :=
  f i * ((s.filter fun j => f i ≤ f j).card : ℝ)

/-- Removing a minimum pays exactly the last harmonic term in the
weak-to-strong first-moment inequality. -/
theorem sum_le_harmonic {α : Type*} (s : Finset α) (f : α → ℝ) (B : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hw : ∀ i ∈ s, levelMass s f i ≤ B) :
    ∑ i ∈ s, f i ≤ (harmonic s.card : ℝ)*B := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    obtain he | hs := s.eq_empty_or_nonempty
    · simp [he]
    obtain ⟨i,hi,hmin⟩ := s.exists_min_image f hs
    let r := s.erase i
    have hrs : r ⊆ s := erase_subset _ _
    have hrest := ih r (erase_ssubset hi) (fun j hj => hf j (hrs hj)) (fun j hj => by
      have hsub : (r.filter fun k => f j ≤ f k) ⊆ s.filter fun k => f j ≤ f k :=
        fun k hk => mem_filter.mpr ⟨hrs (mem_filter.mp hk).1,(mem_filter.mp hk).2⟩
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub)) (hf j (hrs hj))).trans
        (hw j (hrs hj)))
    have hcard : r.card+1 = s.card := by
      dsimp only [r]; rw [card_erase_of_mem hi]; have := card_pos.mpr hs; omega
    have hminprice := hw i hi
    rw [levelMass,filter_eq_self.mpr hmin] at hminprice
    have hc : 0 < (s.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr hs)
    have hprice := (le_div_iff₀ hc).mpr hminprice
    rw [←sum_erase_add s f hi,←hcard,harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
    change (∑ j ∈ r, f j) + f i ≤ _
    rw [hcard]
    rw [div_eq_inv_mul] at hprice
    linarith only [hrest,hprice]

/-- At least one observed height attains the harmonic fraction of the mass.
The same level is always bounded above by the full mass. -/
theorem exists_capturing_level {α : Type*} {s : Finset α} (hs : s.Nonempty)
    (f : α → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∃ i ∈ s, (∑ j ∈ s, f j) ≤ (harmonic s.card : ℝ)*levelMass s f i ∧
      levelMass s f i ≤ ∑ j ∈ s, f j := by
  obtain ⟨i,hi,hmax⟩ := s.exists_max_image (levelMass s f) hs
  refine ⟨i,hi,sum_le_harmonic s f _ hf hmax,?_⟩
  let r := s.filter fun j => f i ≤ f j
  calc levelMass s f i = ∑ _ ∈ r, f i := by simp [levelMass,r,mul_comm]
       _ ≤ ∑ j ∈ r, f j := sum_le_sum (fun j hj => (mem_filter.mp hj).2)
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j hj _ => hf j hj)

/-- Reciprocal ranks attain the harmonic constant at every sample size. -/
theorem sharp_reciprocal_sample (n : ℕ) :
    (∑ i ∈ Icc 1 n, (i:ℝ)⁻¹) = (harmonic n : ℝ) ∧
      ∀ i ∈ Icc 1 n, levelMass (Icc 1 n) (fun j : ℕ => (j:ℝ)⁻¹) i = 1 := by
  constructor
  · rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    simp only [Rat.cast_inv,Rat.cast_natCast]
  · intro i hi
    have hi₀ : 0 < (i:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hi).1
    have hset : (Icc 1 n).filter (fun j : ℕ => (i:ℝ)⁻¹ ≤ (j:ℝ)⁻¹) = Icc 1 i := by
      ext j
      rw [mem_filter,mem_Icc,mem_Icc]
      constructor
      · rintro ⟨⟨hj,_⟩,hh⟩
        exact ⟨hj,Nat.cast_le.mp ((inv_le_inv₀ hi₀ (Nat.cast_pos.mpr hj)).mp hh)⟩
      · rintro ⟨hj,hji⟩
        exact ⟨⟨hj,hji.trans (mem_Icc.mp hi).2⟩,(inv_le_inv₀ hi₀ (Nat.cast_pos.mpr hj)).mpr
          (Nat.cast_le.mpr hji)⟩
    rw [levelMass,hset,Nat.card_Icc]
    simp [hi₀.ne']

#print axioms sum_le_harmonic
#print axioms exists_capturing_level
#print axioms sharp_reciprocal_sample

end GaloisForLFunctions.FiniteWeakMoment
