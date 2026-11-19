import GaloisForLFunctions.RHTower.ChenGuptaLiHybridCharacterMeanSquare
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture
import GaloisForLFunctions.RHTower.Sieve.ResiduePartitionCount

/-!
# Uniform survivors of sparse divisor restrictions

A shared vanishing reciprocal tail permits a fixed small-prime progression,
followed by a second cutoff after the progression modulus is fixed. The
remaining integers avoid every forbidden divisor throughout each large
sharp octave, uniformly over the actual list of restrictions.
-/

noncomputable section

open Finset Filter
open scoped Classical

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

def reciprocalTail (B : Finset ℕ) (Y : ℕ) : ℝ :=
  ∑ b ∈ B.filter (Y < ·), 1/(b:ℝ)

private def progression (Q X : ℕ) := (Ioc X (2*X)).filter (fun n => n%Q=1)

private theorem progression_lower {Q : ℕ} (hq : 1<Q) (X : ℕ) :
    (X:ℝ)/Q-2 ≤ (progression Q X).card := by
  let A := fun U => (Icc 1 U).filter (fun n => n%Q=1)
  have hsub : A (2*X) ⊆ A X ∪ progression Q X := by
    intro n hn
    obtain ⟨hi,he⟩ := mem_filter.mp hn
    obtain ⟨h1,h2⟩ := mem_Icc.mp hi
    by_cases h : n ≤ X
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨h1,h⟩,he⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.lt_of_not_ge h,h2⟩,he⟩)
  have hc := (Nat.cast_le (α := ℝ)).mpr ((card_le_card hsub).trans (card_union_le ..))
  rw [Nat.cast_add] at hc
  have hl := RHTower.Sieve.card_residue_class_ge (zero_lt_one.trans hq) (2*X) hq
  have hu := RHTower.Sieve.card_residue_class_le (zero_lt_one.trans hq) X 1
  change _ ≤ ((A (2*X)).card:ℝ) at hl
  change ((A X).card:ℝ) ≤ _ at hu
  push_cast at hl
  rw [mul_div_assoc] at hl
  linarith only [hc,hl,hu]

private theorem congruent_one {Q X n : ℕ} (hq : 1<Q) (hn : n ∈ progression Q X) :
    n ≡ 1 [MOD Q] := by
  change n%Q=1%Q
  rw [Nat.mod_eq_of_lt hq]
  exact (mem_filter.mp hn).2

private theorem middle_hits {Q b : ℕ} (hq : 1<Q) (hb : 0 < b) (X : ℕ) :
    (((progression Q X).filter (b ∣ ·)).card:ℝ) ≤ (X:ℝ)/(Q*b:ℕ)+1 := by
  let H := (progression Q X).filter (b ∣ ·)
  by_cases he : H.Nonempty
  · obtain ⟨a,ha⟩ := he
    obtain ⟨hga,hba⟩ := mem_filter.mp ha
    have hcA := (congruent_one hq hga).gcd_eq
    rw [Nat.one_gcd] at hcA
    have hcop := (Nat.Coprime.coprime_dvd_left hba (show a.Coprime Q from hcA)).symm
    have hsub : H ⊆ (Ioc X (2*X)).filter (fun n => n%(Q*b)=a%(Q*b)) := by
      intro n hn
      obtain ⟨hg,hd⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨(mem_filter.mp hg).1,(Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨?_,?_⟩⟩
      · exact (congruent_one hq hg).trans (congruent_one hq hga).symm
      · change n%b=a%b
        rw [Nat.mod_eq_zero_of_dvd hd,Nat.mod_eq_zero_of_dvd hba]
    have h := (Nat.cast_le.mpr (card_le_card hsub) : (H.card:ℝ) ≤ _).trans
      (RHTower.Sieve.card_residue_Ioc_le (Nat.mul_pos (zero_lt_one.trans hq) hb) X (2*X) (a%(Q*b)))
    simpa only [show 2*X-X=X by omega] using h
  · change (H.card:ℝ) ≤ _
    rw [not_nonempty_iff_eq_empty.mp he,card_empty,Nat.cast_zero]
    positivity

private theorem far_hits {b : ℕ} (hb : 0 < b) (Q X : ℕ) :
    (((progression Q X).filter (b ∣ ·)).card:ℝ) ≤ 2*(X:ℝ)/b := by
  have hsub : (progression Q X).filter (b ∣ ·) ⊆ (Icc 1 (2*X)).filter (b ∣ ·) := by
    intro n hn
    obtain ⟨hg,hd⟩ := mem_filter.mp hn
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hg).1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hu⟩,hd⟩
  have he := RHTower.sum_Icc_dvd_reindex b (2*X) hb (fun _ => (1:ℕ))
  simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,Nat.add_sub_cancel] at he
  have hc := (card_le_card hsub).trans_eq he
  apply (Nat.cast_le.mpr hc).trans
  exact (le_div_iff₀ (Nat.cast_pos.mpr hb)).2 (by exact_mod_cast Nat.div_mul_le_self (2*X) b)

/-- Uniform absolute density for the integers outside all forbidden
multiples, whenever the whole family has uniformly vanishing reciprocal
tails. Both cutoffs are independent of the list eventually used. -/
theorem uniform_density_outside_sparse_divisors (family : Set (Finset ℕ))
    (hmin : ∀ B ∈ family, ∀ b ∈ B, 1 < b)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ Y : ℕ, ∀ B ∈ family, reciprocalTail B Y ≤ ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop, ∀ B ∈ family,
      δ*X ≤ (((Ioc X (2*X)).filter (fun n => ∀ b ∈ B, ¬b ∣ n)).card:ℝ) := by
  obtain ⟨Y,hY⟩ := htail (1/8) (by norm_num)
  let Q := (Y+2).factorial
  have hfac : 2 ∣ Q := Nat.dvd_factorial (by decide) (by omega : 2 ≤ Y+2)
  have hQ : 1<Q := Nat.le_of_dvd (Nat.factorial_pos _) hfac
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr (zero_lt_one.trans hQ)
  obtain ⟨T,hT⟩ := htail (1/(16*(Q:ℝ))) (by positivity)
  refine ⟨1/(4*(Q:ℝ)),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (8*Q*(T+3))] with X hX
  intro B hB
  let G := progression Q X
  let S := B.filter (fun b => Y < b ∧ b ≤ T)
  let R := B.filter (T < ·)
  let H := fun b : ℕ => G.filter (b ∣ ·)
  let free := (Ioc X (2*X)).filter (fun n => ∀ b ∈ B, ¬b ∣ n)
  have hsub : G ⊆ free ∪ (S.biUnion H ∪ R.biUnion H) := by
    intro n hn
    by_cases hh : ∀ b ∈ B, ¬b ∣ n
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hn).1,hh⟩)
    push_neg at hh
    obtain ⟨b,hb,hd⟩ := hh
    have hnot : Y < b := by
      by_contra! h
      have hdQ : b ∣ Q := Nat.dvd_factorial (zero_lt_one.trans (hmin _ hB _ hb)) (by omega)
      have h := Nat.ModEq.of_dvd hdQ (congruent_one hQ hn)
      have hb1 := (h.dvd_iff (dvd_refl b)).mp hd
      exact (hmin _ hB _ hb).ne' (Nat.eq_one_of_dvd_one hb1)
    apply mem_union_right
    by_cases ht : b ≤ T
    · exact mem_union_left _ (mem_biUnion.mpr ⟨b,mem_filter.mpr ⟨hb,hnot,ht⟩,mem_filter.mpr ⟨hn,hd⟩⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨b,mem_filter.mpr ⟨hb,Nat.lt_of_not_ge ht⟩,mem_filter.mpr ⟨hn,hd⟩⟩)
  have hcost := (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_left
    ((card_union_le ..).trans (add_le_add (card_biUnion_le ..) (card_biUnion_le ..))) _))
  have hc := (Nat.cast_le (α := ℝ)).mpr hcost
  push_cast only [Nat.cast_add,Nat.cast_sum] at hc
  have hScard : S.card ≤ T := by
    have sub : S ⊆ Icc 1 T := fun _ hb => mem_Icc.mpr ⟨(hmin _ hB _ (mem_filter.mp hb).1).le,
      (mem_filter.mp hb).2.2⟩
    simpa using card_le_card sub
  have hScost : ∑ b ∈ S,((H b).card:ℝ) ≤ (X:ℝ)/Q*(1/8)+T := by
    calc _ ≤ ∑ b ∈ S, ((X:ℝ)/Q*(1/b)+1) := by
             apply sum_le_sum
             intro b hb
             have h := middle_hits (b := b) hQ (zero_lt_one.trans (hmin _ hB _ (mem_filter.mp hb).1)) X
             push_cast at h
             exact h.trans_eq (by ring)
         _ = (X:ℝ)/Q*(∑ b ∈ S,1/(b:ℝ))+S.card := by rw [sum_add_distrib,←mul_sum]; simp
         _ ≤ _ := by
             apply add_le_add _ (Nat.cast_le.mpr hScard)
             apply mul_le_mul_of_nonneg_left _ (by positivity)
             apply le_trans _ (hY _ hB)
             exact sum_le_sum_of_subset_of_nonneg
               (fun b hb => mem_filter.mpr ⟨(mem_filter.mp hb).1,(mem_filter.mp hb).2.1⟩) (fun _ _ _ => by positivity)
  have hRcost : ∑ b ∈ R, ((H b).card:ℝ) ≤ 2*(X:ℝ)*(1/(16*(Q:ℝ))) := by
    calc _ ≤ ∑ b ∈ R, 2*(X:ℝ)*(1/b) := by
              apply sum_le_sum
              intro b hb
              simpa only [mul_one_div] using far_hits (zero_lt_one.trans (hmin _ hB _ (mem_filter.mp hb).1)) Q X
         _ = 2*(X:ℝ)*reciprocalTail B T := (mul_sum ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (hT _ hB) (by positivity)
  have hscale : 8*((T:ℝ)+3) ≤ (X:ℝ)/Q := (le_div_iff₀ hQr).2 (by
    have hh : (8:ℝ)*Q*(T+3) ≤ X := by exact_mod_cast hX
    linarith only [hh])
  have hg := progression_lower hQ X
  change (X:ℝ)/Q-2 ≤ (G.card:ℝ) at hg
  change 1/(4*(Q:ℝ))*X ≤ (free.card:ℝ)
  have hfar : 2*(X:ℝ)*(1/(16*(Q:ℝ)))=(X:ℝ)/Q/8 := by ring
  rw [hfar] at hRcost
  rw [show 1/(4*(Q:ℝ))*X=(X:ℝ)/Q/4 by ring]
  linarith only [hc,hg,hScost,hRcost,hscale]

#print axioms uniform_density_outside_sparse_divisors

end GaloisForLFunctions.RestrictedFactorizationCalculus
