import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! # Counting the words that can survive a centered trace moment -/

open Finset
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
noncomputable section
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A word of length $2k$ with more than $k$ different letters contains
a singleton. Its sign average therefore vanishes. -/
theorem singleton_of_large_image {k : ℕ} (v : Fin (2*k) → J) (hl : k<(univ.image v).card) :
    ∃ i, (univ.filter fun j => v j=i).card=1 := by
  let S := univ.image v
  have hm : Set.MapsTo v (↑(univ : Finset (Fin (2*k)))) (↑S) := fun i _ => mem_image_of_mem v (mem_univ i)
  have ht := card_eq_sum_card_fiberwise hm
  by_contra! hn
  have hb : (∑ _i ∈ S, 2)≤∑ i ∈ S, (univ.filter fun j => v j=i).card := by
    apply sum_le_sum
    intro i hi
    obtain ⟨j,_,he⟩ := mem_image.mp hi
    have hp := card_pos.mpr (show (univ.filter fun j => v j=i).Nonempty from
      ⟨j,mem_filter.mpr ⟨mem_univ _,he⟩⟩)
    have hh := hn i
    omega
  have hsize : 2*S.card≤2*k := calc
    _ = ∑ _i ∈ S, (2:ℕ) := by simp [Nat.mul_comm]
    _ ≤ _ := hb
    _ = _ := ht.symm.trans (by simp)
  change k<S.card at hl
  omega

/-- Choose a set of $k$ letters and then a word in that alphabet.
The factorial in the binomial count saves a full factor of $k^k$
up to $4^k$. -/
theorem small_image_count (k : ℕ) (hk : k≤Fintype.card J) :
    ((univ : Finset (Fin (2*k) → J)).filter (fun v => (univ.image v).card≤k)).card ≤
      (4*Fintype.card J*k)^k := by
  classical
  let N := Fintype.card J
  let masks := (univ : Finset J).powersetCard k
  let words (T : Finset J) := univ.image (fun w : Fin (2*k) → T => fun j => (w j : J))
  have hsub : univ.filter (fun v : Fin (2*k) → J => (univ.image v).card≤k) ⊆ masks.biUnion words := by
    intro v hv
    obtain ⟨T,hT,_,hcard⟩ := exists_subsuperset_card_eq (subset_univ (univ.image v))
      (mem_filter.mp hv).2 (by simpa only [card_univ] using hk)
    let w (j : Fin (2*k)) : T := ⟨v j,hT (mem_image_of_mem _ (mem_univ j))⟩
    exact mem_biUnion.mpr ⟨T,mem_powersetCard.mpr ⟨subset_univ _,hcard⟩,
      mem_image.mpr ⟨w,mem_univ _,rfl⟩⟩
  have hb (T : Finset J) (h : T∈masks) : (words T).card≤k^(2*k) := by
    have hT := (mem_powersetCard.mp h).2
    exact card_image_le.trans (by simp [hT])
  have hc : (N.choose k)*k^(2*k)≤(4*N*k)^k := by
    have hp : k^k≤k.factorial*(2*k).choose k := by
      rw [←Nat.descFactorial_eq_factorial_mul_choose]
      exact (Nat.pow_le_pow_left (by omega : k≤2*k+1-k) k).trans ((2*k).pow_sub_le_descFactorial k)
    have hd : k.factorial*N.choose k≤N^k := by
      rw [←Nat.descFactorial_eq_factorial_mul_choose]; exact N.descFactorial_le_pow k
    have hm : (2*k).choose k≤4^k := by
      simpa only [pow_mul,show (2:ℕ)^2=4 by norm_num] using (2*k).choose_le_two_pow k
    calc
      _ = N.choose k*k^k*k^k := by rw [two_mul,pow_add]; ac_rfl
      _ ≤ N.choose k*(k.factorial*(2*k).choose k)*k^k := by gcongr
      _ = (k.factorial*N.choose k)*(2*k).choose k*k^k := by ac_rfl
      _ ≤ N^k*4^k*k^k := by gcongr
      _ = _ := by rw [mul_comm 4 N,mul_pow,mul_pow]
  apply (card_le_card hsub).trans
  apply (card_biUnion_le_card_mul masks words _ hb).trans
  simpa only [masks,card_powersetCard,card_univ,N] using hc

#print axioms small_image_count
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
