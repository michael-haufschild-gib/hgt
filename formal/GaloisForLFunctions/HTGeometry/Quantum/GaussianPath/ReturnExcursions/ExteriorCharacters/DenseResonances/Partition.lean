import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.Hamming
import Mathlib.Algebra.Order.Chebyshev

/-! # Large-support collisions in any partition of the subset sums -/

open Finset
open scoped symmDiff
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Ordered pairs with a large support and satisfying a prescribed
symmetric frequency test. Each retained pair is counted with unit weight. -/
def pairCount (F : Finset (Finset I)) (r : ℕ) (p : Finset I → Finset I → Prop)
    [DecidableRel p] : ℕ :=
  ∑ S ∈ F, (F.filter fun T => r<(S ∆ T).card ∧ p S T).card

/-- Bins containing the energy sums force close pairs even after all
small-support differences have been removed. -/
theorem partition_floor {J : Type*} [Fintype J] [DecidableEq J] (F : Finset (Finset I))
    (r : ℕ) (b : Finset I → J) (p : Finset I → Finset I → Prop) [DecidableRel p]
    (hp : ∀ S∈F, ∀ T∈F, b S=b T → p S T) :
    (F.card:ℝ)^2 ≤ (Fintype.card J:ℝ)*((pairCount F r p:ℝ)+F.card*(2^r*(3/2)^Fintype.card I)) := by
  classical
  let U (j : J) := F.filter fun S => b S=j
  let A : ℝ := 2^r*(3/2)^Fintype.card I
  let L (S : Finset I) := (F.filter fun T => r<(S ∆ T).card ∧ p S T).card
  have hmap : (F : Set (Finset I)).MapsTo b (univ : Finset J) := fun _ _ => mem_univ _
  have hsum : (∑ j, ((U j).card:ℝ))=(F.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_fiberwise hmap).symm
  have hrow (j : J) (S : Finset I) (hS : S∈U j) : ((U j).card:ℝ)≤(L S:ℝ)+A := by
    let near := (U j).filter fun T => (S ∆ T).card≤r
    let far := (U j).filter fun T => ¬(S ∆ T).card≤r
    have hnear : (near.card:ℝ)≤A := small_support_count (U j) S r
    have hfar : far.card≤L S := by
      apply card_le_card
      intro T hT
      obtain ⟨hT,hd⟩ := mem_filter.mp hT
      obtain ⟨hTF,heT⟩ := mem_filter.mp hT
      obtain ⟨hSF,heS⟩ := mem_filter.mp hS
      exact mem_filter.mpr ⟨hTF,lt_of_not_ge hd,hp S hSF T hTF (heS.trans heT.symm)⟩
    have ht : near.card+far.card=(U j).card := card_filter_add_card_filter_not ..
    have hfar' : (far.card:ℝ)≤(L S:ℝ) := by exact_mod_cast hfar
    linarith only [show (near.card:ℝ)+far.card=(U j).card by exact_mod_cast ht,hnear,hfar']
  have hbin (j : J) : ((U j).card:ℝ)^2 ≤ ∑ S ∈ U j, ((L S:ℝ)+A) := by
    simpa only [sum_const,nsmul_eq_mul,←sq] using sum_le_sum (fun S hS => hrow j S hS)
  have htot := sum_le_sum (fun j (_ : j∈(univ:Finset J)) => hbin j)
  dsimp only [U] at htot
  rw [sum_fiberwise_of_maps_to hmap (fun S => (L S:ℝ)+A),sum_add_distrib,sum_const,nsmul_eq_mul] at htot
  have hh := sq_sum_le_card_mul_sum_sq (s:=univ) (f:=fun j => ((U j).card:ℝ))
  rw [card_univ,hsum] at hh
  apply hh.trans (mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _))
  simpa only [pairCount,L,Nat.cast_sum,A] using htot

#print axioms partition_floor
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
