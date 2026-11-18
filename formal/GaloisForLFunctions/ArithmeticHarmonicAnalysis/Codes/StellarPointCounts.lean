import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementPolynomial
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Point counts under stellar subdivision

Splitting faces by their intersection with the subdivided simplex gives the change
in the homogeneous face enumerator and in both support point counts.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset Polynomial
open scoped Classical
noncomputable section
variable {α β ι R : Type*} [Fintype α] [Fintype β] [Fintype ι] [CommRing R]

private def joinFaces : Finset α × Finset β ↪ Finset (α ⊕ β) where
  toFun s := s.1.disjSum s.2
  inj' := fun _ _ h => Prod.ext (disjSum_inj.mp h).1 (disjSum_inj.mp h).2

private def fullCenter : Finset β ↪ Finset (α ⊕ β) where
  toFun v := (univ : Finset α).disjSum v
  inj' := fun _ _ h => (disjSum_inj.mp h).2

/-- Link of the face consisting of all vertices in the first summand. -/
def subdivisionLink (K : Finset (Finset (α ⊕ β))) : Finset (Finset β) :=
  univ.filter fun v => fullCenter v ∈ K

private def offCenter (K : Finset (Finset (α ⊕ β))) :=
  K.filter fun s => s.toLeft ≠ univ

private def liftOld : Finset ι ↪ Finset (Option ι) where
  toFun s := s.map Function.Embedding.some
  inj' := fun _ _ h => map_inj.mp h

/-- The old faces avoiding the center survive. The new faces containing
the apex are joined from a proper central face and a link face. -/
def stellarFaces (K : Finset (Finset (α ⊕ β))) : Finset (Finset (Option (α ⊕ β))) :=
  (offCenter K).map liftOld ∪
    (((((univ : Finset (Finset α)).erase univ) ×ˢ subdivisionLink K).map joinFaces).map
      insertNone.toEmbedding)

private theorem old_decompose (K : Finset (Finset (α ⊕ β))) :
    K = offCenter K ∪ (subdivisionLink K).map fullCenter := by
  ext s
  by_cases h : s.toLeft = univ
  · have hs : fullCenter s.toRight = s := by
      change (univ : Finset α).disjSum s.toRight = s
      rw [← h,toLeft_disjSum_toRight]
    constructor
    · intro hk
      exact mem_union_right _ (mem_map.mpr ⟨s.toRight, mem_filter.mpr ⟨mem_univ _,hs ▸ hk⟩,hs⟩)
    · intro hk
      rcases mem_union.mp hk with hd | h'
      · exact (mem_filter.mp hd).1
      · obtain ⟨t,ht,rfl⟩ := mem_map.mp h'
        exact (mem_filter.mp ht).2
  · constructor
    · exact fun hk => mem_union_left _ (mem_filter.mpr ⟨hk,h⟩)
    · intro hk
      rcases mem_union.mp hk with hd | h'
      · exact (mem_filter.mp hd).1
      · obtain ⟨t,ht,rfl⟩ := mem_map.mp h'
        exact (mem_filter.mp ht).2

private def faceWeightAt (s : Finset ι) (x y : R) := x^s.card*y^(Fintype.card ι-s.card)

/-- Homogeneous face enumerator of marked and unmarked coordinates. -/
def faceEnumerator (K : Finset (Finset ι)) (x y : R) := ∑ s ∈ K, faceWeightAt s x y

private theorem split_weight (u : Finset α) (v : Finset β) (x y : R) :
    faceWeightAt (u.disjSum v) x y = faceWeightAt u x y*faceWeightAt v x y := by
  simp only [faceWeightAt,card_disjSum,Fintype.card_sum]
  rw [show Fintype.card α+Fintype.card β-(u.card+v.card) =
      (Fintype.card α-u.card)+(Fintype.card β-v.card) by
        have := u.card_le_univ; have := v.card_le_univ; omega,pow_add,pow_add]
  ring

private theorem sum_proper_weight (x y : R) :
    (∑ u ∈ (univ : Finset (Finset α)).erase univ, faceWeightAt u x y) =
      (x+y)^Fintype.card α - x^Fintype.card α := by
  have ht := prod_add (fun _ : α => x) (fun _ : α => y) univ
  have he : (∑ u : Finset α, faceWeightAt u x y) = (x+y)^Fintype.card α := by
    simpa [faceWeightAt,card_compl] using ht.symm
  have h := sum_erase_add (univ : Finset (Finset α)) (fun u => faceWeightAt u x y) (mem_univ univ)
  rw [he] at h
  simp only [faceWeightAt,card_univ,Nat.sub_self,pow_zero,mul_one] at h
  exact eq_sub_of_add_eq h

/-- Bihomogeneous stellar-subdivision formula. Its two specializations count
affine Stanley–Reisner points and coordinate-arrangement complements. -/
theorem faceEnumerator_stellar (K : Finset (Finset (α ⊕ β))) (x y : R) :
    faceEnumerator (stellarFaces K) x y = y*faceEnumerator K x y +
      (x*(x+y)^Fintype.card α-(x+y)*x^Fintype.card α)*faceEnumerator (subdivisionLink K) x y := by
  let L := subdivisionLink K
  let U := (univ : Finset (Finset α)).erase univ
  have hparent : faceEnumerator K x y = faceEnumerator (offCenter K) x y +
      x^Fintype.card α*faceEnumerator L x y := by
    unfold faceEnumerator
    conv_lhs => rw [old_decompose K]
    rw [sum_union,sum_map,mul_sum]
    · congr 1
      refine sum_congr rfl fun v _ => ?_
      simp [fullCenter,split_weight,faceWeightAt]
    · apply disjoint_left.mpr
      intro s hs ht
      obtain ⟨v,_,rfl⟩ := mem_map.mp ht
      exact (mem_filter.mp hs).2 (by simp [fullCenter])
  have hlift (s : Finset (α ⊕ β)) : faceWeightAt (liftOld s) x y = y*faceWeightAt s x y := by
    simp only [faceWeightAt,liftOld,Function.Embedding.coeFn_mk,card_map,Fintype.card_option]
    rw [show Fintype.card (α ⊕ β)+1-s.card = Fintype.card (α ⊕ β)-s.card+1 by
      have := s.card_le_univ; omega,pow_succ]
    ring
  have hapex (p : Finset α × Finset β) :
      faceWeightAt (insertNone (joinFaces p)) x y =
        x*(faceWeightAt p.1 x y*faceWeightAt p.2 x y) := by
    rw [← split_weight]
    simp only [faceWeightAt,card_insertNone,Fintype.card_option,joinFaces,Function.Embedding.coeFn_mk,
      Nat.add_sub_add_right,pow_succ]
    ring
  change faceEnumerator ((offCenter K).map liftOld ∪ ((U ×ˢ L).map joinFaces).map insertNone.toEmbedding) x y = _
  unfold faceEnumerator
  rw [sum_union]
  · simp only [sum_map,RelEmbedding.toEmbedding_apply,hlift,hapex,← mul_sum,sum_product]
    simp_rw [← mul_sum,← sum_mul]
    rw [show (∑ u ∈ U, faceWeightAt u x y) = _ from sum_proper_weight x y]
    change y*faceEnumerator (offCenter K) x y +
      x*(((x+y)^Fintype.card α-x^Fintype.card α)*faceEnumerator L x y) = _
    rw [show (∑ s ∈ K, faceWeightAt s x y) = _ from hparent]
    change _ = y*(faceEnumerator (offCenter K) x y+x^Fintype.card α*faceEnumerator L x y)+
      (x*(x+y)^Fintype.card α-(x+y)*x^Fintype.card α)*faceEnumerator L x y
    ring
  · apply disjoint_left.mpr
    intro s hs ht
    obtain ⟨v,_,hv⟩ := mem_map.mp hs
    obtain ⟨u,_,hu⟩ := mem_map.mp ht
    have hno : none ∉ liftOld v := by simp [liftOld]
    exact hno (hv ▸ hu ▸ none_mem_insertNone)

private theorem arrangement_eq_faceEnumerator (K : Finset (Finset ι)) :
    arrangementPolynomial K = faceEnumerator K (1:ℤ[X]) (X-1) := by
  simp [faceEnumerator,faceWeightAt,arrangementPolynomial]

/-- A stellar subdivision changes the actual arrangement counting polynomial
by a multiple of the link polynomial depending only on the center size. -/
theorem arrangementPolynomial_stellar (K : Finset (Finset (α ⊕ β))) :
    arrangementPolynomial (stellarFaces K) = (X-1)*arrangementPolynomial K +
      (X^Fintype.card α-X)*arrangementPolynomial (subdivisionLink K) := by
  simp only [arrangement_eq_faceEnumerator,faceEnumerator_stellar,one_pow,one_mul,mul_one,
    show (1:ℤ[X])+(X-1)=X by ring]

/-- Field points whose marked (or complementary) support belongs to a family. -/
def fieldSupportCount {γ : Type*} [Fintype γ] (F : Type*) [Field F] [Fintype F]
    (D : Finset F) (S : Finset (Finset γ)) : ℤ := (arrangementWords (fun _ : γ => D) S).card

/-- Local surgery for actual finite-field arrangement counts. The number of
new allowed words depends only on the old count and the center link. -/
theorem stellar_pointCount (F : Type*) [Field F] [Fintype F] (K : Finset (Finset (α ⊕ β))) :
    let q := (Fintype.card F:ℤ)
    fieldSupportCount F {0} (stellarFaces K) = (q-1)*fieldSupportCount F {0} K+
      (q^Fintype.card α-q)*fieldSupportCount F {0} (subdivisionLink K) := by
  dsimp only
  have h := congrArg (Polynomial.eval (Fintype.card F:ℤ)) (arrangementPolynomial_stellar K)
  simpa only [eval_add,eval_mul,eval_sub,eval_X,eval_pow,eval_one,eval_arrangementPolynomial] using h

private theorem complementary_count (F : Type*) [Field F] [Fintype F] (K : Finset (Finset ι)) :
    ((arrangementWords (fun _ : ι => ({0} : Finset F)ᶜ) K).card:ℤ) =
      faceEnumerator K ((Fintype.card F:ℤ)-1) 1 := by
  have hp : 1 ≤ Fintype.card F := Fintype.card_pos
  have hq : Fintype.card F - (Fintype.card F - 1) = 1 := by omega
  rw [card_arrangementWords,Nat.cast_sum]
  refine sum_congr rfl fun S _ => ?_
  simp only [card_compl,card_singleton,hq,Nat.cast_prod,Nat.cast_ite,Nat.cast_sub hp,Nat.cast_one,
    faceWeightAt,one_pow,mul_one]
  rw [← prod_filter]
  simp

/-- In the complementary convention, support on a face describes the affine
Stanley--Reisner locus. Stellar subdivision adds the link times the explicit
difference between the two torus counts. -/
theorem stellar_nonzeroSupport_count (F : Type*) [Field F] [Fintype F] (K : Finset (Finset (α ⊕ β))) :
    let q := (Fintype.card F:ℤ)
    fieldSupportCount F {0}ᶜ (stellarFaces K) = fieldSupportCount F {0}ᶜ K+
      ((q-1)*q^Fintype.card α-q*(q-1)^Fintype.card α)*fieldSupportCount F {0}ᶜ (subdivisionLink K) := by
  dsimp only [fieldSupportCount]
  simp only [complementary_count,faceEnumerator_stellar,sub_add_cancel,one_mul]

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
