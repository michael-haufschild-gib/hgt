import GaloisForLFunctions.HodgeTheoryWithoutVarieties.FiniteFaceSingularEuler
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheNerveOfTheStarCover
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeVertexDynamics
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeVertexLocalFlow
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeVertexSingularIndex

/-!
# Signed localization of the arithmetic Mertens count

The local index is the Euler characteristic of the actual block/exit
relative singular homology. Excision and the upper-link good cover prove
its finiteness and identify it with a signed count defined only by prime
products. Partitioning faces by their least prime gives the Mertens
localization formula, retaining the isolated-prime correction on the core.
The projective chart conjugates the arithmetic map to time one of the flow.
-/
noncomputable section


open Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open EffectiveScalingGeometry HodgeTheoryWithoutVarieties

/-- Signed count of upper-link faces, including the empty face. -/
def primeVertexSignedCount (B N : ℕ) (p : Fin (B+3)) : ℤ :=
  ∑ S∈primeUpperLinkFaces B N p,(-1)^S.card

/-- Faces charged to their least arithmetic vertex. -/
def primeMinimumFaces (B N : ℕ) (p : Fin (B+3)) : Finset (Finset (Fin (B+3))) :=
  (primeHeightFaces B N).filter (fun S => p∈S ∧ ∀q∈S,p≤q)

theorem primeUpperLink_apex_not_mem {B N : ℕ} {p : Fin (B+3)} {S : Finset (Fin (B+3))}
    (hS : S∈primeUpperLinkFaces B N p) : p∉S :=
  fun hp => (lt_irrefl p) ((mem_filter.mp hS).2.1 p hp)

/-- Inserting the apex identifies exit-link faces with faces whose least vertex is the apex. -/
theorem primeVertexSignedCount_eq_minimum_faces (B N : ℕ) (p : Fin (B+3)) :
    primeVertexSignedCount B N p=∑ T∈primeMinimumFaces B N p,-((-1:ℤ)^T.card) := by
  apply sum_bij (fun S _ => insert p S)
  · intro S hS
    have h := (mem_filter.mp hS).2
    refine mem_filter.mpr ⟨h.2,mem_insert_self p S,?_⟩
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact le_rfl
    · exact (h.1 q hq).le
  · intro S hS T hT he
    have hSp := primeUpperLink_apex_not_mem hS
    have hTp := primeUpperLink_apex_not_mem hT
    have hh := congrArg (fun U : Finset (Fin (B+3)) => U.erase p) he
    simpa only [erase_insert hSp,erase_insert hTp] using hh
  · intro T hT
    have h := mem_filter.mp hT
    refine ⟨T.erase p,mem_filter.mpr ⟨mem_univ _,?_,?_⟩,insert_erase h.2.1⟩
    · intro q hq
      have hq' := mem_erase.mp hq
      exact lt_of_le_of_ne (h.2.2 q hq'.2) (Ne.symm hq'.1)
    · rw [insert_erase h.2.1]
      exact h.1
  · intro S hS
    rw [card_insert_of_notMem (primeUpperLink_apex_not_mem hS),pow_succ]
    ring

/-- Unique least vertices partition every nonempty face. -/
theorem primeMinimumFaces_partition_sum (B N : ℕ) :
    (∑ p,∑ T∈primeMinimumFaces B N p,-((-1:ℤ)^T.card))=
      ∑ T∈(primeHeightFaces B N).erase ∅,-((-1:ℤ)^T.card) := by
  simp only [primeMinimumFaces,sum_filter]
  rw [sum_comm]
  have he (T : Finset (Fin (B+3))) :
      (∑ p,if p∈T ∧ ∀q∈T,p≤q then -((-1:ℤ)^T.card) else 0)=
        if T=∅ then 0 else -((-1:ℤ)^T.card) := by
    by_cases hT : T=∅
    · subst T
      simp only [Finset.notMem_empty,false_and,if_false,sum_const_zero,ite_true]
    · have hn := nonempty_iff_ne_empty.mpr hT
      have hm := min'_mem T hn
      have hmin : ∀q∈T,T.min' hn≤q := fun q hq => min'_le T q hq
      rw [if_neg hT,sum_eq_single (T.min' hn)]
      · rw [if_pos ⟨hm,hmin⟩]
      · intro q _ hq
        rw [if_neg]
        intro h
        exact hq (le_antisymm (h.2 _ hm) (hmin q h.1))
      · exact fun h => (h (mem_univ _)).elim
  simp_rw [he]
  have hs : (∑ T∈(primeHeightFaces B N).erase ∅,
      if T=∅ then (0:ℤ) else -((-1:ℤ)^T.card))=
      ∑ T∈primeHeightFaces B N,if T=∅ then (0:ℤ) else -((-1:ℤ)^T.card) := by
    apply sum_subset (erase_subset _ _)
    intro T hT hnot
    have heT : T=∅ := by
      by_contra hne
      exact hnot (mem_erase.mpr ⟨hne,hT⟩)
    rw [if_pos heT]
  rw [←hs]
  apply sum_congr rfl
  intro T hT
  rw [if_neg (mem_erase.mp hT).1]

/-- Local signed counts recover ordinary Euler characteristic, with the empty-face correction. -/
theorem primeVertexSignedCount_sum (B N : ℕ) (hN : 1≤N) :
    (∑ p,primeVertexSignedCount B N p)=1-∑ S∈primeHeightFaces B N,(-1:ℤ)^S.card := by
  simp_rw [primeVertexSignedCount_eq_minimum_faces]
  rw [primeMinimumFaces_partition_sum]
  have he : (∅ : Finset (Fin (B+3)))∈primeHeightFaces B N :=
    mem_primeHeightFaces.mpr ⟨by simp only [Finset.notMem_empty,false_implies,implies_true],by simpa only [prod_empty] using hN⟩
  rw [sum_neg_distrib,←sum_erase_add (f := fun S : Finset (Fin (B+3)) => (-1:ℤ)^S.card) _ he]
  simp only [card_empty,pow_zero]
  ring

#print axioms primeVertexSignedCount_eq_minimum_faces
#print axioms primeMinimumFaces_partition_sum
#print axioms primeVertexSignedCount_sum

/-- The finite ambient realization retains exactly the original arithmetic Euler sum. -/
theorem primeHeightFaceSum_eq_nerve (B N : ℕ) (hNB : N≤B) :
    (∑S∈primeHeightFaces B N,(-1:ℤ)^S.card)=nerveEulerChar N := by
  apply sum_bij (fun S _ => S.map Fin.valEmbedding)
  · intro S hS
    apply mem_squarefreeNerve.mpr
    simpa only [forall_mem_map,Fin.valEmbedding_apply,prod_map] using mem_primeHeightFaces.mp hS
  · intro S _ T _ he
    exact Finset.map_injective Fin.valEmbedding he
  · intro T hT
    have ht : T∈_root_.RHTower.primeSets N := HTGeometry.mem_primeSets_iff.mpr (mem_squarefreeNerve.mp hT)
    obtain ⟨S,hS,he⟩ := (primeSets_iff_exists_heightFace_of_le B N hNB T).mp ht
    exact ⟨S,hS,he⟩
  · intro S _
    rw [card_map]

/-- The local arithmetic signed counts sum exactly to one minus the Mertens sum. -/
theorem primeVertexSignedCount_sum_mertens (B N : ℕ) (hNB : N≤B) (hN : 1≤N) :
    (∑p,primeVertexSignedCount B N p)=1-∑n∈Icc 1 N,ArithmeticFunction.moebius n := by
  rw [primeVertexSignedCount_sum B N hN,primeHeightFaceSum_eq_nerve B N hNB,nerveEulerChar_eq_mertens]

#print axioms primeHeightFaceSum_eq_nerve
#print axioms primeVertexSignedCount_sum_mertens

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts


open Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open EffectiveScalingGeometry HodgeTheoryWithoutVarieties DifferentialGeometry.Homology

private theorem primeFace_vertex_valid {B N : ℕ} {S : Finset (Fin (B+3))}
    (hS : S∈primeHeightFaces B N) {p : Fin (B+3)} (hpS : p∈S) : p.val.Prime ∧ p.val≤N := by
  have h := mem_primeHeightFaces.mp hS
  exact ⟨h.1 p hpS,(Nat.le_of_dvd (prod_pos (fun q hq => (h.1 q hq).pos))
    (dvd_prod_of_mem (fun q : Fin (B+3) => q.val) hpS)).trans h.2⟩

theorem primeUpperLink_down_closed (B N : ℕ) (p : Fin (B+3)) :
    ∀S∈primeUpperLinkFaces B N p,∀T⊆S,T∈primeUpperLinkFaces B N p := by
  intro S hS T hTS
  have h := (mem_filter.mp hS).2
  exact mem_filter.mpr ⟨mem_univ _,fun q hq => h.1 q (hTS hq),
    primeHeightFaces_down_closed B N (insert p S) h.2 (insert p T) (insert_subset_insert p hTS)⟩

/-- The empty upper face is present at every actual arithmetic vertex. -/
theorem empty_mem_primeUpperLink {B N : ℕ} (p : Fin (B+3))
    (hp : p.val.Prime) (hpN : p.val≤N) : ∅∈primeUpperLinkFaces B N p := by
  apply mem_filter.mpr
  refine ⟨mem_univ _,by simp only [Finset.notMem_empty,false_implies,implies_true],?_⟩
  rw [insert_empty_eq]
  exact mem_primeHeightFaces.mpr ⟨fun q hq => by simpa only [mem_singleton.mp hq] using hp,
    by simpa only [prod_singleton] using hpN⟩

/-- The actual local relative singular homology is finite in rank and degree at every label. -/
theorem primeVertexRelativeHomology_finite (B N : ℕ) (p : Fin (B+3)) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of (primeVertexBlock B N p))
        (primeVertexExit B N p) (ModuleCat.of ℚ ℚ)) := by
  by_cases hp : p.val.Prime ∧ p.val≤N
  · letI : ContractibleSpace (primeVertexBlock B N p) :=
      primeVertexBlock_contractible p hp.1 hp.2
    have hlink := (finiteFace_singular_euler (primeUpperLinkFaces B N p)
      (primeUpperLink_down_closed B N p)).1
    have hexit := (finiteHomologyType_iff_of_homotopyEquiv ℚ
      (X := TopCat.of (primeVertexExit B N p))
      (Y := TopCat.of (faceFamilySpace (primeUpperLinkFaces B N p)))
      (primeExitLinkHomotopyEquiv B N p)).mpr hlink
    exact finiteHomologyType_relativeChainComplex _ _ ℚ hexit
      (finiteHomologyType_of_contractible ℚ)
  · letI : IsEmpty (primeVertexCone B N p) := ⟨fun y => by
      obtain ⟨S,hS,hpS,_⟩ := y.property.2.2
      exact hp (primeFace_vertex_valid hS hpS)⟩
    exact finiteHomologyType_relativeChainComplex _ _ ℚ
      (finiteHomologyType_of_subsingleton ℚ) (finiteHomologyType_of_subsingleton ℚ)

#print axioms primeVertexRelativeHomology_finite

/-- At every prime vertex the local singular-homology index equals its arithmetic exit-face count. -/
theorem primeVertexRelativeIndex_eq_signedCount_of_prime {B N : ℕ} (p : Fin (B+3))
    (hp : p.val.Prime) (hpN : p.val≤N) :
    primeVertexRelativeIndex B N p=primeVertexSignedCount B N p := by
  letI : ContractibleSpace (primeVertexBlock B N p) := primeVertexBlock_contractible p hp hpN
  have hface := finiteFace_singular_euler (primeUpperLinkFaces B N p) (primeUpperLink_down_closed B N p)
  have he := primeExitLinkHomotopyEquiv B N p
  have hi : primeVertexRelativeIndex B N p=
      1-eulerChar ℚ (TopCat.of (faceFamilySpace (primeUpperLinkFaces B N p))) :=
    relativeEuler_contractible_exit (TopCat.of (primeVertexBlock B N p))
      (TopCat.of (faceFamilySpace (primeUpperLinkFaces B N p))) (primeVertexExit B N p) he hface.1
  rw [hi,hface.2,sum_neg_distrib]
  unfold primeVertexSignedCount
  rw [←sum_erase_add (f := fun S : Finset (Fin (B+3)) => (-1:ℤ)^S.card) _
    (empty_mem_primeUpperLink p hp hpN)]
  simp only [card_empty,pow_zero]
  ring

/-- Invalid ambient labels have empty local pairs and contribute zero. -/
theorem primeVertexRelativeIndex_zero_of_not_vertex {B N : ℕ} (p : Fin (B+3))
    (hp : ¬(p.val.Prime ∧ p.val≤N)) : primeVertexRelativeIndex B N p=0 := by
  letI : IsEmpty (primeVertexCone B N p) := ⟨fun y => by
    obtain ⟨S,hS,hpS,_⟩ := y.property.2.2
    exact hp (primeFace_vertex_valid hS hpS)⟩
  exact relativeEuler_empty (TopCat.of (primeVertexBlock B N p)) (primeVertexExit B N p)

theorem primeVertexSignedCount_zero_of_not_vertex {B N : ℕ} (p : Fin (B+3))
    (hp : ¬(p.val.Prime ∧ p.val≤N)) : primeVertexSignedCount B N p=0 := by
  have he : primeUpperLinkFaces B N p=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro S hS
    exact hp (primeFace_vertex_valid (mem_filter.mp hS).2.2 (mem_insert_self p S))
  rw [primeVertexSignedCount,he,sum_empty]

/-- No ambient label contributes an artificial local index. -/
theorem primeVertexRelativeIndex_eq_signedCount (B N : ℕ) (p : Fin (B+3)) :
    primeVertexRelativeIndex B N p=primeVertexSignedCount B N p := by
  by_cases hp : p.val.Prime ∧ p.val≤N
  · exact primeVertexRelativeIndex_eq_signedCount_of_prime p hp.1 hp.2
  · rw [primeVertexRelativeIndex_zero_of_not_vertex p hp,primeVertexSignedCount_zero_of_not_vertex p hp]

/-- Actual local relative singular-homology indices localize the arithmetic Mertens count. -/
theorem primeVertexRelativeIndex_sum_mertens (B N : ℕ) (hNB : N≤B) (hN : 1≤N) :
    (∑p,primeVertexRelativeIndex B N p)=1-∑n∈Icc 1 N,ArithmeticFunction.moebius n := by
  simp_rw [primeVertexRelativeIndex_eq_signedCount]
  exact primeVertexSignedCount_sum_mertens B N hNB hN

#print axioms primeVertexRelativeIndex_eq_signedCount
#print axioms primeVertexRelativeIndex_sum_mertens

/-- Every isolated upper-half prime has an empty exit link. -/
theorem primeUpperLink_upperHalf (B N : ℕ) (p : Fin (B+3))
    (hp : p.val.Prime) (hpN : p.val≤N) (hlate : N<2*p.val) :
    primeUpperLinkFaces B N p={∅} := by
  ext S
  constructor
  · intro hS
    have he := HeightHomotopyArithmeticCounts.upperPrime_face_singleton hlate
      (mem_filter.mp hS).2.2 (mem_insert_self p S)
    apply mem_singleton.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqp : q=p := by
      have h : q∈insert p S := mem_insert_of_mem hq
      rw [he] at h
      exact mem_singleton.mp h
    exact (lt_irrefl p) (hqp ▸ (mem_filter.mp hS).2.1 q hq)
  · intro hS
    rw [mem_singleton] at hS
    subst S
    exact empty_mem_primeUpperLink p hp hpN

/-- The isolated prime components each contribute index one. -/
theorem primeVertexRelativeIndex_upperHalf (B N : ℕ) (p : Fin (B+3))
    (hp : p.val.Prime) (hpN : p.val≤N) (hlate : N<2*p.val) :
    primeVertexRelativeIndex B N p=1 := by
  rw [primeVertexRelativeIndex_eq_signedCount,primeVertexSignedCount,
    primeUpperLink_upperHalf B N p hp hpN hlate,sum_singleton,card_empty,pow_zero]

private theorem upperHalfVertex_card (B N : ℕ) (hNB : N≤B) :
    (univ.filter (fun p : Fin (B+3) => p.val.Prime ∧ N<2*p.val ∧ p.val≤N)).card=
      ((Ioc (N/2) N).filter Nat.Prime).card := by
  have he : (univ.filter (fun p : Fin (B+3) => p.val.Prime ∧ N<2*p.val ∧ p.val≤N)).map
      Fin.valEmbedding=(Ioc (N/2) N).filter Nat.Prime := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp,rfl⟩ := mem_map.mp hq
      have h := (mem_filter.mp hp).2
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by change N/2<p.val; omega,h.2.2⟩,h.1⟩
    · intro hq
      have h := mem_filter.mp hq
      have hqN := mem_Ioc.mp h.1
      let p : Fin (B+3) := ⟨q,by omega⟩
      exact mem_map.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,h.2,by change N<2*q; omega,hqN.2⟩,rfl⟩
  have hc := congrArg Finset.card he
  simpa only [card_map] using hc

/-- Signed localization on the connected core retains exactly the removed prime-component mass. -/
theorem primeCoreVertexRelativeIndex_sum (B N : ℕ) (hNB : N≤B) (hN : 4≤N) :
    (∑p∈univ.filter (fun p : Fin (B+3) => 2*p.val≤N),primeVertexRelativeIndex B N p)=
      1-(∑n∈Icc 1 N,ArithmeticFunction.moebius n)-
        (((Ioc (N/2) N).filter Nat.Prime).card:ℤ) := by
  have hout : (∑p∈univ.filter (fun p : Fin (B+3) => N<2*p.val),primeVertexRelativeIndex B N p)=
      (((Ioc (N/2) N).filter Nat.Prime).card:ℤ) := by
    have he (p : Fin (B+3)) (hp : p∈univ.filter (fun p : Fin (B+3) => N<2*p.val)) :
        primeVertexRelativeIndex B N p=if p.val.Prime ∧ p.val≤N then 1 else 0 := by
      by_cases hv : p.val.Prime ∧ p.val≤N
      · rw [if_pos hv]
        exact primeVertexRelativeIndex_upperHalf B N p hv.1 hv.2 (mem_filter.mp hp).2
      · rw [if_neg hv]
        exact primeVertexRelativeIndex_zero_of_not_vertex p hv
    rw [sum_congr rfl he,←sum_filter]
    have hf : (univ.filter (fun p : Fin (B+3) => N<2*p.val)).filter
        (fun p => p.val.Prime ∧ p.val≤N)=
        univ.filter (fun p : Fin (B+3) => p.val.Prime ∧ N<2*p.val ∧ p.val≤N) := by
      ext p
      simp only [mem_filter,mem_univ,true_and]
      tauto
    rw [hf,sum_const,nsmul_eq_mul,mul_one,upperHalfVertex_card B N hNB]
  have hs : (∑p∈univ.filter (fun p : Fin (B+3) => 2*p.val≤N),primeVertexRelativeIndex B N p)+
      (∑p∈univ.filter (fun p : Fin (B+3) => N<2*p.val),primeVertexRelativeIndex B N p)=
      ∑p,primeVertexRelativeIndex B N p := by
    simpa only [not_le] using sum_filter_add_sum_filter_not univ
      (fun p : Fin (B+3) => 2*p.val≤N) (fun p => primeVertexRelativeIndex B N p)
  rw [hout,primeVertexRelativeIndex_sum_mertens B N hNB (by omega)] at hs
  linarith only [hs]

#print axioms primeVertexRelativeIndex_upperHalf
#print axioms primeCoreVertexRelativeIndex_sum

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts


open Finset ContinuousMap
open DifferentialGeometry.Simplex
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open EffectiveScalingGeometry

def primeVertexStarMap (B N : ℕ) (p : Fin (B+3)) :
    C(primeVertexOpenStar B N p,primeVertexOpenStar B N p) where
  toFun x := ⟨primeVertexMap B N x.val,by
    change 0<(1+((1:unitInterval):ℝ)*(p.val:ℝ))*x.val.val.val p/
      primeVertexNormalizer 1 x.val.val
    have hp : 0<x.val.val.val p := x.property
    have hw : 0<1+((1:unitInterval):ℝ)*(p.val:ℝ) := by
      change 0<1+1*(p.val:ℝ)
      positivity
    exact div_pos (mul_pos hw hp)
      (lt_of_lt_of_le zero_lt_one (primeVertexNormalizer_one_le 1 x.val.val))⟩
  continuous_toFun := ((primeVertexMap B N).continuous.comp continuous_subtype_val).subtype_mk _

theorem primeConeFlow_one_apply {B N : ℕ} (p : Fin (B+3)) (y : primeVertexCone B N p)
    (q : Fin (B+3)) :
    (primeConeFlow p 1 y).val q=((q.val:ℝ)+1)/((p.val:ℝ)+1)*y.val q := by
  change Real.exp (1*(Real.log ((q.val:ℝ)+1)-Real.log ((p.val:ℝ)+1)))*y.val q=_
  rw [one_mul,Real.exp_sub,Real.exp_log (by positivity),Real.exp_log (by positivity)]

/-- The actual map and the local arithmetic flow are conjugate at time one. -/
theorem primeVertexMap_projective_conjugacy {B N : ℕ} (p : Fin (B+3))
    (x : primeVertexOpenStar B N p) :
    primeStarToCone (primeVertexStarMap B N p x)=primeConeFlow p 1 (primeStarToCone x) := by
  apply Subtype.ext
  funext q
  rw [primeConeFlow_one_apply]
  by_cases hq : q=p
  · subst q
    exact (primeStarToCone (primeVertexStarMap B N p x)).property.2.1.trans
      (by rw [(primeStarToCone x).property.2.1,mul_zero])
  · change ((1+((1:unitInterval):ℝ)*(q.val:ℝ))*x.val.val.val q/primeVertexNormalizer 1 x.val.val)/
        ((1+((1:unitInterval):ℝ)*(p.val:ℝ))*x.val.val.val p/primeVertexNormalizer 1 x.val.val)-
        (if q=p then (1:ℝ) else 0)=
      ((q.val:ℝ)+1)/((p.val:ℝ)+1)*(x.val.val.val q/x.val.val.val p-(if q=p then (1:ℝ) else 0))
    rw [if_neg hq,sub_zero,sub_zero]
    have hx : x.val.val.val p≠0 := ne_of_gt x.property
    have hd : primeVertexNormalizer 1 x.val.val≠0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one (primeVertexNormalizer_one_le 1 x.val.val))
    have hp : (p.val:ℝ)+1≠0 := by positivity
    simp only [show ((1:unitInterval):ℝ)=1 from rfl,one_mul]
    field_simp [hx,hd,hp]
    ring

#print axioms primeVertexMap_projective_conjugacy
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts