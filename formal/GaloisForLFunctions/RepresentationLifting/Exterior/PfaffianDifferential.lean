import GaloisForLFunctions.HTGeometry.SignedPairingExpansion
import GaloisForLFunctions.BezoutValuationIncidence.Finite.SubsetSumRecovery
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Recovery from the differential of Pfaffian observations

At the standard symplectic contraction, paired words observe subset sums
of the diagonal pair variations. Two distinguished endpoints and unused
complete pairs then recover every contraction entry. This proves injectivity
of the actual Pfaffian differential below the top degree.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RepresentationLifting.Exterior
noncomputable section
variable {α : Type*}

/-- First variation of the signed perfect-pairing expansion. -/
def pfaffianFirstJet (J A : α → α → ℝ) : List α → ℝ
  | [] => 0
  | u::t => ∑ k : Fin t.length, (-1:ℝ)^(k:ℕ) *
      (A u t[(k:ℕ)] * pfaffianPairing ℝ J (t.eraseIdx (k:ℕ)) +
       J u t[(k:ℕ)] * pfaffianFirstJet J A (t.eraseIdx (k:ℕ)))
termination_by l => l.length
decreasing_by
  have h := List.length_eraseIdx_le t (k:ℕ)
  simp only [List.length_cons]
  omega

lemma pfaffianFirstJet_cons (J A : α → α → ℝ) (u : α) (t : List α) :
    pfaffianFirstJet J A (u::t)=signedPositionSum ℝ t (fun a s =>
      A u a*pfaffianPairing ℝ J s+J u a*pfaffianFirstJet J A s) := by
  rw [pfaffianFirstJet]
  rfl

/-- The recursive first jet is the derivative of the actual Pfaffian polynomial. -/
theorem pfaffianFirstJet_hasDerivAt (J A : α → α → ℝ) (l : List α) :
    HasDerivAt (fun t : ℝ => pfaffianPairing ℝ (fun i j => J i j+t*A i j) l)
      (pfaffianFirstJet J A l) 0 := by
  match l with
  | [] => simpa only [pfaffianPairing,pfaffianFirstJet] using hasDerivAt_const (0:ℝ) (1:ℝ)
  | u::s =>
    rw [pfaffianFirstJet]
    simp only [pfaffianPairing]
    have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin s.length))) (fun k _ =>
      ((((hasDerivAt_id (0:ℝ)).mul_const (A u s[(k:ℕ)])).const_add (J u s[(k:ℕ)])).mul
        (pfaffianFirstJet_hasDerivAt J A (s.eraseIdx (k:ℕ)))).const_mul ((-1:ℝ)^(k:ℕ)))
    convert! h using 1
    · funext t
      simp only [id_eq,Pi.mul_apply,Finset.sum_apply]
    · simp only [zero_mul,add_zero,mul_one,one_mul,id_eq]
termination_by l.length
decreasing_by
  have h := List.length_eraseIdx_le s (k:ℕ)
  simp only [List.length_cons]
  omega

private lemma pfaffian_zero_row (J : α → α → ℝ) (u : α) (s : List α)
    (h : ∀ a ∈ s, J u a=0) : pfaffianPairing ℝ J (u::s)=0 := by
  rw [pfaffianPairing]
  apply Finset.sum_eq_zero
  intro k _
  rw [h _ (List.getElem_mem _)]
  simp only [zero_mul,mul_zero]

private lemma pfaffian_isolated_pair (J : α → α → ℝ) (u v : α) (s : List α)
    (hu : ∀ a ∈ s, J u a=0) :
    pfaffianPairing ℝ J (u::v::s)=J u v*pfaffianPairing ℝ J s := by
  rw [pfaffianPairing_cons,signedPositionSum_cons]
  have hz : signedPositionSum ℝ s (fun a t => J u a*pfaffianPairing ℝ J (v::t))=0 := by
    rw [signedPositionSum]
    apply Finset.sum_eq_zero
    intro k _
    rw [hu _ (List.getElem_mem _)]
    simp only [zero_mul,smul_zero]
  rw [hz,sub_zero]

private lemma pfaffianFirstJet_isolated_pair (J A : α → α → ℝ) (u v : α) (s : List α)
    (hu : ∀ a ∈ s, J u a=0) (hv : ∀ a ∈ s, J v a=0) :
    pfaffianFirstJet J A (u::v::s)=
      A u v*pfaffianPairing ℝ J s+J u v*pfaffianFirstJet J A s := by
  rw [pfaffianFirstJet_cons,signedPositionSum_cons]
  have hz : signedPositionSum ℝ s (fun a t =>
      A u a*pfaffianPairing ℝ J (v::t)+J u a*pfaffianFirstJet J A (v::t))=0 := by
    rw [signedPositionSum]
    apply Finset.sum_eq_zero
    intro k _
    have hv' : ∀ a ∈ s.eraseIdx (k:ℕ), J v a=0 := by
      intro a ha
      exact hv a (List.mem_of_mem_eraseIdx ha)
    rw [hu _ (List.getElem_mem _),pfaffian_zero_row J v _ hv']
    simp only [mul_zero,zero_mul,add_zero,smul_zero]
  rw [hz,sub_zero]

/-- Standard symplectic contraction in a basis arranged into ordered pairs. -/
def pairedSymplectic {ι : Type*} [DecidableEq ι] (u v : ι × Bool) : ℝ :=
  if u.1=v.1 then (if u.2 then 0 else 1)-(if v.2 then 0 else 1) else 0

/-- Each index contributes its two basis vectors, in the order `false`, `true`. -/
def pairedWord {ι : Type*} (l : List ι) : List (ι × Bool) :=
  l.flatMap (fun i => [(i,false),(i,true)])

lemma pairedWord_length {ι : Type*} (l : List ι) : (pairedWord l).length=2*l.length := by
  induction l with
  | nil => simp [pairedWord]
  | cons i l ih => simp only [pairedWord,List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons] at *; omega

private lemma pairedWord_fst_mem {ι : Type*} {l : List ι} {x : ι × Bool}
    (hx : x ∈ pairedWord l) : x.1 ∈ l := by
  simp only [pairedWord,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hx
  obtain ⟨i,hi,hx⟩ := hx
  rcases hx with rfl | rfl <;> exact hi

private lemma pairedSymplectic_outside {ι : Type*} [DecidableEq ι] (u : ι × Bool) (l : List ι)
    (hu : u.1 ∉ l) : ∀ a ∈ pairedWord l, pairedSymplectic u a=0 := by
  intro a ha
  have hne : u.1 ≠ a.1 := fun h => hu (h.symm ▸ pairedWord_fst_mem ha)
  exact if_neg hne

/-- A word made of distinct complete pairs has unit Pfaffian. -/
theorem pfaffian_pairedWord {ι : Type*} [DecidableEq ι] (l : List ι) (hl : l.Nodup) :
    pfaffianPairing ℝ pairedSymplectic (pairedWord l)=1 := by
  induction l with
  | nil => simp [pairedWord]
  | cons i l ih =>
    have hn := List.nodup_cons.mp hl
    change pfaffianPairing ℝ pairedSymplectic ((i,false)::(i,true)::pairedWord l)=1
    rw [pfaffian_isolated_pair _ _ _ _ (pairedSymplectic_outside (i,false) l hn.1),ih hn.2]
    simp [pairedSymplectic]

/-- Paired words observe exactly the sum of the corresponding diagonal pair variations. -/
theorem pfaffianFirstJet_pairedWord {ι : Type*} [DecidableEq ι]
    (A : (ι × Bool) → (ι × Bool) → ℝ) (l : List ι) (hl : l.Nodup) :
    pfaffianFirstJet pairedSymplectic A (pairedWord l)=
      (l.map (fun i => A (i,false) (i,true))).sum := by
  induction l with
  | nil => simp [pairedWord,pfaffianFirstJet]
  | cons i l ih =>
    have hn := List.nodup_cons.mp hl
    change pfaffianFirstJet pairedSymplectic A ((i,false)::(i,true)::pairedWord l)=_
    rw [pfaffianFirstJet_isolated_pair _ _ _ _ _
      (pairedSymplectic_outside (i,false) l hn.1) (pairedSymplectic_outside (i,true) l hn.1),
      pfaffian_pairedWord l hn.2,ih hn.2]
    simp [pairedSymplectic]

/-- Two distinguished endpoints isolate their contraction, up to the already observed diagonal sum. -/
theorem pfaffianFirstJet_endpoints {ι : Type*} [DecidableEq ι]
    (A : (ι × Bool) → (ι × Bool) → ℝ) (u v : ι × Bool) (l : List ι)
    (hl : l.Nodup) (hu : u.1 ∉ l) (hv : v.1 ∉ l) :
    pfaffianFirstJet pairedSymplectic A (u::v::pairedWord l)=
      A u v+pairedSymplectic u v*(l.map (fun i => A (i,false) (i,true))).sum := by
  rw [pfaffianFirstJet_isolated_pair _ _ _ _ _
    (pairedSymplectic_outside u l hu) (pairedSymplectic_outside v l hv),
    pfaffian_pairedWord l hl,pfaffianFirstJet_pairedWord A l hl,mul_one]

#print axioms pfaffianFirstJet_hasDerivAt
#print axioms pfaffianFirstJet_pairedWord
#print axioms pfaffianFirstJet_endpoints

/-- All first-order Pfaffian observations of size `2(k+2)` on `k+l+3` symplectic pairs. -/
def pairedPfaffianDifferential (k l : ℕ)
    (A : (Fin (k+l+3) × Bool) → (Fin (k+l+3) × Bool) → ℝ) :
    {w : List (Fin (k+l+3) × Bool) // w.length=2*(k+2)} → ℝ :=
  fun w => pfaffianFirstJet pairedSymplectic A w.1

/-- Every contraction entry is determined below the top Pfaffian degree. -/
theorem pairedPfaffianDifferential_injective (k l : ℕ) :
    Function.Injective (pairedPfaffianDifferential k l) := by
  intro A B h
  have hd : (fun i => A (i,false) (i,true))=(fun i => B (i,false) (i,true)) := by
    apply fixedSubsetObservation_injective k l
    funext S
    have hcard : S.1.card=k+2 := (Finset.mem_powersetCard.mp S.2).2
    have hw : (pairedWord S.1.toList).length=2*(k+2) := by
      rw [pairedWord_length,Finset.length_toList,hcard]
    have he := congrFun h ⟨pairedWord S.1.toList,hw⟩
    change pfaffianFirstJet pairedSymplectic A (pairedWord S.1.toList)=
      pfaffianFirstJet pairedSymplectic B (pairedWord S.1.toList) at he
    rw [pfaffianFirstJet_pairedWord A _ S.1.nodup_toList,
      pfaffianFirstJet_pairedWord B _ S.1.nodup_toList] at he
    simpa only [fixedSubsetObservation,fixedSubsetSum,Finset.sum_map_toList] using he
  funext u v
  let T : Finset (Fin (k+l+3)) := (Finset.univ.erase u.1).erase v.1
  have ht : k+1 ≤ T.card := by
    simp only [T,Finset.card_erase_eq_ite,Finset.mem_erase,Finset.mem_univ,
      Finset.card_univ,Fintype.card_fin,if_true]
    split_ifs <;> omega
  obtain ⟨S,hST,hS⟩ := Finset.exists_subset_card_eq ht
  have hu : u.1 ∉ S.toList := by
    simp only [Finset.mem_toList]
    intro hm
    have he := Finset.mem_erase.mp (hST hm)
    exact (Finset.mem_erase.mp he.2).1 rfl
  have hv : v.1 ∉ S.toList := by
    simp only [Finset.mem_toList]
    intro hm
    exact (Finset.mem_erase.mp (hST hm)).1 rfl
  have hw : (u::v::pairedWord S.toList).length=2*(k+2) := by
    rw [List.length_cons,List.length_cons,pairedWord_length,Finset.length_toList,hS]
    omega
  have he := congrFun h ⟨u::v::pairedWord S.toList,hw⟩
  change pfaffianFirstJet pairedSymplectic A (u::v::pairedWord S.toList)=
    pfaffianFirstJet pairedSymplectic B (u::v::pairedWord S.toList) at he
  rw [pfaffianFirstJet_endpoints A _ _ _ S.nodup_toList hu hv,
    pfaffianFirstJet_endpoints B _ _ _ S.nodup_toList hu hv,hd] at he
  exact add_right_cancel he

#print axioms pairedPfaffianDifferential_injective
end
end GaloisForLFunctions.RepresentationLifting.Exterior
