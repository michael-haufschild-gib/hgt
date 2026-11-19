import GaloisForLFunctions.RestrictedFactorizationCalculus.AlternatingCofactorDescent

/-!
# Exact gain and optimality of an alternating transport

Reached old positives and unreached new positives give the two parts of a
minimum vertex cover: use the old negative images of the former and the
positive vertices of the latter. Any joint matching retaining the old
positives and new negatives attains this bound on the union of the edges.
-/

noncomputable section

open Finset
open scoped Classical
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev DyadicMatching (S : Finset ℕ) := OppositeParityMatching GlobalDyadicOneTwoRel S

/-- Every edge used by the matching is an actual edge of one of the two inputs. -/
def usesTransportEdges {S : Finset ℕ} (A B M : DyadicMatching S) : Prop :=
  ∀ x ∈ M.sources, (x ∈ A.sources ∧ M.partner x = A.partner x) ∨
    (x ∈ B.sources ∧ M.partner x = B.partner x)

/-- New-only positive vertices which are not consumed by a retry from an old-only vertex. -/
def transportGain {S : Finset ℕ} (A B : DyadicMatching S) : Finset ℕ :=
  (B.sources \ A.sources).filter (fun x => ¬switchReachable A B x)

private theorem off_in_new {S : Finset ℕ} {A B : DyadicMatching S} {x : ℕ}
    (ha : x ∈ A.sources) (hoff : ¬switchReachable A B x) : x ∈ B.sources := by
  by_contra hn
  exact hoff ⟨x,ha,hn,0,.nil⟩

private theorem incoming {S : Finset ℕ} {A B : DyadicMatching S} {y : ℕ}
    (hy : switchReachable A B y) (hb : y ∈ B.sources) :
    ∃ x ∈ A.sources, switchReachable A B x ∧ A.partner x = B.partner y := by
  obtain ⟨a,ha,hn,k,hw⟩ := hy
  cases hw with
  | nil => exact False.elim (hn hb)
  | snoc prev last => exact ⟨_,last.1,⟨a,ha,hn,_,prev⟩,last.2.2⟩

/-- A joint matching has exactly one extra edge per unreached new-only
positive. No rearrangement of either input's edges alone or together can
produce a larger matching. This applies to every sharp finite domain. -/
theorem exact_gain_of_joint_transport {S : Finset ℕ}
    (A B M : OppositeParityMatching GlobalDyadicOneTwoRel S)
    (hA : A.sources ⊆ M.sources) (hB : B.targets ⊆ M.targets) (hE : usesTransportEdges A B M) :
    M.sources.card = A.sources.card + (transportGain A B).card ∧
      ∀ C : OppositeParityMatching GlobalDyadicOneTwoRel S, usesTransportEdges A B C →
        C.sources.card ≤ M.sources.card := by
  classical
  let on := switchReachable A B
  let U := A.sources.filter on
  let P := B.sources.filter (fun x => ¬on x)
  let N := U.image A.partner
  have hU : U ⊆ A.sources := filter_subset _ _
  have hP : P ⊆ B.sources := filter_subset _ _
  have cardN : N.card = U.card := card_image_of_injOn (A.injOn.mono (coe_subset.mpr hU))
  -- Every reached edge ends in N, including a new edge at the end of a retry.
  have target {C : DyadicMatching S} (hC : usesTransportEdges A B C) {x : ℕ}
      (hx : x ∈ C.sources) (hr : on x) : C.partner x ∈ N := by
    rcases hC x hx with ⟨ha,he⟩ | ⟨hb,he⟩
    · rw [he]
      exact mem_image_of_mem A.partner (mem_filter.mpr ⟨ha,hr⟩)
    · obtain ⟨z,hz,ho,hp⟩ := incoming hr hb
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,ho⟩,hp.trans he.symm⟩
  have cap {C : DyadicMatching S} (hC : usesTransportEdges A B C) :
      C.sources.card ≤ U.card + P.card := by
    let R := C.sources.filter on
    have hin : R.image C.partner ⊆ N := by
      intro n hn
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
      exact target hC (mem_filter.mp hx).1 (mem_filter.mp hx).2
    have hc := card_le_card hin
    rw [card_image_of_injOn (C.injOn.mono (coe_subset.mpr (filter_subset _ _))),cardN] at hc
    have hoff : C.sources.filter (fun x => ¬on x) ⊆ P := by
      intro x hx
      obtain ⟨hs,hn⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨?_,hn⟩
      exact (hC x hs).elim (fun e => off_in_new e.1 hn) And.left
    have hcOff := card_le_card hoff
    have hs := card_filter_add_card_filter_not (s := C.sources) on
    change (C.sources.filter on).card ≤ U.card at hc
    omega
  -- All old sources in U use N. Their distinct images already fill it.
  have hUM := hU.trans hA
  have hi : U.image M.partner ⊆ N := by
    intro n hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    exact target hE (hUM hx) (mem_filter.mp hx).2
  have hcU : (U.image M.partner).card = N.card :=
    (card_image_of_injOn (M.injOn.mono (coe_subset.mpr hUM))).trans cardN.symm
  have hie := eq_of_subset_of_card_le hi hcU.ge
  have hN : N ⊆ M.targets := by
    rw [←hie]; exact image_subset_image hUM
  -- New targets of P are disjoint from N by forward closure of the walk.
  have dis : Disjoint N (P.image B.partner) := by
    apply disjoint_left.mpr
    intro n hn hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    obtain ⟨y,hy,he⟩ := mem_image.mp hp
    exact (mem_filter.mp hy).2 (switchReachable_step (mem_filter.mp hx).2 ⟨hU hx,hP hy,he.symm⟩)
  have full := card_le_card (union_subset hN ((image_subset_image hP).trans hB))
  rw [card_union_of_disjoint dis,cardN,card_image_of_injOn (B.injOn.mono (coe_subset.mpr hP)),
    M.card_targets] at full
  have eqsize := le_antisymm (cap hE) full
  let V := A.sources.filter (fun x => ¬on x)
  have hVP : V ⊆ P := fun _ hx =>
    mem_filter.mpr ⟨off_in_new (mem_filter.mp hx).1 (mem_filter.mp hx).2,(mem_filter.mp hx).2⟩
  have he : P \ V = transportGain A B := by
    ext x
    simp only [P,V,transportGain,mem_sdiff,mem_filter,on]
    tauto
  have hsplit := card_sdiff_add_card_eq_card hVP
  rw [he] at hsplit
  have hold : U.card+V.card=A.sources.card := card_filter_add_card_filter_not (s := A.sources) on
  exact ⟨by omega,fun C hc => (cap hc).trans_eq eqsize.symm⟩

/-- The alternating construction attains the exact gain while retaining the
specified endpoints. Its optimality ranges over every rearrangement of the
same arithmetic edges. -/
theorem optimal_alternating_transport {S : Finset ℕ} (A B : OppositeParityMatching GlobalDyadicOneTwoRel S) :
    ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel S,
      A.sources ⊆ M.sources ∧ B.targets ⊆ M.targets ∧ usesTransportEdges A B M ∧
      M.sources.card = A.sources.card + (transportGain A B).card ∧
      ∀ C : OppositeParityMatching GlobalDyadicOneTwoRel S, usesTransportEdges A B C →
        C.sources.card ≤ M.sources.card := by
  obtain ⟨M,ha,hb,he⟩ := combine_matchings A B
  exact ⟨M,ha,hb,he,exact_gain_of_joint_transport A B M ha hb he⟩

#print axioms optimal_alternating_transport

end GaloisForLFunctions.RestrictedFactorizationCalculus
