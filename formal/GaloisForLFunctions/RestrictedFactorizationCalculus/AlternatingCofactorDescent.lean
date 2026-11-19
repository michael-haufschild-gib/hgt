import GaloisForLFunctions.RestrictedFactorizationCalculus.TransportAcrossOrderedFibres

/-!
# Combining cofactor transports by descending alternating paths

An old edge goes from a positive integer to a negative integer. Follow it by
the inverse of a new edge. A path starting outside the new positive sources
can switch to old edges throughout, with every new negative target preserved.
When the two matchings contract the two largest primes in opposite parity
classes, each two-edge step removes exactly two prime factors.
-/

noncomputable section

open Finset
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev Matching (S : Finset ℕ) := OppositeParityMatching GlobalDyadicOneTwoRel S

/-- Two injective endpoint maps on one index set determine a disjoint matching. -/
theorem matching_of_indexed_edges {ι : Type*} [Fintype ι] {S : Finset ℕ} (f g : ι → ℕ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ i, f i ∈ posParity S ∧ g i ∈ negParity S ∧ GlobalDyadicOneTwoRel (f i) (g i)) :
    ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel S,
      M.sources = univ.image f ∧ M.targets = univ.image g := by
  let partner := fun x => if hx : ∃ i, f i = x then g hx.choose else 0
  have he (i : ι) : partner (f i) = g i := by
    have hx : ∃ j, f j = f i := ⟨i,rfl⟩
    change (if h : ∃ j, f j = f i then g h.choose else 0) = g i
    rw [dif_pos hx]
    exact congrArg g (hf hx.choose_spec)
  let M : OppositeParityMatching GlobalDyadicOneTwoRel S := {
    sources := univ.image f
    partner := partner
    sources_subset := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact (h i).1
    injOn := by
      intro x hx y hy hxy
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hy
      rw [he,he] at hxy
      exact congrArg f (hg hxy)
    partner_mem := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      rw [he]; exact (h i).2.1
    adj := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      rw [he]; exact (h i).2.2 }
  refine ⟨M,rfl,?_⟩
  change (univ.image f).image partner = univ.image g
  rw [image_image]
  exact image_congr (fun i _ => he i)

private def rowEmbedding (P Q : Finset ℕ) (h : P.card ≤ Q.card) : P ↪ Q where
  toFun p := (Q.orderIsoOfFin rfl) ⟨((P.orderIsoOfFin rfl).symm p).val,
    ((P.orderIsoOfFin rfl).symm p).isLt.trans_le h⟩
  inj' := by
    intro p q he
    apply (P.orderIsoOfFin rfl).symm.injective
    exact Fin.ext (congrArg (fun i : Fin Q.card => i.val) ((Q.orderIsoOfFin rfl).injective he))

/-- The element of the target row of the same rank, whenever the source row fits. -/
def rankedSlot (P Q : Finset ℕ) (n : ℕ) : ℕ :=
  if h : P.card ≤ Q.card ∧ n ∈ P then rowEmbedding P Q h.1 ⟨n,h.2⟩ else 0

theorem rankedSlot_mem {P Q : Finset ℕ} {n : ℕ} (h : P.card ≤ Q.card) (hn : n ∈ P) :
    rankedSlot P Q n ∈ Q := by
  rw [rankedSlot,dif_pos ⟨h,hn⟩]
  exact (rowEmbedding P Q h ⟨n,hn⟩).property

theorem rankedSlot_inj {P Q : Finset ℕ} (h : P.card ≤ Q.card) : Set.InjOn (rankedSlot P Q) P := by
  intro m hm n hn he
  have hm' : P.card ≤ Q.card ∧ m ∈ P := ⟨h,hm⟩
  have hn' : P.card ≤ Q.card ∧ n ∈ P := ⟨h,hn⟩
  simp only [rankedSlot,dif_pos hm',dif_pos hn'] at he
  have hrow : rowEmbedding P Q h ⟨m,hm⟩ = rowEmbedding P Q h ⟨n,hn⟩ := Subtype.ext he
  exact congrArg Subtype.val ((rowEmbedding P Q h).injective hrow)

/-- An old edge followed by an inverse new edge, sharing their negative endpoint. -/
def cofactorStep {S : Finset ℕ} (A B : OppositeParityMatching GlobalDyadicOneTwoRel S)
    (x y : ℕ) : Prop :=
  x ∈ A.sources ∧ y ∈ B.sources ∧ A.partner x = B.partner y

/-- Number of pairs of edges traversed between two positive vertices. -/
inductive CofactorWalk {S : Finset ℕ} (A B : OppositeParityMatching GlobalDyadicOneTwoRel S)
    (start : ℕ) : ℕ → ℕ → Prop
  | nil : CofactorWalk A B start 0 start
  | snoc {k x y} : CofactorWalk A B start k x → cofactorStep A B x y →
      CofactorWalk A B start (k+1) y

private theorem steps_unique {S : Finset ℕ} {A B : Matching S} {x y z : ℕ}
    (h : cofactorStep A B x y) (h' : cofactorStep A B x z) : y = z :=
  B.injOn h.2.1 h'.2.1 (h.2.2.symm.trans h'.2.2)

/-- Distinct paths from old-only sources never visit the same positive integer.
Both the source and the number of moves are determined by the endpoint. -/
theorem cofactor_walks_do_not_merge {S : Finset ℕ} {A B : OppositeParityMatching GlobalDyadicOneTwoRel S}
    {a b k l x : ℕ} (ha : a ∉ B.sources) (hb : b ∉ B.sources)
    (h : CofactorWalk A B a k x) (h' : CofactorWalk A B b l x) : a = b ∧ k = l := by
  induction h generalizing l with
  | nil =>
    cases h' with
    | nil => exact ⟨rfl,rfl⟩
    | snoc _ hlast => exact False.elim (ha hlast.2.1)
  | snoc hw he ih =>
    cases h' with
    | nil => exact False.elim (hb he.2.1)
    | snoc hw' he' =>
      have hprev := A.injOn he.1 he'.1 (he.2.2.trans he'.2.2.symm)
      subst_vars
      obtain ⟨ha',hl'⟩ := ih hw'
      exact ⟨ha',congrArg Nat.succ hl'⟩

/-- The positive vertices reached from an old-only source by alternating the two matchings. -/
def switchReachable {S : Finset ℕ} (A B : Matching S) (x : ℕ) : Prop :=
  ∃ a ∈ A.sources, a ∉ B.sources ∧ ∃ k, CofactorWalk A B a k x

/-- One alternating step extends a reached walk. -/
theorem switchReachable_step {S : Finset ℕ} {A B : Matching S} {x y : ℕ}
    (hx : switchReachable A B x) (h : cofactorStep A B x y) : switchReachable A B y := by
  obtain ⟨a,ha,hb,k,hw⟩ := hx
  exact ⟨a,ha,hb,k+1,hw.snoc h⟩

/-- Two matchings have a joint choice of edges retaining the first source set and the second target set. -/
theorem combine_matchings {S : Finset ℕ}
    (A B : OppositeParityMatching GlobalDyadicOneTwoRel S) :
    ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel S, A.sources ⊆ M.sources ∧ B.targets ⊆ M.targets ∧
      ∀ x ∈ M.sources, (x ∈ A.sources ∧ M.partner x = A.partner x) ∨
        (x ∈ B.sources ∧ M.partner x = B.partner x) := by
  classical
  let on := switchReachable A B
  let src := (A.sources.filter on) ∪ (B.sources.filter (fun x => ¬ on x))
  let f := fun x => if on x then A.partner x else B.partner x
  have mem {x : ℕ} : x ∈ src ↔ (x ∈ A.sources ∧ on x) ∨ (x ∈ B.sources ∧ ¬ on x) := by
    simp only [src,mem_union,mem_filter]
  have old {x : ℕ} (hx : x ∈ src) (h : on x) : x ∈ A.sources :=
    (mem.mp hx).elim And.left (fun h' => False.elim (h'.2 h))
  have new {x : ℕ} (hx : x ∈ src) (h : ¬ on x) : x ∈ B.sources :=
    (mem.mp hx).elim (fun h' => False.elim (h h'.2)) And.left
  have distinct {x y : ℕ} (hx : x ∈ src) (hy : y ∈ src) (ha : on x) (hb : ¬ on y) :
      A.partner x ≠ B.partner y := fun he => hb (switchReachable_step ha ⟨old hx ha,new hy hb,he⟩)
  let M : Matching S := {
    sources := src
    partner := f
    sources_subset := fun _ hx => (mem.mp hx).elim (fun h => A.sources_subset h.1)
      (fun h => B.sources_subset h.1)
    injOn := by
      intro x hx y hy he
      by_cases ha : on x <;> by_cases hb : on y <;> simp only [f,ha,hb,if_true,if_false] at he
      · exact A.injOn (old hx ha) (old hy hb) he
      · exact False.elim (distinct hx hy ha hb he)
      · exact False.elim (distinct hy hx hb ha he.symm)
      · exact B.injOn (new hx ha) (new hy hb) he
    partner_mem := by
      intro x hx
      by_cases h : on x
      · simpa only [f,if_pos h] using A.partner_mem x (old hx h)
      · simpa only [f,if_neg h] using B.partner_mem x (new hx h)
    adj := by
      intro x hx
      by_cases h : on x
      · simpa only [f,if_pos h] using A.adj x (old hx h)
      · simpa only [f,if_neg h] using B.adj x (new hx h) }
  refine ⟨M,?_,?_,?_⟩
  · intro x hx
    by_cases h : on x
    · exact mem.mpr (Or.inl ⟨hx,h⟩)
    · exact mem.mpr (Or.inr ⟨by
        by_contra hn
        exact h ⟨x,hx,hn,0,.nil⟩,h⟩)
  · intro n hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    by_cases h : on x
    · obtain ⟨a,ha,hab,k,hw⟩ := h
      cases hw with
      | nil => exact False.elim (hab hx)
      | snoc prev last =>
        have hp := show switchReachable A B _ from ⟨a,ha,hab,_,prev⟩
        exact mem_image.mpr ⟨_,mem.mpr (Or.inl ⟨last.1,hp⟩),by
          change (if on _ then _ else _) = _
          rw [if_pos hp]; exact last.2.2⟩
    · exact mem_image.mpr ⟨x,mem.mpr (Or.inr ⟨hx,h⟩),if_neg h⟩
  · intro x hx
    exact (mem.mp hx).elim (fun h => Or.inl ⟨h.1,if_pos h.2⟩)
      (fun h => Or.inr ⟨h.1,if_neg h.2⟩)

/-- The ordered-fibre graph inside the global one-to-two graph. -/
abbrev OrderedExchange (m n : ℕ) :=
  GlobalDyadicOneTwoRel m n ∧ evenPrefixCofactor m = evenPrefixCofactor n

/-- Read an ordered-fibre matching as a global matching with the same edges. -/
def globalMatching {S : Finset ℕ} (A : OppositeParityMatching OrderedExchange S) :
    OppositeParityMatching GlobalDyadicOneTwoRel S where
  sources := A.sources
  partner := A.partner
  sources_subset := A.sources_subset
  injOn := A.injOn
  partner_mem := A.partner_mem
  adj := fun x h => (A.adj x h).1

/-- An ordered matching drops one prime factor on every positive-to-negative edge. -/
theorem ordered_drop {X x : ℕ} (A : OppositeParityMatching OrderedExchange (Ioc X (2*X)))
    (hx : x ∈ A.sources) : (A.partner x).primeFactors.card + 1 = x.primeFactors.card := by
  have hpos := A.sources_subset hx
  have hneg := A.partner_mem x hx
  have hX : 1 ≤ X := by
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hpos).1
    omega
  let a := evenPrefixCofactor x
  have hA : x ∈ fibrePos X a := mem_filter.mpr ⟨hpos,rfl⟩
  have hB : A.partner x ∈ fibreNeg X a := mem_filter.mpr ⟨hneg,(A.adj x hx).2.symm⟩
  obtain ⟨hc,_,q,r,hq,hr,hqr,he,ht⟩ := mem_fibrePos_structure hX hA
  obtain ⟨_,_,p,hp,he',ht'⟩ := mem_fibreNeg_structure hX hB
  rw [he',card_append_largest hc.ne_zero hp ht',he,card_append_ordered_pair hc.ne_zero hq hr hqr ht]

/-- A ranked cross-fibre matching can be superimposed on any ordered-fibre
matching. Every formerly paired positive and every transported negative is
covered simultaneously. The switching paths are unbranched and a path of
length `k` removes exactly `2k` prime factors. -/
theorem exists_combined_cofactor_descent (X : ℕ) (K : ℕ → ℝ)
    (A : OppositeParityMatching OrderedExchange (Ioc X (2*X))) :
    ∃ B M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
      A.sources ⊆ M.sources ∧ B.targets ⊆ M.targets ∧
      (∀ c ∈ Icc 1 (2*X), μ c = -1 → ∀ w ∈ productRow (K c) X (2*X) c,
        (productRow (K c) X (2*X) c).card ≤ (primeRow X (2*X) c).card → c*w ∈ B.targets) ∧
      (∀ {x y z}, cofactorStep (globalMatching A) B x y →
        cofactorStep (globalMatching A) B x z → y = z) ∧
      (∀ {a k x}, CofactorWalk (globalMatching A) B a k x →
        x.primeFactors.card + 2*k = a.primeFactors.card) ∧
      (∀ x ∈ M.sources, (x ∈ A.sources ∧ M.partner x = A.partner x) ∨
        (x ∈ B.sources ∧ M.partner x = B.partner x)) := by
  obtain ⟨B,hB,hrows⟩ := exists_ranked_transport K X (2*X)
  obtain ⟨M,ha,hb,he⟩ := combine_matchings (globalMatching A) B
  refine ⟨B,M,ha,hb,fun c hc hμ => (hrows c hc hμ).2.2,
    fun {_ _ _} h h' => steps_unique h h',fun {a k x} h => ?_,he⟩
  induction h with
  | nil => simp
  | snoc hw hstep ih =>
    obtain ⟨ha',hb',heq⟩ := hstep
    have hold := ordered_drop A ha'
    have hnew := hB _ hb'
    change A.partner _ = B.partner _ at heq
    rw [heq] at hold
    omega

end GaloisForLFunctions.RestrictedFactorizationCalculus
