import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Abstract differential-matroid gluing engine

The differential transcendence degree over a fixed base field `k`,
`ρ(s) = dtrdeg_k k⟨s⟩`, is a monotone submodular `ℕ`-valued rank on finite subsets of a common
overfield.  Translation by a derivation-commuting automorphism preserves it.  This file abstracts
exactly that structure — a `Rank` together with rank-preserving permutations — and proves the two
combinatorial statements that convert individual atomicity into joint atomicity:

* `Rank.freeBlock` — the **free-block replication lemma**: if the whole base is undisturbed by every
  translate of a set `B` (each `σ^n T` is differentially algebraic over `T`) and `B` admits
  arbitrarily many disjoint independent translates, then `B` is independent *over* the base, i.e.
  the marginal rank of `B` over `T` is the full `B.card`.

The analytic facts that `dtrdeg` is such a rank and that the concrete orbits are independent enter
downstream as hypotheses; nothing here depends on them.
-/

namespace GaloisForLFunctions.MatroidGluing

open Finset

variable {Ω : Type*} [DecidableEq Ω]

/-- A monotone, submodular `ℕ`-valued rank on the finite subsets of `Ω`, subcardinal on every set.
Models the differential transcendence degree `dtrdeg_k k⟨·⟩` over a fixed base field `k`. -/
structure Rank (Ω : Type*) [DecidableEq Ω] where
  /-- The rank of a finite set of coordinates. -/
  ρ : Finset Ω → ℕ
  /-- Rank is monotone under inclusion. -/
  mono : ∀ {s t : Finset Ω}, s ⊆ t → ρ s ≤ ρ t
  /-- Rank is submodular. -/
  submodular : ∀ s t : Finset Ω, ρ (s ∪ t) + ρ (s ∩ t) ≤ ρ s + ρ t
  /-- Rank never exceeds cardinality (unit increments). -/
  ρ_le_card : ∀ s : Finset Ω, ρ s ≤ s.card

namespace Rank

variable (R : Rank Ω)

/-- Adjoining to `t` two sets, each of which leaves the rank of `t` unchanged, still leaves it
unchanged.  This is the two-set core of "the compositum of finitely many DA extensions is DA". -/
theorem neutral_union {t x y : Finset Ω}
    (hx : R.ρ (t ∪ x) = R.ρ t) (hy : R.ρ (t ∪ y) = R.ρ t) :
    R.ρ (t ∪ (x ∪ y)) = R.ρ t := by
  have hsub := R.submodular (t ∪ x) (t ∪ y)
  have hset : (t ∪ x) ∪ (t ∪ y) = t ∪ (x ∪ y) := by
    ext a; simp only [Finset.mem_union]; tauto
  have hle : R.ρ t ≤ R.ρ ((t ∪ x) ∩ (t ∪ y)) :=
    R.mono (Finset.subset_inter Finset.subset_union_left Finset.subset_union_left)
  rw [hset, hx, hy] at hsub
  have hge : R.ρ t ≤ R.ρ (t ∪ (x ∪ y)) :=
    R.mono (by intro a ha; exact Finset.mem_union.mpr (Or.inl ha))
  omega

/-- Adjoining to `t` a finite family of rank-neutral sets leaves the rank of `t` unchanged. -/
theorem neutral_biUnion {ι : Type*} [DecidableEq ι] (t : Finset Ω) {s : Finset ι}
    {X : ι → Finset Ω} (h : ∀ i ∈ s, R.ρ (t ∪ X i) = R.ρ t) :
    R.ρ (t ∪ s.biUnion X) = R.ρ t := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert]
      have hax : R.ρ (t ∪ X a) = R.ρ t := h a (Finset.mem_insert_self a s)
      have hrest : R.ρ (t ∪ s.biUnion X) = R.ρ t :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact R.neutral_union hax hrest

/-- Enlarging the base can only shrink the marginal rank: for `V ⊆ U`,
`ρ(U ∪ A) - ρ U ≤ ρ(V ∪ A) - ρ V`, written additively to avoid `ℕ` subtraction. -/
theorem marginal_base_mono {U V A : Finset Ω} (hVU : V ⊆ U) :
    R.ρ (U ∪ A) + R.ρ V ≤ R.ρ U + R.ρ (V ∪ A) := by
  have hsub := R.submodular U (V ∪ A)
  have hset : U ∪ (V ∪ A) = U ∪ A := by
    rw [← Finset.union_assoc, Finset.union_eq_left.mpr hVU]
  have hVin : V ⊆ U ∩ (V ∪ A) :=
    Finset.subset_inter hVU Finset.subset_union_left
  have hle : R.ρ V ≤ R.ρ (U ∩ (V ∪ A)) := R.mono hVin
  rw [hset] at hsub
  omega

/-- Relative-rank subadditivity: the marginal rank over a base `U` of a finite union of sets is at
most the sum of the individual marginals.  Stated multiplicatively to avoid `ℕ` subtraction. -/
theorem relRank_biUnion_le {ι : Type*} [DecidableEq ι] (U : Finset Ω) (s : Finset ι)
    (A : ι → Finset Ω) :
    R.ρ (U ∪ s.biUnion A) + s.card * R.ρ U ≤ R.ρ U + ∑ i ∈ s, R.ρ (U ∪ A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      -- submodular on (U ∪ A a) and (U ∪ s.biUnion A)
      have hsub := R.submodular (U ∪ A a) (U ∪ s.biUnion A)
      have hset : (U ∪ A a) ∪ (U ∪ s.biUnion A) = U ∪ (A a ∪ s.biUnion A) := by
        ext x; simp only [Finset.mem_union]; tauto
      have hUin : U ⊆ (U ∪ A a) ∩ (U ∪ s.biUnion A) :=
        Finset.subset_inter Finset.subset_union_left Finset.subset_union_left
      have hle : R.ρ U ≤ R.ρ ((U ∪ A a) ∩ (U ∪ s.biUnion A)) := R.mono hUin
      rw [hset] at hsub
      have hexp : (s.card + 1) * R.ρ U = s.card * R.ρ U + R.ρ U := by ring
      omega

/-- The rank automorphisms: permutations of `Ω` that preserve `R.ρ` on every finite set.  These form
a subgroup, so every integer power of a rank automorphism is again one. -/
def rankAutSubgroup : Subgroup (Equiv.Perm Ω) where
  carrier := {e | ∀ s : Finset Ω, R.ρ (s.image ⇑e) = R.ρ s}
  one_mem' := by intro s; simp
  mul_mem' := by
    intro a b ha hb s
    have h1 : s.image ⇑(a * b) = (s.image ⇑b).image ⇑a := by
      rw [Equiv.Perm.coe_mul, ← Finset.image_image]
    rw [h1, ha (s.image ⇑b), hb s]
  inv_mem' := by
    intro a ha s
    have h := ha (s.image ⇑a⁻¹)
    rw [Finset.image_image] at h
    have hid : (⇑a ∘ ⇑a⁻¹) = (id : Ω → Ω) := by
      funext x; simp
    rw [hid, Finset.image_id] at h
    exact h.symm

/-- Every rank automorphism preserves the rank on every finite set. -/
theorem ρ_image_of_mem {e : Equiv.Perm Ω} (he : e ∈ R.rankAutSubgroup) (s : Finset Ω) :
    R.ρ (s.image ⇑e) = R.ρ s := he s

/-- Integer powers of a rank automorphism are rank automorphisms. -/
theorem ρ_image_zpow {σ : Equiv.Perm Ω} (hσ : σ ∈ R.rankAutSubgroup) (n : ℤ) (s : Finset Ω) :
    R.ρ (s.image ⇑(σ ^ n)) = R.ρ s :=
  (R.rankAutSubgroup.zpow_mem hσ n) s

/-- The image of a union under an equivalence commutes with the rank via the automorphism law. -/
theorem ρ_image_union_zpow {σ : Equiv.Perm Ω} (hσ : σ ∈ R.rankAutSubgroup) (n : ℤ)
    (s t : Finset Ω) :
    R.ρ ((s ∪ t).image ⇑(σ ^ n)) = R.ρ (s ∪ t) :=
  R.ρ_image_zpow hσ n (s ∪ t)

/-!
## Free-block replication lemma

Let `T` be a finite base of rank `d`, and `σ` a rank automorphism such that every translate
`σ^n T` is differentially algebraic over `T` (adjoining it does not raise the rank of `T`).
If for every `M` the set `B` has `M` pairwise-disjoint translates whose union has rank `M·|B|`
(automatic when the translates lie in a single independent orbit), then the marginal rank of `B`
over `T` is exactly `|B|`: `B` is independent over `T`.
-/

/-- The marginal rank of any set over `T` is at most its cardinality. -/
theorem marginal_le_card (T B : Finset Ω) : R.ρ (T ∪ B) ≤ R.ρ T + B.card := by
  have hsub := R.submodular T B
  have hB : R.ρ B ≤ B.card := R.ρ_le_card B
  omega

/-- **Free-block replication lemma.**  Under the disjoint-independent-translate hypothesis and
base-stationarity `hDA`, the base rank increases by the full `B.card` when `B` is adjoined. -/
theorem freeBlock {T B : Finset Ω} {σ : Equiv.Perm Ω} (hσ : σ ∈ R.rankAutSubgroup)
    (hDA : ∀ n : ℤ, R.ρ (T ∪ (T.image ⇑(σ ^ n))) = R.ρ T)
    (hFree : ∀ M : ℕ, ∃ N : Fin M → ℤ,
      R.ρ ((univ : Finset (Fin M)).biUnion (fun j => B.image ⇑(σ ^ (N j)))) = M * B.card) :
    R.ρ (T ∪ B) = R.ρ T + B.card := by
  set d := R.ρ T with hd
  set s := B.card with hscard
  -- Upper bound is automatic.
  refine le_antisymm (R.marginal_le_card T B) ?_
  -- Lower bound: rule out a strict deficiency by the pigeonhole on `M = d + 1`.
  by_contra hlt
  rw [not_le] at hlt
  -- `hlt : R.ρ (T ∪ B) < d + s`.
  -- If `s = 0` then `B = ∅`, so `R.ρ (T ∪ B) = d`, contradicting `hlt`.
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · have hBempty : B = ∅ := Finset.card_eq_zero.mp (by rw [← hscard]; exact hs0)
    rw [hBempty, Finset.union_empty] at hlt
    omega
  -- Take `M = d + 1` disjoint independent translates.
  set M := d + 1 with hM
  obtain ⟨N, hN⟩ := hFree M
  set A : Fin M → Finset Ω := fun j => B.image ⇑(σ ^ (N j)) with hA
  -- Base together with all translated bases: still rank `d`.
  set U : Finset Ω := T ∪ (univ : Finset (Fin M)).biUnion (fun j => T.image ⇑(σ ^ (N j))) with hU
  have hρU : R.ρ U = d := by
    rw [hU]
    exact R.neutral_biUnion T (fun j _ => hDA (N j))
  -- Each translated block has marginal at most `s - 1` over `U`.
  have hblock : ∀ j : Fin M, R.ρ (U ∪ A j) ≤ d + (s - 1) := by
    intro j
    -- base-monotonicity with `V = T.image (σ^(N j)) ⊆ U`
    have hVU : (T.image ⇑(σ ^ (N j))) ⊆ U := by
      rw [hU]
      refine Finset.Subset.trans ?_ Finset.subset_union_right
      exact Finset.subset_biUnion_of_mem (fun j => T.image ⇑(σ ^ (N j))) (Finset.mem_univ j)
    have hmm := R.marginal_base_mono (U := U) (V := T.image ⇑(σ ^ (N j))) (A := A j) hVU
    -- ρ V = d
    have hρV : R.ρ (T.image ⇑(σ ^ (N j))) = d := by rw [hd]; exact R.ρ_image_zpow hσ (N j) T
    -- V ∪ A j = (T ∪ B).image (σ^(N j)); its rank is ρ (T ∪ B)
    have hVA : (T.image ⇑(σ ^ (N j))) ∪ A j = (T ∪ B).image ⇑(σ ^ (N j)) := by
      rw [hA, Finset.image_union]
    have hρVA : R.ρ ((T.image ⇑(σ ^ (N j))) ∪ A j) = R.ρ (T ∪ B) := by
      rw [hVA]; exact R.ρ_image_zpow hσ (N j) (T ∪ B)
    -- combine
    rw [hρV, hρVA] at hmm
    -- hmm : ρ(U ∪ A j) + d ≤ ρ U + ρ(T ∪ B) = d + ρ(T ∪ B)
    rw [hρU] at hmm
    have hTBle : R.ρ (T ∪ B) ≤ d + (s - 1) := by omega
    omega
  -- Relative-rank subadditivity over `U`.
  have hsubadd := R.relRank_biUnion_le U (univ : Finset (Fin M)) A
  have hcard : (univ : Finset (Fin M)).card = M := by simp
  rw [hcard, hρU] at hsubadd
  -- Sum of blocks ≤ M * (d + (s-1))
  have hsumle : ∑ j ∈ (univ : Finset (Fin M)), R.ρ (U ∪ A j) ≤ M * (d + (s - 1)) := by
    calc ∑ j ∈ (univ : Finset (Fin M)), R.ρ (U ∪ A j)
        ≤ ∑ _j ∈ (univ : Finset (Fin M)), (d + (s - 1)) :=
          Finset.sum_le_sum (fun j _ => hblock j)
      _ = M * (d + (s - 1)) := by rw [Finset.sum_const, hcard]; ring
  -- Lower bound on the big union rank from `hN`, transported to base `U`.
  have hbig : R.ρ ((univ : Finset (Fin M)).biUnion A) = M * s := hN
  have hbigle :
      R.ρ ((univ : Finset (Fin M)).biUnion A)
        ≤ R.ρ (U ∪ (univ : Finset (Fin M)).biUnion A) :=
    R.mono Finset.subset_union_right
  -- Distribute so `omega` can chain the products as atoms.
  have hdist : M * (d + (s - 1)) = M * d + M * (s - 1) := by ring
  have hss : M * s = M * (s - 1) + M := by
    have hsucc : (s - 1) + 1 = s := by omega
    calc M * s = M * ((s - 1) + 1) := by rw [hsucc]
      _ = M * (s - 1) + M := by ring
  -- Chain: M*s = ρ(big) ≤ ρ(U ∪ big) ≤ d + Σ ≤ d + M*(d+(s-1)); cancel to get M ≤ d.
  have hMd : M ≤ d := by
    rw [hbig] at hbigle
    omega
  rw [hM] at hMd
  omega

/-!
## Star independence

The first gluing step.  A finite family of orbits, each free and independent along its own
direction `τ e`, whose direction is rank-neutral on every *other* orbit of the family
(`CrossNeutral`), has an independent union.  This is exactly the vertex-star case of the graph
gluing theorem: for the star at `q`, the far endpoint direction of each incident edge does not move
any other incident edge, so cross-neutrality holds.
-/

/-- A set of coordinates is independent when every finite subset has rank equal to its cardinality. -/
def IndepSet (S : Set Ω) : Prop := ∀ t : Finset Ω, (↑t : Set Ω) ⊆ S → R.ρ t = t.card

/-- The empty set is independent. -/
theorem indepSet_empty : R.IndepSet (∅ : Set Ω) := by
  intro t ht
  have : t = ∅ := by
    rw [← Finset.coe_eq_empty]; exact Set.subset_empty_iff.mp ht
  subst this
  simpa using Nat.le_zero.mp (R.ρ_le_card ∅)

/-- A free independent orbit for the direction `σ`: `σ` is a rank automorphism, and any finite block
inside the orbit has, for every `M`, an `M`-fold disjoint independent family of `σ`-translates
(union rank `M · |B|`).  This is the rank shadow of a free, differentially independent one-direction
orbit. -/
structure FreeIndepOrbit (σ : Equiv.Perm Ω) (O : Set Ω) : Prop where
  /-- `σ` preserves the rank. -/
  aut : σ ∈ R.rankAutSubgroup
  /-- Arbitrarily many disjoint independent `σ`-translates of any finite block of the orbit. -/
  free : ∀ B : Finset Ω, (↑B : Set Ω) ⊆ O → ∀ M : ℕ, ∃ N : Fin M → ℤ,
      R.ρ ((univ : Finset (Fin M)).biUnion (fun j => B.image ⇑(σ ^ (N j)))) = M * B.card

/-- `σ` is rank-neutral on `S`: adjoining any `σ`-translate of a finite subset of `S` never raises
its rank.  This is the rank shadow of "`σ^n(Y) − Y` is differentially algebraic" for coordinates
`Y` lying in orbits that `σ` does not move. -/
def CrossNeutral (σ : Equiv.Perm Ω) (S : Set Ω) : Prop :=
  ∀ t : Finset Ω, (↑t : Set Ω) ⊆ S → ∀ n : ℤ, R.ρ (t ∪ t.image ⇑(σ ^ n)) = R.ρ t

theorem crossNeutral_mono {σ : Equiv.Perm Ω} {S S' : Set Ω} (h : R.CrossNeutral σ S)
    (hS : S' ⊆ S) : R.CrossNeutral σ S' :=
  fun t ht n => h t (subset_trans ht hS) n

/-- `σ` produces, for every finite block of `S` and every `M`, an `M`-fold family of pairwise
disjoint `σ`-translates that stay inside `S`.  Geometric freeness of the direction on `S`. -/
def HasFreeTranslates (σ : Equiv.Perm Ω) (S : Set Ω) : Prop :=
  ∀ B : Finset Ω, (↑B : Set Ω) ⊆ S → ∀ M : ℕ, ∃ N : Fin M → ℤ,
    (∀ i j : Fin M, i ≠ j → Disjoint (B.image ⇑(σ ^ (N i))) (B.image ⇑(σ ^ (N j)))) ∧
    (∀ j : Fin M, (↑(B.image ⇑(σ ^ (N j))) : Set Ω) ⊆ S)

/-- Star independence feeds the free-block interface: an independent set on which `σ` acts with free
translates is a free independent orbit for `σ`.  This is the bridge from the first gluing step
(`crossNeutral_iUnion_indep`) to the free-block hypothesis of the second step. -/
theorem freeIndepOrbit_of_indep {σ : Equiv.Perm Ω} {S : Set Ω} (haut : σ ∈ R.rankAutSubgroup)
    (hindep : R.IndepSet S) (hfree : HasFreeTranslates σ S) : R.FreeIndepOrbit σ S := by
  refine ⟨haut, ?_⟩
  intro B hB M
  obtain ⟨N, hdisj, hsub⟩ := hfree B hB M
  refine ⟨N, ?_⟩
  have hunionsub :
      (↑((univ : Finset (Fin M)).biUnion (fun j => B.image ⇑(σ ^ (N j)))) : Set Ω) ⊆ S := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_biUnion] at hx
    obtain ⟨j, _, hxj⟩ := hx
    exact hsub j (Finset.mem_coe.mpr hxj)
  rw [hindep _ hunionsub,
    Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
  have hcard : ∀ j : Fin M, (B.image ⇑(σ ^ (N j))).card = B.card :=
    fun j => Finset.card_image_of_injective B (σ ^ (N j)).injective
  rw [Finset.sum_congr rfl (fun j _ => hcard j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Star independence.**  If each orbit in a finite family is a free independent orbit along its
own direction, and each direction is rank-neutral on the union of the other orbits, then the whole
union of orbits is independent. -/
theorem crossNeutral_iUnion_indep {ι : Type*} [DecidableEq ι] (O : ι → Set Ω)
    (τ : ι → Equiv.Perm Ω) (s : Finset ι)
    (hOrbit : ∀ e ∈ s, R.FreeIndepOrbit (τ e) (O e))
    (hCross : ∀ e ∈ s, R.CrossNeutral (τ e) (⋃ e' ∈ s.erase e, O e')) :
    R.IndepSet (⋃ e ∈ s, O e) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using R.indepSet_empty
  | @insert a s' ha ih =>
      -- Restrict the hypotheses to `s'` for the induction hypothesis.
      have hOrbit' : ∀ e ∈ s', R.FreeIndepOrbit (τ e) (O e) :=
        fun e he => hOrbit e (Finset.mem_insert_of_mem he)
      have hCross' : ∀ e ∈ s', R.CrossNeutral (τ e) (⋃ e' ∈ s'.erase e, O e') := by
        intro e he
        have hsub : (⋃ e' ∈ s'.erase e, O e') ⊆ (⋃ e' ∈ (insert a s').erase e, O e') := by
          apply Set.biUnion_subset_biUnion_left
          exact Finset.erase_subset_erase _ (Finset.subset_insert a s')
        exact R.crossNeutral_mono (hCross e (Finset.mem_insert_of_mem he)) hsub
      have IHindep : R.IndepSet (⋃ e ∈ s', O e) := ih hOrbit' hCross'
      -- The direction `τ a` is rank-neutral on the union over `s'`.
      have hCrossA : R.CrossNeutral (τ a) (⋃ e' ∈ s', O e') := by
        have := hCross a (Finset.mem_insert_self a s')
        rwa [Finset.erase_insert ha] at this
      have hOrbitA : R.FreeIndepOrbit (τ a) (O a) := hOrbit a (Finset.mem_insert_self a s')
      -- Prove independence of the enlarged union.
      intro F hF
      -- Split `F` by membership in `O a`.
      set Fa : Finset Ω := F.filter (fun x => x ∈ O a) with hFa
      set Fs : Finset Ω := F.filter (fun x => x ∉ O a) with hFs
      have hFaO : (↑Fa : Set Ω) ⊆ O a := by
        intro x hx
        rw [Finset.mem_coe, hFa, Finset.mem_filter] at hx
        exact hx.2
      have hFsU : (↑Fs : Set Ω) ⊆ ⋃ e ∈ s', O e := by
        intro x hx
        rw [Finset.mem_coe, hFs, Finset.mem_filter] at hx
        have hxF : x ∈ (⋃ e ∈ insert a s', O e) := hF hx.1
        rw [Set.mem_iUnion₂] at hxF
        obtain ⟨e, he, hxe⟩ := hxF
        rw [Finset.mem_insert] at he
        rcases he with rfl | he'
        · exact absurd hxe hx.2
        · rw [Set.mem_iUnion₂]; exact ⟨e, he', hxe⟩
      -- `F = Fs ∪ Fa`, disjointly.
      have hunion : Fs ∪ Fa = F := by
        rw [hFs, hFa]; ext x
        simp only [Finset.mem_union, Finset.mem_filter]
        tauto
      have hdisj : Disjoint Fs Fa := by
        rw [hFs, hFa, Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_filter] at hx hx'
        exact hx.2 hx'.2
      have hcardF : F.card = Fs.card + Fa.card := by
        rw [← hunion]; exact Finset.card_union_of_disjoint hdisj
      -- Independence of `Fs` from the induction hypothesis.
      have hρFs : R.ρ Fs = Fs.card := IHindep Fs hFsU
      -- Free-block replication adjoining `Fa` over `Fs`.
      have hDA : ∀ n : ℤ, R.ρ (Fs ∪ Fs.image ⇑((τ a) ^ n)) = R.ρ Fs :=
        fun n => hCrossA Fs hFsU n
      have hFree : ∀ M : ℕ, ∃ N : Fin M → ℤ,
          R.ρ ((univ : Finset (Fin M)).biUnion (fun j => Fa.image ⇑((τ a) ^ (N j))))
            = M * Fa.card := hOrbitA.free Fa hFaO
      have hblock := R.freeBlock hOrbitA.aut hDA hFree
      -- Assemble.
      calc R.ρ F = R.ρ (Fs ∪ Fa) := by rw [hunion]
        _ = R.ρ Fs + Fa.card := hblock
        _ = Fs.card + Fa.card := by rw [hρFs]
        _ = F.card := hcardF.symm

/-!
## Graph orbit-gluing

The second gluing step.  The incidence structure is abstracted to a predicate `inc : V → ι → Prop`
(`inc q e` means vertex `q` is an endpoint of edge `e`).  For each vertex `q` the *star*
`⋃ {O e | inc q e}` is a free independent orbit along the direction `σ q`, and `σ q` is rank-neutral
on the complementary union `⋃ {O e | ¬ inc q e}` (a coordinate outside the star lies in an orbit
that `σ q` does not move).  Then the whole union of edge orbits is independent — no hidden nonlinear
relation crosses a star.

The `FreeIndepOrbit (σ q) (star q)` hypothesis is discharged in a concrete instance from star
independence (`crossNeutral_iUnion_indep`, the first gluing step) together with geometric freeness
of `σ q` on the star (`freeIndepOrbit_of_indep`).

Because the incidence is an abstract predicate `inc : V → ι → Prop`, the theorem is independent of
edge arity: it applies verbatim to graphs (two-element faces), to `s`-uniform hypergraphs (the
uniform simplicial-star gluing of the all-order hierarchy), and to faces carrying an extra label
(the compatible pair-faces of the all-depth matroid).  Only the discharge of `FreeIndepOrbit` on the
star changes with arity — a nested-star recursion in the hypergraph case.
-/

/-- **Graph orbit-gluing theorem.**  Under star-freeness and off-star rank-neutrality for every
vertex, the union of all edge orbits is independent.  Proved by the minimal-circuit argument: a
minimal dependent finite set is split at a star, and the free-block replication lemma with the star
direction `σ q` contradicts the dependence. -/
theorem graphGluing {V ι : Type*} [DecidableEq ι] (edges : Finset ι) (O : ι → Set Ω)
    (σ : V → Equiv.Perm Ω) (inc : V → ι → Prop) [∀ q, DecidablePred (inc q)]
    (hCover : ∀ e ∈ edges, ∃ q : V, inc q e)
    (hStar : ∀ q : V, R.FreeIndepOrbit (σ q) (⋃ e ∈ edges.filter (inc q), O e))
    (hOff : ∀ q : V, R.CrossNeutral (σ q) (⋃ e ∈ edges.filter (fun e => ¬ inc q e), O e)) :
    R.IndepSet (⋃ e ∈ edges, O e) := by
  classical
  intro F
  induction F using Finset.strongInduction with
  | _ F ih =>
    intro hF
    by_contra hne
    have hlt : R.ρ F < F.card := lt_of_le_of_ne (R.ρ_le_card F) hne
    have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxF⟩ := hFne
    -- `x` lies in some edge orbit; pick an incident vertex `q`.
    have hxU : x ∈ (⋃ e ∈ edges, O e) := hF (Finset.mem_coe.mpr hxF)
    rw [Set.mem_iUnion₂] at hxU
    obtain ⟨e, heE, hxe⟩ := hxU
    obtain ⟨q, hq⟩ := hCover e heE
    -- `x` lies in the star at `q`.
    have hxStar : x ∈ (⋃ e ∈ edges.filter (inc q), O e) := by
      rw [Set.mem_iUnion₂]; exact ⟨e, Finset.mem_filter.mpr ⟨heE, hq⟩, hxe⟩
    -- Split `F` at the star.
    set B : Finset Ω := F.filter (fun y => y ∈ (⋃ e ∈ edges.filter (inc q), O e)) with hB
    set C0 : Finset Ω := F.filter (fun y => y ∉ (⋃ e ∈ edges.filter (inc q), O e)) with hC0
    have hxB : x ∈ B := by rw [hB, Finset.mem_filter]; exact ⟨hxF, hxStar⟩
    have hC0sub : C0 ⊆ F := by rw [hC0]; exact Finset.filter_subset _ _
    have hC0ssub : C0 ⊂ F :=
      (Finset.ssubset_iff_of_subset hC0sub).mpr
        ⟨x, hxF, fun hc => (Finset.mem_filter.mp hc).2 hxStar⟩
    have hunion : C0 ∪ B = F := by
      rw [hC0, hB]; ext y; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint C0 B := by
      rw [hC0, hB, Finset.disjoint_left]; intro y hy hy'
      simp only [Finset.mem_filter] at hy hy'; exact hy.2 hy'.2
    have hcardF : F.card = C0.card + B.card := by
      rw [← hunion]; exact Finset.card_union_of_disjoint hdisj
    -- `C0` lies in the off-star union.
    have hC0Off : (↑C0 : Set Ω) ⊆ ⋃ e ∈ edges.filter (fun e => ¬ inc q e), O e := by
      intro y hy
      rw [Finset.mem_coe, hC0, Finset.mem_filter] at hy
      obtain ⟨hyF, hyStar⟩ := hy
      have hyU : y ∈ (⋃ e ∈ edges, O e) := hF (Finset.mem_coe.mpr hyF)
      rw [Set.mem_iUnion₂] at hyU
      obtain ⟨e', he'E, hye'⟩ := hyU
      rw [Set.mem_iUnion₂]
      refine ⟨e', Finset.mem_filter.mpr ⟨he'E, ?_⟩, hye'⟩
      intro hinc
      exact hyStar (by rw [Set.mem_iUnion₂]; exact ⟨e', Finset.mem_filter.mpr ⟨he'E, hinc⟩, hye'⟩)
    -- `C0 ⊆ ⋃ edges O` for the induction hypothesis.
    have hC0U : (↑C0 : Set Ω) ⊆ ⋃ e ∈ edges, O e := by
      intro y hy
      rw [Finset.mem_coe, hC0, Finset.mem_filter] at hy
      exact hF (Finset.mem_coe.mpr hy.1)
    have hρC0 : R.ρ C0 = C0.card := ih C0 hC0ssub hC0U
    -- `B` lies in the star.
    have hBStar : (↑B : Set Ω) ⊆ ⋃ e ∈ edges.filter (inc q), O e := by
      intro y hy; rw [Finset.mem_coe, hB, Finset.mem_filter] at hy; exact hy.2
    -- Free-block replication with the star direction `σ q`.
    have hDA : ∀ n : ℤ, R.ρ (C0 ∪ C0.image ⇑((σ q) ^ n)) = R.ρ C0 :=
      fun n => hOff q C0 hC0Off n
    have hFree := (hStar q).free B hBStar
    have hblock := R.freeBlock (hStar q).aut hDA hFree
    -- `ρ F = F.card`, contradicting the deficiency.
    have hEq : R.ρ F = F.card :=
      calc R.ρ F = R.ρ (C0 ∪ B) := by rw [hunion]
        _ = R.ρ C0 + B.card := hblock
        _ = C0.card + B.card := by rw [hρC0]
        _ = F.card := hcardF.symm
    omega

/-- Graph gluing from the concrete star data: a rank automorphism, independence of each star,
and freely separated translates.  These three hypotheses construct the `FreeIndepOrbit` input of
`graphGluing`; callers need not package that intermediate structure themselves. -/
theorem graphGluing_of_indep_hasFreeTranslates
    {V iota : Type*} [DecidableEq iota]
    (edges : Finset iota) (O : iota → Set Ω)
    (sigma : V → Equiv.Perm Ω) (inc : V → iota → Prop)
    [∀ q, DecidablePred (inc q)]
    (hCover : ∀ e ∈ edges, ∃ q : V, inc q e)
    (hStarAut : ∀ q : V, sigma q ∈ R.rankAutSubgroup)
    (hStarIndep : ∀ q : V, R.IndepSet (⋃ e ∈ edges.filter (inc q), O e))
    (hStarFree : ∀ q : V,
      Rank.HasFreeTranslates (sigma q) (⋃ e ∈ edges.filter (inc q), O e))
    (hOff : ∀ q : V,
      R.CrossNeutral (sigma q) (⋃ e ∈ edges.filter (fun e => ¬ inc q e), O e)) :
    R.IndepSet (⋃ e ∈ edges, O e) := by
  apply R.graphGluing edges O sigma inc hCover
  · intro q
    exact R.freeIndepOrbit_of_indep (hStarAut q) (hStarIndep q) (hStarFree q)
  · exact hOff

/-!
## Uniform hypergraph nested-star gluing

For an `s`-uniform face family, the star of a fixed vertex set `A` is the union of the face
orbits whose faces contain `A`.  Descending on the number of unfixed vertices reduces independence
of `Star(A)` to independence of the one-vertex-larger stars `Star(A ∪ {q})`.  The existing graph
gluing theorem performs each reduction: its vertices are the choices `q ∉ A`, its incident star is
`Star(A ∪ {q})`, and its off-star is the union of faces avoiding `q`.

This is the arity-independent nested-star recursion needed for the all-order multiple-elliptic-
gamma face filtration.  The analytic application still has to discharge the two exact rank
interfaces below: free translates on each enlarged star and rank-neutrality on its complement.
-/

/-- The union of the face orbits whose faces contain the fixed vertex set `A`. -/
def faceStar {V : Type*} [DecidableEq V] (faces : Finset (Finset V))
    (O : Finset V → Set Ω) (A : Finset V) : Set Ω :=
  ⋃ J ∈ faces.filter (fun J => A ⊆ J), O J

/-- Independence passes to a smaller coordinate set. -/
theorem indepSet_mono {S S' : Set Ω} (h : R.IndepSet S)
    (hsub : S' ⊆ S) : R.IndepSet S' := by
  intro t ht
  exact h t (ht.trans hsub)

/-- **Uniform hypergraph orbit gluing by descending nested stars.**

Every atomic `s`-face orbit is independent.  If every structural direction preserves rank,
admits arbitrarily many disjoint translates on each enlarged star, and is rank-neutral on the
faces of the current star which avoid that direction, then the union of all face orbits is
independent.  No bound on `s` is imposed. -/
theorem uniformFace_nestedStar_indep {V : Type*} [DecidableEq V]
    (faces : Finset (Finset V)) (O : Finset V → Set Ω)
    (σ : V → Equiv.Perm Ω) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hAtomic : ∀ J ∈ faces, R.IndepSet (O J))
    (hAut : ∀ q, σ q ∈ R.rankAutSubgroup)
    (hFree : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      R.HasFreeTranslates (σ q) (faceStar faces O (insert q A)))
    (hOff : ∀ (A : Finset V) (q : V), A.card < s → q ∉ A →
      R.CrossNeutral (σ q)
        (⋃ J ∈ (faces.filter (fun J => A ⊆ J)).filter (fun J => q ∉ J), O J)) :
    R.IndepSet (faceStar faces O ∅) := by
  classical
  have hstar (A : Finset V) : R.IndepSet (faceStar faces O A) := by
    generalize hd : s - A.card = d
    induction d using Nat.strong_induction_on generalizing A with
    | h d ih =>
      by_cases hge : s ≤ A.card
      · by_cases hA : A ∈ faces
        · apply indepSet_mono (hAtomic A hA)
          intro x hx
          rw [faceStar, Set.mem_iUnion₂] at hx
          obtain ⟨J, hJ, hxJ⟩ := hx
          have hJ' := Finset.mem_filter.mp hJ
          have hAJ : A ⊆ J := hJ'.2
          have hEq : A = J := Finset.eq_of_subset_of_card_le hAJ (by
            rw [huniform J hJ'.1]
            exact hge)
          simpa [← hEq] using hxJ
        · have hempty : faceStar faces O A = ∅ := by
            apply Set.eq_empty_iff_forall_not_mem.mpr
            intro x hx
            rw [faceStar, Set.mem_iUnion₂] at hx
            obtain ⟨J, hJ, _⟩ := hx
            have hJ' := Finset.mem_filter.mp hJ
            have hAJ : A ⊆ J := hJ'.2
            have hEq : A = J := Finset.eq_of_subset_of_card_le hAJ (by
              rw [huniform J hJ'.1]
              exact hge)
            exact hA (by simpa [hEq] using hJ'.1)
          simpa [hempty] using R.indepSet_empty
      · have hlt : A.card < s := Nat.lt_of_not_ge hge
        let vertices := {q : V // q ∉ A}
        let edges := faces.filter (fun J => A ⊆ J)
        let σ' : vertices → Equiv.Perm Ω := fun q => σ q.1
        let inc : vertices → Finset V → Prop := fun q J => q.1 ∈ J
        change R.IndepSet (⋃ J ∈ edges, O J)
        apply R.graphGluing_of_indep_hasFreeTranslates edges O σ' inc
        · intro J hJ
          have hJ' := Finset.mem_filter.mp hJ
          have hcard : A.card < J.card := by
            rw [huniform J hJ'.1]
            exact hlt
          have hproper : A ⊂ J := (Finset.ssubset_iff_subset_ne).mpr ⟨hJ'.2, by
            intro hEq
            subst J
            omega⟩
          obtain ⟨q, hqJ, hqA⟩ := Finset.exists_of_ssubset hproper
          exact ⟨⟨q, hqA⟩, hqJ⟩
        · intro q
          exact hAut q.1
        · intro q
          have hmeasure : s - (insert q.1 A).card < d := by
            rw [Finset.card_insert_of_not_mem q.2, ← hd]
            omega
          have hrec := ih (s - (insert q.1 A).card) hmeasure (insert q.1 A) rfl
          simpa [faceStar, edges, inc, Finset.insert_subset_iff,
            and_left_comm, and_comm, and_assoc] using hrec
        · intro q
          simpa [faceStar, edges, inc, Finset.insert_subset_iff,
            and_left_comm, and_comm, and_assoc] using hFree A q.1 hlt q.2
        · intro q
          simpa [edges, inc] using hOff A q.1 hlt q.2
  simpa [faceStar] using hstar (∅ : Finset V)

end Rank

/-!
## Order-three bottom-face joint atomicity

The order-three multiple-elliptic-gamma bottom faces occupy the complete graph on the four
structural directions `Fin 4`: one face `O (i,j)` for each pair `i < j`.  Specializing the graph
orbit-gluing theorem to this complete graph gives joint independence of all six bottom-face orbits,
with the analytic content supplied through the two rank interfaces (`FreeIndepOrbit`, `CrossNeutral`)
per structural direction.
-/

/-- The six order-three bottom-face orbits (complete graph on `Fin 4`) are jointly independent,
given that each structural direction is free and independent on its star and rank-neutral off it. -/
theorem Rank.orderThree_sixFace_indep {Ω : Type*} [DecidableEq Ω] (R : Rank Ω)
    (O : Fin 4 × Fin 4 → Set Ω) (σ : Fin 4 → Equiv.Perm Ω)
    (hStar : ∀ q : Fin 4, R.FreeIndepOrbit (σ q)
      (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
        (fun p => q = p.1 ∨ q = p.2), O e))
    (hOff : ∀ q : Fin 4, R.CrossNeutral (σ q)
      (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
        (fun p => ¬ (q = p.1 ∨ q = p.2)), O e)) :
    R.IndepSet (⋃ e ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2), O e) := by
  refine R.graphGluing _ O σ (fun q p => q = p.1 ∨ q = p.2) ?_ hStar hOff
  intro e _
  exact ⟨e.1, Or.inl rfl⟩

end GaloisForLFunctions.MatroidGluing
