import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Spectral causality on finite interaction graphs

This module proves the finite algebraic core of graph-distance spectral causality. A mixed
two-coordinate contrast annihilates every function local on a coordinate set missing either
coordinate. Consequently, a sum of terms local on connected interaction clusters of depth at most
`r` has zero contrast between sites at graph distance greater than `r`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- A function of product configurations is local on `S` when changing coordinates outside
`S` cannot change its value. -/
def CoordinateLocalOn {ι A R : Type*} (S : Set ι) (f : (ι → A) → R) : Prop :=
  ∀ x y, (∀ i, i ∈ S → x i = y i) → f x = f y

/-- The mixed two-coordinate finite difference. -/
def mixedCoordinateContrast {ι A R : Type*} [DecidableEq ι] [AddCommGroup R]
    (x : ι → A) (u v : ι) (a b : A) (f : (ι → A) → R) : R :=
  f (Function.update (Function.update x u a) v b) -
    f (Function.update x u a) -
    f (Function.update x v b) + f x

theorem mixedCoordinateContrast_eq_zero_of_left_not_mem
    {ι A R : Type*} [DecidableEq ι] [AddCommGroup R]
    {S : Set ι} {f : (ι → A) → R} (hf : CoordinateLocalOn S f)
    (x : ι → A) {u v : ι} (hu : u ∉ S) (a b : A) :
    mixedCoordinateContrast x u v a b f = 0 := by
  have hab_b :
      f (Function.update (Function.update x u a) v b) =
        f (Function.update x v b) := by
    apply hf
    intro i hi
    have hiu : i ≠ u := by
      intro hiueq
      exact hu (hiueq ▸ hi)
    by_cases hiv : i = v
    · subst i
      simp
    · simp [Function.update_of_ne hiu, Function.update_of_ne hiv]
  have ha_x : f (Function.update x u a) = f x := by
    apply hf
    intro i hi
    have hiu : i ≠ u := by
      intro hiueq
      exact hu (hiueq ▸ hi)
    exact Function.update_of_ne hiu a x
  rw [mixedCoordinateContrast, hab_b, ha_x]
  abel

theorem mixedCoordinateContrast_eq_zero_of_right_not_mem
    {ι A R : Type*} [DecidableEq ι] [AddCommGroup R]
    {S : Set ι} {f : (ι → A) → R} (hf : CoordinateLocalOn S f)
    (x : ι → A) {u v : ι} (hv : v ∉ S) (a b : A) :
    mixedCoordinateContrast x u v a b f = 0 := by
  have hab_a :
      f (Function.update (Function.update x u a) v b) =
        f (Function.update x u a) := by
    apply hf
    intro i hi
    have hiv : i ≠ v := by
      intro hiveq
      exact hv (hiveq ▸ hi)
    exact Function.update_of_ne hiv b (Function.update x u a)
  have hb_x : f (Function.update x v b) = f x := by
    apply hf
    intro i hi
    have hiv : i ≠ v := by
      intro hiveq
      exact hv (hiveq ▸ hi)
    exact Function.update_of_ne hiv b x
  rw [mixedCoordinateContrast, hab_a, hb_x]
  abel

theorem mixedCoordinateContrast_eq_zero_of_not_both_mem
    {ι A R : Type*} [DecidableEq ι] [AddCommGroup R]
    {S : Set ι} {f : (ι → A) → R} (hf : CoordinateLocalOn S f)
    (x : ι → A) {u v : ι} (hmiss : u ∉ S ∨ v ∉ S) (a b : A) :
    mixedCoordinateContrast x u v a b f = 0 := by
  rcases hmiss with hu | hv
  · exact mixedCoordinateContrast_eq_zero_of_left_not_mem hf x hu a b
  · exact mixedCoordinateContrast_eq_zero_of_right_not_mem hf x hv a b

theorem mixedCoordinateContrast_sum
    {ι A R κ : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset κ) (term : κ → (ι → A) → R)
    (x : ι → A) (u v : ι) (a b : A) :
    mixedCoordinateContrast x u v a b (∑ c ∈ s, term c) =
      ∑ c ∈ s, mixedCoordinateContrast x u v a b (term c) := by
  simp only [mixedCoordinateContrast, Finset.sum_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem mixedCoordinateContrast_sum_eq_zero_of_cluster_local
    {ι A R κ : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset κ) (support : κ → Set ι) (term : κ → (ι → A) → R)
    (hlocal : ∀ c ∈ s, CoordinateLocalOn (support c) (term c))
    (x : ι → A) {u v : ι}
    (hmiss : ∀ c ∈ s, u ∉ support c ∨ v ∉ support c) (a b : A) :
    mixedCoordinateContrast x u v a b (∑ c ∈ s, term c) = 0 := by
  rw [mixedCoordinateContrast_sum]
  apply Finset.sum_eq_zero
  intro c hc
  exact mixedCoordinateContrast_eq_zero_of_not_both_mem
    (hlocal c hc) x (hmiss c hc) a b

/-- A connected interaction cluster containing two sites must use at least their ambient graph
distance in edges. -/
theorem graph_dist_le_connectedCluster_edge_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph)
    (hH : H.Connected) {u v : V} (hu : u ∈ H.verts) (hv : v ∈ H.verts) :
    G.dist u v ≤ Nat.card H.coe.edgeSet := by
  classical
  let uH : H.verts := ⟨u, hu⟩
  let vH : H.verts := ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hH.coe.exists_isPath uH vH
  let q : G.Walk u v := p.map H.hom
  calc
    G.dist u v ≤ q.length := G.dist_le q
    _ = p.length := p.length_map H.hom
    _ ≤ Nat.card H.coe.edgeSet := by
      rw [Nat.card_eq_fintype_card]
      rw [← H.coe.edgeFinset_card]
      exact hp.isTrail.length_le_card_edgeFinset

/-- A cluster with fewer edges than the graph distance cannot contain both sites. -/
theorem connectedCluster_misses_endpoint_of_edge_card_lt_dist
    {V : Type*} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph)
    (hH : H.Connected) {u v : V}
    (hsmall : Nat.card H.coe.edgeSet < G.dist u v) :
    u ∉ H.verts ∨ v ∉ H.verts := by
  classical
  by_cases hu : u ∈ H.verts
  · right
    intro hv
    exact (not_lt_of_ge
      (graph_dist_le_connectedCluster_edge_card G H hH hu hv)) hsmall
  · exact Or.inl hu

/-- **Graph-distance spectral causality.** Every sum of cluster-local terms from connected
clusters with at most `r` edges has zero mixed two-site contrast at sites whose graph distance
exceeds `r`. -/
theorem mixedCoordinateContrast_sum_eq_zero_of_connectedCluster_depth
    {V A R κ : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (G : SimpleGraph V) (s : Finset κ) (cluster : κ → G.Subgraph)
    (term : κ → (V → A) → R)
    (hconnected : ∀ c ∈ s, (cluster c).Connected)
    (hlocal : ∀ c ∈ s, CoordinateLocalOn (cluster c).verts (term c))
    {r : ℕ} (hdepth : ∀ c ∈ s, Nat.card (cluster c).coe.edgeSet ≤ r)
    (x : V → A) {u v : V} (hdist : r < G.dist u v) (a b : A) :
    mixedCoordinateContrast x u v a b (∑ c ∈ s, term c) = 0 := by
  classical
  apply mixedCoordinateContrast_sum_eq_zero_of_cluster_local
    s (fun c => (cluster c).verts) term hlocal x
  intro c hc
  apply connectedCluster_misses_endpoint_of_edge_card_lt_dist G (cluster c)
    (hconnected c hc)
  exact (hdepth c hc).trans_lt hdist

/-- Index of a standard two-factor rectangle contrast with an arbitrary spectator background. -/
structure RectangleContrastIndex (A B C : Type*) (a₀ : A) (b₀ : B) where
  left : A
  left_ne : left ≠ a₀
  right : B
  right_ne : right ≠ b₀
  background : C
deriving DecidableEq

/-- Configuration carrying both non-base values of a rectangle contrast. -/
def rectangleDistinguished {A B C : Type*} {a₀ : A} {b₀ : B}
    (j : RectangleContrastIndex A B C a₀ b₀) : A × B × C :=
  (j.left, j.right, j.background)

theorem rectangleDistinguished_injective
    {A B C : Type*} {a₀ : A} {b₀ : B} :
    Function.Injective
      (rectangleDistinguished :
        RectangleContrastIndex A B C a₀ b₀ → A × B × C) := by
  intro j k h
  rcases j with ⟨ja, hja, jb, hjb, jc⟩
  rcases k with ⟨ka, hka, kb, hkb, kc⟩
  simp only [rectangleDistinguished, Prod.mk.injEq] at h
  cases h.1
  cases h.2.1
  cases h.2.2
  rfl

/-- The balanced four-point relation for one rectangle contrast. -/
noncomputable def rectangleContrastRelation
    {A B C R : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] [Ring R]
    (a₀ : A) (b₀ : B) (j : RectangleContrastIndex A B C a₀ b₀) :
    (A × B × C) →₀ R :=
  Finsupp.single (j.left, j.right, j.background) 1 +
    Finsupp.single (a₀, b₀, j.background) 1 -
    Finsupp.single (j.left, b₀, j.background) 1 -
    Finsupp.single (a₀, j.right, j.background) 1

theorem rectangleContrastRelation_apply_distinguished
    {A B C R : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] [Ring R]
    (a₀ : A) (b₀ : B)
    (j k : RectangleContrastIndex A B C a₀ b₀) :
    rectangleContrastRelation (R := R) a₀ b₀ k (rectangleDistinguished j) =
      if k = j then 1 else 0 := by
  by_cases hkj : k = j
  · subst k
    simp [rectangleContrastRelation, rectangleDistinguished, j.left_ne, j.right_ne]
  · have hdist :
        rectangleDistinguished k ≠ rectangleDistinguished j := by
      exact fun h => hkj (rectangleDistinguished_injective h)
    have hfirst :
        (k.left, k.right, k.background) ≠ rectangleDistinguished j := by
      simpa [rectangleDistinguished] using hdist
    have hbase :
        (a₀, b₀, k.background) ≠ rectangleDistinguished j := by
      intro h
      have hleft : a₀ = j.left := congrArg Prod.fst h
      exact j.left_ne hleft.symm
    have hleft :
        (k.left, b₀, k.background) ≠ rectangleDistinguished j := by
      intro h
      have hright : b₀ = j.right := congrArg (fun z => z.2.1) h
      exact j.right_ne hright.symm
    have hright :
        (a₀, k.right, k.background) ≠ rectangleDistinguished j := by
      intro h
      have hleft : a₀ = j.left := congrArg Prod.fst h
      exact j.left_ne hleft.symm
    simp [rectangleContrastRelation, hkj, hfirst, hbase, hleft, hright]

/-- Standard rectangle relations are linearly independent: the all-non-base configuration is a
private pivot for each relation. -/
theorem rectangleContrastRelation_linearIndependent
    {A B C R : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] [CommRing R]
    (a₀ : A) (b₀ : B) :
    LinearIndependent R
      (rectangleContrastRelation (R := R) a₀ b₀ :
        RectangleContrastIndex A B C a₀ b₀ → (A × B × C) →₀ R) := by
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro j
  have hj := congrArg
    (fun z : (A × B × C) →₀ R => z (rectangleDistinguished j)) hl
  rw [Finsupp.linearCombination_apply] at hj
  change
    (l.sum fun i a => a • rectangleContrastRelation (R := R) a₀ b₀ i)
        (rectangleDistinguished j) = 0 at hj
  rw [Finsupp.sum_apply] at hj
  simpa [rectangleContrastRelation_apply_distinguished] using hj

def rectangleContrastIndexEquiv
    {A B C : Type*} (a₀ : A) (b₀ : B) :
    RectangleContrastIndex A B C a₀ b₀ ≃
      ({a : A // a ≠ a₀} × {b : B // b ≠ b₀}) × C where
  toFun j := ((⟨j.left, j.left_ne⟩, ⟨j.right, j.right_ne⟩), j.background)
  invFun j := ⟨j.1.1, j.1.1.2, j.1.2, j.1.2.2, j.2⟩
  left_inv j := by cases j; rfl
  right_inv j := by rcases j with ⟨⟨a, b⟩, c⟩; rfl

noncomputable instance rectangleContrastIndexFintype
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] (a₀ : A) (b₀ : B) :
    Fintype (RectangleContrastIndex A B C a₀ b₀) :=
  Fintype.ofEquiv (({a : A // a ≠ a₀} × {b : B // b ≠ b₀}) × C)
    (rectangleContrastIndexEquiv a₀ b₀).symm

/-- Exact number of independent rectangle contrasts. -/
theorem rectangleContrastIndex_card
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] (a₀ : A) (b₀ : B) :
    Fintype.card (RectangleContrastIndex A B C a₀ b₀) =
      (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C := by
  classical
  rw [Fintype.card_congr (rectangleContrastIndexEquiv a₀ b₀),
    Fintype.card_prod, Fintype.card_prod]
  have hA :
      Fintype.card {a : A // a ≠ a₀} = Fintype.card A - 1 := by
    rw [Fintype.card_subtype_compl (fun a : A => a = a₀),
      Fintype.card_subtype_eq]
  have hB :
      Fintype.card {b : B // b ≠ b₀} = Fintype.card B - 1 := by
    rw [Fintype.card_subtype_compl (fun b : B => b = b₀),
      Fintype.card_subtype_eq]
  rw [hA, hB]

/-- The relation space generated by rectangle contrasts has the exact predicted dimension. -/
theorem rectangleContrastRelation_span_finrank
    {A B C R : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Field R]
    (a₀ : A) (b₀ : B) :
    Module.finrank R
        (Submodule.span R
          (Set.range
            (rectangleContrastRelation (R := R) a₀ b₀ :
              RectangleContrastIndex A B C a₀ b₀ → (A × B × C) →₀ R))) =
      (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C := by
  rw [finrank_span_eq_card (rectangleContrastRelation_linearIndependent a₀ b₀)]
  exact rectangleContrastIndex_card a₀ b₀

/-- A fixed pair of sites in an `n`-site `q`-level system carries
`(q-1)^2 q^(n-2)` independent rectangle contrasts. -/
theorem quditPair_rectangleContrastIndex_card
    {q n : ℕ} (a₀ b₀ : Fin q) :
    Fintype.card
        (RectangleContrastIndex (Fin q) (Fin q) (Fin (n - 2) → Fin q) a₀ b₀) =
      (q - 1) ^ 2 * q ^ (n - 2) := by
  rw [rectangleContrastIndex_card]
  simp only [Fintype.card_fin, Fintype.card_fun]
  rw [pow_two]

/-- A balanced relation is visible to an `m`-replica mixed reporter when it is the difference of
two multisets of `m` spectral labels. -/
def HasBalancedReplicaRepresentation
    {X : Type*} [DecidableEq X] (m : ℕ) (k : X →₀ ℤ) : Prop :=
  ∃ positive negative : Fin m → X,
    k = (∑ i, Finsupp.single (positive i) 1) -
      ∑ i, Finsupp.single (negative i) 1

/-- Every rectangle contrast is a second-replica relation. -/
theorem rectangleContrastRelation_hasBalancedReplicaRepresentation_two
    {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B) (j : RectangleContrastIndex A B C a₀ b₀) :
    HasBalancedReplicaRepresentation 2
      (rectangleContrastRelation (R := ℤ) a₀ b₀ j) := by
  refine ⟨![((j.left, j.right, j.background) : A × B × C),
      (a₀, b₀, j.background)],
    ![((j.left, b₀, j.background) : A × B × C),
      (a₀, j.right, j.background)], ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold rectangleContrastRelation
  abel

/-! ## Arbitrary-support spectral causality -/

/-- Generic Boolean Möbius transform of a response packet. -/
def finsetMobiusResponse {ι R : Type*} [DecidableEq ι] [CommRing R]
    (t : Finset ι) (response : Finset ι → R) : R :=
  ∑ d ∈ t.powerset, (-1 : R) ^ d.card * response (t \ d)

theorem finsetMobiusResponse_insert
    {ι R : Type*} [DecidableEq ι] [CommRing R]
    {p : ι} {s : Finset ι} (hp : p ∉ s) (response : Finset ι → R) :
    finsetMobiusResponse (insert p s) response =
      finsetMobiusResponse s (fun t => response (insert p t)) -
        finsetMobiusResponse s response := by
  unfold finsetMobiusResponse
  rw [Finset.sum_powerset_insert hp, sub_eq_add_neg]
  congr 1
  · apply Finset.sum_congr rfl
    intro d hd
    have hpd : p ∉ d := fun hmem => hp ((Finset.mem_powerset.mp hd) hmem)
    have hdiff : insert p s \ d = insert p (s \ d) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    rw [hdiff]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hpd : p ∉ d := fun hmem => hp ((Finset.mem_powerset.mp hd) hmem)
    have hdiff : insert p s \ insert p d = s \ d := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    rw [hdiff, Finset.card_insert_of_notMem hpd, pow_succ]
    ring

/-- Replace the coordinates in `s` by their selected alternative values. -/
def updateOnFinset {ι A : Type*} [DecidableEq ι]
    (x alternative : ι → A) (s : Finset ι) : ι → A :=
  fun i => if i ∈ s then alternative i else x i

/-- Alternating mixed difference over every subpacket of `sites`. -/
def higherCoordinateContrast
    {ι A R : Type*} [DecidableEq ι] [CommRing R]
    (x alternative : ι → A) (sites : Finset ι) (f : (ι → A) → R) : R :=
  finsetMobiusResponse sites
    (fun active => f (updateOnFinset x alternative active))

theorem coordinateLocalOn_updateOnFinset_insert_eq
    {ι A R : Type*} [DecidableEq ι] [CommRing R]
    {support : Set ι} {f : (ι → A) → R}
    (hf : CoordinateLocalOn support f)
    (x alternative : ι → A) {i : ι} (hi : i ∉ support) (active : Finset ι) :
    f (updateOnFinset x alternative (insert i active)) =
      f (updateOnFinset x alternative active) := by
  apply hf
  intro j hj
  have hji : j ≠ i := by
    intro h
    exact hi (h ▸ hj)
  simp [updateOnFinset, hji]

/-- A higher mixed difference vanishes when its local function misses any changed coordinate. -/
theorem higherCoordinateContrast_eq_zero_of_local_miss
    {ι A R : Type*} [DecidableEq ι] [CommRing R]
    {support : Set ι} {f : (ι → A) → R}
    (hf : CoordinateLocalOn support f)
    (x alternative : ι → A) {sites : Finset ι} {i : ι}
    (hi_sites : i ∈ sites) (hi_support : i ∉ support) :
    higherCoordinateContrast x alternative sites f = 0 := by
  have hi_erase : i ∉ sites.erase i := by simp
  rw [← Finset.insert_erase hi_sites]
  unfold higherCoordinateContrast
  rw [finsetMobiusResponse_insert hi_erase]
  have hresponse :
      (fun active =>
        f (updateOnFinset x alternative (insert i active))) =
      (fun active => f (updateOnFinset x alternative active)) := by
    funext active
    exact coordinateLocalOn_updateOnFinset_insert_eq
      hf x alternative hi_support active
  rw [hresponse, sub_self]

theorem higherCoordinateContrast_sum
    {ι A R κ : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset κ) (term : κ → (ι → A) → R)
    (x alternative : ι → A) (sites : Finset ι) :
    higherCoordinateContrast x alternative sites (∑ c ∈ s, term c) =
      ∑ c ∈ s, higherCoordinateContrast x alternative sites (term c) := by
  unfold higherCoordinateContrast finsetMobiusResponse
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Every sum of cluster-local functions vanishes under the `sites` contrast when each cluster
misses at least one changed site. -/
theorem higherCoordinateContrast_sum_eq_zero_of_cluster_miss
    {ι A R κ : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset κ) (support : κ → Set ι) (term : κ → (ι → A) → R)
    (hlocal : ∀ c ∈ s, CoordinateLocalOn (support c) (term c))
    (x alternative : ι → A) (sites : Finset ι)
    (hmiss : ∀ c ∈ s, ∃ i ∈ sites, i ∉ support c) :
    higherCoordinateContrast x alternative sites (∑ c ∈ s, term c) = 0 := by
  rw [higherCoordinateContrast_sum]
  apply Finset.sum_eq_zero
  intro c hc
  obtain ⟨i, hi_sites, hi_support⟩ := hmiss c hc
  exact higherCoordinateContrast_eq_zero_of_local_miss
    (hlocal c hc) x alternative hi_sites hi_support

/-- Minimum number of edges in a connected subgraph spanning `sites`, with value `⊤` when no such
subgraph exists. -/
noncomputable def connectedSpanningCost
    {V : Type*} [Fintype V] (G : SimpleGraph V) (sites : Finset V) : WithTop ℕ :=
  sInf {cost : WithTop ℕ |
    ∃ H : G.Subgraph, H.Connected ∧
      (sites : Set V) ⊆ H.verts ∧ cost = Nat.card H.coe.edgeSet}

theorem connectedSpanningCost_le_edge_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) (sites : Finset V)
    (H : G.Subgraph) (hconnected : H.Connected)
    (hspan : (sites : Set V) ⊆ H.verts) :
    connectedSpanningCost G sites ≤ Nat.card H.coe.edgeSet := by
  unfold connectedSpanningCost
  apply sInf_le
  exact ⟨H, hconnected, hspan, rfl⟩

theorem connectedCluster_misses_site_of_depth_lt_connectedSpanningCost
    {V : Type*} [Fintype V] (G : SimpleGraph V) (sites : Finset V)
    (H : G.Subgraph) (hconnected : H.Connected) {r : ℕ}
    (hdepth : Nat.card H.coe.edgeSet ≤ r)
    (hcost : (r : WithTop ℕ) < connectedSpanningCost G sites) :
    ∃ i ∈ sites, i ∉ H.verts := by
  by_contra h
  have hspan : (sites : Set V) ⊆ H.verts := by
    intro i hi
    by_contra hin
    exact h ⟨i, hi, hin⟩
  have hle := connectedSpanningCost_le_edge_card G sites H hconnected hspan
  have hedge : (Nat.card H.coe.edgeSet : WithTop ℕ) ≤ r := by
    exact_mod_cast hdepth
  exact (not_lt_of_ge (hle.trans hedge)) hcost

/-- **Steiner spectral causality.** A higher contrast supported on `sites` annihilates every
depth-`r` connected-cluster expansion whenever `r` is smaller than the minimum connected spanning
cost of `sites`. -/
theorem higherCoordinateContrast_sum_eq_zero_of_connectedSpanningCost
    {V A R κ : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (G : SimpleGraph V) (s : Finset κ) (cluster : κ → G.Subgraph)
    (term : κ → (V → A) → R)
    (hconnected : ∀ c ∈ s, (cluster c).Connected)
    (hlocal : ∀ c ∈ s, CoordinateLocalOn (cluster c).verts (term c))
    {r : ℕ} (hdepth : ∀ c ∈ s, Nat.card (cluster c).coe.edgeSet ≤ r)
    (x alternative : V → A) (sites : Finset V)
    (hcost : (r : WithTop ℕ) < connectedSpanningCost G sites) :
    higherCoordinateContrast x alternative sites (∑ c ∈ s, term c) = 0 := by
  apply higherCoordinateContrast_sum_eq_zero_of_cluster_miss
    s (fun c => (cluster c).verts) term hlocal x alternative sites
  intro c hc
  exact connectedCluster_misses_site_of_depth_lt_connectedSpanningCost
    G sites (cluster c) (hconnected c hc) (hdepth c hc) hcost

end GaloisForLFunctions.HTGeometry
