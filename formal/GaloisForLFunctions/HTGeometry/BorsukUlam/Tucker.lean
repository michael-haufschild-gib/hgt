import GaloisForLFunctions.HTGeometry.BorsukUlam.Alternating
import GaloisForLFunctions.HTGeometry.BorsukUlam.FlagComplex
import GaloisForLFunctions.HTGeometry.BorsukUlam.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Tucker's lemma

Let `K` be a `FlagComplex n` — an antipodally symmetric triangulation of the `n`-sphere aligned
with a flag of hemispheres — and let `lab` be an antisymmetric labelling of its vertices by
nonzero integers of absolute value at most `n`.  Then some edge of `K` carries two labels summing
to zero.

The proof is the path argument of Fan, in the constructive form of Prescott–Su.  Assuming no such
edge, one builds a graph whose nodes are

* `T1` agreeable alternating faces with `card = cdim`,
* `T2` agreeable almost-alternating faces with `card = cdim + 1`,
* `T3` alternating faces with `card = cdim + 1`,

with `σ` adjacent to `τ` when one is a facet of the other, the smaller one is alternating, the
larger one satisfies `card = cdim + 1`, and the sign of the smaller matches the carrier sign of the
larger.  Every node then has degree `1` or `2`, and the nodes of degree `1` are exactly the two
antipodal vertices of `H₀` (an alternating face with `card = n + 1` would need `n + 1` labels of
distinct absolute value in `{1, …, n}`).  But the antipodal involution acts freely on the graph
and moves every edge, so the number of odd-degree nodes is divisible by `4` — and it is `2`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.BorsukUlam

open Finset

attribute [local instance 0] Classical.propDecidable

namespace FlagComplex

variable {n : ℕ} {K : FlagComplex n} {lab : K.V → ℤ}

/-- The three kinds of node of the Fan graph. -/
def IsNode (K : FlagComplex n) (lab : K.V → ℤ) (σ : Finset K.V) : Prop :=
  σ ∈ K.faces ∧
    ((σ.card = K.cdim σ ∧ alt lab (K.csgn σ) σ) ∨
      (σ.card = K.cdim σ + 1 ∧ almostAlt lab (K.csgn σ) σ) ∨
      (σ.card = K.cdim σ + 1 ∧ AltSet lab σ))

/-- `τ` covers `σ`: it is a face with one more vertex, it is a top face of its own carrier
hemisphere, and `σ` is alternating with the carrier sign of `τ`. -/
def Cov (K : FlagComplex n) (lab : K.V → ℤ) (σ τ : Finset K.V) : Prop :=
  σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ τ.card = K.cdim τ + 1 ∧ alt lab (K.csgn τ) σ

/-- Adjacency in the Fan graph. -/
def Adj (K : FlagComplex n) (lab : K.V → ℤ) (σ τ : Finset K.V) : Prop :=
  IsNode K lab σ ∧ IsNode K lab τ ∧ (Cov K lab σ τ ∨ Cov K lab τ σ)

/-- The nodes of the Fan graph. -/
noncomputable def nodes (K : FlagComplex n) (lab : K.V → ℤ) : Finset (Finset K.V) :=
  K.faces.filter (IsNode K lab)

/-- The degree of a node. -/
noncomputable def deg (K : FlagComplex n) (lab : K.V → ℤ) (σ : Finset K.V) : ℕ :=
  ((nodes K lab).filter (Adj K lab σ)).card

theorem mem_nodes {σ : Finset K.V} : σ ∈ nodes K lab ↔ IsNode K lab σ := by
  rw [nodes, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem adj_symm {σ τ : Finset K.V} (h : Adj K lab σ τ) : Adj K lab τ σ :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem cov_card_ne {σ τ : Finset K.V} (h : Cov K lab σ τ) : σ ≠ τ := by
  intro hcon
  rw [hcon] at h
  have := h.2.1
  omega

theorem adj_irrefl {σ : Finset K.V} : ¬ Adj K lab σ σ := by
  rintro ⟨-, -, h | h⟩ <;> exact cov_card_ne h rfl

/-- A face with one vertex removed is a face, provided at least two vertices remain. -/
theorem erase_mem_faces {σ : Finset K.V} (hσ : σ ∈ K.faces) {v : K.V} (hv : v ∈ σ)
    (h2 : 2 ≤ σ.card) : σ.erase v ∈ K.faces := by
  refine K.faces_down σ hσ _ (erase_subset _ _) ?_
  rw [← card_pos, card_erase_of_mem hv]
  omega

/-- A subset with one fewer element is obtained by erasing a vertex. -/
theorem exists_erase {σ τ : Finset K.V} (hsub : τ ⊆ σ) (hc : σ.card = τ.card + 1) :
    ∃ v ∈ σ, τ = σ.erase v := by
  have hcard : (σ \ τ).card = 1 := by
    rw [card_sdiff_of_subset hsub]
    omega
  obtain ⟨v, hv⟩ := card_eq_one.mp hcard
  have hvσ : v ∈ σ := by
    have : v ∈ σ \ τ := by rw [hv]; exact mem_singleton_self v
    exact (mem_sdiff.mp this).1
  refine ⟨v, hvσ, ?_⟩
  ext z
  simp only [mem_erase]
  constructor
  · intro hz
    refine ⟨?_, hsub hz⟩
    rintro rfl
    have : z ∈ σ \ τ := by rw [hv]; exact mem_singleton_self z
    exact (mem_sdiff.mp this).2 hz
  · rintro ⟨hzv, hzσ⟩
    by_contra hzτ
    have : z ∈ σ \ τ := mem_sdiff.mpr ⟨hzσ, hzτ⟩
    rw [hv, mem_singleton] at this
    exact hzv this

section Antipodal

theorem negF_erase (σ : Finset K.V) (v : K.V) :
    K.negF (σ.erase v) = (K.negF σ).erase (K.neg v) := by
  ext z
  rw [mem_negF, mem_erase, mem_erase, mem_negF]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hcon => h1 ?_, h2⟩
    rw [hcon, K.neg_neg]
  · rintro ⟨h1, h2⟩
    refine ⟨fun hcon => h1 ?_, h2⟩
    rw [← hcon, K.neg_neg]

theorem negF_nonempty {σ : Finset K.V} (hne : σ.Nonempty) : (K.negF σ).Nonempty := by
  obtain ⟨v, hv⟩ := hne
  exact ⟨K.neg v, mem_negF.mpr (by rwa [K.neg_neg])⟩

theorem negF_ne_self {σ : Finset K.V} (hσ : σ ∈ K.faces) : K.negF σ ≠ σ := by
  intro hcon
  have h1 := csgn_negF hσ (K.faces_nonempty σ hσ)
  rw [hcon] at h1
  simp at h1

variable (hanti : ∀ v, lab (K.neg v) = -(lab v))

include hanti

theorem alt_negF {s : Bool} {σ : Finset K.V} (h : alt lab s σ) : alt lab (!s) (K.negF σ) :=
  alt_image_neg neg_injective hanti h

theorem altSet_negF {σ : Finset K.V} (hne : σ.Nonempty) (h : AltSet lab σ) :
    AltSet lab (K.negF σ) := by
  obtain ⟨s, hs⟩ := (altSet_iff_exists_alt hne).mp h
  exact altSet_of_alt (alt_negF hanti hs)

theorem altSet_negF_iff {σ : Finset K.V} (hne : σ.Nonempty) :
    AltSet lab (K.negF σ) ↔ AltSet lab σ := by
  refine ⟨fun h => ?_, altSet_negF hanti hne⟩
  have := altSet_negF hanti (negF_nonempty hne) h
  rwa [negF_negF] at this

theorem almostAlt_negF {s : Bool} {σ : Finset K.V} (hne : σ.Nonempty)
    (h : almostAlt lab s σ) : almostAlt lab (!s) (K.negF σ) := by
  obtain ⟨hnot, v, hv, hav⟩ := h
  refine ⟨fun hcon => hnot ((altSet_negF_iff hanti hne).mp hcon), K.neg v, ?_, ?_⟩
  · exact mem_negF.mpr (by rwa [K.neg_neg])
  · rw [← negF_erase]
    exact alt_negF hanti hav

theorem isNode_negF {σ : Finset K.V} (h : IsNode K lab σ) : IsNode K lab (K.negF σ) := by
  obtain ⟨hσ, hcase⟩ := h
  have hne := K.faces_nonempty σ hσ
  have hcs : K.csgn (K.negF σ) = !K.csgn σ := csgn_negF hσ hne
  refine ⟨negF_mem hσ, ?_⟩
  rcases hcase with ⟨hc, ha⟩ | ⟨hc, ha⟩ | ⟨hc, ha⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [card_negF, cdim_negF]; exact hc
    · rw [hcs]; exact alt_negF hanti ha
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rw [card_negF, cdim_negF]; exact hc
    · rw [hcs]; exact almostAlt_negF hanti hne ha
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [card_negF, cdim_negF]; exact hc
    · exact altSet_negF hanti hne ha

theorem cov_negF {σ τ : Finset K.V} (hτ : τ ∈ K.faces) (h : Cov K lab σ τ) :
    Cov K lab (K.negF σ) (K.negF τ) := by
  obtain ⟨hsub, hc1, hc2, ha⟩ := h
  refine ⟨negF_subset hsub, ?_, ?_, ?_⟩
  · rw [card_negF, card_negF]; exact hc1
  · rw [card_negF, cdim_negF]; exact hc2
  · rw [csgn_negF hτ (K.faces_nonempty τ hτ)]
    exact alt_negF hanti ha

theorem adj_negF {σ τ : Finset K.V} (h : Adj K lab σ τ) :
    Adj K lab (K.negF σ) (K.negF τ) := by
  obtain ⟨hnσ, hnτ, hcov⟩ := h
  refine ⟨isNode_negF hanti hnσ, isNode_negF hanti hnτ, ?_⟩
  rcases hcov with hc | hc
  · exact Or.inl (cov_negF hanti hnτ.1 hc)
  · exact Or.inr (cov_negF hanti hnσ.1 hc)

end Antipodal

theorem erase_ne_erase {σ : Finset K.V} {a b : K.V} (ha : a ∈ σ) (hb : b ∈ σ) (hab : a ≠ b) :
    σ.erase a ≠ σ.erase b := by
  intro hcon
  have : a ∈ σ.erase b := mem_erase.mpr ⟨hab, ha⟩
  rw [← hcon] at this
  exact (notMem_erase a σ) this

section Degrees

variable (hnz : ∀ v, lab v ≠ 0)

include hnz

/-- Erasing a vertex from a top face of its carrier hemisphere, when the result is alternating
with the carrier sign, gives a node. -/
theorem isNode_erase {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ + 1)
    (h2 : 2 ≤ σ.card) {v : K.V} (hv : v ∈ σ) (ha : alt lab (K.csgn σ) (σ.erase v)) :
    IsNode K lab (σ.erase v) := by
  have hτ : σ.erase v ∈ K.faces := erase_mem_faces hσ hv h2
  have hcardτ : (σ.erase v).card = σ.card - 1 := card_erase_of_mem hv
  have hcd1 : K.cdim (σ.erase v) ≤ K.cdim σ := cdim_mono (erase_subset _ _)
  have hcd2 : (σ.erase v).card ≤ K.cdim (σ.erase v) + 1 := K.card_le _ hτ
  rcases Nat.lt_or_ge (K.cdim (σ.erase v)) (K.cdim σ) with hlt | hge
  · exact ⟨hτ, Or.inr (Or.inr ⟨by omega, altSet_of_alt ha⟩)⟩
  · have hcdeq : K.cdim (σ.erase v) = K.cdim σ := le_antisymm hcd1 hge
    have hcsgn : K.csgn (σ.erase v) = K.csgn σ := csgn_eq_of_subset hτ hσ (erase_subset _ _) hcdeq
    exact ⟨hτ, Or.inl ⟨by omega, by rw [hcsgn]; exact ha⟩⟩

/-- The larger member of a covering pair is a node. -/
theorem isNode_of_cov {σ τ : Finset K.V} (hτ : τ ∈ K.faces) (h : Cov K lab σ τ) :
    IsNode K lab τ := by
  obtain ⟨hsub, hc1, hc2, ha⟩ := h
  obtain ⟨v, hv, hveq⟩ := exists_erase hsub (by omega)
  rw [hveq] at ha
  rcases altSet_or_almostAlt hv ha with hAS | hAA
  · exact ⟨hτ, Or.inr (Or.inr ⟨hc2, hAS⟩)⟩
  · exact ⟨hτ, Or.inr (Or.inl ⟨hc2, hAA⟩)⟩

/-- Neighbours of a `T1` node: the two faces of the same carrier dimension above it. -/
theorem adj_iff_T1 {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ)
    (ha : alt lab (K.csgn σ) σ) (τ : Finset K.V) :
    Adj K lab σ τ ↔ (τ ∈ K.faces ∧ σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ K.cdim τ = K.cdim σ) := by
  constructor
  · rintro ⟨hnσ, hnτ, hcov | hcov⟩
    · have h1 := hcov.2.1
      have h2 := hcov.2.2.1
      exact ⟨hnτ.1, hcov.1, h1, by omega⟩
    · have h2 := hcov.2.2.1
      exact absurd h2 (by omega)
  · rintro ⟨hτ, hsub, hcard, hcd⟩
    have hcov : Cov K lab σ τ := by
      refine ⟨hsub, hcard, by omega, ?_⟩
      rw [← csgn_eq_of_subset hσ hτ hsub hcd.symm]
      exact ha
    exact ⟨⟨hσ, Or.inl ⟨hc, ha⟩⟩, isNode_of_cov hnz hτ hcov, Or.inl hcov⟩

theorem deg_T1 {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ)
    (ha : alt lab (K.csgn σ) σ) : deg K lab σ = 2 := by
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, hne12, ⟨hs1, hc1, hd1⟩, ⟨hs2, hc2, hd2⟩, huniq⟩ :=
    facets_two_cdim hσ hc
  have hfilter : (nodes K lab).filter (Adj K lab σ) = {τ₁, τ₂} := by
    ext τ
    simp only [mem_filter, mem_insert, mem_singleton, mem_nodes]
    constructor
    · rintro ⟨-, hadj⟩
      obtain ⟨hτ, hsub, hcard, hcd⟩ := (adj_iff_T1 hnz hσ hc ha τ).mp hadj
      exact huniq τ hτ hsub hcard hcd
    · rintro (rfl | rfl)
      · exact ⟨(adj_iff_T1 hnz hσ hc ha τ).mpr ⟨hτ₁, hs1, hc1, hd1⟩ |>.2.1,
          (adj_iff_T1 hnz hσ hc ha τ).mpr ⟨hτ₁, hs1, hc1, hd1⟩⟩
      · exact ⟨(adj_iff_T1 hnz hσ hc ha τ).mpr ⟨hτ₂, hs2, hc2, hd2⟩ |>.2.1,
          (adj_iff_T1 hnz hσ hc ha τ).mpr ⟨hτ₂, hs2, hc2, hd2⟩⟩
  rw [deg, hfilter, card_insert_of_notMem (by simp [hne12]), card_singleton]

/-- Neighbours of a `T2` node: its two alternating facets. -/
theorem adj_iff_T2 {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ + 1)
    (haa : almostAlt lab (K.csgn σ) σ) (τ : Finset K.V) :
    Adj K lab σ τ ↔ (∃ v ∈ σ, τ = σ.erase v ∧ alt lab (K.csgn σ) τ) := by
  have h2 : 2 ≤ σ.card := by
    by_contra hcon
    exact haa.1 (altSet_of_card_le_one (fun v _ => hnz v) (by omega))
  constructor
  · rintro ⟨hnσ, hnτ, hcov | hcov⟩
    · exact absurd (altSet_of_alt hcov.2.2.2) haa.1
    · obtain ⟨v, hv, hveq⟩ := exists_erase hcov.1 hcov.2.1
      exact ⟨v, hv, hveq, hcov.2.2.2⟩
  · rintro ⟨v, hv, rfl, halt⟩
    have hnodeτ := isNode_erase hnz hσ hc h2 hv halt
    refine ⟨⟨hσ, Or.inr (Or.inl ⟨hc, haa⟩)⟩, hnodeτ, Or.inr ⟨erase_subset _ _, ?_, hc, halt⟩⟩
    rw [card_erase_of_mem hv]
    omega

theorem deg_T2 {σ : Finset K.V}
    (hcompl : ∀ σ' ∈ K.faces, ∀ u ∈ σ', ∀ v ∈ σ', lab u + lab v ≠ 0)
    (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ + 1)
    (haa : almostAlt lab (K.csgn σ) σ) : deg K lab σ = 2 := by
  obtain ⟨a, ha, b, hb, hab, halta, haltb, huniq⟩ :=
    exists_pair_alt_erase_of_almostAlt (fun v _ => hnz v) (hcompl σ hσ) haa
  have hfilter : (nodes K lab).filter (Adj K lab σ) = {σ.erase a, σ.erase b} := by
    ext τ
    simp only [mem_filter, mem_insert, mem_singleton, mem_nodes]
    constructor
    · rintro ⟨-, hadj⟩
      obtain ⟨v, hv, rfl, halt⟩ := (adj_iff_T2 hnz hσ hc haa τ).mp hadj
      rcases (huniq v hv _ halt).1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · have hA := (adj_iff_T2 hnz hσ hc haa (σ.erase a)).mpr ⟨a, ha, rfl, halta⟩
      have hB := (adj_iff_T2 hnz hσ hc haa (σ.erase b)).mpr ⟨b, hb, rfl, haltb⟩
      rintro (rfl | rfl)
      · exact ⟨hA.2.1, hA⟩
      · exact ⟨hB.2.1, hB⟩
  rw [deg, hfilter, card_insert_of_notMem (by simp only [mem_singleton]; exact erase_ne_erase ha hb hab), card_singleton]

/-- Neighbours of a `T3` node: one alternating facet below, and one face above. -/
theorem adj_iff_T3 {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ + 1)
    {s : Bool} (has : alt lab s σ) (τ : Finset K.V) :
    Adj K lab σ τ ↔
      ((2 ≤ σ.card ∧ ∃ v ∈ σ, τ = σ.erase v ∧ alt lab (K.csgn σ) τ) ∨
       (τ ∈ K.faces ∧ σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ K.cdim τ = K.cdim σ + 1 ∧
         K.csgn τ = s)) := by
  have hne : σ.Nonempty := K.faces_nonempty σ hσ
  have hnodeσ : IsNode K lab σ := ⟨hσ, Or.inr (Or.inr ⟨hc, altSet_of_alt has⟩)⟩
  constructor
  · rintro ⟨hnσ, hnτ, hcov | hcov⟩
    · obtain ⟨hsub, hc1, hc2, ha⟩ := hcov
      exact Or.inr ⟨hnτ.1, hsub, hc1, by omega, alt_sign_unique hne ha has⟩
    · obtain ⟨hsub, hc1, hc2, ha⟩ := hcov
      obtain ⟨v, hv, hveq⟩ := exists_erase hsub hc1
      have hτpos : 0 < τ.card := card_pos.mpr (K.faces_nonempty τ hnτ.1)
      exact Or.inl ⟨by omega, v, hv, hveq, ha⟩
  · rintro (⟨h2, v, hv, rfl, halt⟩ | ⟨hτ, hsub, hc1, hcd, hcs⟩)
    · refine ⟨hnodeσ, isNode_erase hnz hσ hc h2 hv halt, Or.inr ⟨erase_subset _ _, ?_, hc, halt⟩⟩
      rw [card_erase_of_mem hv]
      omega
    · have hcov : Cov K lab σ τ := ⟨hsub, hc1, by omega, by rw [hcs]; exact has⟩
      exact ⟨hnodeσ, isNode_of_cov hnz hτ hcov, Or.inl hcov⟩

theorem deg_T3_bottom {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ + 1)
    {s : Bool} (has : alt lab s σ) (h1 : σ.card = 1) (hn : 0 < n) : deg K lab σ = 1 := by
  obtain ⟨τup, hτup, ⟨hsub, hc1, hcd, hcs⟩, huniq⟩ := facets_one_cdim hσ hc (by omega) s
  have hfilter : (nodes K lab).filter (Adj K lab σ) = {τup} := by
    ext τ
    simp only [mem_filter, mem_singleton, mem_nodes]
    constructor
    · rintro ⟨-, hadj⟩
      rcases (adj_iff_T3 hnz hσ hc has τ).mp hadj with ⟨hh2, -⟩ | ⟨hτ, hs2, hc2, hcd2, hcs2⟩
      · omega
      · exact huniq τ hτ hs2 hc2 hcd2 hcs2
    · rintro rfl
      have hA := (adj_iff_T3 hnz hσ hc has τ).mpr (Or.inr ⟨hτup, hsub, hc1, hcd, hcs⟩)
      exact ⟨hA.2.1, hA⟩
  rw [deg, hfilter, card_singleton]

theorem deg_T3_mid {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ + 1)
    {s : Bool} (has : alt lab s σ) (h2 : 2 ≤ σ.card) (hlt : K.cdim σ < n) :
    deg K lab σ = 2 := by
  obtain ⟨a, ha, halta, huniqa⟩ := exists_unique_alt_erase_of_alt has h2 (K.csgn σ)
  obtain ⟨τup, hτup, ⟨hsub, hc1, hcd, hcs⟩, huniqu⟩ := facets_one_cdim hσ hc hlt s
  have hcarda : (σ.erase a).card = σ.card - 1 := card_erase_of_mem ha
  have hne : σ.erase a ≠ τup := by
    intro hcon
    rw [hcon, hc1] at hcarda
    omega
  have hfilter : (nodes K lab).filter (Adj K lab σ) = {σ.erase a, τup} := by
    ext τ
    simp only [mem_filter, mem_insert, mem_singleton, mem_nodes]
    constructor
    · rintro ⟨-, hadj⟩
      rcases (adj_iff_T3 hnz hσ hc has τ).mp hadj with ⟨-, v, hv, rfl, halt⟩ |
        ⟨hτ, hs2, hc2, hcd2, hcs2⟩
      · exact Or.inl (by rw [huniqa v hv halt])
      · exact Or.inr (huniqu τ hτ hs2 hc2 hcd2 hcs2)
    · have hA := (adj_iff_T3 hnz hσ hc has (σ.erase a)).mpr (Or.inl ⟨h2, a, ha, rfl, halta⟩)
      have hB := (adj_iff_T3 hnz hσ hc has τup).mpr (Or.inr ⟨hτup, hsub, hc1, hcd, hcs⟩)
      rintro (rfl | rfl)
      · exact ⟨hA.2.1, hA⟩
      · exact ⟨hB.2.1, hB⟩
  rw [deg, hfilter, card_insert_of_notMem (by simp only [mem_singleton]; exact hne),
    card_singleton]

theorem deg_T3_top {σ : Finset K.V} (hσ : σ ∈ K.faces) (hc : σ.card = K.cdim σ + 1)
    {s : Bool} (has : alt lab s σ) (h2 : 2 ≤ σ.card) (htop : K.cdim σ = n) :
    deg K lab σ = 1 := by
  obtain ⟨a, ha, halta, huniqa⟩ := exists_unique_alt_erase_of_alt has h2 (K.csgn σ)
  have hfilter : (nodes K lab).filter (Adj K lab σ) = {σ.erase a} := by
    ext τ
    simp only [mem_filter, mem_singleton, mem_nodes]
    constructor
    · rintro ⟨-, hadj⟩
      rcases (adj_iff_T3 hnz hσ hc has τ).mp hadj with ⟨-, v, hv, rfl, halt⟩ |
        ⟨hτ, hs2, hc2, hcd2, hcs2⟩
      · rw [huniqa v hv halt]
      · have := cdim_le (K := K) τ
        omega
    · rintro rfl
      have hA := (adj_iff_T3 hnz hσ hc has (σ.erase a)).mpr (Or.inl ⟨h2, a, ha, rfl, halta⟩)
      exact ⟨hA.2.1, hA⟩
  rw [deg, hfilter, card_singleton]

end Degrees

section Main

variable (hn : 1 ≤ n) (hnz : ∀ v, lab v ≠ 0) (hbound : ∀ v, |lab v| ≤ (n : ℤ))
  (hanti : ∀ v, lab (K.neg v) = -(lab v))
  (hcompl : ∀ σ ∈ K.faces, ∀ u ∈ σ, ∀ v ∈ σ, lab u + lab v ≠ 0)

include hnz

theorem base_isNode : IsNode K lab ({K.base} : Finset K.V) := by
  refine ⟨K.base_face, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · rw [card_singleton, base_cdim]
  · exact altSet_of_card_le_one (fun v _ => hnz v) (by simp)

theorem neg_base_isNode : IsNode K lab ({K.neg K.base} : Finset K.V) := by
  refine ⟨neg_base_face, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · rw [card_singleton, neg_base_cdim]
  · exact altSet_of_card_le_one (fun v _ => hnz v) (by simp)

include hn

theorem deg_base : deg K lab ({K.base} : Finset K.V) = 1 := by
  obtain ⟨s, hs⟩ := (altSet_iff_exists_alt ⟨K.base, mem_singleton_self _⟩).mp
    (altSet_of_card_le_one (fun v _ => hnz v) (by simp))
  exact deg_T3_bottom hnz K.base_face (by rw [card_singleton, base_cdim]) hs (by simp) (by omega)

theorem deg_neg_base : deg K lab ({K.neg K.base} : Finset K.V) = 1 := by
  obtain ⟨s, hs⟩ := (altSet_iff_exists_alt ⟨K.neg K.base, mem_singleton_self _⟩).mp
    (altSet_of_card_le_one (fun v _ => hnz v) (by simp))
  exact deg_T3_bottom hnz neg_base_face (by rw [card_singleton, neg_base_cdim]) hs (by simp)
    (by omega)

include hbound hcompl

/-- Under the Tucker hypotheses the only odd-degree nodes are the two vertices of `H₀`. -/
theorem deg_odd_iff {σ : Finset K.V} (hnode : IsNode K lab σ) :
    deg K lab σ % 2 = 1 ↔ (σ = ({K.base} : Finset K.V) ∨ σ = ({K.neg K.base} : Finset K.V)) := by
  obtain ⟨hσ, hcase⟩ := hnode
  rcases hcase with ⟨hc, ha⟩ | ⟨hc, haa⟩ | ⟨hc, hAS⟩
  · rw [deg_T1 hnz hσ hc ha]
    constructor
    · intro h; omega
    · rintro (rfl | rfl)
      · rw [card_singleton, base_cdim] at hc; omega
      · rw [card_singleton, neg_base_cdim] at hc; omega
  · rw [deg_T2 hnz hcompl hσ hc haa]
    constructor
    · intro h; omega
    · rintro (rfl | rfl) <;>
        exact absurd (altSet_of_card_le_one (fun v _ => hnz v) (by simp)) haa.1
  · obtain ⟨s, hs⟩ := (altSet_iff_exists_alt (K.faces_nonempty σ hσ)).mp hAS
    by_cases h1 : σ.card = 1
    · rw [deg_T3_bottom hnz hσ hc hs h1 (by omega)]
      constructor
      · intro _
        obtain ⟨v, hv⟩ := card_eq_one.mp h1
        have hlev : K.lev v = 0 := by
          have hcd : K.cdim σ = 0 := by omega
          have : K.lev v ≤ K.cdim σ := lev_le_cdim (by rw [hv]; exact mem_singleton_self v)
          omega
        rcases K.lev_zero σ hσ v (by rw [hv]; exact mem_singleton_self v) hlev with hb | hb
        · exact Or.inl (by rw [hv, hb])
        · exact Or.inr (by rw [hv, hb])
      · intro _; rfl
    · have h2 : 2 ≤ σ.card := by
        have := card_pos.mpr (K.faces_nonempty σ hσ)
        omega
      have hnotbase : ¬(σ = ({K.base} : Finset K.V) ∨ σ = ({K.neg K.base} : Finset K.V)) := by
        rintro (rfl | rfl) <;> simp at h1
      have hlt : K.cdim σ < n := by
        rcases Nat.lt_or_ge (K.cdim σ) n with h | h
        · exact h
        · exfalso
          have hcd : K.cdim σ = n := le_antisymm (cdim_le σ) h
          have := alt_card_le hs (fun v _ => hbound v)
          omega
      rw [deg_T3_mid hnz hσ hc hs h2 hlt]
      constructor
      · intro h; omega
      · intro h; exact absurd h hnotbase

include hanti

theorem deg_negF {σ : Finset K.V} (hσ : σ ∈ K.faces) :
    deg K lab (K.negF σ) = deg K lab σ := by
  have himg : (nodes K lab).filter (Adj K lab (K.negF σ)) =
      ((nodes K lab).filter (Adj K lab σ)).image K.negF := by
    ext τ
    simp only [mem_filter, mem_image, mem_nodes]
    constructor
    · rintro ⟨hnτ, hadj⟩
      refine ⟨K.negF τ, ⟨isNode_negF hanti hnτ, ?_⟩, negF_negF τ⟩
      have hh := adj_negF hanti hadj
      rwa [negF_negF] at hh
    · rintro ⟨ρ, ⟨hnρ, hadjρ⟩, rfl⟩
      exact ⟨isNode_negF hanti hnρ, adj_negF hanti hadjρ⟩
  have hinj : Function.Injective (K.negF) := by
    intro a b hab
    have := congrArg K.negF hab
    rwa [negF_negF, negF_negF] at this
  rw [deg, deg, himg, card_image_of_injective _ hinj]

end Main

theorem adj_card_ne {σ τ : Finset K.V} (h : Adj K lab σ τ) : σ.card ≠ τ.card := by
  rcases h.2.2 with hc | hc
  · have := hc.2.1; omega
  · have := hc.2.1; omega

/-- **Tucker's lemma.**  An antisymmetric labelling of a symmetric flag triangulation of the
`n`-sphere by nonzero integers of absolute value at most `n` has a complementary edge. -/
theorem tucker {n : ℕ} (K : FlagComplex n) (lab : K.V → ℤ) (hn : 1 ≤ n)
    (hnz : ∀ v, lab v ≠ 0) (hbound : ∀ v, |lab v| ≤ (n : ℤ))
    (hanti : ∀ v, lab (K.neg v) = -(lab v)) :
    ∃ σ ∈ K.faces, ∃ u ∈ σ, ∃ v ∈ σ, lab u + lab v = 0 := by
  by_contra hcon
  push Not at hcon
  set N := nodes K lab with hNdef
  set P : Finset (Finset K.V × Finset K.V) :=
    (N ×ˢ N).filter (fun p => Adj K lab p.1 p.2) with hPdef
  have hmemP : ∀ p : Finset K.V × Finset K.V,
      p ∈ P ↔ (p.1 ∈ N ∧ p.2 ∈ N ∧ Adj K lab p.1 p.2) := by
    intro p
    rw [hPdef, mem_filter, Finset.mem_product]
    tauto
  have hPcard : P.card = ∑ σ ∈ N, deg K lab σ := by
    rw [hPdef, card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [deg, card_eq_sum_ones, Finset.sum_filter]
  have h4 : 4 ∣ P.card := by
    refine card_four_dvd_of_klein (σ := Prod.swap)
      (τ := fun p => (K.negF p.1, K.negF p.2)) P ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [hmemP] at hp ⊢
      exact ⟨hp.2.1, hp.1, adj_symm hp.2.2⟩
    · intro p hp
      rw [hmemP] at hp ⊢
      refine ⟨mem_nodes.mpr (isNode_negF hanti (mem_nodes.mp hp.1)),
        mem_nodes.mpr (isNode_negF hanti (mem_nodes.mp hp.2.1)), adj_negF hanti hp.2.2⟩
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.ext (negF_negF p.1) (negF_negF p.2)
    · intro p _
      rfl
    · intro p hp
      rw [hmemP] at hp
      intro hcc
      have h12 : p.1 = p.2 := by
        have hh := congrArg Prod.fst hcc
        simp only [Prod.fst_swap] at hh
        exact hh.symm
      exact adj_irrefl (h12 ▸ hp.2.2)
    · intro p hp
      rw [hmemP] at hp
      intro hcc
      have h1 : K.negF p.1 = p.1 := by
        have := congrArg Prod.fst hcc
        simpa using this
      exact negF_ne_self (mem_nodes.mp hp.1).1 h1
    · intro p hp
      rw [hmemP] at hp
      intro hcc
      have h1 : K.negF p.2 = p.1 := by
        have := congrArg Prod.fst hcc
        simpa using this
      have h2 : K.negF p.1 = p.2 := by
        have := congrArg Prod.snd hcc
        simpa using this
      apply adj_card_ne hp.2.2
      rw [← h1, ← h2, card_negF, card_negF]
  obtain ⟨T, U, hsum, hcardodd, hpar⟩ :=
    freeInvolution_sum_odd_parity (ι := K.negF) (f := deg K lab) N
      (fun σ hσ => mem_nodes.mpr (isNode_negF hanti (mem_nodes.mp hσ)))
      (fun σ _ => negF_negF σ)
      (fun σ hσ => negF_ne_self (mem_nodes.mp hσ).1)
      (fun σ hσ => deg_negF hn hnz hbound hanti hcon (mem_nodes.mp hσ).1)
  have hoddset : N.filter (fun σ => deg K lab σ % 2 = 1) =
      ({({K.base} : Finset K.V), {K.neg K.base}} : Finset (Finset K.V)) := by
    ext σ
    simp only [mem_filter, mem_insert, mem_singleton, hNdef, mem_nodes]
    constructor
    · rintro ⟨hnode, hodd⟩
      exact (deg_odd_iff hn hnz hbound hcon hnode).mp hodd
    · rintro (rfl | rfl)
      · exact ⟨base_isNode hnz, by rw [deg_base hn hnz]⟩
      · exact ⟨neg_base_isNode hnz, by rw [deg_neg_base hn hnz]⟩
  have hne : ({K.base} : Finset K.V) ≠ ({K.neg K.base} : Finset K.V) := by
    intro hcc
    exact neg_base_ne (Finset.singleton_inj.mp hcc).symm
  have hcard2 : ({({K.base} : Finset K.V), {K.neg K.base}} : Finset (Finset K.V)).card = 2 := by
    rw [card_insert_of_notMem (by simp only [mem_singleton]; exact hne), card_singleton]
  rw [hoddset, hcard2] at hcardodd
  rw [hPcard, hsum] at h4
  obtain ⟨k, hk⟩ := h4
  omega

end FlagComplex

end GaloisForLFunctions.BorsukUlam
