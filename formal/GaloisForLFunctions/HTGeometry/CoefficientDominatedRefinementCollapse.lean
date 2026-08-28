import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.BigOperators.Option
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Coefficient-dominated refinement collapse

Explicit normalized deletion, prism contraction, presentation-core homology equivalence,
coefficient naturality, serial-pair quotient descent, relabelling invariance, and sharp
join-redundancy countermodel for finite coefficient-incidence complexes.
-/

open scoped DirectSum

noncomputable section

namespace CoefficientDominatedRefinementCollapse

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

variable (k : Type*) [Field k] (ι : Type*) [Fintype ι] [LinearOrder ι]
variable (E : Type*) [AddCommGroup E] [Module k E]

abbrev Simplex (p : ℕ) := {s : Finset ι // s.card = p}

abbrev AmbientChains (p : ℕ) := ⨁ _ : Simplex ι p, E

structure Coeff where
  obj : Finset ι → Submodule k E
  anti : ∀ {s t : Finset ι}, t ⊆ s → obj s ≤ obj t

variable (C : Coeff k ι E)

def chainSubmodule (p : ℕ) : Submodule k (AmbientChains ι E p) :=
  ⨅ s, (C.obj s.1).comap (DirectSum.component k (Simplex ι p) (fun _ => E) s)

abbrev Chains (p : ℕ) := chainSubmodule k ι E C p

def eraseSimplex {p : ℕ} (s : Simplex ι (p + 1)) (v : s.1) : Simplex ι p :=
  ⟨s.1.erase v.1, by
    rw [Finset.card_erase_of_mem v.2, s.2]
    omega⟩

def position (s : Finset ι) (v : ι) : ℕ :=
  (s.filter fun x => x < v).card

def faceMap {p : ℕ} (s : Simplex ι (p + 1)) (v : s.1) :
    E →ₗ[k] AmbientChains ι E p :=
  ((-1 : k) ^ position ι s.1 v.1) •
    DirectSum.lof k (Simplex ι p) (fun _ => E) (eraseSimplex ι s v)

def ambientBoundary {p : ℕ} :
    AmbientChains ι E (p + 1) →ₗ[k] AmbientChains ι E p :=
  DirectSum.toModule k _ _ fun s => ∑ v : s.1, faceMap k ι E s v

lemma position_erase_before {s : Finset ι} {i j : ι} (hi : i ∈ s) (hij : i < j) :
    position ι (s.erase i) j + 1 = position ι s j := by
  rw [position, position, Finset.filter_erase]
  rw [Finset.card_erase_of_mem]
  · have hc : 0 < (s.filter fun x => x < j).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩⟩
    omega
  · exact Finset.mem_filter.mpr ⟨hi, hij⟩

lemma position_erase_after {s : Finset ι} {i j : ι} (hji : j < i) :
    position ι (s.erase i) j = position ι s j := by
  rw [position, position, Finset.filter_erase]
  rw [Finset.erase_eq_self.mpr]
  exact fun hi => (not_lt_of_ge (le_of_lt hji)) (Finset.mem_filter.mp hi).2

lemma boundary_sign_swap {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    (-1 : k) ^ position ι s i * (-1 : k) ^ position ι (s.erase i) j =
      -((-1 : k) ^ position ι s j * (-1 : k) ^ position ι (s.erase j) i) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · rw [position_erase_after ι hij]
    have hpos := position_erase_before ι hi hij
    rw [← hpos, pow_succ]
    ring
  · rw [position_erase_after ι hji]
    have hpos := position_erase_before ι hj hji
    rw [← hpos, pow_succ]
    ring

abbrev DeletionPair {p : ℕ} (s : Simplex ι (p + 1 + 1)) :=
  Σ i : s.1, (eraseSimplex ι s i).1

def swapDeletionPair {p : ℕ} (s : Simplex ι (p + 1 + 1))
    (q : DeletionPair ι s) : DeletionPair ι s := by
  refine ⟨⟨q.2.1, (Finset.mem_erase.mp q.2.2).2⟩, ⟨q.1.1, ?_⟩⟩
  exact Finset.mem_erase.mpr ⟨(Ne.symm (Finset.mem_erase.mp q.2.2).1), q.1.2⟩

lemma swapDeletionPair_ne {p : ℕ} (s : Simplex ι (p + 1 + 1))
    (q : DeletionPair ι s) : swapDeletionPair ι s q ≠ q := by
  intro h
  have hfirst := congrArg (fun z : DeletionPair ι s => z.1.1) h
  exact (Finset.mem_erase.mp q.2.2).1 hfirst

lemma swapDeletionPair_involutive {p : ℕ} (s : Simplex ι (p + 1 + 1))
    (q : DeletionPair ι s) :
    swapDeletionPair ι s (swapDeletionPair ι s q) = q := by
  rcases q with ⟨i, j⟩
  apply Sigma.ext rfl
  rfl

def twiceErasedSimplex {p : ℕ} (s : Simplex ι (p + 1 + 1))
    (q : DeletionPair ι s) : Simplex ι p :=
  eraseSimplex ι (eraseSimplex ι s q.1) q.2

lemma twiceErasedSimplex_swap {p : ℕ} (s : Simplex ι (p + 1 + 1))
    (q : DeletionPair ι s) :
    twiceErasedSimplex ι s (swapDeletionPair ι s q) = twiceErasedSimplex ι s q := by
  apply Subtype.ext
  ext x
  simp [twiceErasedSimplex, eraseSimplex, swapDeletionPair, and_left_comm]

def twoFaceMap {p : ℕ} (s : Simplex ι (p + 1 + 1)) (q : DeletionPair ι s) :
    E →ₗ[k] AmbientChains ι E p :=
  ((-1 : k) ^ position ι s.1 q.1.1 *
      (-1 : k) ^ position ι (eraseSimplex ι s q.1).1 q.2.1) •
    DirectSum.lof k (Simplex ι p) (fun _ => E) (twiceErasedSimplex ι s q)

lemma twoFaceMap_swap_add {p : ℕ} (s : Simplex ι (p + 1 + 1))
    (q : DeletionPair ι s) :
    twoFaceMap k ι E s q + twoFaceMap k ι E s (swapDeletionPair ι s q) = 0 := by
  have hsign := boundary_sign_swap k ι (hi := q.1.2)
    (hj := (Finset.mem_erase.mp q.2.2).2) (hij := (Ne.symm (Finset.mem_erase.mp q.2.2).1))
  have hsign' :
      (-1 : k) ^ position ι s.1 q.1.1 *
          (-1 : k) ^ position ι (eraseSimplex ι s q.1).1 q.2.1 =
        -((-1 : k) ^ position ι s.1 (swapDeletionPair ι s q).1.1 *
          (-1 : k) ^ position ι (eraseSimplex ι s (swapDeletionPair ι s q).1).1
            (swapDeletionPair ι s q).2.1) := by
    simpa [eraseSimplex, swapDeletionPair] using hsign
  rw [twoFaceMap, twoFaceMap, twiceErasedSimplex_swap ι s q, hsign']
  module

lemma sum_twoFaceMap {p : ℕ} (s : Simplex ι (p + 1 + 1)) :
    ∑ q : DeletionPair ι s, twoFaceMap k ι E s q = 0 := by
  apply Finset.sum_involution (s := Finset.univ)
    (fun q _ => swapDeletionPair ι s q)
  · intro q _
    exact twoFaceMap_swap_add k ι E s q
  · intro q _ _
    exact swapDeletionPair_ne ι s q
  · simp
  · intro q _
    exact swapDeletionPair_involutive ι s q

lemma ambientBoundary_comp_lof {p : ℕ} (s : Simplex ι (p + 1 + 1)) :
    (ambientBoundary k ι E (p := p)).comp
        ((ambientBoundary k ι E (p := p + 1)).comp
          (DirectSum.lof k (Simplex ι (p + 1 + 1)) (fun _ => E) s)) =
      ∑ q : DeletionPair ι s, twoFaceMap k ι E s q := by
  rw [Fintype.sum_sigma]
  ext x t
  simp [ambientBoundary, faceMap, twoFaceMap, LinearMap.comp_apply,
    Finset.smul_sum, mul_smul, twiceErasedSimplex]

theorem ambientBoundary_sq {p : ℕ} :
    (ambientBoundary k ι E (p := p)).comp (ambientBoundary k ι E (p := p + 1)) = 0 := by
  apply DirectSum.linearMap_ext
  intro s
  rw [LinearMap.comp_assoc, ambientBoundary_comp_lof k ι E s, sum_twoFaceMap k ι E s]
  simp

lemma mem_chainSubmodule_iff {p : ℕ} (x : AmbientChains ι E p) :
    x ∈ chainSubmodule k ι E C p ↔
      ∀ s : Simplex ι p,
        DirectSum.component k (Simplex ι p) (fun _ => E) s x ∈ C.obj s.1 := by
  simp [chainSubmodule]

lemma sum_lof_component {p : ℕ} (x : AmbientChains ι E p) :
    (∑ s : Simplex ι p,
      DirectSum.lof k (Simplex ι p) (fun _ => E) s
        (DirectSum.component k (Simplex ι p) (fun _ => E) s x)) = x := by
  apply (DirectSum.linearEquivFunOnFintype k (Simplex ι p) (fun _ => E)).injective
  rw [map_sum]
  simp only [DirectSum.linearEquivFunOnFintype_lof]
  simp_rw [← DirectSum.apply_eq_component]
  exact Finset.univ_sum_single
    ((DirectSum.linearEquivFunOnFintype k (Simplex ι p) (fun _ => E)) x)

lemma ambientBoundary_mem_chainSubmodule {p : ℕ} {x : AmbientChains ι E (p + 1)}
    (hx : x ∈ chainSubmodule k ι E C (p + 1)) :
    ambientBoundary k ι E x ∈ chainSubmodule k ι E C p := by
  rw [mem_chainSubmodule_iff]
  intro t
  have hx' := (mem_chainSubmodule_iff k ι E C x).mp hx
  rw [← sum_lof_component k ι E x]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s _
  simp only [ambientBoundary, DirectSum.toModule_lof]
  rw [LinearMap.sum_apply]
  rw [map_sum]
  apply Submodule.sum_mem
  intro v _
  by_cases h : eraseSimplex ι s v = t
  · subst t
    simp [faceMap]
    exact C.obj (eraseSimplex ι s v).1 |>.smul_mem _
      (C.anti (Finset.erase_subset _ _) (hx' s))
  · have hcomp :
        DirectSum.component k (Simplex ι p) (fun _ => E) t
            (DirectSum.lof k (Simplex ι p) (fun _ => E) (eraseSimplex ι s v)
              (DirectSum.component k (Simplex ι (p + 1)) (fun _ => E) s x)) = 0 := by
      rw [DirectSum.component.of]
      simp [h]
    simp [faceMap, hcomp]

def boundary {p : ℕ} : Chains k ι E C (p + 1) →ₗ[k] Chains k ι E C p where
  toFun x := ⟨ambientBoundary k ι E x.1, ambientBoundary_mem_chainSubmodule k ι E C x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' a x := by
    ext
    simp

theorem boundary_sq {p : ℕ} :
    (boundary k ι E C (p := p)).comp (boundary k ι E C (p := p + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ambientBoundary k ι E (ambientBoundary k ι E x.1) = 0
  simpa [LinearMap.comp_apply] using
    LinearMap.congr_fun (ambientBoundary_sq k ι E (p := p)) x.1

structure TerminalPair (a star : ι) : Prop where
  anchor_lt_star : a < star
  below_anchor : ∀ x, x ≠ star → x ≤ a

def replaceStarSimplex {p : ℕ} (a star : ι) (s : Simplex ι p)
    (hstar : star ∈ s.1) (ha : a ∉ s.1) : Simplex ι p :=
  ⟨insert a (s.1.erase star), by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_erase_of_mem hstar, s.2]
      have hp : 0 < p := by
        rw [← s.2]
        exact Finset.card_pos.mpr ⟨star, hstar⟩
      omega
    · intro h
      exact ha (Finset.mem_of_mem_erase h)⟩

def addAnchorSimplex {p : ℕ} (a star : ι) (s : Simplex ι p)
    (hstar : star ∈ s.1) (ha : a ∉ s.1) : Simplex ι (p + 1) :=
  ⟨insert a s.1, by simp [Finset.card_insert_of_notMem ha, s.2]⟩

def collapseGenerator {p : ℕ} (a star : ι) (s : Simplex ι p) :
    E →ₗ[k] AmbientChains ι E p :=
  if hstar : star ∈ s.1 then
    if ha : a ∈ s.1 then 0
    else DirectSum.lof k (Simplex ι p) (fun _ => E) (replaceStarSimplex ι a star s hstar ha)
  else DirectSum.lof k (Simplex ι p) (fun _ => E) s

def collapseAmbient {p : ℕ} (a star : ι) :
    AmbientChains ι E p →ₗ[k] AmbientChains ι E p :=
  DirectSum.toModule k _ _ fun s => collapseGenerator k ι E a star s

def prismGenerator {p : ℕ} (a star : ι) (s : Simplex ι p) :
    E →ₗ[k] AmbientChains ι E (p + 1) :=
  if hstar : star ∈ s.1 then
    if ha : a ∈ s.1 then 0
    else ((-1 : k) ^ (p - 1)) •
      DirectSum.lof k (Simplex ι (p + 1)) (fun _ => E)
        (addAnchorSimplex ι a star s hstar ha)
  else 0

def prismAmbient {p : ℕ} (a star : ι) :
    AmbientChains ι E p →ₗ[k] AmbientChains ι E (p + 1) :=
  DirectSum.toModule k _ _ fun s => prismGenerator k ι E a star s

lemma position_star_of_terminalPair {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (s : Simplex ι p) (hs : star ∈ s.1) : position ι s.1 star = p - 1 := by
  have heq : s.1.filter (fun x => x < star) = s.1.erase star := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun hx => ⟨ne_of_lt hx.2, hx.1⟩
    · intro hx
      exact ⟨hx.2, lt_of_le_of_lt (T.below_anchor x hx.1) T.anchor_lt_star⟩
  rw [position, heq, Finset.card_erase_of_mem hs, s.2]

lemma position_anchor_of_terminalPair {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (s : Simplex ι (p + 1)) (ha : a ∈ s.1) (hs : star ∈ s.1) :
    position ι s.1 a = p - 1 := by
  have heq : s.1.filter (fun x => x < a) = (s.1.erase star).erase a := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro hx
      exact ⟨ne_of_lt hx.2, ne_of_lt (hx.2.trans T.anchor_lt_star), hx.1⟩
    · intro hx
      exact ⟨hx.2.2, lt_of_le_of_ne (T.below_anchor x hx.2.1) hx.1⟩
  rw [position, heq, Finset.card_erase_of_mem]
  · rw [Finset.card_erase_of_mem hs, s.2]
    omega
  · exact Finset.mem_erase.mpr ⟨T.anchor_lt_star.ne, ha⟩

lemma addAnchor_erase_anchor {p : ℕ} (a star : ι) (T : TerminalPair ι a star)
    (s : Simplex ι (p + 1)) (ha : a ∈ s.1) (hs : star ∈ s.1) :
    addAnchorSimplex ι a star (eraseSimplex ι s ⟨a, ha⟩)
      (by exact Finset.mem_erase.mpr ⟨T.anchor_lt_star.ne', hs⟩) (by simp [eraseSimplex]) = s := by
  apply Subtype.ext
  simp [addAnchorSimplex, eraseSimplex, Finset.insert_erase ha]

def insertSubtypeEquiv (a : ι) (s : Finset ι) (ha : a ∉ s) :
    {x // x ∈ insert a s} ≃ Option {x // x ∈ s} where
  toFun x := if h : x.1 = a then none
    else some ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left h⟩
  invFun x := x.elim ⟨a, Finset.mem_insert_self _ _⟩
    (fun y => ⟨y.1, Finset.mem_insert_of_mem y.2⟩)
  left_inv x := by
    dsimp
    split <;> rename_i h
    · apply Subtype.ext
      exact h.symm
    · rfl
  right_inv x := by
    cases x with
    | none => simp
    | some x =>
        have hne : x.1 ≠ a := by
          intro h
          exact ha (h ▸ x.2)
        simp [hne]

lemma sum_insert_subtype {M : Type*} [AddCommMonoid M] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (f : {x // x ∈ insert a s} → M) :
    (∑ x, f x) = f ⟨a, Finset.mem_insert_self _ _⟩ +
      ∑ x : {x // x ∈ s}, f ⟨x.1, Finset.mem_insert_of_mem x.2⟩ := by
  rw [← (insertSubtypeEquiv ι a s ha).symm.sum_comp f]
  simp [insertSubtypeEquiv]

lemma erase_addAnchor_anchor {p : ℕ} (a star : ι) (s : Simplex ι (p + 1))
    (hs : star ∈ s.1) (ha : a ∉ s.1) :
    eraseSimplex ι (addAnchorSimplex ι a star s hs ha)
      ⟨a, Finset.mem_insert_self _ _⟩ = s := by
  apply Subtype.ext
  simp [addAnchorSimplex, eraseSimplex, ha]

lemma erase_addAnchor_star {p : ℕ} (a star : ι) (T : TerminalPair ι a star)
    (s : Simplex ι (p + 1)) (hs : star ∈ s.1) (ha : a ∉ s.1) :
    eraseSimplex ι (addAnchorSimplex ι a star s hs ha)
      ⟨star, Finset.mem_insert_of_mem hs⟩ = replaceStarSimplex ι a star s hs ha := by
  apply Subtype.ext
  ext x
  simp only [addAnchorSimplex, eraseSimplex, replaceStarSimplex, Finset.mem_erase,
    Finset.mem_insert]
  constructor
  · intro hx
    exact Or.elim hx.2 (fun h => Or.inl h) (fun h => Or.inr ⟨hx.1, h⟩)
  · intro hx
    exact Or.elim hx
      (fun h => ⟨fun h' => T.anchor_lt_star.ne (h.symm.trans h'), Or.inl h⟩)
      (fun h => ⟨h.1, Or.inr h.2⟩)

lemma position_old_addAnchor {p : ℕ} (a star : ι) (T : TerminalPair ι a star)
    (s : Simplex ι (p + 1)) (hs : star ∈ s.1) (ha : a ∉ s.1)
    (v : s.1) (hv : v.1 ≠ star) :
    position ι (addAnchorSimplex ι a star s hs ha).1 v.1 =
      position ι s.1 v.1 := by
  rw [position, position]
  have hva : v.1 < a := lt_of_le_of_ne (T.below_anchor v.1 hv) (fun h => ha (h ▸ v.2))
  congr 1
  ext x
  simp only [addAnchorSimplex, Finset.mem_filter, Finset.mem_insert]
  constructor
  · intro hx
    rcases hx.1 with hxa | hxs
    · subst x
      exact (not_lt_of_ge hva.le hx.2).elim
    · exact ⟨hxs, hx.2⟩
  · exact fun hx => ⟨Or.inr hx.1, hx.2⟩

lemma erase_addAnchor_old {p : ℕ} (a star : ι) (s : Simplex ι (p + 1))
    (hs : star ∈ s.1) (ha : a ∉ s.1) (v : s.1) (hv : v.1 ≠ star) :
    eraseSimplex ι (addAnchorSimplex ι a star s hs ha)
        ⟨v.1, Finset.mem_insert_of_mem v.2⟩ =
      addAnchorSimplex ι a star (eraseSimplex ι s v)
        (Finset.mem_erase.mpr ⟨hv.symm, hs⟩) (by
          intro h
          exact ha (Finset.mem_of_mem_erase h)) := by
  apply Subtype.ext
  ext x
  simp only [addAnchorSimplex, eraseSimplex, Finset.mem_erase, Finset.mem_insert]
  aesop

theorem ambient_prism_identity_succ {p : ℕ} {a star : ι} (T : TerminalPair ι a star) :
    (ambientBoundary k ι E (p := p + 1)).comp
        (prismAmbient k ι E a star (p := p + 1)) +
        (prismAmbient k ι E a star (p := p)).comp
          (ambientBoundary k ι E (p := p)) =
      LinearMap.id - collapseAmbient k ι E a star := by
  apply DirectSum.linearMap_ext
  intro s
  by_cases hs : star ∈ s.1
  · by_cases ha : a ∈ s.1
    · ext x t
      simp [ambientBoundary, faceMap, prismAmbient, prismGenerator, collapseAmbient,
        collapseGenerator, LinearMap.comp_apply, hs, ha]
      rw [Finset.sum_eq_single ⟨a, ha⟩]
      · rw [position_anchor_of_terminalPair ι T s ha hs]
        have hadd := addAnchor_erase_anchor ι a star T s ha hs
        have hstarface : star ∈ (eraseSimplex ι s ⟨a, ha⟩).1 := by
          exact Finset.mem_erase.mpr ⟨T.anchor_lt_star.ne', hs⟩
        have hanchorface : a ∉ (eraseSimplex ι s ⟨a, ha⟩).1 := by
          simp [eraseSimplex]
        simp only [dif_pos hstarface, dif_neg hanchorface]
        rw [hadd]
        have hsign : (-1 : k) ^ (p - 1) * (-1 : k) ^ (p - 1) = 1 := by
          rw [← mul_pow]
          simp
        simp [smul_smul, hsign]
      · intro v hv hne
        have hva : v.1 ≠ a := by
          intro h
          apply hne
          exact Subtype.ext h
        by_cases hvs : v.1 = star
        · simp [eraseSimplex, hvs]
        · simp [eraseSimplex, hs, ha, Ne.symm hva, Ne.symm hvs]
      · simp
    · apply LinearMap.ext
      intro x
      simp [ambientBoundary, faceMap, prismAmbient, prismGenerator, collapseAmbient,
        collapseGenerator, LinearMap.comp_apply, hs, ha, Finset.smul_sum]
      change
        (∑ v : {v // v ∈ insert a s.1},
          (-1 : k) ^ p •
            (-1 : k) ^ position ι (addAnchorSimplex ι a star s hs ha).1 v.1 •
              DirectSum.lof k (Simplex ι (p + 1)) (fun _ => E)
                (eraseSimplex ι (addAnchorSimplex ι a star s hs ha) v) x) + _ = _
      rw [sum_insert_subtype ι a s.1 ha]
      have hposAnchor :
          position ι (addAnchorSimplex ι a star s hs ha).1 a = p := by
        simpa using position_anchor_of_terminalPair ι T
          (addAnchorSimplex ι a star s hs ha) (Finset.mem_insert_self _ _)
            (Finset.mem_insert_of_mem hs)
      rw [hposAnchor]
      simp [eraseSimplex, addAnchorSimplex, ha]
      have hanchorSign : (-1 : k) ^ p * (-1 : k) ^ p = 1 := by
        rw [← mul_pow]
        simp
      simp only [smul_smul, hanchorSign, one_smul]
      abel_nf
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_eq_single ⟨star, hs⟩]
      · have hposStar : position ι (insert a s.1) star = p + 1 := by
          simpa [addAnchorSimplex] using position_star_of_terminalPair ι T
            (addAnchorSimplex ι a star s hs ha) (Finset.mem_insert_of_mem hs)
        have hidxStar :
            (⟨(insert a s.1).erase star, by
              rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem hs),
                Finset.card_insert_of_notMem ha, s.2]
              omega⟩ : Simplex ι (p + 1)) =
              replaceStarSimplex ι a star s hs ha := by
          apply Subtype.ext
          ext y
          simp only [replaceStarSimplex, Finset.mem_erase, Finset.mem_insert]
          constructor
          · intro hy
            exact Or.elim hy.2 (fun h => Or.inl h) (fun h => Or.inr ⟨hy.1, h⟩)
          · intro hy
            exact Or.elim hy
              (fun h => ⟨fun h' => T.anchor_lt_star.ne (h.symm.trans h'), Or.inl h⟩)
              (fun h => ⟨h.1, Or.inr h.2⟩)
        rw [hposStar, hidxStar]
        have hstarSign : (-1 : k) ^ p * (-1 : k) ^ (p + 1) = -1 := by
          rw [pow_succ, ← mul_assoc, ← mul_pow]
          simp
        simp [hstarSign]
      · intro v hv_mem hne
        have hvstar : v.1 ≠ star := by
          intro h
          apply hne
          exact Subtype.ext h
        have hp : 0 < p := by
          have hc : 0 < (s.1.erase star).card :=
            Finset.card_pos.mpr ⟨v.1, Finset.mem_erase.mpr ⟨hvstar, v.2⟩⟩
          rw [Finset.card_erase_of_mem hs, s.2] at hc
          omega
        have hposOld := position_old_addAnchor ι a star T s hs ha v hvstar
        have hposOld' : position ι (insert a s.1) v.1 = position ι s.1 v.1 := by
          simpa [addAnchorSimplex] using hposOld
        have hidxOld' :
            (⟨(insert a s.1).erase v.1, by
              rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem v.2),
                Finset.card_insert_of_notMem ha, s.2]
              omega⟩ : Simplex ι (p + 1)) =
              ⟨insert a (s.1.erase v.1), by
                rw [Finset.card_insert_of_notMem]
                · rw [Finset.card_erase_of_mem v.2, s.2]
                  omega
                · intro h
                  exact ha (Finset.mem_of_mem_erase h)⟩ := by
          apply Subtype.ext
          ext y
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor <;> aesop
        have hstep : p - 1 + 1 = p := by omega
        have hsign : (-1 : k) ^ p = -((-1 : k) ^ (p - 1)) := by
          calc
            (-1 : k) ^ p = (-1 : k) ^ (p - 1 + 1) := by rw [hstep]
            _ = -((-1 : k) ^ (p - 1)) := by rw [pow_succ]; ring
        simp only [show ¬star = v.1 by exact Ne.symm hvstar, not_false_eq_true, hs,
          and_self, if_true]
        rw [hposOld', hidxOld']
        generalize_proofs
        simp only [neg_smul, one_smul, LinearMap.smul_apply, smul_smul]
        rw [← add_smul]
        have hcoeff :
            (-1 : k) ^ p * (-1 : k) ^ position ι s.1 v.1 +
              (-1 : k) ^ position ι s.1 v.1 * (-1 : k) ^ (p - 1) = 0 := by
          rw [hsign]
          ring
        rw [hcoeff, zero_smul]
      · simp
  · ext x t
    have hface (v : s.1) : star ∉ (eraseSimplex ι s v).1 := by
      intro h
      exact hs (Finset.mem_of_mem_erase h)
    simp [ambientBoundary, faceMap, prismAmbient, prismGenerator, collapseAmbient,
      collapseGenerator, LinearMap.comp_apply, hs, hface]

theorem ambient_prism_identity_zero {a star : ι} (T : TerminalPair ι a star) :
    (ambientBoundary k ι E (p := 0)).comp (prismAmbient k ι E a star (p := 0)) =
      LinearMap.id - collapseAmbient k ι E a star := by
  apply DirectSum.linearMap_ext
  intro s
  have hs : star ∉ s.1 := by
    intro h
    have hc := Finset.card_pos.mpr ⟨star, h⟩
    rw [s.2] at hc
    omega
  ext x t
  simp [ambientBoundary, prismAmbient, prismGenerator, collapseAmbient,
    collapseGenerator, LinearMap.comp_apply, hs]

def IsDominated (a star : ι) : Prop :=
  ∀ s : Finset ι, star ∈ s → C.obj s ≤ C.obj (insert a s)

lemma lof_mem_chainSubmodule {p : ℕ} (s : Simplex ι p) {x : E}
    (hx : x ∈ C.obj s.1) :
    DirectSum.lof k (Simplex ι p) (fun _ => E) s x ∈ chainSubmodule k ι E C p := by
  rw [mem_chainSubmodule_iff]
  intro t
  by_cases h : s = t
  · subst t
    simpa using hx
  · rw [DirectSum.component.of]
    simp [h]

lemma collapseAmbient_mem_chainSubmodule {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    {x : AmbientChains ι E p} (hx : x ∈ chainSubmodule k ι E C p) :
    collapseAmbient k ι E a star x ∈ chainSubmodule k ι E C p := by
  have hx' := (mem_chainSubmodule_iff k ι E C x).mp hx
  rw [← sum_lof_component k ι E x]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [collapseAmbient, DirectSum.toModule_lof, collapseGenerator]
  split <;> rename_i hs
  · split <;> rename_i ha
    · exact Submodule.zero_mem _
    · apply lof_mem_chainSubmodule k ι E C
      have hy := D s.1 hs (hx' s)
      have hy' := C.anti (Finset.erase_subset star (insert a s.1)) hy
      have heq : (insert a s.1).erase star = insert a (s.1.erase star) := by
        ext y
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · intro hy
          exact Or.elim hy.2 (fun h => Or.inl h) (fun h => Or.inr ⟨hy.1, h⟩)
        · intro hy
          exact Or.elim hy
            (fun h => ⟨fun h' => T.anchor_lt_star.ne (h.symm.trans h'), Or.inl h⟩)
            (fun h => ⟨h.1, Or.inr h.2⟩)
      rw [heq] at hy'
      exact hy'
  · exact lof_mem_chainSubmodule k ι E C s (hx' s)

lemma prismAmbient_mem_chainSubmodule {p : ℕ} {a star : ι}
    (D : IsDominated k ι E C a star) {x : AmbientChains ι E p}
    (hx : x ∈ chainSubmodule k ι E C p) :
    prismAmbient k ι E a star x ∈ chainSubmodule k ι E C (p + 1) := by
  have hx' := (mem_chainSubmodule_iff k ι E C x).mp hx
  rw [← sum_lof_component k ι E x]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [prismAmbient, DirectSum.toModule_lof, prismGenerator]
  split <;> rename_i hs
  · split <;> rename_i ha
    · exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      apply lof_mem_chainSubmodule k ι E C
      exact D s.1 hs (hx' s)
  · exact Submodule.zero_mem _

def collapse {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) : Chains k ι E C p →ₗ[k] Chains k ι E C p where
  toFun x := ⟨collapseAmbient k ι E a star x.1,
    collapseAmbient_mem_chainSubmodule k ι E C T D x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

def prism {p : ℕ} {a star : ι} (D : IsDominated k ι E C a star) :
    Chains k ι E C p →ₗ[k] Chains k ι E C (p + 1) where
  toFun x := ⟨prismAmbient k ι E a star x.1,
    prismAmbient_mem_chainSubmodule k ι E C D x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

theorem prism_identity_succ {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    (boundary k ι E C (p := p + 1)).comp (prism k ι E C D (p := p + 1)) +
        (prism k ι E C D (p := p)).comp (boundary k ι E C (p := p)) =
      LinearMap.id - collapse k ι E C T D := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambient_prism_identity_succ k ι E T (p := p)) x.1

theorem prism_identity_zero {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    (boundary k ι E C (p := 0)).comp (prism k ι E C D (p := 0)) =
      LinearMap.id - collapse k ι E C T D := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambient_prism_identity_zero k ι E T) x.1

theorem ambient_collapse_comm_boundary_zero {a star : ι} (T : TerminalPair ι a star) :
    (ambientBoundary k ι E (p := 0)).comp
        (collapseAmbient k ι E a star (p := 1)) =
      (collapseAmbient k ι E a star (p := 0)).comp
        (ambientBoundary k ι E (p := 0)) := by
  have hHigh := ambient_prism_identity_succ k ι E T (p := 0)
  have hZero := ambient_prism_identity_zero k ι E T
  have hPHigh : collapseAmbient k ι E a star (p := 1) =
      LinearMap.id -
        ((ambientBoundary k ι E (p := 1)).comp (prismAmbient k ι E a star (p := 1)) +
          (prismAmbient k ι E a star (p := 0)).comp (ambientBoundary k ι E (p := 0))) := by
    apply (eq_sub_iff_add_eq).2
    rw [hHigh]
    abel
  have hPZero : collapseAmbient k ι E a star (p := 0) =
      LinearMap.id -
        (ambientBoundary k ι E (p := 0)).comp (prismAmbient k ι E a star (p := 0)) := by
    apply (eq_sub_iff_add_eq).2
    rw [hZero]
    abel
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [LinearMap.congr_fun hPHigh x,
    LinearMap.congr_fun hPZero (ambientBoundary k ι E x)]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, map_sub, map_add]
  have hsq := LinearMap.congr_fun (ambientBoundary_sq k ι E (p := 0))
    (prismAmbient k ι E a star x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hsq
  rw [hsq]
  abel

theorem ambient_collapse_comm_boundary_succ {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) :
    (ambientBoundary k ι E (p := p + 1)).comp
        (collapseAmbient k ι E a star (p := p + 2)) =
      (collapseAmbient k ι E a star (p := p + 1)).comp
        (ambientBoundary k ι E (p := p + 1)) := by
  have hHigh := ambient_prism_identity_succ k ι E T (p := p + 1)
  have hLow := ambient_prism_identity_succ k ι E T (p := p)
  have hPHigh : collapseAmbient k ι E a star (p := p + 2) =
      LinearMap.id -
        ((ambientBoundary k ι E (p := p + 2)).comp
            (prismAmbient k ι E a star (p := p + 2)) +
          (prismAmbient k ι E a star (p := p + 1)).comp
            (ambientBoundary k ι E (p := p + 1))) := by
    apply (eq_sub_iff_add_eq).2
    rw [hHigh]
    abel
  have hPLow : collapseAmbient k ι E a star (p := p + 1) =
      LinearMap.id -
        ((ambientBoundary k ι E (p := p + 1)).comp
            (prismAmbient k ι E a star (p := p + 1)) +
          (prismAmbient k ι E a star (p := p)).comp
            (ambientBoundary k ι E (p := p))) := by
    apply (eq_sub_iff_add_eq).2
    rw [hLow]
    abel
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [LinearMap.congr_fun hPHigh x,
    LinearMap.congr_fun hPLow (ambientBoundary k ι E x)]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, map_sub, map_add]
  have hsqHigh := LinearMap.congr_fun (ambientBoundary_sq k ι E (p := p + 1))
    (prismAmbient k ι E a star x)
  have hsqLow := LinearMap.congr_fun (ambientBoundary_sq k ι E (p := p)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hsqHigh hsqLow
  rw [hsqHigh, hsqLow]
  simp

theorem collapse_comm_boundary_zero {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    (boundary k ι E C (p := 0)).comp (collapse k ι E C T D (p := 1)) =
      (collapse k ι E C T D (p := 0)).comp (boundary k ι E C (p := 0)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambient_collapse_comm_boundary_zero k ι E T) x.1

theorem collapse_comm_boundary_succ {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    (boundary k ι E C (p := p + 1)).comp (collapse k ι E C T D (p := p + 2)) =
      (collapse k ι E C T D (p := p + 1)).comp
        (boundary k ι E C (p := p + 1)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambient_collapse_comm_boundary_succ k ι E T) x.1

lemma star_not_mem_replaceStarSimplex {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (s : Simplex ι p)
    (hstar : star ∈ s.1) (ha : a ∉ s.1) :
    star ∉ (replaceStarSimplex ι a star s hstar ha).1 := by
  simp [replaceStarSimplex, ne_of_gt T.anchor_lt_star]

theorem ambient_collapse_idempotent {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) :
    (collapseAmbient k ι E a star (p := p)).comp
        (collapseAmbient k ι E a star (p := p)) =
      collapseAmbient k ι E a star := by
  apply DirectSum.linearMap_ext k
  intro s
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, collapseAmbient, DirectSum.toModule_lof,
    collapseGenerator]
  split <;> rename_i hs
  · split <;> rename_i ha
    · simp
    · rw [DirectSum.toModule_lof]
      simp [star_not_mem_replaceStarSimplex ι T s hs ha]
  · rw [DirectSum.toModule_lof]
    simp [hs]

theorem collapse_idempotent {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    (collapse k ι E C T D (p := p)).comp (collapse k ι E C T D (p := p)) =
      collapse k ι E C T D := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambient_collapse_idempotent k ι E T) x.1

theorem collapse_comm_boundary (p : ℕ) {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    (boundary k ι E C (p := p)).comp (collapse k ι E C T D (p := p + 1)) =
      (collapse k ι E C T D (p := p)).comp (boundary k ι E C (p := p)) := by
  cases p with
  | zero => exact collapse_comm_boundary_zero k ι E C T D
  | succ p => exact collapse_comm_boundary_succ k ι E C T D (p := p)

def outgoing : (p : ℕ) → Chains k ι E C p →ₗ[k] Chains k ι E C (p - 1)
  | 0 => 0
  | p + 1 => boundary k ι E C (p := p)

def cycles (p : ℕ) : Submodule k (Chains k ι E C p) :=
  LinearMap.ker (outgoing k ι E C p)

def boundaries (p : ℕ) : Submodule k (Chains k ι E C p) :=
  LinearMap.range (boundary k ι E C (p := p))

theorem boundaries_le_cycles (p : ℕ) :
    boundaries k ι E C p ≤ cycles k ι E C p := by
  rintro _ ⟨x, rfl⟩
  cases p with
  | zero => simp [cycles, outgoing]
  | succ p =>
      rw [cycles, LinearMap.mem_ker]
      exact LinearMap.congr_fun (boundary_sq k ι E C (p := p)) x

def homologyBoundaries (p : ℕ) : Submodule k (cycles k ι E C p) :=
  (boundaries k ι E C p).comap (cycles k ι E C p).subtype

def homologyRel (p : ℕ) : Setoid (cycles k ι E C p) where
  r x y := x.1 - y.1 ∈ boundaries k ι E C p
  iseqv := ⟨by
      intro x
      simp,
    by
      intro x y h
      simpa [sub_eq_add_neg, add_comm] using (boundaries k ι E C p).neg_mem h,
    by
      intro x y z hxy hyz
      have hsum := (boundaries k ι E C p).add_mem hxy hyz
      convert hsum using 1 <;> abel⟩

abbrev Homology (p : ℕ) : Type _ := Quotient (homologyRel k ι E C p)

theorem collapse_mem_cycles {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    {x : Chains k ι E C p} (hx : x ∈ cycles k ι E C p) :
    collapse k ι E C T D x ∈ cycles k ι E C p := by
  cases p with
  | zero => simp [cycles, outgoing]
  | succ p =>
      rw [cycles, LinearMap.mem_ker] at hx ⊢
      change boundary k ι E C x = 0 at hx
      change boundary k ι E C (collapse k ι E C T D x) = 0
      have hcomm := LinearMap.congr_fun (collapse_comm_boundary k ι E C p T D) x
      simp only [LinearMap.comp_apply] at hcomm
      rw [hcomm, hx, map_zero]

def collapseCycles {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    cycles k ι E C p →ₗ[k] cycles k ι E C p where
  toFun x := ⟨collapse k ι E C T D x.1, collapse_mem_cycles k ι E C T D x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

theorem collapseCycles_preserves_homologyBoundaries {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    homologyBoundaries k ι E C p ≤
      (homologyBoundaries k ι E C p).comap (collapseCycles k ι E C T D) := by
  intro x hx
  change collapse k ι E C T D x.1 ∈ boundaries k ι E C p
  change x.1 ∈ boundaries k ι E C p at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨collapse k ι E C T D y, ?_⟩
  have hcomm := LinearMap.congr_fun (collapse_comm_boundary k ι E C p T D) y
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm, hy]

def homologyCollapse {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    Homology k ι E C p → Homology k ι E C p :=
  Quotient.map (collapseCycles k ι E C T D) fun x y h => by
    change collapse k ι E C T D x.1 - collapse k ι E C T D y.1 ∈
      boundaries k ι E C p
    rw [← map_sub]
    have hxy : x - y ∈ homologyBoundaries k ι E C p := h
    exact collapseCycles_preserves_homologyBoundaries k ι E C T D hxy

theorem sub_collapse_mem_boundaries {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    {x : Chains k ι E C p} (hx : x ∈ cycles k ι E C p) :
    x - collapse k ι E C T D x ∈ boundaries k ι E C p := by
  cases p with
  | zero =>
      refine ⟨prism k ι E C D x, ?_⟩
      simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (prism_identity_zero k ι E C T D) x
  | succ p =>
      refine ⟨prism k ι E C D x, ?_⟩
      have h := LinearMap.congr_fun (prism_identity_succ k ι E C T D (p := p)) x
      rw [cycles, LinearMap.mem_ker] at hx
      change boundary k ι E C x = 0 at hx
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply, hx, map_zero, add_zero] at h
      exact h

theorem homologyCollapse_eq_id {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    homologyCollapse k ι E C T D (p := p) = id := by
  apply funext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  apply Quotient.sound
  change collapse k ι E C T D x.1 - x.1 ∈ boundaries k ι E C p
  have hx := sub_collapse_mem_boundaries k ι E C T D x.2
  simpa [sub_eq_add_neg, add_comm] using (boundaries k ι E C p).neg_mem hx

def PresentationCore {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) (p : ℕ) : Submodule k (Chains k ι E C p) :=
  LinearMap.range (collapse k ι E C T D)

def coreInclusion {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    PresentationCore k ι E C T D p →ₗ[k] Chains k ι E C p :=
  (PresentationCore k ι E C T D p).subtype

def coreRetraction {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    Chains k ι E C p →ₗ[k] PresentationCore k ι E C T D p :=
  (collapse k ι E C T D).rangeRestrict

theorem coreRetraction_comp_coreInclusion {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    (coreRetraction k ι E C T D (p := p)).comp (coreInclusion k ι E C T D) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rcases x.2 with ⟨y, hy⟩
  change collapse k ι E C T D x.1 = x.1
  rw [← hy]
  exact LinearMap.congr_fun (collapse_idempotent k ι E C T D) y

theorem coreInclusion_comp_coreRetraction {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    (coreInclusion k ι E C T D).comp (coreRetraction k ι E C T D (p := p)) =
      collapse k ι E C T D := by
  rfl

def coreBoundary {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    PresentationCore k ι E C T D (p + 1) →ₗ[k]
      PresentationCore k ι E C T D p where
  toFun x := ⟨boundary k ι E C x.1, by
    rcases x.2 with ⟨y, hy⟩
    refine ⟨boundary k ι E C y, ?_⟩
    have hcomm := LinearMap.congr_fun (collapse_comm_boundary k ι E C p T D) y
    simp only [LinearMap.comp_apply] at hcomm
    rw [← hy]
    exact hcomm.symm⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

theorem coreBoundary_sq {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    (coreBoundary k ι E C T D (p := p)).comp
        (coreBoundary k ι E C T D (p := p + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (boundary_sq k ι E C (p := p)) x.1

def coreOutgoing {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    (p : ℕ) → PresentationCore k ι E C T D p →ₗ[k]
      PresentationCore k ι E C T D (p - 1)
  | 0 => 0
  | p + 1 => coreBoundary k ι E C T D (p := p)

def coreCycles {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) (p : ℕ) :
    Submodule k (PresentationCore k ι E C T D p) :=
  LinearMap.ker (coreOutgoing k ι E C T D p)

def coreBoundaries {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) (p : ℕ) :
    Submodule k (PresentationCore k ι E C T D p) :=
  LinearMap.range (coreBoundary k ι E C T D (p := p))

theorem coreBoundaries_le_coreCycles (p : ℕ) {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    coreBoundaries k ι E C T D p ≤ coreCycles k ι E C T D p := by
  rintro _ ⟨x, rfl⟩
  cases p with
  | zero => simp [coreCycles, coreOutgoing]
  | succ p =>
      rw [coreCycles, LinearMap.mem_ker]
      exact LinearMap.congr_fun (coreBoundary_sq k ι E C T D (p := p)) x

def coreHomologyRel {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) (p : ℕ) : Setoid (coreCycles k ι E C T D p) where
  r x y := x.1 - y.1 ∈ coreBoundaries k ι E C T D p
  iseqv := ⟨by
      intro x
      have hz := (coreBoundaries k ι E C T D p).zero_mem
      convert hz using 1
      exact sub_self x.1,
    by
      intro x y h
      change x.1 - y.1 ∈ LinearMap.range (coreBoundary k ι E C T D) at h
      change y.1 - x.1 ∈ LinearMap.range (coreBoundary k ι E C T D)
      rcases h with ⟨b, hb⟩
      refine ⟨-b, ?_⟩
      calc
        (coreBoundary k ι E C T D) (-b) = -(coreBoundary k ι E C T D b) :=
          map_neg (coreBoundary k ι E C T D) b
        _ = y.1 - x.1 := by rw [hb]; abel,
    by
      intro x y z hxy hyz
      have hsum := (coreBoundaries k ι E C T D p).add_mem hxy hyz
      convert hsum using 1 <;> abel⟩

abbrev CoreHomology {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) (p : ℕ) : Type _ :=
  Quotient (coreHomologyRel k ι E C T D p)

theorem coreInclusion_mem_cycles {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    {x : PresentationCore k ι E C T D p}
    (hx : x ∈ coreCycles k ι E C T D p) :
    x.1 ∈ cycles k ι E C p := by
  cases p with
  | zero => simp [cycles, outgoing]
  | succ p =>
      rw [coreCycles, LinearMap.mem_ker] at hx
      rw [cycles, LinearMap.mem_ker]
      change boundary k ι E C x.1 = 0
      exact congrArg Subtype.val hx

theorem coreRetraction_mem_coreCycles {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    {x : Chains k ι E C p} (hx : x ∈ cycles k ι E C p) :
    coreRetraction k ι E C T D x ∈ coreCycles k ι E C T D p := by
  cases p with
  | zero => simp [coreCycles, coreOutgoing]
  | succ p =>
      rw [cycles, LinearMap.mem_ker] at hx
      change boundary k ι E C x = 0 at hx
      rw [coreCycles, LinearMap.mem_ker]
      apply Subtype.ext
      change boundary k ι E C (collapse k ι E C T D x) = 0
      have hcomm := LinearMap.congr_fun (collapse_comm_boundary k ι E C p T D) x
      simp only [LinearMap.comp_apply] at hcomm
      rw [hcomm, hx, map_zero]

def coreInclusionCycles {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    coreCycles k ι E C T D p →ₗ[k] cycles k ι E C p where
  toFun x := ⟨x.1.1, coreInclusion_mem_cycles k ι E C T D x.2⟩
  map_add' x y := by
    ext
    rfl
  map_smul' c x := by
    ext
    rfl

def coreRetractionCycles {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    cycles k ι E C p →ₗ[k] coreCycles k ι E C T D p where
  toFun x := ⟨coreRetraction k ι E C T D x.1,
    coreRetraction_mem_coreCycles k ι E C T D x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (coreRetraction k ι E C T D) x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (coreRetraction k ι E C T D) c x.1

theorem coreInclusionCycles_respects {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    {x y : coreCycles k ι E C T D p}
    (h : coreHomologyRel k ι E C T D p x y) :
    homologyRel k ι E C p (coreInclusionCycles k ι E C T D x)
      (coreInclusionCycles k ι E C T D y) := by
  change x.1.1 - y.1.1 ∈ boundaries k ι E C p
  change x.1 - y.1 ∈ LinearMap.range (coreBoundary k ι E C T D) at h
  rcases h with ⟨b, hb⟩
  refine ⟨b.1, ?_⟩
  exact congrArg Subtype.val hb

theorem coreRetractionCycles_respects {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    {x y : cycles k ι E C p} (h : homologyRel k ι E C p x y) :
    coreHomologyRel k ι E C T D p (coreRetractionCycles k ι E C T D x)
      (coreRetractionCycles k ι E C T D y) := by
  change coreRetraction k ι E C T D x.1 - coreRetraction k ι E C T D y.1 ∈
    LinearMap.range (coreBoundary k ι E C T D)
  rcases h with ⟨b, hb⟩
  refine ⟨coreRetraction k ι E C T D b, ?_⟩
  apply Subtype.ext
  change boundary k ι E C (collapse k ι E C T D b) =
    collapse k ι E C T D x.1 - collapse k ι E C T D y.1
  have hcomm := LinearMap.congr_fun (collapse_comm_boundary k ι E C p T D) b
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm, hb, map_sub]

def coreHomologyInclusion {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    CoreHomology k ι E C T D p → Homology k ι E C p :=
  Quotient.map (coreInclusionCycles k ι E C T D)
    fun _ _ h => coreInclusionCycles_respects k ι E C T D h

def coreHomologyRetraction {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (D : IsDominated k ι E C a star) :
    Homology k ι E C p → CoreHomology k ι E C T D p :=
  Quotient.map (coreRetractionCycles k ι E C T D)
    fun _ _ h => coreRetractionCycles_respects k ι E C T D h

theorem coreHomologyRetraction_inclusion {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    coreHomologyRetraction k ι E C T D (p := p) ∘
      coreHomologyInclusion k ι E C T D = id := by
  apply funext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  change Quotient.mk (coreHomologyRel k ι E C T D p)
      (coreRetractionCycles k ι E C T D
        (coreInclusionCycles k ι E C T D x)) =
    Quotient.mk (coreHomologyRel k ι E C T D p) x
  have hcycle : coreRetractionCycles k ι E C T D
      (coreInclusionCycles k ι E C T D x) = x := by
    apply Subtype.ext
    apply Subtype.ext
    rcases x.1.2 with ⟨z, hz⟩
    change collapse k ι E C T D x.1.1 = x.1.1
    rw [← hz]
    exact LinearMap.congr_fun (collapse_idempotent k ι E C T D) z
  rw [hcycle]

theorem coreHomologyInclusion_retraction {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    coreHomologyInclusion k ι E C T D ∘
      coreHomologyRetraction k ι E C T D (p := p) = id := by
  apply funext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  apply Quotient.sound
  change collapse k ι E C T D x.1 - x.1 ∈ boundaries k ι E C p
  have hx := sub_collapse_mem_boundaries k ι E C T D x.2
  simpa [sub_eq_add_neg, add_comm] using (boundaries k ι E C p).neg_mem hx

def presentationCoreHomologyEquiv {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star) :
    CoreHomology k ι E C T D p ≃ Homology k ι E C p where
  toFun := coreHomologyInclusion k ι E C T D
  invFun := coreHomologyRetraction k ι E C T D
  left_inv q := congrFun (coreHomologyRetraction_inclusion k ι E C T D) q
  right_inv q := congrFun (coreHomologyInclusion_retraction k ι E C T D) q

variable (E' : Type*) [AddCommGroup E'] [Module k E']

structure CoeffMorphism (C' : Coeff k ι E') where
  map : E →ₗ[k] E'
  map_obj : ∀ s, C.obj s ≤ (C'.obj s).comap map

variable (C' : Coeff k ι E')

def ambientCoeffMap {p : ℕ} (F : CoeffMorphism k ι E C E' C') :
    AmbientChains ι E p →ₗ[k] AmbientChains ι E' p :=
  DirectSum.toModule k _ _ fun s =>
    (DirectSum.lof k (Simplex ι p) (fun _ => E') s).comp F.map

theorem ambientCoeffMap_comp_lof {p : ℕ} (F : CoeffMorphism k ι E C E' C')
    (s : Simplex ι p) :
    (ambientCoeffMap k ι E C E' C' F).comp
        (DirectSum.lof k (Simplex ι p) (fun _ => E) s) =
      (DirectSum.lof k (Simplex ι p) (fun _ => E') s).comp F.map := by
  apply LinearMap.ext
  intro x
  simp [ambientCoeffMap]

theorem ambientCoeffMap_mem_chainSubmodule {p : ℕ}
    (F : CoeffMorphism k ι E C E' C') {x : AmbientChains ι E p}
    (hx : x ∈ chainSubmodule k ι E C p) :
    ambientCoeffMap k ι E C E' C' F x ∈ chainSubmodule k ι E' C' p := by
  have hx' := (mem_chainSubmodule_iff k ι E C x).mp hx
  rw [← sum_lof_component k ι E x]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [ambientCoeffMap, DirectSum.toModule_lof]
  apply lof_mem_chainSubmodule k ι E' C'
  exact F.map_obj s.1 (hx' s)

def coeffMap {p : ℕ} (F : CoeffMorphism k ι E C E' C') :
    Chains k ι E C p →ₗ[k] Chains k ι E' C' p where
  toFun x := ⟨ambientCoeffMap k ι E C E' C' F x.1,
    ambientCoeffMap_mem_chainSubmodule k ι E C E' C' F x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

theorem ambientCoeffMap_comm_boundary {p : ℕ}
    (F : CoeffMorphism k ι E C E' C') :
    (ambientBoundary k ι E' (p := p)).comp
        (ambientCoeffMap k ι E C E' C' F (p := p + 1)) =
      (ambientCoeffMap k ι E C E' C' F (p := p)).comp
        (ambientBoundary k ι E (p := p)) := by
  apply DirectSum.linearMap_ext k
  intro s
  apply LinearMap.ext
  intro x
  simp [ambientBoundary, faceMap, ambientCoeffMap, LinearMap.comp_apply]

theorem coeffMap_comm_boundary {p : ℕ}
    (F : CoeffMorphism k ι E C E' C') :
    (boundary k ι E' C' (p := p)).comp
        (coeffMap k ι E C E' C' F (p := p + 1)) =
      (coeffMap k ι E C E' C' F (p := p)).comp
        (boundary k ι E C (p := p)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambientCoeffMap_comm_boundary k ι E C E' C' F) x.1

theorem ambientCoeffMap_comm_collapse {p : ℕ} {a star : ι}
    (F : CoeffMorphism k ι E C E' C') :
    (ambientCoeffMap k ι E C E' C' F (p := p)).comp
        (collapseAmbient k ι E a star) =
      (collapseAmbient k ι E' a star).comp
        (ambientCoeffMap k ι E C E' C' F (p := p)) := by
  apply DirectSum.linearMap_ext k
  intro s
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, collapseAmbient, DirectSum.toModule_lof,
    collapseGenerator]
  split <;> rename_i hs
  · split <;> rename_i ha
    · simp [ambientCoeffMap, hs, ha]
    · simp [ambientCoeffMap, hs, ha]
  · simp [ambientCoeffMap, hs]

theorem coeffMap_comm_collapse {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (D : IsDominated k ι E C a star)
    (D' : IsDominated k ι E' C' a star)
    (F : CoeffMorphism k ι E C E' C') :
    (coeffMap k ι E C E' C' F (p := p)).comp
        (collapse k ι E C T D (p := p)) =
      (collapse k ι E' C' T D' (p := p)).comp
        (coeffMap k ι E C E' C' F (p := p)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambientCoeffMap_comm_collapse k ι E C E' C' F
    (a := a) (star := star)) x.1

theorem ambientCoeffMap_comm_prism {p : ℕ} {a star : ι}
    (F : CoeffMorphism k ι E C E' C') :
    (ambientCoeffMap k ι E C E' C' F (p := p + 1)).comp
        (prismAmbient k ι E a star (p := p)) =
      (prismAmbient k ι E' a star (p := p)).comp
        (ambientCoeffMap k ι E C E' C' F (p := p)) := by
  apply DirectSum.linearMap_ext k
  intro s
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, prismAmbient, DirectSum.toModule_lof, prismGenerator]
  split <;> rename_i hs
  · split <;> rename_i ha
    · simp [ambientCoeffMap, hs, ha]
    · simp [ambientCoeffMap, hs, ha]
  · simp [ambientCoeffMap, hs]

theorem coeffMap_comm_prism {p : ℕ} {a star : ι}
    (D : IsDominated k ι E C a star) (D' : IsDominated k ι E' C' a star)
    (F : CoeffMorphism k ι E C E' C') :
    (coeffMap k ι E C E' C' F (p := p + 1)).comp (prism k ι E C D) =
      (prism k ι E' C' D').comp (coeffMap k ι E C E' C' F (p := p)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambientCoeffMap_comm_prism k ι E C E' C' F
    (a := a) (star := star)) x.1

def CoeffLE (P Q : Coeff k ι E) : Prop := ∀ s, P.obj s ≤ Q.obj s

def coefficientInclusion {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q) :
    CoeffMorphism k ι E P E Q where
  map := LinearMap.id
  map_obj s x hx := h s hx

def pairRel (P Q : Coeff k ι E) (h : CoeffLE k ι E P Q) (p : ℕ) :
    Setoid (Chains k ι E Q p) where
  r x y := x - y ∈ LinearMap.range
    (coeffMap k ι E P E Q (coefficientInclusion k ι E h) (p := p))
  iseqv := ⟨by
      intro x
      refine ⟨0, ?_⟩
      simp,
    by
      intro x y hxy
      rcases hxy with ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      calc
        coeffMap k ι E P E Q (coefficientInclusion k ι E h) (-z) =
            -coeffMap k ι E P E Q (coefficientInclusion k ι E h) z :=
          map_neg _ z
        _ = y - x := by rw [hz]; abel,
    by
      intro x y z hxy hyz
      rcases hxy with ⟨u, hu⟩
      rcases hyz with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      rw [map_add, hu, hv]
      abel⟩

abbrev PairQuotient (P Q : Coeff k ι E) (h : CoeffLE k ι E P Q) (p : ℕ) :=
  Quotient (pairRel k ι E P Q h p)

theorem pairRel_add {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q) {p : ℕ}
    {x₁ x₂ y₁ y₂ : Chains k ι E Q p}
    (hx : pairRel k ι E P Q h p x₁ x₂) (hy : pairRel k ι E P Q h p y₁ y₂) :
    pairRel k ι E P Q h p (x₁ + y₁) (x₂ + y₂) := by
  rcases hx with ⟨u, hu⟩
  rcases hy with ⟨v, hv⟩
  refine ⟨u + v, ?_⟩
  rw [map_add, hu, hv]
  abel

theorem pairRel_sub {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q) {p : ℕ}
    {x₁ x₂ y₁ y₂ : Chains k ι E Q p}
    (hx : pairRel k ι E P Q h p x₁ x₂) (hy : pairRel k ι E P Q h p y₁ y₂) :
    pairRel k ι E P Q h p (x₁ - y₁) (x₂ - y₂) := by
  rcases hx with ⟨u, hu⟩
  rcases hy with ⟨v, hv⟩
  refine ⟨u - v, ?_⟩
  rw [map_sub, hu, hv]
  abel

theorem pairBoundary_respects {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} {x y : Chains k ι E Q (p + 1)}
    (hxy : pairRel k ι E P Q h (p + 1) x y) :
    pairRel k ι E P Q h p (boundary k ι E Q x) (boundary k ι E Q y) := by
  rcases hxy with ⟨z, hz⟩
  refine ⟨boundary k ι E P z, ?_⟩
  have hcomm := LinearMap.congr_fun
    (coeffMap_comm_boundary k ι E P E Q (coefficientInclusion k ι E h) (p := p)) z
  simp only [LinearMap.comp_apply] at hcomm
  rw [← hcomm, hz, map_sub]

theorem pairCollapse_respects {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (DP : IsDominated k ι E P a star) (DQ : IsDominated k ι E Q a star)
    {x y : Chains k ι E Q p} (hxy : pairRel k ι E P Q h p x y) :
    pairRel k ι E P Q h p (collapse k ι E Q T DQ x) (collapse k ι E Q T DQ y) := by
  rcases hxy with ⟨z, hz⟩
  refine ⟨collapse k ι E P T DP z, ?_⟩
  have hcomm := LinearMap.congr_fun
    (coeffMap_comm_collapse k ι E P E Q T DP DQ
      (coefficientInclusion k ι E h) (p := p)) z
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm, hz, map_sub]

theorem pairPrism_respects {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} {a star : ι} (DP : IsDominated k ι E P a star)
    (DQ : IsDominated k ι E Q a star) {x y : Chains k ι E Q p}
    (hxy : pairRel k ι E P Q h p x y) :
    pairRel k ι E P Q h (p + 1) (prism k ι E Q DQ x) (prism k ι E Q DQ y) := by
  rcases hxy with ⟨z, hz⟩
  refine ⟨prism k ι E P DP z, ?_⟩
  have hcomm := LinearMap.congr_fun
    (coeffMap_comm_prism k ι E P E Q DP DQ
      (coefficientInclusion k ι E h) (p := p)) z
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm, hz, map_sub]

def pairBoundary {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q) {p : ℕ} :
    PairQuotient k ι E P Q h (p + 1) → PairQuotient k ι E P Q h p :=
  Quotient.map (boundary k ι E Q) fun _ _ hxy =>
    pairBoundary_respects k ι E h hxy

def pairCollapse {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (DP : IsDominated k ι E P a star) (DQ : IsDominated k ι E Q a star) :
    PairQuotient k ι E P Q h p → PairQuotient k ι E P Q h p :=
  Quotient.map (collapse k ι E Q T DQ) fun _ _ hxy =>
    pairCollapse_respects k ι E h T DP DQ hxy

def pairPrism {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} {a star : ι} (DP : IsDominated k ι E P a star)
    (DQ : IsDominated k ι E Q a star) :
    PairQuotient k ι E P Q h p → PairQuotient k ι E P Q h (p + 1) :=
  Quotient.map (prism k ι E Q DQ) fun _ _ hxy =>
    pairPrism_respects k ι E h DP DQ hxy

theorem pair_prism_identity_succ {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} {a star : ι} (T : TerminalPair ι a star)
    (DP : IsDominated k ι E P a star) (DQ : IsDominated k ι E Q a star)
    (q : PairQuotient k ι E P Q h (p + 1)) :
    Quotient.liftOn q
        (fun x => Quotient.mk (pairRel k ι E P Q h (p + 1))
          (boundary k ι E Q (prism k ι E Q DQ x) +
            prism k ι E Q DQ (boundary k ι E Q x)))
        (by
          intro x y hxy
          apply Quotient.sound
          exact pairRel_add k ι E h
            (pairBoundary_respects k ι E h (pairPrism_respects k ι E h DP DQ hxy))
            (pairPrism_respects k ι E h DP DQ (pairBoundary_respects k ι E h hxy))) =
      Quotient.liftOn q
        (fun x => Quotient.mk (pairRel k ι E P Q h (p + 1))
          (x - collapse k ι E Q T DQ x))
        (by
          intro x y hxy
          apply Quotient.sound
          exact pairRel_sub k ι E h hxy
            (pairCollapse_respects k ι E h T DP DQ hxy)) := by
  refine Quotient.inductionOn q ?_
  intro x
  apply congrArg (Quotient.mk (pairRel k ι E P Q h (p + 1)))
  exact LinearMap.congr_fun (prism_identity_succ k ι E Q T DQ (p := p)) x

theorem pair_prism_identity_zero {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {a star : ι} (T : TerminalPair ι a star)
    (DP : IsDominated k ι E P a star) (DQ : IsDominated k ι E Q a star)
    (q : PairQuotient k ι E P Q h 0) :
    Quotient.liftOn q
        (fun x => Quotient.mk (pairRel k ι E P Q h 0)
          (boundary k ι E Q (prism k ι E Q DQ x)))
        (by
          intro x y hxy
          apply Quotient.sound
          exact pairBoundary_respects k ι E h
            (pairPrism_respects k ι E h DP DQ hxy)) =
      Quotient.liftOn q
        (fun x => Quotient.mk (pairRel k ι E P Q h 0)
          (x - collapse k ι E Q T DQ x))
        (by
          intro x y hxy
          apply Quotient.sound
          exact pairRel_sub k ι E h hxy
            (pairCollapse_respects k ι E h T DP DQ hxy)) := by
  refine Quotient.inductionOn q ?_
  intro x
  apply congrArg (Quotient.mk (pairRel k ι E P Q h 0))
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (prism_identity_zero k ι E Q T DQ) x

def pairClass {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q) {p : ℕ} :
    Chains k ι E Q p → PairQuotient k ι E P Q h p :=
  Quotient.mk (pairRel k ι E P Q h p)

theorem pairClass_surjective {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} : Function.Surjective (pairClass k ι E h (p := p)) :=
  Quotient.mk_surjective

theorem pairClass_eq_zero_iff {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)
    {p : ℕ} (x : Chains k ι E Q p) :
    pairClass k ι E h x = pairClass k ι E h 0 ↔
      x ∈ LinearMap.range
        (coeffMap k ι E P E Q (coefficientInclusion k ι E h) (p := p)) := by
  constructor
  · intro hx
    have hrel := Quotient.exact hx
    change x - 0 ∈ LinearMap.range
      (coeffMap k ι E P E Q (coefficientInclusion k ι E h) (p := p)) at hrel
    simpa only [sub_zero] using hrel
  · intro hx
    apply Quotient.sound
    change x - 0 ∈ LinearMap.range
      (coeffMap k ι E P E Q (coefficientInclusion k ι E h) (p := p))
    simpa only [sub_zero] using hx

theorem ambientCoeffMap_inclusion_eq_id {P Q : Coeff k ι E}
    (h : CoeffLE k ι E P Q) {p : ℕ} :
    ambientCoeffMap k ι E P E Q (coefficientInclusion k ι E h) (p := p) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext k
  intro s
  apply LinearMap.ext
  intro x
  simp [ambientCoeffMap, coefficientInclusion]

theorem coefficientInclusion_injective {P Q : Coeff k ι E}
    (h : CoeffLE k ι E P Q) {p : ℕ} :
    Function.Injective (coeffMap k ι E P E Q (coefficientInclusion k ι E h)
      (p := p)) := by
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg Subtype.val hxy
  change ambientCoeffMap k ι E P E Q (coefficientInclusion k ι E h) x.1 =
    ambientCoeffMap k ι E P E Q (coefficientInclusion k ι E h) y.1 at hval
  rw [ambientCoeffMap_inclusion_eq_id k ι E h] at hval
  exact hval

structure SerialFormationCoefficients where
  K_M_over_L : Coeff k ι E
  F_L : Coeff k ι E
  F_ML : Coeff k ι E
  F_M_over_L : Coeff k ι E
  kernel_le_upstream : CoeffLE k ι E K_M_over_L F_L
  direct_le_retained : CoeffLE k ι E F_ML F_M_over_L
  eraseMap : CoeffMorphism k ι E F_L E F_ML
  erase_exact : ∀ p,
    LinearMap.range (coeffMap k ι E K_M_over_L E F_L
      (coefficientInclusion k ι E kernel_le_upstream) (p := p)) =
      LinearMap.ker (coeffMap k ι E F_L E F_ML eraseMap (p := p))
  erase_surjective : ∀ p,
    Function.Surjective (coeffMap k ι E F_L E F_ML eraseMap (p := p))

structure SerialDominatedRefinement {a star : ι}
    (S : SerialFormationCoefficients k ι E) : Prop where
  K_M_over_L : IsDominated k ι E S.K_M_over_L a star
  F_L : IsDominated k ι E S.F_L a star
  F_ML : IsDominated k ι E S.F_ML a star
  F_M_over_L : IsDominated k ι E S.F_M_over_L a star

structure SerialRefinementCertificate {a star : ι}
    (S : SerialFormationCoefficients k ι E) (T : TerminalPair ι a star)
    (D : SerialDominatedRefinement k ι E S (a := a) (star := star)) where
  kernelHomology : ∀ p,
    CoreHomology k ι E S.K_M_over_L T D.K_M_over_L p ≃
      Homology k ι E S.K_M_over_L p
  upstreamHomology : ∀ p,
    CoreHomology k ι E S.F_L T D.F_L p ≃ Homology k ι E S.F_L p
  directHomology : ∀ p,
    CoreHomology k ι E S.F_ML T D.F_ML p ≃ Homology k ι E S.F_ML p
  retainedHomology : ∀ p,
    CoreHomology k ι E S.F_M_over_L T D.F_M_over_L p ≃
      Homology k ι E S.F_M_over_L p
  eraseCollapseSquare : ∀ p,
    (coeffMap k ι E S.F_L E S.F_ML S.eraseMap (p := p)).comp
        (collapse k ι E S.F_L T D.F_L) =
      (collapse k ι E S.F_ML T D.F_ML).comp
        (coeffMap k ι E S.F_L E S.F_ML S.eraseMap (p := p))
  kernelInclusionCollapseSquare : ∀ p,
    (coeffMap k ι E S.K_M_over_L E S.F_L
        (coefficientInclusion k ι E S.kernel_le_upstream) (p := p)).comp
        (collapse k ι E S.K_M_over_L T D.K_M_over_L) =
      (collapse k ι E S.F_L T D.F_L).comp
        (coeffMap k ι E S.K_M_over_L E S.F_L
          (coefficientInclusion k ι E S.kernel_le_upstream) (p := p))
  retainedInclusionCollapseSquare : ∀ p,
    (coeffMap k ι E S.F_ML E S.F_M_over_L
        (coefficientInclusion k ι E S.direct_le_retained) (p := p)).comp
        (collapse k ι E S.F_ML T D.F_ML) =
      (collapse k ι E S.F_M_over_L T D.F_M_over_L).comp
        (coeffMap k ι E S.F_ML E S.F_M_over_L
          (coefficientInclusion k ι E S.direct_le_retained) (p := p))
  quotientCollapse : ∀ p,
    PairQuotient k ι E S.F_ML S.F_M_over_L S.direct_le_retained p →
      PairQuotient k ι E S.F_ML S.F_M_over_L S.direct_le_retained p
  quotientPrism : ∀ p,
    PairQuotient k ι E S.F_ML S.F_M_over_L S.direct_le_retained p →
      PairQuotient k ι E S.F_ML S.F_M_over_L S.direct_le_retained (p + 1)

def serial_refinement_certificate {a star : ι}
    (S : SerialFormationCoefficients k ι E) (T : TerminalPair ι a star)
    (D : SerialDominatedRefinement k ι E S (a := a) (star := star)) :
    SerialRefinementCertificate k ι E S T D where
  kernelHomology p := presentationCoreHomologyEquiv k ι E S.K_M_over_L T D.K_M_over_L
  upstreamHomology p := presentationCoreHomologyEquiv k ι E S.F_L T D.F_L
  directHomology p := presentationCoreHomologyEquiv k ι E S.F_ML T D.F_ML
  retainedHomology p := presentationCoreHomologyEquiv k ι E S.F_M_over_L T D.F_M_over_L
  eraseCollapseSquare p := coeffMap_comm_collapse k ι E S.F_L E S.F_ML T
    D.F_L D.F_ML S.eraseMap (p := p)
  kernelInclusionCollapseSquare p := coeffMap_comm_collapse k ι E S.K_M_over_L E
    S.F_L T D.K_M_over_L D.F_L (coefficientInclusion k ι E S.kernel_le_upstream)
      (p := p)
  retainedInclusionCollapseSquare p := coeffMap_comm_collapse k ι E S.F_ML E
    S.F_M_over_L T D.F_ML D.F_M_over_L
      (coefficientInclusion k ι E S.direct_le_retained) (p := p)
  quotientCollapse p := pairCollapse k ι E S.direct_le_retained T D.F_ML D.F_M_over_L
  quotientPrism p := pairPrism k ι E S.direct_le_retained D.F_ML D.F_M_over_L

def iteratedEquiv {H : ℕ → Type*} (step : ∀ n, H (n + 1) ≃ H n) :
    ∀ n, H n ≃ H 0
  | 0 => Equiv.refl _
  | n + 1 => (step n).trans (iteratedEquiv step n)

theorem iterated_legal_refinements_preserve_homology {H : ℕ → Type*}
    (step : ∀ n, H (n + 1) ≃ H n) (n : ℕ) : Nonempty (H n ≃ H 0) :=
  ⟨iteratedEquiv step n⟩

structure MarkPolicy where
  forgettable : ι → Prop

def IsLegalRefinement {a star : ι} (P : MarkPolicy ι) : Prop :=
  IsDominated k ι E C a star ∧ P.forgettable star

def presentation_invariant_of_legal_refinement {p : ℕ} {a star : ι}
    (T : TerminalPair ι a star) (P : MarkPolicy ι)
    (h : IsLegalRefinement k ι E C P (a := a) (star := star)) :
    CoreHomology k ι E C T h.1 p ≃ Homology k ι E C p :=
  presentationCoreHomologyEquiv k ι E C T h.1

theorem marked_refinement_requires_forgetfulness {a star : ι} (P : MarkPolicy ι)
    (h : IsLegalRefinement k ι E C P (a := a) (star := star)) :
    P.forgettable star := h.2

def coordinateSum (n : ℕ) : (Fin n → k) →ₗ[k] k where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem coordinateSum_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (coordinateSum k n) := by
  intro y
  refine ⟨Pi.single (0 : Fin n) y, ?_⟩
  simp [coordinateSum]

theorem coordinateSum_ker_finrank (n : ℕ) [NeZero n] :
    Module.finrank k (LinearMap.ker (coordinateSum k n)) = n - 1 := by
  have hrange : LinearMap.range (coordinateSum k n) = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (coordinateSum_surjective k n)
  have hdim := LinearMap.finrank_range_add_finrank_ker (coordinateSum k n)
  rw [hrange] at hdim
  rw [finrank_top, Module.finrank_self] at hdim
  simp only [Module.finrank_fin_fun] at hdim
  omega

namespace JoinRedundancyCountermodel

abbrev Plane := ℚ × ℚ

def e₁ : Plane := (1, 0)
def e₂ : Plane := (0, 1)
def e₃ : Plane := (1, 1)

def W₁ : Submodule ℚ Plane := ℚ ∙ e₁
def W₂ : Submodule ℚ Plane := ℚ ∙ e₂
def W₃ : Submodule ℚ Plane := ℚ ∙ e₃

theorem old_join_eq_top : W₁ ⊔ W₂ = ⊤ := by
  apply top_unique
  rintro ⟨x, y⟩ _
  rw [Submodule.mem_sup]
  refine ⟨x • e₁, ?_, y • e₂, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e₁))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e₂))
  · ext <;> simp [e₁, e₂]

theorem enlarged_join_eq_top : (W₁ ⊔ W₂) ⊔ W₃ = ⊤ := by
  rw [old_join_eq_top, top_sup_eq]

theorem third_leg_not_le_first : ¬W₃ ≤ W₁ := by
  intro h
  have he₃ : e₃ ∈ W₃ := Submodule.subset_span (Set.mem_singleton e₃)
  have hmem := h he₃
  change e₃ ∈ ℚ ∙ e₁ at hmem
  rw [Submodule.mem_span_singleton] at hmem
  rcases hmem with ⟨c, hc⟩
  have hsecond := congrArg Prod.snd hc
  simp [e₁, e₃] at hsecond

theorem third_leg_not_le_second : ¬W₃ ≤ W₂ := by
  intro h
  have he₃ : e₃ ∈ W₃ := Submodule.subset_span (Set.mem_singleton e₃)
  have hmem := h he₃
  change e₃ ∈ ℚ ∙ e₂ at hmem
  rw [Submodule.mem_span_singleton] at hmem
  rcases hmem with ⟨c, hc⟩
  have hfirst := congrArg Prod.fst hc
  simp [e₂, e₃] at hfirst

theorem two_leg_H0_finrank :
    Module.finrank ℚ (LinearMap.ker (coordinateSum ℚ 2)) = 1 := by
  simpa using coordinateSum_ker_finrank ℚ 2

theorem three_leg_H0_finrank :
    Module.finrank ℚ (LinearMap.ker (coordinateSum ℚ 3)) = 2 := by
  simpa using coordinateSum_ker_finrank ℚ 3

theorem join_redundancy_creates_charge :
    W₁ ⊔ W₂ = (W₁ ⊔ W₂) ⊔ W₃ ∧
      Module.finrank ℚ (LinearMap.ker (coordinateSum ℚ 2)) = 1 ∧
      Module.finrank ℚ (LinearMap.ker (coordinateSum ℚ 3)) = 2 ∧
      ¬W₃ ≤ W₁ ∧ ¬W₃ ≤ W₂ := by
  exact ⟨old_join_eq_top.trans enlarged_join_eq_top.symm,
    two_leg_H0_finrank, three_leg_H0_finrank,
    third_leg_not_le_first, third_leg_not_le_second⟩

end JoinRedundancyCountermodel

variable (κ : Type*) [Fintype κ] [LinearOrder κ]

def relabelSimplex (e : ι ≃o κ) (p : ℕ) : Simplex ι p ≃ Simplex κ p where
  toFun s := ⟨s.1.map e.toEquiv.toEmbedding, by simp [s.2]⟩
  invFun s := ⟨s.1.map e.symm.toEquiv.toEmbedding, by simp [s.2]⟩
  left_inv s := by
    apply Subtype.ext
    ext x
    simp
  right_inv s := by
    apply Subtype.ext
    ext x
    simp

def ambientRelabel (e : ι ≃o κ) (p : ℕ) :
    AmbientChains ι E p ≃ₗ[k] AmbientChains κ E p :=
  DirectSum.lequivCongrLeft k (relabelSimplex ι κ e p)

def relabelVertex (e : ι ≃o κ) {p : ℕ} (s : Simplex ι p) (v : s.1) :
    (relabelSimplex ι κ e p s).1 :=
  ⟨e v.1, by simp [relabelSimplex, v.2]⟩

def relabelVertexEquiv (e : ι ≃o κ) {p : ℕ} (s : Simplex ι p) :
    s.1 ≃ (relabelSimplex ι κ e p s).1 where
  toFun := relabelVertex ι κ e s
  invFun w := ⟨e.symm w.1, by simpa [relabelSimplex] using w.2⟩
  left_inv v := by
    apply Subtype.ext
    simp [relabelVertex]
  right_inv w := by
    apply Subtype.ext
    simp [relabelVertex]

theorem position_relabel (e : ι ≃o κ) {p : ℕ} (s : Simplex ι (p + 1))
    (v : s.1) :
    position κ (relabelSimplex ι κ e (p + 1) s)
        (relabelVertex ι κ e s v) = position ι s v := by
  simp only [position]
  calc
    Finset.card {x ∈ (relabelSimplex ι κ e (p + 1) s).1 |
        x < (relabelVertex ι κ e s v).1} =
        Finset.card (({x ∈ s.1 | x < v.1}).map e.toEquiv.toEmbedding) := by
      apply congrArg Finset.card
      ext x
      simp [relabelVertex, relabelSimplex]
      intro _
      simpa using
        (e.lt_iff_lt : e (e.symm x) < e v.1 ↔ e.symm x < v.1)
    _ = Finset.card {x ∈ s.1 | x < v.1} := Finset.card_map _

theorem eraseSimplex_relabel (e : ι ≃o κ) {p : ℕ}
    (s : Simplex ι (p + 1)) (v : s.1) :
    eraseSimplex κ (relabelSimplex ι κ e (p + 1) s)
        (relabelVertex ι κ e s v) =
      relabelSimplex ι κ e p (eraseSimplex ι s v) := by
  apply Subtype.ext
  change (Finset.map e.toEmbedding s.1).erase (e v.1) =
    Finset.map e.toEmbedding (s.1.erase v.1)
  simp

theorem ambientRelabel_lof (e : ι ≃o κ) {p : ℕ} (s : Simplex ι p) (x : E) :
    ambientRelabel k ι E κ e p
        (DirectSum.lof k (Simplex ι p) (fun _ => E) s x) =
      DirectSum.lof k (Simplex κ p) (fun _ => E)
        (relabelSimplex ι κ e p s) x := by
  rw [ambientRelabel]
  apply DirectSum.lequivCongrLeft_lof
  · rfl
  · exact ((relabelSimplex ι κ e p).symm_apply_apply s).symm

theorem ambientRelabel_comm_boundary (e : ι ≃o κ) {p : ℕ} :
    (ambientBoundary k κ E (p := p)).comp
        (ambientRelabel k ι E κ e (p + 1)).toLinearMap =
      (ambientRelabel k ι E κ e p).toLinearMap.comp
        (ambientBoundary k ι E (p := p)) := by
  apply DirectSum.linearMap_ext k
  intro s
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change ambientBoundary k κ E
      (ambientRelabel k ι E κ e (p + 1)
        (DirectSum.lof k (Simplex ι (p + 1)) (fun _ => E) s x)) =
    ambientRelabel k ι E κ e p
      (ambientBoundary k ι E
        (DirectSum.lof k (Simplex ι (p + 1)) (fun _ => E) s x))
  rw [ambientRelabel_lof k ι E κ e s x]
  simp only [ambientBoundary, DirectSum.toModule_lof]
  simp only [LinearMap.sum_apply]
  rw [map_sum]
  apply (Fintype.sum_equiv (relabelVertexEquiv ι κ e s)
    (fun v => ambientRelabel k ι E κ e p (faceMap k ι E s v x))
    (fun w => faceMap k κ E (relabelSimplex ι κ e (p + 1) s) w x) ?_).symm
  intro v
  change ambientRelabel k ι E κ e p (faceMap k ι E s v x) =
    faceMap k κ E (relabelSimplex ι κ e (p + 1) s)
      (relabelVertex ι κ e s v) x
  simp only [faceMap]
  rw [position_relabel ι κ e s v, eraseSimplex_relabel ι κ e s v]
  simp [ambientRelabel_lof]

def relabelCoeff (e : ι ≃o κ) : Coeff k κ E where
  obj s := C.obj (s.map e.symm.toEquiv.toEmbedding)
  anti h := C.anti (Finset.map_subset_map.mpr h)

theorem relabelCoeff_obj_relabelSimplex (e : ι ≃o κ) {p : ℕ}
    (s : Simplex ι p) :
    (relabelCoeff k ι E C κ e).obj
        (relabelSimplex ι κ e p s).1 = C.obj s.1 := by
  apply congrArg C.obj
  ext x
  simp [relabelSimplex]

theorem ambientRelabel_mem_chainSubmodule (e : ι ≃o κ) {p : ℕ}
    {x : AmbientChains ι E p} (hx : x ∈ chainSubmodule k ι E C p) :
    ambientRelabel k ι E κ e p x ∈
      chainSubmodule k κ E (relabelCoeff k ι E C κ e) p := by
  have hx' := (mem_chainSubmodule_iff k ι E C x).mp hx
  rw [← sum_lof_component k ι E x]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [ambientRelabel_lof k ι E κ e s]
  apply lof_mem_chainSubmodule k κ E (relabelCoeff k ι E C κ e)
  rw [relabelCoeff_obj_relabelSimplex k ι E C κ e s]
  exact hx' s

theorem ambientRelabel_symm_mem_chainSubmodule (e : ι ≃o κ) {p : ℕ}
    {x : AmbientChains κ E p}
    (hx : x ∈ chainSubmodule k κ E (relabelCoeff k ι E C κ e) p) :
    (ambientRelabel k ι E κ e p).symm x ∈ chainSubmodule k ι E C p := by
  have hx' := (mem_chainSubmodule_iff k κ E (relabelCoeff k ι E C κ e) x).mp hx
  rw [← sum_lof_component k κ E x]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro s _
  change ambientRelabel k κ E ι e.symm p
      (DirectSum.lof k (Simplex κ p) (fun _ => E) s (DirectSum.component k _ _ s x)) ∈
    chainSubmodule k ι E C p
  rw [ambientRelabel_lof k κ E ι e.symm s]
  apply lof_mem_chainSubmodule k ι E C
  have hs := hx' s
  change DirectSum.component k (Simplex κ p) (fun _ => E) s x ∈
    C.obj (s.1.map e.symm.toEquiv.toEmbedding) at hs
  exact hs

def chainRelabel (e : ι ≃o κ) (p : ℕ) :
    Chains k ι E C p ≃ₗ[k] Chains k κ E (relabelCoeff k ι E C κ e) p where
  toFun x := ⟨ambientRelabel k ι E κ e p x.1,
    ambientRelabel_mem_chainSubmodule k ι E C κ e x.2⟩
  invFun x := ⟨(ambientRelabel k ι E κ e p).symm x.1,
    ambientRelabel_symm_mem_chainSubmodule k ι E C κ e x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp
  left_inv x := by
    apply Subtype.ext
    exact (ambientRelabel k ι E κ e p).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact (ambientRelabel k ι E κ e p).apply_symm_apply x.1

theorem chainRelabel_comm_boundary (e : ι ≃o κ) {p : ℕ} :
    (boundary k κ E (relabelCoeff k ι E C κ e) (p := p)).comp
        (chainRelabel k ι E C κ e (p + 1)).toLinearMap =
      (chainRelabel k ι E C κ e p).toLinearMap.comp
        (boundary k ι E C (p := p)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (ambientRelabel_comm_boundary k ι E κ e (p := p)) x.1

end CoefficientDominatedRefinementCollapse
