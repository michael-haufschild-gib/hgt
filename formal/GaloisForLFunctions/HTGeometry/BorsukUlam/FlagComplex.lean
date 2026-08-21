import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Card
import Mathlib.Order.CompleteLattice.Finset

/-!
# Symmetric complexes aligned with a flag of hemispheres

`FlagComplex n` packages the combinatorial data of an antipodally symmetric triangulation of the
`n`-sphere that is aligned with a flag of hemispheres `H₀ ⊂ H₁ ⊂ ⋯ ⊂ H_n`.

Each vertex carries a *level* `lev v ≤ n` and a *sign* `sgn v`; the antipodal involution `neg`
preserves the level and flips the sign.  The hemisphere `± H_d` consists of the faces all of whose
vertices have level `≤ d`, with the level-`d` vertices carrying the sign `±`.  The *carrier* of a
face `σ` is therefore `±H_{cdim σ}` with `cdim σ = σ.sup lev` and sign `csgn σ`, and the alignment
axioms are:

* `card_le`   — a face of carrier dimension `d` has at most `d + 1` vertices;
* `facets_two` — a face with `card = cdim` (a "boundary-free" facet of its carrier hemisphere) is
  contained in exactly two faces of the same carrier dimension with one more vertex;
* `facets_one` — a face with `card = cdim + 1` (a top face of its carrier hemisphere, hence a
  boundary face of the next hemisphere) is contained in exactly one face of carrier dimension
  `cdim + 1` of each sign;
* `lev_zero`  — the only level-zero vertices are `base` and `neg base`, i.e. `H₀` is a point.
-/

namespace GaloisForLFunctions.BorsukUlam

open Finset

/-- An antipodally symmetric finite complex aligned with a flag of hemispheres of an
`n`-sphere. -/
structure FlagComplex (n : ℕ) where
  /-- Vertices. -/
  V : Type
  /-- Vertices have decidable equality. -/
  decEq : DecidableEq V
  /-- The antipodal involution. -/
  neg : V → V
  /-- The hemisphere level of a vertex. -/
  lev : V → ℕ
  /-- The hemisphere sign of a vertex. -/
  sgn : V → Bool
  /-- The faces of the complex; all are nonempty. -/
  faces : Finset (Finset V)
  /-- The vertex `H₀`. -/
  base : V
  neg_neg : ∀ v, neg (neg v) = v
  lev_le : ∀ v, lev v ≤ n
  lev_neg : ∀ v, lev (neg v) = lev v
  sgn_neg : ∀ v, sgn (neg v) = !sgn v
  faces_nonempty : ∀ σ ∈ faces, σ.Nonempty
  faces_down : ∀ σ ∈ faces, ∀ τ ⊆ σ, τ.Nonempty → τ ∈ faces
  faces_neg : ∀ σ ∈ faces, @Finset.image _ _ decEq neg σ ∈ faces
  coherent : ∀ σ ∈ faces, ∀ u ∈ σ, ∀ v ∈ σ, lev u = σ.sup lev → lev v = σ.sup lev → sgn u = sgn v
  card_le : ∀ σ ∈ faces, σ.card ≤ σ.sup lev + 1
  facets_two : ∀ σ ∈ faces, σ.card = σ.sup lev →
    ∃ τ₁ ∈ faces, ∃ τ₂ ∈ faces, τ₁ ≠ τ₂ ∧
      (σ ⊆ τ₁ ∧ τ₁.card = σ.card + 1 ∧ τ₁.sup lev = σ.sup lev) ∧
      (σ ⊆ τ₂ ∧ τ₂.card = σ.card + 1 ∧ τ₂.sup lev = σ.sup lev) ∧
      ∀ τ ∈ faces, σ ⊆ τ → τ.card = σ.card + 1 → τ.sup lev = σ.sup lev → τ = τ₁ ∨ τ = τ₂
  facets_one : ∀ σ ∈ faces, σ.card = σ.sup lev + 1 → σ.sup lev < n → ∀ ε : Bool,
    ∃ τ ∈ faces, (σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ τ.sup lev = σ.sup lev + 1 ∧
        ∃ v ∈ τ, lev v = τ.sup lev ∧ sgn v = ε) ∧
      ∀ τ' ∈ faces, σ ⊆ τ' → τ'.card = σ.card + 1 → τ'.sup lev = σ.sup lev + 1 →
        (∃ v ∈ τ', lev v = τ'.sup lev ∧ sgn v = ε) → τ' = τ
  base_face : ({base} : Finset V) ∈ faces
  base_lev : lev base = 0
  lev_zero : ∀ σ ∈ faces, ∀ v ∈ σ, lev v = 0 → v = base ∨ v = neg base

attribute [instance] FlagComplex.decEq

/-- A superset with one more element is an `insert`. -/
theorem exists_insert {α : Type*} [DecidableEq α] {c c' : Finset α} (hsub : c ⊆ c')
    (hcard : c'.card = c.card + 1) : ∃ ρ ∉ c, c' = insert ρ c := by
  have hd : (c' \ c).card = 1 := by
    rw [card_sdiff_of_subset hsub]
    omega
  obtain ⟨ρ, hρ⟩ := card_eq_one.mp hd
  have hρc' : ρ ∈ c' := by
    have : ρ ∈ c' \ c := by rw [hρ]; exact mem_singleton_self ρ
    exact (mem_sdiff.mp this).1
  have hρc : ρ ∉ c := by
    have : ρ ∈ c' \ c := by rw [hρ]; exact mem_singleton_self ρ
    exact (mem_sdiff.mp this).2
  refine ⟨ρ, hρc, ?_⟩
  ext z
  simp only [mem_insert]
  constructor
  · intro hz
    by_cases hzc : z ∈ c
    · exact Or.inr hzc
    · left
      have : z ∈ c' \ c := mem_sdiff.mpr ⟨hz, hzc⟩
      rw [hρ, mem_singleton] at this
      exact this
  · rintro (rfl | hz)
    · exact hρc'
    · exact hsub hz

/-- Between `A` and a `B` with two more elements there are exactly two intermediate sets. -/
theorem two_middles {α : Type*} [DecidableEq α] {A B : Finset α} (hAB : A ⊆ B)
    (hcard : B.card = A.card + 2) :
    ∃ p q : α, p ≠ q ∧ p ∈ B ∧ q ∈ B ∧ p ∉ A ∧ q ∉ A ∧
      ∀ ρ : Finset α, (A ⊆ ρ ∧ ρ ⊆ B ∧ ρ.card = A.card + 1) ↔
        (ρ = insert p A ∨ ρ = insert q A) := by
  have hd : (B \ A).card = 2 := by
    rw [card_sdiff_of_subset hAB]
    omega
  obtain ⟨p, q, hpq, hpqset⟩ := card_eq_two.mp hd
  have hpB : p ∈ B ∧ p ∉ A := by
    have : p ∈ B \ A := by rw [hpqset]; simp
    exact mem_sdiff.mp this
  have hqB : q ∈ B ∧ q ∉ A := by
    have : q ∈ B \ A := by rw [hpqset]; simp
    exact mem_sdiff.mp this
  refine ⟨p, q, hpq, hpB.1, hqB.1, hpB.2, hqB.2, fun ρ => ?_⟩
  constructor
  · rintro ⟨hAρ, hρB, hcρ⟩
    have hsub : ρ \ A ⊆ B \ A := sdiff_subset_sdiff hρB (le_refl A)
    have hcard1 : (ρ \ A).card = 1 := by
      rw [card_sdiff_of_subset hAρ]
      omega
    obtain ⟨r, hr⟩ := card_eq_one.mp hcard1
    have hrmem : r ∈ B \ A := by
      apply hsub
      rw [hr]
      exact mem_singleton_self r
    have hρeq : ρ = insert r A := by
      ext z
      simp only [mem_insert]
      constructor
      · intro hz
        by_cases hzA : z ∈ A
        · exact Or.inr hzA
        · left
          have : z ∈ ρ \ A := mem_sdiff.mpr ⟨hz, hzA⟩
          rw [hr, mem_singleton] at this
          exact this
      · intro hz
        have hrρ : r ∈ ρ := by
          have hmm : r ∈ ρ \ A := by rw [hr]; exact mem_singleton_self r
          exact (mem_sdiff.mp hmm).1
        rcases hz with hz | hz
        · rw [hz]; exact hrρ
        · exact hAρ hz
    rw [hpqset, mem_insert, mem_singleton] at hrmem
    rcases hrmem with rfl | rfl
    · exact Or.inl hρeq
    · exact Or.inr hρeq
  · rintro (rfl | rfl)
    · exact ⟨subset_insert _ _, insert_subset hpB.1 hAB, by
        rw [card_insert_of_notMem hpB.2]⟩
    · exact ⟨subset_insert _ _, insert_subset hqB.1 hAB, by
        rw [card_insert_of_notMem hqB.2]⟩

namespace FlagComplex

variable {n : ℕ} (K : FlagComplex n)

/-- Carrier dimension of a face. -/
def cdim (σ : Finset K.V) : ℕ := σ.sup K.lev

/-- Carrier sign of a face. -/
def csgn (σ : Finset K.V) : Bool := decide (∃ v ∈ σ, K.lev v = K.cdim σ ∧ K.sgn v = true)

/-- The antipodal image of a face. -/
def negF (σ : Finset K.V) : Finset K.V := σ.image K.neg

variable {K}

theorem neg_injective : Function.Injective K.neg :=
  Function.LeftInverse.injective K.neg_neg

theorem neg_ne (v : K.V) : K.neg v ≠ v := by
  intro h
  have := K.sgn_neg v
  rw [h] at this
  simp at this

theorem negF_mem {σ : Finset K.V} (h : σ ∈ K.faces) : K.negF σ ∈ K.faces :=
  K.faces_neg σ h

theorem card_negF (σ : Finset K.V) : (K.negF σ).card = σ.card :=
  card_image_of_injective _ neg_injective

theorem cdim_negF (σ : Finset K.V) : K.cdim (K.negF σ) = K.cdim σ := by
  simp only [cdim, negF]
  rw [Finset.sup_image]
  congr 1
  funext v
  exact K.lev_neg v

theorem mem_negF {σ : Finset K.V} {v : K.V} : v ∈ K.negF σ ↔ K.neg v ∈ σ := by
  simp only [negF, mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [K.neg_neg]
  · intro h
    exact ⟨K.neg v, h, K.neg_neg v⟩

theorem negF_negF (σ : Finset K.V) : K.negF (K.negF σ) = σ := by
  ext v
  rw [mem_negF, mem_negF, K.neg_neg]

theorem negF_subset {σ τ : Finset K.V} (h : σ ⊆ τ) : K.negF σ ⊆ K.negF τ :=
  image_subset_image h

theorem cdim_mono {σ τ : Finset K.V} (h : σ ⊆ τ) : K.cdim σ ≤ K.cdim τ :=
  Finset.sup_mono h

theorem exists_max {σ : Finset K.V} (h : σ.Nonempty) : ∃ v ∈ σ, K.lev v = K.cdim σ := by
  obtain ⟨v, hv, hveq⟩ := Finset.exists_mem_eq_sup σ h K.lev
  exact ⟨v, hv, hveq.symm⟩

theorem cdim_le (σ : Finset K.V) : K.cdim σ ≤ n := Finset.sup_le (fun v _ => K.lev_le v)

theorem lev_le_cdim {σ : Finset K.V} {v : K.V} (hv : v ∈ σ) : K.lev v ≤ K.cdim σ :=
  Finset.le_sup hv

theorem csgn_eq {σ : Finset K.V} (hσ : σ ∈ K.faces) {v : K.V} (hv : v ∈ σ)
    (hlev : K.lev v = K.cdim σ) : K.csgn σ = K.sgn v := by
  by_cases h : K.sgn v = true
  · rw [csgn, h]
    simp only [decide_eq_true_eq]
    exact ⟨v, hv, hlev, h⟩
  · have hfalse : K.sgn v = false := by simpa using h
    rw [csgn, hfalse]
    simp only [decide_eq_false_iff_not]
    rintro ⟨w, hw, hwlev, hwsgn⟩
    have hco := K.coherent σ hσ w hw v hv hwlev hlev
    rw [hwsgn, hfalse] at hco
    simp at hco

theorem csgn_negF {σ : Finset K.V} (hσ : σ ∈ K.faces) (hne : σ.Nonempty) :
    K.csgn (K.negF σ) = !K.csgn σ := by
  obtain ⟨v, hv, hvlev⟩ := exists_max hne
  have hvn : K.neg v ∈ K.negF σ := mem_negF.mpr (by rwa [K.neg_neg])
  have hlevn : K.lev (K.neg v) = K.cdim (K.negF σ) := by
    rw [K.lev_neg, cdim_negF]
    exact hvlev
  rw [csgn_eq (negF_mem hσ) hvn hlevn, csgn_eq hσ hv hvlev, K.sgn_neg]

theorem csgn_eq_iff {τ : Finset K.V} (hτ : τ ∈ K.faces) (ε : Bool) :
    K.csgn τ = ε ↔ ∃ v ∈ τ, K.lev v = K.cdim τ ∧ K.sgn v = ε := by
  obtain ⟨v, hv, hvlev⟩ := exists_max (K.faces_nonempty τ hτ)
  constructor
  · intro h
    exact ⟨v, hv, hvlev, by rw [← csgn_eq hτ hv hvlev, h]⟩
  · rintro ⟨w, hw, hwlev, hwsgn⟩
    rw [csgn_eq hτ hw hwlev, hwsgn]

theorem csgn_eq_of_subset {σ τ : Finset K.V} (hσ : σ ∈ K.faces) (hτ : τ ∈ K.faces)
    (hsub : σ ⊆ τ) (hcd : K.cdim σ = K.cdim τ) : K.csgn σ = K.csgn τ := by
  obtain ⟨v, hv, hvlev⟩ := exists_max (K.faces_nonempty σ hσ)
  rw [csgn_eq hσ hv hvlev, csgn_eq hτ (hsub hv) (by rw [hvlev, hcd])]

theorem facets_two_cdim {σ : Finset K.V} (hσ : σ ∈ K.faces) (h : σ.card = K.cdim σ) :
    ∃ τ₁ ∈ K.faces, ∃ τ₂ ∈ K.faces, τ₁ ≠ τ₂ ∧
      (σ ⊆ τ₁ ∧ τ₁.card = σ.card + 1 ∧ K.cdim τ₁ = K.cdim σ) ∧
      (σ ⊆ τ₂ ∧ τ₂.card = σ.card + 1 ∧ K.cdim τ₂ = K.cdim σ) ∧
      ∀ τ ∈ K.faces, σ ⊆ τ → τ.card = σ.card + 1 → K.cdim τ = K.cdim σ → τ = τ₁ ∨ τ = τ₂ :=
  K.facets_two σ hσ h

theorem facets_one_cdim {σ : Finset K.V} (hσ : σ ∈ K.faces) (h : σ.card = K.cdim σ + 1)
    (hlt : K.cdim σ < n) (ε : Bool) :
    ∃ τ ∈ K.faces, (σ ⊆ τ ∧ τ.card = σ.card + 1 ∧ K.cdim τ = K.cdim σ + 1 ∧ K.csgn τ = ε) ∧
      ∀ τ' ∈ K.faces, σ ⊆ τ' → τ'.card = σ.card + 1 → K.cdim τ' = K.cdim σ + 1 → K.csgn τ' = ε →
        τ' = τ := by
  obtain ⟨τ, hτ, ⟨hs, hc, hd, hex⟩, huniq⟩ := K.facets_one σ hσ h hlt ε
  refine ⟨τ, hτ, ⟨hs, hc, hd, (csgn_eq_iff hτ ε).mpr hex⟩, ?_⟩
  intro τ' hτ' hs' hc' hd' hsgn'
  exact huniq τ' hτ' hs' hc' hd' ((csgn_eq_iff hτ' ε).mp hsgn')

theorem neg_base_ne : K.neg K.base ≠ K.base := neg_ne K.base

theorem base_cdim : K.cdim ({K.base} : Finset K.V) = 0 := by
  simp [cdim, K.base_lev]

theorem neg_base_face : ({K.neg K.base} : Finset K.V) ∈ K.faces := by
  have := K.faces_neg _ K.base_face
  have himg : @Finset.image _ _ K.decEq K.neg ({K.base} : Finset K.V) = {K.neg K.base} := by
    simp
  rwa [himg] at this

theorem neg_base_cdim : K.cdim ({K.neg K.base} : Finset K.V) = 0 := by
  simp [cdim, K.lev_neg, K.base_lev]

end FlagComplex

end GaloisForLFunctions.BorsukUlam
