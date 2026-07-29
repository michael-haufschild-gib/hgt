import Mathlib

/-!
# Valuated spectral characters and temporal wall crossing

An observer cannot detect common phase. Its finite phase reporters are
therefore the integer characters of the projective spectral torus: finitely
supported integer combinations with total coefficient zero.

An arbitrary spectral jet assigns to each such character the first order at
which its exact energy relation breaks. The relations persisting through
order `r` form a decreasing saturated subgroup. Exact birth order obeys a
non-Archimedean law: cancellation can delay equal-depth characters, but a
sum can never be born before the shallower summand, and unequal depths
cannot cancel.

This file proves those claims for every label type. Finite support belongs
to the character, not to the ambient spectrum, so no finiteness assumption
on the spectral label set is needed.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Total integer charge of a finite phase character. -/
def integerCharacterCharge (I : Type*) : (I →₀ ℤ) →+ ℤ where
  toFun k := k.sum fun _ m => m
  map_zero' := by simp
  map_add' k l := by
    classical
    exact Finsupp.sum_add_index (by simp) (by simp)

/-- Characters of the projective phase torus: finite integer characters
whose total charge is zero, so global phase is invisible. -/
def projectiveCharacterLattice (I : Type*) : AddSubgroup (I →₀ ℤ) :=
  (integerCharacterCharge I).ker

/-- A finite-support projective phase character. -/
abbrev ProjectiveCharacter (I : Type*) :=
  projectiveCharacterLattice I

/-- The `n`th spectral jet paired with an integer phase character. -/
def spectralRelationJet {I : Type*} (jet : ℕ → I → ℂ) (n : ℕ) :
    (I →₀ ℤ) →+ ℂ where
  toFun k := k.sum fun i m => (m : ℂ) * jet n i
  map_zero' := by simp
  map_add' k l := by
    classical
    exact Finsupp.sum_add_index (by simp) (by
      intro i hi a b
      push_cast
      ring)

/-- Pair a spectral jet with a projective character. -/
def projectiveSpectralRelationJet {I : Type*}
    (jet : ℕ → I → ℂ) (n : ℕ) :
    ProjectiveCharacter I →+ ℂ :=
  (spectralRelationJet jet n).comp
    (projectiveCharacterLattice I).subtype

/-- A projective spectral relation persists through every order below `r`. -/
def spectralConstraintAtLeast {I : Type*}
    (jet : ℕ → I → ℂ) (r : ℕ) (k : ProjectiveCharacter I) : Prop :=
  ∀ n < r, projectiveSpectralRelationJet jet n k = 0

/-- Order-`r` persistent spectral relations form an additive subgroup. -/
def spectralConstraintFiltration {I : Type*}
    (jet : ℕ → I → ℂ) (r : ℕ) :
    AddSubgroup (ProjectiveCharacter I) where
  carrier := {k | spectralConstraintAtLeast jet r k}
  zero_mem' := by
    intro n hn
    exact map_zero _
  add_mem' := by
    intro k l hk hl n hn
    rw [map_add, hk n hn, hl n hn, add_zero]
  neg_mem' := by
    intro k hk n hn
    rw [map_neg, hk n hn, neg_zero]

@[simp] theorem mem_spectralConstraintFiltration_iff
    {I : Type*} (jet : ℕ → I → ℂ) (r : ℕ)
    (k : ProjectiveCharacter I) :
    k ∈ spectralConstraintFiltration jet r ↔
      ∀ n < r, projectiveSpectralRelationJet jet n k = 0 :=
  Iff.rfl

/-- The order-zero filtration contains every projective character. -/
theorem spectralConstraintFiltration_zero
    {I : Type*} (jet : ℕ → I → ℂ) :
    spectralConstraintFiltration jet 0 = ⊤ := by
  ext k
  simp

/-- Increasing resolution order can only remove spectral relations. -/
theorem spectralConstraintFiltration_antitone
    {I : Type*} (jet : ℕ → I → ℂ) :
    Antitone (spectralConstraintFiltration jet) := by
  intro r s hrs k hk n hn
  exact hk n (hn.trans_le hrs)

/-- The filtration law in minimum form: sums preserve the weaker of two
constraint depths. -/
theorem add_mem_spectralConstraintFiltration_min
    {I : Type*} {jet : ℕ → I → ℂ}
    {r s : ℕ} {k l : ProjectiveCharacter I}
    (hk : k ∈ spectralConstraintFiltration jet r)
    (hl : l ∈ spectralConstraintFiltration jet s) :
    k + l ∈ spectralConstraintFiltration jet (min r s) := by
  apply (spectralConstraintFiltration jet (min r s)).add_mem
  · exact spectralConstraintFiltration_antitone jet (min_le_left _ _) hk
  · exact spectralConstraintFiltration_antitone jet (min_le_right _ _) hl

/-- No nonzero integer multiple can hide a lower-order spectral breaking.
Each filtration layer is saturated in the projective character lattice. -/
theorem mem_spectralConstraintFiltration_of_zsmul_mem
    {I : Type*} {jet : ℕ → I → ℂ} {r : ℕ}
    {m : ℤ} (hm : m ≠ 0) {k : ProjectiveCharacter I}
    (hk : m • k ∈ spectralConstraintFiltration jet r) :
    k ∈ spectralConstraintFiltration jet r := by
  intro n hn
  have hmk := hk n hn
  rw [map_zsmul] at hmk
  rw [zsmul_eq_mul] at hmk
  exact (mul_eq_zero.mp hmk).resolve_left (Int.cast_ne_zero.mpr hm)

/-- A character is active when some spectral jet breaks it. -/
def SpectralCharacterActive {I : Type*}
    (jet : ℕ → I → ℂ) (k : ProjectiveCharacter I) : Prop :=
  ∃ n, projectiveSpectralRelationJet jet n k ≠ 0

/-- Exact birth order of an active projective spectral character. -/
noncomputable def spectralCharacterBirthOrder {I : Type*}
    (jet : ℕ → I → ℂ) (k : ProjectiveCharacter I)
    (hactive : SpectralCharacterActive jet k) : ℕ :=
  Nat.find hactive

/-- The birth coefficient is nonzero. -/
theorem spectralRelationJet_birthOrder_ne_zero
    {I : Type*} {jet : ℕ → I → ℂ} {k : ProjectiveCharacter I}
    (hactive : SpectralCharacterActive jet k) :
    projectiveSpectralRelationJet jet
      (spectralCharacterBirthOrder jet k hactive) k ≠ 0 :=
  Nat.find_spec hactive

/-- Every coefficient before the exact birth order vanishes. -/
theorem spectralRelationJet_eq_zero_of_lt_birthOrder
    {I : Type*} {jet : ℕ → I → ℂ} {k : ProjectiveCharacter I}
    (hactive : SpectralCharacterActive jet k)
    {n : ℕ} (hn : n < spectralCharacterBirthOrder jet k hactive) :
    projectiveSpectralRelationJet jet n k = 0 := by
  by_contra hne
  exact (Nat.not_lt_of_ge (Nat.find_min' hactive hne)) hn

/-- An active character belongs exactly to the filtration levels at or below
its birth order. -/
theorem mem_spectralConstraintFiltration_iff_le_birthOrder
    {I : Type*} {jet : ℕ → I → ℂ} {k : ProjectiveCharacter I}
    (hactive : SpectralCharacterActive jet k) (r : ℕ) :
    k ∈ spectralConstraintFiltration jet r ↔
      r ≤ spectralCharacterBirthOrder jet k hactive := by
  constructor
  · intro hk
    by_contra hnot
    have hlt : spectralCharacterBirthOrder jet k hactive < r := by omega
    exact spectralRelationJet_birthOrder_ne_zero hactive
      (hk _ hlt)
  · intro hr n hn
    exact spectralRelationJet_eq_zero_of_lt_birthOrder hactive
      (hn.trans_le hr)

/-- A permanently exact relation is precisely a character contained in
every finite-resolution layer. -/
theorem not_spectralCharacterActive_iff_forall_mem
    {I : Type*} {jet : ℕ → I → ℂ} {k : ProjectiveCharacter I} :
    ¬ SpectralCharacterActive jet k ↔
      ∀ r, k ∈ spectralConstraintFiltration jet r := by
  constructor
  · intro hinactive r n hn
    by_contra hne
    exact hinactive ⟨n, hne⟩
  · intro hall hactive
    let b := spectralCharacterBirthOrder jet k hactive
    have hmem := hall (b + 1)
    exact spectralRelationJet_birthOrder_ne_zero hactive
      (hmem b (Nat.lt_succ_self b))

/-- Exact wall-crossing certificate: an active character survives through
its birth layer and exits at the immediately following layer. -/
theorem mem_birthOrder_not_mem_succ
    {I : Type*} {jet : ℕ → I → ℂ} {k : ProjectiveCharacter I}
    (hactive : SpectralCharacterActive jet k) :
    k ∈ spectralConstraintFiltration jet
        (spectralCharacterBirthOrder jet k hactive) ∧
      k ∉ spectralConstraintFiltration jet
        (spectralCharacterBirthOrder jet k hactive + 1) := by
  constructor
  · exact
      (mem_spectralConstraintFiltration_iff_le_birthOrder hactive _).mpr
        le_rfl
  · intro hmem
    exact spectralRelationJet_birthOrder_ne_zero hactive
      (hmem _ (Nat.lt_succ_self _))

/-- Changing an integer character's primitive scale cannot change its exact
birth order. -/
theorem birthOrder_zsmul_eq
    {I : Type*} {jet : ℕ → I → ℂ} {k : ProjectiveCharacter I}
    (hactive : SpectralCharacterActive jet k)
    (m : ℤ) (hm : m ≠ 0) :
    ∃ hmactive : SpectralCharacterActive jet (m • k),
      spectralCharacterBirthOrder jet (m • k) hmactive =
        spectralCharacterBirthOrder jet k hactive := by
  let b := spectralCharacterBirthOrder jet k hactive
  have hb :
      projectiveSpectralRelationJet jet b k ≠ 0 :=
    spectralRelationJet_birthOrder_ne_zero hactive
  have hmb :
      projectiveSpectralRelationJet jet b (m • k) ≠ 0 := by
    rw [map_zsmul, zsmul_eq_mul]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hm) hb
  have hmactive : SpectralCharacterActive jet (m • k) :=
    ⟨b, hmb⟩
  refine ⟨hmactive, le_antisymm ?_ ?_⟩
  · exact Nat.find_min' hmactive hmb
  · let bm := spectralCharacterBirthOrder jet (m • k) hmactive
    have hbm :
        projectiveSpectralRelationJet jet bm (m • k) ≠ 0 :=
      spectralRelationJet_birthOrder_ne_zero hmactive
    have hkbm :
        projectiveSpectralRelationJet jet bm k ≠ 0 := by
      intro hkzero
      apply hbm
      rw [map_zsmul, zsmul_eq_mul, hkzero, mul_zero]
    exact Nat.find_min' hactive hkbm

/-- **Non-Archimedean temporal law.** The exact birth order of a sum cannot
precede the shallower birth order of its summands. -/
theorem min_birthOrder_le_birthOrder_add
    {I : Type*} {jet : ℕ → I → ℂ}
    {k l : ProjectiveCharacter I}
    (hk : SpectralCharacterActive jet k)
    (hl : SpectralCharacterActive jet l)
    (hadd : SpectralCharacterActive jet (k + l)) :
    min (spectralCharacterBirthOrder jet k hk)
        (spectralCharacterBirthOrder jet l hl) ≤
      spectralCharacterBirthOrder jet (k + l) hadd := by
  rw [← mem_spectralConstraintFiltration_iff_le_birthOrder hadd]
  exact add_mem_spectralConstraintFiltration_min
    ((mem_spectralConstraintFiltration_iff_le_birthOrder hk _).mpr le_rfl)
    ((mem_spectralConstraintFiltration_iff_le_birthOrder hl _).mpr le_rfl)

/-- If two active characters have unequal birth order, their sum is active
at exactly the smaller order: cancellation cannot occur across depths. -/
theorem birthOrder_add_eq_min_of_ne
    {I : Type*} {jet : ℕ → I → ℂ}
    {k l : ProjectiveCharacter I}
    (hk : SpectralCharacterActive jet k)
    (hl : SpectralCharacterActive jet l)
    (hne :
      spectralCharacterBirthOrder jet k hk ≠
        spectralCharacterBirthOrder jet l hl) :
    ∃ hadd : SpectralCharacterActive jet (k + l),
      spectralCharacterBirthOrder jet (k + l) hadd =
        min (spectralCharacterBirthOrder jet k hk)
          (spectralCharacterBirthOrder jet l hl) := by
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hcoeffK :=
      spectralRelationJet_birthOrder_ne_zero hk
    have hcoeffL :=
      spectralRelationJet_eq_zero_of_lt_birthOrder hl hkl
    have hadd : SpectralCharacterActive jet (k + l) := by
      use spectralCharacterBirthOrder jet k hk
      rw [map_add, hcoeffL, add_zero]
      exact hcoeffK
    refine ⟨hadd, ?_⟩
    have hle :=
      min_birthOrder_le_birthOrder_add hk hl hadd
    have hupper :=
      Nat.find_min' hadd (by
        rw [map_add, hcoeffL, add_zero]
        exact hcoeffK)
    rw [Nat.min_eq_left hkl.le]
    exact le_antisymm
      (by simpa [spectralCharacterBirthOrder] using hupper)
      (by simpa [Nat.min_eq_left hkl.le] using hle)
  · have hcoeffL :=
      spectralRelationJet_birthOrder_ne_zero hl
    have hcoeffK :=
      spectralRelationJet_eq_zero_of_lt_birthOrder hk hlk
    have hadd : SpectralCharacterActive jet (k + l) := by
      use spectralCharacterBirthOrder jet l hl
      rw [map_add, hcoeffK, zero_add]
      exact hcoeffL
    refine ⟨hadd, ?_⟩
    have hle :=
      min_birthOrder_le_birthOrder_add hk hl hadd
    have hupper :=
      Nat.find_min' hadd (by
        rw [map_add, hcoeffK, zero_add]
        exact hcoeffL)
    rw [Nat.min_eq_right hlk.le]
    exact le_antisymm
      (by simpa [spectralCharacterBirthOrder] using hupper)
      (by simpa [Nat.min_eq_right hlk.le] using hle)

end

end GaloisForLFunctions.HTGeometry
