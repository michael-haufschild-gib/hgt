import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity

/-!
# Transverse differences of the multiple elliptic gamma hierarchy

The structural difference operator in a parameter direction is `Δ_q x = x(· + τ_q) − x`.  Applied to
the logarithmic derivative of the multiple elliptic gamma product, one difference in a *new*
direction deletes that parameter, by the coface equation of the hierarchy.  Iterating along a list
of directions therefore reaches the face obtained by deleting the distinct directions occurring in
the list, and any further differences act on that face.

This module builds the iterated difference operator, proves that it depends only on the multiset of
directions, identifies it on a repetition-free list with the corresponding face, and deduces the
sufficiency half of the transverse-depth law: as soon as the deleted directions leave at most one
surviving parameter, every iterated difference along that list is differentially algebraic over the
rational coordinate field, whatever repetitions the list contains.

The surviving-parameter criterion is the exact rank-three-minor law of the hierarchy: a face with at
most one surviving parameter has no rank-three period minor, and a face with none is the terminal
constant.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The iterated structural difference -/

/-- The structural difference operator of a translation. -/
def meroShiftDiff (q : ℂ) (x : meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv q x - x

/-- Iterated structural differences along a list of parameter directions. -/
def listShiftDiff (τ : ι → ℂ) : List ι → meroField (Set.univ : Set ℂ) →
    meroField (Set.univ : Set ℂ)
  | [], x => x
  | i :: l, x => meroShiftDiff (τ i) (listShiftDiff τ l x)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem listShiftDiff_nil (τ : ι → ℂ) (x : meroField (Set.univ : Set ℂ)) :
    listShiftDiff τ [] x = x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem listShiftDiff_cons (τ : ι → ℂ) (i : ι) (l : List ι)
    (x : meroField (Set.univ : Set ℂ)) :
    listShiftDiff τ (i :: l) x = meroShiftDiff (τ i) (listShiftDiff τ l x) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem listShiftDiff_append (τ : ι → ℂ) (l₁ l₂ : List ι) (x : meroField (Set.univ : Set ℂ)) :
    listShiftDiff τ (l₁ ++ l₂) x = listShiftDiff τ l₁ (listShiftDiff τ l₂ x) := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => rw [List.cons_append, listShiftDiff_cons, ih, listShiftDiff_cons]

/-- **Structural differences commute**, because the translations do. -/
theorem meroShiftDiff_comm (p q : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    meroShiftDiff p (meroShiftDiff q x) = meroShiftDiff q (meroShiftDiff p x) := by
  have hpq : addTranslationMeroEquiv p (addTranslationMeroEquiv q x)
      = addTranslationMeroEquiv q (addTranslationMeroEquiv p x) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  simp only [meroShiftDiff, map_sub]
  rw [hpq]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The iterated difference depends only on the multiset of directions. -/
theorem listShiftDiff_perm (τ : ι → ℂ) {l₁ l₂ : List ι} (h : l₁.Perm l₂)
    (x : meroField (Set.univ : Set ℂ)) :
    listShiftDiff τ l₁ x = listShiftDiff τ l₂ x := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [listShiftDiff_cons, listShiftDiff_cons, ih]
  | swap a b l => rw [listShiftDiff_cons, listShiftDiff_cons, listShiftDiff_cons,
      listShiftDiff_cons, meroShiftDiff_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-! ### Repetition-free differences are faces -/

/-- **A repetition-free iterated difference is exactly the corresponding face.**  Each new direction
deletes its parameter, by the coface equation of the hierarchy. -/
theorem listShiftDiff_nodup (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {l : List ι} (hl : l.Nodup) :
    listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ)
      = multipleEllipticGammaLogDerivFaceMero τ hτ l.toFinset := by
  induction l with
  | nil =>
      rw [listShiftDiff_nil, List.toFinset_nil, multipleEllipticGammaLogDerivFaceMero_empty]
  | cons i l ih =>
      have hnodup : l.Nodup := hl.of_cons
      have hi : i ∉ l.toFinset := by
        rw [List.mem_toFinset]
        exact (List.nodup_cons.mp hl).1
      rw [listShiftDiff_cons, ih hnodup, List.toFinset_cons, meroShiftDiff]
      exact multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ l.toFinset i hi

/-! ### Differential algebraicity is preserved -/

theorem differentialAlgebraicOver_meroShiftDiff {q : ℂ} {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (meroShiftDiff q x) :=
  differentialAlgebraicOver_sub (differentialAlgebraicOver_addTranslationMeroEquiv q hx) hx

omit [Fintype ι] [DecidableEq ι] in
theorem differentialAlgebraicOver_listShiftDiff (τ : ι → ℂ) (l : List ι)
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (listShiftDiff τ l x) := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact differentialAlgebraicOver_meroShiftDiff ih

/-! ### Faces with at most one surviving parameter -/

/-- Differential algebraicity of the embedded constants. -/
theorem differentialAlgebraicOver_algebraMap_complex (c : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) := by
  have h := HTGeometry.differentialAlgebraicOver_algebraMap
    (F := RatFunc ℂ) (E := meroField (Set.univ : Set ℂ)) (algebraMap ℂ (RatFunc ℂ) c)
  rwa [meromorphicRatFunc_algebraMap_complex] at h

/-- **A face with at most one surviving parameter is differentially algebraic.**  With one survivor
there is no rank-three period minor; with none the face is the terminal constant. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_subsingleton
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (hJ : ∀ i j : ι, i ∉ J → j ∉ J → i = j) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
  by_cases hne : ∃ i : ι, i ∉ J
  · obtain ⟨i₀, hi₀⟩ := hne
    haveI : Nonempty (MultipleEllipticGammaFaceIndex J) := ⟨⟨i₀, hi₀⟩⟩
    rw [multipleEllipticGammaLogDerivFaceMero,
      differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor]
    rintro ⟨q, r, hqr, -⟩
    exact hqr (Subtype.ext (hJ q r q.2 r.2))
  · have hall : ∀ i : ι, i ∈ J := by
      intro i
      by_contra hi
      exact hne ⟨i, hi⟩
    haveI : IsEmpty (MultipleEllipticGammaFaceIndex J) := ⟨fun i => i.2 (hall i)⟩
    rw [multipleEllipticGammaLogDerivFaceMero,
      multipleEllipticGammaLogDerivMero_isEmpty]
    exact differentialAlgebraicOver_algebraMap_complex _

/-! ### The sufficiency half of the transverse-depth law -/

/-- **Transverse depth is sufficient.**  If the directions occurring in a list already delete all
but at most one parameter, then the iterated structural difference along that list is differentially
algebraic over the rational coordinate field, no matter how many repetitions the list contains.

Repetitions are absorbed because differences and translations preserve differential algebraicity,
so only the set of distinct directions matters, and that set reaches a face with at most one
surviving parameter. -/
theorem differentialAlgebraicOver_listShiftDiff_multipleEllipticGammaLogDerivMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (l : List ι) (S : Finset ι)
    (hS : S ⊆ l.toFinset) (hsurv : ∀ i j : ι, i ∉ S → j ∉ S → i = j) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ)) := by
  classical
  have hsubset : S.toList ⊆ l := by
    intro i hi
    have : i ∈ S := (Finset.mem_toList).mp hi
    exact List.mem_toFinset.mp (hS this)
  obtain ⟨l₁, hperm₁, hsub₁⟩ := List.Nodup.subperm (S.nodup_toList) hsubset
  obtain ⟨l₂, hl⟩ := hsub₁.exists_perm_append
  have hlperm : l.Perm (l₂ ++ l₁) := hl.trans (List.perm_append_comm)
  have hnodup₁ : l₁.Nodup := hperm₁.nodup_iff.mpr (S.nodup_toList)
  have htoFinset : l₁.toFinset = S := by
    ext a
    rw [List.mem_toFinset, hperm₁.mem_iff, Finset.mem_toList]
  rw [listShiftDiff_perm τ hlperm, listShiftDiff_append,
    listShiftDiff_nodup τ hτ hnodup₁, htoFinset]
  exact differentialAlgebraicOver_listShiftDiff τ l₂
    (differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_subsingleton
      τ hτ S hsurv)

end

end GaloisForLFunctions
