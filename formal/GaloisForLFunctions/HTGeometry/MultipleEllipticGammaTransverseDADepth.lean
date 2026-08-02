import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy

/-!
# Transverse differential-algebraic depth of the multiple elliptic gamma hierarchy

Fix a finite upper-half-plane period family `τ`.  The structural transverse difference in the
direction `τ j` is the operator `T_{τ j} - 1` acting on the global meromorphic field.  Applying
the differences indexed by a duplicate-free list of labels to the genuine logarithmic derivative
deletes exactly those parameters, so the composite depends only on the underlying face.

The **transverse differential-algebraic depth** is the least number of distinct structural
directions whose composite difference lands in the differentially algebraic locus over `ℂ(z)`.
The exact period-rank dichotomy turns each face test into a purely rational statement about the
surviving labels: a face is differentially algebraic exactly when no two of its surviving periods
are rationally independent together with `1`.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The structural transverse difference operator -/

/-- The structural transverse difference `T_a - 1` on the global meromorphic field. -/
def transverseDifferenceMero (a : ℂ) (f : meroField (Set.univ : Set ℂ)) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv a f - f

/-- Composite of the structural transverse differences indexed by a list of labels. -/
def iteratedTransverseDifferenceMero (τ : ι → ℂ) :
    List ι → meroField (Set.univ : Set ℂ) → meroField (Set.univ : Set ℂ)
  | [], f => f
  | j :: l, f => transverseDifferenceMero (τ j) (iteratedTransverseDifferenceMero τ l f)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem iteratedTransverseDifferenceMero_nil (τ : ι → ℂ)
    (f : meroField (Set.univ : Set ℂ)) :
    iteratedTransverseDifferenceMero τ [] f = f := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem iteratedTransverseDifferenceMero_cons (τ : ι → ℂ) (j : ι) (l : List ι)
    (f : meroField (Set.univ : Set ℂ)) :
    iteratedTransverseDifferenceMero τ (j :: l) f =
      transverseDifferenceMero (τ j) (iteratedTransverseDifferenceMero τ l f) := rfl

/-- **Hierarchy identity.** The composite of the structural transverse differences along a
duplicate-free list of labels deletes exactly those parameters from the genuine multiple elliptic
gamma logarithmic derivative. -/
theorem iteratedTransverseDifferenceMero_eq_face
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    ∀ l : List ι, l.Nodup →
      iteratedTransverseDifferenceMero τ l (multipleEllipticGammaLogDerivMero τ hτ) =
        multipleEllipticGammaLogDerivFaceMero τ hτ l.toFinset := by
  intro l
  induction l with
  | nil =>
      intro _
      simpa using (multipleEllipticGammaLogDerivFaceMero_empty τ hτ).symm
  | cons j l ih =>
      intro hnodup
      have hjl : j ∉ l := (List.nodup_cons.mp hnodup).1
      have hnodupl : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hjfin : j ∉ l.toFinset := by simpa using hjl
      rw [iteratedTransverseDifferenceMero_cons, ih hnodupl, transverseDifferenceMero,
        multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ l.toFinset j hjfin,
        List.toFinset_cons]

/-! ## Face tests through the exact period-rank dichotomy -/

/-- A face is differentially algebraic exactly when its surviving period family has no rank-three
minor. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_iff_not_rankThreeMinor
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    [Nonempty (MultipleEllipticGammaFaceIndex J)] :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ↔
      ¬ MultipleEllipticGammaHasRankThreeMinor (multipleEllipticGammaFaceParameters τ J) :=
  differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
    (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i.1)

/-- A face carrying two surviving labels whose periods are rationally independent together with
`1` never reaches the differentially algebraic locus. -/
theorem not_differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_independentPair
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q r : ι}
    (hq : q ∉ J) (hr : r ∉ J) (hqr : q ≠ r)
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r))) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
  haveI : Nonempty (MultipleEllipticGammaFaceIndex J) := ⟨⟨q, hq⟩⟩
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_iff_not_rankThreeMinor
    τ hτ J]
  intro hno
  exact hno ⟨⟨q, hq⟩, ⟨r, hr⟩, by simpa [Subtype.ext_iff] using hqr, hind⟩

/-- A nonempty face all of whose surviving pairs are rationally dependent with `1` reaches the
differentially algebraic locus. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_no_independentPair
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q₀ : ι} (hq₀ : q₀ ∉ J)
    (hno : ∀ q r : ι, q ∉ J → r ∉ J → q ≠ r →
      ¬ LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r))) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
  haveI : Nonempty (MultipleEllipticGammaFaceIndex J) := ⟨⟨q₀, hq₀⟩⟩
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_iff_not_rankThreeMinor
    τ hτ J]
  rintro ⟨a, b, hab, hind⟩
  exact hno a.1 b.1 a.2 b.2 (fun h => hab (Subtype.ext h)) hind

/-- A face with a single surviving label always reaches the differentially algebraic locus: two
distinct labels are needed for a rank-three minor. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_unique_survivor
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι}
    (hq : q ∉ J) (huniq : ∀ i, i ∉ J → i = q) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
  haveI : Nonempty (MultipleEllipticGammaFaceIndex J) := ⟨⟨q, hq⟩⟩
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_iff_not_rankThreeMinor
    τ hτ J]
  rintro ⟨a, b, hab, -⟩
  exact hab (Subtype.ext ((huniq a.1 a.2).trans (huniq b.1 b.2).symm))

/-! ## The transverse differential-algebraic depth -/

/-- Cardinalities of the deleted faces which reach the differentially algebraic locus. -/
def multipleEllipticGammaDADeletionCards (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : Set ℕ :=
  {n | ∃ J : Finset ι, J.card = n ∧
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J)}

/-- The **transverse differential-algebraic depth**: the least number of distinct structural
directions whose composite difference is differentially algebraic over `ℂ(z)`. -/
def multipleEllipticGammaTransverseDADepth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : ℕ :=
  sInf (multipleEllipticGammaDADeletionCards τ hτ)

/-- The depth is computed by the least admissible deletion cardinality. -/
theorem multipleEllipticGammaTransverseDADepth_eq_of_min
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (n : ℕ)
    (hmem : ∃ J : Finset ι, J.card = n ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J))
    (hmin : ∀ J : Finset ι, J.card < n →
      ¬ DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J)) :
    multipleEllipticGammaTransverseDADepth τ hτ = n := by
  have hmemSet : n ∈ multipleEllipticGammaDADeletionCards τ hτ := hmem
  refine le_antisymm (Nat.sInf_le hmemSet) ?_
  refine le_csInf ⟨n, hmemSet⟩ ?_
  rintro b ⟨J, hcard, hDA⟩
  by_contra hlt
  exact hmin J (hcard ▸ not_le.mp hlt) hDA

/-- The depth is also the least length of a duplicate-free list of structural directions whose
composite transverse difference is differentially algebraic. -/
theorem multipleEllipticGammaTransverseDADepth_eq_sInf_nodupLists
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaTransverseDADepth τ hτ =
      sInf {n | ∃ l : List ι, l.Nodup ∧ l.length = n ∧
        DifferentialAlgebraicOver (RatFunc ℂ)
          (iteratedTransverseDifferenceMero τ l
            (multipleEllipticGammaLogDerivMero τ hτ))} := by
  have hsets : multipleEllipticGammaDADeletionCards τ hτ =
      {n | ∃ l : List ι, l.Nodup ∧ l.length = n ∧
        DifferentialAlgebraicOver (RatFunc ℂ)
          (iteratedTransverseDifferenceMero τ l
            (multipleEllipticGammaLogDerivMero τ hτ))} := by
    ext n
    constructor
    · rintro ⟨J, hcard, hDA⟩
      refine ⟨J.toList, J.nodup_toList, by simpa using hcard, ?_⟩
      rw [iteratedTransverseDifferenceMero_eq_face τ hτ _ J.nodup_toList,
        Finset.toList_toFinset]
      exact hDA
    · rintro ⟨l, hnodup, hlen, hDA⟩
      refine ⟨l.toFinset, by rw [List.toFinset_card_of_nodup hnodup]; exact hlen, ?_⟩
      rwa [iteratedTransverseDifferenceMero_eq_face τ hτ l hnodup] at hDA
  rw [multipleEllipticGammaTransverseDADepth, hsets]

end

end GaloisForLFunctions
