import GaloisForLFunctions.HTGeometry.CompactConfigurationBaire
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Finite regular stratifications

`IsLocalRegularLevelSetOfCodimAtLeast S c` is the exact smooth-stratum surface used here: locally,
`S` is the zero set of a smooth map to `R^m`, with surjective derivative and `c <= m`.  A finite
regular stratification is a finite disjoint cover by such strata.  Whitney's stratification theorem
supplies this surface for a complex algebraic set, with real codimension twice its complex
codimension.  Hirsch's parametric transversality theorem supplies the dense-avoidance conclusion.

The in-tree stratified-avoidance proof consumes only this finite regular-stratification surface.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A subset of a real normed space is locally a smooth regular level set of real codimension at
least `c`.  The local target dimension `m` is allowed to exceed `c`, so one predicate covers all
strata in a codimension-bounded stratification. -/
def IsLocalRegularLevelSetOfCodimAtLeast
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (S : Set Y) (c : ℕ) : Prop :=
  ∀ y ∈ S, ∃ m : ℕ, c ≤ m ∧ ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
    ∃ g : Y → (Fin m → ℝ),
      ContDiffOn ℝ ⊤ g U ∧
      (∀ x ∈ U, (x ∈ S ↔ g x = 0)) ∧
      ∀ x ∈ U, Function.Surjective (fderivWithin ℝ g U x)

/-- A finite disjoint smooth stratification of `bad`, every stratum having real codimension at
least `c`.  Whitney frontier conditions are stronger than the extracted surface recorded here;
finite regular strata are exactly what the avoidance proof consumes. -/
structure FiniteRegularStratification
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (bad : Set Y) (c : ℕ) where
  numberOfStrata : ℕ
  stratum : Fin numberOfStrata → Set Y
  pairwise_disjoint : Set.PairwiseDisjoint Set.univ stratum
  cover : bad = ⋃ i, stratum i
  regular : ∀ i, IsLocalRegularLevelSetOfCodimAtLeast (stratum i) c

end

end GaloisForLFunctions.HTGeometry
