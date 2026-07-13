import GaloisForLFunctions.HTGeometry.CompactConfigurationBaire
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Exact classical interface for finite-stratified parametric avoidance

The carrier argument uses one theorem from classical differential topology: a smooth submersive
finite-dimensional family can be made transverse to every stratum of a finite smooth
stratification, and a codimension excess then forces avoidance on a compact configuration patch.

This file records that theorem at its general Euclidean boundary.  It contains no Nevanlinna
function, evaluation matrix, incidence ring, or carrier hypothesis.  Those data must be constructed
and the hypotheses below must be discharged in separate project modules.

`IsLocalRegularLevelSetOfCodimAtLeast S c` is the exact smooth-stratum surface used here: locally,
`S` is the zero set of a smooth map to `R^m`, with surjective derivative and `c <= m`.  A finite
regular stratification is a finite disjoint cover by such strata.  Whitney's stratification theorem
supplies this surface for a complex algebraic set, with real codimension twice its complex
codimension.  Hirsch's parametric transversality theorem supplies the dense-avoidance conclusion.

The structure `ClassicalStratifiedParametricAvoidance` is deliberately a theorem interface rather
than a project axiom.  Publication-facing theorems may take one value of this structure as the
precise cited classical input; every deduction after that input remains kernel-checked Lean.
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

/-- The exact classical Whitney--Hirsch input used by the project.

The configuration variable ranges over an open subset `U` of a finite-dimensional real normed
space `H`; `K` is the compact patch to be controlled.  Surjectivity is required only in the
finite-dimensional perturbation variable `P`.  When the bad set has a finite regular
stratification of codimension `c` and `finrank H < c`, parameters avoiding the bad set uniformly
on `K` are dense. -/
structure ClassicalStratifiedParametricAvoidance : Prop where
  dense_avoidance :
    ∀ {P H Y : Type}
      [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
      [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
      (F : P × H → Y) (bad : Set Y) (c : ℕ)
      (U : Set H) (K : Set H),
      IsOpen U → IsCompact K → K ⊆ U →
      ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U) →
      (∀ p h, h ∈ U → Function.Surjective (fderiv ℝ (fun v => F (v, h)) p)) →
      FiniteRegularStratification bad c →
      Module.finrank ℝ H < c →
      Dense (compactConfigurationAvoidance F bad K)

/-- Direct use form of the classical interface.  This theorem is intentionally only projection
from the exact literature input; it is useful for keeping subsequent project proofs readable
without expanding the complete quantified interface at each application. -/
theorem compactConfigurationAvoidance_dense_of_classicalStratifiedTransversality
    (classicalInput : ClassicalStratifiedParametricAvoidance)
    {P H Y : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : P × H → Y) (bad : Set Y) (c : ℕ)
    (U : Set H) (K : Set H)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U))
    (hsubmersion : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c) :
    Dense (compactConfigurationAvoidance F bad K) :=
  classicalInput.dense_avoidance (P := P) (H := H) (Y := Y)
    F bad c U K hU hK hKU hF hsubmersion hstrata hdim

end

end GaloisForLFunctions.HTGeometry
