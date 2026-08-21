/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CyclicAlgebraDescent
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraSplit

/-!
# Vanishing cyclic degree-two classes give split cyclic algebras

The degree-two cyclic norm quotient identifies a zero cohomology parameter with an actual field
norm.  The split cyclic-algebra theorem turns that norm witness into a central simple algebra
whose Brauer class is zero.  This proves the zero-kernel direction of the cyclic
cohomology-to-Brauer comparison without postulating a Brauer class for arbitrary cyclic
parameters.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- A vanishing base-unit degree-two class has an actual field-norm witness. -/
theorem cyclicGaloisH2BaseProjection_eq_zero_exists_norm
    [FiniteDimensional K L] [IsGalois K L] (a : Additive Kˣ)
    (h : cyclicGaloisH2BaseProjection K L a = 0) :
    ∃ c : Lˣ, (a.toMul : K) = Algebra.norm K (c : L) := by
  have heq : cyclicGaloisH2BaseProjection K L a = cyclicGaloisH2BaseProjection K L 0 := by
    simpa using h
  obtain ⟨c, hc⟩ :=
    (cyclicGaloisH2BaseProjection_eq_iff_exists_norm_ratio K L a 0).mp heq
  exact ⟨c, by simpa using hc⟩

/-- The central simple cyclic algebra selected by a vanishing degree-two base parameter. -/
noncomputable def cyclicGaloisH2ZeroCSA [FiniteDimensional K L] [IsGalois K L]
    (a : Additive Kˣ) (h : cyclicGaloisH2BaseProjection K L a = 0) : CSA K :=
  cyclicGaloisAlgebraNormCSA K L (a.toMul : K)
    (cyclicGaloisH2BaseProjection_eq_zero_exists_norm K L a h).choose
    (cyclicGaloisH2BaseProjection_eq_zero_exists_norm K L a h).choose_spec

/-- A vanishing degree-two base parameter yields the split Brauer class. -/
theorem brauerClass_cyclicGaloisH2ZeroCSA_eq_split [FiniteDimensional K L] [IsGalois K L]
    (a : Additive Kˣ) (h : cyclicGaloisH2BaseProjection K L a = 0) :
    brauerClass (cyclicGaloisH2ZeroCSA K L a h) = brauerSplitClass K := by
  exact brauerClass_cyclicGaloisAlgebraNormCSA_eq_split K L (a.toMul : K)
    (cyclicGaloisH2BaseProjection_eq_zero_exists_norm K L a h).choose
    (cyclicGaloisH2BaseProjection_eq_zero_exists_norm K L a h).choose_spec

end GaloisForLFunctions.HTGeometry.ABHN
