/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.MilnorKFiniteField
import GaloisForLFunctions.HTGeometry.MilnorWittWittComparison

/-!
# The first Milnor `K`-group of a finite field

The existing degree-one equivalence `K₁ᴹ(F) ≃ Fˣ`, together with finite-field unit cyclicity,
makes `K₁ᴹ(F)` finite cyclic.  This is the natural target of degree-two tame residues and hence
of the local Milnor layer adjacent to Brauer theory.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

/-- The first Milnor `K`-group of a finite field is finite. -/
noncomputable instance finiteMilnorKDegOne
    (F : Type u) [Field F] [Finite F] : Finite (MilnorKDeg F 1) :=
  Finite.of_equiv (Additive Fˣ) (milnorDegOneEquiv F).toEquiv.symm

/-- The first Milnor `K`-group of a finite field is cyclic. -/
theorem finiteMilnorKDegOne_isAddCyclic
    (F : Type u) [Field F] [Finite F] : IsAddCyclic (MilnorKDeg F 1) :=
  (milnorDegOneEquiv F).isAddCyclic.mpr inferInstance

end GaloisForLFunctions.HTGeometry
