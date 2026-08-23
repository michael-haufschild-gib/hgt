/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.Data.DFinsupp.BigOperators

/-!
# Additive maps commute with dependent finite-support sums

This is the dependent-finitely-supported analogue of `map_sum`, packaged for the local invariant
sums used by reciprocity laws.
-/

namespace GaloisForLFunctions.HTGeometry

set_option linter.unnecessarySimpa false in
/-- An additive homomorphism commutes with a dependent finite-support sum of additive maps. -/
theorem addMonoidHom_map_dfinsupp_sum
    {ι : Type*} {β : ι → Type*} [DecidableEq ι]
    [(i : ι) → AddCommMonoid (β i)] [(i : ι) → DecidableEq (β i)]
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : (i : ι) → β i →+ A) (g : A →+ B) (z : Π₀ i, β i) :
    g (z.sum fun i x ↦ f i x) = z.sum fun i x ↦ g (f i x) := by
  let lhs : (Π₀ i, β i) →+ B := g.comp (DFinsupp.sumAddHom f)
  let rhs : (Π₀ i, β i) →+ B := DFinsupp.sumAddHom (fun i ↦ g.comp (f i))
  have h : lhs = rhs := by
    apply DFinsupp.addHom_ext
    intro i x
    simp [lhs, rhs, DFinsupp.sumAddHom]
  simpa [lhs, rhs, DFinsupp.sumAddHom] using DFunLike.congr_fun h z

end GaloisForLFunctions.HTGeometry
