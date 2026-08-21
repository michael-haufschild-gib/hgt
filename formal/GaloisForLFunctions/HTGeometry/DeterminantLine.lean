import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The determinant line and duality of exterior powers

For a finite free module `M` over a commutative ring `R`:

* `exteriorPower.pairingDual R M n : ⋀^n (M^∨) →ₗ[R] (⋀^n M)^∨` is an **isomorphism**
  (`DetLine.pairingDual_bijective`, `DetLine.pairingDualEquiv`) — mathlib defines the map and
  proves the basis identities, but does not record that it is bijective;
* the **determinant line** `det M = ⋀^{rank M} M` is free of rank one (`DetLine.finrank_detLine`),
  and `det (M^∨) ≅ (det M)^∨` canonically (`DetLine.detLineDualEquiv`).

These are the objects `det Lie 𝒜` and `ω_𝒜 = (det Lie 𝒜)^{⊗ -1}` of Suzuki, *Duality invariance of
Faltings heights, Hodge line bundles and global periods* (arXiv:2504.04993); Proposition 2.2 of
that paper is a statement about exactly this duality of determinant lines.
-/

namespace GaloisForLFunctions.HTGeometry.DetLine

open Module exteriorPower Set

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- On a basis, `pairingDual` produces the dual basis of the exterior power. -/
theorem pairingDual_basis {ι : Type*} [LinearOrder ι] [Finite ι] [DecidableEq ι]
    (b : Basis ι R M) (n : ℕ) (s : Set.powersetCard ι n) :
    exteriorPower.pairingDual R M n ((b.dualBasis).exteriorPower n s)
      = ((b.exteriorPower n).dualBasis) s := by
  have hcoord : (b.dualBasis : ι → Module.Dual R M) = (fun i => b.coord i) := by
    funext i
    exact LinearMap.ext fun x => by rw [Basis.dualBasis_apply, Basis.coord_apply]
  have h1 : ((b.dualBasis).exteriorPower n) s = ιMulti_family R n b.coord s := by
    rw [exteriorPower.coe_basis, hcoord]
  rw [h1, ← exteriorPower.ιMultiDual, ← exteriorPower.basis_coord]
  exact LinearMap.ext fun x => by rw [Basis.dualBasis_apply, Basis.coord_apply]

/-- **`pairingDual` is an isomorphism for finite free modules.** -/
theorem pairingDual_bijective (n : ℕ) :
    Function.Bijective (exteriorPower.pairingDual R M n) := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  set b := Module.Free.chooseBasis R M with hb
  set e := Basis.equiv ((b.dualBasis).exteriorPower n) ((b.exteriorPower n).dualBasis)
    (Equiv.refl _) with he
  have heq : exteriorPower.pairingDual R M n = (e : _ →ₗ[R] _) := by
    refine Basis.ext ((b.dualBasis).exteriorPower n) fun s => ?_
    rw [pairingDual_basis R M b n s, he]
    simp only [Basis.equiv_apply, Equiv.refl_apply, LinearEquiv.coe_coe]
  rw [heq]
  exact e.bijective

/-- `pairingDual` as a linear equivalence. -/
noncomputable def pairingDualEquiv (n : ℕ) :
    ⋀[R]^n (Module.Dual R M) ≃ₗ[R] Module.Dual R (⋀[R]^n M) :=
  LinearEquiv.ofBijective _ (pairingDual_bijective R M n)

@[simp] theorem pairingDualEquiv_apply (n : ℕ) (x : ⋀[R]^n (Module.Dual R M)) :
    pairingDualEquiv R M n x = exteriorPower.pairingDual R M n x := rfl

/-! ### The determinant line -/

/-- The **determinant line** of a finite free module: its top exterior power. -/
noncomputable abbrev detLine : Type _ := ⋀[R]^(Module.finrank R M) M

theorem finrank_detLine [Nontrivial R] : Module.finrank R (detLine R M) = 1 := by
  rw [exteriorPower.finrank_eq, Nat.choose_self]

/-- **`det (M^∨) ≅ (det M)^∨`**, canonically. -/
noncomputable def detLineDualEquiv :
    ⋀[R]^(Module.finrank R M) (Module.Dual R M) ≃ₗ[R] Module.Dual R (detLine R M) :=
  pairingDualEquiv R M (Module.finrank R M)

theorem finrank_dual_eq [Nontrivial R] :
    Module.finrank R (Module.Dual R M) = Module.finrank R M :=
  Module.finrank_linearMap_self R R M

end GaloisForLFunctions.HTGeometry.DetLine
