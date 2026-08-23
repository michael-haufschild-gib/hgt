/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsion

/-!
# Finite-level invariant sums

For each positive or zero denominator `n`, finitely supported `ℚ/ℤ[n]` profiles have their own
additive sum and exact zero-sum presentation.  This is the finite-level target of ABHN.  It does
not identify any profile with a family of local Brauer classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Sum a finite profile with values already restricted to `ℚ/ℤ[n]`. -/
noncomputable def finsuppRatModIntNTorsionSumAddHom (ι : Type u) (n : ℕ) :
    (ι →₀ ratModIntNTorsion n) →+ ratModIntNTorsion n := by
  classical
  exact
    { toFun := fun f ↦ f.sum fun _ q ↦ q
      map_zero' := Finsupp.sum_zero_index
      map_add' := fun f g ↦ Finsupp.sum_add_index (by intros; rfl) (by intros; rfl) }

/-- A singleton finite-level profile sums to its one local value. -/
theorem finsuppRatModIntNTorsionSumAddHom_apply_single
    (ι : Type u) (n : ℕ) (i : ι) (q : ratModIntNTorsion n) :
    finsuppRatModIntNTorsionSumAddHom ι n (Finsupp.single i q) = q := by
  change (Finsupp.single i q).sum (fun _ q ↦ q) = q
  exact Finsupp.sum_single_index rfl

/-- A finite-level invariant sum is surjective as soon as the index type has one place. -/
theorem finsuppRatModIntNTorsionSumAddHom_surjective
    (ι : Type u) [Nonempty ι] (n : ℕ) :
    Function.Surjective (finsuppRatModIntNTorsionSumAddHom ι n) := by
  intro q
  let i : ι := Classical.choice inferInstance
  exact ⟨Finsupp.single i q, finsuppRatModIntNTorsionSumAddHom_apply_single ι n i q⟩

/-- Modulo finite-level zero-sum profiles, the `ℚ/ℤ[n]` profile group is canonically
`ℚ/ℤ[n]`. -/
noncomputable def finsuppRatModIntNTorsionSumQuotientAddEquiv
    (ι : Type u) [Nonempty ι] (n : ℕ) :
    ((ι →₀ ratModIntNTorsion n) ⧸
      (finsuppRatModIntNTorsionSumAddHom ι n).ker) ≃+ ratModIntNTorsion n :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (finsuppRatModIntNTorsionSumAddHom ι n)
    (finsuppRatModIntNTorsionSumAddHom_surjective ι n)

/-- The finite-level profile sum is exact after including its zero-sum subgroup. -/
theorem finsuppRatModIntNTorsionSum_zeroSum_exact
    (ι : Type u) (n : ℕ) :
    Function.Exact (finsuppRatModIntNTorsionSumAddHom ι n).ker.subtype
      (finsuppRatModIntNTorsionSumAddHom ι n) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact y.property

end GaloisForLFunctions.HTGeometry.ABHN
