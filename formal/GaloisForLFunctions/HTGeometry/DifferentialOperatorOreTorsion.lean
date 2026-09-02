import GaloisForLFunctions.HTGeometry.KaehlerModuleFree
import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreField

/-!
# Canonical Ore-torsion submodule

For a module over the differential-operator Ore domain, elements annihilated by some nonzero
operator form a submodule.  Closure under addition and scalar multiplication uses the corpus Ore
common-left-multiple theorem.  The quotient by this canonical submodule is torsion-free.

This is the literal `Tor_R` object required by the differential variational-building construction.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {M : Type*} [AddCommGroup M] [Module (DiffOp K) M]

/-- Elements annihilated by at least one nonzero differential operator. -/
def oreTorsionSubmodule : Submodule (DiffOp K) M where
  carrier := {x | ∃ r : DiffOp K, r ≠ 0 ∧ r • x = 0}
  zero_mem' := ⟨1, one_ne_zero, smul_zero 1⟩
  add_mem' := by
    rintro x y ⟨r, hr, hrx⟩ ⟨s, hs, hsy⟩
    obtain ⟨r', s', hs', hcommon⟩ := exists_ore_left_multiple r s hs
    refine ⟨s' * r, mul_ne_zero hs' hr, ?_⟩
    rw [smul_add, mul_smul, hrx, smul_zero, hcommon, mul_smul, hsy,
      smul_zero, add_zero]
  smul_mem' := by
    rintro a x ⟨r, hr, hrx⟩
    obtain ⟨r', s', hs', hcommon⟩ := exists_ore_left_multiple a r hr
    refine ⟨s', hs', ?_⟩
    rw [← mul_smul, hcommon, mul_smul, hrx, smul_zero]

/-- Membership in the canonical Ore-torsion submodule. -/
theorem mem_oreTorsionSubmodule_iff (x : M) :
    x ∈ oreTorsionSubmodule (K := K) (M := M) ↔
      ∃ r : DiffOp K, r ≠ 0 ∧ r • x = 0 := Iff.rfl

/-- The quotient by all Ore-torsion elements is torsion-free. -/
theorem oreTorsionQuotient_torsionFree
    (r : DiffOp K) (x : M ⧸ oreTorsionSubmodule (K := K) (M := M))
    (hr : r ≠ 0) (hrx : r • x = 0) : x = 0 := by
  let N : Submodule (DiffOp K) M := oreTorsionSubmodule (K := K) (M := M)
  obtain ⟨y, rfl⟩ := N.mkQ_surjective x
  change N.mkQ (r • y) = 0 at hrx
  have hry : r • y ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hrx
  obtain ⟨s, hs, hsry⟩ := hry
  apply (Submodule.Quotient.mk_eq_zero N).mpr
  exact ⟨s * r, mul_ne_zero hs hr, by rw [mul_smul, hsry]⟩

end
end GaloisForLFunctions.HTGeometry.DiffOp

