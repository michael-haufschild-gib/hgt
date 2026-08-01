import GaloisForLFunctions.HTGeometry.GenericPolynomialSplitting

/-!
# The roots of the generic polynomial are the generic roots

The generic polynomial is the product of the linear factors attached to the generic roots, so a
value where it vanishes must annihilate one of those factors.

Together with the generic roots being roots, this identifies the root set exactly, which is the
enumeration the base change step asks for.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {d : ℕ}

/-- **The root set of the generic polynomial is the set of generic roots.** -/
theorem rootSet_genericMonic :
    (genericMonic K d).rootSet (SymmetricRationalField K d) = Set.range (genericRoot K d) := by
  ext x
  constructor
  · intro hx
    rw [Polynomial.mem_rootSet'] at hx
    have hev : Polynomial.eval x (genericMonicF K d) = 0 := by
      have h := hx.2
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, map_genericMonic] at h
      exact h
    rw [genericMonicF, Polynomial.eval_prod] at hev
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hev
    exact ⟨i, (sub_eq_zero.1 (by simpa using hi)).symm⟩
  · rintro ⟨i, rfl⟩
    exact genericRoot_mem_rootSet i

end GaloisForLFunctions.HTGeometry
