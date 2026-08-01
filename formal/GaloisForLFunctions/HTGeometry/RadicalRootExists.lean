import GaloisForLFunctions.HTGeometry.RootFieldTransport

/-!
# A radical polynomial has a root in its own root field

Where a polynomial splits it has a root, and a root lies in the field its roots generate.  For the
radical polynomial that root is an `n`-th root of the constant, so the generator the base change
step asks for is produced by the situation rather than assumed.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The radical polynomial has an `n`-th root of its constant in its root field.** -/
theorem exists_pow_eq_mem_rootField {c : F} {n : ℕ} (hn : 0 < n)
    (hsplit : (((Polynomial.X ^ n - Polynomial.C c : Polynomial F)).map
      (algebraMap F L)).Splits) :
    ∃ α : L, α ∈ rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c) ∧
      α ^ n = algebraMap F L c := by
  have hdeg : ((Polynomial.X ^ n - Polynomial.C c : Polynomial F).map
      (algebraMap F L)).degree ≠ 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.degree_X_pow_sub_C hn]
    exact_mod_cast Nat.pos_iff_ne_zero.1 hn
  obtain ⟨α, hα⟩ := hsplit.exists_eval_eq_zero hdeg
  have haeval : Polynomial.aeval α (Polynomial.X ^ n - Polynomial.C c : Polynomial F) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hα
  have hpow : α ^ n = algebraMap F L c := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at haeval
    exact haeval
  refine ⟨α, ?_, hpow⟩
  refine IntermediateField.subset_adjoin _ _ ?_
  rw [Polynomial.mem_rootSet']
  refine ⟨?_, haeval⟩
  intro hcon
  exact (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero
    ((Polynomial.map_eq_zero_iff (algebraMap F L).injective).1 hcon)

end GaloisForLFunctions.HTGeometry
