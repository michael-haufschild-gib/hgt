import GaloisForLFunctions.HTGeometry.DifferentialAlgebra.OreAffineTranslation

/-!
# Affine translations preserve differential order

Translation by an order-zero coefficient is triangular for the differential
order filtration. Applying the opposite translation turns the upper bound
into equality, including the zero operator and rings with zero divisors.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DiffOp

variable {K : Type*} [CommRing K] [Differential K]

theorem degree_affineGenerator_pow_le (a : K) (n : ℕ) :
    degree ((X + C a) ^ n) ≤ n := by
  have hgen : degree (X + C a) ≤ 1 := by
    apply (degree_add_le _ _).trans
    exact max_le (degree_mono_le 1 1) ((degree_mono_le 0 a).trans (by omega))
  induction n with
  | zero => exact degree_mono_le 0 1
  | succ n ih =>
    rw [pow_succ]
    exact (degree_mul_le _ _).trans (by omega)

theorem degree_affineTranslationHom_mono_le (a c : K) (n : ℕ) :
    degree (affineTranslationHom a (mono n c)) ≤ n := by
  change degree (connectionDiffOpSMul (affineConnection a) (mono n c) 1) ≤ n
  rw [connectionDiffOpSMul_mono, affineConnection_iterate, mul_one]
  exact (degree_smul_le _ _).trans (degree_affineGenerator_pow_le a n)

/-- Translation cannot increase order: every transformed monomial stays within its degree. -/
theorem degree_affineTranslationHom_le (a : K) (p : DiffOp K) :
    degree (affineTranslationHom a p) ≤ degree p := by
  have hexp : p = ∑ i ∈ (toFinsupp p).support, mono i (coeff p i) :=
    (Finsupp.sum_single (toFinsupp p)).symm
  apply degree_le_iff.mpr
  intro m hm
  conv_lhs => rw [hexp, map_sum]
  rw [← coeffAddHom_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply coeff_eq_zero_of_degree_lt
  exact lt_of_le_of_lt (degree_affineTranslationHom_mono_le a (coeff p i) i)
    (lt_of_le_of_lt (Finset.le_sup (f := id) hi) hm)

/-- Affine translations preserve the complete differential-order filtration. -/
theorem degree_affineTranslationHom (a : K) (p : DiffOp K) :
    degree (affineTranslationHom a p) = degree p := by
  apply le_antisymm (degree_affineTranslationHom_le a p)
  have h := degree_affineTranslationHom_le (-a) (affineTranslationHom a p)
  rwa [affineTranslationHom_comp, neg_add_cancel, affineTranslationHom_zero] at h

end GaloisForLFunctions.HTGeometry.DiffOp

#print axioms GaloisForLFunctions.HTGeometry.DiffOp.degree_affineTranslationHom
