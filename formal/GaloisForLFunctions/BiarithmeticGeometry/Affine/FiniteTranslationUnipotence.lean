import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteRationalUnitaryRigidity
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.HTGeometry.StrictlyLoweringFiltration

/-!
# Unipotent translations in finite rational affine representations

The affine trace law applies to every power of a translation. Schur triangularization and
power-sum Torelli force every eigenvalue to be one. Subtracting the identity gives a strictly
triangular matrix, whose nilpotence exponent is bounded by the representation dimension.
-/

noncomputable section

open scoped Matrix
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Integer powers of a translation act by the corresponding integer multiple. -/
theorem finite_rational_affine_translation_pow {n : ℕ}
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : ℚ) (k : ℕ) :
    ρ (translation b) ^ k = ρ (translation ((k : ℚ) * b)) := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, translation_zero, map_one]
  | succ k ih =>
    rw [pow_succ, ih, ← map_mul, ← translation_add]
    congr 2
    push_cast
    ring

/-- Every rational translation in a finite-dimensional complex affine representation is
unipotent, with nilpotence exponent at most the dimension. No continuity is required. -/
theorem finite_rational_affine_translation_unipotent {n : ℕ}
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : ℚ) :
    (ρ (translation b) - 1) ^ n = 0 := by
  obtain ⟨U, T, hU1, hU2, hT, hAT⟩ := exists_schur_triangulation n (ρ (translation b))
  have htrace (k : ℕ) : (ρ (translation b) ^ k).trace =
      (1 : Matrix (Fin n) (Fin n) ℂ).trace := by
    rw [finite_rational_affine_translation_pow, finite_rational_affine_translation_trace]
  -- Power sums determine the diagonal multiset, including multiplicities.
  have hmulti : Finset.univ.val.map (fun i => T i i) =
      Finset.univ.val.map (fun _ : Fin n => (1 : ℂ)) := by
    apply GaloisForLFunctions.powerSum_torelli
    intro k
    change (∑ i, (T i i) ^ k) = ∑ _ : Fin n, (1 : ℂ) ^ k
    rw [← trace_pow_eq_sum_diag hU1 hU2 hT hAT k, htrace]
    simp only [Matrix.trace_one, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  have hdiag (i : Fin n) : T i i = 1 := by
    have hmem : T i i ∈ Finset.univ.val.map (fun j => T j j) :=
      Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    rw [hmulti] at hmem
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hmem
    exact hj.symm
  have hstrict : StrictlyLowering.StrictlyUpper (T - 1) := by
    intro i j hji
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, hdiag, Matrix.one_apply_eq, sub_self]
    · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      have hlt : id j < id i := by
        change (j : ℕ) < (i : ℕ)
        omega
      simp only [Matrix.sub_apply, hT hlt, Matrix.one_apply_ne hij, sub_self]
  -- Strict triangularity gives the exact exponent before conjugating back.
  have hnil := StrictlyLowering.pow_eq_zero_of_strictlyUpper hstrict
  have hsub : ρ (translation b) - 1 = U * (T - 1) * Uᴴ := by
    rw [mul_sub, sub_mul, mul_one, hU2, ← eq_conj_of_schur hU2 hAT]
  have hpow (k : ℕ) : (ρ (translation b) - 1) ^ k = U * (T - 1) ^ k * Uᴴ := by
    induction k with
    | zero => simp only [pow_zero, mul_one, hU2]
    | succ k ih =>
      rw [pow_succ, ih, hsub, pow_succ]
      calc
        U * (T - 1) ^ k * Uᴴ * (U * (T - 1) * Uᴴ) =
            U * (T - 1) ^ k * (Uᴴ * U) * (T - 1) * Uᴴ := by noncomm_ring
        _ = U * ((T - 1) ^ k * (T - 1)) * Uᴴ := by
          rw [hU1]
          noncomm_ring
  rw [hpow, hnil, mul_zero, zero_mul]

#print axioms finite_rational_affine_translation_pow
#print axioms finite_rational_affine_translation_unipotent

end GaloisForLFunctions.BiarithmeticGeometry

