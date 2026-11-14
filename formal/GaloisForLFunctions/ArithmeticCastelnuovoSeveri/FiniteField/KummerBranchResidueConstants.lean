import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerNormFibers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality

/-!
# Constant roots for the normalized branch residue equation

If `δ=gcd(Q+1,R)`, every nonzero `Q`-Frobenius-fixed element times
an inverse `R`-th power is a `δ`-th power in the square constant field.
Norm surjectivity supplies the first factor and divisibility by `δ`
supplies the second. The Frobenius condition is discharged at every
nonzero auxiliary-field point of the prime-power family.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)

/-- A nonzero norm value times an inverse `R`-th power is a `gcd(Q+1,R)`-th power. -/
theorem squareConstantField_exists_branch_residue_root
    (η : (SquareConstantField p s)ˣ) (R : ℕ) (a : SquareConstantField p s)
    (ha : a ≠ 0) (hfixed : a ^ p ^ (s + 1) = a) :
    ∃ β : SquareConstantField p s, β ≠ 0 ∧
      β ^ Nat.gcd (p ^ (s + 1) + 1) R =
        (((η⁻¹) ^ R : (SquareConstantField p s)ˣ) : SquareConstantField p s) * a := by
  obtain ⟨z, hz⟩ := (squareConstantField_exists_norm_iff p s a).mpr hfixed
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.succ_ne_zero _)] at hz
    exact ha hz.symm
  let δ := Nat.gcd (p ^ (s + 1) + 1) R
  refine ⟨((η : SquareConstantField p s)⁻¹) ^ (R / δ) * z ^ ((p ^ (s + 1) + 1) / δ),
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Units.ne_zero η))) (pow_ne_zero _ hz0), ?_⟩
  rw [mul_pow, ← pow_mul, ← pow_mul,
    Nat.div_mul_cancel (Nat.gcd_dvd_right (p ^ (s + 1) + 1) R),
    Nat.div_mul_cancel (Nat.gcd_dvd_left (p ^ (s + 1) + 1) R), hz]
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]

/-- The residue equation splits at every nonzero auxiliary-field point of the prime-power family. -/
theorem squareConstantField_exists_auxiliary_branch_residue_root (d n R : ℕ)
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ)
    (a : (KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1))ˣ) :
    ∃ β : SquareConstantField p (kummerSquareIndex d n), β ≠ 0 ∧
      β ^ Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) R =
        (((η⁻¹) ^ R : (SquareConstantField p (kummerSquareIndex d n))ˣ) :
          SquareConstantField p (kummerSquareIndex d n)) *
          ((a : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)) :
            SquareConstantField p (kummerSquareIndex d n)) := by
  apply squareConstantField_exists_branch_residue_root p (kummerSquareIndex d n) η R
  · intro h
    exact Units.ne_zero a (Subtype.ext h)
  · apply GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.frobenius_fixed_of_dvd p
      (show d + 1 ∣ kummerSquareIndex d n + 1 from by
        rw [kummerSquareIndex_succ]
        exact dvd_mul_right _ _)
    exact (a : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)).property

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
