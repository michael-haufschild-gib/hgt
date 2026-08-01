import GaloisForLFunctions.HTGeometry.UniversalMonicPolynomial
import GaloisForLFunctions.HTGeometry.TschirnhausShift

/-!
# Centering the monic polynomial with indeterminate coefficients

Shifting the universal monic polynomial by minus the next-to-leading coefficient divided by the
degree removes that coefficient, and changes every other one by a multiple of the shift.

So the centered coefficients are the original ones plus corrections that vanish when the
next-to-leading coefficient does, which is the triangularity of the change of parameters.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- The shift that centers the universal monic polynomial. -/
noncomputable def centeringShift (K : Type*) [Field K] (d : ℕ) (hd : 0 < d) :
    MvPolynomial (Fin d) K :=
  -((d : K)⁻¹ • MvPolynomial.X (⟨d - 1, by omega⟩ : Fin d))

/-- The coefficients of the centered universal polynomial. -/
noncomputable def universalCenteredCoeff (K : Type*) [Field K] (d : ℕ) (hd : 0 < d) (k : ℕ) :
    MvPolynomial (Fin d) K :=
  (Polynomial.taylor (centeringShift K d hd) (universalMonic K d)).coeff k

/-- **Centering removes the next-to-leading coefficient.** -/
theorem universalCenteredCoeff_pred (hd : 0 < d) :
    universalCenteredCoeff K d hd (d - 1) = 0 := by
  have hdne : (d : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [universalCenteredCoeff,
    taylor_coeff_pred (by omega : 1 ≤ d) (natDegree_universalMonic hd)
      (monic_universalMonic hd),
    coeff_universalMonic_lt (by omega : d - 1 < d), centeringShift]
  have hcast : ((d : ℕ) : MvPolynomial (Fin d) K) = MvPolynomial.C ((d : ℕ) : K) :=
    (map_natCast MvPolynomial.C _).symm
  rw [hcast, smul_eq_C_mul, mul_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hdne, map_one,
    one_mul, neg_add_cancel]

omit [CharZero K] in
/-- **Every centered coefficient is the original one plus a multiple of the shift.** -/
theorem universalCenteredCoeff_eq_add (hd : 0 < d) (k : ℕ) :
    ∃ s : MvPolynomial (Fin d) K,
      universalCenteredCoeff K d hd k =
        (universalMonic K d).coeff k + centeringShift K d hd * s :=
  taylor_coeff_eq_add _ _ _

end GaloisForLFunctions.HTGeometry
