import GaloisForLFunctions.HTGeometry.HorizonCompletedJets
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# The completed jets are inverse in the critical fibre algebra

Pushing the two completed jets into the quotient by the truncated compatibility relations makes
their inversion error vanish below the horizon, because each of its low coefficients *is* one of the
defining relations:

```text
horizonEval                        the quotient map onto the fibre algebra
horizonRawJetFibre, horizonRecipJetFibre
X_pow_dvd_horizonJet_mul_sub_one
    ** X^(m+n) ∣ rawJetFibre * recipJetFibre - 1 **
```

This is exactly the hypothesis of `TruncatedToeplitz.toeplitz_mul_toeplitz_of_inverse`, so over the
fibre algebra the Toeplitz matrix of the reciprocal jet is a genuine inverse of that of the raw jet,
with unit determinant — no completion and no limits are involved.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial MvPolynomial

variable (A : Type*) [CommRing A] (m n : ℕ) (P Q : A[X])

/-- The evaluation of the presentation ring in the critical fibre algebra. -/
noncomputable abbrev horizonEval :
    MvPolynomial (Fin (m + n)) A →+* horizonFibreAlgebra A m n P Q :=
  Ideal.Quotient.mk (Ideal.span <| Set.range (horizonRelation A m n P Q))

/-- The completed raw jet in the fibre algebra. -/
noncomputable def horizonRawJetFibre : (horizonFibreAlgebra A m n P Q)[X] :=
  (horizonRawJet A m n P).map (horizonEval A m n P Q)

/-- The completed reciprocal jet in the fibre algebra. -/
noncomputable def horizonRecipJetFibre : (horizonFibreAlgebra A m n P Q)[X] :=
  (horizonRecipJet A m n Q).map (horizonEval A m n P Q)

/-- **The two jets are inverse to the horizon in the fibre algebra.** -/
theorem X_pow_dvd_horizonJet_mul_sub_one :
    (Polynomial.X : (horizonFibreAlgebra A m n P Q)[X]) ^ (m + n) ∣
      horizonRawJetFibre A m n P Q * horizonRecipJetFibre A m n P Q - 1 := by
  classical
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [horizonRawJetFibre, horizonRecipJetFibre, ← Polynomial.map_one
    (f := horizonEval A m n P Q), ← Polynomial.map_mul, ← Polynomial.map_sub,
    Polynomial.coeff_map]
  have hrel : (horizonRawJet A m n P * horizonRecipJet A m n Q - 1).coeff d
      = horizonRelation A m n P Q ⟨d, hd⟩ := (horizonRelation_eq_coeff A m n P Q ⟨d, hd⟩).symm
  rw [hrel, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨⟨d, hd⟩, rfl⟩

end

end GaloisForLFunctions.HTGeometry
