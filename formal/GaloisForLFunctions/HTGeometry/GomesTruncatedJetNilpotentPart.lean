import GaloisForLFunctions.HTGeometry.GomesTruncatedJetAugmentation

/-!
# The exact nilpotent part of every joint symmetry

Subtracting the observed scalar matrix leaves an element annihilated by the
jet-horizon power. In particular, scalar coordinate one is equivalent to the
literal unipotence equation, with no additional spectral hypotheses.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Every joint symmetry differs from its scalar matrix by a horizon-nilpotent matrix. -/
theorem gomesTruncatedJetJointAlgebra_sub_scalar_pow (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    (E.val - algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (gomesTruncatedJetAugmentation n z E)) ^ (n + 1) = 0 := by
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) E.val).mp
    ((gomesTruncatedJetJointAlgebra_mem_iff n z E.val).mp E.property).1
  have ha : gomesTruncatedJetAugmentation n z E = p.coeff 0 := by
    rw [gomesTruncatedJetAugmentation_apply, ← hp, gomesFiniteFockPolynomialHom_diagonal]
  have hC : gomesFiniteFockPolynomialHom (n + 1) (Polynomial.C (p.coeff 0)) =
      algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p.coeff 0) :=
    (gomesFiniteFockPolynomialHom (n + 1)).commutes (p.coeff 0)
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr
    (show (p - Polynomial.C (p.coeff 0)).coeff 0 = 0 by simp)
  rw [ha, ← hp, ← hC, ← map_sub, ← map_pow, hq, mul_pow,
    map_mul, map_pow, gomesFiniteFockPolynomialHom_X, fockShiftMatrix_nilpotent, zero_mul]

/-- A joint symmetry is unipotent exactly when its scalar coordinate is one. -/
theorem gomesTruncatedJetJointAlgebra_unipotent_iff (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    (E.val - 1) ^ (n + 1) = 0 ↔ gomesTruncatedJetAugmentation n z E = 1 := by
  constructor
  · intro h
    have hE : (E - 1) ^ (n + 1) = 0 := Subtype.ext h
    have ha := congrArg (gomesTruncatedJetAugmentation n z) hE
    simp only [map_pow, map_sub, map_one, map_zero] at ha
    exact sub_eq_zero.mp ((pow_eq_zero_iff (Nat.succ_ne_zero n)).mp ha)
  · intro h
    simpa only [h, map_one] using gomesTruncatedJetJointAlgebra_sub_scalar_pow n z E

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
