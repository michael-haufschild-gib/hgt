import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LNDAction

/-!
# Exact linear orbits of a locally nilpotent action

This reusable source-exponential calculation was first used privately for
discriminant translation. It also gives literal prime-coordinate translations.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

/-- An element killed by the second derivative has an exact affine polynomial orbit. -/
theorem paperLND_exponential_linear_on {K A : Type*} [Field K] [CharZero K]
    [CommRing A] [Algebra K A]
    (D : Derivation K A A) (hD : IsLocallyNilpotent D) (a : A) (h : D (D a) = 0) :
    (exponentialAction D hD).toAlgHom a =
      Polynomial.C a + Polynomial.C (D a) * Polynomial.X := by
  rw [exponentialAction_toAlgHom]
  ext m
  cases m with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp
    | succ m =>
      have htwo : (D : A → A)^[2] a = 0 := h
      have hz := derivation_iterate_eq_zero_of_le D htwo
        (show 2 ≤ m + 1 + 1 by omega)
      simp [hz, Polynomial.coeff_mul_X]

end

end GaloisForLFunctions.HTGeometry
