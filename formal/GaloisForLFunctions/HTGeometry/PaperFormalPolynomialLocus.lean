import GaloisForLFunctions.HTGeometry.PaperFormalExponential
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The exact polynomial locus of a formal derivation flow

An input has polynomial formal orbit exactly when an iterate of the
derivation kills it. Thus the source's polynomial additive actions are
precisely the terminating instances of the unrestricted formal construction.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]

/-- Truncation at a specified order is exact precisely at that annihilation order. -/
theorem paperFormalExponential_trunc_iff (D : Derivation k A A) (a : A) (m : ℕ) :
    paperFormalExponential D a =
        (PowerSeries.trunc m (paperFormalExponential D a) : PowerSeries A) ↔
      (D : A → A)^[m] a = 0 := by
  constructor
  · intro h
    have hc := congrArg (PowerSeries.coeff m) h
    rw [paperFormalExponential_coeff, Polynomial.coeff_coe, PowerSeries.coeff_trunc] at hc
    simp only [lt_self_iff_false, ↓reduceIte] at hc
    exact (smul_eq_zero.mp hc).resolve_left
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)))
  · intro h
    apply PowerSeries.ext
    intro n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    by_cases hn : n < m
    · simp [hn]
    · have hz := derivation_iterate_eq_zero_of_le D h (show m ≤ n by omega)
      simp [hn, paperFormalExponential_coeff, hz]

/-- Polynomial-valued inputs are exactly the elements with a terminating derivative tower. -/
theorem paperFormalExponential_polynomial_iff (D : Derivation k A A) (a : A) :
    (∃ P : Polynomial A, paperFormalExponential D a = (P : PowerSeries A)) ↔
      ∃ n : ℕ, (D : A → A)^[n] a = 0 := by
  constructor
  · rintro ⟨P, h⟩
    have hc := congrArg (PowerSeries.coeff (P.natDegree + 1)) h
    rw [paperFormalExponential_coeff, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at hc
    exact ⟨P.natDegree + 1, (smul_eq_zero.mp hc).resolve_left
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))⟩
  · rintro ⟨n, hn⟩
    exact ⟨PowerSeries.trunc n (paperFormalExponential D a),
      (paperFormalExponential_trunc_iff D a n).mpr hn⟩

/-- Local nilpotence is exactly the condition that every formal orbit is polynomial. -/
theorem paperFormalExponential_all_polynomial_iff (D : Derivation k A A) :
    (∀ a, ∃ P : Polynomial A, paperFormalExponential D a = (P : PowerSeries A)) ↔
      IsLocallyNilpotent D := by
  simp only [paperFormalExponential_polynomial_iff, IsLocallyNilpotent]

/-- A linear orbit needs only the input's second derivative to vanish. -/
theorem paperFormalExponential_linear_on (D : Derivation k A A) (a : A)
    (h : D (D a) = 0) :
    paperFormalExponential D a = PowerSeries.C a + PowerSeries.C (D a) * PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      have hz := derivation_iterate_eq_zero_of_le D (m := 2) h
        (show 2 ≤ n + 1 + 1 by omega)
      simp [paperFormalExponential_coeff, hz]

/-- The formal construction recovers the source polynomial exponential coefficient for coefficient. -/
theorem paperFormalExponential_of_locallyNilpotent (D : Derivation k A A)
    (hD : IsLocallyNilpotent D) (a : A) :
    paperFormalExponential D a =
      (LNDExponential.exponential D hD a : PowerSeries A) := by
  apply PowerSeries.ext
  intro n
  rw [paperFormalExponential_coeff, Polynomial.coeff_coe,
    LNDExponential.coeff_exponential]

/-- In particular the source's complete polynomial action embeds into this formal flow. -/
theorem paperFormalExponential_eq_additiveAction (D : Derivation k A A)
    (hD : IsLocallyNilpotent D) (a : A) :
    paperFormalExponential D a =
      ((exponentialAction D hD).toAlgHom a : PowerSeries A) := by
  rw [exponentialAction_toAlgHom]
  exact paperFormalExponential_of_locallyNilpotent D hD a

end

end GaloisForLFunctions.HTGeometry
