import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The displacement identity of a critical fibre

Two jets with reciprocals agree in the critical range exactly when their difference and the
difference of their reciprocals are linked by

`A' - A = (B - B') A A'   modulo the horizon`,

which holds for any two reciprocal pairs by the polynomial identity

`(B - B') A A' - (A' - A) = A' (A B - 1) - A (A' B' - 1)`.

So a second point of a critical fibre over the same observation is the same thing as a pair
`(U, D)` — the raw displacement, of degree below the raw critical order, and the reciprocal
displacement, of degree below the reciprocal critical order — subject to the single quadratic
relation `U = D A (A + U)`.  That is the equation whose second solution is the atomic ambiguity of
the horizon: the displacement equation is quadratic in `U`, so the fibre doubles, and the
displacement is nonzero exactly when the two points are distinct.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R]

/-- **The displacement identity.**  The difference of two raw jets equals the difference of their
reciprocals times the product of the jets, up to the two inversion errors. -/
theorem fibreDisplacement_identity (A B A' B' : R[X]) :
    (B - B') * A * A' - (A' - A) = A' * (A * B - 1) - A * (A' * B' - 1) := by
  ring

/-- **Two reciprocal pairs are displaced by the identity.**  Over the horizon, the raw displacement
is the reciprocal displacement times the product of the two jets. -/
theorem dvd_fibreDisplacement {L : ℕ} {A B A' B' : R[X]}
    (h : (X : R[X]) ^ L ∣ A * B - 1) (h' : (X : R[X]) ^ L ∣ A' * B' - 1) :
    (X : R[X]) ^ L ∣ (B - B') * A * A' - (A' - A) := by
  rw [fibreDisplacement_identity]
  exact dvd_sub (h.mul_left A') (h'.mul_left A)

/-- **The displacement equation.**  Writing `U` for the raw displacement and `D` for the reciprocal
displacement, the two are linked by `U = D A (A + U)` over the horizon. -/
theorem dvd_displacement_equation {L : ℕ} {A B A' B' : R[X]}
    (h : (X : R[X]) ^ L ∣ A * B - 1) (h' : (X : R[X]) ^ L ∣ A' * B' - 1) :
    (X : R[X]) ^ L ∣ (A' - A) - (B - B') * A * (A + (A' - A)) := by
  have hrw : (A' - A) - (B - B') * A * (A + (A' - A))
      = -((B - B') * A * A' - (A' - A)) := by ring
  rw [hrw]
  exact dvd_neg.2 (dvd_fibreDisplacement h h')

/-- **The converse.**  A raw displacement satisfying the displacement equation against a reciprocal
displacement produces a second reciprocal pair, with the displaced jet and the displaced
reciprocal. -/
theorem reciprocal_of_displacement {L : ℕ} {A B U D : R[X]}
    (h : (X : R[X]) ^ L ∣ A * B - 1)
    (hUD : (X : R[X]) ^ L ∣ U - D * A * (A + U)) :
    (X : R[X]) ^ L ∣ (A + U) * (B - D) - 1 := by
  have hrw : (A + U) * (B - D) - 1
      = (A * B - 1) + (U - D * A * (A + U)) * B + D * (A + U) * (A * B - 1) := by ring
  rw [hrw]
  exact dvd_add (dvd_add h (hUD.mul_right B)) (h.mul_left (D * (A + U)))

/-! ## The critical range is unchanged

A displacement of low degree changes no coefficient in the critical range.  So a solution of the
displacement equation with both displacements of low degree is a second point of the same critical
fibre.
-/

/-- **A low-degree raw displacement leaves the raw critical coefficients alone.** -/
theorem coeff_add_eq_of_degree_lt {A U : R[X]} {m i : ℕ} (hU : U.degree < (m : ℕ))
    (hi : m ≤ i) : (A + U).coeff i = A.coeff i := by
  rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_degree_lt
    (lt_of_lt_of_le hU (by exact_mod_cast hi)), add_zero]

/-- **A low-degree reciprocal displacement leaves the reciprocal critical coefficients alone.** -/
theorem coeff_sub_eq_of_degree_lt {B D : R[X]} {n j : ℕ} (hD : D.degree < (n : ℕ))
    (hj : n ≤ j) : (B - D).coeff j = B.coeff j := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_degree_lt
    (lt_of_lt_of_le hD (by exact_mod_cast hj)), sub_zero]

/-- **A nonzero solution of the displacement equation is a second point of the same critical
fibre.**  The displaced pair inverts to the horizon, agrees with the original in every raw
coefficient from the raw critical order on and in every reciprocal coefficient from the reciprocal
critical order on, and is distinct from it. -/
theorem exists_second_fibre_point {L m n : ℕ} {A B U D : R[X]}
    (h : (X : R[X]) ^ L ∣ A * B - 1)
    (hUD : (X : R[X]) ^ L ∣ U - D * A * (A + U))
    (hU : U.degree < (m : ℕ)) (hD : D.degree < (n : ℕ)) (hU0 : U ≠ 0) :
    (X : R[X]) ^ L ∣ (A + U) * (B - D) - 1 ∧
      (∀ i, m ≤ i → (A + U).coeff i = A.coeff i) ∧
      (∀ j, n ≤ j → (B - D).coeff j = B.coeff j) ∧
      A + U ≠ A :=
  ⟨reciprocal_of_displacement h hUD,
    fun _ hi => coeff_add_eq_of_degree_lt hU hi,
    fun _ hj => coeff_sub_eq_of_degree_lt hD hj,
    fun hcon => hU0 (by
      have := congrArg (fun p => p - A) hcon
      simpa using this)⟩

end GaloisForLFunctions.HTGeometry
