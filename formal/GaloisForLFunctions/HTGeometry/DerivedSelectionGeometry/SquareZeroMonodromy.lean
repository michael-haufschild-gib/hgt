import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.ReflectionEnergy
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.RiemannPullback

/-!
# Square-zero infinitesimal monodromy

For `h` with `h² = 0` in a commutative ring, `q = 1 + h` and `v = 1 - h` are mutually inverse,
the reflected energy `q + v - 2` vanishes and the ambidextrous curvature `q - v` equals `2h`.
When multiplication by `2` is injective, `2h = 0`, `h = 0` and `q = 1` are equivalent.  The
Laurent monodromy line has exactly one specialization sending its coordinate to a given unit.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open LaurentPolynomial

universe u

section SquareZero

variable {R : Type*} [CommRing R] {h : R}

theorem squareZero_monodromy_mul_inv (hh : h ^ 2 = 0) : (1 + h) * (1 - h) = 1 := by
  linear_combination -hh

theorem squareZero_monodromy_inv_mul (hh : h ^ 2 = 0) : (1 - h) * (1 + h) = 1 := by
  linear_combination -hh

/-- The square-zero monodromy as a unit. -/
def squareZeroMonodromyUnit (hh : h ^ 2 = 0) : Rˣ where
  val := 1 + h
  inv := 1 - h
  val_inv := squareZero_monodromy_mul_inv hh
  inv_val := squareZero_monodromy_inv_mul hh

/-- **(NIMM.3)** The reflected energy of square-zero monodromy vanishes. -/
theorem squareZero_reflEnergy (h : R) : reflEnergy (1 + h) (1 - h) = 0 := by
  unfold reflEnergy; ring

/-- **(NIMM.3)** The ambidextrous curvature is `2h`. -/
theorem squareZero_ambiCurvature (h : R) : ambiCurvature (1 + h) (1 - h) = 2 * h := by
  unfold ambiCurvature; ring

/-- **Corollary 3.2 (NIMM.5)** With `2` cancellable, curvature vanishes iff the tangent does. -/
theorem squareZero_ambiCurvature_eq_zero_iff (h2 : ∀ x : R, 2 * x = 0 → x = 0) (h : R) :
    ambiCurvature (1 + h) (1 - h) = 0 ↔ h = 0 := by
  rw [squareZero_ambiCurvature]
  exact ⟨h2 h, fun hz => by rw [hz, mul_zero]⟩

theorem squareZero_monodromy_eq_one_iff (h : R) : 1 + h = 1 ↔ h = 0 := by
  constructor
  · intro e; linear_combination e
  · intro e; rw [e, add_zero]

end SquareZero

section Specialization

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

theorem specializeHom_T (b : Aˣ) (n : ℤ) : specializeHom b (T n : MonodromyRing k) = ↑(b ^ n) := by
  rw [specializeHom, LaurentPolynomial.eval₂_T]

/-- **Uniqueness of the specialization.**  A ring map from the Laurent monodromy line which is
`k`-linear on constants and sends the coordinate to the unit `b` is the specialization at `b`. -/
theorem eq_specializeHom (b : Aˣ) (φ : MonodromyRing k →+* A)
    (hC : ∀ a : k, φ (C a) = algebraMap k A a) (hq : φ (monodromyParam k) = b) :
    φ = specializeHom b := by
  have hT : ∀ n : ℤ, φ (T n) = ↑(b ^ n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [T_zero]
    | succ n ih =>
      rw [T_add, map_mul, ih, show φ (T 1) = b from hq, zpow_add_one, Units.val_mul]
    | pred n ih =>
      have h1 : φ (T (-(n : ℤ) - 1)) * b = ↑(b ^ (-(n : ℤ))) := by
        rw [← ih, ← show φ (T 1) = b from hq, ← map_mul, ← T_add]
        congr 2; ring
      calc φ (T (-(n : ℤ) - 1)) = φ (T (-(n : ℤ) - 1)) * b * ↑b⁻¹ := by
            rw [mul_assoc, Units.mul_inv, mul_one]
        _ = ↑(b ^ (-(n : ℤ) - 1)) := by
            rw [h1, zpow_sub_one, Units.val_mul]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq' => rw [map_add, map_add, hp, hq']
  | C_mul_T n a =>
    rw [map_mul, map_mul, hC, hT, specializeHom_T]
    simp [specializeHom]

end Specialization

end GaloisForLFunctions.HTGeometry.DerivedSelection
