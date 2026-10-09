import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LNDAction
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal flows of arbitrary characteristic-zero derivations

The source's divided-iterate multiplication identity does not require local
nilpotence. It therefore constructs a formal power-series flow for every
derivation. Its iterative coefficient law is the additive group law, and
coefficient one recovers the original derivation.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]

/-- The formal exponential, without any termination or analytic convergence premise. -/
def paperFormalExponential (D : Derivation k A A) : A →ₐ[k] PowerSeries A where
  toFun a := PowerSeries.mk fun n => ((n.factorial : k)⁻¹) • (D : A → A)^[n] a
  map_one' := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp
    | succ n =>
      have hz := LNDExponentialLaw.iterate_eq_zero_of_pos D (by simp : D 1 = 0)
        (Nat.succ_pos n)
      simp [hz, PowerSeries.coeff_one]
  map_mul' a b := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    exact LNDExponential.dividedIterate_mul D n a b
  map_zero' := by
    apply PowerSeries.ext
    intro n
    simp [Function.iterate_fixed (map_zero D)]
  map_add' a b := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk, map_add, LNDExponential.iterate_add, smul_add]
  commutes' c := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [PowerSeries.algebraMap_apply]
    | succ n =>
      have hz := LNDExponentialLaw.iterate_eq_zero_of_pos D
        (by simp : D (algebraMap k A c) = 0) (Nat.succ_pos n)
      simp [hz, PowerSeries.algebraMap_apply]

@[simp] theorem paperFormalExponential_coeff (D : Derivation k A A) (a : A) (n : ℕ) :
    PowerSeries.coeff n (paperFormalExponential D a) =
      ((n.factorial : k)⁻¹) • (D : A → A)^[n] a := by
  exact PowerSeries.coeff_mk (R := A) n
    (fun m => ((m.factorial : k)⁻¹) • (D : A → A)^[m] a)

@[simp] theorem paperFormalExponential_coeff_zero (D : Derivation k A A) (a : A) :
    PowerSeries.coeff 0 (paperFormalExponential D a) = a := by simp

@[simp] theorem paperFormalExponential_coeff_one (D : Derivation k A A) (a : A) :
    PowerSeries.coeff 1 (paperFormalExponential D a) = D a := by simp

/-- The formal flow retains its input exactly in its constant coefficient. -/
theorem paperFormalExponential_injective (D : Derivation k A A) :
    Function.Injective (paperFormalExponential D) := by
  intro a b h
  simpa using congrArg (PowerSeries.coeff 0) h

/-- The additive iterative law, valid even when infinitely many coefficients survive. -/
theorem paperFormalExponential_iterative (D : Derivation k A A) (a : A) (n m : ℕ) :
    PowerSeries.coeff n
        (paperFormalExponential D (PowerSeries.coeff m (paperFormalExponential D a))) =
      (n + m).choose n • PowerSeries.coeff (n + m) (paperFormalExponential D a) := by
  simp only [paperFormalExponential_coeff, LNDExponentialLaw.iterate_smul, smul_smul]
  rw [← Function.iterate_add_apply, LNDExponentialLaw.inv_factorial_mul_inv_factorial]
  rw [mul_smul]
  exact Nat.cast_smul_eq_nsmul k _ _

/-- Formal fixed elements are precisely the infinitesimal constants. -/
theorem paperFormalExponential_fixed_iff (D : Derivation k A A) (a : A) :
    paperFormalExponential D a = PowerSeries.C a ↔ D a = 0 := by
  constructor
  · intro h
    simpa using congrArg (PowerSeries.coeff 1) h
  · intro h
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [paperFormalExponential_coeff,
        LNDExponentialLaw.iterate_eq_zero_of_pos D h (Nat.succ_pos n), smul_zero]
      simp

/-- Formal exponentiation is faithful on derivations as well as on their inputs. -/
theorem paperFormalExponential_eq_iff (D E : Derivation k A A) :
    paperFormalExponential D = paperFormalExponential E ↔ D = E := by
  constructor
  · intro h
    apply Derivation.ext
    intro a
    have he := congrArg (fun F : A →ₐ[k] PowerSeries A => PowerSeries.coeff 1 (F a)) h
    simpa using he
  · rintro rfl
    rfl

/-- The identity formal flow occurs exactly for the zero derivation. -/
theorem paperFormalExponential_trivial_iff (D : Derivation k A A) :
    (∀ a, paperFormalExponential D a = PowerSeries.C a) ↔ D = 0 := by
  simp only [paperFormalExponential_fixed_iff]
  constructor
  · intro h
    apply Derivation.ext
    exact h
  · rintro rfl
    simp

/-- Every homomorphism intertwining derivations intertwines their complete formal flows. -/
theorem paperFormalExponential_naturality {B : Type*} [CommRing B] [Algebra k B]
    (D : Derivation k A A) (E : Derivation k B B) (f : A →ₐ[k] B)
    (h : ∀ a, E (f a) = f (D a)) (a : A) :
    paperFormalExponential E (f a) =
      PowerSeries.map f.toRingHom (paperFormalExponential D a) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, paperFormalExponential_coeff, paperFormalExponential_coeff,
    derivation_iterate_naturality D E f h]
  exact (f.toLinearMap.map_smul _ _).symm

end

end GaloisForLFunctions.HTGeometry
