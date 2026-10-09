import GaloisForLFunctions.HTGeometry.PaperStabilizedPolynomialClock
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LNDAction
import Mathlib.Algebra.Polynomial.Roots

/-!
# Integrating the actual stabilized clock

The source's exponential correspondence integrates the constructed clock to
a polynomial additive action and genuine scalar algebra automorphisms. The
distinguished polynomial translates, the complementary coordinates stay fixed,
and scalar fixed elements are exactly the kernel of the native clock.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

/-- The polynomial additive action of the already constructed stabilized clock. -/
def paperStabilizedAction : PolynomialAdditiveAction ℂ (R 5) :=
  exponentialAction paperStabilizedClock paperStabilizedClock_locallyNilpotent

@[simp] theorem paperStabilizedAction_derivation :
    paperStabilizedAction.derivation = paperStabilizedClock :=
  exponentialAction_derivation _ _

/-- The action translates the actual source polynomial by its formal parameter. -/
theorem paperStabilizedAction_f :
    paperStabilizedAction.toAlgHom (stabilize f) =
      Polynomial.C (stabilize f) + Polynomial.X := by
  ext n
  cases n with
  | zero => simp [paperStabilizedAction]
  | succ n =>
    cases n with
    | zero => simp [paperStabilizedAction, paperStabilizedClock_slice]
    | succ n =>
      have htwo : (paperStabilizedClock : R 5 → R 5)^[2] (stabilize f) = 0 := by
        simp [Function.iterate_succ_apply, paperStabilizedClock_slice]
      have hz := derivation_iterate_eq_zero_of_le paperStabilizedClock htwo
        (show 2 ≤ n + 1 + 1 by omega)
      simp [paperStabilizedAction, hz, Polynomial.coeff_X]

/-- The formal action fixes all four complementary coordinates. -/
theorem paperStabilizedAction_complementary (i : Fin 4) :
    paperStabilizedAction.toAlgHom
      (paperStabilizedCoordinateEquiv.symm (MvPolynomial.X i.succ)) =
      Polynomial.C (paperStabilizedCoordinateEquiv.symm (MvPolynomial.X i.succ)) :=
  (exponentialAction_fixed_iff _ _ _).mpr (paperStabilizedClock_complementary_constant i)

/-- Each complex time gives an actual automorphism of the five-variable algebra. -/
def paperStabilizedTranslation (t : ℂ) : R 5 ≃ₐ[ℂ] R 5 :=
  paperStabilizedAction.specializeEquiv t

@[simp] theorem paperStabilizedTranslation_zero (p : R 5) :
    paperStabilizedTranslation 0 p = p :=
  paperStabilizedAction.specialize_zero p

theorem paperStabilizedTranslation_add (s t : ℂ) (p : R 5) :
    paperStabilizedTranslation s (paperStabilizedTranslation t p) =
      paperStabilizedTranslation (s + t) p :=
  paperStabilizedAction.specialize_add s t p

@[simp] theorem paperStabilizedTranslation_f (t : ℂ) :
    paperStabilizedTranslation t (stabilize f) = stabilize f + MvPolynomial.C t := by
  simp [paperStabilizedTranslation, PolynomialAdditiveAction.specialize_apply,
    paperStabilizedAction_f]

@[simp] theorem paperStabilizedTranslation_complementary (t : ℂ) (i : Fin 4) :
    paperStabilizedTranslation t (paperStabilizedCoordinateEquiv.symm (MvPolynomial.X i.succ)) =
      paperStabilizedCoordinateEquiv.symm (MvPolynomial.X i.succ) := by
  simp [paperStabilizedTranslation, PolynomialAdditiveAction.specialize_apply,
    paperStabilizedAction_complementary]

/-- Distinct scalar times give distinct automorphisms. -/
theorem paperStabilizedTranslation_injective : Function.Injective paperStabilizedTranslation := by
  intro s t h
  have he := DFunLike.congr_fun h (stabilize f)
  rw [paperStabilizedTranslation_f, paperStabilizedTranslation_f] at he
  exact (algebraMap ℂ (R 5)).injective (add_left_cancel he)

/-- Being fixed at every scalar time is exactly the infinitesimal kernel condition. -/
theorem paperStabilizedTranslation_fixed_iff (p : R 5) :
    (∀ t : ℂ, paperStabilizedTranslation t p = p) ↔ paperStabilizedClock p = 0 := by
  constructor
  · intro h
    apply (exponentialAction_fixed_iff paperStabilizedClock
      paperStabilizedClock_locallyNilpotent p).mp
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (algebraMap ℂ (R 5)).injective).mono
    rintro _ ⟨t, rfl⟩
    simpa [paperStabilizedTranslation, paperStabilizedAction,
      PolynomialAdditiveAction.specialize_apply] using h t
  · intro h t
    have he := (exponentialAction_fixed_iff paperStabilizedClock
      paperStabilizedClock_locallyNilpotent p).mpr h
    change paperStabilizedAction.toAlgHom p = Polynomial.C p at he
    simp [paperStabilizedTranslation, PolynomialAdditiveAction.specialize_apply, he]

end

end GaloisForLFunctions.HTGeometry
