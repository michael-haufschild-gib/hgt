import GaloisForLFunctions.HTGeometry.PaperSplitPolynomialClockMultipliers
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LocalizationLND

/-!
# Multiplier rigidity for the native finite-étale polynomial clock

The native splitting theorem pays for a product presentation. The source
local-nilpotence criterion then classifies all speeds of the lifted clock,
including finite-étale rings with zero divisors.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate Polynomial

noncomputable section

variable {K B : Type*} [Field K]
  [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B]
  [Module.Free K[X] B] [Module.Finite K[X] B]
  {n : ℕ} (e : Module.Basis (Fin n) K[X] B) (hd : IsUnit (Algebra.discr K[X] e))

/-- Every polynomial-algebra splitting carries the native lift to component differentiation. -/
theorem paperEtalePolynomialClock_split (Φ : B ≃ₐ[K[X]] (Fin n → K[X])) (b : B) :
    Φ (Lift.liftDerivation e hd (polyDeriv K) b) = piPolyDeriv K n (Φ b) := by
  let E := Φ.restrictScalars K
  let D := Lift.liftDerivation e hd (polyDeriv K)
  have hdisc : IsUnit (Algebra.discr K[X] (Pi.basisFun K[X] (Fin n))) := by
    rw [discr_pi_basisFun]
    exact isUnit_one
  have heq : LocalizationLND.transport D E = piPolyDeriv K n := by
    apply Lift.derivation_ext (Pi.basisFun K[X] (Fin n)) hdisc
    intro p
    rw [← Φ.commutes p]
    change LocalizationLND.transport D E (E (algebraMap K[X] B p)) = _
    rw [LocalizationLND.transport_apply]
    change Φ (Lift.liftDerivation e hd (polyDeriv K) (algebraMap K[X] B p)) = _
    rw [Lift.liftDerivation_algebraMap, Φ.commutes, Φ.commutes]
    funext i
    rfl
  have h := congrArg (fun d : Derivation K (Fin n → K[X]) (Fin n → K[X]) => d (E b)) heq
  rw [LocalizationLND.transport_apply] at h
  exact h

/-- The splitting intertwines every iterate, even for a speed depending on the state. -/
theorem paperEtalePolynomialClockMultiplier_iterate
    (Φ : B ≃ₐ[K[X]] (Fin n → K[X])) (q b : B) (m : ℕ) :
    Φ (((q • Lift.liftDerivation e hd (polyDeriv K) : Derivation K B B) : B → B)^[m] b) =
      (((Φ q • piPolyDeriv K n : Derivation K (Fin n → K[X]) (Fin n → K[X])) :
        (Fin n → K[X]) → (Fin n → K[X]))^[m]) (Φ b) := by
  induction m generalizing b with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    congr 1
    change Φ (q * Lift.liftDerivation e hd (polyDeriv K) b) =
      Φ q * piPolyDeriv K n (Φ b)
    rw [map_mul, paperEtalePolynomialClock_split]

/-- Every derivation of the finite-étale algebra is determined by its speed on the base coordinate. -/
theorem paperEtalePolynomialDerivation_eq_clock
    (D : Derivation K B B) :
    D = D (algebraMap K[X] B Polynomial.X) • Lift.liftDerivation e hd (polyDeriv K) := by
  apply Lift.derivation_ext e hd
  have heq : D.compAlgebraMap K[X] =
      (D (algebraMap K[X] B Polynomial.X) •
        Lift.liftDerivation e hd (polyDeriv K)).compAlgebraMap K[X] := by
    apply Polynomial.derivation_ext
    simp [Derivation.compAlgebraMap_apply, Lift.liftDerivation_algebraMap]
  intro p
  exact congrArg (fun d : Derivation K K[X] B => d p) heq

variable [CharZero K] [IsAlgClosed K]

/-- A speed preserves termination precisely when the lifted clock fixes that speed. -/
theorem paperEtalePolynomialClock_multiplier_iff (q : B) :
    IsLocallyNilpotent (q • Lift.liftDerivation e hd (polyDeriv K)) ↔
      Lift.liftDerivation e hd (polyDeriv K) q = 0 := by
  constructor
  · intro h
    obtain ⟨Φ⟩ := nonempty_algEquiv_pi_of_isUnit_discr K n e hd
    have hP : IsLocallyNilpotent (Φ q • piPolyDeriv K n) := by
      intro f
      obtain ⟨b, rfl⟩ := Φ.surjective f
      obtain ⟨m, hm⟩ := h b
      refine ⟨m, ?_⟩
      rw [← paperEtalePolynomialClockMultiplier_iterate e hd Φ, hm, map_zero]
    apply Φ.injective
    rw [paperEtalePolynomialClock_split, map_zero]
    funext i
    exact (paperPiPolynomialClock_multiplier_iff (Φ q)).mp hP i
  · exact paperLND_invariant_smul _ (locallyNilpotent_liftDerivation K e hd) q

/-- In any splitting, the allowed speeds are exactly independent constants on the components. -/
theorem paperEtalePolynomialClock_multiplier_iff_constants
    (Φ : B ≃ₐ[K[X]] (Fin n → K[X])) (q : B) :
    IsLocallyNilpotent (q • Lift.liftDerivation e hd (polyDeriv K)) ↔
      ∀ i, Φ q i = Polynomial.C ((Φ q i).coeff 0) := by
  rw [paperEtalePolynomialClock_multiplier_iff e hd]
  constructor
  · intro h i
    apply Polynomial.eq_C_of_derivative_eq_zero
    have he := paperEtalePolynomialClock_split e hd Φ q
    rw [h, map_zero] at he
    exact (congrFun he i).symm
  · intro h
    apply Φ.injective
    rw [paperEtalePolynomialClock_split, map_zero]
    funext i
    change (Φ q i).derivative = 0
    rw [h i]
    simp

/-- Every independently chosen constant speed on the split components is realizable. -/
theorem paperEtalePolynomialClock_constantSpeeds_locallyNilpotent
    (Φ : B ≃ₐ[K[X]] (Fin n → K[X])) (c : Fin n → K) :
    IsLocallyNilpotent (Φ.symm (fun i => Polynomial.C (c i)) •
      Lift.liftDerivation e hd (polyDeriv K)) := by
  apply (paperEtalePolynomialClock_multiplier_iff_constants e hd Φ _).mpr
  intro i
  simp

/-- All locally nilpotent derivations are uniquely parametrized by invariant clock speeds. -/
theorem paperEtalePolynomialLND_classification (D : Derivation K B B) :
    IsLocallyNilpotent D ↔ ∃! q : B,
      Lift.liftDerivation e hd (polyDeriv K) q = 0 ∧
        D = q • Lift.liftDerivation e hd (polyDeriv K) := by
  constructor
  · intro hD
    have heq := paperEtalePolynomialDerivation_eq_clock e hd D
    refine ⟨D (algebraMap K[X] B Polynomial.X), ⟨?_, heq⟩, ?_⟩
    · apply (paperEtalePolynomialClock_multiplier_iff e hd _).mp
      rwa [← heq]
    · intro q hq
      have hx := congrArg (fun d : Derivation K B B => d (algebraMap K[X] B Polynomial.X)) hq.2
      simpa [Lift.liftDerivation_algebraMap] using hx.symm
  · rintro ⟨q, ⟨hq, rfl⟩, _⟩
    exact (paperEtalePolynomialClock_multiplier_iff e hd q).mpr hq

end

end GaloisForLFunctions.HTGeometry
