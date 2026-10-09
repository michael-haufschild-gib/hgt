import GaloisForLFunctions.HTGeometry.PaperLocallyNilpotentMultipliers
import GaloisForLFunctions.HTGeometry.AffineLineEtaleLocallyNilpotent

/-!
# Exact multiplier classification for the native split polynomial clock

The native finite-product derivative lives in a ring with zero divisors.
Its multiplier problem still reduces to the source domain criterion on
each component. Termination survives precisely for a separate constant
speed on each polynomial component, including the empty-product case.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate Polynomial

noncomputable section

private theorem native_polyDeriv_locallyNilpotent (R : Type*) [CommRing R] :
    IsLocallyNilpotent (polyDeriv R) := by
  intro p
  refine ⟨p.natDegree + 1, ?_⟩
  change (Polynomial.derivative^[p.natDegree + 1]) p = 0
  exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)

/-- Every weighted native product-clock iterate is the weighted component-clock iterate. -/
theorem paperPiPolynomialClockMultiplier_iterate
    {R : Type*} [CommRing R] {n : ℕ} (q : Fin n → Polynomial R)
    (m : ℕ) (f : Fin n → Polynomial R) (i : Fin n) :
    (((q • piPolyDeriv R n : Derivation R (Fin n → Polynomial R) (Fin n → Polynomial R)) :
      (Fin n → Polynomial R) → (Fin n → Polynomial R))^[m] f) i =
      (((q i • polyDeriv R : Derivation R (Polynomial R) (Polynomial R)) :
        Polynomial R → Polynomial R)^[m]) (f i) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    rfl

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The domain multiplier criterion remains exact on the native finite product, componentwise. -/
theorem paperPiPolynomialClock_multiplier_iff (q : Fin n → Polynomial K) :
    IsLocallyNilpotent (q • piPolyDeriv K n) ↔ ∀ i, (q i).derivative = 0 := by
  constructor
  · intro h i
    have hi : IsLocallyNilpotent (q i • polyDeriv K) := by
      intro p
      obtain ⟨m, hm⟩ := h (fun _ => p)
      refine ⟨m, ?_⟩
      have he := congrFun hm i
      rw [paperPiPolynomialClockMultiplier_iterate] at he
      exact he
    exact (paperLND_smul_iff (polyDeriv K) (native_polyDeriv_locallyNilpotent K) (q i)).mp hi
  · intro h
    apply paperLND_invariant_smul (piPolyDeriv K n) (locallyNilpotent_piPolyDeriv K n) q
    funext i
    exact h i

/-- All permitted polynomial-valued speeds are exactly the componentwise constant polynomials. -/
theorem paperPiPolynomialClock_multiplier_iff_constants (q : Fin n → Polynomial K) :
    IsLocallyNilpotent (q • piPolyDeriv K n) ↔ ∀ i, q i = Polynomial.C ((q i).coeff 0) := by
  rw [paperPiPolynomialClock_multiplier_iff]
  constructor
  · intro h i
    exact Polynomial.eq_C_of_derivative_eq_zero (h i)
  · intro h i
    rw [h i]
    simp

/-- Every family of independent scalar component speeds gives a terminating native clock. -/
theorem paperPiPolynomialClock_constantSpeeds_locallyNilpotent (c : Fin n → K) :
    IsLocallyNilpotent ((fun i => Polynomial.C (c i)) • piPolyDeriv K n) := by
  apply (paperPiPolynomialClock_multiplier_iff _).mpr
  intro i
  simp

/-- Weighting every component derivative by its own polynomial variable destroys termination. -/
theorem paperPiPolynomialClock_coordinate_not_locallyNilpotent (n : ℕ) :
    ¬ IsLocallyNilpotent
      ((fun _ : Fin (n + 1) => (Polynomial.X : Polynomial K)) • piPolyDeriv K (n + 1)) := by
  intro h
  have he := (paperPiPolynomialClock_multiplier_iff _).mp h (0 : Fin (n + 1))
  simp at he

end

end GaloisForLFunctions.HTGeometry
