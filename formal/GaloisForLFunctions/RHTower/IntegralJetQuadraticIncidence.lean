import GaloisForLFunctions.RHTower.CompletedSEMContourBoundary

/-!
# Quadratic incidence on the integral divisor-jet lattice

The constant coefficient of an integral divisor jet is an integer before any finite reduction.
Its square therefore gives a canonical quadratic function on `Z[X]/(X^m)`.  On the actual
completed symmetric Euler--Maclaurin contour boundary, this function is the square of the winding
index, hence the square of both the isolated SEM hole count and the local Xi order.

This is a source-to-quadratic bridge.  It does not distinguish reflection-fixed zeros from free
reflection pairs and does not prove that a global source constraint annihilates a fixed-point
corrected sum of these local squares.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Constant-coefficient evaluation of an integral polynomial, before finite reduction. -/
def coeffZeroRingHomInt : Polynomial ℤ →+* ℤ :=
  Polynomial.evalRingHom 0

@[simp] theorem coeffZeroRingHomInt_C (t : ℤ) :
    coeffZeroRingHomInt (C t) = t := by
  simp [coeffZeroRingHomInt]

/-- Positive powers of `X` have zero integral constant coefficient. -/
theorem coeffZeroRingHomInt_X_pow (m : ℕ) (hm : 1 ≤ m) :
    coeffZeroRingHomInt ((X : ℤ[X]) ^ m) = 0 := by
  simp [coeffZeroRingHomInt, zero_pow (show m ≠ 0 by omega)]

/-- Integral constant-coefficient evaluation descends to the truncated divisor-jet ring. -/
def jetCoeffZeroRingHomInt (m : ℕ) (hm : 1 ≤ m) :
    LocalDivisorJet ℤ m →+* ℤ :=
  Ideal.Quotient.lift (jetIdeal ℤ m) coeffZeroRingHomInt (by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, coeffZeroRingHomInt_X_pow m hm, zero_mul])

@[simp] theorem jetCoeffZeroRingHomInt_jetClass
    (m : ℕ) (hm : 1 ≤ m) (P : Polynomial ℤ) :
    jetCoeffZeroRingHomInt m hm (jetClass ℤ m P) = coeffZeroRingHomInt P := by
  rw [jetClass, jetCoeffZeroRingHomInt, Ideal.Quotient.lift_mk]

/-- Square of the canonical integral constant coefficient of a divisor jet. -/
def integralJetQuadraticIndex (m : ℕ) (hm : 1 ≤ m)
    (J : LocalDivisorJet ℤ m) : ℤ :=
  (jetCoeffZeroRingHomInt m hm J) ^ (2 : ℕ)

@[simp] theorem integralJetQuadraticIndex_constJet
    (m : ℕ) (hm : 1 ≤ m) (t : ℤ) :
    integralJetQuadraticIndex m hm (jetClass ℤ m (C t)) = t ^ (2 : ℕ) := by
  simp [integralJetQuadraticIndex]

/-- The source-defined completed-SEM contour boundary has quadratic index equal to the square of
its actual winding number. -/
theorem integralJetQuadraticIndex_completedSEMContourBoundaryZ
    (ρ : ℂ) (r₀ R : ℝ) (N m : ℕ) (hm : 1 ≤ m) :
    integralJetQuadraticIndex m hm
        (completedSEMContourBoundaryZ ρ r₀ R N m) =
      (completedSEMContourIndexZ ρ r₀ R N) ^ (2 : ℕ) := by
  rw [completedSEMContourBoundaryZ_eq_indexJet]
  exact integralJetQuadraticIndex_constJet m hm _

/-- On a dominating SEM split, the source quadratic index is the square of the isolated hole
count. -/
theorem integralJetQuadraticIndex_eq_splitCount_sq
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) {m : ℕ} (hm : 1 ≤ m) :
    integralJetQuadraticIndex m hm
        (completedSEMContourBoundaryZ ρ r₀ R N m) =
      (zs.length : ℤ) ^ (2 : ℕ) := by
  rw [integralJetQuadraticIndex_completedSEMContourBoundaryZ,
    completedSEMContourIndexZ_eq_splitCount h]

/-- On a dominating SEM split, the source quadratic index is the square of the local Xi order. -/
theorem integralJetQuadraticIndex_eq_xiOrder_sq
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) {m : ℕ} (hm : 1 ≤ m) :
    integralJetQuadraticIndex m hm
        (completedSEMContourBoundaryZ ρ r₀ R N m) =
      (((analyticOrderAt xi ρ).toNat : ℤ) ^ (2 : ℕ)) := by
  rw [integralJetQuadraticIndex_completedSEMContourBoundaryZ,
    completedSEMContourIndexZ_eq_xiOrder h]

end


end RHTower
