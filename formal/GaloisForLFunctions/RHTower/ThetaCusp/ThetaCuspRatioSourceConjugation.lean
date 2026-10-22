import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioSquareSlopeSeam
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Real coefficients of the modular ratio source polynomials

Coefficientwise complex conjugation fixes the integer source field, hence every integer jet,
reflection, the third minor and the third slope.  The squared chart `U ↦ U²` is injective (evaluate
after choosing a square root of the `U`-coordinate), so the shear/square factorization of the
third slope transports this to the reduced slope: `reducedSlope` has real coefficients.
-/

namespace HTGeometry.ThetaRatioSquare
noncomputable section
open MvPolynomial ThetaRatioSource ComplexConjugate

/-- Coefficientwise complex conjugation of source polynomials. -/
abbrev conjSourcePoly : Poly →+* Poly := MvPolynomial.map (starRingEnd ℂ)

@[simp] theorem conjSourcePoly_X (i : Coord) : conjSourcePoly (X i) = X i := map_X _ _

@[simp] theorem conjSourcePoly_ofNat (n : ℕ) [n.AtLeastTwo] : conjSourcePoly (ofNat(n) : Poly) = ofNat(n) :=
  map_ofNat _ n

theorem conjSourcePoly_pderiv (i : Coord) (P : Poly) : conjSourcePoly (pderiv i P) = pderiv i (conjSourcePoly P) :=
  pderiv_map.symm

theorem conjSourcePoly_conjSourcePoly (P : Poly) : conjSourcePoly (conjSourcePoly P) = P := by
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext c; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

/-- An evaluation homomorphism whose coordinates have real coefficients commutes with conjugation. -/
theorem conjSourcePoly_eval₂Hom (g : Coord → Poly) (hg : ∀ i, conjSourcePoly (g i) = g i) (P : Poly) :
    conjSourcePoly (eval₂Hom C g P) = eval₂Hom C g (conjSourcePoly P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, eval₂Hom_X', conjSourcePoly_X, hg]

theorem conjSourcePoly_integerField (i : Coord) : conjSourcePoly (integerField i) = integerField i := by
  cases i <;> simp [integerField]

theorem conjSourcePoly_integerLie (P : Poly) : conjSourcePoly (integerLie P) = integerLie (conjSourcePoly P) := by
  simp only [integerLie, map_sum, map_mul, conjSourcePoly_pderiv, conjSourcePoly_integerField]

theorem conjSourcePoly_integerStep (P : Poly) : conjSourcePoly (integerStep P) = integerStep (conjSourcePoly P) := by
  simp [integerStep, conjSourcePoly_integerLie]

theorem conjSourcePoly_integerJet (n : ℕ) : conjSourcePoly (integerJet n) = integerJet n := by
  induction n with
  | zero => simp [integerJet]
  | succ n ih => rw [integerJet, conjSourcePoly_integerStep, ih]

theorem conjSourcePoly_integerReflection (n : ℕ) :
    conjSourcePoly (integerReflection n) = integerReflection n := by
  simp [integerReflection, map_sum, conjSourcePoly_integerJet]

theorem conjSourcePoly_integerThirdMinor : conjSourcePoly integerThirdMinor = integerThirdMinor := by
  simp [integerThirdMinor, integerSignedMoment, conjSourcePoly_integerReflection]

theorem conjSourcePoly_integerThirdSlope : conjSourcePoly integerThirdSlope = integerThirdSlope := by
  simp [integerThirdSlope, conjSourcePoly_integerLie, conjSourcePoly_integerThirdMinor, conjSourcePoly_integerJet]

theorem conjSourcePoly_shear (P : Poly) : conjSourcePoly (shear P) = shear (conjSourcePoly P) :=
  conjSourcePoly_eval₂Hom shearCoord (fun i => by cases i <;> simp [shearCoord]) P

theorem conjSourcePoly_square (P : Poly) : conjSourcePoly (square P) = square (conjSourcePoly P) :=
  conjSourcePoly_eval₂Hom squareCoord (fun i => by cases i <;> simp [squareCoord]) P

/-- The squared chart is injective on source polynomials. -/
theorem square_injective : Function.Injective square := by
  intro P Q hPQ
  apply MvPolynomial.funext
  intro v
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (v Coord.U) (by norm_num : 0 < 2)
  let v' : Coord → ℂ := fun i => match i with
    | .U => w
    | .K => v .K
    | .J => v .J
  have key : ∀ R : Poly, eval v' (square R) = eval v R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => cases i <;> simp [hp, squareCoord, v', hw]
  rw [← key P, ← key Q, hPQ]

/-- The reduced third slope has real coefficients. -/
theorem conjSourcePoly_reducedSlope : conjSourcePoly reducedSlope = reducedSlope := by
  apply square_injective
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero Coord.U)
  have h := congrArg conjSourcePoly integerSlope_shear_factor
  rw [conjSourcePoly_shear, conjSourcePoly_integerThirdSlope, map_mul, conjSourcePoly_X, conjSourcePoly_square] at h
  rw [← h, integerSlope_shear_factor]

end
end HTGeometry.ThetaRatioSquare
