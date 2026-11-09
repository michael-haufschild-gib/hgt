import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldRootCover
import GaloisForLFunctions.HTGeometry.PaperIntegralDiscriminant
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The integral equation of the orientation cover

The integral symmetric discriminant is evaluated at the signed coefficients
of a monic polynomial. Vieta identifies this equation with the squared
Vandermonde of its roots, retaining collisions and arbitrary characteristic.
-/

noncomputable section
open Finset Polynomial
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

variable {R : Type*} [CommRing R] (n : ℕ)

/-- Elementary-symmetric coordinates read directly from polynomial coefficients. -/
def monicSymmetricCoordinates (f : R[X]) (i : Fin n) : R :=
  (-1) ^ (i.val + 1) * f.coeff (n - (i.val + 1))

/-- One integral polynomial in the elementary-symmetric coefficient coordinates. -/
def integralOrientationDiscriminant : MvPolynomial (Fin n) ℤ :=
  HTGeometry.paperIntegralDiscriminantPolynomial ℤ n

/-- Evaluation of the integral discriminant at the coefficients of a monic polynomial. -/
def coefficientOrientationDiscriminant (f : R[X]) : R :=
  MvPolynomial.eval₂ (Int.castRingHom R) (monicSymmetricCoordinates n f)
    (integralOrientationDiscriminant n)

/-- The same integral equation in the ordinary coefficients, in ascending degree order. -/
def integralCoefficientDiscriminant : MvPolynomial (Fin n) ℤ :=
  MvPolynomial.aeval (fun i : Fin n =>
    (-1) ^ (i.val + 1) * MvPolynomial.X i.rev) (integralOrientationDiscriminant n)

/-- Ordinary coefficient evaluation recovers the arithmetic discriminant coordinate. -/
theorem integralCoefficientDiscriminant_eval (f : R[X]) :
    MvPolynomial.eval₂ (Int.castRingHom R) (fun i : Fin n => f.coeff i.val)
      (integralCoefficientDiscriminant n) = coefficientOrientationDiscriminant n f := by
  let ev : MvPolynomial (Fin n) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin n => f.coeff i.val)
  let sub : MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ :=
    MvPolynomial.aeval (fun i : Fin n => (-1) ^ (i.val + 1) * MvPolynomial.X i.rev)
  have he : ev.comp sub.toRingHom =
      MvPolynomial.eval₂Hom (Int.castRingHom R) (monicSymmetricCoordinates n f) := by
    ext i
    · simp [ev, sub]
    · simp [ev, sub, monicSymmetricCoordinates, Fin.rev]
  change (ev.comp sub.toRingHom) (integralOrientationDiscriminant n) = _
  rw [he]
  rfl

/-- Integral specialization agrees with the symmetric polynomial over the target ring. -/
theorem coefficientOrientationDiscriminant_eq_native (f : R[X]) :
    coefficientOrientationDiscriminant n f =
      MvPolynomial.aeval (monicSymmetricCoordinates n f)
        (HTGeometry.paperIntegralDiscriminantPolynomial R n) := by
  rw [coefficientOrientationDiscriminant, integralOrientationDiscriminant,
    MvPolynomial.eval₂_eq_eval_map,
    HTGeometry.paperIntegralDiscriminantPolynomial_baseChange]
  rfl

/-- Vieta recovers every elementary-symmetric coordinate, with repeated roots allowed. -/
theorem monicSymmetricCoordinates_prod (x : Fin n → R) (i : Fin n) :
    monicSymmetricCoordinates n (∏ j, (X - C (x j))) i =
      MvPolynomial.aeval x (MvPolynomial.esymm (Fin n) R (i.val + 1)) := by
  classical
  let s := (Finset.univ : Finset (Fin n)).val.map x
  have hs : s.card = n := by
    rw [Multiset.card_map]
    change (univ : Finset (Fin n)).card = n
    simp only [card_univ, Fintype.card_fin]
  have hp : (s.map (fun r => X - C r)).prod = ∏ j, (X - C (x j)) := by
    rw [Multiset.map_map]
    rfl
  have hi : i.val + 1 ≤ n := i.isLt
  have hc := s.prod_X_sub_C_coeff (k := n - (i.val + 1)) (by omega)
  rw [hp, hs, Nat.sub_sub_self hi] at hc
  rw [monicSymmetricCoordinates, hc,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, ← mul_assoc, ← mul_pow]
  simp only [neg_one_mul, neg_neg, one_pow, one_mul]
  rfl

/-- The coefficient equation is precisely the root-orientation square over every ring. -/
theorem coefficientOrientationDiscriminant_prod (x : Fin n → R) :
    coefficientOrientationDiscriminant n (∏ j, (X - C (x j))) =
      HTGeometry.vandermondeProd x ^ 2 := by
  rw [coefficientOrientationDiscriminant_eq_native]
  have hcomp : (MvPolynomial.aeval x).comp
      (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) R (i.val + 1))) =
      MvPolynomial.aeval (monicSymmetricCoordinates n (∏ j, (X - C (x j)))) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, monicSymmetricCoordinates_prod]
  have h := congrArg (MvPolynomial.aeval x)
    (HTGeometry.paperIntegralDiscriminantPolynomial_spec R n)
  rw [← AlgHom.comp_apply, hcomp] at h
  rw [h, map_mul]
  have hv : MvPolynomial.aeval x (HTGeometry.paperUniversalVandermonde R n) =
      HTGeometry.vandermondeProd x := by
    simp only [HTGeometry.paperUniversalVandermonde, HTGeometry.vandermondeProd,
      map_prod, map_sub, MvPolynomial.aeval_X]
  rw [hv, pow_two]

/-- The equation commutes with every ring homomorphism, including reduction modulo a prime. -/
theorem coefficientOrientationDiscriminant_map {S : Type*} [CommRing S]
    (φ : R →+* S) (f : R[X]) :
    coefficientOrientationDiscriminant n (f.map φ) =
      φ (coefficientOrientationDiscriminant n f) := by
  have hc : monicSymmetricCoordinates n (f.map φ) =
      φ ∘ monicSymmetricCoordinates n f := by
    funext i
    simp only [monicSymmetricCoordinates, Polynomial.coeff_map,
      Function.comp_apply, map_mul, map_pow, map_neg, map_one]
  have hφ : φ.comp (Int.castRingHom R) = Int.castRingHom S := by
    ext z
    simp only [RingHom.comp_apply, Int.coe_castRingHom, map_intCast]
  change MvPolynomial.eval₂Hom (Int.castRingHom S) _ _ =
    φ (MvPolynomial.eval₂Hom (Int.castRingHom R) _ _)
  rw [MvPolynomial.map_eval₂Hom, hφ, hc]
  rfl

#print axioms integralCoefficientDiscriminant_eval
#print axioms coefficientOrientationDiscriminant_prod
#print axioms coefficientOrientationDiscriminant_map

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts



namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticGaugeTheory
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  (n : ℕ)
attribute [local instance] Classical.propDecidable

/-- The integral coefficient equation agrees with the chosen arithmetic root tuple. -/
theorem coefficientOrientationDiscriminant_rootTuple
    (hd : n.factorial ∣ Module.finrank F E) (f : monicOfDeg F n) :
    algebraMap F E (coefficientOrientationDiscriminant n f.val) =
      HTGeometry.vandermondeProd (monicRootTuple F E n hd f) ^ 2 := by
  rw [← coefficientOrientationDiscriminant_map, monicRootTuple_spec,
    tupleRootPolynomial, coefficientOrientationDiscriminant_prod]

/-- The orientation cover given by one integral polynomial in coefficient coordinates. -/
def coefficientOrientationCover : Finset (monicOfDeg F n × F) :=
  univ.filter (fun fy => fy.2 ^ 2 = coefficientOrientationDiscriminant n fy.1.val)

/-- Equality of the actual finite sets, not merely equality of their cardinalities. -/
theorem rootOrientationCover_eq_coefficientOrientationCover
    (hd : n.factorial ∣ Module.finrank F E) :
    rootOrientationCover F E n hd = coefficientOrientationCover F n := by
  ext fy
  simp only [rootOrientationCover, coefficientOrientationCover, mem_filter,
    mem_univ, true_and, ← coefficientOrientationDiscriminant_rootTuple F E n hd,
    ← map_pow]
  exact (algebraMap F E).injective.eq_iff

#print axioms coefficientOrientationDiscriminant_rootTuple
#print axioms rootOrientationCover_eq_coefficientOrientationCover
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField ArithmeticGaugeTheory Equiv
variable (F : Type*) [Field F] [Fintype F] (n : ℕ)
attribute [local instance] Classical.propDecidable

/-- Independent normal-basis counts give the number of coefficient-cover points. -/
theorem coefficientOrientationCover_card [Nontrivial (Fin n)] (hF : ringChar F ≠ 2) :
    (coefficientOrientationCover F n).card = Fintype.card F ^ n := by
  letI : Fact (ringChar F).Prime := ⟨CharP.prime_ringChar F⟩
  let E := Extension F (ringChar F) (Fintype.card (Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  have hd : n.factorial ∣ Module.finrank F E := by
    simp only [E, finrank_extension, Fintype.card_perm, Fintype.card_fin, dvd_refl]
  rw [← rootOrientationCover_eq_coefficientOrientationCover F E n hd]
  exact rootOrientationCover_card F E n hF hd

#print axioms coefficientOrientationCover_card

/-- The monic polynomial with the prescribed coefficients below its leading term. -/
def monicPolynomialOfCoefficients (c : Fin n → F) : monicOfDeg F n :=
  ⟨X ^ n + ((degreeLTEquiv F n).symm c : F[X]), mem_image.mpr ⟨c, mem_univ _, rfl⟩⟩

/-- Actual coefficient vectors parametrize the full monic coefficient space. -/
def monicCoefficientEquiv : (Fin n → F) ≃ monicOfDeg F n :=
  Equiv.ofBijective (monicPolynomialOfCoefficients F n) ⟨by
    intro c d h
    apply (degreeLTEquiv F n).symm.injective
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val h), by
    intro f
    obtain ⟨c, _, hc⟩ := mem_image.mp f.property
    exact ⟨c, Subtype.ext hc⟩⟩

/-- The parametrization retains the literal polynomial coefficients. -/
theorem monicCoefficientEquiv_coeff (c : Fin n → F) (i : Fin n) :
    (monicCoefficientEquiv F n c).val.coeff i.val = c i := by
  change (X ^ n + ((degreeLTEquiv F n).symm c : F[X])).coeff i.val = c i
  rw [coeff_add]
  have hx : (X ^ n : F[X]).coeff i.val = 0 := by
    simp only [coeff_X_pow, if_neg (ne_of_lt i.isLt)]
  rw [hx, zero_add]
  exact congrFun ((degreeLTEquiv F n).apply_symm_apply c) i

/-- The integral affine equation, with ordinary coefficient variables and one orientation variable. -/
def integralCoefficientCover : Finset ((Fin n → F) × F) :=
  univ.filter (fun cy => cy.2 ^ 2 =
    MvPolynomial.eval₂ (Int.castRingHom F) cy.1 (integralCoefficientDiscriminant n))

/-- Coefficient parametrization identifies the two defining equations point by point. -/
theorem coefficientCover_mem_iff (c : Fin n → F) (y : F) :
    (monicCoefficientEquiv F n c, y) ∈ coefficientOrientationCover F n ↔
      (c, y) ∈ integralCoefficientCover F n := by
  simp only [coefficientOrientationCover, integralCoefficientCover, mem_filter,
    mem_univ, true_and]
  rw [← integralCoefficientDiscriminant_eval]
  have hc : (fun i : Fin n => (monicCoefficientEquiv F n c).val.coeff i.val) = c :=
    funext (monicCoefficientEquiv_coeff F n c)
  rw [hc]

/-- The integral affine equation and the monic-polynomial cover have the same actual points. -/
def integralCoefficientCoverEquiv :
    ↥(integralCoefficientCover F n) ≃ ↥(coefficientOrientationCover F n) where
  toFun z := ⟨(monicCoefficientEquiv F n z.val.1, z.val.2),
    (coefficientCover_mem_iff F n z.val.1 z.val.2).mpr z.property⟩
  invFun z := ⟨((monicCoefficientEquiv F n).symm z.val.1, z.val.2),
    (coefficientCover_mem_iff F n _ z.val.2).mp (by
      simpa only [Equiv.apply_symm_apply] using z.property)⟩
  left_inv z := Subtype.ext (Prod.ext (Equiv.symm_apply_apply _ _) rfl)
  right_inv z := Subtype.ext (Prod.ext (Equiv.apply_symm_apply _ _) rfl)

/-- Independent arithmetic counting applies to the single integral coefficient equation. -/
theorem integralCoefficientCover_card [Nontrivial (Fin n)] (hF : ringChar F ≠ 2) :
    (integralCoefficientCover F n).card = Fintype.card F ^ n := by
  have h := Fintype.card_congr (integralCoefficientCoverEquiv F n)
  rw [Fintype.card_coe, Fintype.card_coe] at h
  rw [h, coefficientOrientationCover_card F n hF]

#print axioms monicCoefficientEquiv_coeff
#print axioms integralCoefficientCoverEquiv
#print axioms integralCoefficientCover_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
