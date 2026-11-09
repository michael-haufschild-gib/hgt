import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.CoefficientDiscriminantCover
import GaloisForLFunctions.HTGeometry.MonicRootDiscriminant

/-!
# Arithmetic discriminant-cover counts

The integral coefficient equation equals the Sylvester discriminant of every
monic polynomial. Its finite-field points are therefore the independently
counted arithmetic orientation cover, with colliding roots retained.
-/

noncomputable section
open Finset Polynomial
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- The integral coefficient polynomial agrees with the actual Sylvester discriminant. -/
theorem coefficientOrientationDiscriminant_eq_discr {F : Type*} [Field F]
    (n : ℕ) {f : F[X]} (hf : f.Monic) (hn : f.natDegree = n) :
    coefficientOrientationDiscriminant n f = f.discr := by
  let E := f.SplittingField
  have hs : (f.map (algebraMap F E)).Splits := Polynomial.IsSplittingField.splits E f
  obtain ⟨x, hx⟩ := HTGeometry.exists_root_tuple_of_monic_splits (hf.map _) hs
    ((hf.natDegree_map _).trans hn)
  apply (algebraMap F E).injective
  rw [← coefficientOrientationDiscriminant_map, HTGeometry.map_discr_of_monic _ hf,
    hx, coefficientOrientationDiscriminant_prod, HTGeometry.discr_rootPolynomial]

/-- The coefficient equation is the Sylvester discriminant over every integral domain. -/
theorem coefficientOrientationDiscriminant_eq_discr_of_domain
    {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {f : R[X]} (hf : f.Monic) (hn : f.natDegree = n) :
    coefficientOrientationDiscriminant n f = f.discr := by
  let K := FractionRing R
  apply (IsFractionRing.injective R K)
  rw [← coefficientOrientationDiscriminant_map, HTGeometry.map_discr_of_monic _ hf]
  exact coefficientOrientationDiscriminant_eq_discr n (hf.map _)
    ((hf.natDegree_map _).trans hn)

/-- The single integral polynomial computes the discriminant from ordinary coefficients. -/
theorem integralCoefficientDiscriminant_eq_discr
    {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {f : R[X]} (hf : f.Monic) (hn : f.natDegree = n) :
    MvPolynomial.eval₂ (Int.castRingHom R) (fun i : Fin n => f.coeff i.val)
      (integralCoefficientDiscriminant n) = f.discr := by
  rw [integralCoefficientDiscriminant_eval,
    coefficientOrientationDiscriminant_eq_discr_of_domain n hf hn]

section LocalOrientation
open MulAction Equiv HTGeometry ArithmeticGaugeTheory
attribute [local instance] Classical.propDecidable
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  (n : ℕ)
local instance : MulAction (Perm (Fin n)) (Fin n → E) :=
  permutationTupleAction E (Perm (Fin n)) (Fin n)

/-- The actual discriminant character is the signed arithmetic transporter weight, fibre by fibre. -/
theorem discriminant_quadraticChar_eq_orientationWeight
    (hd : n.factorial ∣ Module.finrank F E) (hF : ringChar F ≠ 2)
    (f : monicOfDeg F n) :
    (quadraticChar F f.val.discr : ℚ) =
      orientationOrbitWeight (tupleFrobenius F E (Perm (Fin n)) (Fin n))
        Perm.sign ((monicFrobeniusOrbitEquiv F E n hd) f).val := by
  classical
  let q := (monicFrobeniusOrbitEquiv F E n hd) f
  obtain ⟨hm, hn⟩ := mem_monicOfDeg.mp f.property
  have hdsc : algebraMap F E f.val.discr =
      vandermondeProd (monicRootTuple F E n hd f) ^ 2 := by
    rw [← coefficientOrientationDiscriminant_eq_discr n hm hn]
    exact coefficientOrientationDiscriminant_rootTuple F E n hd f
  have hq : (Quotient.mk'' (monicRootTuple F E n hd f) :
      Quotient (orbitRel (Perm (Fin n)) (Fin n → E))) = q.val := rfl
  have hv := vandermonde_square_eq_of_orbit (E := E) (n := n)
    (monicRootTuple F E n hd f) q.val.out
    (hq.trans (Quotient.out_eq q.val).symm)
  have hfibre : univ.filter (fun y : F => y ^ 2 = f.val.discr) =
      baseOrientationFibre F E (vandermondeProd q.val.out) := by
    ext y
    simp only [baseOrientationFibre, mem_filter, mem_univ, true_and]
    rw [← hv, ← hdsc, ← map_pow]
    exact (algebraMap F E).injective.eq_iff.symm
  have hcard : ((univ.filter (fun y : F => y ^ 2 = f.val.discr)).card : ℚ) =
      1 + (quadraticChar F f.val.discr : ℚ) := by
    have h : ((univ.filter (fun y : F => y ^ 2 = f.val.discr)).card : ℤ) =
        1 + quadraticChar F f.val.discr := by
      simpa only [Set.toFinset_setOf, add_comm] using quadraticChar_card_sqrts hF f.val.discr
    exact_mod_cast h
  have hw := baseOrientationFibre_card_eq_weight F E n hF q
  rw [← hfibre, hcard] at hw
  exact add_left_cancel hw

end LocalOrientation

open ArithmeticGaugeTheory
variable (F : Type*) [Field F] [Fintype F] (n : ℕ)
attribute [local instance] Classical.propDecidable

/-- Actual points of the discriminant equation over monic coefficient polynomials. -/
def arithmeticDiscriminantCover : Finset (monicOfDeg F n × F) :=
  univ.filter (fun fy => fy.2 ^ 2 = fy.1.val.discr)

/-- Equality of the Sylvester-discriminant cover and the integral coefficient cover. -/
theorem arithmeticDiscriminantCover_eq_coefficientOrientationCover :
    arithmeticDiscriminantCover F n = coefficientOrientationCover F n := by
  ext fy
  obtain ⟨hm, hn⟩ := mem_monicOfDeg.mp fy.1.property
  simp only [arithmeticDiscriminantCover, coefficientOrientationCover,
    mem_filter, mem_univ, true_and, coefficientOrientationDiscriminant_eq_discr n hm hn]

/-- The actual discriminant cover has q^n points in every degree at least two. -/
theorem arithmeticDiscriminantCover_card [Nontrivial (Fin n)] (hF : ringChar F ≠ 2) :
    (arithmeticDiscriminantCover F n).card = Fintype.card F ^ n := by
  rw [arithmeticDiscriminantCover_eq_coefficientOrientationCover]
  exact coefficientOrientationCover_card F n hF

/-- Each discriminant fibre contributes one plus its arithmetic quadratic character. -/
theorem arithmeticDiscriminantCover_card_signed (hF : ringChar F ≠ 2) :
    ((arithmeticDiscriminantCover F n).card : ℤ) =
      (Fintype.card F : ℤ) ^ n + ∑ f : monicOfDeg F n, quadraticChar F f.val.discr := by
  have hf (f : monicOfDeg F n) :
      ((univ.filter (fun y : F => y ^ 2 = f.val.discr)).card : ℤ) =
        1 + quadraticChar F f.val.discr := by
    simpa only [Set.toFinset_setOf, add_comm] using quadraticChar_card_sqrts hF f.val.discr
  calc
    ((arithmeticDiscriminantCover F n).card : ℤ) =
        ∑ f : monicOfDeg F n, ((univ.filter (fun y : F => y ^ 2 = f.val.discr)).card : ℤ) := by
      simp only [arithmeticDiscriminantCover, card_eq_sum_ones, Nat.cast_sum, sum_filter]
      rw [← Finset.univ_product_univ]
      exact Finset.sum_product _ _ _
    _ = ∑ f : monicOfDeg F n, (1 + quadraticChar F f.val.discr) :=
      sum_congr rfl (fun f _ => hf f)
    _ = (Fintype.card F : ℤ) ^ n + ∑ f : monicOfDeg F n, quadraticChar F f.val.discr := by
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
        Fintype.card_coe, card_monicOfDeg, Nat.cast_pow]

/-- The signed discriminant fibres cancel independently in every degree at least two. -/
theorem sum_discriminant_quadraticChar_eq_zero [Nontrivial (Fin n)] (hF : ringChar F ≠ 2) :
    (∑ f : monicOfDeg F n, quadraticChar F f.val.discr) = 0 := by
  have h := arithmeticDiscriminantCover_card_signed F n hF
  rw [arithmeticDiscriminantCover_card F n hF, Nat.cast_pow] at h
  omega

/-- In degrees zero and one every monic polynomial has two orientation lifts. -/
theorem arithmeticDiscriminantCover_card_low (hF : ringChar F ≠ 2) (hn : n ≤ 1) :
    (arithmeticDiscriminantCover F n).card = 2 * Fintype.card F ^ n := by
  have hd (f : monicOfDeg F n) : f.val.discr = 1 := by
    obtain ⟨hm, hdeg⟩ := mem_monicOfDeg.mp f.property
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have hf := eq_one_of_monic_natDegree_zero hm hdeg
      rw [hf]
      exact Polynomial.discr_C 1
    · have hn1 : n = 1 := by omega
      apply Polynomial.discr_of_degree_eq_one
      rw [degree_eq_natDegree hm.ne_zero, hdeg, hn1, Nat.cast_one]
  have he : arithmeticDiscriminantCover F n =
      (univ : Finset (monicOfDeg F n)) ×ˢ (univ.filter (fun y : F => y ^ 2 = 1)) := by
    ext fy
    simp only [arithmeticDiscriminantCover, mem_filter, mem_univ, true_and,
      mem_product, hd]
  have hy : (univ.filter (fun y : F => y ^ 2 = 1)).card = 2 := by
    have h := quadraticChar_card_sqrts hF (1 : F)
    have hz : ((univ.filter (fun y : F => y ^ 2 = 1)).card : ℤ) = 2 := by
      simpa only [Set.toFinset_setOf, map_one, one_add_one_eq_two] using h
    exact_mod_cast hz
  rw [he, card_product, card_univ, Fintype.card_coe, card_monicOfDeg, hy, Nat.mul_comm]

#print axioms coefficientOrientationDiscriminant_eq_discr
#print axioms coefficientOrientationDiscriminant_eq_discr_of_domain
#print axioms integralCoefficientDiscriminant_eq_discr
#print axioms discriminant_quadraticChar_eq_orientationWeight
#print axioms arithmeticDiscriminantCover_eq_coefficientOrientationCover
#print axioms arithmeticDiscriminantCover_card
#print axioms arithmeticDiscriminantCover_card_signed
#print axioms sum_discriminant_quadraticChar_eq_zero
#print axioms arithmeticDiscriminantCover_card_low
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
