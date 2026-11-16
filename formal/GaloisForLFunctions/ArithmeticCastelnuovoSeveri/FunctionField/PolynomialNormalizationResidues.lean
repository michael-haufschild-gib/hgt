import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalResidue

/-!
# Polynomial evaluation at finite normalization places

For a Dedekind algebra over a polynomial ring, polynomial functions
are integral at every finite place. Above a linear prime, reduction
equals evaluation in the constants. A polynomial nonzero at that point
is therefore a valuation unit. These statements do not depend on a
particular radical equation or on the size of the constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable {K B L : Type*} [Field K] [CommRing B] [IsDedekindDomain B] [Field L]
    [Algebra K B] [Algebra K[X] B] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra K[X] L]
    [IsScalarTower K K[X] B] [IsScalarTower K[X] B L] [IsScalarTower K K[X] L]
    (w : HeightOneSpectrum B)

/-- Polynomial functions as elements of the actual finite-place valuation ring. -/
def heightOnePolynomialHom : K[X] →+* (w.valuation L).valuationSubring :=
  RingHom.codRestrict (algebraMap K[X] L) (w.valuation L).valuationSubring.toSubring
    (fun f => by
      change w.valuation L (algebraMap K[X] L f) ≤ 1
      rw [IsScalarTower.algebraMap_apply K[X] B L, HeightOneSpectrum.valuation_of_algebraMap]
      exact w.intValuation_le_one _)

/-- Constants embedded through the polynomial map into the finite-place valuation ring. -/
def heightOnePolynomialConstantHom : K →+* (w.valuation L).valuationSubring :=
  (heightOnePolynomialHom (K := K) (L := L) w).comp C

omit [Algebra K B] [IsScalarTower K K[X] B] in
/-- Taking underlying values recovers the canonical constant-field embedding. -/
theorem heightOnePolynomialConstantHom_coe (a : K) :
    (heightOnePolynomialConstantHom (K := K) (L := L) w a : L) = algebraMap K L a :=
  (IsScalarTower.algebraMap_apply K K[X] L a).symm

omit [Algebra K B] [Algebra K L] [IsScalarTower K K[X] B] [IsScalarTower K K[X] L] in
/-- The coordinate reduces to its constant value above a linear base prime. -/
theorem heightOnePolynomialResidue_coordinate (a : K)
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    IsLocalRing.residue _ (heightOnePolynomialHom (K := K) (L := L) w X) =
      IsLocalRing.residue _ (heightOnePolynomialConstantHom (K := K) (L := L) w a) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (IsLocalRing.residue_eq_zero_iff _).mpr
  apply (w.valuation L).mem_maximalIdeal_iff.mpr
  change w.valuation L (algebraMap K[X] L X - algebraMap K[X] L (C a)) < 1
  rw [← map_sub, IsScalarTower.algebraMap_apply K[X] B L,
    HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact (Ideal.mem_of_liesOver w.asIdeal (Ideal.span {X - C a}) (X - C a)).mp
    (Ideal.subset_span (Set.mem_singleton _))

omit [Algebra K B] [Algebra K L] [IsScalarTower K K[X] B] [IsScalarTower K K[X] L] in
/-- Reduction of every polynomial above a linear prime equals evaluation followed by constant reduction. -/
theorem heightOnePolynomialResidue_eval (a : K)
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] (f : K[X]) :
    IsLocalRing.residue _ (heightOnePolynomialHom (K := K) (L := L) w f) =
      IsLocalRing.residue _ (heightOnePolynomialConstantHom (K := K) (L := L) w (f.eval a)) := by
  let W := (w.valuation L).valuationSubring
  let φ := (IsLocalRing.residue W).comp (heightOnePolynomialHom (K := K) (L := L) w)
  let ψ := ((IsLocalRing.residue W).comp
    (heightOnePolynomialConstantHom (K := K) (L := L) w)).comp (evalRingHom a)
  have h : φ = ψ := by
    apply Polynomial.ringHom_ext
    · intro x
      change IsLocalRing.residue W (heightOnePolynomialHom (K := K) (L := L) w (C x)) =
        IsLocalRing.residue W (heightOnePolynomialConstantHom (K := K) (L := L) w ((C x).eval a))
      rw [eval_C]
      rfl
    · change IsLocalRing.residue W (heightOnePolynomialHom (K := K) (L := L) w X) =
        IsLocalRing.residue W (heightOnePolynomialConstantHom (K := K) (L := L) w (X.eval a))
      rw [eval_X]
      exact heightOnePolynomialResidue_coordinate (K := K) (L := L) w a
  exact RingHom.congr_fun h f

omit [Algebra K L] [IsScalarTower K K[X] L] in
/-- A polynomial with nonzero value at the base coordinate is a unit for every valuation above it. -/
theorem heightOne_polynomial_valuation_one_of_eval_ne_zero (a : K) (f : K[X])
    (hf : f.eval a ≠ 0) [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    w.valuation L (algebraMap K[X] L f) = 1 := by
  rw [IsScalarTower.algebraMap_apply K[X] B L]
  apply (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr
  intro hm
  letI : w.asIdeal.IsPrime := w.isPrime
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [linearPrime_quotient_polynomial a w.asIdeal] at hz
  exact hf ((algebraMap K (B ⧸ w.asIdeal)).injective (hz.trans (map_zero _).symm))

/-- Residue degree one above a linear prime means every normalization residue is a constant. -/
theorem heightOne_linearPrime_constant_residue_surjective (a : K)
    [w.asIdeal.LiesOver (Ideal.span {X - C a})]
    (hf : (Ideal.span {X - C a}).inertiaDeg' w.asIdeal = 1) :
    Function.Surjective (algebraMap K (B ⧸ w.asIdeal)) := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  letI : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI := Ideal.Quotient.field (Ideal.span {X - C a})
  letI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  rw [Ideal.inertiaDeg'_algebraMap] at hf
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hf
  have hsurj := (bijective_algebraMap_of_linearEquiv e).surjective
  intro z
  obtain ⟨y, hy⟩ := hsurj z
  let e0 := Polynomial.quotientSpanXSubCAlgEquiv a
  have hbase : algebraMap K (K[X] ⧸ Ideal.span {X - C a}) (e0 y) = y := by
    apply e0.injective
    rw [e0.commutes]
    rfl
  refine ⟨e0 y, ?_⟩
  calc
    algebraMap K (B ⧸ w.asIdeal) (e0 y) =
        algebraMap (K[X] ⧸ Ideal.span {X - C a}) (B ⧸ w.asIdeal)
          (algebraMap K (K[X] ⧸ Ideal.span {X - C a}) (e0 y)) := by
      rw [IsScalarTower.algebraMap_apply K K[X] (B ⧸ w.asIdeal),
        IsScalarTower.algebraMap_apply K[X] (K[X] ⧸ Ideal.span {X - C a}) (B ⧸ w.asIdeal),
        ← IsScalarTower.algebraMap_apply K K[X] (K[X] ⧸ Ideal.span {X - C a})]
    _ = z := by rw [hbase, hy]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
