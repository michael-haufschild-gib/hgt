import Mathlib.RingTheory.Discriminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic
import GaloisForLFunctions.ArithmeticGaugeTheory.TheFunctionFieldCalibrationIsDerived

/-!
# Finite-field orientation counts

Frobenius orientation equals the quadratic character of the trace discriminant.
Residue fields of irreducible factors therefore define square-root fibres that
retain polynomial Möbius signs. The aggregate count over monic polynomials is
exact in every degree. The invariant uses factor trace discriminants, extended
by zero off the squarefree locus.
-/

noncomputable section
open Polynomial Matrix Module Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Frobenius has the full cyclic characteristic polynomial. -/
theorem finiteField_frobenius_charpoly (b : Basis ι F K) :
    (LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom F K).toLinearMap).charpoly =
      X ^ Module.finrank F K - 1 := by
  let A := LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom F K).toLinearMap
  have hm : minpoly F A = X ^ Module.finrank F K - 1 := by
    rw [LinearMap.minpoly_toMatrix, FiniteField.minpoly_frobeniusAlgHom]
  have hd := Matrix.minpoly_dvd_charpoly A
  rw [hm] at hd
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (monic_X_pow_sub_C (1 : F) Module.finrank_pos.ne')
    (Matrix.charpoly_monic A) hd (by
      rw [Matrix.charpoly_natDegree_eq_dim, ← C_1, natDegree_X_pow_sub_C,
        Module.finrank_eq_card_basis b]))

/-- The determinant of Frobenius supplies the extension-degree orientation. -/
theorem finiteField_frobenius_det (b : Basis ι F K) :
    (LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom F K).toLinearMap).det =
      (-1 : F) ^ (Module.finrank F K + 1) := by
  rw [Matrix.det_eq_sign_charpoly_coeff, finiteField_frobenius_charpoly]
  have hn : Module.finrank F K ≠ 0 := Module.finrank_pos.ne'
  simp only [coeff_sub, coeff_X_pow, if_neg (Ne.symm hn), coeff_one_zero, zero_sub,
    ← Module.finrank_eq_card_basis b, pow_succ]

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Polynomial Matrix Module Finset
variable (F K : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [Algebra F K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq F] in
/-- The discriminant square root transforms by the determinant of actual Frobenius. -/
theorem finiteField_discr_euler (hF : ringChar F ≠ 2) (b : Basis ι F K) :
    (Algebra.discr F b) ^ (Fintype.card F / 2) =
      (-1 : F) ^ (Module.finrank F K + 1) := by
  let E := AlgebraicClosure K
  let e : ι ≃ (K →ₐ[F] E) := Fintype.equivOfCardEq (by
    rw [AlgHom.card, Module.finrank_eq_card_basis b])
  let V := Algebra.embeddingsMatrixReindex F E b e
  let A := LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom F K).toLinearMap
  have hmat : V.map (FiniteField.frobeniusAlgHom F E).toRingHom =
      A.transpose.map (algebraMap F E) * V := by
    ext i j
    simp only [V, A, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, Algebra.embeddingsMatrix_apply, LinearMap.toMatrix_apply]
    change (e j (b i)) ^ Fintype.card F =
      ∑ k, algebraMap F E (b.repr ((b i) ^ Fintype.card F) k) * e j (b k)
    have he := congrArg (e j) (b.sum_repr ((b i) ^ Fintype.card F))
    simpa only [map_sum, map_smul, Algebra.smul_def, map_pow, map_mul, AlgHom.commutes] using he.symm
  have hdet : V.det ^ Fintype.card F =
      algebraMap F E ((-1 : F) ^ (Module.finrank F K + 1)) * V.det := by
    have hh := congrArg Matrix.det hmat
    change ((FiniteField.frobeniusAlgHom F E).toRingHom.mapMatrix V).det =
      ((algebraMap F E).mapMatrix A.transpose * V).det at hh
    rw [← RingHom.map_det, Matrix.det_mul, ← RingHom.map_det, Matrix.det_transpose,
      finiteField_frobenius_det] at hh
    exact hh
  have hdisc : algebraMap F E (Algebra.discr F b) = V.det ^ 2 :=
    Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two F E b e
  have hv : V.det ≠ 0 := by
    intro hz
    have he : algebraMap F E (Algebra.discr F b) = 0 := by rw [hdisc, hz, zero_pow two_ne_zero]
    exact Algebra.discr_not_zero_of_basis F b ((algebraMap F E).injective (by simpa using he))
  have hq : 2 * (Fintype.card F / 2) + 1 = Fintype.card F := by
    have ho := FiniteField.odd_card_of_char_ne_two hF
    omega
  apply (algebraMap F E).injective
  apply mul_right_cancel₀ hv
  rw [map_pow, hdisc, ← pow_mul, ← pow_succ, hq]
  exact hdet

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Polynomial Matrix Module Finset
variable (F K : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [Algebra F K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic character of the trace discriminant is the Frobenius orientation sign. -/
theorem finiteField_discr_quadraticChar (hF : ringChar F ≠ 2) (b : Basis ι F K) :
    quadraticChar F (Algebra.discr F b) = (-1 : ℤ) ^ (Module.finrank F K + 1) := by
  have he : (quadraticChar F (Algebra.discr F b) : F) =
      (((-1 : ℤ) ^ (Module.finrank F K + 1) : ℤ) : F) := by
    rw [quadraticChar_eq_pow_of_char_ne_two' hF, finiteField_discr_euler F K hF b]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hu : (-1 : ℤ) ^ (Module.finrank F K + 1) = 1 ∨
      (-1 : ℤ) ^ (Module.finrank F K + 1) = -1 := by
    apply sq_eq_one_iff.mp
    rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow]
  rcases quadraticChar_dichotomy (Algebra.discr_not_zero_of_basis F b) with hc | hc
  · rcases hu with hu | hu
    · rw [hc, hu]
    · rw [hc, hu, Int.cast_one, Int.cast_neg, Int.cast_one] at he
      exact False.elim ((Ring.neg_one_ne_one_of_char_ne_two hF) he.symm)
  · rcases hu with hu | hu
    · rw [hc, hu, Int.cast_neg, Int.cast_one] at he
      exact False.elim ((Ring.neg_one_ne_one_of_char_ne_two hF) he)
    · rw [hc, hu]

/-- The actual orientation-cover fibre of a finite field extension. -/
def finiteFieldOrientationCover (b : Basis ι F K) : Finset F :=
  univ.filter (fun y => y ^ 2 = Algebra.discr F b)

/-- The fibre count detects extension-degree parity through Frobenius. -/
theorem finiteFieldOrientationCover_card (hF : ringChar F ≠ 2) (b : Basis ι F K) :
    ((finiteFieldOrientationCover F K b).card : ℤ) =
      1 + (-1 : ℤ) ^ (Module.finrank F K + 1) := by
  have h := quadraticChar_card_sqrts hF (Algebra.discr F b)
  rw [finiteField_discr_quadraticChar F K hF b] at h
  simpa only [finiteFieldOrientationCover, Set.toFinset_setOf, add_comm] using h

#print axioms finiteField_frobenius_charpoly
#print axioms finiteField_frobenius_det
#print axioms finiteField_discr_euler
#print axioms finiteField_discr_quadraticChar
#print axioms finiteFieldOrientationCover_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Polynomial Matrix Module Finset UniqueFactorizationMonoid
open ArithmeticGaugeTheory
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Trace discriminant of the actual residue field of an irreducible polynomial. -/
def irreducibleTraceDiscriminant (P : F[X]) : F := by
  classical
  exact if h : Irreducible P then
    Algebra.discr F (AdjoinRoot.powerBasis h.ne_zero).basis else 0

/-- The residue-field orientation contributes one minus sign per irreducible factor. -/
theorem irreducibleTraceDiscriminant_character (hF : ringChar F ≠ 2)
    {P : F[X]} (hP : Irreducible P) :
    quadraticChar F (irreducibleTraceDiscriminant P) = (-1 : ℤ) ^ (P.natDegree + 1) := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite F (AdjoinRoot P) := Module.Finite.of_basis (AdjoinRoot.powerBasis hP.ne_zero).basis
  letI : Finite (AdjoinRoot P) := Module.finite_of_finite F
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  rw [irreducibleTraceDiscriminant, dif_pos hP,
    finiteField_discr_quadraticChar F (AdjoinRoot P) hF,
    (AdjoinRoot.powerBasis hP.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

/-- The normalization discriminant, with the ramified locus assigned its zero fibre. -/
def factorTraceDiscriminant (f : F[X]) : F := by
  classical
  exact if Squarefree f then ((normalizedFactors f).map irreducibleTraceDiscriminant).prod else 0

#print axioms irreducibleTraceDiscriminant_character
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Polynomial Matrix Module Finset UniqueFactorizationMonoid
open ArithmeticGaugeTheory
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem traceDiscriminant_product_character (hF : ringChar F ≠ 2)
    (s : Multiset F[X]) (hs : ∀ P ∈ s, Irreducible P) :
    quadraticChar F (s.map irreducibleTraceDiscriminant).prod =
      (-1 : ℤ) ^ ((s.map Polynomial.natDegree).sum + s.card) := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.prod_zero, map_one,
      Multiset.sum_zero, Multiset.card_zero, zero_add, pow_zero]
  | @cons P s ih =>
    have hP := hs P (Multiset.mem_cons_self P s)
    have htail : ∀ Q ∈ s, Irreducible Q := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
    simp only [Multiset.map_cons, Multiset.prod_cons, map_mul,
      irreducibleTraceDiscriminant_character hF hP, ih htail,
      Multiset.sum_cons, Multiset.card_cons]
    rw [← pow_add]
    congr 1
    omega

/-- The orientation invariant recovers polynomial Möbius signs from residue-field discriminants. -/
theorem factorTraceDiscriminant_character (hF : ringChar F ≠ 2)
    {f : F[X]} (hf : f.Monic) :
    quadraticChar F (factorTraceDiscriminant f) =
      (-1 : ℤ) ^ f.natDegree * polyMoebius f := by
  classical
  have hdeg : ((normalizedFactors f).map Polynomial.natDegree).sum = f.natDegree := by
    rw [← natDegree_multiset_prod (normalizedFactors f) (zero_notMem_normalizedFactors f)]
    have he := leadingCoeff_mul_prod_normalizedFactors f
    rw [hf.leadingCoeff, C_1, one_mul] at he
    rw [he]
  by_cases hs : Squarefree f
  · rw [factorTraceDiscriminant, if_pos hs, polyMoebius, if_pos hs,
      traceDiscriminant_product_character hF _ (fun P hP => irreducible_of_normalized_factor P hP),
      hdeg, pow_add]
  · rw [factorTraceDiscriminant, if_neg hs, quadraticChar_zero, polyMoebius, if_neg hs, mul_zero]

/-- Actual points of the factor-trace orientation cover over monic polynomials. -/
def factorOrientationCover (n : ℕ) : Finset (F[X] × F) := by
  classical
  exact ((monicOfDeg F n).product univ).filter (fun x => x.2 ^ 2 = factorTraceDiscriminant x.1)

/-- Fibre counting retains the arithmetic orientation sign. -/
theorem factorOrientationCover_card_signed (hF : ringChar F ≠ 2) (n : ℕ) :
    ((factorOrientationCover (F := F) n).card : ℤ) =
      (Fintype.card F : ℤ) ^ n + (-1 : ℤ) ^ n * moebiusDegreeSum F n := by
  classical
  have hc : ((factorOrientationCover (F := F) n).card : ℤ) =
      ∑ f ∈ monicOfDeg F n, ((univ.filter (fun y : F => y ^ 2 = factorTraceDiscriminant f)).card : ℤ) := by
    simp only [factorOrientationCover, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    exact Finset.sum_product _ _ _
  have hfibre (f : F[X]) (hf : f ∈ monicOfDeg F n) :
      ((univ.filter (fun y : F => y ^ 2 = factorTraceDiscriminant f)).card : ℤ) =
        1 + (-1 : ℤ) ^ n * polyMoebius f := by
    have hh := quadraticChar_card_sqrts hF (factorTraceDiscriminant f)
    rw [factorTraceDiscriminant_character hF (mem_monicOfDeg.mp hf).1,
      (mem_monicOfDeg.mp hf).2] at hh
    simpa only [Set.toFinset_setOf, add_comm] using hh
  rw [hc, sum_congr rfl hfibre, sum_add_distrib, sum_const, ← mul_sum,
    nsmul_eq_mul, mul_one, card_monicOfDeg, Nat.cast_pow]
  rfl

/-- The actual cover has exact mass `q^n` in every degree at least two. -/
theorem factorOrientationCover_card (hF : ringChar F ≠ 2) (n : ℕ) :
    ((factorOrientationCover (F := F) n).card : ℤ) =
      if n = 0 then 2 else if n = 1 then 2 * (Fintype.card F : ℤ) else (Fintype.card F : ℤ) ^ n := by
  rw [factorOrientationCover_card_signed hF, sum_monicOfDeg_polyMoebius]
  by_cases h0 : n = 0
  · subst n
    simp only [ite_true, pow_zero, mul_one]
    ring
  · by_cases h1 : n = 1
    · subst n
      simp only [if_neg one_ne_zero, ite_true, pow_one]
      ring
    · simp only [h0, h1, if_false, mul_zero, add_zero]

#print axioms factorTraceDiscriminant_character
#print axioms factorOrientationCover_card_signed
#print axioms factorOrientationCover_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
