import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicRamification
import GaloisForLFunctions.HTGeometry.NumberFieldIntegralBasisDiscriminantDivisibility
import Mathlib

/-!
# Discriminant and two-adic unramifiedness of the Q8 maximal abelian field

For the literal maximal abelian field `ℚ(√5, √41)`, this module constructs
the integral rational basis
`{1,(1+√5)/2} ⊗ {1,(1+√41)/2}`. Its trace matrix is the Kronecker product
`[[2,1],[1,3]] ⊗ [[2,1],[1,21]]`, hence its discriminant is `42025`.
The absolute field discriminant therefore divides an odd integer, proving
that the maximal abelian subextension is unramified at two even though the
top quaternion field is ramified there.
-/

namespace RHTower

open Polynomial
open scoped Matrix Kronecker NumberField

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

section BasisConstruction

noncomputable local instance fdK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis

noncomputable local instance fdQK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_firstQuadratic_irreducible.ne_zero).basis

noncomputable local instance fdQK2 : FiniteDimensional ℚ K2 :=
  FiniteDimensional.trans ℚ K1 K2

def q8BiquadU : K1 :=
  (1 + deningerQ8RootNumberNegOneFirstQuadraticRoot) / 2

def q8BiquadV : K2 :=
  (1 + deningerQ8RootNumberNegOneSecondQuadraticRoot) / 2

theorem q8BiquadU_sq : q8BiquadU ^ 2 = q8BiquadU + 1 := by
  have hx := deningerQ8RootNumberNegOneFirstQuadraticRoot_sq
  unfold q8BiquadU
  field_simp
  linear_combination hx

theorem q8BiquadV_sq : q8BiquadV ^ 2 = q8BiquadV + 10 := by
  have hy := deningerQ8RootNumberNegOneSecondQuadraticRoot_sq
  have h2 : (2 : K2) ≠ 0 := by
    simpa using (algebraMap ℚ K2).injective.ne (by norm_num : (2 : ℚ) ≠ 0)
  unfold q8BiquadV
  field_simp [h2]
  linear_combination hy

def q8BiquadUBasisFamily : Fin 2 → K1
  | 0 => 1
  | 1 => q8BiquadU

theorem q8BiquadUBasisFamily_linearIndependent :
    LinearIndependent ℚ q8BiquadUBasisFamily := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : g 0 + g 1 * q8BiquadU = 0 := by
    simpa [q8BiquadUBasisFamily, Fin.sum_univ_two, Algebra.smul_def] using hg
  have hcoord :
      ((g 0 + g 1 / 2 : ℚ) : K1) +
        (g 1 / 2 : ℚ) * deningerQ8RootNumberNegOneFirstQuadraticRoot = 0 := by
    rw [← hsum]
    unfold q8BiquadU
    push_cast
    ring
  obtain ⟨h0, h1⟩ := deningerQ8RootNumberNegOneFirstQuadratic_coordinates_eq_zero hcoord
  have hg1 : g 1 = 0 := by linarith
  have hg0 : g 0 = 0 := by linarith
  fin_cases i
  · exact hg0
  · exact hg1

theorem q8BiquadUBasisFamily_span :
    ⊤ ≤ Submodule.span ℚ (Set.range q8BiquadUBasisFamily) := by
  rw [top_le_iff]
  apply top_unique
  intro w _
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨a, b, rfl⟩ := deningerQ8RootNumberNegOneFirstQuadratic_normal_form w
  refine ⟨![a - b, 2 * b], ?_⟩
  simp [q8BiquadUBasisFamily, Fin.sum_univ_two, Algebra.smul_def]
  unfold q8BiquadU
  have h2 : (2 : K1) ≠ 0 := by
    simpa using (algebraMap ℚ K1).injective.ne (by norm_num : (2 : ℚ) ≠ 0)
  field_simp [h2]
  ring

def q8BiquadUBasis : Module.Basis (Fin 2) ℚ K1 :=
  Module.Basis.mk q8BiquadUBasisFamily_linearIndependent q8BiquadUBasisFamily_span

@[simp] theorem q8BiquadUBasis_apply (i : Fin 2) :
    q8BiquadUBasis i = q8BiquadUBasisFamily i := by
  exact Module.Basis.mk_apply _ _ _

def q8BiquadVBasisFamily : Fin 2 → K2
  | 0 => 1
  | 1 => q8BiquadV

theorem q8BiquadVBasisFamily_linearIndependent :
    LinearIndependent K1 q8BiquadVBasisFamily := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : (g 0 : K2) + (g 1 : K2) * q8BiquadV = 0 := by
    simpa [q8BiquadVBasisFamily, Fin.sum_univ_two, Algebra.smul_def] using hg
  have hg1 : g 1 = 0 := by
    by_contra hg1
    let w : K1 := -((2 * g 0 + g 1) / g 1)
    have hroot : (w : K2) = deningerQ8RootNumberNegOneSecondQuadraticRoot := by
      have hb : (g 1 : K2) ≠ 0 := by
        simpa using (algebraMap K1 K2).injective.ne hg1
      unfold w
      change (algebraMap K1 K2) (-((2 * g 0 + g 1) / g 1)) = _
      rw [map_neg]
      rw [map_div₀ (algebraMap K1 K2) (2 * g 0 + g 1) (g 1)]
      rw [map_add, map_mul, map_ofNat]
      norm_num
      change -(((2 : K2) * (g 0 : K2) + (g 1 : K2)) / (g 1 : K2)) = _
      rw [neg_eq_iff_eq_neg, div_eq_iff hb]
      unfold q8BiquadV at hsum
      have h2 : (2 : K2) ≠ 0 := by
        simpa using (algebraMap ℚ K2).injective.ne (by norm_num : (2 : ℚ) ≠ 0)
      field_simp [h2] at hsum
      linear_combination hsum
    apply deningerQ8RootNumberNegOne_fortyOne_not_square_in_firstQuadratic w
    apply (algebraMap K1 K2).injective
    rw [map_pow]
    change (w : K2) ^ 2 = ((41 : K1) : K2)
    rw [hroot, deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
    exact (map_natCast (algebraMap K1 K2) 41).symm
  have hg0 : g 0 = 0 := by
    rw [hg1] at hsum
    simpa using hsum
  fin_cases i
  · exact hg0
  · exact hg1

theorem q8BiquadVBasisFamily_span :
    ⊤ ≤ Submodule.span K1 (Set.range q8BiquadVBasisFamily) := by
  rw [top_le_iff]
  apply top_unique
  intro w _
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨a, b, rfl⟩ := deningerQ8RootNumberNegOneSecondQuadratic_normal_form w
  refine ⟨![a - b, 2 * b], ?_⟩
  simp [q8BiquadVBasisFamily, Fin.sum_univ_two, Algebra.smul_def]
  unfold q8BiquadV
  have h2 : (2 : K2) ≠ 0 := by
    simpa using (algebraMap ℚ K2).injective.ne (by norm_num : (2 : ℚ) ≠ 0)
  field_simp [h2]
  rw [map_ofNat]
  ring

def q8BiquadVBasis : Module.Basis (Fin 2) K1 K2 :=
  Module.Basis.mk q8BiquadVBasisFamily_linearIndependent q8BiquadVBasisFamily_span

@[simp] theorem q8BiquadVBasis_apply (i : Fin 2) :
    q8BiquadVBasis i = q8BiquadVBasisFamily i := by
  exact Module.Basis.mk_apply _ _ _

def q8BiquadIntegralBasis : Module.Basis (Fin 2 × Fin 2) ℚ K2 :=
  q8BiquadUBasis.smulTower q8BiquadVBasis

end BasisConstruction

theorem q8Biquad_trace_firstRoot :
    Algebra.trace ℚ K1 deningerQ8RootNumberNegOneFirstQuadraticRoot = 0 := by
  let pb := AdjoinRoot.powerBasis
    deningerQ8RootNumberNegOne_firstQuadratic_irreducible.ne_zero
  calc
    Algebra.trace ℚ K1 deningerQ8RootNumberNegOneFirstQuadraticRoot =
        -(minpoly ℚ pb.gen).nextCoeff := by
      exact pb.trace_gen_eq_nextCoeff_minpoly
    _ = 0 := by
      have hp : minpoly ℚ pb.gen = deningerQ8RootNumberNegOneFirstQuadraticPolynomial := by
        exact AdjoinRoot.minpoly_powerBasis_gen_of_monic
          (monic_X_pow_sub_C _ (by norm_num))
      rw [hp]
      norm_num [deningerQ8RootNumberNegOneFirstQuadraticPolynomial,
        Polynomial.nextCoeff]

theorem q8Biquad_trace_secondRoot :
    Algebra.trace K1 K2 deningerQ8RootNumberNegOneSecondQuadraticRoot = 0 := by
  let pb := AdjoinRoot.powerBasis
    deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero
  calc
    Algebra.trace K1 K2 deningerQ8RootNumberNegOneSecondQuadraticRoot =
        -(minpoly K1 pb.gen).nextCoeff := by
      exact pb.trace_gen_eq_nextCoeff_minpoly
    _ = 0 := by
      rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic]
      · norm_num [deningerQ8RootNumberNegOneSecondQuadraticPolynomial,
          Polynomial.nextCoeff]
      · exact monic_X_pow_sub_C _ (by norm_num)

theorem q8Biquad_trace_one_first : Algebra.trace ℚ K1 1 = 2 := by
  change Algebra.trace ℚ K1 (algebraMap ℚ K1 1) = 2
  rw [Algebra.trace_algebraMap,
    deningerQ8RootNumberNegOneFirstQuadraticField_finrank]
  norm_num

theorem q8Biquad_trace_one_second : Algebra.trace K1 K2 1 = 2 := by
  change Algebra.trace K1 K2 (algebraMap K1 K2 1) = 2
  rw [Algebra.trace_algebraMap,
    deningerQ8RootNumberNegOneSecondQuadraticField_finrank]
  norm_num

theorem q8Biquad_trace_U : Algebra.trace ℚ K1 q8BiquadU = 1 := by
  have hu : q8BiquadU =
      (1 / 2 : ℚ) • (1 + deningerQ8RootNumberNegOneFirstQuadraticRoot) := by
    unfold q8BiquadU
    rw [Algebra.smul_def]
    rw [map_div₀, map_one, map_ofNat]
    have h2 : (2 : K1) ≠ 0 := by
      simpa using (algebraMap ℚ K1).injective.ne (by norm_num : (2 : ℚ) ≠ 0)
    field_simp [h2]
  rw [hu, map_smul, map_add, q8Biquad_trace_firstRoot, add_zero,
    q8Biquad_trace_one_first]
  norm_num

theorem q8Biquad_trace_V : Algebra.trace K1 K2 q8BiquadV = 1 := by
  have hv : q8BiquadV =
      (1 / 2 : K1) • (1 + deningerQ8RootNumberNegOneSecondQuadraticRoot) := by
    unfold q8BiquadV
    rw [Algebra.smul_def]
    rw [map_div₀, map_one, map_ofNat]
    have h2 : (2 : K2) ≠ 0 := by
      simpa using (algebraMap ℚ K2).injective.ne (by norm_num : (2 : ℚ) ≠ 0)
    field_simp [h2]
  rw [hv, map_smul, map_add, q8Biquad_trace_secondRoot, add_zero,
    q8Biquad_trace_one_second]
  norm_num

theorem q8Biquad_trace_U_sq : Algebra.trace ℚ K1 (q8BiquadU ^ 2) = 3 := by
  rw [q8BiquadU_sq, map_add, q8Biquad_trace_U, q8Biquad_trace_one_first]
  norm_num

theorem q8Biquad_trace_V_sq : Algebra.trace K1 K2 (q8BiquadV ^ 2) = 21 := by
  rw [q8BiquadV_sq, map_add, q8Biquad_trace_V]
  have hten : Algebra.trace K1 K2 (10 : K2) = 20 := by
    change Algebra.trace K1 K2 (algebraMap K1 K2 10) = 20
    rw [Algebra.trace_algebraMap,
      deningerQ8RootNumberNegOneSecondQuadraticField_finrank]
    norm_num
  rw [hten]
  norm_num

def q8BiquadUTraceMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2, 1; 1, 3]

def q8BiquadVTraceMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2, 1; 1, 21]

theorem q8Biquad_trace_U_product (i k : Fin 2) :
    Algebra.trace ℚ K1 (q8BiquadUBasisFamily i * q8BiquadUBasisFamily k) =
      q8BiquadUTraceMatrix i k := by
  fin_cases i <;> fin_cases k <;>
    simp [q8BiquadUBasisFamily, q8BiquadUTraceMatrix,
      q8Biquad_trace_one_first, q8Biquad_trace_U, ← pow_two,
      q8Biquad_trace_U_sq]

theorem q8Biquad_trace_V_product (j l : Fin 2) :
    Algebra.trace K1 K2 (q8BiquadVBasisFamily j * q8BiquadVBasisFamily l) =
      (q8BiquadVTraceMatrix j l : K1) := by
  fin_cases j <;> fin_cases l <;>
    simp [q8BiquadVBasisFamily, q8BiquadVTraceMatrix,
      q8Biquad_trace_one_second, q8Biquad_trace_V, ← pow_two,
      q8Biquad_trace_V_sq]

theorem q8Biquad_trace_tower_smul (x : K1) (z : K2) :
    Algebra.trace ℚ K2 ((algebraMap K1 K2 x) * z) =
      Algebra.trace ℚ K1 (x * Algebra.trace K1 K2 z) := by
  rw [← Algebra.trace_trace_of_basis q8BiquadUBasis q8BiquadVBasis]
  congr 1
  rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
  simp

theorem q8Biquad_trace_mul_rat (x : K1) (r : ℚ) :
    Algebra.trace ℚ K1 (x * (r : K1)) =
      r * Algebra.trace ℚ K1 x := by
  have hr : (r : K1) = algebraMap ℚ K1 r := by
    exact DFunLike.congr_fun
      (Subsingleton.elim (Rat.castHom K1) (algebraMap ℚ K1)) r
  calc
    Algebra.trace ℚ K1 (x * (r : K1)) =
        Algebra.trace ℚ K1 ((r : K1) * x) := by rw [mul_comm]
    _ = Algebra.trace ℚ K1 ((algebraMap ℚ K1 r) * x) := by rw [hr]
    _ = Algebra.trace ℚ K1 (r • x) := by
      congr 1
      exact (Algebra.smul_def r x).symm
    _ = r • Algebra.trace ℚ K1 x := by rw [map_smul]
    _ = r * Algebra.trace ℚ K1 x := by rw [smul_eq_mul]

theorem q8Biquad_trace_integralBasis_mul (i j k l : Fin 2) :
    Algebra.trace ℚ K2
        (q8BiquadIntegralBasis (i, j) * q8BiquadIntegralBasis (k, l)) =
      q8BiquadUTraceMatrix i k * q8BiquadVTraceMatrix j l := by
  rw [q8BiquadIntegralBasis, Module.Basis.smulTower_apply,
    Module.Basis.smulTower_apply, q8BiquadUBasis_apply,
    q8BiquadUBasis_apply, q8BiquadVBasis_apply, q8BiquadVBasis_apply]
  simp only [Algebra.smul_def]
  rw [show
      ((algebraMap K1 K2) (q8BiquadUBasisFamily i) * q8BiquadVBasisFamily j) *
          ((algebraMap K1 K2) (q8BiquadUBasisFamily k) * q8BiquadVBasisFamily l) =
        (algebraMap K1 K2)
            (q8BiquadUBasisFamily i * q8BiquadUBasisFamily k) *
          (q8BiquadVBasisFamily j * q8BiquadVBasisFamily l) by
      rw [map_mul]
      ring]
  rw [q8Biquad_trace_tower_smul, q8Biquad_trace_V_product,
    q8Biquad_trace_mul_rat, q8Biquad_trace_U_product]
  ring

theorem q8Biquad_traceMatrix_eq_kronecker :
    Algebra.traceMatrix ℚ q8BiquadIntegralBasis =
      q8BiquadUTraceMatrix ⊗ₖ q8BiquadVTraceMatrix := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    q8Biquad_trace_integralBasis_mul]
  rfl

theorem q8BiquadIntegralBasis_discr :
    Algebra.discr ℚ q8BiquadIntegralBasis = 42025 := by
  rw [Algebra.discr_def, q8Biquad_traceMatrix_eq_kronecker,
    Matrix.det_kronecker]
  norm_num [q8BiquadUTraceMatrix, q8BiquadVTraceMatrix,
    Matrix.det_fin_two]

theorem q8BiquadU_isIntegral : IsIntegral ℤ q8BiquadU := by
  let p : ℤ[X] := X ^ 2 - X - 1
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    monicity <;> norm_num
  · have h : (q8BiquadU ^ 2 - q8BiquadU - 1 : K1) = 0 := by
      rw [q8BiquadU_sq]
      ring
    simpa [p] using h

theorem q8BiquadV_isIntegral : IsIntegral ℤ q8BiquadV := by
  let p : ℤ[X] := X ^ 2 - X - 10
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    monicity <;> norm_num
  · have h : (q8BiquadV ^ 2 - q8BiquadV - 10 : K2) = 0 := by
      rw [q8BiquadV_sq]
      ring
    simpa [p] using h

theorem q8BiquadIntegralBasis_isIntegral (ij : Fin 2 × Fin 2) :
    IsIntegral ℤ (q8BiquadIntegralBasis ij) := by
  obtain ⟨i, j⟩ := ij
  rw [q8BiquadIntegralBasis, Module.Basis.smulTower_apply,
    q8BiquadUBasis_apply, q8BiquadVBasis_apply]
  simp only [Algebra.smul_def]
  have hU : IsIntegral ℤ
      ((algebraMap K1 K2) q8BiquadU) :=
    q8BiquadU_isIntegral.map (IsScalarTower.toAlgHom ℤ K1 K2)
  fin_cases i <;> fin_cases j
  · simpa [q8BiquadUBasisFamily, q8BiquadVBasisFamily] using
      (isIntegral_one : IsIntegral ℤ (1 : K2))
  · simpa [q8BiquadUBasisFamily, q8BiquadVBasisFamily] using q8BiquadV_isIntegral
  · simpa [q8BiquadUBasisFamily, q8BiquadVBasisFamily] using hU
  · simpa [q8BiquadUBasisFamily, q8BiquadVBasisFamily] using hU.mul q8BiquadV_isIntegral

section NumberFieldConsequences

local instance q8BiquadCharZero : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective

noncomputable local instance q8BiquadFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis

noncomputable local instance q8BiquadFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis

noncomputable local instance q8BiquadFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis

noncomputable local instance q8BiquadNumberField : NumberField K2 := NumberField.mk

theorem q8Biquad_discr_dvd_42025 :
    NumberField.discr K2 ∣ 42025 := by
  exact NumberField.discr_dvd_of_integral_basis_discr
    q8BiquadIntegralBasis q8BiquadIntegralBasis_isIntegral q8BiquadIntegralBasis_discr

/-- Every rational prime dividing the discriminant of the actual maximal
abelian Q8 subfield is one of its two literal source primes. -/
theorem q8Biquad_prime_dvd_discr_eq_five_or_fortyOne
    (p : ℕ) (hp : p.Prime)
    (hpd : (p : ℤ) ∣ NumberField.discr K2) :
    p = 5 ∨ p = 41 := by
  have hp42025 : (p : ℤ) ∣ 42025 :=
    dvd_trans hpd q8Biquad_discr_dvd_42025
  have hpNat : p ∣ 42025 := by
    exact_mod_cast hp42025
  have hfactor : (42025 : ℕ) = 5 ^ 2 * 41 ^ 2 := by norm_num
  rw [hfactor] at hpNat
  rcases (hp.dvd_mul).mp hpNat with h5 | h41
  · have hp5 : p ∣ 5 := hp.dvd_of_dvd_pow h5
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hp5 with hp1 | hp5
    · exact (hp.ne_one hp1).elim
    · exact Or.inl hp5
  · have hp41 : p ∣ 41 := hp.dvd_of_dvd_pow h41
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 41)).mp hp41 with hp1 | hp41
    · exact (hp.ne_one hp1).elim
    · exact Or.inr hp41

/-- Fröhlich Theorem 6(i)'s literal discriminant gate: every prime divisor
of the maximal abelian subfield discriminant is `1 mod 4`. -/
theorem q8Biquad_prime_dvd_discr_mod_four_eq_one
    (p : ℕ) (hp : p.Prime)
    (hpd : (p : ℤ) ∣ NumberField.discr K2) :
    p % 4 = 1 := by
  rcases q8Biquad_prime_dvd_discr_eq_five_or_fortyOne p hp hpd with rfl | rfl <;>
    norm_num

theorem q8Biquad_two_not_dvd_discr :
    ¬ (2 : ℤ) ∣ NumberField.discr K2 := by
  intro htwo
  have : (2 : ℤ) ∣ 42025 := dvd_trans htwo q8Biquad_discr_dvd_42025
  norm_num at this

theorem q8Biquad_two_isUnramifiedIn :
    Algebra.IsUnramifiedIn (𝓞 K2) (Ideal.span {(2 : ℤ)}) := by
  exact (NumberField.not_dvd_discr_iff_isUnramifiedIn
    K2 (𝓞 K2) Int.prime_two).mp q8Biquad_two_not_dvd_discr

end NumberFieldConsequences

end

end RHTower
