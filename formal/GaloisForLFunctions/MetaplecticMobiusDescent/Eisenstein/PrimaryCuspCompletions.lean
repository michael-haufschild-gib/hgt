/-
Primary cusp completions adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CuspReflectionOfTheSource

/-!
# Primary cusp completions

Primary numerators and denominators admit determinant-one completions divisible by nine.
Within a matrix residue class the varying automorphy is the relative cubic character
`primeCuspRowCharacter`; the unit source sums `cuspUnitSourceSum` reflect.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap

lemma cuspSymbol_ramified_fixed_norm (a b c r d u : O)
    (hdet : a * d - b * (u * (c * r)) = 1)
    (ha : lambda ^ 2 ∣ a - 1) (hA : lambda ^ 2 ∣ a - u * b - 1) :
    ‖ringComplex (symbol (-u) (a - u * b) * symbol c a)‖ = 1 := by
  have hfirst : ‖ringComplex (symbol (-u) (a - u * b))‖ = 1 := by
    apply norm_cuspSymbol_of_coprime _ _ hA
    refine ⟨b * (c * r - d), d, ?_⟩
    linear_combination hdet
  have hsecond : ‖ringComplex (symbol c a)‖ = 1 := by
    apply norm_cuspSymbol_of_coprime _ _ ha
    refine ⟨-b * u * r, d, ?_⟩
    linear_combination hdet
  rw [map_mul, norm_mul, hfirst, hsecond, one_mul]

lemma fixedCuspSector_eq_of_relative (M N : SL(2, O)) (h : M * N⁻¹ ∈ levelThree) :
    fixedCuspSector M = fixedCuspSector N := by
  apply Subtype.ext
  change fixedCuspReduction M = fixedCuspReduction N
  have he : fixedCuspReduction (M * N⁻¹) = 1 := h
  rw [map_mul, map_inv] at he
  exact mul_inv_eq_one.mp he

/-- Within one matrix residue class, all varying automorphy is carried by the relative cubic character. -/
lemma fixedCuspGamma_character_relative (M N : SL(2, O)) (h : M * N⁻¹ ∈ levelThree) :
    extendedComplexCharacter (fixedCuspGamma M) =
      complexCharacter ⟨M * N⁻¹, h⟩ * extendedComplexCharacter (fixedCuspGamma N) := by
  have hs := fixedCuspSector_eq_of_relative M N h
  let D : levelThree := ⟨M * N⁻¹, h⟩
  let E : rationalExtension := ⟨(D : SL(2, O)), levelThree_le_rationalExtension D.property⟩
  have he : fixedCuspGamma M = E * fixedCuspGamma N := by
    apply Subtype.ext
    change (fixedCuspGamma M : SL(2, O)) = (M * N⁻¹) * (fixedCuspGamma N : SL(2, O))
    have hm := fixedCusp_factorization M
    rw [hs] at hm
    have hn := fixedCusp_factorization N
    let g : SL(2, O) := fixedCuspGamma M
    let k : SL(2, O) := fixedCuspGamma N
    let T : SL(2, O) := cuspRepresentative (fixedCuspIndex (fixedCuspSector N)) *
      fixedCuspTriangular (fixedCuspSector N)
    have hm' : M = g * T := by simpa only [mul_assoc] using hm
    have hn' : N = k * T := by simpa only [mul_assoc] using hn
    change g = (M * N⁻¹) * k
    rw [hm', hn']
    group
  rw [he, map_mul, extendedComplexCharacter_restrict]

/-- The Weyl cusp chart with integral horizontal coordinate. -/
def weylCuspMatrix (u : O) : SL(2, O) := ⟨!![u, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

lemma lowerCusp_relative_matrix (M : SL(2, O)) (u : O) :
    ((M * (lowerCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) =
      !![M 0 0 - u * M 0 1, M 0 1; M 1 0 - u * M 1 1, M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerCuspMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma weylCusp_relative_matrix (M : SL(2, O)) (u : O) :
    ((M * (weylCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) =
      !![-M 0 1, M 0 0 + u * M 0 1; -M 1 1, M 1 0 + u * M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylCuspMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma lowerCusp_relative_character (M : SL(2, O)) (u : O)
    (h : M * (lowerCuspMatrix u)⁻¹ ∈ levelThree) :
    complexCharacter ⟨M * (lowerCuspMatrix u)⁻¹, h⟩ =
      ringComplex (symbol (M 1 0 - u * M 1 1) (M 0 0 - u * M 0 1)) := by
  change ringComplex (symbol
    (((M * (lowerCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) 1 0)
    (((M * (lowerCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) 0 0)) = _
  rw [lowerCusp_relative_matrix]
  rfl

lemma weylCusp_relative_character (M : SL(2, O)) (u : O)
    (h : M * (weylCuspMatrix u)⁻¹ ∈ levelThree) :
    complexCharacter ⟨M * (weylCuspMatrix u)⁻¹, h⟩ = ringComplex (symbol (-M 1 1) (-M 0 1)) := by
  change ringComplex (symbol
    (((M * (weylCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) 1 0)
    (((M * (weylCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) 0 0)) = _
  rw [weylCusp_relative_matrix]
  rfl

lemma lowerCusp_relative_primary (M : SL(2, O)) (u : O)
    (h : M * (lowerCuspMatrix u)⁻¹ ∈ levelThree) :
    lambda ^ 2 ∣ (M 0 0 - u * M 0 1) - 1 := by
  have hp := levelThree_primary ⟨M * (lowerCuspMatrix u)⁻¹, h⟩
  change lambda ^ 2 ∣ (((M * (lowerCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) 0 0) - 1 at hp
  rw [lowerCusp_relative_matrix] at hp
  exact hp

/-- The ramified cusp character is a fixed factor times the moving cubic row. -/
theorem fixedCuspGamma_ramified_factor (M : SL(2, O)) (u c r : O)
    (h : M * (lowerCuspMatrix u)⁻¹ ∈ levelThree)
    (ha : lambda ^ 2 ∣ M 0 0 - 1) (hr : lambda ^ 2 ∣ r - 1)
    (hC : M 1 0 = u * (c * r)) :
    extendedComplexCharacter (fixedCuspGamma M) =
      (ringComplex (symbol (-u) (M 0 0 - u * M 0 1) * symbol c (M 0 0)) *
        extendedComplexCharacter (fixedCuspGamma (lowerCuspMatrix u))) *
      ringComplex (symbol (M 0 0) r) := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * (u * (c * r)) = 1 := by
    simpa only [Matrix.det_fin_two, hC] using M.property
  rw [fixedCuspGamma_character_relative M (lowerCuspMatrix u) h, lowerCusp_relative_character, hC,
    cuspSymbol_ramified_factor _ _ _ _ _ _ hdet ha (lowerCusp_relative_primary M u h) hr, map_mul]
  ring

/-- The Weyl cusp character is a fixed factor times the moving cubic row. -/
theorem fixedCuspGamma_weyl_factor (M : SL(2, O)) (u c r : O)
    (h : M * (weylCuspMatrix u)⁻¹ ∈ levelThree)
    (hc : lambda ^ 2 ∣ M 1 0 - 1) (h9 : (9 : O) ∣ M 0 0 * M 1 1)
    (hC : M 1 0 = c * r) :
    extendedComplexCharacter (fixedCuspGamma M) =
      (ringComplex (symbol (M 0 0) c) * extendedComplexCharacter (fixedCuspGamma (weylCuspMatrix u))) *
        ringComplex (symbol (M 0 0) r) := by
  have hb := levelThree_primary ⟨M * (weylCuspMatrix u)⁻¹, h⟩
  change lambda ^ 2 ∣ (((M * (weylCuspMatrix u)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) 0 0) - 1 at hb
  rw [weylCusp_relative_matrix] at hb
  change lambda ^ 2 ∣ -M 0 1 - 1 at hb
  have hdet : M 0 0 * M 1 1 - M 0 1 * (c * r) = 1 := by
    simpa only [Matrix.det_fin_two, hC] using M.property
  rw [hC] at hc
  rw [fixedCuspGamma_character_relative M (weylCuspMatrix u) h, weylCusp_relative_character,
    cuspSymbol_weyl_factor _ _ _ _ _ hdet hb hc h9, map_mul]
  ring

/-- A primary numerator admits a determinant-one completion whose upper-right entry is divisible by nine. -/
lemma exists_primary_numerator_matrix (a c : O) (hac : IsCoprime a c)
    (ha : lambda ^ 2 ∣ a - 1) :
    ∃ M : SL(2, O), M 0 0 = a ∧ M 1 0 = c ∧ (9 : O) ∣ M 0 1 ∧ (3 : O) ∣ M 1 1 - 1 := by
  have ha3 := primary_coprime_three a ha
  have ha9 : IsCoprime a (9 : O) := by
    simpa only [show (3 : O) * 3 = 9 from by norm_num] using ha3.mul_right ha3
  obtain ⟨d, t, ht⟩ := ha9.mul_right hac
  have hdet : a * d - (-9 * t) * c = 1 := by linear_combination ht
  let M : SL(2, O) := ⟨!![a, -9 * t; c, d], by rw [Matrix.det_fin_two]; exact hdet⟩
  refine ⟨M, rfl, rfl, ⟨-t, by change -9 * t = 9 * (-t); ring⟩, ?_⟩
  have hb : (3 : O) ∣ -9 * t := ⟨-3 * t, by ring⟩
  change (3 : O) ∣ d - 1
  convert dvd_sub (dvd_mul_of_dvd_left hb c)
    (dvd_mul_of_dvd_left (three_dvd_primary_sub_one a ha) d) using 1
  linear_combination hdet

/-- A primary denominator admits a determinant-one completion whose lower-right entry is divisible by nine. -/
lemma exists_primary_denominator_matrix (a c : O) (hac : IsCoprime a c)
    (hc : lambda ^ 2 ∣ c - 1) :
    ∃ M : SL(2, O), M 0 0 = a ∧ M 1 0 = c ∧ (3 : O) ∣ M 0 1 + 1 ∧ (9 : O) ∣ M 1 1 := by
  have hc3 := primary_coprime_three c hc
  have hc9 : IsCoprime c (9 : O) := by
    simpa only [show (3 : O) * 3 = 9 from by norm_num] using hc3.mul_right hc3
  obtain ⟨y, x, ht⟩ := hc9.mul_right hac.symm
  have hdet : a * (9 * x) - (-y) * c = 1 := by linear_combination ht
  let M : SL(2, O) := ⟨!![a, -y; c, 9 * x], by rw [Matrix.det_fin_two]; exact hdet⟩
  refine ⟨M, rfl, rfl, ?_, ⟨x, rfl⟩⟩
  have hd : (3 : O) ∣ 9 * x := ⟨3 * x, by ring⟩
  change (3 : O) ∣ -y + 1
  convert dvd_sub (dvd_mul_of_dvd_right hd a)
    (dvd_mul_of_dvd_right (three_dvd_primary_sub_one c hc) (-y)) using 1
  linear_combination -hdet

/-- Primitive columns congruent modulo a fixed modulus admit completions in one matrix residue class. -/
lemma exists_fixed_matrix_family {ι : Type*} (i₀ : ι) (a : ι → O) (c N : O)
    (hac : ∀ i, IsCoprime (a i) c) (ha : ∀ i, N ∣ a i - a i₀)
    (M₀ : SL(2, O)) (hM₀a : M₀ 0 0 = a i₀) (hM₀c : M₀ 1 0 = c) :
    ∃ M : ι → SL(2, O), (∀ i, M i 0 0 = a i) ∧ (∀ i, M i 1 0 = c) ∧
      (∀ i r s, N ∣ M i r s - M₀ r s) ∧ ∀ i r s, N ∣ M i r s - M i₀ r s := by
  have hex (i : ι) := primitiveColumn_congruent_completion M₀ (a i) c N (hac i)
    (by simpa only [hM₀a] using ha i) (by simp only [hM₀c, sub_self, dvd_zero])
  choose M hMa hMc hMM using hex
  refine ⟨M, hMa, hMc, hMM, ?_⟩
  intro i r s
  convert dvd_sub (hMM i r s) (hMM i₀ r s) using 1
  ring

lemma primary_numerator_matrix_relative (M : SL(2, O)) (u : O)
    (ha : lambda ^ 2 ∣ M 0 0 - 1) (hb : (9 : O) ∣ M 0 1)
    (hc : (3 : O) ∣ M 1 0 - u) (hd : (3 : O) ∣ M 1 1 - 1) :
    M * (lowerCuspMatrix u)⁻¹ ∈ levelThree := by
  apply integralMatrix_congruent_levelThree
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [lowerCuspMatrix] using three_dvd_primary_sub_one (M 0 0) ha
  · simpa [lowerCuspMatrix] using
      (show (3 : O) ∣ 9 from ⟨3, by norm_num⟩).trans hb
  · simpa [lowerCuspMatrix] using hc
  · simpa [lowerCuspMatrix] using hd

lemma primary_denominator_matrix_relative (M : SL(2, O)) (u : O)
    (ha : (3 : O) ∣ M 0 0 - u) (hb : (3 : O) ∣ M 0 1 + 1)
    (hc : lambda ^ 2 ∣ M 1 0 - 1) (hd : (9 : O) ∣ M 1 1) :
    M * (weylCuspMatrix u)⁻¹ ∈ levelThree := by
  apply integralMatrix_congruent_levelThree
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [weylCuspMatrix] using ha
  · simpa [weylCuspMatrix] using hb
  · simpa [weylCuspMatrix] using three_dvd_primary_sub_one (M 1 0) hc
  · simpa [weylCuspMatrix] using
      (show (3 : O) ∣ 9 from ⟨3, by norm_num⟩).trans hd

/-- Unit frequencies on an active prime set, extended by zero elsewhere. -/
def assembleUnitFrequencies {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]
    (s : Finset ι) (u : ∀ i : s, (F i.val)ˣ) (i : ι) : F i := by
  classical
  exact if hi : i ∈ s then (u ⟨i, hi⟩ : F i) else 0

lemma assembleUnitFrequencies_ne_zero_iff {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]
    (s : Finset ι) (u : ∀ i : s, (F i.val)ˣ) (i : ι) :
    assembleUnitFrequencies s u i ≠ 0 ↔ i ∈ s := by
  classical
  by_cases hi : i ∈ s
  · simp only [assembleUnitFrequencies, hi, dite_true, iff_true]
    exact (u ⟨i, hi⟩).ne_zero
  · simp [assembleUnitFrequencies, hi]

lemma assembleUnitFrequencies_bijective {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] :
    Function.Bijective (fun v : Σ s : Finset ι, ∀ i : s, (F i.val)ˣ => assembleUnitFrequencies v.1 v.2) := by
  classical
  constructor
  · rintro ⟨s, u⟩ ⟨t, v⟩ he
    have hst : s = t := by
      apply Finset.ext
      intro i
      rw [← assembleUnitFrequencies_ne_zero_iff s u i, ← assembleUnitFrequencies_ne_zero_iff t v i]
      exact Iff.of_eq (congrArg (fun f : ∀ i, F i => f i ≠ 0) he)
    subst t
    have huv : u = v := by
      funext i
      apply Units.ext
      have h := congrFun he i.val
      simpa only [assembleUnitFrequencies, dif_pos i.property] using h
    subst v
    rfl
  · intro f
    let s : Finset ι := Finset.univ.filter (fun i => f i ≠ 0)
    let u : ∀ i : s, (F i.val)ˣ := fun i => Units.mk0 (f i.val) (Finset.mem_filter.mp i.property).2
    refine ⟨⟨s, u⟩, ?_⟩
    funext i
    by_cases hi : f i = 0
    · simp [assembleUnitFrequencies, s, hi]
    · have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      simp only [assembleUnitFrequencies, dif_pos his, u, Units.val_mk0]

/-- Every finite frequency sum splits exactly into active unit-frequency strata. -/
theorem finite_frequency_sum_strata {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)] (A : (∀ i, F i) → ℂ) :
    (∑ x : ∀ i, F i, A x) =
      ∑ s : Finset ι, ∑ u : ∀ i : s, (F i.val)ˣ, A (assembleUnitFrequencies s u) := by
  classical
  let e : (Σ s : Finset ι, ∀ i : s, (F i.val)ˣ) ≃ (∀ i, F i) :=
    Equiv.ofBijective _ assembleUnitFrequencies_bijective
  have he := Fintype.sum_equiv e (fun v => A (assembleUnitFrequencies v.1 v.2)) A (fun _ => rfl)
  rw [Fintype.sum_sigma] at he
  exact he.symm

/-- Inactive frequencies vanish for nontrivial multiplicative characters. -/
lemma finiteAdditiveFourierCoeff_mulChar_zero {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    finiteAdditiveFourierCoeff ψ χ 0 =
      if χ = 1 then (Nat.card Fˣ : ℂ) / (Fintype.card F : ℂ) else 0 := by
  classical
  have he : (∑ x : F, χ x * ψ (-(0 : F) * x)) = gaussSum χ (1 : AddChar F ℂ) := by
    simp only [neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one, gaussSum, AddChar.one_apply]
  rw [finiteAdditiveFourierCoeff, he]
  by_cases hχ : χ = 1
  · rw [if_pos hχ, hχ, gaussSum_one_one]
  · rw [if_neg hχ, gaussSum_one_right hχ, zero_div]

/-- A stratum vanishes if it omits a prime carrying a nontrivial row character. -/
lemma finite_frequency_stratum_vanishes {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (ψ : ∀ i, AddChar (F i) ℂ)
    (s : Finset ι) (u : ∀ i : s, (F i.val)ˣ) (k : ι) (hk : k ∉ s) (hχ : χ k ≠ 1) :
    (∏ i, finiteAdditiveFourierCoeff (ψ i) (χ i) (assembleUnitFrequencies s u i)) = 0 := by
  classical
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  rw [assembleUnitFrequencies, dif_neg hk, finiteAdditiveFourierCoeff_mulChar_zero, if_neg hχ]

/-- A residue unit has a lift divisible by the square of any coprime fixed modulus. -/
lemma exists_unit_frequency_lift (N p : O) (hNp : IsCoprime N p)
    (v : (O ⧸ Ideal.span {p})ˣ) :
    ∃ t : O, N ^ 2 ∣ t ∧ Ideal.Quotient.mk (Ideal.span {p}) t = (v : O ⧸ Ideal.span {p}) ∧
      IsCoprime t p := by
  have hN2 : IsCoprime (N ^ 2) p := by simpa only [pow_two] using hNp.mul_left hNp
  obtain ⟨a, b, hab⟩ := hN2
  let x : O := Quotient.out (v : O ⧸ Ideal.span {p})
  let t : O := N ^ 2 * a * x
  have hd : p ∣ t - x := by
    refine ⟨-b * x, ?_⟩
    dsimp only [t]
    linear_combination x * hab
  have he : Ideal.Quotient.mk (Ideal.span {p}) t = (v : O ⧸ Ideal.span {p}) :=
    (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hd)).trans (Ideal.Quotient.mk_out _)
  refine ⟨t, ⟨a * x, by dsimp only [t]; ring⟩, he, ?_⟩
  apply IsCoprime.symm
  apply (isUnit_quotient_span_iff p t).mp
  rw [he]
  exact v.isUnit

lemma cusp_isCoprime_of_dvd_sub (m a b : O) (hab : m ∣ a - b) (hb : IsCoprime m b) :
    IsCoprime m a := by
  obtain ⟨r, hr⟩ := hab
  obtain ⟨u, v, hv⟩ := hb
  refine ⟨u - v * r, v, ?_⟩
  linear_combination hv + v * hr

/-- The complementary prime product in a finite conductor. -/
def cuspPrimeCofactor {ι : Type*} [Fintype ι] (p : ι → O) (i : ι) : O := by
  classical
  exact ∏ k ∈ Finset.univ.erase i, p k

lemma cuspPrime_mul_cofactor {ι : Type*} [Fintype ι] (p : ι → O) (i : ι) :
    p i * cuspPrimeCofactor p i = ∏ k, p k := by
  classical
  exact Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

lemma cuspPrime_dvd_other_cofactor {ι : Type*} [Fintype ι] (p : ι → O) {i k : ι} (hik : i ≠ k) :
    p i ∣ cuspPrimeCofactor p k := by
  classical
  exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)

/-- A common denominator for the fixed cusp and its local additive frequencies. -/
def cuspCrossNumerator {ι : Type*} [Fintype ι] (a c l : O) (p h : ι → O) : O :=
  a * (∏ i, p i) + l ^ 2 * c * ∑ i, h i * cuspPrimeCofactor p i

lemma cuspCrossNumerator_local {ι : Type*} [Fintype ι] (a c l : O) (p h : ι → O) (i : ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (cuspCrossNumerator a c l p h) =
      Ideal.Quotient.mk (Ideal.span {p i}) (l ^ 2 * c * cuspPrimeCofactor p i) *
        Ideal.Quotient.mk (Ideal.span {p i}) (h i) := by
  classical
  let q := Ideal.Quotient.mk (Ideal.span {p i})
  have hz : q (∏ k, p k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ⟨cuspPrimeCofactor p i, (cuspPrime_mul_cofactor p i).symm⟩)
  have hs : (∑ k, q (h k) * q (cuspPrimeCofactor p k)) = q (h i) * q (cuspPrimeCofactor p i) := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      have hk0 : q (cuspPrimeCofactor p k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (cuspPrime_dvd_other_cofactor p hki.symm))
      rw [hk0, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  change q (cuspCrossNumerator a c l p h) = q (l ^ 2 * c * cuspPrimeCofactor p i) * q (h i)
  simp only [cuspCrossNumerator, map_add, map_mul, map_sum, map_pow, hz, mul_zero, zero_add, hs]
  ring

lemma cuspCrossNumerator_fixed {ι : Type*} [Fintype ι] (N a c l : O) (p h : ι → O)
    (hh : ∀ i, N ∣ h i) : N ∣ cuspCrossNumerator a c l p h - a * (∏ i, p i) := by
  have hs : N ∣ ∑ i, h i * cuspPrimeCofactor p i :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (hh i) _)
  convert dvd_mul_of_dvd_right hs (l ^ 2 * c) using 1
  simp only [cuspCrossNumerator, add_sub_cancel_left]

/-- Pairwise coprime local moduli and unit frequencies produce a primitive cusp column. -/
lemma cuspCrossNumerator_coprime {ι : Type*} [Fintype ι] (a c l : O) (p h : ι → O)
    (hbase : IsCoprime a c) (hpair : Pairwise (Function.onFun IsCoprime p))
    (hc : ∀ i, IsCoprime c (p i)) (hl : ∀ i, IsCoprime l (p i))
    (hh : ∀ i, IsCoprime (h i) (p i)) :
    IsCoprime (cuspCrossNumerator a c l p h) (c * ∏ i, p i) := by
  classical
  have hmodc : c ∣ cuspCrossNumerator a c l p h - a * (∏ i, p i) := by
    refine ⟨l ^ 2 * (∑ i, h i * cuspPrimeCofactor p i), ?_⟩
    dsimp only [cuspCrossNumerator]
    ring
  have hcR : IsCoprime c (∏ i, p i) := IsCoprime.prod_right (fun i _ => hc i)
  have hca := cusp_isCoprime_of_dvd_sub c _ _ hmodc (hbase.symm.mul_right hcR)
  apply hca.symm.mul_right
  apply IsCoprime.prod_right
  intro i hi
  have hcof : IsCoprime (p i) (cuspPrimeCofactor p i) :=
    IsCoprime.prod_right (fun k hk => hpair (Ne.symm (Finset.mem_erase.mp hk).1))
  have hl2 : IsCoprime (p i) (l ^ 2) := by
    simpa only [pow_two] using (hl i).symm.mul_right (hl i).symm
  have hterm : IsCoprime (p i) (l ^ 2 * c * cuspPrimeCofactor p i * h i) :=
    ((hl2.mul_right (hc i).symm).mul_right hcof).mul_right (hh i).symm
  have he := cuspCrossNumerator_local a c l p h i
  rw [← map_mul] at he
  have hd : p i ∣ cuspCrossNumerator a c l p h - l ^ 2 * c * cuspPrimeCofactor p i * h i :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact (cusp_isCoprime_of_dvd_sub (p i) _ _ hd hterm).symm

/-- Local unit frequencies admit primitive cusp matrices in a single residue class. -/
theorem exists_fixed_cusp_frequency_matrices {ι : Type*} [Fintype ι]
    (p : ι → O) (N a c l : O)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (hp : ∀ i, lambda ^ 2 ∣ p i - 1) (hNp : ∀ i, IsCoprime N (p i))
    (h9N : (9 : O) ∣ N) (hcN : c ∣ N) (hlN : l ∣ N)
    (hac : IsCoprime a c) (mode : Bool)
    (hbase : if mode then lambda ^ 2 ∣ a - 1 else lambda ^ 2 ∣ c - 1) :
    ∃ (lift : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → ι → O)
      (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O)),
      (∀ v i, N ^ 2 ∣ lift v i) ∧
      (∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (lift v i) = (v i : O ⧸ Ideal.span {p i})) ∧
      (∀ v, M v 0 0 = cuspCrossNumerator a c l p (lift v)) ∧
      (∀ v, M v 1 0 = c * ∏ i, p i) ∧
      (∀ v r s, N ∣ M v r s - M (fun _ => 1) r s) ∧
      (∀ v, if mode then (9 : O) ∣ M v 0 1 ∧ (3 : O) ∣ M v 1 1 - 1
        else (3 : O) ∣ M v 0 1 + 1 ∧ (9 : O) ∣ M v 1 1) := by
  classical
  have h3N : (3 : O) ∣ N := (show (3 : O) ∣ 9 from ⟨3, by norm_num⟩).trans h9N
  have hprimaryN : lambda ^ 2 ∣ N := lambda_sq_dvd_three.trans h3N
  have hr : lambda ^ 2 ∣ (∏ i, p i) - 1 :=
    primary_finset_product Finset.univ p (fun i _ => hp i)
  have hlf (v : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (i : ι) :=
    exists_unit_frequency_lift N (p i) (hNp i) (v i)
  choose lift hperiod hres hcop using hlf
  let A := fun v => cuspCrossNumerator a c l p (lift v)
  have hA (v) : N ∣ A v - a * ∏ i, p i :=
    cuspCrossNumerator_fixed N a c l p (lift v)
      (fun i => (dvd_pow_self N (by decide : (2 : ℕ) ≠ 0)).trans (hperiod v i))
  have hAA (v) : N ∣ A v - A (fun _ => 1) := by
    convert dvd_sub (hA v) (hA (fun _ => 1)) using 1
    ring
  have hprimitive (v) : IsCoprime (A v) (c * ∏ i, p i) :=
    cuspCrossNumerator_coprime a c l p (lift v) hac hpair
      (fun i => (hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i => (hNp i).of_isCoprime_of_dvd_left hlN) (hcop v)
  have hfirst : ∃ M₀ : SL(2, O), M₀ 0 0 = A (fun _ => 1) ∧ M₀ 1 0 = c * ∏ i, p i ∧
      (if mode then (9 : O) ∣ M₀ 0 1 ∧ (3 : O) ∣ M₀ 1 1 - 1
        else (3 : O) ∣ M₀ 0 1 + 1 ∧ (9 : O) ∣ M₀ 1 1) := by
    cases mode
    · exact exists_primary_denominator_matrix _ _ (hprimitive _) (primary_mul c _ hbase hr)
    · apply exists_primary_numerator_matrix _ _ (hprimitive _)
      convert dvd_add (hprimaryN.trans (hA (fun _ => 1))) (primary_mul a _ hbase hr) using 1
      ring
  obtain ⟨M₀, hM₀a, hM₀c, hM₀⟩ := hfirst
  obtain ⟨M, hMa, hMc, hMM₀, hMM⟩ := exists_fixed_matrix_family
    (fun _ => 1) A (c * ∏ i, p i) N hprimitive hAA M₀ hM₀a hM₀c
  refine ⟨lift, M, hperiod, hres, hMa, hMc, hMM, ?_⟩
  intro v
  cases mode
  · constructor
    · convert dvd_add (h3N.trans (hMM₀ v 0 1)) hM₀.1 using 1
      ring
    · convert dvd_add (h9N.trans (hMM₀ v 1 1)) hM₀.2 using 1
      ring
  · constructor
    · convert dvd_add (h9N.trans (hMM₀ v 0 1)) hM₀.1 using 1
      ring
    · convert dvd_add (h3N.trans (hMM₀ v 1 1)) hM₀.2 using 1
      ring

/-- A common-denominator cusp represents the sum of its local rational frequencies. -/
lemma cuspCrossNumerator_fraction {ι : Type*} [Fintype ι] (a c l : O) (p h : ι → O)
    (hc : c ≠ 0) (hp : ∀ i, p i ≠ 0) :
    ringComplex (cuspCrossNumerator a c l p h) / ringComplex (c * ∏ i, p i) =
      ringComplex a / ringComplex c + ringComplex l ^ 2 * ∑ i, ringComplex (h i) / ringComplex (p i) := by
  classical
  have hec : ringComplex c ≠ 0 := ringComplex_ne_zero hc
  have hep (i) : ringComplex (p i) ≠ 0 := ringComplex_ne_zero (hp i)
  have her : ringComplex (∏ i, p i) ≠ 0 :=
    ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hterm (i) : ringComplex (h i * cuspPrimeCofactor p i) / ringComplex (∏ k, p k) =
      ringComplex (h i) / ringComplex (p i) := by
    rw [← cuspPrime_mul_cofactor p i, map_mul, map_mul]
    have hecof : ringComplex (cuspPrimeCofactor p i) ≠ 0 := by
      intro hz
      apply her
      rw [← cuspPrime_mul_cofactor p i, map_mul, hz, mul_zero]
    field_simp
  have hsum : (∑ i, ringComplex (h i) * ringComplex (cuspPrimeCofactor p i)) =
      (∑ i, ringComplex (h i) / ringComplex (p i)) * ringComplex (∏ i, p i) := by
    apply (div_eq_iff her).mp
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by simpa only [map_mul] using hterm i)
  simp only [cuspCrossNumerator, map_add, map_mul, map_pow, map_sum]
  rw [hsum]
  field_simp

/-- The lower-right matrix entry reduces to the inverse of the local numerator. -/
lemma cuspMatrix_inverse_local {ι : Type*} [Fintype ι] (p : ι → O) (c : O)
    (M : SL(2, O)) (hM : M 1 0 = c * ∏ i, p i) (i : ι)
    (s : (O ⧸ Ideal.span {p i})ˣ)
    (hs : Ideal.Quotient.mk (Ideal.span {p i}) (M 0 0) = (s : O ⧸ Ideal.span {p i})) :
    Ideal.Quotient.mk (Ideal.span {p i}) (M 1 1) = (↑s⁻¹ : O ⧸ Ideal.span {p i}) := by
  let q := Ideal.Quotient.mk (Ideal.span {p i})
  have hz : q (M 1 0) = 0 := by
    rw [hM]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    exact dvd_mul_of_dvd_right ⟨cuspPrimeCofactor p i, (cuspPrime_mul_cofactor p i).symm⟩ c
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.property
  have he := congrArg q hd
  simp only [map_sub, map_mul, map_one, hz, mul_zero, sub_zero] at he
  have hs' : q (M 0 0) = (s : O ⧸ Ideal.span {p i}) := hs
  rw [hs'] at he
  calc
    q (M 1 1) = (↑s⁻¹ : O ⧸ Ideal.span {p i}) * ((s : O ⧸ Ideal.span {p i}) * q (M 1 1)) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [he, mul_one]

lemma tracePhase_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    tracePhase (∑ i ∈ s, f i) = ∏ i ∈ s, tracePhase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- Complementary-prime inverses give the exact finite CRT factorization of the trace character. -/
theorem residueTraceQuotientChar_finite_crt {ι : Type*} [Fintype ι]
    (p t : ι → O) (hp : ∀ i, p i ≠ 0)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (ht : ∀ i, p i ∣ cuspPrimeCofactor p i * t i - 1) (z : O) :
    residueTraceQuotientChar 1 (∏ i, p i)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) z) =
    ∏ i, residueTraceQuotientChar 1 (p i) (hp i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (t i * z)) := by
  classical
  let S : O := ∑ i, t i * z * cuspPrimeCofactor p i
  have hd : (∏ i, p i) ∣ z - S := by
    apply Fintype.prod_dvd_of_isRelPrime (fun i k hik => (hpair hik).isRelPrime)
    intro i
    let q := Ideal.Quotient.mk (Ideal.span {p i})
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq.mp
    change q z = q S
    have ht' : q (cuspPrimeCofactor p i) * q (t i) = 1 := by
      have he := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (ht i))
      simpa only [map_mul, map_one] using he
    have hs : (∑ k, q (t k) * q z * q (cuspPrimeCofactor p k)) =
        q (t i) * q z * q (cuspPrimeCofactor p i) := by
      apply Finset.sum_eq_single i
      · intro k hk hki
        have he : q (cuspPrimeCofactor p k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton.mpr (cuspPrime_dvd_other_cofactor p hki.symm))
        rw [he, mul_zero]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    simp only [S, map_sum, map_mul, hs]
    calc
      q z = (q (cuspPrimeCofactor p i) * q (t i)) * q z := by rw [ht', one_mul]
      _ = _ := by ring
  have he : Ideal.Quotient.mk (Ideal.span {∏ i, p i}) z =
      Ideal.Quotient.mk (Ideal.span {∏ i, p i}) S :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hd)
  rw [he, residueTraceQuotientChar_phase, one_mul]
  simp_rw [residueTraceQuotientChar_phase, one_mul]
  simp only [S, map_sum, map_mul, Finset.sum_div, tracePhase_finset_sum]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  have hep := ringComplex_ne_zero (hp i)
  have heR : ringComplex (∏ i, p i) ≠ 0 := ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hel := ringComplex_ne_zero traceLambda_ne_zero
  have hprod := congrArg ringComplex (cuspPrime_mul_cofactor p i)
  simp only [map_mul] at hprod
  apply (div_eq_div_iff (mul_ne_zero heR hel) (mul_ne_zero hep hel)).mpr
  linear_combination ringComplex (t i) * ringComplex z * ringComplex traceLambda * hprod

/-- The fixed denominator and the prime conductor split by Bezout before local Fourier summation. -/
lemma cuspInverse_phase_pair (c r d U w x : O) (hc : c ≠ 0) (hr : r ≠ 0)
    (hbez : U * r + (traceLambda ^ 3 * w) * c = 1) :
    tracePhase (-(ringComplex d * ringComplex x) / (ringComplex traceLambda ^ 4 * ringComplex c * ringComplex r)) =
      tracePhase (-(ringComplex d * ringComplex U * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c)) *
      residueTraceQuotientChar 1 r hr (Ideal.Quotient.mk (Ideal.span {r}) (-d * w * x)) := by
  rw [residueTraceQuotientChar_phase, one_mul, ← AddChar.map_add_eq_mul]
  congr 1
  have he := congrArg ringComplex hbez
  simp only [map_add, map_mul, map_pow, map_one] at he
  have hec := ringComplex_ne_zero hc
  have her := ringComplex_ne_zero hr
  have hel := ringComplex_ne_zero traceLambda_ne_zero
  simp only [map_neg, map_mul]
  field_simp
  linear_combination (ringComplex d * ringComplex x) * he

lemma cuspInverse_fixed_phase_congr (c d e U x : O) (hc : c ≠ 0)
    (hde : traceLambda ^ 3 * c ∣ d - e) :
    tracePhase (-(ringComplex d * ringComplex U * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c)) =
    tracePhase (-(ringComplex e * ringComplex U * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c)) := by
  have hmod : traceLambda ^ 3 * c ∣ (-d * U * x) - (-e * U * x) := by
    convert dvd_mul_of_dvd_left hde (-U * x) using 1
    ring
  have hq := congrArg (residueTraceQuotientChar 1 (traceLambda ^ 3 * c)
    (mul_ne_zero (pow_ne_zero _ traceLambda_ne_zero) hc))
    (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hmod))
  have hephase (y : O) :
      tracePhase (-(ringComplex y * ringComplex U * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c)) =
      residueTraceQuotientChar 1 (traceLambda ^ 3 * c)
        (mul_ne_zero (pow_ne_zero _ traceLambda_ne_zero) hc)
        (Ideal.Quotient.mk (Ideal.span {traceLambda ^ 3 * c}) (-y * U * x)) := by
    rw [residueTraceQuotientChar_phase, one_mul]
    congr 1
    simp only [map_neg, map_mul, map_pow]
    ring
  exact (hephase d).trans (hq.trans (hephase e).symm)

lemma symbol_finset_denominator {ι : Type*} (s : Finset ι) (p : ι → O) (a : O) :
    symbol a (∏ i ∈ s, p i) = ∏ i ∈ s, symbol a (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, symbol_one]
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, symbol_mul_denominator, ih]

/-- The conjugate cubic symbol is the product of inverse-square sextic characters. -/
lemma cuspSymbol_sextic_product {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i}) (a : O) :
    star (ringComplex (symbol a (∏ i, p i))) =
      ∏ i, ((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹ ^ 2)
        (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
  classical
  rw [symbol_finset_denominator, map_prod, star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have he : ringComplex (symbol a (p i)) =
      (complexSexticChar (Ideal.span {p i}) (hg i) ^ 2) (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
    rw [(complexSexticChar_powers (Ideal.span {p i}) (hg i)).1]
    change ringComplex (idealSymbol (Ideal.span {p i}) a) = _
    rw [idealSymbol_prime _ (hg i)]
    rfl
  rw [he, MulChar.star_apply', inv_pow]

/-- The numerator scale and the inverse-cusp phase have unit local coefficients. -/
lemma exists_cusp_local_units {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (c d l : O)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (hc : ∀ i, IsCoprime c (p i)) (hd : ∀ i, IsCoprime d (p i))
    (hl : ∀ i, IsCoprime l (p i)) :
    ∃ σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ,
      (∀ i, (σ i : O ⧸ Ideal.span {p i}) =
        Ideal.Quotient.mk (Ideal.span {p i}) (l ^ 2 * c * cuspPrimeCofactor p i)) ∧
      (∀ i, Ideal.Quotient.mk (Ideal.span {p i}) (l ^ 3 * d * cuspPrimeCofactor p i) *
        (σ i : O ⧸ Ideal.span {p i}) * (ε i : O ⧸ Ideal.span {p i}) = -1) := by
  classical
  have hcof (i) : IsCoprime (p i) (cuspPrimeCofactor p i) :=
    IsCoprime.prod_right (fun k hk => hpair (Ne.symm (Finset.mem_erase.mp hk).1))
  have hpow2 (i) : IsCoprime (p i) (l ^ 2) := by
    simpa only [pow_two] using (hl i).symm.mul_right (hl i).symm
  have hpow3 (i) : IsCoprime (p i) (l ^ 3) := by
    simpa only [show (3 : ℕ) = 2 + 1 from rfl, pow_succ] using (hpow2 i).mul_right (hl i).symm
  have hσ (i) := (isUnit_quotient_span_iff (p i) (l ^ 2 * c * cuspPrimeCofactor p i)).mpr
    (((hpow2 i).mul_right (hc i).symm).mul_right (hcof i))
  have hδ (i) := (isUnit_quotient_span_iff (p i) (l ^ 3 * d * cuspPrimeCofactor p i)).mpr
    (((hpow3 i).mul_right (hd i).symm).mul_right (hcof i))
  choose σ hσ using hσ
  choose δ hδ using hδ
  refine ⟨σ, (fun i => -(δ i * σ i)⁻¹), hσ, ?_⟩
  intro i
  rw [← hδ i, ← Units.val_mul, Units.val_neg, mul_neg, Units.mul_inv]

/-- CRT turns the inverse-cusp coordinate into independent inverse local frequencies. -/
theorem cuspMatrix_inverse_phase_product {ι : Type*} [Fintype ι] (p t : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (ht : ∀ i, p i ∣ cuspPrimeCofactor p i * t i - 1)
    (c U w x : O) (hc : c ≠ 0)
    (hbez : U * (∏ i, p i) + (traceLambda ^ 3 * w) * c = 1)
    (M : SL(2, O)) (hM : (∏ i, p i) ∣ M 1 0)
    (σ ε v : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (hfreq : ∀ i, Ideal.Quotient.mk (Ideal.span {p i}) (M 0 0) =
      (σ i : O ⧸ Ideal.span {p i}) * (v i : O ⧸ Ideal.span {p i}))
    (hε : ∀ i, Ideal.Quotient.mk (Ideal.span {p i})
      (traceLambda ^ 3 * c * cuspPrimeCofactor p i) *
      (σ i : O ⧸ Ideal.span {p i}) * (ε i : O ⧸ Ideal.span {p i}) = -1) :
    tracePhase (-(ringComplex (M 1 1) * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c * ringComplex (∏ i, p i))) =
      tracePhase (-(ringComplex (M 1 1) * ringComplex U * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c)) *
      ∏ i, residueTraceQuotientChar 1 (p i) (hp i)
        ((ε i : O ⧸ Ideal.span {p i}) * Ideal.Quotient.mk (Ideal.span {p i}) x *
          (↑(v i)⁻¹ : O ⧸ Ideal.span {p i})) := by
  classical
  rw [cuspInverse_phase_pair c _ _ U w x hc
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hbez,
    residueTraceQuotientChar_finite_crt p t hp hpair ht]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply congrArg (residueTraceQuotientChar 1 (p i) (hp i))
  let q := Ideal.Quotient.mk (Ideal.span {p i})
  have hR : q (∏ k, p k) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ⟨cuspPrimeCofactor p i, (cuspPrime_mul_cofactor p i).symm⟩)
  have hw : q (traceLambda ^ 3 * c) * q w = 1 := by
    have he := congrArg q hbez
    simp only [map_add, map_mul, map_pow, map_one, hR, mul_zero, zero_add] at he
    simpa only [map_mul, map_pow, mul_assoc, mul_comm, mul_left_comm] using he
  have hti : q (cuspPrimeCofactor p i) * q (t i) = 1 := by
    have he := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (ht i))
    simpa only [map_mul, map_one] using he
  have heps : (q (traceLambda ^ 3 * c) * q (cuspPrimeCofactor p i) *
      (σ i : O ⧸ Ideal.span {p i})) * (ε i : O ⧸ Ideal.span {p i}) = -1 := by
    have he := hε i
    change q ((traceLambda ^ 3 * c) * cuspPrimeCofactor p i) *
      (σ i : O ⧸ Ideal.span {p i}) * (ε i : O ⧸ Ideal.span {p i}) = -1 at he
    rw [map_mul] at he
    exact he
  have hD : q (traceLambda ^ 3 * c) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hw
    exact zero_ne_one hw
  have hRi : q (cuspPrimeCofactor p i) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hti
    exact zero_ne_one hti
  obtain ⟨c₀, hc₀⟩ := hM
  have hcol : M 1 0 = c₀ * ∏ k, p k := by rw [hc₀, mul_comm]
  have hdinv := cuspMatrix_inverse_local p c₀ M hcol i (σ i * v i) (hfreq i)
  change q (M 1 1) = (↑(σ i * v i)⁻¹ : O ⧸ Ideal.span {p i}) at hdinv
  have hsy : (σ i : O ⧸ Ideal.span {p i}) * q (M 1 1) = (↑(v i)⁻¹ : O ⧸ Ideal.span {p i}) := by
    rw [hdinv]
    simp only [mul_inv_rev, Units.val_mul]
    calc
      _ = ((σ i : O ⧸ Ideal.span {p i}) * (↑(σ i)⁻¹ : O ⧸ Ideal.span {p i})) *
          (↑(v i)⁻¹ : O ⧸ Ideal.span {p i}) := by ring
      _ = _ := by rw [Units.mul_inv, one_mul]
  change q (t i * (-M 1 1 * w * x)) = _
  simp only [map_mul, map_neg]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hD hRi) (σ i).ne_zero)
  calc
    _ = -((q (traceLambda ^ 3 * c) * q w) * (q (cuspPrimeCofactor p i) * q (t i)) *
        ((σ i : O ⧸ Ideal.span {p i}) * q (M 1 1)) * q x) := by ring
    _ = -((↑(v i)⁻¹ : O ⧸ Ideal.span {p i}) * q x) := by rw [hw, hti, hsy, one_mul, one_mul]
    _ = (q (traceLambda ^ 3 * c) * q (cuspPrimeCofactor p i) *
        (σ i : O ⧸ Ideal.span {p i})) *
        ((ε i : O ⧸ Ideal.span {p i}) * q x * (↑(v i)⁻¹ : O ⧸ Ideal.span {p i})) := by
      rw [← mul_assoc, ← mul_assoc, heps]
      ring

/-- Controlled completions have one fixed unit phase multiplying the moving cubic symbol. -/
theorem fixedCuspGamma_family_character {ι : Type*} (i₀ : ι)
    (N a c r : O) (h9N : (9 : O) ∣ N) (hcN : c ∣ N)
    (hr : lambda ^ 2 ∣ r - 1) (mode : Bool)
    (hbase : if mode then lambda ^ 2 ∣ a - 1 else lambda ^ 2 ∣ c - 1)
    (M : ι → SL(2, O)) (hMa : ∀ i, N ∣ M i 0 0 - a * r)
    (hMc : ∀ i, M i 1 0 = c * r) (hM : ∀ i j k, N ∣ M i j k - M i₀ j k)
    (hcond : ∀ i, if mode then (9 : O) ∣ M i 0 1 ∧ (3 : O) ∣ M i 1 1 - 1
      else (3 : O) ∣ M i 0 1 + 1 ∧ (9 : O) ∣ M i 1 1) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ i,
      extendedComplexCharacter (fixedCuspGamma (M i)) = κ * ringComplex (symbol (M i 0 0) r) := by
  have h3N : (3 : O) ∣ N := (show (3 : O) ∣ 9 from ⟨3, by norm_num⟩).trans h9N
  have hprimaryN : lambda ^ 2 ∣ N := lambda_sq_dvd_three.trans h3N
  have hdet (i) : M i 0 0 * M i 1 1 - M i 0 1 * (c * r) = 1 := by
    simpa only [Matrix.det_fin_two, hMc] using (M i).property
  cases mode
  · have hprimary : lambda ^ 2 ∣ c * r - 1 := primary_mul c r hbase hr
    have hrelative (i) : M i * (weylCuspMatrix a)⁻¹ ∈ levelThree := by
      apply primary_denominator_matrix_relative (M i) a
      · convert dvd_add (h3N.trans (hMa i))
          (dvd_mul_of_dvd_right (three_dvd_primary_sub_one r hr) a) using 1
        ring
      · exact (hcond i).1
      · rw [hMc]
        exact hprimary
      · exact (hcond i).2
    refine ⟨ringComplex (symbol (M i₀ 0 0) c) *
      extendedComplexCharacter (fixedCuspGamma (weylCuspMatrix a)), ?_, ?_⟩
    · rw [norm_mul, norm_extendedComplexCharacter,
        cuspSymbol_weyl_fixed_norm _ _ _ _ _ (hdet i₀) hbase, one_mul]
    · intro i
      rw [fixedCuspGamma_weyl_factor (M i) a c r (hrelative i)
        (by rw [hMc]; exact hprimary) (dvd_mul_of_dvd_right (hcond i).2 _) (hMc i),
        cuspSymbol_weyl_fixed_congr N c _ _ hcN (hM i 0 0)]
  · have hprimary (i) : lambda ^ 2 ∣ M i 0 0 - 1 := by
      convert dvd_add (hprimaryN.trans (hMa i)) (primary_mul a r hbase hr) using 1
      ring
    have hrelative (i) : M i * (lowerCuspMatrix c)⁻¹ ∈ levelThree := by
      apply primary_numerator_matrix_relative (M i) c (hprimary i) (hcond i).1
      · rw [hMc]
        convert dvd_mul_of_dvd_right (three_dvd_primary_sub_one r hr) c using 1
        ring
      · exact (hcond i).2
    let κ : ℂ := ringComplex
      (symbol (-c) (M i₀ 0 0 - c * M i₀ 0 1) * symbol 1 (M i₀ 0 0)) *
      extendedComplexCharacter (fixedCuspGamma (lowerCuspMatrix c))
    refine ⟨κ, ?_, ?_⟩
    · dsimp only [κ]
      rw [norm_mul, norm_extendedComplexCharacter, mul_one]
      apply cuspSymbol_ramified_fixed_norm _ _ 1 r _ c
      · simpa only [one_mul] using hdet i₀
      · exact hprimary i₀
      · exact lowerCusp_relative_primary (M i₀) c (hrelative i₀)
    · intro i
      rw [fixedCuspGamma_ramified_factor (M i) c 1 r (hrelative i) (hprimary i) hr
        (by simpa only [one_mul] using hMc i),
        cuspSymbol_ramified_fixed_congr N 1 c (M i 0 0) (M i₀ 0 0) (M i 0 1) (M i₀ 0 1)
          h9N (one_dvd N) hcN (hprimary i) (hprimary i₀)
          (lowerCusp_relative_primary (M i) c (hrelative i))
          (lowerCusp_relative_primary (M i₀) c (hrelative i₀)) (hM i 0 0) (hM i 0 1)]

/-- The finite cusp sum is an exact product of local Gauss pairs, including exceptional characters. -/
theorem cuspMatrix_frequency_sum {ι : Type*} [Fintype ι] (p t : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (ht : ∀ i, p i ∣ cuspPrimeCofactor p i * t i - 1)
    (c U w x : O) (hc : c ≠ 0)
    (hbez : U * (∏ i, p i) + (traceLambda ^ 3 * w) * c = 1)
    (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O))
    (hM : ∀ v, (∏ i, p i) ∣ M v 1 0)
    (hfixed : ∀ v, traceLambda ^ 3 * c ∣ M v 1 1 - M (fun _ => 1) 1 1)
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (hfreq : ∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (M v 0 0) =
      (σ i : O ⧸ Ideal.span {p i}) * (v i : O ⧸ Ideal.span {p i}))
    (hε : ∀ i, Ideal.Quotient.mk (Ideal.span {p i})
      (traceLambda ^ 3 * c * cuspPrimeCofactor p i) *
      (σ i : O ⧸ Ideal.span {p i}) * (ε i : O ⧸ Ideal.span {p i}) = -1)
    (κ : ℂ) (hκ : ∀ v, extendedComplexCharacter (fixedCuspGamma (M v)) =
      κ * ringComplex (symbol (M v 0 0) (∏ i, p i))) (j : ι → ℕ) :
    (∑ v : ∀ i, (O ⧸ Ideal.span {p i})ˣ,
      (∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i))
        (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ)
        (v i : O ⧸ Ideal.span {p i})) *
      star (extendedComplexCharacter (fixedCuspGamma (M v))) *
      tracePhase (-(ringComplex (M v 1 1) * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c * ringComplex (∏ i, p i)))) =
    (star κ * tracePhase (-(ringComplex (M (fun _ => 1) 1 1) * ringComplex U * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c))) *
      ∏ i, ((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹ ^ 2) (σ i) *
        ((Fintype.card (O ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
          gaussSum (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i)
            ((residueTraceQuotientChar 1 (p i) (hp i)).mulShift (-1)) *
          gaussSum (complexSexticChar (Ideal.span {p i}) (hg i) ^ (j i + 2))
            ((residueTraceQuotientChar 1 (p i) (hp i)).mulShift
              ((ε i : O ⧸ Ideal.span {p i}) * Ideal.Quotient.mk (Ideal.span {p i}) x))) := by
  classical
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  let ψ := fun i => residueTraceQuotientChar 1 (p i) (hp i)
  let C := star κ * tracePhase
    (-(ringComplex (M (fun _ => 1) 1 1) * ringComplex U * ringComplex x) /
      (ringComplex traceLambda ^ 4 * ringComplex c))
  let f := fun (i : ι) (v : (O ⧸ Ideal.span {p i})ˣ) =>
    finiteAdditiveFourierCoeff (ψ i) (χ i ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ) v *
      ((χ i)⁻¹ ^ 2) v * ψ i ((ε i : O ⧸ Ideal.span {p i}) *
        Ideal.Quotient.mk (Ideal.span {p i}) x * (↑v⁻¹ : O ⧸ Ideal.span {p i}))
  have hpoint (v : ∀ i, (O ⧸ Ideal.span {p i})ˣ) :
      (∏ i, finiteAdditiveFourierCoeff (ψ i) (χ i ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ) (v i)) *
      star (extendedComplexCharacter (fixedCuspGamma (M v))) *
      tracePhase (-(ringComplex (M v 1 1) * ringComplex x) /
        (ringComplex traceLambda ^ 4 * ringComplex c * ringComplex (∏ i, p i))) =
      (C * ∏ i, ((χ i)⁻¹ ^ 2) (σ i)) * ∏ i, f i (v i) := by
    rw [hκ v, star_mul, cuspSymbol_sextic_product p hg,
      cuspMatrix_inverse_phase_product p t hp hpair ht c U w x hc hbez (M v) (hM v) σ ε v (hfreq v) hε,
      cuspInverse_fixed_phase_congr c _ _ U x hc (hfixed v)]
    simp_rw [hfreq v]
    simp only [map_mul, Finset.prod_mul_distrib, C, f, χ, ψ]
    ring
  calc
    _ = (C * ∏ i, ((χ i)⁻¹ ^ 2) (σ i)) * ∑ v : ∀ i, (O ⧸ Ideal.span {p i})ˣ, ∏ i, f i (v i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => hpoint v)
    _ = (C * ∏ i, ((χ i)⁻¹ ^ 2) (σ i)) * ∏ i, ∑ v : (O ⧸ Ideal.span {p i})ˣ, f i v := by
      rw [← Fintype.prod_sum f]
    _ = _ := by
      have he (i) : (∑ v : (O ⧸ Ideal.span {p i})ˣ, f i v) =
          (Fintype.card (O ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
          gaussSum (χ i ^ j i) ((ψ i).mulShift (-1)) *
          gaussSum (χ i ^ (j i + 2)) ((ψ i).mulShift
            ((ε i : O ⧸ Ideal.span {p i}) * Ideal.Quotient.mk (Ideal.span {p i}) x)) :=
        finiteReflectionGauss_product (χ i) (ψ i) (j i) _
      simp_rw [he]
      dsimp only [C, χ, ψ]
      simp only [Finset.prod_mul_distrib]
      ring

/-- An integral numerator for every cusp phase, with a common fixed denominator. -/
def sourceCuspIntegralPhaseNumerator (j : Fin 3) (u h : O) : O :=
  (if j = 0 then 3 else 1) * traceLambda * u ^ 2 * h

lemma sourceCuspIntegralPhaseNumerator_embedding (j : Fin 3) (u h : O) :
    ringComplex (sourceCuspIntegralPhaseNumerator j u h) =
      -3 * ringComplex traceLambda ^ 4 * cuspFrequency h * ringComplex u ^ 2 /
        (sourceCuspScale j : ℂ) := by
  have hl := ringComplex_ne_zero traceLambda_ne_zero
  have hs : ringComplex traceLambda ^ 2 = (-3 : ℂ) := by
    simpa only [map_pow, map_neg, map_ofNat] using congrArg ringComplex traceLambda_square
  have hfour : ringComplex traceLambda ^ 4 = (9 : ℂ) := by
    rw [show ringComplex traceLambda ^ 4 = (ringComplex traceLambda ^ 2) ^ 2 by ring, hs]
    norm_num
  rw [hfour]
  fin_cases j <;>
    norm_num [sourceCuspIntegralPhaseNumerator, sourceCuspScale, cuspFrequency, map_mul, map_pow] <;>
    field_simp <;> simp only [hs, map_ofNat] <;> ring

/-- The common fixed denominator removes all divisibility requirements on cusp frequencies. -/
lemma sourceCuspIntegralPhaseNumerator_phase (j : Fin 3) (u h c d : O) (hc : c ≠ 0) :
    tracePhase (cuspFrequency h * ringComplex u ^ 2 * ringComplex d /
      ((sourceCuspScale j : ℂ) * ringComplex c)) =
    tracePhase (-(ringComplex d * ringComplex (sourceCuspIntegralPhaseNumerator j u h)) /
      (ringComplex traceLambda ^ 4 * ringComplex (3 * c))) := by
  rw [sourceCuspIntegralPhaseNumerator_embedding]
  congr 1
  have hl := ringComplex_ne_zero traceLambda_ne_zero
  have hec := ringComplex_ne_zero hc
  have hscale := Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
  simp only [map_mul, map_ofNat]
  field_simp

lemma traceLambda_pow_four : traceLambda ^ 4 = (9 : O) := by
  rw [show traceLambda ^ 4 = (traceLambda ^ 2) ^ 2 by ring, traceLambda_square]
  norm_num

lemma cuspInverse_fixed_modulus_dvd (c : O) : traceLambda ^ 3 * (3 * c) ∣ (27 : O) * c := by
  refine ⟨traceLambda, ?_⟩
  calc
    (27 : O) * c = 3 * traceLambda ^ 4 * c := by rw [traceLambda_pow_four]; ring
    _ = _ := by ring

/-- Actual local frequencies have controlled cusp completions and a fixed unit character factor. -/
theorem exists_fixed_cusp_frequency_character {ι : Type*} [Fintype ι]
    (p : ι → O) (N a c l : O)
    (hpair : Pairwise (Function.onFun IsCoprime p))
    (hp : ∀ i, lambda ^ 2 ∣ p i - 1) (hNp : ∀ i, IsCoprime N (p i))
    (h9N : (9 : O) ∣ N) (hcN : c ∣ N) (hlN : l ∣ N)
    (hac : IsCoprime a c) (mode : Bool)
    (hbase : if mode then lambda ^ 2 ∣ a - 1 else lambda ^ 2 ∣ c - 1) :
    ∃ (lift : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → ι → O)
      (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O)) (κ : ℂ),
      (∀ v i, N ^ 2 ∣ lift v i) ∧
      (∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (lift v i) = (v i : O ⧸ Ideal.span {p i})) ∧
      (∀ v, M v 0 0 = cuspCrossNumerator a c l p (lift v)) ∧
      (∀ v, M v 1 0 = c * ∏ i, p i) ∧
      (∀ v r s, N ∣ M v r s - M (fun _ => 1) r s) ∧
      ‖κ‖ = 1 ∧ ∀ v, extendedComplexCharacter (fixedCuspGamma (M v)) =
        κ * ringComplex (symbol (M v 0 0) (∏ i, p i)) := by
  obtain ⟨lift, M, hperiod, hres, hMa, hMc, hM, hcond⟩ :=
    exists_fixed_cusp_frequency_matrices p N a c l hpair hp hNp h9N hcN hlN hac mode hbase
  have hMaN (v) : N ∣ M v 0 0 - a * ∏ i, p i := by
    rw [hMa]
    exact cuspCrossNumerator_fixed N a c l p (lift v)
      (fun i => (dvd_pow_self N (by decide : (2 : ℕ) ≠ 0)).trans (hperiod v i))
  obtain ⟨κ, hκnorm, hκ⟩ := fixedCuspGamma_family_character (fun _ => 1) N a c (∏ i, p i)
    h9N hcN (primary_finset_product Finset.univ p (fun i _ => hp i)) mode hbase
    M hMaN hMc hM hcond
  exact ⟨lift, M, κ, hperiod, hres, hMa, hMc, hM, hκnorm, hκ⟩

lemma exists_cuspPrime_inverse {ι : Type*} [Fintype ι] (p : ι → O)
    (hpair : Pairwise (Function.onFun IsCoprime p)) :
    ∃ t : ι → O, ∀ i, p i ∣ cuspPrimeCofactor p i * t i - 1 := by
  classical
  have hex (i) : ∃ t : O, p i ∣ cuspPrimeCofactor p i * t - 1 := by
    have hcof : IsCoprime (p i) (cuspPrimeCofactor p i) :=
      IsCoprime.prod_right (fun k hk => hpair (Ne.symm (Finset.mem_erase.mp hk).1))
    obtain ⟨u, v, h⟩ := hcof
    refine ⟨v, -u, ?_⟩
    linear_combination h
  choose t ht using hex
  exact ⟨t, ht⟩

/-- The fixed modulus supplies the inverse coefficient needed for the reflected trace phase. -/
lemma exists_cuspInverse_bezout {ι : Type*} [Fintype ι] (p : ι → O) (N c : O)
    (hN : (27 : O) * c ∣ N) (hNp : ∀ i, IsCoprime N (p i)) :
    ∃ U w : O, U * (∏ i, p i) + (traceLambda ^ 3 * w) * (3 * c) = 1 := by
  have hNr : IsCoprime N (∏ i, p i) := IsCoprime.prod_right (fun i _ => hNp i)
  have hD : traceLambda ^ 3 * (3 * c) ∣ N := (cuspInverse_fixed_modulus_dvd c).trans hN
  obtain ⟨U, w, h⟩ := hNr.symm.of_isCoprime_of_dvd_right hD
  refine ⟨U, w, ?_⟩
  linear_combination h

/-- The actual finite unit-frequency sum at a common cusp denominator. -/
def cuspUnitFrequencySum {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : O)
    (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O)) (j : ι → ℕ) (x : O) : ℂ :=
  ∑ v : ∀ i, (O ⧸ Ideal.span {p i})ˣ,
    (∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i))
      (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ)
      (v i : O ⧸ Ideal.span {p i})) *
    star (extendedComplexCharacter (fixedCuspGamma (M v))) *
    tracePhase (-(ringComplex (M v 1 1) * ringComplex x) /
      (ringComplex traceLambda ^ 4 * ringComplex (3 * c) * ringComplex (∏ i, p i)))

/-- The local factors retain both nontrivial Gauss sums and the exceptional zero output. -/
def cuspLocalReflectedProduct {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (j : ι → ℕ) (x : O) : ℂ :=
  ∏ i, ((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹ ^ 2) (σ i) *
    finiteReflectionGauss (complexSexticChar (Ideal.span {p i}) (hg i))
      (residueTraceQuotientChar 1 (p i) (hp i)) (j i)
      ((ε i : O ⧸ Ideal.span {p i}) * Ideal.Quotient.mk (Ideal.span {p i}) x)

/-- Every primitive fixed cusp has an exact unit-frequency reflection with all local data constructed. -/
theorem exists_native_cusp_reflection {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp0 : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpair : Pairwise (Function.onFun IsCoprime p)) (hp : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N a c : O) (hc : c ≠ 0) (hN : (27 : O) * c ∣ N)
    (hNp : ∀ i, IsCoprime N (p i)) (hac : IsCoprime a c) (mode : Bool)
    (hbase : if mode then lambda ^ 2 ∣ a - 1 else lambda ^ 2 ∣ c - 1) :
    ∃ (lift : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → ι → O)
      (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O))
      (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (U : O) (κ : ℂ),
      (∀ v i, N ^ 2 ∣ lift v i) ∧
      (∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (lift v i) = (v i : O ⧸ Ideal.span {p i})) ∧
      (∀ v, M v 0 0 = cuspCrossNumerator a c traceLambda p (lift v)) ∧
      (∀ v, M v 1 0 = c * ∏ i, p i) ∧
      (∀ v r s, N ∣ M v r s - M (fun _ => 1) r s) ∧
      ‖κ‖ = 1 ∧ ∀ (j : ι → ℕ) (x : O),
        cuspUnitFrequencySum p hp0 hg c M j x =
          (star κ * tracePhase (-(ringComplex (M (fun _ => 1) 1 1) * ringComplex U * ringComplex x) /
            (ringComplex traceLambda ^ 4 * ringComplex (3 * c)))) *
          cuspLocalReflectedProduct p hp0 hg σ ε j x := by
  have h9N : (9 : O) ∣ N := (show (9 : O) ∣ 27 * c from ⟨3 * c, by ring⟩).trans hN
  have hcN : c ∣ N := (show c ∣ 27 * c from ⟨27, by ring⟩).trans hN
  have h3cN : 3 * c ∣ N := (show (3 : O) * c ∣ 27 * c from ⟨9, by ring⟩).trans hN
  have hlN : traceLambda ∣ N := (show traceLambda ∣ (9 : O) from
    ⟨traceLambda ^ 3, by rw [← traceLambda_pow_four]; ring⟩).trans h9N
  obtain ⟨lift, M, κ, hperiod, hres, hMa, hMc, hfixed, hκnorm, hκ⟩ :=
    exists_fixed_cusp_frequency_character p N a c traceLambda hpair hp hNp h9N hcN hlN hac mode hbase
  obtain ⟨σ, ε, hσ, hε⟩ := exists_cusp_local_units p c (3 * c) traceLambda hpair
    (fun i => (hNp i).of_isCoprime_of_dvd_left hcN)
    (fun i => (hNp i).of_isCoprime_of_dvd_left h3cN)
    (fun i => (hNp i).of_isCoprime_of_dvd_left hlN)
  obtain ⟨U, w, hbez⟩ := exists_cuspInverse_bezout p N c hN hNp
  obtain ⟨t, ht⟩ := exists_cuspPrime_inverse p hpair
  have hfreq (v) (i) : Ideal.Quotient.mk (Ideal.span {p i}) (M v 0 0) =
      (σ i : O ⧸ Ideal.span {p i}) * (v i : O ⧸ Ideal.span {p i}) := by
    rw [hMa, cuspCrossNumerator_local, hres, hσ]
  have hdenom (v) : (∏ i, p i) ∣ M v 1 0 := by
    rw [hMc]
    exact dvd_mul_left _ _
  have hD (v) : traceLambda ^ 3 * (3 * c) ∣ M v 1 1 - M (fun _ => 1) 1 1 :=
    ((cuspInverse_fixed_modulus_dvd c).trans hN).trans (hfixed v 1 1)
  refine ⟨lift, M, σ, ε, U, κ, hperiod, hres, hMa, hMc, hfixed, hκnorm, ?_⟩
  intro j x
  simpa only [cuspUnitFrequencySum, cuspLocalReflectedProduct, finiteReflectionGauss_product] using
    cuspMatrix_frequency_sum p t hp0 hg hpair ht (3 * c) U w x
      (mul_ne_zero (by norm_num) hc) hbez M hdenom hD σ ε hfreq hε κ hκ j

/-- The fixed cusp amplitude; the denominator contributes only an angular phase. -/
def fixedCuspReflectionScalar (s : FixedCuspSector) (c : O) : ℂ :=
  -ringComplex (fixedCuspTriangular s 0 0) ^ 2 *
    (star (ringComplex c) / ringComplex c) * (sourceCuspScale (fixedCuspIndex s) : ℂ) ^ 2

def fixedCuspReflectionScale (s : FixedCuspSector) (c : O) (X : ℝ) : ℝ :=
  27 * (sourceCuspRadialScale 0) ^ 2 * (sourceCuspRadialScale (fixedCuspIndex s)) ^ 2 * X /
    ‖ringComplex c‖ ^ 4

lemma fixedCuspReflectionScale_pos (s : FixedCuspSector) (c : O) (hc : c ≠ 0)
    (X : ℝ) (hX : 0 < X) : 0 < fixedCuspReflectionScale s c X := by
  have hq₀ := sourceCuspRadialScale_pos 0
  have hq := sourceCuspRadialScale_pos (fixedCuspIndex s)
  have hcn := norm_pos_iff.mpr (ringComplex_ne_zero hc)
  unfold fixedCuspReflectionScale
  positivity

/-- Integral inverse phase at a fixed cusp shape. -/
def fixedCuspInversePhase (s : FixedCuspSector) (c d h : O) : ℂ :=
  tracePhase (-(ringComplex d * ringComplex
    (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h)) /
    (ringComplex traceLambda ^ 4 * ringComplex (3 * c)))

lemma fixedCuspInversePhase_norm (s : FixedCuspSector) (c d h : O) :
    ‖fixedCuspInversePhase s c d h‖ = 1 := tracePhase_norm _

lemma fixedMatrixCusp_reflected_term (M : SL(2, O)) (hc : M 1 0 ≠ 0) (h : O) :
    (fixedMatrixCusp M hc).smoothingMultiplier *
      sourceCuspRadialCoefficient (fixedMatrixCusp M hc).index (fixedMatrixCusp M hc).dualPoint h =
    fixedCuspReflectionScalar (fixedCuspSector M) (M 1 0) *
      fixedCuspRadialArray (fixedCuspSector M) h * star (extendedComplexCharacter (fixedCuspGamma M)) *
      fixedCuspInversePhase (fixedCuspSector M) (M 1 0) (M 1 1) h := by
  rw [fixedMatrixCusp_smoothingMultiplier, fixedMatrixCusp_radialCoefficient,
    sourceCuspIntegralPhaseNumerator_phase _ _ _ _ _ hc]
  unfold fixedCuspReflectionScalar fixedCuspInversePhase
  ring

lemma fixedCuspRadialArray_kernel_norm_summable (s : FixedCuspSector)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (R : ℝ) (hR : 0 < R) :
    Summable (fun h : O => ‖fixedCuspRadialArray s h * paperKernel V (R * sourceCuspRadialLength h)‖) := by
  have hcoeff : Summable (fun h : O => ‖fixedCuspRadialArray s h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [fixedCuspRadialArray_norm, sourceCuspRadialCoefficient_norm, neg_div] using
      sourceCuspRadialCoefficient_weighted_summable (fixedCuspIndex s) 0
  exact paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (fixedCuspRadialArray s) hcoeff V a b ha hs hV R hR

/-- Finite frequency summation commutes with the actual reflected source, retaining its cubic phase. -/
theorem fixedCusp_finite_smoothed_reflection {ι : Type*} [Fintype ι]
    (M : ι → SL(2, O)) (s : FixedCuspSector) (hsector : ∀ i, fixedCuspSector (M i) = s)
    (c : O) (hc : c ≠ 0) (hMc : ∀ i, M i 1 0 = c) (weight : ι → ℂ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0 < X) :
    (∑ i, weight i * ∑' h : O,
      sourceBarRadialCoefficient (ringComplex (M i 0 0) / ringComplex c) h * V (sourceCuspRadialLength h / X)) =
    fixedCuspReflectionScalar s c * ∑' h : O,
      (fixedCuspRadialArray s h * paperKernel V (fixedCuspReflectionScale s c X * sourceCuspRadialLength h)) *
      ∑ i, weight i * star (extendedComplexCharacter (fixedCuspGamma (M i))) *
        fixedCuspInversePhase s c (M i 1 1) h := by
  classical
  have hcn (i) : M i 1 0 ≠ 0 := by rw [hMc]; exact hc
  let A : O → ℂ := fun h => fixedCuspRadialArray s h *
    paperKernel V (fixedCuspReflectionScale s c X * sourceCuspRadialLength h)
  let f : ι → O → ℂ := fun i h => A h *
    (weight i * star (extendedComplexCharacter (fixedCuspGamma (M i))) * fixedCuspInversePhase s c (M i 1 1) h)
  have hA : Summable (fun h => ‖A h‖) := fixedCuspRadialArray_kernel_norm_summable s V a b ha hs hV _
    (fixedCuspReflectionScale_pos s c hc X hX)
  have hf (i) : Summable (f i) := by
    apply Summable.of_norm
    simpa only [f, norm_mul, norm_star, norm_extendedComplexCharacter,
      fixedCuspInversePhase_norm, mul_one] using hA.mul_right ‖weight i‖
  have he (i) : weight i * (∑' h : O,
      sourceBarRadialCoefficient (ringComplex (M i 0 0) / ringComplex c) h * V (sourceCuspRadialLength h / X)) =
      fixedCuspReflectionScalar s c * ∑' h : O, f i h := by
    have hpoint : (fixedMatrixCusp (M i) (hcn i)).point = ringComplex (M i 0 0) / ringComplex c := by
      rw [fixedMatrixCusp_point, hMc]
    rw [← hpoint, (fixedMatrixCusp (M i) (hcn i)).smoothed_reflection V a b ha hs hV X hX]
    simp only [← tsum_mul_left]
    apply tsum_congr
    intro h
    rw [← mul_assoc (fixedMatrixCusp (M i) (hcn i)).smoothingMultiplier,
      fixedMatrixCusp_reflected_term, fixedMatrixCusp_smoothingScale, hsector, hMc]
    dsimp only [f, A, fixedCuspReflectionScale]
    ring
  rw [Finset.sum_congr rfl (fun i _ => he i), ← Finset.mul_sum,
    ← Summable.tsum_finsetSum (fun i _ => hf i)]
  congr 1
  apply tsum_congr
  intro h
  simp only [f, A, Finset.mul_sum]

/-- Prime residue characters form a genuine multiplicative row on Eisenstein integers. -/
def primeCuspRowCharacter {ι : Type*} [Fintype ι] (p : ι → O)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) : O →* ℂ where
  toFun x := ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) x)
  map_one' := by simp only [map_one, Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

lemma fixedThetaTwist_mul (Ψ Φ : O →* ℂ) (h : O) :
    fixedThetaTwist (Ψ * Φ) h = fixedThetaTwist Ψ h * Φ h := by
  by_cases hh : lambda ^ 2 ∣ h - 1
  · simp only [fixedThetaTwist, if_pos hh, MonoidHom.mul_apply, mul_assoc]
  · simp only [fixedThetaTwist, if_neg hh, zero_mul]

/-- Tensor Fourier inversion keeps the local zero frequencies. -/
lemma finiteAdditiveFourier_product_inversion {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    (ψ : ∀ i, AddChar (F i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (φ : ∀ i, F i → ℂ) (x : ∀ i, F i) :
    (∑ h : ∀ i, F i, ∏ i, finiteAdditiveFourierCoeff (ψ i) (φ i) (h i) * ψ i (h i * x i)) =
      ∏ i, φ i (x i) := by
  classical
  let f := fun (i : ι) (h : F i) => finiteAdditiveFourierCoeff (ψ i) (φ i) h * ψ i (h * x i)
  change (∑ h : ∀ i, F i, ∏ i, f i (h i)) = _
  rw [← Fintype.prod_sum f]
  exact Finset.prod_congr rfl (fun i _ => finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i))

lemma primeCuspTranslation_phase {ι : Type*} [Fintype ι] (p t : ι → O)
    (hp : ∀ i, p i ≠ 0) (h : O) :
    tracePhase (-cuspFrequency h * (ringComplex traceLambda ^ 2 * ∑ i, ringComplex (t i) / ringComplex (p i))) =
      ∏ i, residueTraceQuotientChar 1 (p i) (hp i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (t i * h)) := by
  classical
  have he : -cuspFrequency h * (ringComplex traceLambda ^ 2 * ∑ i, ringComplex (t i) / ringComplex (p i)) =
      ∑ i, -cuspFrequency h * ringComplex traceLambda ^ 2 * (ringComplex (t i) / ringComplex (p i)) := by
    rw [← Finset.mul_sum]
    ring
  rw [he, tracePhase_finset_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [residueTraceQuotientChar_phase, one_mul]
  have hs : ringComplex traceLambda ^ 2 = (-3 : ℂ) := by
    simpa only [map_pow, map_neg, map_ofNat] using congrArg ringComplex traceLambda_square
  congr 1
  rw [hs, cuspFrequency, map_mul]
  have hl := ringComplex_ne_zero traceLambda_ne_zero
  have hpi := ringComplex_ne_zero (hp i)
  field_simp

/-- The fixed arithmetic twist and all prime rows have one exact rational-cusp expansion. -/
theorem primeCuspRow_phase_decomposition {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (lift : (∀ i, O ⧸ Ideal.span {p i}) → ι → O)
    (hlift : ∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (lift v i) = v i)
    (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {9 * c})]
    (Ψ : (O ⧸ Ideal.span {c}) →* ℂ) (h : O) :
    (∑ k : O ⧸ Ideal.span {9 * c}, ∑ v : ∀ i, O ⧸ Ideal.span {p i},
      (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) k *
        ∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i)) (χ i) (v i)) *
      tracePhase (-cuspFrequency h * (thetaFourierTranslation (9 * c) k +
        ringComplex traceLambda ^ 2 * ∑ i, ringComplex (lift v i) / ringComplex (p i)))) =
    fixedThetaTwist
      (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom * primeCuspRowCharacter p χ) h := by
  classical
  let ψ := fun i => residueTraceQuotientChar 1 (p i) (hp i)
  have hlocal (v) : tracePhase
      (-cuspFrequency h * (ringComplex traceLambda ^ 2 * ∑ i, ringComplex (lift v i) / ringComplex (p i))) =
      ∏ i, ψ i (v i * Ideal.Quotient.mk (Ideal.span {p i}) h) := by
    rw [primeCuspTranslation_phase p (lift v) hp h]
    simp only [map_mul, hlift, ψ]
  simp_rw [mul_add, AddChar.map_add_eq_mul, hlocal]
  have hsum (k : O ⧸ Ideal.span {9 * c}) :
      (∑ v : ∀ i, O ⧸ Ideal.span {p i},
        (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
            (finiteThetaTwist c Ψ) k * ∏ i, finiteAdditiveFourierCoeff (ψ i) (χ i) (v i)) *
        (tracePhase (-cuspFrequency h * thetaFourierTranslation (9 * c) k) *
          ∏ i, ψ i (v i * Ideal.Quotient.mk (Ideal.span {p i}) h))) =
      (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) k * tracePhase (-cuspFrequency h * thetaFourierTranslation (9 * c) k)) *
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) h) := by
    rw [← finiteAdditiveFourier_product_inversion ψ (fun i => residueTraceQuotientChar_primitive (p i) (hp i))
      (fun i => χ i) (fun i => Ideal.Quotient.mk (Ideal.span {p i}) h), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.prod_mul_distrib]
    ring
  calc
    _ = ∑ k : O ⧸ Ideal.span {9 * c},
        (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) k * tracePhase (-cuspFrequency h * thetaFourierTranslation (9 * c) k)) *
        ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) h) :=
      Finset.sum_congr rfl (fun k _ => hsum k)
    _ = _ := by
      rw [← Finset.sum_mul, thetaFourierTranslation_inversion, finiteThetaTwist_mk, fixedThetaTwist_mul]
      rfl

/-- Any finite additive decomposition acts diagonally on the absolutely convergent smoothed source. -/
lemma sourceBar_smoothed_phase_translation {ι : Type*} [Fintype ι] (z weight : ι → ℂ)
    (W : O → ℂ) (hW : Summable (fun h : O => ‖sourceBarRadialCoefficient 0 h * W h‖)) :
    (∑ i, weight i * ∑' h : O, sourceBarRadialCoefficient (z i) h * W h) =
      ∑' h : O, (∑ i, weight i * tracePhase (-cuspFrequency h * z i)) * sourceBarRadialCoefficient 0 h * W h := by
  let coeff : O → ℂ := fun h => star (sourceBarRadialCoefficient 0 h * W h)
  have hs : Summable (fun h => ‖coeff h‖) := by simpa only [coeff, norm_star] using hW
  have he := conjugate_cuspCharacterSeries_finite_translation coeff hs z weight 0
  simp only [zero_add, mul_zero, AddChar.map_zero_eq_one, mul_one, coeff, star_star] at he
  calc
    _ = ∑ i, weight i * star (cuspCharacterSeries coeff (z i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [conjugate_cuspCharacterSeries]
      apply tsum_congr
      intro h
      rw [sourceBarRadialCoefficient_phase]
      simp only [coeff, star_star]
      ring
    _ = _ := by simpa only [mul_assoc] using he

/-- The completed Gauss sum is the arithmetic twist of the smoothed source derivative. -/
lemma completedT_source_identity (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    completedT Ψ W X = thetaDerivativeScalar⁻¹ *
      ∑' h : O, fixedThetaTwist Ψ h * sourceBarRadialCoefficient 0 h * Vstar W (sourceCuspRadialLength h / X) := by
  have he : thetaRadialDerivativeScalar * completedT Ψ W X = rationalSourceThetaScalar⁻¹ *
      ∑' h : O, fixedThetaTwist Ψ h * sourceBarRadialCoefficient 0 h * Vstar W (sourceCuspRadialLength h / X) := by
    rw [← thetaSmoothedGaussSum_eq_completedT]
    calc
      _ = ∑' h : O, (rationalSourceThetaScalar⁻¹ * star (rationalSourceResidualFourierCoefficient h) *
          fixedThetaTwist Ψ h) *
          (((-2 * Real.pi * Complex.I * star (cuspFrequency h)) / (sourceCuspRadialLength h : ℂ)) *
            Vstar W (sourceCuspRadialLength h / X)) := (fixedThetaTwist_source_tsum Ψ _).symm
      _ = _ := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro h
        rw [sourceBarRadialCoefficient_at_zero]
        ring
  apply mul_left_cancel₀ thetaRadialDerivativeScalar_ne_zero
  rw [he, thetaDerivativeScalar, mul_inv_rev]
  field_simp [thetaRadialDerivativeScalar_ne_zero]

/-- An exact finite phase decomposition reflects the completed Gauss sum through its actual cusps. -/
theorem completedT_finite_phase_reflection {ι : Type*} [Fintype ι]
    (Ψ : O →* ℂ) (d : ι → SourceCuspDatum) (weight : ι → ℂ)
    (hphase : ∀ h : O, (∑ i, weight i * tracePhase (-cuspFrequency h * (d i).point)) = fixedThetaTwist Ψ h)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    completedT Ψ W X = thetaDerivativeScalar⁻¹ * ∑ i, weight i *
      ((d i).smoothingMultiplier * ∑' h : O, sourceCuspRadialCoefficient (d i).index (d i).dualPoint h *
        paperKernel (Vstar W) ((d i).smoothingScale X * sourceCuspRadialLength h)) := by
  have hcoeff : Summable (fun h : O => ‖sourceBarRadialCoefficient 0 h‖ *
      sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
    simpa only [show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num] using
      sourceBarRadialCoefficient_summable 0 2 le_rfl
  have hsum := weighted_compact_test_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceBarRadialCoefficient 0) (3 / 2) hcoeff (Vstar W) a b ha
    (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) X hX
  have he := sourceBar_smoothed_phase_translation (fun i => (d i).point) weight
    (fun h => Vstar W (sourceCuspRadialLength h / X)) hsum
  simp_rw [hphase] at he
  rw [completedT_source_identity, ← he]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [(d i).smoothed_reflection (Vstar W) a b ha
    (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) X hX]

/-- Tensor Fourier inversion gives the exact completed reflection before active-prime regrouping. -/
theorem completedT_primeCuspRow_reflection {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (lift : (∀ i, O ⧸ Ideal.span {p i}) → ι → O)
    (hlift : ∀ v i, Ideal.Quotient.mk (Ideal.span {p i}) (lift v i) = v i)
    (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {9 * c})]
    (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) × (∀ i, O ⧸ Ideal.span {p i}) → SourceCuspDatum)
    (hd : ∀ k v, (d (k, v)).point = thetaFourierTranslation (9 * c) k +
      ringComplex traceLambda ^ 2 * ∑ i, ringComplex (lift v i) / ringComplex (p i))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom * primeCuspRowCharacter p χ) W X =
      thetaDerivativeScalar⁻¹ * ∑ k : O ⧸ Ideal.span {9 * c}, ∑ v : ∀ i, O ⧸ Ideal.span {p i},
        (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
            (finiteThetaTwist c Ψ) k *
          ∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i)) (χ i) (v i)) *
        ((d (k, v)).smoothingMultiplier * ∑' h : O,
          sourceCuspRadialCoefficient (d (k, v)).index (d (k, v)).dualPoint h *
          paperKernel (Vstar W) ((d (k, v)).smoothingScale X * sourceCuspRadialLength h)) := by
  let weight := fun q : (O ⧸ Ideal.span {9 * c}) × (∀ i, O ⧸ Ideal.span {p i}) =>
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c Ψ) q.1 *
    ∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i)) (χ i) (q.2 i)
  have hphase (h : O) : (∑ q, weight q * tracePhase (-cuspFrequency h * (d q).point)) =
      fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom * primeCuspRowCharacter p χ) h := by
    rw [Fintype.sum_prod_type]
    simp_rw [hd]
    exact primeCuspRow_phase_decomposition p hp χ lift hlift c hc Ψ h
  simpa only [weight, Fintype.sum_prod_type] using
    completedT_finite_phase_reflection _ d weight hphase W a b ha hs hW X hX

lemma assembleUnitFrequencies_prod {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, Field (F i)] {A : Type*} [CommMonoid A]
    (s : Finset ι) (u : ∀ i : s, (F i.val)ˣ) (f : ∀ i, F i → A) :
    (∏ i, f i (assembleUnitFrequencies s u i)) =
      (∏ i : s, f i.val (u i)) * ∏ i : {i // i ∉ s}, f i.val 0 := by
  classical
  rw [← Finset.prod_mul_prod_compl s (fun i => f i (assembleUnitFrequencies s u i)),
    Finset.prod_subtype (F := inferInstanceAs (Fintype s)) s (fun _ => Iff.rfl),
    Finset.prod_subtype (F := inferInstanceAs (Fintype {i // i ∉ s})) sᶜ (fun _ => Finset.mem_compl)]
  apply congrArg₂ (· * ·)
  · exact Finset.prod_congr rfl (fun i _ => by simp only [assembleUnitFrequencies, dif_pos i.property])
  · exact Finset.prod_congr rfl (fun i _ => by simp only [assembleUnitFrequencies, dif_neg i.property])

/-- Fourier inversion splits into unit-frequency sums and the exact inactive-prime factors. -/
theorem finiteAdditiveFourier_active_inversion {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (ψ : ∀ i, AddChar (F i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (φ : ∀ i, F i → ℂ) (x : ∀ i, F i) :
    (∏ i, φ i (x i)) = ∑ s : Finset ι,
      (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) 0) *
      ∑ u : ∀ i : s, (F i.val)ˣ, ∏ i : s,
        finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (u i) * ψ i.val ((u i : F i.val) * x i.val) := by
  classical
  rw [← finiteAdditiveFourier_product_inversion ψ hψ φ x, finite_frequency_sum_strata]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [assembleUnitFrequencies_prod s u (fun i y =>
    finiteAdditiveFourierCoeff (ψ i) (φ i) y * ψ i (y * x i))]
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
  ring

/-- The inactive factor vanishes unless every omitted prime carries the trivial character. -/
lemma finiteAdditiveFourier_inactive_vanishes {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (ψ : ∀ i, AddChar (F i) ℂ)
    (s : Finset ι) (k : ι) (hk : k ∉ s) (hχ : χ k ≠ 1) :
    (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (ψ i.val) (χ i.val) 0) = 0 := by
  classical
  apply Finset.prod_eq_zero (Finset.mem_univ ⟨k, hk⟩)
  rw [finiteAdditiveFourierCoeff_mulChar_zero, if_neg hχ]

/-- Every surviving inactive prime contributes its exact coprimality density. -/
lemma finiteAdditiveFourier_inactive_density {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (χ : ∀ i, MulChar (F i) ℂ) (ψ : ∀ i, AddChar (F i) ℂ)
    (s : Finset ι) (hχ : ∀ i, i ∉ s → χ i = 1) :
    (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (ψ i.val) (χ i.val) 0) =
      ∏ i : {i // i ∉ s}, (1 - (Fintype.card (F i.val) : ℂ)⁻¹) := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  rw [finiteAdditiveFourierCoeff_mulChar_zero, if_pos (hχ i.val i.property),
    Nat.card_eq_fintype_card, Fintype.card_units,
    Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos), Nat.cast_one]
  have hq : (Fintype.card (F i.val) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma finiteMulChar_unit_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (u : Fˣ) : ‖χ u‖ = 1 :=
  Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

/-- At odd good primes, the sextic character has all six distinct powers. -/
lemma complexSexticChar_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (j : ℕ) (hj : j < 6) (hj0 : j ≠ 0) : complexSexticChar P hg ^ j ≠ 1 := by
  let χ := complexSexticChar P hg
  have hχ : χ ≠ 1 := complexSexticChar_ne_one P hg
  have h2 : χ ^ 2 ≠ 1 := by
    rw [(complexSexticChar_powers P hg).1]
    exact complexCubicChar_ne_one P hg
  have h3 : χ ^ 3 ≠ 1 := by
    rw [(complexSexticChar_powers P hg).2.1]
    exact complexQuadraticChar_ne_one P hchar
  have h6 : χ ^ 6 = 1 := (complexSexticChar_powers P hg).2.2
  change χ ^ j ≠ 1
  interval_cases j
  · exact False.elim (hj0 rfl)
  · simpa only [pow_one] using hχ
  · exact h2
  · exact h3
  · intro h4
    apply h2
    have he : χ ^ 2 = χ ^ 6 * (χ ^ 4)⁻¹ := by group
    rw [he, h6, h4, inv_one, one_mul]
  · intro h5
    apply hχ
    have he : χ = χ ^ 6 * (χ ^ 5)⁻¹ := by group
    rw [he, h6, h5, inv_one, one_mul]

/-- Every nonexceptional local reflection is its predicted multiplicative output character. -/
lemma finiteReflectionGauss_nonexceptional {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (hj : χ ^ (j + 2) ≠ 1) (x : F) :
    finiteReflectionGauss χ ψ j x =
      ((Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) * gaussSum (χ ^ (j + 2)) ψ) *
      (χ ^ (j + 2))⁻¹ x := by
  rw [finiteReflectionGauss_product, finiteGauss_mulShift_all _ _ hj]
  ring

/-- The trivial input row pays exactly one square root of the residue-field size. -/
lemma finiteReflectionGauss_trivial_phase_norm_sq {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (hχ2 : χ ^ 2 ≠ 1) :
    ‖(Fintype.card F : ℂ)⁻¹ * gaussSum (1 : MulChar F ℂ) (ψ.mulShift (-1)) * gaussSum (χ ^ 2) ψ‖ ^ 2 =
      (Fintype.card F : ℝ)⁻¹ := by
  have hneg : ψ.mulShift (-1) ≠ 1 := hψ (neg_ne_zero.mpr one_ne_zero)
  have hn : ‖gaussSum (χ ^ 2) ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, ArithmeticEffectivityTheory.normSq_gaussSum_eq_card hχ2 hψ]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [gaussSum_one_left hneg]
  simp only [norm_mul, norm_inv, Complex.norm_natCast, norm_neg, norm_one, mul_one, mul_pow, hn]
  field_simp

/-- The fourth-power exceptional divisor bracket has the same square-root normalization. -/
lemma finiteReflectionGauss_fourth_phase_norm_sq {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (hχ4 : χ ^ 4 ≠ 1) :
    ‖(Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1))‖ ^ 2 =
      (Fintype.card F : ℝ)⁻¹ := by
  have hneg : (ψ.mulShift (-1)).IsPrimitive := by
    intro a ha
    rw [AddChar.mulShift_mulShift]
    exact hψ (mul_ne_zero (neg_ne_zero.mpr one_ne_zero) ha)
  have hn : ‖gaussSum (χ ^ 4) (ψ.mulShift (-1))‖ ^ 2 = (Fintype.card F : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, ArithmeticEffectivityTheory.normSq_gaussSum_eq_card hχ4 hneg]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, hn]
  field_simp

/-- Local unit scales change a reflected sextic row only by one fixed phase of norm one. -/
theorem finiteReflectionGauss_scaled_quadratic_family
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (O ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (σ ε : ∀ i, (O ⧸ P i)ˣ) :
    ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ x : ∀ i, O ⧸ P i,
      (∏ i, ((complexSexticChar (P i) (hg i))⁻¹ ^ 2) (σ i) *
        finiteReflectionGauss (complexSexticChar (P i) (hg i)) (ψ i) 1 ((ε i : O ⧸ P i) * x i)) =
      η * ∏ i, complexQuadraticChar (P i) (x i) := by
  classical
  choose η hηnorm hη using fun i =>
    finiteReflectionGauss_actual_quadratic (P i) (hg i) (hchar i) (ψ i) (hψ i)
  refine ⟨∏ i, (((complexSexticChar (P i) (hg i))⁻¹ ^ 2) (σ i) * η i *
    complexQuadraticChar (P i) (ε i)), ?_, ?_⟩
  · simp only [norm_prod, norm_mul, finiteMulChar_unit_norm, hηnorm, one_mul, Finset.prod_const_one]
  · intro x
    simp_rw [hη, map_mul]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)

/-- Each active prime set may choose its own congruence-controlled unit lifts. -/
theorem primeCuspRow_active_phase_decomposition {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {9 * c})]
    (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (lift : (O ⧸ Ideal.span {9 * c}) → ∀ s : Finset ι,
      (∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ) → s → O)
    (hlift : ∀ k s v i, Ideal.Quotient.mk (Ideal.span {p i.val}) (lift k s v i) =
      (v i : O ⧸ Ideal.span {p i.val})) (h : O) :
    (∑ k : O ⧸ Ideal.span {9 * c}, ∑ s : Finset ι,
      ∑ v : ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ,
      (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) k *
        (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (χ i.val) 0) *
        ∏ i : s, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (χ i.val) (v i)) *
      tracePhase (-cuspFrequency h * (thetaFourierTranslation (9 * c) k +
        ringComplex traceLambda ^ 2 * ∑ i : s, ringComplex (lift k s v i) / ringComplex (p i.val)))) =
    fixedThetaTwist
      (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom * primeCuspRowCharacter p χ) h := by
  classical
  let ψ := fun i => residueTraceQuotientChar 1 (p i) (hp i)
  let inactive := fun s : Finset ι => ∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (ψ i.val) (χ i.val) 0
  let active := fun (s : Finset ι) (v : ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ) =>
    ∏ i : s, finiteAdditiveFourierCoeff (ψ i.val) (χ i.val) (v i)
  let shift := fun (k : O ⧸ Ideal.span {9 * c}) (s : Finset ι) (v : ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ) =>
    ringComplex traceLambda ^ 2 * ∑ i : s, ringComplex (lift k s v i) / ringComplex (p i.val)
  have hlocal (k) (s) (v) : tracePhase (-cuspFrequency h * shift k s v) =
      ∏ i : s, ψ i.val ((v i : O ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk (Ideal.span {p i.val}) h) := by
    change tracePhase (-cuspFrequency h * (ringComplex traceLambda ^ 2 *
      ∑ i : s, ringComplex (lift k s v i) / ringComplex (p i.val))) = _
    rw [primeCuspTranslation_phase (fun i : s => p i.val) (lift k s v) (fun i => hp i.val) h]
    simp only [map_mul, hlift, ψ]
  have hsum (k : O ⧸ Ideal.span {9 * c}) : (∑ s : Finset ι, inactive s *
      ∑ v : ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ, active s v * tracePhase (-cuspFrequency h * shift k s v)) =
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) h) := by
    rw [finiteAdditiveFourier_active_inversion ψ (fun i => residueTraceQuotientChar_primitive (p i) (hp i))
      (fun i => χ i) (fun i => Ideal.Quotient.mk (Ideal.span {p i}) h)]
    apply Finset.sum_congr rfl
    intro s hs
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [hlocal k, Finset.prod_mul_distrib]
  let base := finiteAdditiveFourierCoeff
    (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ)
  calc
    _ = ∑ k : O ⧸ Ideal.span {9 * c},
        (base k * tracePhase (-cuspFrequency h * thetaFourierTranslation (9 * c) k)) *
        (∑ s : Finset ι, inactive s *
          ∑ v : ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ, active s v * tracePhase (-cuspFrequency h * shift k s v)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_add, AddChar.map_add_eq_mul]
      dsimp only [base, inactive, active, shift, ψ]
      ring
    _ = _ := by
      simp_rw [hsum]
      rw [← Finset.sum_mul]
      dsimp only [base]
      rw [thetaFourierTranslation_inversion, finiteThetaTwist_mk, fixedThetaTwist_mul]
      rfl

/-- The completed row reflects stratum by stratum, with zero local frequencies kept as density factors. -/
theorem completedT_active_primeCusp_reflection {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {9 * c})]
    (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (lift : (O ⧸ Ideal.span {9 * c}) → ∀ s : Finset ι,
      (∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ) → s → O)
    (hlift : ∀ k s v i, Ideal.Quotient.mk (Ideal.span {p i.val}) (lift k s v i) =
      (v i : O ⧸ Ideal.span {p i.val}))
    (d : (O ⧸ Ideal.span {9 * c}) × (Σ s : Finset ι, ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ) → SourceCuspDatum)
    (hd : ∀ k s v, (d (k, ⟨s, v⟩)).point = thetaFourierTranslation (9 * c) k +
      ringComplex traceLambda ^ 2 * ∑ i : s, ringComplex (lift k s v i) / ringComplex (p i.val))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    completedT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom * primeCuspRowCharacter p χ) W X =
      thetaDerivativeScalar⁻¹ * ∑ k : O ⧸ Ideal.span {9 * c}, ∑ s : Finset ι,
        ∑ v : ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ,
        (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
            (finiteThetaTwist c Ψ) k *
          (∏ i : {i // i ∉ s}, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (χ i.val) 0) *
          ∏ i : s, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (χ i.val) (v i)) *
        ((d (k, ⟨s, v⟩)).smoothingMultiplier * ∑' h : O,
          sourceCuspRadialCoefficient (d (k, ⟨s, v⟩)).index (d (k, ⟨s, v⟩)).dualPoint h *
          paperKernel (Vstar W) ((d (k, ⟨s, v⟩)).smoothingScale X * sourceCuspRadialLength h)) := by
  classical
  let weight := fun q : (O ⧸ Ideal.span {9 * c}) ×
      (Σ s : Finset ι, ∀ i : s, (O ⧸ Ideal.span {p i.val})ˣ) =>
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c Ψ) q.1 *
    (∏ i : {i // i ∉ q.2.1}, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (χ i.val) 0) *
    ∏ i : q.2.1, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i.val) (hp i.val)) (χ i.val) (q.2.2 i)
  have hphase (h : O) : (∑ q, weight q * tracePhase (-cuspFrequency h * (d q).point)) =
      fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom * primeCuspRowCharacter p χ) h := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_sigma, hd]
    exact primeCuspRow_active_phase_decomposition p hp χ c hc Ψ lift hlift h
  simpa only [weight, Fintype.sum_prod_type, Fintype.sum_sigma] using
    completedT_finite_phase_reflection _ d weight hphase W a b ha hs hW X hX

lemma exists_unit_primary_of_not_lambda_dvd (x : O) (hx : ¬ lambda ∣ x) :
    ∃ u : Oˣ, lambda ^ 2 ∣ (u : O) * x - 1 := by
  have hx0 : x ≠ 0 := by intro hz; exact hx (hz ▸ dvd_zero lambda)
  obtain ⟨u, m, I, hI, he⟩ := exists_unit_lambda_primary_factor x hx0
  have hm : m = 0 := by
    by_contra hm
    apply hx
    rw [he]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self lambda hm) (u : O)) _
  refine ⟨u⁻¹, ?_⟩
  rw [he, hm, pow_zero, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
  exact (primaryIdealGenerator_spec I hI).2

lemma integralMatrix_cusp_denominator_dvd (M : SL(2, O)) (a c : O) (hc : c ≠ 0)
    (hM : M 1 0 ≠ 0)
    (hratio : ringComplex (M 0 0) / ringComplex (M 1 0) = ringComplex a / ringComplex c) :
    M 1 0 ∣ c := by
  have he : M 0 0 * c = a * M 1 0 := by
    apply ringComplex_injective
    simpa only [map_mul] using
      (div_eq_div_iff (ringComplex_ne_zero hM) (ringComplex_ne_zero hc)).mp hratio
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.property
  refine ⟨a * M 1 1 - M 0 1 * c, ?_⟩
  linear_combination -(c * hdet) + M 1 1 * he

/-- Every rational Eisenstein cusp has primitive coordinates with one primary entry and denominator dividing the original. -/
theorem exists_primary_cusp_coordinates (a c : O) (hc : c ≠ 0) :
    ∃ a₀ c₀ : O, c₀ ≠ 0 ∧ IsCoprime a₀ c₀ ∧ c₀ ∣ c ∧
      (lambda ^ 2 ∣ a₀ - 1 ∨ lambda ^ 2 ∣ c₀ - 1) ∧
      ringComplex a₀ / ringComplex c₀ = ringComplex a / ringComplex c := by
  obtain ⟨M, hMc, hratio⟩ := exists_integral_matrix_cusp_ratio a c hc
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.property
  have hprimitive : IsCoprime (M 0 0) (M 1 0) := ⟨M 1 1, -M 0 1, by linear_combination hdet⟩
  have hdiv := integralMatrix_cusp_denominator_dvd M a c hc hMc hratio
  have hu : ∃ u : Oˣ, lambda ^ 2 ∣ (u : O) * M 0 0 - 1 ∨ lambda ^ 2 ∣ (u : O) * M 1 0 - 1 := by
    by_cases ha : lambda ∣ M 0 0
    · have hcn : ¬ lambda ∣ M 1 0 := by
        intro hcm
        apply residue_lambda_prime.2.1
        apply isUnit_of_dvd_one
        rw [← hdet]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hcm _)
      obtain ⟨u, hu⟩ := exists_unit_primary_of_not_lambda_dvd (M 1 0) hcn
      exact ⟨u, Or.inr hu⟩
    · obtain ⟨u, hu⟩ := exists_unit_primary_of_not_lambda_dvd (M 0 0) ha
      exact ⟨u, Or.inl hu⟩
  obtain ⟨u, hu⟩ := hu
  refine ⟨(u : O) * M 0 0, (u : O) * M 1 0, mul_ne_zero u.ne_zero hMc, ?_, ?_, hu, ?_⟩
  · refine ⟨(↑u⁻¹ : O) * M 1 1, -(↑u⁻¹ : O) * M 0 1, ?_⟩
    calc
      _ = ((↑u⁻¹ : O) * (u : O)) * (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by ring
      _ = 1 := by rw [Units.inv_mul, hdet, one_mul]
  · obtain ⟨k, hk⟩ := hdiv
    refine ⟨(↑u⁻¹ : O) * k, ?_⟩
    rw [hk]
    calc
      M 1 0 * k = ((u : O) * (↑u⁻¹ : O)) * (M 1 0 * k) := by rw [Units.mul_inv, one_mul]
      _ = _ := by ring
  · rw [map_mul, map_mul, mul_div_mul_left _ _ (ringComplex_ne_zero u.ne_zero)]
    exact hratio

/-- The smoothed source attached to the unit frequencies of one active prime set. -/
def cuspUnitSourceSum {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : O)
    (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O)) (j : ι → ℕ) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ v : ∀ i, (O ⧸ Ideal.span {p i})ˣ,
    (∏ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i))
      (complexSexticChar (Ideal.span {p i}) (hg i) ^ j i : MulChar (O ⧸ Ideal.span {p i}) ℂ) (v i)) *
    ∑' h : O, sourceBarRadialCoefficient (ringComplex (M v 0 0) / ringComplex (c * ∏ i, p i)) h *
      V (sourceCuspRadialLength h / X)

/-- The fixed cusp array with the exact local reflected characters. -/
def nativeCuspStratumKernel {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (s : FixedCuspSector) (c d U : O) (κ : ℂ)
    (σ ε : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (j : ι → ℕ) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedCuspReflectionScalar s (c * ∏ i, p i) * ∑' h : O,
    (fixedCuspRadialArray s h *
      paperKernel V (fixedCuspReflectionScale s (c * ∏ i, p i) X * sourceCuspRadialLength h)) *
    ((star κ * tracePhase (-(ringComplex d * ringComplex U * ringComplex
        (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h)) /
        (ringComplex traceLambda ^ 4 * ringComplex (3 * c)))) *
      cuspLocalReflectedProduct p hp hg σ ε j
        (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h))

lemma cuspUnitSourceSum_reflection {ι : Type*} [Fintype ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (c : O) (hc : c ≠ 0)
    (M : (∀ i, (O ⧸ Ideal.span {p i})ˣ) → SL(2, O))
    (s : FixedCuspSector) (hsector : ∀ v, fixedCuspSector (M v) = s)
    (hMc : ∀ v, M v 1 0 = c * ∏ i, p i) (j : ι → ℕ)
    (V : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hs : Function.support V ⊆ Set.Icc A B) (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0 < X) :
    cuspUnitSourceSum p hp hg c M j V X =
      fixedCuspReflectionScalar s (c * ∏ i, p i) * ∑' h : O,
        (fixedCuspRadialArray s h *
          paperKernel V (fixedCuspReflectionScale s (c * ∏ i, p i) X * sourceCuspRadialLength h)) *
        cuspUnitFrequencySum p hp hg c M j
          (sourceCuspIntegralPhaseNumerator (fixedCuspIndex s) (fixedCuspTriangular s 0 0) h) := by
  have hcR : c * ∏ i, p i ≠ 0 := mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  rw [cuspUnitSourceSum, fixedCusp_finite_smoothed_reflection M s hsector _ hcR hMc _ V A B hA hs hV X hX]
  congr 1
  apply tsum_congr
  intro h
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp only [cuspUnitFrequencySum, fixedCuspInversePhase, map_mul, mul_assoc]

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
