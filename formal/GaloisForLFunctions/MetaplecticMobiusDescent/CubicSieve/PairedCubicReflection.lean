/-
Paired cubic reflection adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CubicSieveNorm

/-!
# Paired cubic reflection

Row characters and the cubic Gauss factor `gaussTwo`; reciprocity cancels the cross factors in
the paired Gauss sum; smoothed coprime recurrences and the common-factor frequency cost.
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
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson.CanonicalQuadraticSieve  DivisorBlockCauchy
noncomputable section
local notation "O" => Eisenstein.O

lemma gcdPool_subset_columnDivisorPool {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, cols j ≠ 0) :
    gcdPool cols ⊆ columnDivisorPool cols := by
  intro D hD
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact mem_columnDivisorPool_of_dvd cols hc j _ (gcd_dvd_left _ _)

lemma descendedCoefficient_norm_le {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (d : O) (j : n) :
    ‖descendedCoefficient D cols a d j‖ ≤ ‖if D ∣ cols j then a j else 0‖ := by
  unfold descendedCoefficient
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (elementCharacter_norm_le_one _ (totalQuotient_cubic_admissible D _ (hc j)).2 d)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem descended_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
      ∑ j, ‖descendedCoefficient D cols a (cubicIdealGenerator E) j‖^2) ≤
        (divisorConstant ε hε * N^ε)^2 * ∑ j, ‖a j‖^2 := by
  have hc0 (j : n) : cols j ≠ 0 := primaryIdealGenerator_ne_zero_ideal _ (hc j).2
  let B := divisorConstant ε hε * N^ε
  have hB : 0 ≤ B := mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg hN0 _)
  have hcard (D : Ideal O) (hD : D ∈ columnDivisorPool cols) :
      ((idealDivisors D).card : ℝ) ≤ B := by
    have hd := columnDivisorPool_norm_bounds cols hc0 N hN D hD
    have hd0 : D ≠ 0 := by
      intro he
      have hh := hd.1
      norm_num [he] at hh
    exact ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 D hd0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hd.2 hε.le)
        (divisorConstant_pos ε hε).le)
  calc
    _ ≤ ∑ D ∈ columnDivisorPool cols, B * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ ∑ E ∈ idealDivisors D, ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          apply Finset.sum_le_sum
          intro E hE
          exact Finset.sum_le_sum (fun j hj => pow_le_pow_left₀ (norm_nonneg _)
            (descendedCoefficient_norm_le D cols hc a (cubicIdealGenerator E) j) 2)
        _ = ((idealDivisors D).card : ℝ) * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD) (by positivity)
    _ = B * (∑ D ∈ columnDivisorPool cols, ∑ j, ‖if D ∣ cols j then a j else 0‖^2) := by
      rw [Finset.mul_sum]
    _ ≤ B * (B * ∑ j, ‖a j‖^2) := mul_le_mul_of_nonneg_left
      (divisor_mask_energy_small_power ε hε _ cols hc0 N hN a) hB
    _ = _ := by dsimp [B]; ring

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve

/-- Cubic Gauss factor with the fixed trace character. -/
def gaussTwo (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) : ℂ :=
  residueRowGauss (primaryIdealGenerator I) hI (cubicRow I) /
    (‖ringComplex (primaryIdealGenerator I)‖ : ℂ)

lemma cubicRow_congr (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (x y : O) (h : primaryIdealGenerator I ∣ x-y) : cubicRow I x = cubicRow I y := by
  apply congrArg ringComplex
  apply idealSymbol_congr
  rw [←(primaryIdealGenerator_spec I hI).1]
  exact Ideal.mem_span_singleton.mpr h

lemma cubicRow_neg_one (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    cubicRow I (-1) = 1 := by
  have h2 : cubicRow I (-1)^2 = 1 := by
    change elementCharacter I hI (-1)^2 = 1
    rw [←map_pow]
    norm_num
  have h4 := idealSymbol_fourth I (-1)
  change cubicRow I (-1)^4 = cubicRow I (-1) at h4
  rw [show (4 : ℕ)=2*2 by decide,pow_mul,h2,one_pow] at h4
  exact h4.symm

abbrev rowPrime (I : CubicIdeal) (P : idealSupport I) : O := primeGenerator P.val
abbrev rowCharacter (I : CubicIdeal) (P : idealSupport I) :
    MulChar (O ⧸ Ideal.span {rowPrime I P}) ℂ :=
  complexCubicChar _ (primeGenerator_good P.val)

lemma rowPrime_ne_zero (I : CubicIdeal) (P : idealSupport I) : rowPrime I P ≠ 0 :=
  primeGenerator_ne_zero P.val
lemma rowPrime_injective (I : CubicIdeal) :
    Function.Injective (fun P : idealSupport I => Ideal.span {rowPrime I P}) :=
  primeGenerator_span_injective.comp Subtype.val_injective
lemma rowCharacter_nonprincipal (I : CubicIdeal) (P : idealSupport I) : rowCharacter I P ≠ 1 :=
  complexCubicChar_ne_one _ (primeGenerator_good P.val)
lemma rowPrime_product (I : CubicIdeal) :
    (∏ P : idealSupport I, rowPrime I P) = primaryIdealGenerator I.val := by
  rw [Finset.prod_coe_sort]
  exact idealSupport_product I
lemma rowCharacter_eq (I : CubicIdeal) (z : O) :
    primeCuspRowCharacter (rowPrime I) (rowCharacter I) z = cubicRow I.val z := by
  rw [show cubicRow I.val z = primeSubsetRow primeGenerator
    (fun P => complexCubicChar (Ideal.span {primeGenerator P}) (primeGenerator_good P))
    (idealSupport I) z from idealSymbol_eq_primeSubsetRow I z]
  change (∏ P : idealSupport I, complexCubicChar (Ideal.span {primeGenerator P.val})
    (primeGenerator_good P.val) (Ideal.Quotient.mk _ z)) = _
  exact Finset.prod_coe_sort (idealSupport I)
    (fun P : CubicPrime => complexCubicChar (Ideal.span {primeGenerator P})
      (primeGenerator_good P) (Ideal.Quotient.mk _ z))

lemma rowCharacter_inverse_eq (I : CubicIdeal) (z : O) :
    primeCuspRowCharacter (rowPrime I) (fun P => (rowCharacter I P)⁻¹) z =
      star (cubicRow I.val z) := by
  rw [←rowCharacter_eq I z]
  simp only [primeCuspRowCharacter,MonoidHom.coe_mk,OneHom.coe_mk,star_prod,
    MulChar.star_apply']

lemma rowGauss_eq (I : CubicIdeal) :
    primeRowTraceGauss (rowPrime I) (rowPrime_ne_zero I) (rowCharacter I) =
      residueRowGauss (primaryIdealGenerator I.val) I.property.2 (cubicRow I.val) := by
  simp only [primeRowTraceGauss_eq_residueRowGauss, rowPrime_product]
  exact congrArg (residueRowGauss _ _) (funext (rowCharacter_eq I))

theorem gaussTwo_norm_one (I : Ideal O) (hI : Admissible I) : ‖gaussTwo I hI.2‖ = 1 := by
  have h := (prime_row_trace_poisson (rowPrime ⟨I,hI⟩) (rowPrime_ne_zero ⟨I,hI⟩)
    (rowPrime_injective ⟨I,hI⟩) (rowCharacter ⟨I,hI⟩) (rowCharacter_nonprincipal ⟨I,hI⟩)).1
  rw [rowGauss_eq,rowPrime_product] at h
  have hn := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  rw [gaussTwo,norm_div,hn,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero hI.2))

lemma cubicRowGauss_star (I : Ideal O) (hI : Admissible I) :
    residueRowGauss (primaryIdealGenerator I) hI.2 (fun z => star (cubicRow I z)) =
      star (residueRowGauss (primaryIdealGenerator I) hI.2 (cubicRow I)) := by
  have h := primeRowTraceGauss_inverse (rowPrime ⟨I,hI⟩) (rowPrime_ne_zero ⟨I,hI⟩)
    (rowPrime_injective ⟨I,hI⟩) (rowCharacter ⟨I,hI⟩)
  simp only [rowCharacter_eq,cubicRow_neg_one I hI.2,one_mul,rowGauss_eq,
    primeRowTraceGauss_eq_residueRowGauss,rowPrime_product] at h
  rw [show (primeCuspRowCharacter (rowPrime ⟨I,hI⟩) (fun i => (rowCharacter ⟨I,hI⟩ i)⁻¹) : O → ℂ) =
    (fun z => star (cubicRow I z)) from funext (rowCharacter_inverse_eq ⟨I,hI⟩),
    show (primeCuspRowCharacter (rowPrime ⟨I,hI⟩) (rowCharacter ⟨I,hI⟩) : O → ℂ) =
    cubicRow I from funext (rowCharacter_eq ⟨I,hI⟩)] at h
  exact h

end CubicSieve
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve

lemma rowPrime_contains (I : CubicIdeal) (P : idealSupport I) :
    I.val ≤ Ideal.span {rowPrime I P} := by
  rw [primeGenerator_span,←idealSupport_ideal_product I]
  exact Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P : CubicPrime => P.val) P.property)

abbrev pairRowPrime (I J : CubicIdeal) : idealSupport I ⊕ idealSupport J → O :=
  Sum.elim (rowPrime I) (rowPrime J)
instance pairRowPrime_maximal (I J : CubicIdeal) (P : idealSupport I ⊕ idealSupport J) :
    (Ideal.span {pairRowPrime I J P}).IsMaximal := by
  cases P with
  | inl P => exact primeGeneratorMaximal P.val
  | inr P => exact primeGeneratorMaximal P.val
lemma pairRowPrime_ne_zero (I J : CubicIdeal) (P : idealSupport I ⊕ idealSupport J) :
    pairRowPrime I J P ≠ 0 := by
  cases P with
  | inl P => exact rowPrime_ne_zero I P
  | inr P => exact rowPrime_ne_zero J P
lemma pairRowPrime_product (I J : CubicIdeal) :
    (∏ P, pairRowPrime I J P) = primaryIdealGenerator I.val * primaryIdealGenerator J.val := by
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (rowPrime_product I) (rowPrime_product J)

lemma pairRowPrime_injective (I J : CubicIdeal) (hcop : IsCoprime I.val J.val) :
    Function.Injective (fun P => Ideal.span {pairRowPrime I J P}) := by
  have hcross (P : idealSupport I) (Q : idealSupport J) :
      Ideal.span {rowPrime I P} ≠ Ideal.span {rowPrime J Q} := by
    intro he
    have ht : I.val ⊔ J.val ≤ Ideal.span {rowPrime I P} :=
      sup_le (rowPrime_contains I P) (he ▸ rowPrime_contains J Q)
    rw [hcop.sup_eq] at ht
    exact (inferInstance : (Ideal.span {rowPrime I P}).IsMaximal).ne_top (top_unique ht)
  intro P Q he
  cases P with
  | inl P => cases Q with
    | inl Q => exact congrArg Sum.inl (rowPrime_injective I he)
    | inr Q => exact (hcross P Q he).elim
  | inr P => cases Q with
    | inl Q => exact (hcross Q P he.symm).elim
    | inr Q => exact congrArg Sum.inr (rowPrime_injective J he)

def pairRowCharacter (I J : CubicIdeal) (P : idealSupport I ⊕ idealSupport J) :
    MulChar (O ⧸ Ideal.span {pairRowPrime I J P}) ℂ :=
  match P with
  | Sum.inl P => (rowCharacter I P)⁻¹
  | Sum.inr P => rowCharacter J P
lemma pairRowCharacter_nonprincipal (I J : CubicIdeal) (P : idealSupport I ⊕ idealSupport J) :
    pairRowCharacter I J P ≠ 1 := by
  cases P with
  | inl P => exact inv_ne_one.mpr (rowCharacter_nonprincipal I P)
  | inr P => exact rowCharacter_nonprincipal J P
lemma pairRowCharacter_eq (I J : CubicIdeal) (z : O) :
    primeCuspRowCharacter (pairRowPrime I J) (pairRowCharacter I J) z =
      star (cubicRow I.val z) * cubicRow J.val z := by
  change (∏ P, pairRowCharacter I J P (Ideal.Quotient.mk _ z)) = _
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (rowCharacter_inverse_eq I z) (rowCharacter_eq J z)
lemma pairRowCharacter_inverse_eq (I J : CubicIdeal) (z : O) :
    primeCuspRowCharacter (pairRowPrime I J) (fun P => (pairRowCharacter I J P)⁻¹) z =
      cubicRow I.val z * star (cubicRow J.val z) := by
  change (∏ P, (pairRowCharacter I J P)⁻¹ (Ideal.Quotient.mk _ z)) = _
  rw [Fintype.prod_sum_type]
  change primeCuspRowCharacter (rowPrime I) (fun P => ((rowCharacter I P)⁻¹)⁻¹) z *
    primeCuspRowCharacter (rowPrime J) (fun P => (rowCharacter J P)⁻¹) z = _
  simp only [inv_inv,rowCharacter_eq,rowCharacter_inverse_eq]

lemma primary_generators_coprime (I J : CubicIdeal) (h : IsCoprime I.val J.val) :
    IsCoprime (primaryIdealGenerator I.val) (primaryIdealGenerator J.val) := by
  have hmem : (1 : O) ∈ I.val ⊔ J.val := by rw [h.sup_eq]; trivial
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hmem
  rw [←(primaryIdealGenerator_spec I.val I.property.2).1] at hx
  rw [←(primaryIdealGenerator_spec J.val J.property.2).1] at hy
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨a,b,?_⟩
  rw [ha,hb] at hxy
  simpa only [mul_comm] using hxy

/-- Reciprocity cancels the cross factors in the paired Gauss sum. -/
lemma pairRowGauss_separation (I J : CubicIdeal) (hcop : IsCoprime I.val J.val) :
    primeRowTraceGauss (pairRowPrime I J) (pairRowPrime_ne_zero I J) (pairRowCharacter I J) =
      star (residueRowGauss (primaryIdealGenerator I.val) I.property.2 (cubicRow I.val)) *
        residueRowGauss (primaryIdealGenerator J.val) J.property.2 (cubicRow J.val) := by
  simp only [primeRowTraceGauss_eq_residueRowGauss,pairRowPrime_product]
  rw [show (primeCuspRowCharacter (pairRowPrime I J) (pairRowCharacter I J) : O → ℂ) =
    (fun z => star (cubicRow I.val z) * cubicRow J.val z) from funext (pairRowCharacter_eq I J)]
  have hmul := residueRowGauss_mul _ _ I.property.2 J.property.2 (primary_generators_coprime I J hcop)
    ((starRingEnd ℂ).toMonoidHom.comp (elementCharacter I.val I.property.2))
    (elementCharacter J.val J.property.2)
    (fun x y h => congrArg star (cubicRow_congr I.val I.property.2 x y h))
    (cubicRow_congr J.val J.property.2)
  change residueRowGauss _ _ (fun z => star (cubicRow I.val z) * cubicRow J.val z) =
    (star (idealKernel I.val J.val) * idealKernel J.val I.val) *
      residueRowGauss _ _ (fun z => star (cubicRow I.val z)) *
      residueRowGauss _ _ (cubicRow J.val) at hmul
  rw [hmul]
  have hcross : star (idealKernel I.val J.val) * idealKernel J.val I.val = 1 := by
    rw [←idealKernel_reciprocity I.val J.val I.property.2 J.property.2]
    change star (cubicRow I.val (primaryIdealGenerator J.val)) *
      cubicRow I.val (primaryIdealGenerator J.val) = 1
    rw [cubicRow_common_mask I.val I.property.2,
      (primaryIdealGenerator_spec J.val J.property.2).1,if_pos hcop]
  rw [hcross,one_mul,cubicRowGauss_star I.val I.property]

end CubicSieve
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve

/-- Paired cubic reflection with separated unit Gauss factors. -/
theorem cubic_pair_poisson (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, (star (cubicRow I z) * cubicRow J z) * W (‖ringComplex z‖ ^ 2 / M)) =
      ((M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
        (‖ringComplex (primaryIdealGenerator I * primaryIdealGenerator J)‖ : ℂ)) *
      ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖ringComplex h‖ ^ 2 /
          ‖ringComplex (primaryIdealGenerator I * primaryIdealGenerator J)‖ ^ 2) := by
  have hp := (prime_row_trace_poisson
    (pairRowPrime ⟨I,hI⟩ ⟨J,hJ⟩) (pairRowPrime_ne_zero ⟨I,hI⟩ ⟨J,hJ⟩)
    (pairRowPrime_injective ⟨I,hI⟩ ⟨J,hJ⟩ hcop)
    (pairRowCharacter ⟨I,hI⟩ ⟨J,hJ⟩) (pairRowCharacter_nonprincipal ⟨I,hI⟩ ⟨J,hJ⟩)).2 W M hM
  simp_rw [pairRowCharacter_eq,pairRowCharacter_inverse_eq,pairRowPrime_product] at hp
  rw [hp,pairRowGauss_separation ⟨I,hI⟩ ⟨J,hJ⟩ hcop]
  congr 1
  simp only [gaussTwo, star_div₀, Complex.star_def, Complex.conj_ofReal]
  simp only [map_mul,norm_mul,Complex.ofReal_mul,Complex.ofReal_pow,
    div_eq_mul_inv,mul_inv,inv_pow,mul_pow]
  ring

end CubicSieve
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson
noncomputable section
local notation "O" => Eisenstein.O

def cubicDualCoefficient {n : Type*} (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (j : n) : ℂ :=
  star (a j * gaussTwo (cols j) (hc j).2) / (‖ringComplex (primaryIdealGenerator (cols j))‖ : ℂ)

lemma cubicDualCoefficient_norm_sq {n : Type*}
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (j : n) :
    ‖cubicDualCoefficient cols hc a j‖ ^ 2 = ‖a j‖ ^ 2 / (Ideal.absNorm (cols j) : ℝ) := by
  simp only [cubicDualCoefficient, norm_div, norm_star, norm_mul, gaussTwo_norm_one _ (hc j),
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_pow,
    primaryIdealGenerator_norm_sq _ (hc j).2]

lemma cubicDualCoefficient_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (N : ℝ) (hN : 0 < N) (hcols : ∀ j, N / 2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    (∑ j, ‖cubicDualCoefficient cols hc a j‖ ^ 2) ≤ (2 / N) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [cubicDualCoefficient_norm_sq]
  calc
    _ ≤ ‖a j‖ ^ 2 / (N / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hcols j)
    _ = _ := by field_simp

def cubicDualRow {n : Type*} [Fintype n] (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
      ((‖ringComplex (primaryIdealGenerator (cols j))‖ : ℂ) * (‖ringComplex (primaryIdealGenerator (cols k))‖ : ℂ))) *
      (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0

lemma cubicDualRow_eq_gram {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) :
    cubicDualRow cols hc a W M h =
      ∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) h * cubicDualCoefficient cols hc a j) *
          (cubicRow (cols k) h * cubicDualCoefficient cols hc a k) else 0) *
        paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
          ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) := by
  unfold cubicDualRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [isCoprime_comm (x := cols k) (y := cols j)]
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [if_pos hcop, if_pos hcop]
    have hscale : (Ideal.absNorm (cols k) : ℝ) * (Ideal.absNorm (cols j) : ℝ) =
        (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) := mul_comm _ _
    rw [hscale]
    congr 1
    simp only [cubicDualCoefficient, star_mul, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · simp only [if_neg hcop, zero_mul]

lemma cubicRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    cubicRow I 0 = 0 := by
  have hI_top : I ≠ ⊤ := by simpa only [Ideal.one_eq_top] using hI1
  have hcop : ¬ IsCoprime I (Ideal.span {(0 : O)}) := by
    simpa only [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_zero, sup_bot_eq] using hI_top
  have h := idealSymbol_cube_mask I 0 hI.2
  rw [if_neg hcop] at h
  exact eq_zero_of_pow_eq_zero h

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson
noncomputable section
local notation "O" => Eisenstein.O

lemma cubicRow_norm_le_one (I : Ideal O) (hI : Admissible I) (z : O) : ‖cubicRow I z‖ ≤ 1 :=
  elementCharacter_norm_le_one I hI.2 z

lemma cubic_pair_fourier_summable (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (cubicRow I h * star (cubicRow J h)) *
      paperRadialFourier W (t * ‖ringComplex h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (cubicRow_norm_le_one I hI h) (norm_nonneg _)).trans
      (by simpa only [one_mul] using cubicRow_norm_le_one J hJ h))
    (norm_nonneg _)).trans_eq (one_mul _)

def cubicSmoothedCoprime {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k * ∑' z : O, (star (cubicRow (cols j) z) * cubicRow (cols k) z) *
      W (‖ringComplex z‖ ^ 2 / M) else 0

lemma pair_modulus_norm_sq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖ringComplex (primaryIdealGenerator I * primaryIdealGenerator J)‖ ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [map_mul, norm_mul, mul_pow, primaryIdealGenerator_norm_sq I hI.2, primaryIdealGenerator_norm_sq J hJ.2]

lemma cubicDualRow_summable {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (cubicDualRow cols hc a W M) := by
  apply summable_sum
  intro j hj
  apply summable_sum
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [if_pos hcop]
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ (hc k).2))
    have hs := (cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity)).mul_left
      (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
        ((‖ringComplex (primaryIdealGenerator (cols j))‖ : ℂ) * (‖ringComplex (primaryIdealGenerator (cols k))‖ : ℂ)))
    apply hs.congr
    intro z
    rw [ringComplex_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  · simp only [if_neg hcop]
    exact summable_zero

lemma cubicDualRow_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' h : O, cubicDualRow cols hc a W M h) =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖ringComplex (primaryIdealGenerator (cols j))‖ : ℂ) * (‖ringComplex (primaryIdealGenerator (cols k))‖ : ℂ))) *
          ∑' h : O, (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0 := by
  have hs (j k : n) : Summable (fun h : O => (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))) := by
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ (hc k).2))
    convert cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity) using 1
    ext z
    rw [ringComplex_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  unfold cubicDualRow
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖ringComplex (primaryIdealGenerator (cols j))‖ : ℂ) * (‖ringComplex (primaryIdealGenerator (cols k))‖ : ℂ)))
    · exact summable_zero))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖ringComplex (primaryIdealGenerator (cols j))‖ : ℂ) * (‖ringComplex (primaryIdealGenerator (cols k))‖ : ℂ)))
    · exact summable_zero)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp only [tsum_zero, mul_assoc, tsum_mul_left]

theorem cubicSmoothedCoprime_poisson {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    cubicSmoothedCoprime cols a W M =
      (M : ℂ) * ∑' h : O, cubicDualRow cols hc a W M h := by
  rw [cubicDualRow_tsum cols hc a W M hM]
  unfold cubicSmoothedCoprime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [if_pos hcop, if_pos hcop, cubic_pair_poisson _ _ (hc j) (hc k) hcop W M hM]
    rw [pair_modulus_norm_sq _ _ (hc j) (hc k)]
    simp_rw [ringComplex_norm_sq_eq_absNorm_span]
    rw [map_mul, norm_mul, Complex.ofReal_mul]
    ring
  · simp only [if_neg hcop, mul_zero]

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson.CanonicalQuadraticSieve  SecondPassArithmetic
noncomputable section
local notation "O" => Eisenstein.O

lemma majorant_radial_summable (P : O → ℂ) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowMajorant (‖ringComplex z‖^2 / M) * P z) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall M) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside M hM z hz, zero_mul]

lemma majorant_rescale (d z : O) (_hd : d ≠ 0) (M : ℝ) :
    rowMajorant (‖ringComplex (d*z)‖^2 / M) =
      rowMajorant (‖ringComplex z‖^2 / (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) := by
  rw [map_mul, norm_mul, mul_pow, ringComplex_norm_sq_eq_absNorm_span d]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma dividedMajorant_tsum (P : O → ℂ) (d : O) (hd : d ≠ 0)
    (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ dividedRows (rowMajorantBall M) d,
      rowMajorant (‖ringComplex (d*z)‖^2 / M) * P z) =
      ∑' z : O, rowMajorant (‖ringComplex z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z := by
  symm
  rw [← show (fun z : O => rowMajorant (‖ringComplex (d*z)‖^2 / M) * P z) =
      (fun z : O => rowMajorant (‖ringComplex z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z) by
          funext z; rw [majorant_rescale d z hd M]]
  apply tsum_eq_sum
  intro z hz
  have hout : d*z ∉ rowMajorantBall M := by
    intro hin
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨d*z, Finset.mem_filter.mpr ⟨hin, dvd_mul_right d z⟩, ?_⟩
    apply mul_left_cancel₀ hd
    exact elementQuotient_mul d (d*z) (dvd_mul_right d z)
  rw [rowMajorant_zero_outside M hM (d*z) hout, zero_mul]

lemma majorant_coprime_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowMajorant (‖ringComplex z‖^2 / M) *
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) =
      cubicSmoothedCoprime cols a rowMajorant M := by
  have hs (j k : n) := majorant_radial_summable
    (fun z => if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) M hM
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => hs j k))]
  unfold cubicSmoothedCoprime
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => hs j k)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [if_pos hcop]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    simp only [star_mul]
    ring
  · simp only [if_neg hcop, mul_zero, tsum_zero]

lemma compact_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryIdealGenerator D ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ rowMajorantBall M, rowMajorant (‖ringComplex z‖^2 / M) *
      ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ idealDivisors D, (UniqueFactorizationMonoid.moebius E : ℂ) *
        cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (cubicIdealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ)) := by
  rw [cubic_gcd_mobius_descent D hD cols hc a]
  apply Finset.sum_congr rfl
  intro E hE
  have hE0 : E ≠ 0 := by
    intro he
    have hh := (mem_idealDivisors (primaryIdealGenerator_ne_zero_ideal D hD)).mp hE
    rw [he, zero_dvd_iff] at hh
    exact primaryIdealGenerator_ne_zero_ideal D hD hh
  have hgen := cubicIdealGenerator_ne_zero E hE0
  congr 1
  rw [dividedMajorant_tsum _ _ hgen M hM, span_cubicIdealGenerator]
  apply majorant_coprime_tsum
  have hNE : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  exact div_pos hM hNE

lemma gcdPool_cubic_admissible {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (D : Ideal O) (hD : D ∈ gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact cubic_admissible_of_dvd (hc j) (gcd_dvd_left _ _)

theorem finite_energy_le_compact_descendants {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (R : Finset O) (M : ℝ) (hM : 0 < M)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ‖cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (cubicIdealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ))‖ := by
  have hs := finite_row_energy_le_rowMajorant
    (fun z => ∑ j, cubicRow (cols j) z * a j) R M hM hR
  apply hs.trans
  apply (Complex.re_le_norm _).trans
  rw [rowMajorant_tsum_eq_sum _ M hM,
    cubic_weighted_energy_eq_gcd_blocks (rowMajorantBall M) _ cols a]
  have he (D : Ideal O) (hD : D ∈ gcdPool cols) :=
    compact_gcd_mobius_descent D (gcdPool_cubic_admissible cols hc D hD).2 cols hc a M hM
  calc
    _ ≤ ∑ D ∈ gcdPool cols,
        ‖∑ z ∈ rowMajorantBall M, rowMajorant (‖ringComplex z‖^2 / M) *
          ∑ j, ∑ k, cubicGcdTerm D cols a z j k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro D hD
      rw [he D hD]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (IdealCoprimeBilinearSieve.moebius_norm_le_one E)
        (norm_nonneg _)).trans_eq (one_mul _)

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson.CanonicalQuadraticSieve
noncomputable section
local notation "O" => Eisenstein.O

lemma finite_sum_restrict {n A : Type*} [Fintype n] [AddCommMonoid A]
    (p : n → Prop) (f : n → A) (hf : ∀ j, ¬p j → f j = 0) :
    (∑ j, f j) = ∑ j : {j // p j}, f j.val := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ j : {j // ¬p j}, f j.val) = 0 :=
    Finset.sum_eq_zero (fun j hj => hf j.val j.property)
  rw [hz, add_zero] at h
  exact h.symm

lemma cubicSmoothedCoprime_restrict {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (p : n → Prop)
    (ha : ∀ j, ¬p j → a j = 0) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime cols a W M =
      cubicSmoothedCoprime (fun j : {j // p j} => cols j.val) (fun j => a j.val) W M := by
  unfold cubicSmoothedCoprime
  rw [finite_sum_restrict p _ (by
    intro j hj
    simp [ha j hj])]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_sum_restrict p _ (by
    intro k hk
    simp [ha k hk])

def quotientColumn {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (j : {j // D ∣ cols j}) : Ideal O := quadraticIdealQuotient D (cols j.val)

def quotientCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : {j // D ∣ cols j}) : ℂ :=
  cubicRow (quotientColumn D cols j) d * a j.val

lemma quotientColumn_injective {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : Function.Injective cols) : Function.Injective (quotientColumn D cols) := by
  intro j k he
  exact Subtype.ext (hc (quadraticIdealQuotient_injective D j.property k.property he))

lemma quotientColumn_admissible {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (j : {j // D ∣ cols j}) :
    Admissible (quotientColumn D cols j) := cubic_admissible_quotient (hc j.val) j.property

lemma cubic_quotient_in_shell {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ)
    (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (j : {j // D ∣ cols j}) :
    (N / (Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) ∧
      (Ideal.absNorm (quotientColumn D cols j) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryIdealGenerator_ne_zero_ideal _ (hc j.val).2) j.property
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have he : (Ideal.absNorm (quotientColumn D cols j) : ℝ) * (Ideal.absNorm D : ℝ) =
      (Ideal.absNorm (cols j.val) : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, quotientColumn, quadraticIdeal_mul_quotient j.property]
  have hn : (Ideal.absNorm (quotientColumn D cols j) : ℝ) ≤ N / Ideal.absNorm D := by
    rw [quotientColumn,quadraticIdealQuotient_norm hD0 j.property]
    exact div_le_div_of_nonneg_right (hcols j.val).2 (Nat.cast_nonneg _)
  refine ⟨?_, hn⟩
  have hh : (N/2) / (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) := by
    apply (div_le_iff₀ hDN).mpr
    rw [he]
    exact (hcols j.val).1
  convert hh using 1; ring

lemma compact_descendant_restrict {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
      (descendedCoefficient D cols a d) W M =
    cubicSmoothedCoprime (quotientColumn D cols) (quotientCoefficient D cols a d) W M := by
  rw [cubicSmoothedCoprime_restrict _ _ (fun j => D ∣ cols j) (by
    intro j hj
    simp only [descendedCoefficient, if_neg hj, mul_zero])]
  have hc : (fun j : {j // D ∣ cols j} => totalQuotient D (cols j.val)) = quotientColumn D cols := by
    funext j
    simp only [totalQuotient, if_pos j.property, quotientColumn]
  have ha : (fun j : {j // D ∣ cols j} => descendedCoefficient D cols a d j.val) =
      quotientCoefficient D cols a d := by
    funext j
    simp only [descendedCoefficient, totalQuotient, if_pos j.property, quotientCoefficient, quotientColumn]
  rw [hc, ha]

lemma quotientCoefficient_energy {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O) :
    (∑ j : {j // D ∣ cols j}, ‖quotientCoefficient D cols a d j‖^2) =
      ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
  rw [finite_sum_restrict (fun j => D ∣ cols j) _ (by
    intro j hj
    simp only [descendedCoefficient, if_neg hj, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [quotientCoefficient, quotientColumn, descendedCoefficient, totalQuotient, if_pos j.property]

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson 
noncomputable section
local notation "O" => Eisenstein.O

theorem cubic_radial_kernel_transfer (W : 𝓢(ℝ, ℂ)) (Lr Lc : ℝ)
    (hLr : 0 ≤ Lr) (hLc : 0 ≤ Lc) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hN : 0 ≤ N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
        (_hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E)
        (x : m → ℝ) (y : n → ℝ) (_hx : ∀ i, |x i| ≤ Lr) (_hy : ∀ j, |y j| ≤ Lc),
        (1 + R) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (R * Real.exp (x i + (y j + y k)))‖) ≤
          C * (elementSieveNorm M N *
            (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, htransfer⟩ := QuadraticKernelTransfer.radial_matrix_kernel_transfer
    W Lr (2 * Lc) hLr (by positivity) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ _ _ ε hε M N hN rows cols hr hc hrows hcols a b E hE ha hb x y hx hy
  let c : m → n × n → ℂ := fun i p => if IsCoprime (cols p.1) (cols p.2) then
    star (cubicRow (cols p.1) (rows i) * a p.1) *
      (cubicRow (cols p.2) (rows i) * b p.2) else 0
  let H := elementSieveNorm M N * (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) * E
  have hfac : 0 ≤ elementSieveNorm M N * (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) :=
    mul_nonneg (elementSieveNorm_nonneg _ _)
      (mul_nonneg (DivisorBlockCauchy.divisorConstant_pos ε hε).le (Real.rpow_nonneg hN _))
  have hH : 0 ≤ H := mul_nonneg hfac hE
  have hyy (p : n × n) : |y p.1 + y p.2| ≤ 2 * Lc :=
    (abs_add_le _ _).trans (by linarith [hy p.1, hy p.2])
  have hphase (t : ℝ) : (∑ i, ‖∑ p : n × n, c i p * kernelLogPhase t (y p.1 + y p.2)‖) ≤ H := by
    let aTwist : n → ℂ := fun j => a j * star (kernelLogPhase t (y j))
    let bTwist : n → ℂ := fun j => b j * kernelLogPhase t (y j)
    have ha' : (∑ j, ‖aTwist j‖ ^ 2) ≤ E := by simpa only [aTwist, norm_mul, norm_star, kernelLogPhase_norm, mul_one] using ha
    have hb' : (∑ j, ‖bTwist j‖ ^ 2) ≤ E := by simpa only [bTwist, norm_mul, kernelLogPhase_norm, mul_one] using hb
    have he (i : m) : (∑ p : n × n, c i p * kernelLogPhase t (y p.1 + y p.2)) =
        ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
          star (cubicRow (cols j) (rows i) * aTwist j) *
            (cubicRow (cols k) (rows i) * bTwist k) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c, aTwist, bTwist]
      split_ifs
      · rw [kernelLogPhase_add]
        simp only [star_mul, star_star]
        ring
      · simp only [zero_mul]
    simp_rw [he]
    have hbil := element_coprime_bilinear_bound ε hε M N hN rows cols hr hc hrows hcols aTwist bTwist
    apply (sq_le_sq₀ (by positivity) hH).mp
    apply hbil.trans
    calc
      _ ≤ (elementSieveNorm M N * (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) * E) *
          (elementSieveNorm M N * (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) * E) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha' hfac) (mul_le_mul_of_nonneg_left hb' hfac)
          (by positivity) hH
      _ = H ^ 2 := by ring
  have ht := htransfer R hR c x (fun p : n × n => y p.1 + y p.2) H hH hx hyy hphase
  simpa only [Fintype.sum_prod_type, c, H] using ht

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson 
noncomputable section
local notation "O" => Eisenstein.O

lemma log_shell_ratio (K q : ℝ) (hK : 0 < K) (hq : K / 2 ≤ q ∧ q ≤ K) :
    |Real.log (q / K)| ≤ 4 := by
  apply SchwartzPlanePoisson.CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hK).mpr
    linarith [hq.1]
  · apply (div_le_iff₀ hK).mpr
    linarith [hq.2]

lemma log_inverse_shell_ratio (N q : ℝ) (hN : 0 < N) (hq : N / 2 ≤ q ∧ q ≤ N) :
    |Real.log (N / q)| ≤ 4 := by
  have hq0 : 0 < q := by linarith [hq.1]
  apply SchwartzPlanePoisson.CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hq0).mpr
    linarith [hq.2]
  · apply (div_le_iff₀ hq0).mpr
    linarith [hq.1]

lemma radial_product_log_identity (M K N q u v : ℝ)
    (hK : 0 < K) (hN : 0 < N) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) :
    (M * K / N ^ 2) * Real.exp (Real.log (q / K) + (Real.log (N / u) + Real.log (N / v))) =
      M * q / (u * v) := by
  rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hq hK),
    Real.exp_log (div_pos hN hu), Real.exp_log (div_pos hN hv)]
  field_simp

theorem cubic_frequency_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {rows i}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))‖) ≤
          C * (elementSieveNorm K N *
            (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, ht⟩ := cubic_radial_kernel_transfer W 4 4 (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a b E hE ha hb
  have hq (i : m) : 0 < (Ideal.absNorm (Ideal.span {rows i}) : ℝ) := by linarith [(hrows i).1]
  have hn (j : n) : 0 < (Ideal.absNorm (cols j) : ℝ) := by linarith [(hcols j).2.1]
  have hr0 (i : m) : rows i ≠ 0 := by
    intro hz
    simpa [hz] using hq i
  have hp := ht (M * K / N ^ 2) (by positivity) ε hε K N hN.le rows cols hr hc
    (fun i => ⟨hr0 i, (hrows i).2⟩) (fun j => ⟨(hcols j).1, (hcols j).2.2⟩)
    a b E hE ha hb
    (fun i => Real.log ((Ideal.absNorm (Ideal.span {rows i}) : ℝ) / K))
    (fun j => Real.log (N / (Ideal.absNorm (cols j) : ℝ)))
    (fun i => log_shell_ratio K _ hK (hrows i))
    (fun j => log_inverse_shell_ratio N _ hN (hcols j).2)
  simp_rw [radial_product_log_identity M K N _ _ _ hK hN (hq _) (hn _) (hn _)] at hp
  exact hp

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson
noncomputable section
local notation "O" => Eisenstein.O

lemma cubicDualRow_zero {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hunit : ∀ j, cols j ≠ 1) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicDualRow cols hc a W M 0 = 0 := by
  unfold cubicDualRow
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  rw [cubicRow_zero_of_ne_one _ (hc j) (hunit j)]
  simp

theorem cubic_dual_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖cubicDualRow cols (fun j => (hcols j).1) a W M (rows i)‖) ≤
          C * (elementSieveNorm K N *
            (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) *
              ((2 / N) * ∑ j, ‖a j‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := cubic_frequency_shell_bound W A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a
  have he := cubicDualCoefficient_energy cols (fun j => (hcols j).1) a N hN
    (fun j => (hcols j).2.1)
  have h := hb ε hε M K N hM hK hN rows cols hr hc hrows hcols
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    ((2 / N) * ∑ j, ‖a j‖ ^ 2) (by positivity) he he
  simpa only [cubicDualRow_eq_gram] using h

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

def frequencyDyad (j : ℕ) : Finset O :=
  (elementRange ((2 : ℝ)^j)).filter (fun h => Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j)

lemma mem_frequencyDyad (h : O) (j : ℕ) :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_elementRange]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hh, hj⟩
    refine ⟨⟨hh, ?_⟩, hj⟩
    have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
    rw [hj] at hu
    exact_mod_cast hu

lemma frequencyDyad_bounds (j : ℕ) (h : O) (hh : h ∈ frequencyDyad j) :
    h ≠ 0 ∧ (2 : ℝ)^j / 2 ≤ (Ideal.absNorm (Ideal.span {h}) : ℝ) ∧
      (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ (2 : ℝ)^j := by
  obtain ⟨hn, hj⟩ := (mem_frequencyDyad h j).mp hh
  have hnorm : Ideal.absNorm (Ideal.span {h}) ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
  have hl := two_pow_clog_le_double _ (Nat.one_le_iff_ne_zero.mpr hnorm)
  rw [hj] at hu hl
  refine ⟨hn, ?_, by exact_mod_cast hu⟩
  have hr : (2 : ℝ)^j ≤ 2 * (Ideal.absNorm (Ideal.span {h}) : ℝ) := by exact_mod_cast hl
  linarith

def frequencyDyadicEquiv : {h : O // h ≠ 0} ≃ Σ j : ℕ, frequencyDyad j where
  toFun h := ⟨Nat.clog 2 (Ideal.absNorm (Ideal.span {h.val})),
    ⟨h.val, (mem_frequencyDyad _ _).mpr ⟨h.property, rfl⟩⟩⟩
  invFun h := ⟨h.2.val, ((mem_frequencyDyad _ _).mp h.2.property).1⟩
  left_inv h := by cases h; rfl
  right_inv h := by
    rcases h with ⟨j, h, hh⟩
    have hj := ((mem_frequencyDyad h j).mp hh).2
    dsimp only
    subst j
    rfl

theorem tsum_frequencyDyads (f : O → ℂ) (hf : Summable f) (hzero : f 0 = 0) :
    (∑' h : O, f h) = ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
    symm
    exact tsum_subtype_eq_of_support_subset (fun h hh => by
      change h ≠ 0
      intro hz
      exact hh (hz ▸ hzero))
  rw [he]
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

theorem tsum_frequencyDyads_with_zero (f : O → ℂ) (hf : Summable f) :
    (∑' h : O, f h) = f 0 + ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = f 0 + ∑' h : {h : O // h ≠ 0}, f h.val := by
    have hs := (hf.sum_add_tsum_compl (s := {0})).symm
    have hset : ((↑({0} : Finset O) : Set O)ᶜ) = {h : O | h ≠ 0} := by
      ext h
      simp
    rw [hset] at hs
    simp only [Finset.sum_singleton] at hs
    exact hs
  rw [he]
  congr 1
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical
noncomputable section

def elementInitialConstant : ℝ := elementSieveNorm_initial.choose
lemma elementInitialConstant_pos : 0 < elementInitialConstant :=
  elementSieveNorm_initial.choose_spec.1
lemma elementSieveNorm_initial_bound (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    elementSieveNorm M N ≤ elementInitialConstant * (M + N^2) :=
  elementSieveNorm_initial.choose_spec.2 M N hM hN

def frequencyMajorant (M N : ℝ) (j : ℕ) : ℝ :=
  elementSieveNorm ((2 : ℝ)^j) N / (1 + M * (2 : ℝ)^j / N^2)^3

lemma frequencyMajorant_nonneg (M N : ℝ) (hM : 0 ≤ M) (j : ℕ) :
    0 ≤ frequencyMajorant M N j := by
  unfold frequencyMajorant
  exact div_nonneg (elementSieveNorm_nonneg _ _) (by positivity)

lemma frequencyMajorant_geometric (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) (j : ℕ) :
    frequencyMajorant M N j ≤
      (elementInitialConstant * (1 + N^2) /
        (M / N^2)^3) * ((1 / 4 : ℝ)^j) := by
  let K : ℝ := (2 : ℝ)^j
  let c : ℝ := M / N^2
  let Q : ℝ := N^2
  let C : ℝ := elementInitialConstant
  have hK : 1 ≤ K := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hK0 : 0 < K := by positivity
  have hN0 : 0 < N := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : 0 ≤ Q := sq_nonneg _
  have hC : 0 ≤ C := elementInitialConstant_pos.le
  have hi : elementSieveNorm K N ≤ C * (1 + Q) * K := by
    apply (elementSieveNorm_initial_bound K N hK hN).trans
    dsimp only [C, Q]
    nlinarith [mul_nonneg hC (mul_nonneg hQ (sub_nonneg.mpr hK))]
  have hden : (c*K)^3 ≤ (1+c*K)^3 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hgeom : (K^2)⁻¹ = (1/4 : ℝ)^j := by
    dsimp only [K]
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ← inv_pow]
    norm_num
  change elementSieveNorm K N / (1 + M*K/N^2)^3 ≤ _
  rw [show M*K/N^2 = c*K by dsimp [c]; ring]
  calc
    _ ≤ (C*(1+Q)*K) / (1+c*K)^3 := div_le_div_of_nonneg_right hi (by positivity)
    _ ≤ (C*(1+Q)*K) / (c*K)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (C*(1+Q)/c^3) * (K^2)⁻¹ := by field_simp
    _ = _ := by rw [hgeom]

theorem frequencyMajorant_summable (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) :
    Summable (frequencyMajorant M N) := by
  have hg : Summable (fun j : ℕ => (1/4 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact (hg.mul_left _).of_nonneg_of_le
    (frequencyMajorant_nonneg M N hM.le) (frequencyMajorant_geometric M N hM hN)

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson
noncomputable section
local notation "O" => Eisenstein.O

@[simp] lemma cubicRow_one (z : O) : cubicRow 1 z = 1 := by
  rw [cubicRow,←idealRowHom_square,map_one,one_pow]

theorem cubicDualRow_zero_bound {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hinj : Function.Injective cols) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M N : ℝ)
    (hN : 0 < N) (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    ‖cubicDualRow cols hc a W M 0‖ ≤
      ((2/N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ := by
  by_cases hu : ∃ j, cols j = 1
  · obtain ⟨j₀, hj₀⟩ := hu
    have ho (j : n) (hj : j ≠ j₀) : cols j ≠ 1 := by
      intro he
      exact hj (hinj (he.trans hj₀.symm))
    have he : cubicDualRow cols hc a W M 0 =
        (star (cubicDualCoefficient cols hc a j₀) * cubicDualCoefficient cols hc a j₀) *
          paperRadialFourier W 0 := by
      rw [cubicDualRow_eq_gram]
      rw [Finset.sum_eq_single j₀]
      · rw [Finset.sum_eq_single j₀]
        · simp only [hj₀, cubicRow_one, one_mul, Ideal.span_singleton_zero,
            Ideal.absNorm_bot, Nat.cast_zero, mul_zero, zero_div, if_pos isCoprime_one_left]
        · intro k hk hkj
          rw [cubicRow_zero_of_ne_one _ (hc k) (ho k hkj)]
          simp
        · simp
      · intro j hj hjj
        rw [cubicRow_zero_of_ne_one _ (hc j) (ho j hjj)]
        simp
      · simp
    rw [he, norm_mul, norm_mul, norm_star, ← pow_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Finset.single_le_sum (fun j hj => sq_nonneg ‖cubicDualCoefficient cols hc a j‖)
      (Finset.mem_univ j₀)).trans (cubicDualCoefficient_energy cols hc a N hN hcols)
  · have hz : ∀ j, cols j ≠ 1 := fun j hj => hu ⟨j,hj⟩
    rw [cubicDualRow_zero cols hc hz a W M, norm_zero]
    positivity

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson
noncomputable section
local notation "O" => Eisenstein.O

theorem cubic_smoothed_frequency_recurrence (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (_hunit : ∀ j, cols j ≠ 1) (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (C * (DivisorBlockCauchy.divisorConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols hunit a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (DivisorBlockCauchy.divisorConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hf0 : f 0 = 0 := cubicDualRow_zero cols (fun j => (hcols j).1) hunit a W M
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (DivisorBlockCauchy.divisorConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads f hf hf0]
  exact mul_le_mul_of_nonneg_left hb hM.le

theorem cubic_smoothed_frequency_recurrence_all (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (((2 / N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ + C * (DivisorBlockCauchy.divisorConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (DivisorBlockCauchy.divisorConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (DivisorBlockCauchy.divisorConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads_with_zero f hf]
  apply mul_le_mul_of_nonneg_left _ hM.le
  exact (norm_add_le _ _).trans (add_le_add
    (cubicDualRow_zero_bound cols (fun j => (hcols j).1) hc a W M N hN0
      (fun j => (hcols j).2.1)) hb)

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson.CanonicalQuadraticSieve  SecondPassArithmetic SchwartzPlanePoisson
noncomputable section
local notation "O" => Eisenstein.O

def frequencyCost (C ε : ℝ) (hε : 0 < ε) (M N : ℝ) : ℝ :=
  M * (2/N) * (‖paperRadialFourier rowMajorant 0‖ +
    C * (DivisorBlockCauchy.divisorConstant ε hε * N^ε) *
      ∑' l : ℕ, frequencyMajorant M N l)

theorem cubic_common_factor_frequency_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M)
        (cols : n → Ideal O) (_hinj : Function.Injective cols)
        (_hc : ∀ j, Admissible (cols j))
        (_hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ) (R : Finset O)
        (_hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M),
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
          ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
            frequencyCost C ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ)) *
              ∑ j, ‖descendedCoefficient D cols a (cubicIdealGenerator E) j‖^2 := by
  obtain ⟨C,hC,hrec⟩ := cubic_smoothed_frequency_recurrence_all rowMajorant
  refine ⟨C,hC,?_⟩
  intro n _ _ ε hε M N hM cols hinj hc hcols a R hR
  apply (finite_energy_le_compact_descendants cols hc a R M hM hR).trans
  apply Finset.sum_le_sum
  intro D hD
  have hc0 (j : n) : cols j ≠ 0 := primaryIdealGenerator_ne_zero_ideal _ (hc j).2
  have hDcol := gcdPool_subset_columnDivisorPool cols hc0 hD
  have hDN := columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D hDcol
  have hD0 := gcdPool_ne_zero cols hc0 D hD
  have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith [hDN.1]
  have hNshort : 1 ≤ N / (Ideal.absNorm D : ℝ) := (one_le_div hDN0).mpr hDN.2
  apply Finset.sum_le_sum
  intro E hE
  have hEdiv := (mem_idealDivisors hD0).mp hE
  have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hEdiv
  have hEN : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  rw [compact_descendant_restrict]
  have hh := hrec ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ))
    (div_pos hM hEN) hNshort (quotientColumn D cols) (quotientColumn_injective D cols hinj)
    (fun j => ⟨quotientColumn_admissible D cols hc j, cubic_quotient_in_shell D cols hc N hcols j⟩)
    (quotientCoefficient D cols a (cubicIdealGenerator E))
  rw [quotientCoefficient_energy] at hh
  convert hh using 1 <;> (try dsimp only [frequencyCost]) <;> first | rfl | ring

theorem common_factor_uniform_cost {n : Type*} [Fintype n]
    (C ε U M N : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hN : 0 ≤ N)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hnorm : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ)
    (hcost : ∀ D ∈ gcdPool cols, ∀ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U) :
    (∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) *
        ∑ j, ‖descendedCoefficient D cols a (cubicIdealGenerator E) j‖^2) ≤
      U*(DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2 := by
  have he := descended_energy_small_power ε hε cols hc N hN hnorm a
  have hsub := gcdPool_subset_columnDivisorPool cols
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (hc j).2)
  calc
    _ ≤ ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        U * ∑ j, ‖descendedCoefficient D cols a (cubicIdealGenerator E) j‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_right (hcost D hD E hE) (by positivity)
    _ = U*(∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (cubicIdealGenerator E) j‖^2) := by
      simp only [Finset.mul_sum]
    _ ≤ U*(∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (cubicIdealGenerator E) j‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hU
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hD hnot => by positivity)
    _ ≤ U*((DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left he hU
    _ = _ := by ring

end
end CubicSieve

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
