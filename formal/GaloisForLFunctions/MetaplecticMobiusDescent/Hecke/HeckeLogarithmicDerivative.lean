/-
The logarithmic derivative of Hecke L-functions adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.HeckeLFunctionsAndReciprocals

/-!
# The logarithmic derivative of Hecke L-functions

Unit rows, Euler factors and finite deletion of Hecke series; the trivial character gives the
Dedekind zeta series, and clearing its pole uses the theta completion. The ideal von Mangoldt
function and the pole-subtracted logarithmic derivative.
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
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace EulerFactors

noncomputable section

def factor (N : ℝ) (a s : ℂ) : ℂ := 1 - a * (N : ℂ) ^ (-s)

theorem norm_term_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

theorem factor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)

theorem differentiable_factor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))

def deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a : ι → ℂ)
    (s : ℂ) : ℂ := ∏ p ∈ S, factor (N p) (a p) s

theorem deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs

theorem differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)

theorem deleted_eq_zero_iff {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {L Ldeleted : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hidentity : Ldeleted s = deletedProduct S N a s * L s) :
    Ldeleted s = 0 ↔ L s = 0 := by
  rw [hidentity, mul_eq_zero]
  exact or_iff_right (deletedProduct_ne_zero S N a hN ha hs)

end

end EulerFactors

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

def factors (M : Ideal O) (ψ : Character) : ℂ → ℂ :=
  EulerFactors.deletedProduct (HeckeIdealSeries.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => idealCoeff ψ P.val)

theorem factors_eq (M : Ideal O) (ψ : Character) (s : ℂ) :
    factors M ψ s = ∏ P ∈ HeckeIdealSeries.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : Character) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := HeckeIdealSeries.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (M : Ideal O) (ψ : Character) {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := HeckeIdealSeries.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (isOpen_lt continuous_const Complex.continuous_re)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by intro h; simp [h] at hs)).differentiableWithinAt

theorem regularizedL_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (isOpen_lt continuous_const Complex.continuous_re)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  intro z hz
  have hz' : 1 < z.re := by simpa using hz
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz'
  have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem LFunction_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h := regularizedL_eq_of_mask χ ψ hmask hs
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1, mul_assoc] at h
  exact mul_left_cancel₀ (sub_ne_zero.mpr h1) h

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

theorem principal_iff_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

theorem LFunction_eq_of_mask_nonprincipal (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha (η : Character) (hη : η.residue ≠ 1) :
      AnalyticOnNhd ℂ (LFunction η) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (isOpen_lt continuous_const Complex.continuous_re)).2
    intro z hz
    exact (LFunction_differentiableAt η (by intro h; simp [h] at hz)
      (Or.inr hη)).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (isOpen_lt continuous_const Complex.continuous_re)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (LFunction ψ) (factors χ.modulus ψ) (LFunction χ) (ha ψ hψ) hf (ha χ hχ) _ hs
  intro z hz
  exact (LFunction_eq_of_mask_right χ ψ hmask (by simpa using hz)).symm

theorem LFunction_eq_of_mask_nonpole (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rcases hpole with h1 | hχ
  · exact LFunction_eq_of_mask χ ψ hmask hs h1
  · exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

theorem exists_primitive_same_zeros (χ : Character) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 →
        (LFunction χ s = 0 ↔ LFunction ψ s = 0) := by
  obtain ⟨ψ, hmod, hp, hnorm, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hmod, hp, hnorm, ?_⟩
  intro s hs h1
  rw [LFunction_eq_of_mask χ ψ hmask hs h1, mul_eq_zero]
  exact or_iff_left (factors_ne_zero χ.modulus ψ hs)

theorem exists_primitive_zero (χ : Character) {s : ℂ}
    (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) ∧ LFunction ψ s = 0 := by
  obtain ⟨ψ, _, hp, _, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, ?_, ?_⟩
  · rcases hpole with h1 | hχ
    · exact Or.inl h1
    · exact Or.inr (fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h))
  · rw [LFunction_eq_of_mask_nonpole χ ψ hmask hs hpole, mul_eq_zero] at hz
    exact hz.resolve_right (factors_ne_zero χ.modulus ψ hs)

end HeckeFiniteDeletion

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeUnitRows
open HeckeFamily CanonicalRowCompletion
open Eisenstein CubicRamified 
local notation "O" => Eisenstein.O

theorem seven_coprime_thirty_six : IsCoprime sevenPrime (36 : O) := by
  have hω : Eisenstein.omega ^ 2 = -Eisenstein.omega - 1 := by
    simpa [Eisenstein.omega] using IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ Eisenstein.K)
  change IsCoprime (1 + 3 * Eisenstein.omega) (36 : O)
  refine ⟨31 * (-2 - 3 * Eisenstein.omega), -6, ?_⟩
  linear_combination -279 * hω

theorem supported_unit_thirty_six (n : O) (hn : quadraticSupported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using hs.2)
  have h2 : IsCoprime n (2 : O) := (hneg2.of_isCoprime_of_dvd_left ⟨-1, by ring⟩).symm
  have h9 := (CanonicalRowCompletion.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (h2.pow_right : IsCoprime n ((2 : O)^2)).mul_right h9 using 1 ; norm_num

theorem unitSupplement_unit (u v : Oˣ) : unitSupplement u (v : O) = 1 := by
  have hspan : (Ideal.span {(v : O)} : Ideal O) = 1 := by
    simpa only [Ideal.one_eq_top] using Ideal.span_singleton_eq_top.mpr v.isUnit
  have hs : quadraticSupported (1 : Ideal O) :=
    (CanonicalQuadraticSieve.supported_iff_native _).mp ⟨one_ne_zero, by
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact False.elim (Multiset.notMem_zero P hP)⟩
  change (if quadraticSupported (Ideal.span {(v : O)}) then idealRowHom (u : O) (Ideal.span {(v : O)}) else 0) = 1
  rw [hspan, if_pos hs, map_one]

private theorem unitSupplement_factorsModulo (u : Oˣ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36 : O)}) (unitSupplement u) :=
  unitSupplement_periodic u

def character (u : Oˣ) : Character :=
  HeckeRowClosure.rowCharacter (Ideal.span {(36 : O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)) (unitSupplement u)
    (unitSupplement_factorsModulo u) (unitSupplement_unit u)

theorem elementCoeff_character (u : Oˣ) (n : O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if quadraticSupported (Ideal.span {n}) then _ else 0
    rw [if_neg (fun hs => hn (supported_unit_thirty_six n hs))]

theorem seven_supported : quadraticSupported (Ideal.span {sevenPrime}) := by
  rw [supported_span_iff]
  constructor
  · intro h
    have hd : lambda ∣ (36 : O) :=
      ((dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three).trans ⟨12, by norm_num⟩
    exact residue_lambda_prime.not_unit
      (seven_coprime_thirty_six.isUnit_of_dvd' h hd)
  · intro h
    have hu := seven_coprime_thirty_six.isUnit_of_dvd' h (show (2 : O) ∣ 36 from ⟨18, by norm_num⟩)
    exact negative_two_prime.not_unit hu.neg

theorem unitSupplement_seven (u : Oˣ) :
    unitSupplement u sevenPrime = ringComplex (u : O) := by
  change (if quadraticSupported (Ideal.span {sevenPrime}) then idealRowHom (u : O) (Ideal.span {sevenPrime}) else 0) = _
  rw [if_pos seven_supported,
    idealRowHom_unit_norm u _ seven_supported]
  change ringComplex ((u : O) ^ ((Ideal.absNorm sevenIdeal - 1) / 6)) = _
  rw [sevenIdeal_norm]
  norm_num

theorem character_nonprincipal (u : Oˣ) (hu : u ≠ 1) :
    (character u).residue ≠ 1 := by
  have hv : elementCoeff (character u) sevenPrime = ringComplex (u : O) := by
    rw [elementCoeff_character, unitSupplement_seven]
  have hv0 : elementCoeff (character u) sevenPrime ≠ 0 :=
    hv ▸ (u.isUnit.map ringComplex).ne_zero
  intro h
  have hunit := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff (character u) sevenPrime = 1 := by
    change (character u).residue _ = 1
    rw [h, MulChar.one_apply hunit]
  apply hu
  apply Units.ext
  apply ringComplex_injective
  simpa only [Units.val_one, map_one] using hv.symm.trans hv1

theorem masked_character_nonprincipal (u : Oˣ) (hu : u ≠ 1) (χ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff (character u) I else 0) :
    χ.residue ≠ 1 := by
  intro h
  exact character_nonprincipal u hu ((HeckeFiniteDeletion.principal_iff_of_mask χ (character u) hmask).mp h)

end HeckeUnitRows

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Set Filter
open scoped Topology
namespace HeckeMellinIdentity

def regularized (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀

theorem regularized_entire (P : WeakFEPair ℂ) : Differentiable ℂ (regularized P) := by
  unfold regularized
  have hd := P.differentiable_Λ₀
  fun_prop

theorem regularized_eq (P : WeakFEPair ℂ) (hk : P.k = 1) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) : regularized P s = s * (s-1) * P.Λ s := by
  unfold regularized WeakFEPair.Λ
  rw [hk]
  simp only [smul_eq_mul, Complex.ofReal_one]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem scaled_eq (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (A : ℝ) (hA : 0 < A)
    (hright : ∀ s : ℂ, 1 < s.re → P.Λ s = (A : ℂ)^(-s) * Q.Λ s)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    P.Λ s = (A : ℂ)^(-s) * Q.Λ s := by
  have hd : Differentiable ℂ (fun z : ℂ => (A : ℂ)^(-z) * regularized Q z) :=
    ((differentiable_id.neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))).mul (regularized_entire Q)
  have he : regularized P = fun z : ℂ => (A : ℂ)^(-z) * regularized Q z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularized_entire P)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := (2 : ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [regularized_eq P hP hz0 hz1, regularized_eq Q hQ hz0 hz1, hright z hz]
    ring
  have heq := congr_fun he s
  rw [regularized_eq P hP h0 h1, regularized_eq Q hQ h0 h1] at heq
  apply mul_left_cancel₀ (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  calc
    s * (s - 1) * P.Λ s = (A : ℂ)^(-s) * (s * (s-1) * Q.Λ s) := heq
    _ = s * (s-1) * ((A : ℂ)^(-s) * Q.Λ s) := by ring

theorem eq_of_f (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h

end HeckeMellinIdentity

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace HeckeOrigin
open HeckeFamily HeckeTheta

def poleRemoved (χ : Character) (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^s * (Complex.Gamma (s+1))⁻¹ *
    HeckeMellinIdentity.regularized (pair (coefficients χ)) s / 6

theorem poleRemoved_entire (χ : Character) : Differentiable ℂ (poleRemoved χ) := by
  have hGamma : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s+1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hGamma).mul
      (HeckeMellinIdentity.regularized_entire _)).div_const 6

theorem poleRemoved_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    poleRemoved χ s = (s-1) * LFunction χ s := by
  unfold poleRemoved LFunction continuedLattice latticeL completed
  rw [HeckeMellinIdentity.regularized_eq _ (pair_k _) h0 h1,
    Complex.Gamma_add_one s h0, mul_inv_rev]
  field_simp

theorem poleRemoved_zero (χ : Character) :
    poleRemoved χ 0 = coefficients χ (0,0) / 6 := by
  simp [poleRemoved, HeckeMellinIdentity.regularized, pair_f₀]

theorem poleRemoved_one (χ : Character) :
    poleRemoved χ 1 = HeckeReciprocal.regularizedL χ 1 := by
  rw [HeckeReciprocal.regularizedL_at_one]
  simp [poleRemoved, HeckeMellinIdentity.regularized,
    Complex.Gamma_add_one 1 one_ne_zero,
    show (pair (coefficients χ)).ε = 1 from rfl]

theorem poleRemoved_one_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    poleRemoved χ 1 ≠ 0 := by
  rw [poleRemoved_one]
  exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ

def continued (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then poleRemoved χ s / (s-1) else LFunction χ s

theorem continued_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    continued χ s = LFunction χ s := by
  unfold continued
  split_ifs
  · rw [poleRemoved_eq χ h0 h1, mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)]
  · rfl

theorem continued_differentiableAt (χ : Character) {s : ℂ}
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : DifferentiableAt ℂ (continued χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : continued χ = fun z => poleRemoved χ z / (z-1) := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact (poleRemoved_entire χ s).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (hpole.resolve_right (not_not.mpr hχ)))
  · have heq : continued χ = LFunction χ := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact ((HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6) s

theorem continued_zero (χ : Character) : continued χ 0 = -coefficients χ (0,0) / 6 := by
  by_cases hχ : χ.residue = 1
  · simp [continued, hχ, poleRemoved_zero]
    ring
  · rw [HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal χ hχ]
    simp [continued, hχ, LFunction, continuedLattice, latticeL, Complex.Gamma_zero]

end HeckeOrigin

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace HeckeBoundary

open Eisenstein Complex
open IdealEuler IdealCharacter
open HeckeIdealSeries (PrimeIdeal)
open Asymptotics Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_log_cpow_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-x : ℂ))).re +
      4 * (-log (1 - z * (n : ℂ) ^ (-(x + I * y)))).re +
      (-log (1 - z ^ 2 * (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  have hn' : (n : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz' : ‖z * (n : ℂ) ^ (-(I * y))‖ = 1 := by
    rw [norm_mul, hz, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : (0 : ℕ) < n))]
    simp
  convert! re_log_comb_nonneg (by positivity) hn' hz' using 6
  · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  · congr 2
    rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, mul_left_comm]
  · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
      mul_left_comm]

theorem summable_neg_log_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun P : PrimeIdeal => -log (1 - weighted a s P.val)) :=
  (prime_summable_norm a ha s hs).of_norm.clog_one_sub.neg

theorem exp_log_euler_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val)) = series a s := by
  have hp : HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹)
      (exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val))) :=
    (summable_neg_log_euler a ha s hs).hasSum.cexp.congr
      (fun S => Finset.prod_congr rfl (fun P _ => by
        simp only [Function.comp_apply]
        rw [exp_neg, exp_log (local_factor_ne_zero a ha s (by linarith) P)]))
  exact hp.unique (euler_hasProd a ha s hs)

def PrimeTriple (a₀ a₁ a₂ : Ideal O →*₀ ℂ) : Prop :=
  ∀ P : PrimeIdeal,
    (a₀ P.val = 0 ∧ a₁ P.val = 0 ∧ a₂ P.val = 0) ∨
    (a₀ P.val = 1 ∧ ‖a₁ P.val‖ = 1 ∧ a₂ P.val = a₁ P.val ^ 2)

theorem re_log_weighted_comb_nonneg (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) (P : PrimeIdeal) :
    0 ≤ 3 * (-log (1 - weighted a₀ (x : ℂ) P.val)).re +
      4 * (-log (1 - weighted a₁ (x + I * y) P.val)).re +
      (-log (1 - weighted a₂ (x + 2 * I * y) P.val)).re := by
  change 0 ≤ 3 * (-log (1 - a₀ P.val * normWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * normWeight (x + I * y) P.val)).re +
      (-log (1 - a₂ P.val * normWeight (x + 2 * I * y) P.val)).re
  rcases h P with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  · simp only [h₀, h₁, h₂, zero_mul, sub_zero, log_one, neg_zero, zero_re,
      mul_zero, add_zero, le_refl]
  · simp only [h₀, h₂, one_mul]
    change 0 ≤ 3 * (-log (1 - CubicEisenstein.fullIdealWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * CubicEisenstein.fullIdealWeight (x + I * y) P.val)).re +
      (-log (1 - a₁ P.val ^ 2 * CubicEisenstein.fullIdealWeight (x + 2 * I * y) P.val)).re
    simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
    exact re_log_cpow_comb_nonneg (HeckeIdealSeries.prime_norm_two_le P) hx y h₁

theorem norm_series_product_ge_one (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series a₀ (x : ℂ) ^ 3 * series a₁ (x + I * y) ^ 4 *
      series a₂ (x + 2 * I * y)‖ := by
  have hs₀ : 1 < (x : ℂ).re := hx
  have hs₁ : 1 < (x + I * y : ℂ).re := by simpa using hx
  have hs₂ : 1 < (x + 2 * I * y : ℂ).re := by simpa using hx
  have H₀ := summable_neg_log_euler a₀ ha₀ _ hs₀
  have H₁ := summable_neg_log_euler a₁ ha₁ _ hs₁
  have H₂ := summable_neg_log_euler a₂ ha₂ _ hs₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← exp_log_euler_eq_series a₀ ha₀ _ hs₀,
    ← exp_log_euler_eq_series a₁ ha₁ _ hs₁, ← exp_log_euler_eq_series a₂ ha₂ _ hs₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  exact tsum_nonneg fun P => re_log_weighted_comb_nonneg a₀ a₁ a₂ h hx y P

theorem square_unitInvariant (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : UnitInvariant M (χ ^ 2) := by
  intro u
  rw [χ.pow_apply' two_ne_zero, hχ u, one_pow]

theorem ofResidue_primeTriple (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    PrimeTriple (ofResidue M 1 (one_unitInvariant M))
      (ofResidue M χ hχ) (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) := by
  intro P
  let q := Ideal.Quotient.mk M (Submodule.IsPrincipal.generator P.val)
  have hv (ψ : MulChar (O ⧸ M) ℂ) (hψ : UnitInvariant M ψ) :
      ofResidue M ψ hψ P.val = ψ q := by
    change value M ψ P.val = _
    have hP : P.val ≠ ⊥ := P.property.ne_zero
    simp only [IdealCharacter.value, hP, ite_false, q]
  rw [hv, hv, hv]
  by_cases hq : IsUnit q
  · right
    refine ⟨MulChar.one_apply hq, ?_, χ.pow_apply' two_ne_zero q⟩
    let : Fintype (O ⧸ M)ˣ := Fintype.ofFinite _
    obtain ⟨u, hu⟩ := hq
    rw [← hu]
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using hn
  · left
    exact ⟨MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq⟩

theorem norm_residue_series_product_ge_one (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series (ofResidue M 1 (one_unitInvariant M)) (x : ℂ) ^ 3 *
      series (ofResidue M χ hχ) (x + I * y) ^ 4 *
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) (x + 2 * I * y)‖ :=
  norm_series_product_ge_one _ _ _
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ) hx y

theorem horizontal_isBigO_of_zero (F : ℂ → ℂ) (t : ℝ)
    (hF : DifferentiableAt ℂ F (1 + I * t)) (hz : F (1 + I * t) = 0) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hF.hasDerivAt
  rw [← zero_add (1 + _)] at h
  simpa only [zero_add, hz, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (h.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

theorem horizontal_isBigO_one (F : ℂ → ℂ) (t : ℝ)
    (hF : ContinuousAt F (1 + I * t)) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  rw [← zero_add (1 + _)] at hF
  exact hF.comp (f := fun x : ℝ => x + (1 + I * t)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

theorem boundary_ne_zero_of_series_eq (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) (F₀ F₁ F₂ : ℂ → ℂ)
    (hEq₀ : ∀ s : ℂ, 1 < s.re → F₀ s = series a₀ s)
    (hEq₁ : ∀ s : ℂ, 1 < s.re → F₁ s = series a₁ s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → F₂ s = series a₂ s)
    (t : ℝ)
    (hPole : (fun x : ℝ => F₀ (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x)
    (hReg₁ : DifferentiableAt ℂ F₁ (1 + I * t))
    (hReg₂ : ContinuousAt F₂ (1 + 2 * I * t)) : F₁ (1 + I * t) ≠ 0 := by
  intro hz
  have hLower (x : ℝ) (hx : 0 < x) :
      1 ≤ ‖F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t)‖ := by
    have hs₀ : 1 < (1 + x : ℂ).re := by simp; exact hx
    have hs₁ : 1 < (1 + x + I * t : ℂ).re := by simpa using hs₀
    have hs₂ : 1 < (1 + x + 2 * I * t : ℂ).re := by simpa using hs₀
    rw [hEq₀ _ hs₀, hEq₁ _ hs₁, hEq₂ _ hs₂]
    simpa only [ofReal_add, ofReal_one] using
      norm_series_product_ge_one a₀ a₁ a₂ ha₀ ha₁ ha₂ h (by linarith : 1 < 1 + x) t
  have hReg₂' : ContinuousAt F₂ (1 + I * ((2 * t : ℝ) : ℂ)) := by
    convert hReg₂ using 1
    push_cast
    ring
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by decide), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr hx), one_mul, mul_one]
  have H₀ : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx => (norm_one (α := ℝ)).symm ▸ (hLower x hx)
  have H := (hPole.pow 3).mul ((horizontal_isBigO_of_zero F₁ t hReg₁ hz).pow 4)
    |>.mul (horizontal_isBigO_one F₂ (2 * t) hReg₂')
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

section Quadratic

open UniqueFactorizationMonoid
open scoped ComplexOrder

def zetaConvolutionCoeff (a : Ideal O →*₀ ℂ) (B : Ideal O) : ℂ :=
  if B = 0 then 0 else ∑ D ∈ idealDivisors B, a D

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

@[simp] theorem zetaConvolutionCoeff_one (a : Ideal O →*₀ ℂ) :
    zetaConvolutionCoeff a 1 = 1 := by
  rw [zetaConvolutionCoeff, if_neg one_ne_zero, idealDivisors_one, Finset.sum_singleton]
  exact map_one a

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem zetaConvolutionCoeff_prime_pow (a : Ideal O →*₀ ℂ) (P : Ideal O)
    (hP : Prime P) (k : ℕ) :
    zetaConvolutionCoeff a (P ^ k) = ∑ j ∈ Finset.range (k + 1), a P ^ j := by
  rw [zetaConvolutionCoeff, if_neg (pow_ne_zero k hP.ne_zero), idealDivisors_prime_pow P hP k,
    Finset.sum_image]
  · simp only [map_pow]
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_unit hP.ne_zero hij

theorem zetaConvolutionCoeff_mul (a : Ideal O →*₀ ℂ) (B C : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsRelPrime B C) :
    zetaConvolutionCoeff a (B * C) = zetaConvolutionCoeff a B * zetaConvolutionCoeff a C := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  simp only [zetaConvolutionCoeff, hB, hC, mul_ne_zero hB hC, ite_false]
  rw [SchwartzPlanePoisson.QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem zetaConvolutionCoeff_nonneg (a : Ideal O →*₀ ℂ)
    (ha : ∀ P : Ideal O, Prime P → a P = 0 ∨ a P = 1 ∨ a P = -1)
    (B : Ideal O) : 0 ≤ zetaConvolutionCoeff a B := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => simp [zetaConvolutionCoeff]
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, zetaConvolutionCoeff_one]
    exact zero_le_one
  | hpr k hP =>
    rw [zetaConvolutionCoeff_prime_pow a _ hP k]
    rcases ha _ hP with hz | ho | hm
    · exact Finset.sum_nonneg (fun j _ => by rw [hz]; exact pow_nonneg (le_refl 0) j)
    · exact Finset.sum_nonneg (fun j _ => by rw [ho, one_pow]; exact zero_le_one)
    · rw [hm, neg_one_geom_sum]
      split_ifs <;> first | exact le_refl 0 | exact zero_le_one
  | @hcp B C hBC hB hC =>
    by_cases hB0 : B = 0
    · simp [hB0, zetaConvolutionCoeff]
    by_cases hC0 : C = 0
    · simp [hC0, zetaConvolutionCoeff]
    rw [zetaConvolutionCoeff_mul a B C hB0 hC0 hBC]
    exact mul_nonneg hB hC

theorem quadratic_normFiber_nonneg (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ HeckeIdealSeries.normFiberCoeff
      (zetaConvolutionCoeff (ofResidue M χ hχ)) n := by
  apply Finset.sum_nonneg
  intro B _
  apply zetaConvolutionCoeff_nonneg
  intro P hP
  change value M χ P = 0 ∨ value M χ P = 1 ∨ value M χ P = -1
  have hP0 : P ≠ ⊥ := hP.ne_zero
  simp only [IdealCharacter.value, hP0, ite_false]
  exact MulChar.isQuadratic_iff_sq_eq_one.mpr hquad _

theorem mulFiber_character_sum (a : Ideal O →*₀ ℂ) (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, a p.val.1) = zetaConvolutionCoeff a B := by
  let e := mulFiberDivisorEquiv B hB
  rw [zetaConvolutionCoeff, if_neg hB]
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, a D.val :=
      e.tsum_eq (fun D => a D.val)
    _ = _ := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl) a).symm

theorem zetaConvolution_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => zetaConvolutionCoeff a B * normWeight s B)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  let F : Ideal O × Ideal O → ℂ := fun p => a p.1 * normWeight s (p.1 * p.2)
  have hprod := (weighted_summable_norm a ha s hs).mul_norm
    (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  have heq (p : Ideal O × Ideal O) :
      weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 = F p := by
    change (a p.1 * normWeight s p.1) * normWeight s p.2 = _
    simp only [F, map_mul, mul_assoc]
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      zetaConvolutionCoeff a B * normWeight s B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : MulFiber B, a p.val.1) * normWeight s B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_character_sum a B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  convert hsum using 1
  calc
    _ = ∑' p : Ideal O × Ideal O,
        weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (weighted_summable_norm a ha s hs)
        (CubicEisenstein.fullIdealWeight_summable_norm s hs)
    _ = _ := tsum_congr heq

theorem zetaConvolution_normFiber_one (a : Ideal O →*₀ ℂ) :
    HeckeIdealSeries.normFiberCoeff (zetaConvolutionCoeff a) 1 = 1 := by
  have hsingle : (Ideal.finite_setOf_absNorm_eq (S := O) 1).toFinset = {1} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff.trans (by rw [Ideal.one_eq_top])
  unfold HeckeIdealSeries.normFiberCoeff
  rw [hsingle, Finset.sum_singleton, zetaConvolutionCoeff_one]

theorem zetaConvolution_LSeries_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term (HeckeIdealSeries.normFiberCoeff (zetaConvolutionCoeff a)) s)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  have h := (zetaConvolution_hasSum a ha s hs).tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // Ideal.absNorm I = n},
    zetaConvolutionCoeff a I.val * CubicEisenstein.fullIdealWeight s I.val) _ at h
  simpa only [HeckeIdealSeries.idealDirichlet_fiber] using h

theorem zetaConvolution_LSeries_eq (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (HeckeIdealSeries.normFiberCoeff (zetaConvolutionCoeff a)) s =
      series a s * CubicEisenstein.fullIdealZeta s :=
  (zetaConvolution_LSeries_hasSum a ha s hs).tsum_eq

theorem quadratic_product_positive (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hEq : ∀ s : ℂ, 1 < s.re →
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s) (y : ℝ) :
    0 < F y := by
  refine LSeries.positive_of_differentiable_of_eqOn
    (quadratic_normFiber_nonneg M χ hχ hquad)
    (zetaConvolution_normFiber_one (ofResidue M χ hχ) ▸ zero_lt_one) hF
    (x := 1) ?_ ?_ y
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => (zetaConvolution_LSeries_hasSum (ofResidue M χ hχ)
        (norm_ofResidue_le_one M χ hχ) s hs).summable)
  · intro s hs
    rw [hEq s hs, zetaConvolution_LSeries_eq (ofResidue M χ hχ)
      (norm_ofResidue_le_one M χ hχ) s hs]

/-- The trivial ideal character gives the Dedekind zeta series. -/
def trivialCharacter : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue ⊤ top_ne_bot 1 (IdealCharacter.one_unitInvariant ⊤)

theorem trivialCharacter_LFunction_eq (s : ℂ) (hs : 1 < s.re) :
    HeckeFamily.LFunction trivialCharacter s = fullIdealZeta s := by
  rw [HeckeFamily.LFunction_eq_ideal_tsum trivialCharacter hs]
  apply tsum_congr
  intro I
  unfold HeckeFamily.idealTerm HeckeFamily.idealCoeff trivialCharacter
  change IdealCharacter.ofResidue ⊤ 1 (IdealCharacter.one_unitInvariant ⊤) I /
    (I.absNorm : ℂ)^s = fullIdealWeight s I
  rw [IdealCharacter.ofResidue_one_top]
  by_cases hI : I = ⊥
  · simp only [hI, ite_true, zero_div, fullIdealWeight, Ideal.zero_eq_bot]
  · simp only [fullIdealWeight, Ideal.zero_eq_bot, hI, ite_false, Complex.cpow_neg, one_div]

/-- Clearing the simple pole uses the entire theta completion. -/
def regularizedIdealZeta : ℂ → ℂ := HeckeOrigin.poleRemoved trivialCharacter

theorem regularizedIdealZeta_differentiable : Differentiable ℂ regularizedIdealZeta :=
  HeckeOrigin.poleRemoved_entire trivialCharacter

theorem regularizedIdealZeta_eq (s : ℂ) (hs : 1 < s.re) :
    regularizedIdealZeta s = (s - 1) * fullIdealZeta s := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  rw [regularizedIdealZeta, HeckeOrigin.poleRemoved_eq trivialCharacter h0 h1,
    trivialCharacter_LFunction_eq s hs]

theorem regularizedIdealZeta_neg_two : regularizedIdealZeta (-2 : ℝ) = 0 := by
  have hΓ : Complex.Gamma ((-2 : ℝ) + 1 : ℂ) = 0 := by
    convert Complex.Gamma_neg_nat_eq_zero 1 using 1 <;> norm_num
  simp only [regularizedIdealZeta, HeckeOrigin.poleRemoved, hΓ, inv_zero,
    mul_zero, zero_mul, zero_div]

theorem differentiable_dslope_of_entire (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 c)).mpr
    hF.differentiableOn

theorem quadratic_one_ne_zero_of_regularized_zeta (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L R : ℂ → ℂ) (hL : Differentiable ℂ L) (hR : Differentiable ℂ R)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hReq : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * CubicEisenstein.fullIdealZeta s)
    (y : ℝ) (hRy : R y = 0) : L 1 ≠ 0 := by
  intro hz
  let F : ℂ → ℂ := fun s => R s * dslope L 1 s
  have hF : Differentiable ℂ F := hR.mul (differentiable_dslope_of_entire L hL 1)
  have hEq (s : ℂ) (hs : 1 < s.re) :
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s := by
    have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
    dsimp only [F]
    rw [hReq s hs, dslope_of_ne L hs1, slope, smul_eq_mul, vsub_eq_sub, hz, sub_zero,
      hLeq s hs]
    field_simp
  have hpos := quadratic_product_positive M χ hχ hquad F hF hEq y
  have hzero : F y = 0 := by simp only [F, hRy, zero_mul]
  exact hzero.not_gt hpos

theorem quadratic_one_ne_zero_of_entire (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) : L 1 ≠ 0 :=
  quadratic_one_ne_zero_of_regularized_zeta M χ hχ hquad L regularizedIdealZeta hL
    regularizedIdealZeta_differentiable hLeq regularizedIdealZeta_eq (-2)
    regularizedIdealZeta_neg_two

theorem normWeight_real_nonneg (x : ℝ) (B : Ideal O) : 0 ≤ normWeight (x : ℂ) B := by
  change 0 ≤ CubicEisenstein.fullIdealWeight (x : ℂ) B
  unfold CubicEisenstein.fullIdealWeight
  split_ifs
  · exact le_rfl
  · rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg _)]
    exact_mod_cast Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm B)) (-x)

theorem norm_series_le_norm_fullIdealZeta (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (x : ℝ) (hx : 1 < x) : ‖series a (x : ℂ)‖ ≤ ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ := by
  have hs : 1 < (x : ℂ).re := hx
  have hweight (I : Ideal O) :
      CubicEisenstein.fullIdealWeight (x : ℂ) I = (‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ : ℂ) :=
    eq_coe_norm_of_nonneg (normWeight_real_nonneg x I)
  have hnorm : ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ =
      ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ := by
    unfold CubicEisenstein.fullIdealZeta
    rw [tsum_congr hweight, ← ofReal_tsum,
      Complex.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  rw [hnorm]
  refine (norm_tsum_le_tsum_norm (weighted_summable_norm a ha _ hs)).trans ?_
  apply Summable.tsum_le_tsum _ (weighted_summable_norm a ha _ hs)
    (CubicEisenstein.fullIdealWeight_summable_norm _ hs)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight (x : ℂ) I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem fullIdealZeta_isBigO_near_one_horizontal :
    (fun x : ℝ => CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun x => (1 : ℂ) / x := by
  have hR : (fun x : ℝ => regularizedIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := by
    simpa only [ofReal_zero, mul_zero, add_zero] using horizontal_isBigO_one
      regularizedIdealZeta 0 (by simpa using (regularizedIdealZeta_differentiable 1).continuousAt)
  have hB : (fun x : ℝ => (x : ℂ) * CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := hR.congr'
    (eventually_nhdsWithin_of_forall (fun x hx => by
      dsimp only
      rw [regularizedIdealZeta_eq _ (by simpa using hx), add_sub_cancel_left]))
    (Filter.EventuallyEq.refl _ _)
  exact (isBigO_mul_iff_isBigO_div (eventually_nhdsWithin_of_forall
    (fun x hx => ofReal_ne_zero.mpr (ne_of_gt hx)))).mp hB

theorem series_isBigO_near_one_horizontal (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have h : (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0]
      fun x => CubicEisenstein.fullIdealZeta (1 + x) := by
    apply IsBigO.of_bound'
    apply eventually_nhdsWithin_of_forall
    intro x hx
    change 0 < x at hx
    simpa only [ofReal_add, ofReal_one] using
      norm_series_le_norm_fullIdealZeta a ha (1 + x) (by linarith)
  exact h.trans fullIdealZeta_isBigO_near_one_horizontal

theorem residue_boundary_ne_zero_of_series_eq (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L L₂ : ℂ → ℂ)
    (hEq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → L₂ s =
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) s)
    (t : ℝ) (hL : DifferentiableAt ℂ L (1 + I * t))
    (hL₂ : ContinuousAt L₂ (1 + 2 * I * t)) : L (1 + I * t) ≠ 0 :=
  boundary_ne_zero_of_series_eq
    (ofResidue M 1 (one_unitInvariant M)) (ofResidue M χ hχ)
    (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ))
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ)
    (series (ofResidue M 1 (one_unitInvariant M))) L L₂ (fun _ _ => rfl)
    hEq hEq₂ t
    (series_isBigO_near_one_horizontal _ (norm_ofResidue_le_one M 1 (one_unitInvariant M)))
    hL hL₂

end Quadratic

end

end HeckeBoundary

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeFamily

theorem LFunction_one_ne_zero_quadratic (χ : Character)
    (hχ : χ.residue ≠ 1) (hquad : χ.residue ^ 2 = 1) : LFunction χ 1 ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact HeckeBoundary.quadratic_one_ne_zero_of_entire χ.modulus χ.residue
    χ.unit_trivial hquad (LFunction χ) (LFunction_entire_nonprincipal χ hχ)
      (fun s hs => LFunction_eq_series χ hs)

theorem LFunction_boundary_ne_zero (χ : Character) (t : ℝ)
    (hpole : t ≠ 0 ∨ χ.residue ≠ 1)
    (hsquare : t ≠ 0 ∨ χ.residue ^ 2 ≠ 1) :
    LFunction χ (1 + Complex.I * t) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  have h1 (t : ℝ) (ht : t ≠ 0) : (1 + Complex.I * t : ℂ) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add] at hi
    exact ht hi
  have h0 (t : ℝ) : (1 + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  apply HeckeBoundary.residue_boundary_ne_zero_of_series_eq χ.modulus χ.residue
    χ.unit_trivial (LFunction χ) (LFunction (χ.power 2))
    (fun s hs => LFunction_eq_series χ hs)
    (fun s hs => LFunction_eq_series (χ.power 2) hs) t
  · apply LFunction_differentiableAt χ (h0 t)
    exact hpole.imp (h1 t) id
  · have heq : (1 + 2 * Complex.I * t : ℂ) = 1 + Complex.I * (2 * t : ℝ) := by
      push_cast
      ring
    rw [heq]
    apply DifferentiableAt.continuousAt (𝕜 := ℂ)
    apply LFunction_differentiableAt (χ.power 2) (h0 (2*t))
    rcases hsquare with ht | hsq
    · exact Or.inl (h1 (2*t) (mul_ne_zero (by norm_num) ht))
    · exact Or.inr hsq

theorem LFunction_one_ne_zero_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    LFunction χ 1 ≠ 0 := by
  by_cases hquad : χ.residue ^ 2 = 1
  · exact LFunction_one_ne_zero_quadratic χ hχ hquad
  · simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      LFunction_boundary_ne_zero χ 0 (Or.inr hχ) (Or.inr hquad)

theorem LFunction_ne_zero_of_re_eq_one (χ : Character) {s : ℂ}
    (hs : s.re = 1) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  have heq : s = 1 + Complex.I * s.im := by
    apply Complex.ext <;> simp [hs]
  by_cases ht : s.im = 0
  · have hs1 : s = 1 := by rw [heq, ht]; simp
    subst s
    exact LFunction_one_ne_zero_nonprincipal χ (hpole.resolve_left (not_not.mpr rfl))
  · rw [heq]
    exact LFunction_boundary_ne_zero χ s.im (Or.inl ht) (Or.inl ht)

theorem LFunction_ne_zero_of_one_le_re (χ : Character) {s : ℂ}
    (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  rcases eq_or_lt_of_le hs with h | h
  · exact LFunction_ne_zero_of_re_eq_one χ h.symm hpole
  · exact LFunction_ne_zero_of_one_lt_re χ h

end HeckeFamily

end

end

noncomputable section
namespace HeckeTauberian
open Real ArithmeticFunction LSeries
open scoped BigOperators

def cumsum {E : Type*} [AddCommMonoid E] (f : ℕ → E) (N : ℕ) : E :=
  ∑ n ∈ Finset.range N, f n

def nterm (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ‖f n‖ / n ^ σ

lemma nterm_eq_norm_term {f : ℕ → ℂ} {σ : ℝ} {n : ℕ} :
    nterm f σ n = ‖term f σ n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re {f : ℕ → ℂ} {n : ℕ} (s : ℂ) :
    ‖term f s n‖ = nterm f s.re n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ => rfl)
  intro h
  congr
  exact Complex.norm_natCast_cpow_of_pos (by omega) s

/-- The classical Chebyshev estimate controls the normed von Mangoldt sums. -/
theorem vonMangoldt_cheby :
    ∃ C : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N ≤ C * N := by
  refine ⟨Real.log 4 + 4, fun N => ?_⟩
  by_cases h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, Complex.norm_real, Real.norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith

end HeckeTauberian
end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical
namespace HeckeIdealSeries
private abbrev K := CyclotomicField 3 ℚ
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem orderOf_mod3_eq_two {p : ℕ} (h : p % 3 = 2) :
    orderOf (p : ZMod 3) = 2 := by
  have hc : (p : ZMod 3) = 2 :=
    (ZMod.natCast_eq_natCast_iff' p 2 3).2 (by simpa using h)
  rw [hc]
  have hdvd : orderOf (2 : ZMod 3) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 3) ^ 2 = 1)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).1 hdvd with h1 | h2
  · have h21 : (2 : ZMod 3) = 1 := orderOf_eq_one_iff.mp h1
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 1) h21)
  · exact h2

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

private theorem not_dvd_three {p : ℕ} (hp : p.Prime) (hneq : p ≠ 3) : ¬ p ∣ 3 := by
  intro hd
  have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd
  rcases h with h1 | h3
  · exact hp.ne_one h1
  · exact hneq h3

theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

theorem inert_count_of_mod_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_two hmod, gal_card_two] at hmain
  omega

theorem ramified_count :
    ((Ideal.span {(3 : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 K

theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

theorem absNorm_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 2 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_two hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf]

theorem absNorm_ramified
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfin : (Ideal.span {(3 : ℤ)}).inertiaDegIn O = 1 := by
    simpa using IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 K
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(3 : ℤ)}) P Gal(K/ℚ)]
    exact hfin
  rw [← Ideal.pow_inertiaDeg 3 P, hf, pow_one]


end HeckeIdealSeries

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical


namespace IdealMangoldt
open HeckeTauberian

open Eisenstein UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

def primeBase (I : Ideal O) : Ideal O := if h : IsPrimePow I then h.choose else 1

theorem primeBase_spec {I : Ideal O} (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  obtain ⟨k, hp, hk, heq⟩ := hI.choose_spec
  simp only [primeBase, hI, dite_true]
  exact ⟨hp, k, hk, heq⟩

theorem primeBase_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

def value (I : Ideal O) : ℝ :=
  if IsPrimePow I then Real.log (Ideal.absNorm (primeBase I)) else 0

@[simp] theorem value_zero : value (0 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_zero, ite_false]

@[simp] theorem value_one : value (1 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_one, ite_false]

theorem value_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, if_pos (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg (I : Ideal O) : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, if_pos hI]
    apply Real.log_nonneg
    exact_mod_cast (HeckeIdealSeries.prime_norm_two_le ⟨_, (primeBase_spec hI).1⟩).trans' (by decide : 1 ≤ 2)
  · simp only [value, hI, ite_false, le_refl]

theorem isPrimePow_absNorm {I : Ideal O} (hI : IsPrimePow I) :
    IsPrimePow (Ideal.absNorm I) := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨p, n, hn, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  rw [map_pow, hnorm, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨p, n * k, hp, mul_pos hn hk, rfl⟩

theorem value_eq_zero_of_norm_not_primePow {I : Ideal O}
    (hI : ¬IsPrimePow (Ideal.absNorm I)) : value I = 0 := by
  exact if_neg (fun h => hI (isPrimePow_absNorm h))

theorem prime_mem_primesOver_of_dvd_norm {P : Ideal O} (hP : Prime P)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm P) :
    P ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hd
  have heq : P = Q := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero |>.eq_of_le
    hQ.ne_top (Ideal.dvd_iff_le.mp hQP)
  subst Q
  exact ⟨Ideal.isPrime_of_prime hP, ⟨hQu.symm⟩⟩

theorem primeBase_mem_primesOver {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {I : Ideal O} (hI : IsPrimePow I) (hn : Ideal.absNorm I = p ^ k) :
    primeBase I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨hP, l, hl, heq⟩ := primeBase_spec hI
  apply prime_mem_primesOver_of_dvd_norm hP hp
  apply hp.dvd_of_dvd_pow
  have hnorm := congrArg Ideal.absNorm heq
  rw [map_pow, hn] at hnorm
  rw [hnorm]
  exact dvd_pow_self _ hk.ne'

theorem primeBase_injective_on_norm {I J : Ideal O} (hI : IsPrimePow I)
    (hJ : IsPrimePow J) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (hbase : primeBase I = primeBase J) : I = J := by
  obtain ⟨hP, k, hk, hPk⟩ := primeBase_spec hI
  obtain ⟨_, l, hl, hPl⟩ := primeBase_spec hJ
  rw [← hbase] at hPl
  have hkl : k = l := by
    apply Nat.pow_right_injective (HeckeIdealSeries.prime_norm_two_le ⟨_, hP⟩)
    have hnI : Ideal.absNorm (primeBase I) ^ k = Ideal.absNorm I := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPk
    have hnJ : Ideal.absNorm (primeBase I) ^ l = Ideal.absNorm J := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPl
    exact hnI.trans (hn.trans hnJ.symm)
  exact hPk.symm.trans ((congrArg (primeBase I ^ ·) hkl).trans hPl)

def normFiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOf_absNorm_eq (S := O) n).toFinset

@[simp] theorem mem_normFiber (n : ℕ) (I : Ideal O) : I ∈ normFiber n ↔ Ideal.absNorm I = n :=
  (Ideal.finite_setOf_absNorm_eq (S := O) n).mem_toFinset

def coeff (w : Ideal O → ℝ) (n : ℕ) : ℝ := ∑ I ∈ normFiber n, w I * value I

theorem coeff_nonneg (w : Ideal O → ℝ) (hw : ∀ I, 0 ≤ w I) (n : ℕ) :
    0 ≤ coeff w n :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (hw I) (value_nonneg I))

theorem coeff_le_unweighted (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ coeff (fun _ => 1) n := by
  apply Finset.sum_le_sum
  intro I hI
  exact mul_le_mul_of_nonneg_right (hw I) (value_nonneg I)

theorem coeff_eq_sum_primePowers (n : ℕ) :
    coeff (fun _ => 1) n =
      ∑ I ∈ (normFiber n).filter IsPrimePow, Real.log (Ideal.absNorm (primeBase I)) := by
  simp only [coeff, one_mul, value, Finset.sum_filter]

theorem coeff_eq_zero_of_not_primePow {n : ℕ} (hn : ¬IsPrimePow n)
    (w : Ideal O → ℝ) : coeff w n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  rw [value_eq_zero_of_norm_not_primePow (by simpa only [(mem_normFiber n I).mp hI] using hn),
    mul_zero]

def primesOver (p : ℕ) [Fact p.Prime] : Finset (Ideal O) :=
  (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) O).toFinset

@[simp] theorem mem_primesOver (p : ℕ) [Fact p.Prime] (P : Ideal O) :
    P ∈ primesOver p ↔ P ∈ (Ideal.span {(p : ℤ)}).primesOver O :=
  (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) O).mem_toFinset

theorem primesOver_card (p : ℕ) [Fact p.Prime] :
    (primesOver p).card = ((Ideal.span {(p : ℤ)}).primesOver O).ncard := by
  exact (Set.ncard_eq_toFinset_card _).symm

theorem primesOver_log_sum_le (p : ℕ) [hp : Fact p.Prime] :
    ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) ≤ 2 * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.out.one_lt.le)
  by_cases h1 : p % 3 = 1
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [HeckeIdealSeries.absNorm_split hp.out h1 P]
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      HeckeIdealSeries.split_count_of_mod_one hp.out h1]
    norm_num
  by_cases h2 : p % 3 = 2
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = 2 * Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [HeckeIdealSeries.absNorm_inert hp.out h2 P, Nat.cast_pow, Real.log_pow]
      norm_num
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      HeckeIdealSeries.inert_count_of_mod_two hp.out h2]
    norm_num
  have h3 : p = 3 := by
    have h0 : p % 3 = 0 := by have := Nat.mod_lt p (by decide : 0 < 3); omega
    have h := (Nat.dvd_prime hp.out).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  subst p
  have hv (P : Ideal O) (hP : P ∈ primesOver 3) :
      Real.log (Ideal.absNorm P) = Real.log 3 := by
    have hPP := (mem_primesOver 3 P).mp hP
    let : P.IsPrime := hPP.1
    let : P.LiesOver (Ideal.span {(3 : ℤ)}) := hPP.2
    rw [HeckeIdealSeries.absNorm_ramified P]
    norm_num
  rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card]
  norm_num only [Nat.cast_ofNat]
  rw [HeckeIdealSeries.ramified_count]
  norm_num only [Nat.cast_one, one_mul, Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem coeff_prime_pow_le (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    coeff (fun _ => 1) (p ^ k) ≤ 2 * Real.log p := by
  rw [coeff_eq_sum_primePowers]
  let S := (normFiber (p ^ k)).filter IsPrimePow
  have hS (I : Ideal O) (hI : I ∈ S) : IsPrimePow I ∧ Ideal.absNorm I = p ^ k :=
    ⟨(Finset.mem_filter.mp hI).2, (mem_normFiber _ I).mp (Finset.mem_filter.mp hI).1⟩
  have hinj : Set.InjOn primeBase (↑S : Set (Ideal O)) := by
    intro I hI J hJ heq
    exact primeBase_injective_on_norm (hS I hI).1 (hS J hJ).1
      ((hS I hI).2.trans (hS J hJ).2.symm) heq
  have hsub : S.image primeBase ⊆ primesOver p := by
    intro P hP
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hP
    exact (mem_primesOver p _).mpr (primeBase_mem_primesOver hp.out hk (hS I hI).1 (hS I hI).2)
  calc
    _ = ∑ P ∈ S.image primeBase, Real.log (Ideal.absNorm P) := (Finset.sum_image hinj).symm
    _ ≤ ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro P hP _
      have hPP := (mem_primesOver p P).mp hP
      have hprime : Prime P := Ideal.prime_of_mem_primesOver
        (by simpa using (show (p : ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)) hPP
      exact Real.log_nonneg (by exact_mod_cast
        (HeckeIdealSeries.prime_norm_two_le ⟨P, hprime⟩).trans' (by decide : 1 ≤ 2))
    _ ≤ _ := primesOver_log_sum_le p

theorem coeff_le_two_vonMangoldt (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ 2 * vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let : Fact p.Prime := ⟨hp⟩
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    exact (coeff_le_unweighted w hw _).trans (coeff_prime_pow_le p hk)
  · rw [coeff_eq_zero_of_not_primePow hn, vonMangoldt_eq_zero_iff.mpr hn, mul_zero]

theorem coeff_chebyshev (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) :
    ∃ C : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(coeff w n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨2 * C, fun N => ?_⟩
  calc
    _ ≤ 2 * cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N := by
      unfold cumsum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
        using coeff_le_two_vonMangoldt w hw1 n
    _ ≤ 2 * (C * N) := mul_le_mul_of_nonneg_left (hC N) (by norm_num)
    _ = _ := by ring

theorem coeff_summable_nterm (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (coeff w n : ℂ)) σ) := by
  have hs : Summable (nterm (fun n => (vonMangoldt n : ℂ)) σ) := by
    simpa only [← nterm_eq_norm_term] using
      (@ArithmeticFunction.LSeriesSummable_vonMangoldt (σ : ℂ) (by simpa using hσ)).norm
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro n
    exact ite_nonneg (by positivity) (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
  · intro n
    by_cases hn : n = 0
    · simp only [nterm, hn, ite_true, mul_zero, le_refl]
    · simp only [nterm, hn, ite_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (coeff_le_two_vonMangoldt w hw1 n)
        (Real.rpow_nonneg (by positivity) _)

theorem coeff_LSeriesSummable (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff w n : ℂ)) s := by
  apply Summable.of_norm
  simpa only [norm_term_eq_nterm_re] using coeff_summable_nterm w hw0 hw1 hs

def classCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  coeff (fun I => if I ∈ C then 1 else 0) n

theorem classCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ classCoeff C n :=
  coeff_nonneg _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_le_two_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n ≤ 2 * vonMangoldt n :=
  coeff_le_two_vonMangoldt _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(classCoeff C n : ℂ)‖) N ≤ B * N :=
  coeff_chebyshev _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num)

theorem classCoeff_summable_nterm (C : Set (Ideal O)) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (classCoeff C n : ℂ)) σ) :=
  coeff_summable_nterm _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num) hσ

end

end IdealMangoldt

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical


namespace IdealLogDerivative

open Eisenstein UniqueFactorizationMonoid IdealEuler
open scoped BigOperators Classical Topology

noncomputable section

def coeff (a : Ideal O →*₀ ℂ) (n : ℕ) : ℂ :=
  HeckeIdealSeries.normFiberCoeff (fun I => (IdealMangoldt.value I : ℂ) * a I) n

theorem norm_coeff_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ IdealMangoldt.coeff (fun _ => 1) n := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg I), one_mul]
  exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg I) (ha I)

theorem norm_coeff_le_two_vonMangoldt (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ 2 * ArithmeticFunction.vonMangoldt n :=
  (norm_coeff_le a ha n).trans
    (IdealMangoldt.coeff_le_two_vonMangoldt (fun _ => 1) (fun _ => le_refl _) n)

theorem coeff_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (coeff a) s := by
  apply Summable.of_norm
  have h := (IdealMangoldt.coeff_LSeriesSummable (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_refl _) hs).norm
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.coeff_nonneg (fun _ => 1) (fun _ => zero_le_one) n)]
    using norm_coeff_le a ha n

theorem primePow_coprime_factor {B C : Ideal O} (h : IsPrimePow (B * C))
    (hBC : IsRelPrime B C) : B = 1 ∨ C = 1 := by
  obtain ⟨P, k, hP, hk, heq⟩ := h
  obtain ⟨i, hi, hBi⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_right B C)
  obtain ⟨j, hj, hCj⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_left C B)
  have hB := associated_iff_eq.mp hBi
  have hC := associated_iff_eq.mp hCj
  by_cases hi0 : i = 0
  · left; simpa only [hi0, pow_zero] using hB
  by_cases hj0 : j = 0
  · right; simpa only [hj0, pow_zero] using hC
  exact (hP.not_unit (hBC (hB ▸ dvd_pow_self P hi0) (hC ▸ dvd_pow_self P hj0))).elim

theorem value_mul_coprime {B C : Ideal O} (hBC : IsRelPrime B C) :
    IdealMangoldt.value (B * C) =
      (if C = 1 then IdealMangoldt.value B else 0) +
      (if B = 1 then IdealMangoldt.value C else 0) := by
  by_cases hB : B = 1
  · subst B
    simp only [one_mul, IdealMangoldt.value_one, ite_self, ite_true, zero_add]
  by_cases hC : C = 1
  · subst C
    simp only [mul_one, IdealMangoldt.value_one, ite_self, ite_true, add_zero]
  have hnot : ¬IsPrimePow (B * C) := by
    intro h
    exact (primePow_coprime_factor h hBC).elim hB hC
  simp only [IdealMangoldt.value, hnot, hB, hC, ite_false, zero_add]

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem sum_value_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (∑ D ∈ idealDivisors (P ^ k), (IdealMangoldt.value D : ℂ)) =
      k * (Real.log (Ideal.absNorm P) : ℂ) := by
  rw [idealDivisors_prime_pow P hP k, Finset.sum_image]
  · induction k with
    | zero => simp only [Nat.zero_add, Finset.sum_range_one, pow_zero,
        IdealMangoldt.value_one, Complex.ofReal_zero, Nat.cast_zero, zero_mul]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, IdealMangoldt.value_pow hP (Nat.succ_pos k)]
      push_cast
      ring
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_unit hP.ne_zero hij

theorem sum_value_mul (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsRelPrime B C) :
    (∑ D ∈ idealDivisors (B * C), (IdealMangoldt.value D : ℂ)) =
      (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) +
      ∑ D ∈ idealDivisors C, (IdealMangoldt.value D : ℂ) := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  have h1B : (1 : Ideal O) ∈ idealDivisors B := (mem_idealDivisors hB).mpr (one_dvd _)
  have h1C : (1 : Ideal O) ∈ idealDivisors C := (mem_idealDivisors hC).mpr (one_dvd _)
  rw [SchwartzPlanePoisson.QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  calc
    _ = ∑ D ∈ idealDivisors B, ∑ E ∈ idealDivisors C,
        ((if E = 1 then (IdealMangoldt.value D : ℂ) else 0) +
        (if D = 1 then (IdealMangoldt.value E : ℂ) else 0)) := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      rw [value_mul_coprime ((hBC.of_dvd_left ((mem_idealDivisors hB).mp hD)).of_dvd_right
        ((mem_idealDivisors hC).mp hE)), Complex.ofReal_add]
      split_ifs <;> rfl
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
        Finset.sum_ite_eq', if_pos h1C, if_pos h1B, Finset.sum_const_zero]

theorem sum_value_divisors (B : Ideal O) (hB : B ≠ 0) :
    (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact (hB rfl).elim
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, idealDivisors_one, Finset.sum_singleton]
    simp only [IdealMangoldt.value_one, map_one, Nat.cast_one, Real.log_one]
  | hpr k hP =>
    rw [sum_value_prime_pow _ hP k, map_pow, Nat.cast_pow, Real.log_pow]
    push_cast
    rfl
  | @hcp B C hBC ihB ihC =>
    have hB0 : B ≠ 0 := left_ne_zero_of_mul hB
    have hC0 : C ≠ 0 := right_ne_zero_of_mul hB
    rw [sum_value_mul B C hB0 hC0 hBC, ihB hB0, ihC hC0, map_mul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hB0))
        (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hC0)), Complex.ofReal_add]

theorem value_le_log_norm (B : Ideal O) :
    IdealMangoldt.value B ≤ Real.log (Ideal.absNorm B) := by
  by_cases h : IsPrimePow B
  · obtain ⟨P, k, hP, hk, rfl⟩ := h
    rw [IdealMangoldt.value_pow hP hk, map_pow, Nat.cast_pow, Real.log_pow]
    apply le_mul_of_one_le_left
    · exact Real.log_natCast_nonneg _
    · exact_mod_cast hk
  · rw [IdealMangoldt.value, if_neg h]
    exact Real.log_natCast_nonneg _

theorem weighted_eq_term (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    weighted a s B = LSeries.term (fun _ => a B) s (Ideal.absNorm B) := by
  by_cases hB : B = 0
  · subst B
    simp only [map_zero, LSeries.term_zero]
  · have hn : Ideal.absNorm B ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
    change a B * CubicEisenstein.fullIdealWeight s B = _
    simp only [CubicEisenstein.fullIdealWeight, hB, ite_false,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem weighted_hasDerivAt (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    HasDerivAt (fun z => weighted a z B)
      (-((Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)) s := by
  simp_rw [weighted_eq_term]
  convert LSeries.hasDerivAt_term (fun _ => a B) (Ideal.absNorm B) s using 1
  by_cases hn : Ideal.absNorm B = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  · simp only [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.natCast_log,
      mul_div_assoc]

theorem log_weighted_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => (Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)
      (-deriv (series a) s) := by
  obtain ⟨x, hx, hxs⟩ := exists_between hs
  have hu := weighted_summable_norm a ha (x : ℂ) (by simpa using hx)
  have hd (B : Ideal O) : DifferentiableOn ℂ (fun z => weighted a z B) {z : ℂ | x < z.re} :=
    fun z _ => (weighted_hasDerivAt a z B).differentiableAt.differentiableWithinAt
  have hU : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbound (B : Ideal O) (z : ℂ) (hz : z ∈ {z : ℂ | x < z.re}) :
      ‖weighted a z B‖ ≤ ‖weighted a (x : ℂ) B‖ := by
    simp only [weighted_eq_term]
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hz.le) _
  have H := Complex.hasSum_deriv_of_summable_norm hu hd hU hbound hxs
  simp_rw [(weighted_hasDerivAt a s _).deriv] at H
  unfold IdealEuler.series
  simpa only [neg_neg] using H.neg

theorem mangoldt_weighted_summable_norm (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun B : Ideal O => ‖(IdealMangoldt.value B : ℂ) * weighted a s B‖) := by
  apply (log_weighted_hasSum a ha s hs).summable.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro B
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg B), abs_of_nonneg (Real.log_natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (value_le_log_norm B) (norm_nonneg _)

theorem mangoldt_series_eq_LSeries (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * weighted a s B) = LSeries (coeff a) s := by
  have H := (mangoldt_weighted_summable_norm a ha s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' B : {B : Ideal O // Ideal.absNorm B = n},
    (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) _ at H
  have hf (n : ℕ) : (∑' B : {B : Ideal O // Ideal.absNorm B = n},
      (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) = LSeries.term (coeff a) s n := by
    unfold coeff
    simpa only [weighted, normWeight,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_assoc]
      using HeckeIdealSeries.idealDirichlet_fiber
        (fun B => (IdealMangoldt.value B : ℂ) * a B) s n
  simp_rw [hf] at H
  exact H.tsum_eq.symm

theorem mulFiber_value_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  let e := mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, (IdealMangoldt.value D.val : ℂ) :=
      e.tsum_eq (fun D => (IdealMangoldt.value D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (IdealMangoldt.value D : ℂ))).symm
    _ = _ := sum_value_divisors B hB

theorem coeff_LSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s * series a s = -deriv (series a) s := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (IdealMangoldt.value p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (mangoldt_weighted_summable_norm a ha s hs).mul_norm
    (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      (Real.log (Ideal.absNorm B) : ℂ) * f B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_value_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * f B) * ∑' B : Ideal O, f B := by
      rw [mangoldt_series_eq_LSeries a ha s hs]
      rfl
    _ = ∑' p : Ideal O × Ideal O, ((IdealMangoldt.value p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (mangoldt_weighted_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = -deriv (series a) s := hsum.unique (log_weighted_hasSum a ha s hs)

theorem coeff_LSeries_eq_neg_logDeriv (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv (series a) s / series a s := by
  apply (eq_div_iff (series_ne_zero a ha s hs)).mpr
  exact coeff_LSeries_mul_series a ha s hs

theorem coeff_LSeries_eq_neg_logDeriv_of_eq (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 1 < z.re → F z = series a z)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv F s / F s := by
  have hd : deriv F s = deriv (series a) s := by
    apply Filter.EventuallyEq.deriv_eq
    have hU : {z : ℂ | 1 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    exact hF z hz
  rw [hd, hF s hs]
  exact coeff_LSeries_eq_neg_logDeriv a ha s hs

end
end IdealLogDerivative

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical


noncomputable section
open scoped Classical Topology
namespace HeckeLogDerivative
open HeckeFamily

def coeff (χ : Character) : ℕ → ℂ := IdealLogDerivative.coeff (idealCoeff χ)

theorem coeff_LSeries_eq (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = -deriv (LFunction χ) s / LFunction χ s :=
  IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _ (idealCoeff_norm_le_one χ)
    (LFunction χ) (fun _ hz => LFunction_eq_series χ hz) s hs

def poleSubtracted (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then
    -deriv (HeckeOrigin.poleRemoved χ) s / HeckeOrigin.poleRemoved χ s
  else -deriv (LFunction χ) s / LFunction χ s

theorem poleRemoved_ne_zero_boundary (χ : Character) (hχ : χ.residue = 1)
    {s : ℂ} (hs : 1 ≤ s.re) : HeckeOrigin.poleRemoved χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact HeckeOrigin.poleRemoved_one_ne_zero χ hχ
  · rw [HeckeOrigin.poleRemoved_eq χ (by intro h; norm_num [h] at hs) h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (LFunction_ne_zero_of_one_le_re χ hs (Or.inl h1))

theorem poleSubtracted_analyticAt (χ : Character) {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (poleSubtracted χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : poleSubtracted χ = fun z =>
        -deriv (HeckeOrigin.poleRemoved χ) z / HeckeOrigin.poleRemoved χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (HeckeOrigin.poleRemoved_entire χ).analyticAt s
    exact ha.deriv.neg.div ha (poleRemoved_ne_zero_boundary χ hχ hs)
  · have heq : poleSubtracted χ = fun z => -deriv (LFunction χ) z / LFunction χ z := by
      funext z
      simp [poleSubtracted, hχ]
    rw [heq]
    have ha := (LFunction_entire_nonprincipal χ hχ).analyticAt s
    exact ha.deriv.neg.div ha (LFunction_ne_zero_of_one_le_re χ hs (Or.inr hχ))

theorem poleSubtracted_continuousOn (χ : Character) :
    ContinuousOn (poleSubtracted χ) {s : ℂ | 1 ≤ s.re} :=
  fun _ hs => (poleSubtracted_analyticAt χ hs).continuousAt.continuousWithinAt

theorem poleRemoved_deriv (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    deriv (HeckeOrigin.poleRemoved χ) s = LFunction χ s + (s-1)*deriv (LFunction χ) s := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have heq : HeckeOrigin.poleRemoved χ =ᶠ[nhds s] (fun z => (z-1)*LFunction χ z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact HeckeOrigin.poleRemoved_eq χ
      (by intro h; norm_num [h] at hz) (by intro h; norm_num [h] at hz)
  rw [heq.deriv_eq]
  have hd := (LFunction_differentiableAt χ h0 (Or.inl h1)).hasDerivAt
  have hh := ((hasDerivAt_id s).sub_const 1 |>.mul hd).deriv
  have hfun : ((fun x : ℂ => id x - 1) * LFunction χ) =
      (fun z => (z-1)*LFunction χ z) := rfl
  rw [hfun] at hh
  simpa only [one_mul, id_eq] using hh

theorem coeff_LSeries_eq_poleSubtracted (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = (if χ.residue = 1 then (1 : ℂ)/(s-1) else 0) +
      poleSubtracted χ s := by
  rw [coeff_LSeries_eq χ hs]
  by_cases hχ : χ.residue = 1
  · simp only [hχ, ite_true, poleSubtracted]
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    rw [poleRemoved_deriv χ hs, HeckeOrigin.poleRemoved_eq χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs
    field_simp
    ; ring
  · simp [poleSubtracted, hχ]

end HeckeLogDerivative

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
