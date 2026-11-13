/-
Active supports adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.CompleteCommonParts
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.FiniteSexticRows

/-!
# Active supports

Net exponents and principal and active supports; physical slot coefficients and interpolated
profiles of the detector dictionary; the second diagonal zero energy and old mask radicals.
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
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentActive
open Eisenstein CompletedGauss 
open CanonicalRowCompletion CenteredMomentCanonical

/-- The coprimality mask vanishes exactly on the union of the selected primes. -/
lemma rowCoprimeMask_ideal_indicator {ι : Type*} (P : ι → Ideal O)
    (B : Finset ι) (z : O) :
    rowCoprimeMask P B z = if ∃ i ∈ B, z ∈ P i then 0 else 1 := by
  rw [TruncatedPrincipalPoisson.rowCoprimeMask, primeCoprimeMask_indicator]
  simp only [← Ideal.mem_span_singleton, span_cubicIdealGenerator]
  by_cases h : ∃ i ∈ B, z ∈ P i
  · obtain ⟨i, hi, hz⟩ := h
    rw [if_neg (fun hn => hn i hi hz), if_pos ⟨i, hi, hz⟩]
  · rw [if_pos (by simpa only [not_exists, not_and] using h), if_neg h]

def netExponent (c d : ℕ) : ℕ := (c + 5 * d) % 6

theorem local_pair_reduction (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (c d : ℕ) (x : O ⧸ P) :
    (complexSexticChar P hg ^ c) x * star ((complexSexticChar P hg ^ d) x) =
      (complexSexticChar P hg ^ netExponent c d) x := by
  have h6 : complexSexticChar P hg ^ 6 = 1 := by
    rw [← complexSexticChar_order_six P hg hchar]
    exact pow_orderOf_eq_one _
  have h5 : complexSexticChar P hg ^ 5 = (complexSexticChar P hg)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using h6
  rw [MulChar.star_apply', ← MulChar.mul_apply]
  congr 1
  unfold netExponent
  rw [← complexSexticChar_order_six P hg hchar, pow_mod_orderOf,
    pow_add, pow_mul, h5, inv_pow]

def activeSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) ≠ 0)

def principalSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) = 0)

theorem netExponent_ne_zero {ι : Type*} (B : Finset ι) (c d : ι → ℕ)
    (i : activeSupport B c d) : netExponent (c i.val) (d i.val) ≠ 0 :=
  (Finset.mem_filter.mp i.property).2

theorem netExponent_lt_six (c d : ℕ) : netExponent c d < 6 := Nat.mod_lt _ (by decide)

theorem principal_product_eq_mask {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) (z : O) :
    (∏ i ∈ B, (1 : MulChar (O ⧸ P i) ℂ) (Ideal.Quotient.mk (P i) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ i ∈ B, z ∈ P i
  · rw [rowCoprimeMask_ideal_indicator, if_pos h]
    obtain ⟨i, hi, hz⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask_ideal_indicator, if_neg h]
    apply Finset.prod_eq_one
    intro i hi
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

variable {ι : Type*}

theorem common_ideal_pair_active (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0) (z : O) :
    idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) =
      rowCoprimeMask P (principalSupport B c d) z *
        finiteSexticRow (fun i : activeSupport B c d => P i.val)
          (fun i => hg i.val) (fun i => netExponent (c i.val) (d i.val)) z := by
  let f := fun i => (complexSexticChar (P i) (hg i) ^ netExponent (c i) (d i))
    (Ideal.Quotient.mk (P i) z)
  have hlocal : idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) = ∏ i ∈ B, f i := by
    simp only [map_prod, map_pow, star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [idealRowHom_prime z (P i) (hg i),
      ← MulChar.pow_apply' _ (hc i hi), ← MulChar.pow_apply' _ (hd i hi)]
    exact local_pair_reduction (P i) (hg i) (hchar i) (c i) (d i) _
  have hzero : (∏ i ∈ B.filter (fun i => netExponent (c i) (d i) = 0), f i) =
      rowCoprimeMask P (principalSupport B c d) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    simp only [f, he, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B
    (fun i => netExponent (c i) (d i) = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := activeSupport B c d) (f := f)).symm

theorem activePrimes_pairwise_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B : Finset ι) (c d : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i : activeSupport B c d => P i.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))

theorem active_gauss_norm (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ) :
    ‖canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
      (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))‖ = 1 :=
  norm_canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun _i => netExponent_lt_six _ _)

open  SchwartzPlanePoisson

theorem common_ideal_pair_poisson (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let Q := fun i : activeSupport B c d => P i.val
    let row := finiteSexticRow Q (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))
    let r := finitePrimeModulus Q
    (∑' z : O, (idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
      W (‖ringComplex z‖ ^ 2 / K)) =
      ((K : ℂ) * canonicalNormalizedGauss Q
        (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
        (fun i => netExponent (c i.val) (d i.val)) / (‖ringComplex r‖ : ℂ)) *
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
          (‖ringComplex e‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (K * ‖ringComplex h‖ ^ 2 / (‖ringComplex e‖ ^ 2 * ‖ringComplex r‖ ^ 2)) := by
  simp_rw [common_ideal_pair_active P hg hchar B c d hc hd]
  exact canonical_masked_radial_poisson_collected P hinj (principalSupport B c d)
    (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun i => netExponent_lt_six _ _) W K hK

end CenteredMomentActive
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical
local notation "O" => Eisenstein.O
namespace CenteredMomentPrimitive
open Eisenstein CompletedGauss  
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

def primitiveCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    MulChar (Residue (finitePrimeModulus P)) ℂ :=
  crtCharacter ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
    (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => complexSexticChar (P i) (hg i) ^ j i)

theorem primitiveCharacter_apply {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) (x : Residue (finitePrimeModulus P)) :
    primitiveCharacter P hcop hg j x =
      principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x := rfl

@[simp] theorem primitiveCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) (x : O) :
    primitiveCharacter P hcop hg j (Ideal.Quotient.mk _ x) =
      finiteSexticRow P hg j x := by
  exact (primitiveCharacter_apply P hcop hg j _).trans
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x)

theorem primitive_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    CenteredMomentFourier.residueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h) =
      star (finiteSexticRow P hg j h) * canonicalGaussSum P hcop hg j := by
  let r := finitePrimeModulus P
  let := finiteEisensteinQuotientOfNonzero (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue r) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (Residue r) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  simp only [CenteredMomentFourier.residueGauss, tsum_fintype, primitiveCharacter_apply]
  rw [canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6
    (finitePrimeModulus P) (span_finitePrimeModulus P)]
  exact congrArg (fun z : ℂ => star z * canonicalGaussSum P hcop hg j)
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) h)

lemma sqrt_absNorm (r : O) :
    Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) = ‖ringComplex r‖ := by
  rw [← ringComplex_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

theorem normalized_primitive_gauss_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    ‖normalizedResidueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h)‖ ≤ 1 := by
  rw [normalizedResidueGauss, primitive_gauss_transform P hcop hg hchar j hj0 hj6,
    sqrt_absNorm, mul_div_assoc]
  change ‖star (finiteSexticRow P hg j h) * canonicalNormalizedGauss P hcop hg j‖ ≤ 1
  rw [norm_mul, norm_star, norm_canonicalNormalizedGauss P hcop hg hchar j hj0 hj6, mul_one]
  exact SchwartzPlanePoisson.finiteSexticRow_norm_le_one P hg j h

end CenteredMomentPrimitive
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentBridge
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson

def productCharacter (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) :
    MulChar (Residue (a * b)) ℂ where
  toFun x := χa ((principalCRT a b hcop x).1) * χb ((principalCRT a b hcop x).2)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul]; ring
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (principalCRT a b hcop x) := fun h =>
      hx ((isUnit_map_iff (principalCRT a b hcop) x).mp h)
    rw [Prod.isUnit_iff] at hn
    by_cases h : IsUnit (principalCRT a b hcop x).1
    · rw [χb.map_nonunit (fun hb => hn ⟨h, hb⟩), mul_zero]
    · rw [χa.map_nonunit h, zero_mul]

theorem productCharacter_apply (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : Residue (a * b)) :
    productCharacter a b hcop χa χb x =
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [productCharacter, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    principalCRT_mk, frequencyReduction_mk]

@[simp] theorem productCharacter_mk (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : O) :
    productCharacter a b hcop χa χb (Ideal.Quotient.mk _ x) =
      χa (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x) := by
  rw [productCharacter_apply, frequencyReduction_mk, frequencyReduction_mk]

theorem productCharacter_gauss (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    CenteredMomentFourier.residueGauss (a * b) (mul_ne_zero ha hb) (productCharacter a b hcop χa χb) h =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        CenteredMomentFourier.residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        CenteredMomentFourier.residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let := finiteEisensteinQuotientOfNonzero ha
  let := finiteEisensteinQuotientOfNonzero hb
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  simpa only [CenteredMomentFourier.residueGauss, tsum_fintype, productCharacter_apply] using
    coprime_character_fourier a b ha hb hcop χa χb h

theorem triple_pair_gauss (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (j : O) :
    CenteredMomentFourier.residueGauss (r * (a * b)) (mul_ne_zero hr (mul_ne_zero ha hb))
      (productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹))
      (Ideal.Quotient.mk _ j) =
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      (CenteredMomentFourier.residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        CenteredMomentFourier.residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (CenteredMomentFourier.residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
  let := finiteEisensteinQuotientOfNonzero hb
  rw [productCharacter_gauss r (a * b) hr (mul_ne_zero ha hb),
    frequencyReduction_mk, frequencyReduction_mk,
    productCharacter_mk, productCharacter_gauss a b ha hb, frequencyReduction_mk,
    frequencyReduction_mk, residueGauss_inverse, ← map_neg]
  simp only [map_mul, star_mul, MulChar.star_apply']
  ring

theorem triple_pair_poisson (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖ringComplex z‖ ^ 2 / K)) =
      ((K / ‖ringComplex (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (CenteredMomentFourier.residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        CenteredMomentFourier.residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (CenteredMomentFourier.residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finiteEisensteinQuotientOfNonzero hm
  let := finiteEisensteinQuotientOfNonzero hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) =
      ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z)) := by
    simp only [χ, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hp := actual_radial_poisson_trace W K hK (r * (a * b)) hm χ
  change (∑' z : O, χ (Ideal.Quotient.mk _ z) * W (‖ringComplex z‖ ^ 2 / K)) =
    (K / ‖ringComplex (r * (a * b))‖ ^ 2 : ℝ) •
    ∑' j : O, (∑ x : Residue (r * (a * b)),
      χ x * primitiveTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) *
      paperRadialFourier W
        (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (r * (a * b))‖ ^ 2) at hp
  simp only [hχ] at hp
  rw [hp]
  have hcoeff (j : O) : (∑ x : Residue (r * (a * b)),
      χ x * primitiveTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) =
      CenteredMomentFourier.residueGauss (r * (a * b)) hm χ (Ideal.Quotient.mk _ j) := by
    simp only [CenteredMomentFourier.residueGauss, tsum_fintype]
  simp_rw [hcoeff]
  simp_rw [χ, triple_pair_gauss r a b hr ha hb hrab hab ξ χa χb]
  simp_rw [mul_assoc, tsum_mul_left]
  rw [Complex.real_smul]

theorem masked_triple_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι)
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, rowCoprimeMask P S z *
      (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z))) * W (‖ringComplex z‖ ^ 2 / K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖ringComplex e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖ringComplex (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (CenteredMomentFourier.residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
          CenteredMomentFourier.residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (CenteredMomentFourier.residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖ringComplex j‖ ^ 2 / ‖ringComplex (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finiteEisensteinQuotientOfNonzero hm
  let := finiteEisensteinQuotientOfNonzero hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  let row := fun z : O => ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
    star (χb (Ideal.Quotient.mk _ z))
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) = row z := by
    simp only [χ, row, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hsum : Summable (fun z : O => row z * W (‖ringComplex z‖ ^ 2 / K)) := by
    have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
      (Ideal.Quotient.mk (Ideal.span {r * (a * b)})) χ
    simpa only [hχ, scaledRadialTest_apply] using hs
  have hmul (x y : O) : row (x * y) = row x * row y := by
    simp only [row, map_mul, star_mul]
    ring
  rw [tsum_masked_radial_dilations P hinj S row hmul W K hsum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W
    (K / ‖ringComplex (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hK)]
  ring

theorem normalized_triple_pair_poisson
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖ringComplex z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (r * (a * b))‖ ^ 2) := by
  have hnr : (‖ringComplex r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (ringComplex_ne_zero hr))
  have hna : (‖ringComplex a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (ringComplex_ne_zero ha))
  have hnb : (‖ringComplex b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (ringComplex_ne_zero hb))
  have hpoint (j : O) : CenteredMomentFourier.residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
      CenteredMomentFourier.residueGauss a ha χa (Ideal.Quotient.mk _ j) *
      star (CenteredMomentFourier.residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) =
      ((‖ringComplex r‖ : ℂ) * (‖ringComplex a‖ : ℂ) * (‖ringComplex b‖ : ℂ)) *
      (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    simp only [normalizedResidueGauss, CenteredMomentPrimitive.sqrt_absNorm,
      star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W K hK]
  simp_rw [hpoint, mul_assoc, tsum_mul_left, CenteredMomentPrimitive.sqrt_absNorm]
  simp only [map_mul, norm_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul]
  field_simp

end CenteredMomentBridge
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentInitial
open Eisenstein   SchwartzPlanePoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentBridge

variable {ι : Type*}

abbrev activeModulus (P : ι → Ideal O) (B : Finset ι) (c d : ι → ℕ) : O :=
  finitePrimeModulus (fun i : CenteredMomentActive.activeSupport B c d => P i.val)

def commonCharacter (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (B : Finset ι) (c d : ι → ℕ) : MulChar (Residue (activeModulus P B c d)) ℂ :=
  primitiveCharacter (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))

theorem activeModulus_ne_zero (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) : activeModulus P B c d ≠ 0 :=
  finitePrimeModulus_ne_zero _

theorem activeModulus_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) (v : O)
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {v})) :
    IsCoprime (activeModulus P B c d) v := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [activeModulus, span_finitePrimeModulus]
  apply IsCoprime.prod_left
  intro i _
  exact hcop i.val (Finset.mem_filter.mp i.property).1

theorem allocated_pair_factor (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (z : O) :
    idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b})) =
      rowCoprimeMask P (CenteredMomentActive.principalSupport B c d) z *
      (commonCharacter P hinj hg B c d (Ideal.Quotient.mk _ z) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ z) *
        star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ z))) := by
  calc
    _ = (idealRowHom z (∏ i ∈ B, P i ^ c i) *
        star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
        (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) := by
      rw [map_mul, map_mul, star_mul]
      ring
    _ = _ := by
      rw [CenteredMomentActive.common_ideal_pair_active P hg hchar B c d hc hd]
      simp only [commonCharacter, primitiveCharacter_mk, supportedModulusCharacter_mk]
      ring

theorem allocated_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {a * b})) (hab : IsCoprime a b)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let r := activeModulus P B c d
    let ξ := commonCharacter P hinj hg B c d
    let χa := supportedModulusCharacter a ha
    let χb := supportedModulusCharacter b hb
    (∑' z : O, (idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b}))) *
      W (‖ringComplex z‖ ^ 2 / K)) =
      ∑ E ∈ (CenteredMomentActive.principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖ringComplex e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖ringComplex (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (CenteredMomentFourier.residueGauss r (activeModulus_ne_zero P B c d) ξ (Ideal.Quotient.mk _ j) *
          CenteredMomentFourier.residueGauss a (supported_element_ne_zero a ha) χa (Ideal.Quotient.mk _ j) *
          star (CenteredMomentFourier.residueGauss b (supported_element_ne_zero b hb) χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖ringComplex j‖ ^ 2 / ‖ringComplex (r * (a * b))‖ ^ 2) := by
  simp_rw [allocated_pair_factor P hinj hg hchar B c d hc hd a b ha hb]
  exact masked_triple_pair_poisson P hinj (CenteredMomentActive.principalSupport B c d)
    (activeModulus P B c d) a b (activeModulus_ne_zero P B c d)
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (activeModulus_coprime P B c d (a * b) hcop) hab
    (commonCharacter P hinj hg B c d) (supportedModulusCharacter a ha)
    (supportedModulusCharacter b hb) W K hK

theorem common_gauss_norm_le_one (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ) (h : O) :
    ‖normalizedResidueGauss (activeModulus P B c d) (activeModulus_ne_zero P B c d)
      (commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h)‖ ≤ 1 :=
  normalized_primitive_gauss_norm_le_one
    (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))
    (CenteredMomentActive.netExponent_ne_zero B c d)
    (fun _i => CenteredMomentActive.netExponent_lt_six _ _) h

end CenteredMomentInitial
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open CenteredMomentCommonSupport
open scoped SchwartzMap
namespace CenteredMomentTail
open CenteredMomentFourier TruncatedPrincipalPoisson
theorem actual_first_gauss_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
        (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let ξ := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : {h : O // T ≤ K * ‖ringComplex h‖ ^ 2},
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) ξ
            (Ideal.Quotient.mk _ h.val) *
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h.val) /
            (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)) *
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h.val)) /
            (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
          paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T hK hT ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W K T 1 hK hT zero_le_one
    (fun h => normalizedResidueGauss _ (CenteredMomentInitial.activeModulus_ne_zero P B c d)
      (CenteredMomentInitial.commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h) *
      (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h) /
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)) *
      star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h)) /
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) (by
      intro h
      rw [norm_mul, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _)
          (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)).trans
          (normalizedResidueGauss_div_root_norm_le_one a ha χa _))).trans
        (normalizedResidueGauss_div_root_norm_le_one b hb χb _))


end CenteredMomentTail

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open CenteredMomentCommonSupport
open scoped SchwartzMap
namespace CenteredMomentSectorLocalization
open CenteredMomentFourier
theorem actual_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let χr := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) χr
            (Ideal.Quotient.mk _ h)*
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h)/
            (Real.sqrt (normValue a):ℂ))*
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h))/
            (Real.sqrt (normValue b):ℂ)))*paperRadialFourier W (K*normValue h)‖ ≤
      (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W Tsec Z Csec H ξ K 1 hT hZ hCsec hthreshold hK zero_le_one _ (by
    intro h
    rw [norm_mul,norm_mul,norm_star]
    calc
      _ ≤ (1*1)*1 := mul_le_mul
        (mul_le_mul (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)
          (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one a ha χa _)
          (norm_nonneg _) zero_le_one)
        (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one b hb χb _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num)


end CenteredMomentSectorLocalization

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace CenteredMomentDetectorDictionary
open HeckeDetectorDyadicProfiles

theorem compact_family_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤ L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (k n : ℕ) :
    ∃C : ℝ,0< C ∧ ∀p∈J,SchwartzMap.seminorm ℝ k n (G p)≤ C := by
  have hc := (HeckeDetectorDyadicProfiles.section_iteratedDeriv_smooth F hF n).continuous.norm
  obtain ⟨M,hM⟩ := (hJ.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨1+L^k*(|M|+1),by positivity,?_⟩
  intro p hp
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro x
  have he : (G p : ℝ→ℂ)=F p := funext (hG p)
  rw [he]
  by_cases hx : x∈Icc (-L) L
  · have hnorm : ‖iteratedDeriv n (F p) x‖≤|M|+1 := by
      have hb := hM (Set.mem_image_of_mem _ (show (p,x)∈J×ˢIcc (-L) L from ⟨hp,hx⟩))
      exact hb.trans (by linarith [le_abs_self M])
    have hxp : ‖x‖^k≤ L^k := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using hx
    exact (mul_le_mul hxp hnorm (norm_nonneg _) (pow_nonneg hL k)).trans (by linarith)
  · have hout : iteratedDeriv n (F p) x=0 := by
      by_contra hn
      have hx' := (subset_tsupport (iteratedDeriv n (F p))) hn
      have hh := (tsupport_iteratedDeriv_subset (F p) n) hx'
      exact hx ((closure_minimal (hs p) isClosed_Icc) hh)
    rw [hout,norm_zero,mul_zero]
    positivity

theorem compact_family_finite_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤ L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0< C ∧ ∀p∈J,S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G p)≤ C := by
  choose C hC hb using fun z : ℕ×ℕ=> compact_family_seminorm F hF L hL hs J hJ G hG z.1 z.2
  have hsum : 0≤∑z∈S,C z := Finset.sum_nonneg (fun z _=>(hC z).le)
  refine ⟨1+∑z∈S,C z,by linarith,?_⟩
  intro p hp
  apply Seminorm.finset_sup_apply_le (by linarith)
  intro z hz
  apply (hb z p hp).trans
  have hh := Finset.single_le_sum (fun z (_ : z∈S)=>(hC z).le) hz
  linarith

theorem compact_family_frequencyTwist
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤ L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0< C ∧ ∀p∈J,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (JointLogSeparation.frequencyTwist (G p) t)≤ C*(1+‖t‖)^n := by
  let S' := S.biUnion (fun z=> (Finset.range (z.2+1)).image (fun i=>(z.1,i)))
  obtain ⟨B,hB,hbound⟩ := compact_family_finite_seminorm F hF L hL hs J hJ G hG S'
  let c : ℕ×ℕ→ℝ := fun z=>(2:ℝ)^z.2*(1+2*Real.pi)^z.2*((z.2+1)*B)
  have hc (z : ℕ×ℕ) : 0≤ c z := by dsimp [c];positivity
  have hsum : 0≤∑z∈S,c z := Finset.sum_nonneg (fun z _=> hc z)
  refine ⟨S.sup Prod.snd,1+∑z∈S,c z,by linarith,?_⟩
  intro p hp t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hd : JointLogSeparation.derivativeSeminormSum (G p) z.1 z.2≤(z.2+1)*B := by
    unfold JointLogSeparation.derivativeSeminormSum
    calc
      _≤∑i∈Finset.range (z.2+1),B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : (z.1,i)∈S' := Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
        exact (Seminorm.le_finset_sup_apply hi').trans (hbound p hp)
      _=_ := by simp
  have hzC : c z≤1+∑z∈S,c z := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S)=> hc z) hz
    linarith
  have he := JointLogSeparation.frequencyTwist_seminorm_polynomial (G p) t z.1 z.2
  have hb : SchwartzMap.seminorm ℝ z.1 z.2 (JointLogSeparation.frequencyTwist (G p) t)≤ c z*(1+‖t‖)^z.2 := by
    apply he.trans
    dsimp only [c]
    gcongr
  exact hb.trans (mul_le_mul hzC
    (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)) (by positivity) (by linarith))

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic

def realInterpolatedLog (W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • W (Real.exp x)

lemma realInterpolatedLog_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (realInterpolatedLog W)) := by
  unfold realInterpolatedLog Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=> Real.exp (-p.1.1*p.2))).smul
    (hW.comp (by fun_prop))

lemma realInterpolatedLog_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (realInterpolatedLog W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hw : W (Real.exp x)≠0 := by intro hw;exact hx (by simp [realInterpolatedLog,hw])
  have hlo : Real.log a≤ x := by simpa only [Real.log_exp] using Real.log_le_log ha (hs hw).1
  have hhi : x≤ Real.log b := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) (hs hw).2
  constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),abs_nonneg (Real.log a),abs_nonneg (Real.log b)]

def realInterpolatedLogSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  kernelLogSource (twistProfile W p.1 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W p.1 0 a b ha hs hW)

lemma realInterpolatedLogSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) (x : ℝ) :
    realInterpolatedLogSchwartz W a b ha hs hW p x=realInterpolatedLog W p x := by
  rw [realInterpolatedLogSchwartz,kernelLogSource_apply]
  unfold twistProfile realInterpolatedLog
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ←Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero]
  change W (Real.exp x)*Complex.exp ((x:ℂ)*-(p.1:ℂ))=
    ((Real.exp (-p.1*x):ℝ):ℂ)*W (Real.exp x)
  rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  have he : (x:ℂ)*-(p.1:ℂ)=-(p.1:ℂ)*(x:ℂ) := by ring
  rw [he,mul_comm]

def interpolatedProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CenteredMomentLattice.normPowerProfile (twistProfile W σ 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W σ 0 a b ha hs hW) t

lemma interpolatedProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t x : ℝ) :
    interpolatedProfile W a b ha hs hW σ t x=twistProfile W σ t x := by
  rw [interpolatedProfile,CenteredMomentLattice.normPowerProfile_apply]
  unfold twistProfile
  by_cases hw : W x=0
  · simp [hw]
  · have hx : 0< x := ha.trans_le (hs hw).1
    calc
      _=W x*((x:ℂ)^(Complex.I*t)*(x:ℂ)^(-HeckeDyadic.shift σ 0)) := by ring
      _=W x*(x:ℂ)^(Complex.I*t-HeckeDyadic.shift σ 0) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2;unfold HeckeDyadic.shift;simp only [Complex.ofReal_zero,zero_mul,sub_zero];ring

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic JointLogSeparation

 theorem interpolatedProfile_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0< C ∧ ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤ C*(1+‖t‖)^n := by
  obtain ⟨T,A,hA,hcontrol⟩ := SchwartzPlanePoisson.schwartzCLM_finite_seminorm_control
    (CompletedHeight.fixedLogReturnCLM a b ha) S
  obtain ⟨n,B,hB,hbound⟩ := compact_family_frequencyTwist
    (realInterpolatedLog W) (realInterpolatedLog_smooth W hW)
    (|Real.log a|+|Real.log b|) (by positivity) (realInterpolatedLog_support W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ)) (isCompact_Icc.prod isCompact_singleton)
    (realInterpolatedLogSchwartz W a b ha hs hW) (realInterpolatedLogSchwartz_apply W a b ha hs hW) T
  refine ⟨n,A*B,mul_pos hA hB,?_⟩
  intro σ hσ t
  have hp : (σ,0)∈Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ) := ⟨hσ,rfl⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤ _ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))≤ B*(1+‖t‖)^n :=
    (hbound (σ,0) hp (t/(2*Real.pi))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) n) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open HeckeDetectorRelativePrime
local notation "O" => Eisenstein.O

def physicalSlotCoefficient (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) : ℂ :=
  idealCoeff η.inverse P*conj (W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1))

lemma physicalSlotCoefficient_norm (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) :
    ‖physicalSlotCoefficient η W D z P‖≤‖W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1)‖ := by
  rw [physicalSlotCoefficient,norm_mul,RCLike.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η.inverse P)

lemma physicalSlotCoefficient_annular (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ)
    (P : Ideal O) (hP : P≠0) (hD : 0< D) :
    physicalSlotCoefficient η W D z P=idealCoeff η.inverse P*
      HeckePrimeAnnular.annularWeight (fun y=> conj (W y)) D (1-z.re) (-z.im) P := by
  have hn : 0<(P.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  unfold physicalSlotCoefficient HeckePrimeAnnular.annularWeight
  rw [map_mul,HeckeInverseAmplification.conj_positive_cpow _ (div_pos hn hD)]
  have he : conj (z-1)= -HeckeDyadic.shift (1-z.re) (-z.im) := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  rw [he]

theorem physical_slot_conj (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η : Character) (m u : O) (hmLam : lambda∣m)
    (hMm : M≤ Ideal.span {m}) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) (hD : 0< D)
    (hη : ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus) :
    normalizedSlot η m 1 u (primePool M H b D) (physicalSlotCoefficient η W D z) 0 D=
      conj (HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z) := by
  unfold normalizedSlot rowSlot HeckePrimeRow.canonicalPrimeAmplitude
  rw [←sqrt_inverse_cpow D hD,map_mul]
  simp only [map_inv₀,Complex.conj_ofReal,Complex.ofReal_zero,one_mul,mul_zero,Complex.cpow_zero,mul_one,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hP' : P∈primePool M H b D := hP
  obtain ⟨_,hp,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H m hmLam hMm P hclass
  have hcop := HeckePrimeRow.identityClass_coprime_larger M H hclass hMm
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,if_pos hcop,one_mul]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp only [physicalSlotCoefficient,hw,zero_mul,map_zero,mul_zero,zero_mul]
  · have hn := idealCoeff_ne_zero_of_coprime η P hp.ne_zero (hη P hP' hw)
    simp only [physicalSlotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,map_mul,starRingEnd_self_apply]
    field_simp

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
open Filter
namespace CenteredMomentRankin

local notation "O" => Eisenstein.O

def primeMass (P : Ideal O) (δ : ℝ) : ℝ := ((Ideal.absNorm P:ℝ)^δ-1)⁻¹

theorem prime_norm_ge_two (P : Ideal O) (hp : Prime P) : 2 ≤ Ideal.absNorm P := by
  have h0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro hn
    exact hp.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hn))
  omega

theorem primeMass_nonneg (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ primeMass P δ := by
  apply inv_nonneg.mpr
  have hn : (1:ℝ) < Ideal.absNorm P := by exact_mod_cast (prime_norm_ge_two P hp)
  exact (sub_pos.mpr (Real.one_lt_rpow hn hδ)).le

theorem primeMass_le_fixed (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    primeMass P δ ≤ ((2:ℝ)^δ-1)⁻¹ := by
  apply inv_anti₀ (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hδ))
  exact sub_le_sub_right (Real.rpow_le_rpow (by norm_num)
    (by exact_mod_cast prime_norm_ge_two P hp) hδ.le) 1

theorem uniform_primeMass_product (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Ideal O), (∀ P ∈ S,Prime P) →
      (∏ P ∈ S,primeMass P δ) ≤ C := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2:ℝ)))
  let small : Finset (Ideal O) := (Ideal.finite_setOf_absNorm_le (S := O) N).toFinset
  let B : ℝ := max 1 (((2:ℝ)^δ-1)⁻¹)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B^small.card,pow_pos (zero_lt_one.trans_le hB) _,?_⟩
  intro S hp
  have hs (P : Ideal O) (hP : P ∈ S∩small) : primeMass P δ ≤ B :=
    (primeMass_le_fixed P (hp P (Finset.mem_inter.mp hP).1) δ hδ).trans (le_max_right _ _)
  have hl (P : Ideal O) (hP : P ∈ S\small) : primeMass P δ ≤ 1 := by
    have hn : N < Ideal.absNorm P := by
      by_contra hn
      apply (Finset.mem_sdiff.mp hP).2
      simpa only [small,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using le_of_not_gt hn
    have hpow := hN (Ideal.absNorm P) hn.le
    apply inv_le_one_of_one_le₀
    linarith
  have he : S=(S∩small)∪(S\small) := by
    ext P
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hdis : Disjoint (S∩small) (S\small) := Finset.disjoint_left.mpr
    (fun P hP hQ => (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)
  rw [he,Finset.prod_union hdis]
  have hleft : (∏ P ∈ S∩small,primeMass P δ) ≤ B^small.card := by
    calc
      _ ≤ ∏ _P ∈ S∩small,B := Finset.prod_le_prod
        (fun P hP => primeMass_nonneg P (hp P (Finset.mem_inter.mp hP).1) δ hδ) hs
      _ = B^(S∩small).card := by simp
      _ ≤ _ := pow_le_pow_right₀ hB (Finset.card_le_card Finset.inter_subset_right)
  have hright : (∏ P ∈ S\small,primeMass P δ) ≤ 1 :=
    Finset.prod_le_one (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ) hl
  exact (mul_le_mul hleft hright (Finset.prod_nonneg
    (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ)) (by positivity)).trans_eq (mul_one _)

theorem local_power_sum (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) (K : ℕ) :
    (∑ n ∈ Finset.range K,((Ideal.absNorm P:ℝ)^(n+1))^(-δ)) ≤ primeMass P δ := by
  let q : ℝ := (Ideal.absNorm P:ℝ)^δ
  have hNP : (1:ℝ)< Ideal.absNorm P := by exact_mod_cast prime_norm_ge_two P hp
  have hq : 1 < q := Real.one_lt_rpow hNP hδ
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hsum := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).summable.sum_le_tsum
    (Finset.range K) (fun n _ => mul_nonneg hr0 (pow_nonneg hr0 n))
  rw [((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).tsum_eq] at hsum
  have he (n : ℕ) : ((Ideal.absNorm P:ℝ)^(n+1))^(-δ)=q⁻¹*(q⁻¹)^n := by
    rw [← Real.rpow_natCast_mul (by linarith : (0:ℝ)≤ Ideal.absNorm P),mul_comm,
      Real.rpow_mul_natCast (by linarith : (0:ℝ)≤ Ideal.absNorm P),Real.rpow_neg (by linarith),pow_succ]
    dsimp only [q]
    ring
  simp_rw [he]
  apply hsum.trans_eq
  change q⁻¹*(1-q⁻¹)⁻¹=(q-1)⁻¹
  field_simp

end CenteredMomentRankin

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentRankinCount
open  UniqueFactorizationMonoid CenteredMomentRankin
local notation "O" => Eisenstein.O

def powerCode (R : Finset (Ideal O)) (I : Ideal O) (P : R) : ℕ :=
  (normalizedFactors I).count (P:Ideal O)-1

theorem powerCode_reconstruct (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) :
    I=∏ P : R,(P:Ideal O)^(powerCode R I P+1) := by
  have he (P : R) : powerCode R I P+1=(normalizedFactors I).count (P:Ideal O) := by
    have hp : (P:Ideal O) ∈ primeSupport I := hR ▸ P.property
    have hc := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    dsimp only [powerCode]
    omega
  simp_rw [he]
  calc
    I=(normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
    _=∏ P ∈ (normalizedFactors I).toFinset,P^(normalizedFactors I).count P := Finset.prod_multiset_count _
    _=∏ P : R,(P:Ideal O)^(normalizedFactors I).count (P:Ideal O) := by
      rw [Finset.prod_coe_sort R (fun P : Ideal O => P^(normalizedFactors I).count P)]
      change _=∏ P ∈ R,P^(normalizedFactors I).count P
      rw [← hR]
      rfl

theorem powerCode_injOn (R : Finset (Ideal O)) (S : Finset (Ideal O))
    (hS : ∀ I ∈ S,I ≠ 0) (hR : ∀ I ∈ S,primeSupport I=R) :
    Set.InjOn (powerCode R) S := by
  intro I hI J hJ he
  rw [powerCode_reconstruct R I (hS I hI) (hR I hI),powerCode_reconstruct R J (hS J hJ) (hR J hJ),he]

theorem ideal_mass_eq (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) (δ : ℝ) :
    (Ideal.absNorm I:ℝ)^(-δ)=
      ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(powerCode R I P+1))^(-δ) := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)^(-δ))
    (powerCode_reconstruct R I hI hR)
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] at he
  rw [he]
  exact (Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) _).symm

theorem fixed_support_mass (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      (∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ)) ≤ C := by
  obtain ⟨C,hC,hprod⟩ := uniform_primeMass_product δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hsupport
  let K : ℕ := S.sup (fun I => Finset.univ.sup (powerCode R I))+1
  let mass : (R → ℕ) → ℝ := fun v => ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(v P+1))^(-δ)
  have hm (v : R → ℕ) : 0 ≤ mass v := Finset.prod_nonneg
    (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  have hsub : S.image (powerCode R) ⊆ Fintype.piFinset (fun _P : R => Finset.range K) := by
    intro v hv
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro P
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := powerCode R I) (Finset.mem_univ P)).trans
      (Finset.le_sup (f := fun I => Finset.univ.sup (powerCode R I)) hI))
  calc
    _ = ∑ v ∈ S.image (powerCode R),mass v := by
      rw [Finset.sum_image (powerCode_injOn R S hS hsupport)]
      apply Finset.sum_congr rfl
      intro I hI
      exact ideal_mass_eq R I (hS I hI) (hsupport I hI) δ
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _P : R => Finset.range K),mass v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hm v)
    _ = ∏ P : R,∑ n ∈ Finset.range K,((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ) := by
      exact (Finset.prod_univ_sum (fun _P : R => Finset.range K)
        (fun P n => ((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ))).symm
    _ ≤ ∏ P : R,primeMass P δ := Finset.prod_le_prod
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
      (fun P _ => local_power_sum P (hR P P.property) δ hδ K)
    _ ≤ C := by
      have he := Finset.prod_coe_sort R (fun P => primeMass P δ)
      rw [he]
      exact hprod R hR

theorem fixed_support_count (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^δ := by
  obtain ⟨C,hC,hmass⟩ := fixed_support_mass δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hs X hX hN
  have hterm (I : Ideal O) (hI : I ∈ S) : (1:ℝ) ≤ X^δ*(Ideal.absNorm I:ℝ)^(-δ) := by
    have hn : (0:ℝ)< Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
    have hr := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn.le (hN I hI) hδ.le)
      (Real.rpow_nonneg hn.le (-δ))
    simpa only [← Real.rpow_add hn,add_neg_cancel,Real.rpow_zero] using hr
  calc
    _ = ∑ _I ∈ S,(1:ℝ) := by simp
    _ ≤ ∑ I ∈ S,X^δ*(Ideal.absNorm I:ℝ)^(-δ) := Finset.sum_le_sum (fun I hI => hterm I hI)
    _ = X^δ*∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ) := (Finset.mul_sum _ _ _).symm
    _ ≤ X^δ*C := mul_le_mul_of_nonneg_left (hmass R S hR hS hs) (Real.rpow_nonneg hX.le _)
    _ = _ := mul_comm _ _

end CenteredMomentRankinCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

theorem full_zero_off_diagonal (u v : O)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ)
    (hne : (Ideal.span {u} : Ideal O) ≠ Ideal.span {v}) :
    fullModulusCorrelation u v χ ψ 0 = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence]
  split_ifs with hc
  · by_cases hx0 : χ (Ideal.Quotient.mk _ x) = 0
    · rw [hx0,zero_mul]
    by_cases hy0 : ψ (Ideal.Quotient.mk _ y) = 0
    · rw [hy0,star_zero,mul_zero]
    have hux : IsCoprime u x := ((Ideal.isCoprime_span_singleton_iff x u).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hx0))).symm
    have hvy : IsCoprime v y := ((Ideal.isCoprime_span_singleton_iff y v).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hy0))).symm
    simp only [sub_zero] at hc
    have hu : u ∣ v*x := by
      have he := dvd_add ((dvd_mul_right u v).trans hc) (dvd_mul_right u y)
      convert he using 1 ; ring
    have hv : v ∣ u*y := by
      have he := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hc)
      convert he using 1 ; ring
    have huv := hux.dvd_of_dvd_mul_right hu
    have hvu := hvy.dvd_of_dvd_mul_right hv
    exact False.elim (hne (le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hvu)
      (Ideal.span_singleton_le_span_singleton.mpr huv)))
  · rfl

theorem full_same_zero (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    fullModulusCorrelation u u χ χ 0 = ∑ x : Residue u, χ x*star (χ x) := by
  have hcong (x y : Residue u) :
      scaledResidue u u (u*u) rfl x - scaledResidue u u (u*u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u*u}) 0 ↔ x=y := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence,sub_zero,← mul_sub,mul_dvd_mul_iff_left hu]
    exact Ideal.mem_span_singleton.symm.trans Ideal.Quotient.eq.symm
  simp only [fullModulusCorrelation,fullCorrelation,hcong,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem full_same_zero_norm_le (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    ‖fullModulusCorrelation u u χ χ 0‖ ≤ (Fintype.card (Residue u) : ℝ) := by
  rw [full_same_zero u hu χ]
  calc
    _ ≤ ∑ x : Residue u, ‖χ x*star (χ x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hn : χ x = 0
      · simp only [hn,zero_mul,norm_zero,zero_le_one]
      · rw [MulChar.star_apply',MulChar.inv_apply_eq_inv',mul_inv_cancel₀ hn,norm_one]
    _ = _ := by simp

theorem actual_zero_off_diagonal (u v : O) (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v}))
    (hpu : lambda^2 ∣ u-1)
    (hpv : lambda^2 ∣ v-1) (hne : u ≠ v) :
    actualCorrelation u v hu hv 0 = 0 := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero u hu)
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  apply full_zero_off_diagonal u v
  intro he
  apply hne
  rw [← primaryIdealGenerator_span u (supported_element_ne_zero u hu) hpu,
    ← primaryIdealGenerator_span v (supported_element_ne_zero v hv) hpv,he]

theorem actual_same_zero_norm_le (u : O) (hu : Supported (Ideal.span {u})) :
    ‖actualCorrelation u u hu hu 0‖ ≤ (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero u hu)
  let : Fintype (Residue u) := Fintype.ofFinite _
  have hb := full_same_zero_norm_le u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
  simpa only [actualCorrelation,supportedCorrelation,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hb

theorem divisible_ideal_card (S : Finset (Ideal O)) (s : Ideal O) (hs : s ≠ 0)
    (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hY : 0 ≤ Y) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  by_cases hempty : S.Nonempty
  · have hquot (I : Ideal O) (hI : I ∈ S) : quadraticIdealQuotient s I ≠ 0 :=
      ne_zero_of_dvd_ne_zero (hS I hI) (quadraticIdealQuotient_dvd (hdiv I hI))
    have hbound (I : Ideal O) (hI : I ∈ S) :
        (Ideal.absNorm (quadraticIdealQuotient s I) : ℝ) ≤ Y / Ideal.absNorm s := by
      rw [quadraticIdealQuotient_norm hs (hdiv I hI)]
      exact div_le_div_of_nonneg_right (hN I hI) (Nat.cast_nonneg _)
    obtain ⟨I,hI⟩ := hempty
    have hscale : 1 ≤ Y/(Ideal.absNorm s : ℝ) := by
      have hn : (1:ℝ) ≤ Ideal.absNorm (quadraticIdealQuotient s I) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hquot I hI))
      exact hn.trans (hbound I hI)
    have hc := EisensteinLatticeCount.finite_ideal_count_real (S.image (quadraticIdealQuotient s)) _ hscale
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hquot I hI)
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hbound I hI)
    rw [Finset.card_image_of_injOn (fun I hI J hJ he => quadraticIdealQuotient_injective s
      (hdiv I hI) (hdiv J hJ) he)] at hc
    convert hc using 1 ; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.cast_zero]
    positivity

def secondZeroEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) : ℂ :=
  ∑ i ∈ S, ∑ j ∈ S, (c i*star (c j)) *
    (actualCorrelation (a i) (a j) (ha i) (ha j) 0 /
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ)))

theorem secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, lambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) :
    ‖secondZeroEnergy S a ha c‖ ≤ ∑ i ∈ S, ‖c i‖^2 := by
  have hroot (i : α) :
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)) =
        (Ideal.absNorm (Ideal.span {a i}) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_natCast]
  have he : secondZeroEnergy S a ha c =
      ∑ i ∈ S, (c i*star (c i)) *
        (actualCorrelation (a i) (a i) (ha i) (ha i) 0 /(Ideal.absNorm (Ideal.span {a i}) : ℂ)) := by
    unfold secondZeroEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [hroot]
    · intro j hj hji
      have hne : a i ≠ a j := fun he => hji (hinj hi hj he).symm
      rw [actual_zero_off_diagonal _ _ (ha i) (ha j) (hp i) (hp j) hne,zero_div,mul_zero]
    · exact fun hnot => False.elim (hnot hi)
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,norm_mul,norm_star,norm_div,Complex.norm_natCast,← pow_two]
  have hN : 0 < (Ideal.absNorm (Ideal.span {a i}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ha i).1)
  exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hN).mpr (actual_same_zero_norm_le _ (ha i)))

theorem primary_column_card {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, lambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  have hspan : Set.InjOn (fun i => (Ideal.span {a i} : Ideal O)) S := by
    intro i hi j hj he
    dsimp only at he
    apply hinj hi hj
    rw [← primaryIdealGenerator_span (a i) (supported_element_ne_zero _ (ha i)) (hp i),
      ← primaryIdealGenerator_span (a j) (supported_element_ne_zero _ (ha j)) (hp j),he]
  have hb := divisible_ideal_card (S.image (fun i => Ideal.span {a i})) s hs
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact (ha i).1)
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hdiv i hi)
    Y hY (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hN i hi)
  rwa [Finset.card_image_of_injOn hspan] at hb

theorem secondZeroEnergy_divisor_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, lambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    ‖secondZeroEnergy S a ha c‖ ≤ 128*B^2*Y/(Ideal.absNorm s : ℝ) := by
  calc
    _ ≤ ∑ i ∈ S, ‖c i‖^2 := secondZeroEnergy_bound S a ha hp hinj c
    _ ≤ ∑ _i ∈ S, B^2 := Finset.sum_le_sum (fun i hi =>
      pow_le_pow_left₀ (norm_nonneg _) (hc i hi) 2)
    _ = B^2*(S.card : ℝ) := by simp [mul_comm]
    _ ≤ B^2*(128*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (primary_column_card S a ha hp hinj s hs hdiv Y hY hN) (sq_nonneg _)
    _ = _ := by ring

theorem normalized_secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, lambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y)
    (κ : ℂ) (T : ℝ) (hT : 0 < T) :
    ‖(κ/(T:ℂ))*secondZeroEnergy S a ha c‖ ≤
      128*‖κ‖*B^2*Y/(T*(Ideal.absNorm s : ℝ)) := by
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _ ≤ (‖κ‖/T)*(128*B^2*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (secondZeroEnergy_divisor_bound S a ha hp hinj c B hB hc s hs hdiv Y hY hN)
        (div_nonneg (norm_nonneg _) hT.le)
    _ = _ := by ring

end CenteredMomentSecondDiagonal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentRankinRadical
open  UniqueFactorizationMonoid CenteredMomentDivisorAllocation
local notation "O" => Eisenstein.O

theorem old_mask_radical_count {α : Type*} (S : Finset α) (I J : α → Ideal O)
    (s : Ideal O) (hs : Squarefree s) (hs0 : s ≠ 0)
    (hI : ∀ a ∈ S,I a ≠ 0) (hJ : ∀ a ∈ S,J a ≠ 0)
    (hsi : ∀ a ∈ S,s ∣ I a) (hsj : ∀ a ∈ S,s ∣ J a)
    (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ a ∈ S,(Ideal.absNorm (commonRadical (I a) (J a)):ℝ) ≤ Y) :
    ((S.image (fun a => commonRadical (I a) (J a))).card:ℝ) ≤
      128*Y/(Ideal.absNorm s:ℝ) := by
  refine CenteredMomentSecondDiagonal.divisible_ideal_card _ s hs0 ?_ ?_ Y hY ?_
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact commonRadical_ne_zero _ _
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact old_mask_dvd_commonRadical s _ _ hs (hI a ha) (hJ a ha) (hsi a ha) (hsj a ha)
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact hN a ha

end CenteredMomentRankinRadical

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
