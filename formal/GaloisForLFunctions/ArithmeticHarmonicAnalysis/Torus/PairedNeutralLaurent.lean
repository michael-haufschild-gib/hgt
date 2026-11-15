import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralQuotientBasis
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Laurent coordinates and the exact domain criterion for neutral quotients

For an arbitrary ideal `J ≤ K[hᵢ]`, send `zᵢ` to the Laurent variable `Tᵢ`
and `wᵢ` to `(hᵢ mod J) Tᵢ⁻¹`. The coefficient at weight `q` is the neutral
weight extraction modulo `J`, multiplied by the product of the negative
coordinate powers forced by `q`.

The actual paired quotient is a domain exactly when `K[hᵢ]/J` is a domain
and no coordinate `hᵢ` vanishes in it. Sufficiency follows from an injective
map into the Laurent domain. Necessity uses contraction of prime ideals
and the fact that both paired variables survive every proper neutral ideal.
This applies to nonlinear relations and extends the one-pair domain test.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
open scoped PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Laurent polynomials in the paired weights, with neutral quotient coefficients. -/
abbrev NeutralLaurent (J : Ideal (MvPolynomial ι K)) :=
  AddMonoidAlgebra (MvPolynomial ι K ⧸ J) (ι → ℤ)

/-- Constants enter the Laurent ring through the neutral quotient. -/
def pairedLaurentConstant (J : Ideal (MvPolynomial ι K)) : K →+* NeutralLaurent K J :=
  AddMonoidAlgebra.singleZeroRingHom.comp ((Ideal.Quotient.mk J).comp C)

/-- Positive variables are invertible Laurent variables; negative variables carry neutral factors. -/
def pairedLaurentCoordinates (J : Ideal (MvPolynomial ι K)) : (ι ⊕ ι) → NeutralLaurent K J :=
  Sum.elim (fun i => AddMonoidAlgebra.single (Pi.single i 1) 1)
    (fun i => AddMonoidAlgebra.single (-Pi.single i 1) (Ideal.Quotient.mk J (X i)))

/-- Substitute the paired variables by their Laurent expressions. -/
def pairedLaurentMap (J : Ideal (MvPolynomial ι K)) :
    MvPolynomial (ι ⊕ ι) K →+* NeutralLaurent K J :=
  eval₂Hom (pairedLaurentConstant K J) (pairedLaurentCoordinates K J)

private theorem prod_laurent_single {κ A G : Type*} [CommRing A] [AddCommMonoid G]
    (s : Finset κ) (q : κ → G) (c : κ → A) :
    ∏ i ∈ s, AddMonoidAlgebra.single (q i) (c i) =
      AddMonoidAlgebra.single (∑ i ∈ s, q i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, AddMonoidAlgebra.single_mul_single]

/-- An ordinary monomial becomes one Laurent monomial of its paired weight. -/
theorem pairedLaurentMap_monomial (J : Ideal (MvPolynomial ι K))
    (d : (ι ⊕ ι) →₀ ℕ) (c : K) :
    pairedLaurentMap K J (monomial d c) =
      AddMonoidAlgebra.single (pairedWeight d)
        (Ideal.Quotient.mk J (C c) * ∏ i, (Ideal.Quotient.mk J (X i)) ^ d (Sum.inr i)) := by
  rw [pairedLaurentMap, eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (by intro i; exact pow_zero _), Fintype.prod_sum_type]
  simp only [pairedLaurentCoordinates, Sum.elim_inl, Sum.elim_inr, AddMonoidAlgebra.single_pow,
    one_pow]
  rw [prod_laurent_single, prod_laurent_single]
  change AddMonoidAlgebra.single 0 (Ideal.Quotient.mk J (C c)) * _ = _
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single]
  simp only [Finset.prod_const_one, one_mul, zero_add]
  congr 1
  funext i
  simp [pairedWeight, Pi.single_apply, Finset.sum_apply, nsmul_eq_mul, mul_ite, sub_eq_add_neg]

/-- The neutral coefficient forced by the negative part of a weight. -/
def negativeNeutralFactor (J : Ideal (MvPolynomial ι K)) (q : ι → ℤ) :
    MvPolynomial ι K ⧸ J := ∏ i, (Ideal.Quotient.mk J (X i)) ^ (-q i).toNat

/-- The image of a minimal weight monomial has exactly the forced negative neutral factors. -/
theorem pairedLaurentMap_minimal (J : Ideal (MvPolynomial ι K)) (q : ι → ℤ) :
    pairedLaurentMap K J (minimalPairedMonomial K q) =
      AddMonoidAlgebra.single q (negativeNeutralFactor K J q) := by
  rw [minimalPairedMonomial, pairedLaurentMap_monomial, pairedWeight_normal]
  simp [negativeNeutralFactor]

omit [Fintype ι] in
/-- Every neutral polynomial becomes a constant Laurent polynomial modulo its relations. -/
theorem pairedLaurentMap_invariant (J : Ideal (MvPolynomial ι K)) (f : MvPolynomial ι K) :
    pairedLaurentMap K J (invariantSubstitution K f) =
      AddMonoidAlgebra.single 0 (Ideal.Quotient.mk J f) := by
  have he : (pairedLaurentMap K J).comp (invariantSubstitution K) =
      AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk J) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [pairedLaurentMap, invariantSubstitution, pairedLaurentConstant]
    · intro i
      simp [pairedLaurentMap, invariantSubstitution, pairedLaurentCoordinates,
        AddMonoidAlgebra.single_mul_single]
  exact DFunLike.congr_fun he f

/-- Laurent coefficients of the relative basis expansion are diagonal in the weight. -/
theorem pairedLaurentMap_assembly_coeff (J : Ideal (MvPolynomial ι K))
    (c : (ι → ℤ) →₀ MvPolynomial ι K) (q : ι → ℤ) :
    (pairedLaurentMap K J (pairedNeutralAssembly K c)).coeff q =
      Ideal.Quotient.mk J (c q) * negativeNeutralFactor K J q := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, hc, hd, Finsupp.add_apply, add_mul]
  | single r f =>
    rw [pairedNeutralAssembly, Finsupp.linearCombination_single, pairedNeutral_smul,
      map_mul, pairedLaurentMap_invariant, pairedLaurentMap_minimal,
      AddMonoidAlgebra.single_mul_single, zero_add]
    by_cases h : r = q <;> simp [h, AddMonoidAlgebra.coeff_single]

/-- The Laurent coefficient is the extracted neutral coefficient times its forced factor. -/
theorem pairedLaurentMap_coeff (J : Ideal (MvPolynomial ι K))
    (P : MvPolynomial (ι ⊕ ι) K) (q : ι → ℤ) :
    (pairedLaurentMap K J P).coeff q =
      Ideal.Quotient.mk J (pairedWeightExtraction K q P) * negativeNeutralFactor K J q := by
  have h := pairedLaurentMap_assembly_coeff K J (pairedNeutralEquiv K P) q
  have he : pairedNeutralAssembly K (pairedNeutralEquiv K P) = P :=
    (pairedNeutralEquiv K).symm_apply_apply P
  rw [he, pairedNeutralEquiv_apply] at h
  exact h

/-- Every substituted neutral relation vanishes in the Laurent target. -/
theorem pairedLaurentMap_annihilates (J : Ideal (MvPolynomial ι K))
    (P : MvPolynomial (ι ⊕ ι) K) (hP : P ∈ J.map (invariantSubstitution K)) :
    pairedLaurentMap K J P = 0 := by
  ext q
  rw [pairedLaurentMap_coeff, AddMonoidAlgebra.coeff_zero,
    (Ideal.Quotient.eq_zero_iff_mem).mpr (pairedWeightExtraction_mem K q J hP), zero_mul]
  rfl

/-- The Laurent substitution descends to the actual paired ideal quotient. -/
def pairedQuotientLaurentMap (J : Ideal (MvPolynomial ι K)) :
    (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) →+* NeutralLaurent K J :=
  Ideal.Quotient.lift _ (pairedLaurentMap K J) (pairedLaurentMap_annihilates K J)

/-- Nonzero coordinate classes in a domain give nonzero factors at every weight. -/
theorem negativeNeutralFactor_ne_zero (J : Ideal (MvPolynomial ι K))
    [IsDomain (MvPolynomial ι K ⧸ J)] (h : ∀ i, (X i : MvPolynomial ι K) ∉ J)
    (q : ι → ℤ) : negativeNeutralFactor K J q ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply pow_ne_zero
  exact fun he => h i ((Ideal.Quotient.eq_zero_iff_mem).mp he)

/-- No extra Laurent kernel occurs over a domain with nonvanishing neutral coordinates. -/
theorem pairedQuotientLaurentMap_injective (J : Ideal (MvPolynomial ι K))
    [IsDomain (MvPolynomial ι K ⧸ J)] (h : ∀ i, (X i : MvPolynomial ι K) ∉ J) :
    Function.Injective (pairedQuotientLaurentMap K J) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  intro P hP
  apply (mem_extended_ideal_iff_extractions K J P).mpr
  intro q
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have he := congrArg (fun L : NeutralLaurent K J => L.coeff q) (RingHom.mem_ker.mp hP)
  rw [pairedLaurentMap_coeff, AddMonoidAlgebra.coeff_zero] at he
  exact (mul_eq_zero.mp he).resolve_right (negativeNeutralFactor_ne_zero K J h q)

/-- The Laurent embedding supplies a domain structure on the paired quotient. -/
theorem pairedNeutralQuotient_isDomain (J : Ideal (MvPolynomial ι K))
    [IsDomain (MvPolynomial ι K ⧸ J)] (h : ∀ i, (X i : MvPolynomial ι K) ∉ J) :
    IsDomain (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
  Function.Injective.isDomain (pairedQuotientLaurentMap K J)
    (pairedQuotientLaurentMap_injective K J h)

/-- Each individual paired variable survives exactly when the neutral ideal is proper. -/
theorem pairedVariable_mk_ne_zero_iff (J : Ideal (MvPolynomial ι K)) (v : ι ⊕ ι) :
    Ideal.Quotient.mk (J.map (invariantSubstitution K)) (X v) ≠ 0 ↔ J ≠ ⊤ := by
  have hn : neutralExponent (Finsupp.single v 1) = 0 := by
    ext i
    cases v with
    | inl j => simp [neutralExponent_apply, Finsupp.single_apply]
    | inr j => simp [neutralExponent_apply, Finsupp.single_apply]
  have hx : pairedWeightExtraction K (pairedWeight (Finsupp.single v 1)) (X v) = 1 := by
    change pairedWeightExtraction K _ (monomial _ 1) = _
    rw [pairedWeightExtraction_monomial, if_pos rfl, hn]
    rfl
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h ht
    apply h
    rw [ht, Ideal.map_top]
    trivial
  · intro h hv
    have h1 := pairedWeightExtraction_mem K (pairedWeight (Finsupp.single v 1)) J hv
    rw [hx] at h1
    exact h (Ideal.eq_top_of_isUnit_mem J h1 isUnit_one)

/-- A paired product vanishes precisely when its neutral coordinate belongs to the original ideal. -/
theorem pairedVariable_product_eq_zero_iff (J : Ideal (MvPolynomial ι K)) (i : ι) :
    Ideal.Quotient.mk (J.map (invariantSubstitution K)) (X (Sum.inl i)) *
      Ideal.Quotient.mk (J.map (invariantSubstitution K)) (X (Sum.inr i)) = 0 ↔
      (X i : MvPolynomial ι K) ∈ J := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have he : invariantSubstitution K (X i) = X (Sum.inl i) * X (Sum.inr i) := by
    simp [invariantSubstitution]
  rw [← he]
  change X i ∈ (J.map (invariantSubstitution K)).comap (invariantSubstitution K) ↔ _
  rw [invariantSubstitution_comap_map]

/-- Vanishing neutral coordinates give an explicit pair of nonzero zero divisors exactly in proper quotients. -/
theorem pairedVariable_zeroDivisors_iff (J : Ideal (MvPolynomial ι K)) (i : ι) :
    (Ideal.Quotient.mk (J.map (invariantSubstitution K)) (X (Sum.inl i)) ≠ 0 ∧
      Ideal.Quotient.mk (J.map (invariantSubstitution K)) (X (Sum.inr i)) ≠ 0 ∧
      Ideal.Quotient.mk (J.map (invariantSubstitution K)) (X (Sum.inl i)) *
        Ideal.Quotient.mk (J.map (invariantSubstitution K)) (X (Sum.inr i)) = 0) ↔
      J ≠ ⊤ ∧ (X i : MvPolynomial ι K) ∈ J := by
  rw [pairedVariable_mk_ne_zero_iff, pairedVariable_mk_ne_zero_iff,
    pairedVariable_product_eq_zero_iff, and_self_left]

/-- Domain classification for all paired quotients by arbitrary neutral relations. -/
theorem pairedNeutralQuotient_isDomain_iff (J : Ideal (MvPolynomial ι K)) :
    IsDomain (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) ↔
      IsDomain (MvPolynomial ι K ⧸ J) ∧ ∀ i, (X i : MvPolynomial ι K) ∉ J := by
  constructor
  · intro hD
    letI := hD
    haveI hp : (J.map (invariantSubstitution K)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hD
    haveI hJ : J.IsPrime := by
      rw [← invariantSubstitution_comap_map K J]
      infer_instance
    refine ⟨inferInstance, ?_⟩
    intro i hi
    have hz := (pairedVariable_mk_ne_zero_iff K J (Sum.inl i)).mpr hJ.ne_top
    have hw := (pairedVariable_mk_ne_zero_iff K J (Sum.inr i)).mpr hJ.ne_top
    have hm := (pairedVariable_product_eq_zero_iff K J i).mpr hi
    exact hz ((mul_eq_zero.mp hm).resolve_right hw)
  · rintro ⟨hD, h⟩
    letI := hD
    exact pairedNeutralQuotient_isDomain K J h

/-- Neutral substitution preserves a prime ideal exactly when it contains no coordinate variable. -/
theorem pairedNeutralIdeal_isPrime_iff (J : Ideal (MvPolynomial ι K)) :
    (J.map (invariantSubstitution K)).IsPrime ↔
      J.IsPrime ∧ ∀ i, (X i : MvPolynomial ι K) ∉ J := by
  rw [← Ideal.Quotient.isDomain_iff_prime, pairedNeutralQuotient_isDomain_iff,
    Ideal.Quotient.isDomain_iff_prime]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedLaurentMap_coeff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedQuotientLaurentMap_injective
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedVariable_zeroDivisors_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotient_isDomain_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralIdeal_isPrime_iff
