import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedWeightNormalForm
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Paired torus weights after neutral relations

Write `hᵢ = zᵢwᵢ`. For every ideal `J` in `K[h]`, the weight-`q` component
of `K[z,w]/JK[z,w]` is canonically a copy of `K[h]/J`: multiplication by
the minimal weight monomial creates exactly the relations already in `J`.

The proof extracts the neutral coefficients of a fixed weight. Extraction
commutes with multiplication by neutral polynomials, so it takes the
extended ideal back into `J`. Consequently every character survives every
proper neutral quotient, even when the relations are nonlinear.

This is the ideal-descent mechanism behind the moment-map reduction in §6.1
of Brown, *Equivariant Quantisation of Hypertoric Varieties via Symplectic Cuts*.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial HTGeometry.AddMonoidAlgebraTensorCoefficients
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Common exponents left after removing the minimal weight monomial. -/
def neutralExponent (d : (ι ⊕ ι) →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => min (d (Sum.inl i)) (d (Sum.inr i)))

@[simp] theorem neutralExponent_apply (d : (ι ⊕ ι) →₀ ℕ) (i : ι) :
    neutralExponent d i = min (d (Sum.inl i)) (d (Sum.inr i)) := by
  simp [neutralExponent]

@[simp] theorem neutralExponent_normal (q : ι → ℤ) (s : ι →₀ ℕ) :
    neutralExponent (normalWeightExponent q s) = s := by
  ext i
  simp only [neutralExponent_apply, normalWeightExponent_inl, normalWeightExponent_inr]
  omega

theorem pairedWeight_add_neutral (s : ι →₀ ℕ) (d : (ι ⊕ ι) →₀ ℕ) :
    pairedWeight (normalWeightExponent 0 s + d) = pairedWeight d := by
  funext i
  simp only [pairedWeight, Finsupp.add_apply, normalWeightExponent_inl,
    normalWeightExponent_inr, Pi.zero_apply, neg_zero, Int.toNat_zero, zero_add,
    Nat.cast_add]
  omega

theorem neutralExponent_add_neutral (s : ι →₀ ℕ) (d : (ι ⊕ ι) →₀ ℕ) :
    neutralExponent (normalWeightExponent 0 s + d) = s + neutralExponent d := by
  ext i
  simp only [neutralExponent_apply, Finsupp.add_apply, normalWeightExponent_inl,
    normalWeightExponent_inr, Pi.zero_apply, neg_zero, Int.toNat_zero, zero_add]
  omega

/-- Project to one character and divide its monomials by their forced minimal factor. -/
def pairedWeightExtraction (q : ι → ℤ) :
    MvPolynomial (ι ⊕ ι) K →ₗ[K] MvPolynomial ι K := by
  classical
  exact (Finsupp.lsum K fun d => if pairedWeight d = q then
    (monomial (neutralExponent d) : K →ₗ[K] MvPolynomial ι K) else 0).comp
      (coeffLinearEquiv K _).toLinearMap

@[simp] theorem pairedWeightExtraction_monomial (q : ι → ℤ)
    (d : (ι ⊕ ι) →₀ ℕ) (c : K) :
    pairedWeightExtraction K q (monomial d c) =
      if pairedWeight d = q then monomial (neutralExponent d) c else 0 := by
  classical
  simp only [pairedWeightExtraction, LinearMap.comp_apply,
    show (monomial d c : MvPolynomial (ι ⊕ ι) K) = AddMonoidAlgebra.single d c from rfl,
    LinearEquiv.coe_toLinearMap, coeffLinearEquiv_single, Finsupp.lsum_single]
  split <;> rfl

/-- Extraction is linear over the neutral polynomial ring. -/
theorem pairedWeightExtraction_invariant_mul (q : ι → ℤ)
    (f : MvPolynomial ι K) (P : MvPolynomial (ι ⊕ ι) K) :
    pairedWeightExtraction K q (invariantSubstitution K f * P) =
      f * pairedWeightExtraction K q P := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, add_mul, hf, hg]
  | monomial s c =>
    induction P using MvPolynomial.induction_on' with
    | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
    | monomial d a =>
      rw [invariantSubstitution_monomial, monomial_mul,
        pairedWeightExtraction_monomial, pairedWeightExtraction_monomial,
        pairedWeight_add_neutral, neutralExponent_add_neutral]
      split
      · rw [monomial_mul]
      · rw [mul_zero]

@[simp] theorem pairedWeightExtraction_equiv (q : ι → ℤ) (f : MvPolynomial ι K) :
    pairedWeightExtraction K q (pairedWeightSpaceEquiv K q f).1 = f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Submodule.coe_add, hf, hg]
  | monomial s c =>
    rw [pairedWeightSpaceEquiv_monomial, pairedWeightExtraction_monomial,
      pairedWeight_normal, if_pos rfl, neutralExponent_normal]

/-- An extended neutral relation has every extracted coefficient in the original ideal. -/
theorem pairedWeightExtraction_mem (q : ι → ℤ) (J : Ideal (MvPolynomial ι K))
    {P : MvPolynomial (ι ⊕ ι) K} (hP : P ∈ J.map (invariantSubstitution K)) :
    pairedWeightExtraction K q P ∈ J := by
  have hmem : ∀ z ∈ J.map (invariantSubstitution K),
      ∀ a, pairedWeightExtraction K q (a * z) ∈ J := by
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro y ⟨f, hf, rfl⟩ a
      rw [mul_comm, pairedWeightExtraction_invariant_mul]
      exact J.mul_mem_right _ hf
    · intro a
      rw [mul_zero, map_zero]
      exact J.zero_mem
    · intro y z _ _ hy hz a
      rw [mul_add, map_add]
      exact J.add_mem (hy a) (hz a)
    · intro b y _ hy a
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * b)
  simpa only [one_mul] using hmem P hP 1

/-- Extending neutral relations creates no additional relation in any weight component. -/
theorem pairedWeightSpaceEquiv_mem_map_iff (q : ι → ℤ)
    (J : Ideal (MvPolynomial ι K)) (f : MvPolynomial ι K) :
    (pairedWeightSpaceEquiv K q f).1 ∈ J.map (invariantSubstitution K) ↔ f ∈ J := by
  constructor
  · intro h
    simpa only [pairedWeightExtraction_equiv] using pairedWeightExtraction_mem K q J h
  · intro h
    rw [pairedWeightSpaceEquiv_factor]
    exact (J.map (invariantSubstitution K)).mul_mem_left _ (Ideal.mem_map_of_mem _ h)

/-- Minimal-monomial multiplication followed by the quotient map. -/
def pairedWeightQuotientMap (q : ι → ℤ) (J : Ideal (MvPolynomial ι K)) :
    MvPolynomial ι K →ₗ[K]
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
  (Ideal.Quotient.mkₐ K (J.map (invariantSubstitution K))).toLinearMap.comp
    ((pairedWeightSpace K q).subtype.comp (pairedWeightSpaceEquiv K q).toLinearMap)

theorem ker_pairedWeightQuotientMap (q : ι → ℤ) (J : Ideal (MvPolynomial ι K)) :
    (pairedWeightQuotientMap K q J).ker = J.restrictScalars K := by
  ext f
  change Ideal.Quotient.mk (J.map (invariantSubstitution K))
    (pairedWeightSpaceEquiv K q f).1 = 0 ↔ f ∈ J
  rw [Ideal.Quotient.eq_zero_iff_mem, pairedWeightSpaceEquiv_mem_map_iff]

/-- The image of the actual polynomial weight space in the quotient by neutral relations. -/
def reducedPairedWeightSpace (q : ι → ℤ) (J : Ideal (MvPolynomial ι K)) :
    Submodule K (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
  (pairedWeightQuotientMap K q J).range

theorem reducedPairedWeightSpace_eq_map (q : ι → ℤ) (J : Ideal (MvPolynomial ι K)) :
    reducedPairedWeightSpace K q J =
      (pairedWeightSpace K q).map
        (Ideal.Quotient.mkₐ K (J.map (invariantSubstitution K))).toLinearMap := by
  ext P
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨_, (pairedWeightSpaceEquiv K q f).2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(pairedWeightSpaceEquiv K q).symm ⟨f, hf⟩, ?_⟩
    simp only [pairedWeightQuotientMap, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, Submodule.subtype_apply]

/-- Every reduced weight component is canonically the neutral quotient. -/
def reducedPairedWeightEquiv (q : ι → ℤ) (J : Ideal (MvPolynomial ι K)) :
    (MvPolynomial ι K ⧸ J) ≃ₗ[K] reducedPairedWeightSpace K q J :=
  (Submodule.quotEquivOfEq (J.restrictScalars K) _
    (ker_pairedWeightQuotientMap K q J).symm).trans
      (pairedWeightQuotientMap K q J).quotKerEquivRange

/-- The quotient equivalence is still literal multiplication by the minimal monomial. -/
theorem reducedPairedWeightEquiv_mk (q : ι → ℤ) (J : Ideal (MvPolynomial ι K))
    (f : MvPolynomial ι K) :
    (reducedPairedWeightEquiv K q J (Ideal.Quotient.mk J f)).1 =
      Ideal.Quotient.mk (J.map (invariantSubstitution K))
        (monomial (normalWeightExponent q 0) 1 * invariantSubstitution K f) := by
  change pairedWeightQuotientMap K q J f = _
  change Ideal.Quotient.mk _ (pairedWeightSpaceEquiv K q f).1 = _
  rw [pairedWeightSpaceEquiv_factor]

/-- Extension followed by contraction fixes every ideal of the neutral polynomial ring. -/
theorem invariantSubstitution_comap_map (J : Ideal (MvPolynomial ι K)) :
    (J.map (invariantSubstitution K)).comap (invariantSubstitution K) = J := by
  ext f
  change invariantSubstitution K f ∈ J.map (invariantSubstitution K) ↔ f ∈ J
  have h := pairedWeightSpaceEquiv_mem_map_iff K (0 : ι → ℤ) J f
  have hzero : normalWeightExponent (0 : ι → ℤ) 0 = 0 := by
    ext (i | i) <;> simp
  simpa only [pairedWeightSpaceEquiv_factor, hzero,
    show (monomial (0 : (ι ⊕ ι) →₀ ℕ) (1 : K)) = 1 from rfl, one_mul] using h

/-- Every character survives precisely when the neutral quotient is nonzero. -/
theorem minimalWeight_mk_ne_zero_iff (q : ι → ℤ) (J : Ideal (MvPolynomial ι K)) :
    Ideal.Quotient.mk (J.map (invariantSubstitution K))
      (monomial (normalWeightExponent q 0) (1 : K)) ≠ 0 ↔ J ≠ ⊤ := by
  have h := pairedWeightSpaceEquiv_mem_map_iff K q J 1
  simp only [pairedWeightSpaceEquiv_factor, map_one, mul_one] at h
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, h]
  constructor
  · intro hn htop
    apply hn
    rw [htop]
    trivial
  · intro hn h1
    exact hn (Ideal.eq_top_of_isUnit_mem J h1 isUnit_one)

/-- The quotient normal form respects multiplication by neutral coefficients. -/
theorem pairedWeightQuotientMap_mul (q : ι → ℤ) (J : Ideal (MvPolynomial ι K))
    (f g : MvPolynomial ι K) :
    pairedWeightQuotientMap K q J (f * g) =
      Ideal.Quotient.mk (J.map (invariantSubstitution K)) (invariantSubstitution K f) *
        pairedWeightQuotientMap K q J g := by
  change Ideal.Quotient.mk _ (pairedWeightSpaceEquiv K q (f * g)).1 =
    _ * Ideal.Quotient.mk _ (pairedWeightSpaceEquiv K q g).1
  rw [pairedWeightSpaceEquiv_factor, pairedWeightSpaceEquiv_factor, ← map_mul,
    map_mul (invariantSubstitution K)]
  congr 1
  exact mul_left_comm _ _ _

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedWeightSpaceEquiv_mem_map_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.reducedPairedWeightEquiv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.invariantSubstitution_comap_map
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.minimalWeight_mk_ne_zero_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedWeightQuotientMap_mul
