import GaloisForLFunctions.HTGeometry.AddMonoidAlgebraTensorCoefficients
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic

/-!
# Normal forms for paired torus-weight polynomials

In `K[zᵢ,wᵢ]`, the torus character of a monomial is its exponent difference.
For each weight `q`, every exponent vector has a unique expression
`(q⁺+s,q⁻+s)`. Thus every polynomial of weight `q` factors uniquely as its
minimal monomial times a polynomial in the neutral products `zᵢwᵢ`.
The minimum degree in the `w` variables is the sum of the negative parts of `q`.

This is the minimal-monomial mechanism in §6.1 of Brown,
*Equivariant Quantisation of Hypertoric Varieties via Symplectic Cuts*,
before imposing the moment-map equations. The weight spaces here are actual
subspaces of the polynomial ring, defined by their coefficient supports.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial
variable {ι : Type*} [Fintype ι]

/-- The character of a monomial under opposite scaling of each variable pair. -/
def pairedWeight (d : (ι ⊕ ι) →₀ ℕ) : ι → ℤ :=
  fun i => (d (Sum.inl i) : ℤ) - d (Sum.inr i)

/-- Minimal exponents forced by a character, plus neutral paired exponents. -/
def normalWeightExponent (q : ι → ℤ) (s : ι → ℕ) : (ι ⊕ ι) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim
    (fun i => (q i).toNat + s i) (fun i => (-q i).toNat + s i))

@[simp] theorem normalWeightExponent_inl (q : ι → ℤ) (s : ι → ℕ) (i : ι) :
    normalWeightExponent q s (Sum.inl i) = (q i).toNat + s i := by
  simp [normalWeightExponent]

@[simp] theorem normalWeightExponent_inr (q : ι → ℤ) (s : ι → ℕ) (i : ι) :
    normalWeightExponent q s (Sum.inr i) = (-q i).toNat + s i := by
  simp [normalWeightExponent]

@[simp] theorem pairedWeight_normal (q : ι → ℤ) (s : ι → ℕ) :
    pairedWeight (normalWeightExponent q s) = q := by
  funext i
  simp only [pairedWeight, normalWeightExponent_inl, normalWeightExponent_inr,
    Nat.cast_add, add_sub_add_right_eq_sub, Int.toNat_sub_toNat_neg]

/-- Every exponent vector of a fixed character has unique neutral exponents. -/
def weightExponentEquiv (q : ι → ℤ) :
    (ι → ℕ) ≃ {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q} where
  toFun s := ⟨normalWeightExponent q s, pairedWeight_normal q s⟩
  invFun d i := min (d.1 (Sum.inl i)) (d.1 (Sum.inr i))
  left_inv s := by
    funext i
    simp only [normalWeightExponent_inl, normalWeightExponent_inr]
    omega
  right_inv d := by
    apply Subtype.ext
    have hd (i : ι) : (d.1 (Sum.inl i) : ℤ) - d.1 (Sum.inr i) = q i :=
      congrFun d.2 i
    ext (i | i)
    · simp only [normalWeightExponent_inl]
      have := hd i
      omega
    · simp only [normalWeightExponent_inr]
      have := hd i
      omega

/-- Minimum degree in the negatively weighted variables. -/
def weightSlack (q : ι → ℤ) : ℕ := ∑ i, (-q i).toNat

/-- Degree for the circle action that scales only the second variable in each pair. -/
def cutDegree (d : (ι ⊕ ι) →₀ ℕ) : ℕ := ∑ i, d (Sum.inr i)

/-- Forced slack and neutral degree add without cancellation. -/
theorem cutDegree_normalWeightExponent (q : ι → ℤ) (s : ι → ℕ) :
    cutDegree (normalWeightExponent q s) = weightSlack q + ∑ i, s i := by
  simp only [cutDegree, normalWeightExponent_inr, Finset.sum_add_distrib, weightSlack]

/-- Every monomial pays at least the slack forced by its character. -/
theorem weightSlack_le_cutDegree (d : (ι ⊕ ι) →₀ ℕ) :
    weightSlack (pairedWeight d) ≤ cutDegree d := by
  apply Finset.sum_le_sum
  intro i _
  simp only [pairedWeight]
  omega

/-- A character occurs below a cut exactly when its slack fits the cut. -/
theorem exists_weight_cutDegree_le_iff (q : ι → ℤ) (D : ℕ) :
    (∃ d, pairedWeight d = q ∧ cutDegree d ≤ D) ↔ weightSlack q ≤ D := by
  constructor
  · rintro ⟨d, rfl, hd⟩
    exact (weightSlack_le_cutDegree d).trans hd
  · intro h
    refine ⟨normalWeightExponent q 0, pairedWeight_normal q 0, ?_⟩
    simpa only [cutDegree_normalWeightExponent, Pi.zero_apply, Finset.sum_const_zero,
      add_zero] using h

variable (K : Type*) [Field K]
open HTGeometry.AddMonoidAlgebraTensorCoefficients

/-- The character of a monomial under opposite scaling of each variable pair. -/
/-- The polynomial subspace with the specified torus character. -/
def pairedWeightSpace (q : ι → ℤ) : Submodule K (MvPolynomial (ι ⊕ ι) K) :=
  restrictSupport K {d | pairedWeight d = q}

/-- The character of a monomial under opposite scaling of each variable pair. -/
/-- The neutral monomial basis parametrizes the entire weight subspace. -/
def pairedWeightSpaceEquiv (q : ι → ℤ) :
    MvPolynomial ι K ≃ₗ[K] pairedWeightSpace K q :=
  (coeffLinearEquiv K (ι →₀ ℕ)).trans
    ((Finsupp.lcongr (Finsupp.equivFunOnFinite.trans (weightExponentEquiv q))
      (LinearEquiv.refl K K)).trans
      (basisRestrictSupport K {d | pairedWeight d = q}).repr.symm)

/-- The coefficient equivalence sends each ordinary monomial to its weight normal form. -/
theorem pairedWeightSpaceEquiv_monomial (q : ι → ℤ) (s : ι →₀ ℕ) (c : K) :
    (pairedWeightSpaceEquiv K q (monomial s c)).1 =
      monomial (normalWeightExponent q s) c := by
  classical
  simp only [pairedWeightSpaceEquiv, LinearEquiv.trans_apply,
    show (monomial s c : MvPolynomial ι K) = AddMonoidAlgebra.single s c from rfl,
    coeffLinearEquiv_single, Finsupp.lcongr_single, LinearEquiv.refl_apply]
  change (coeffLinearEquiv K _).symm
    (((Finsupp.supportedEquivFinsupp {d | pairedWeight d = q}).symm
      (Finsupp.single ((Finsupp.equivFunOnFinite.trans (weightExponentEquiv q)) s) c)).1) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Normal exponents split into minimal and neutral parts. -/
theorem normalWeightExponent_split (q : ι → ℤ) (s : ι → ℕ) :
    normalWeightExponent q s = normalWeightExponent q 0 + normalWeightExponent 0 s := by
  ext (i | i) <;> simp

/-- The minimal weight monomial times a neutral monomial is the unique normal monomial. -/
theorem pairedWeight_monomial_factor (q : ι → ℤ) (s : ι → ℕ) (c : K) :
    monomial (normalWeightExponent q s) c =
      monomial (normalWeightExponent q 0) (1 : K) *
        monomial (normalWeightExponent 0 s) c := by
  rw [monomial_mul, one_mul, ← normalWeightExponent_split]

/-- Substitute the invariant products `zᵢwᵢ` for independent variables. -/
def invariantSubstitution : MvPolynomial ι K →+* MvPolynomial (ι ⊕ ι) K :=
  eval₂Hom C (fun i => X (Sum.inl i) * X (Sum.inr i))

/-- Substitution of invariant products doubles each monomial exponent into a pair. -/
theorem invariantSubstitution_monomial (s : ι →₀ ℕ) (c : K) :
    invariantSubstitution K (monomial s c) = monomial (normalWeightExponent 0 s) c := by
  classical
  rw [invariantSubstitution, eval₂Hom_monomial, monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intro i; exact pow_zero _),
    Finsupp.prod_fintype _ _ (by intro i; exact pow_zero _), Fintype.prod_sum_type]
  simp only [normalWeightExponent_inl, normalWeightExponent_inr, Pi.zero_apply,
    neg_zero, Int.toNat_zero, zero_add, mul_pow, Finset.prod_mul_distrib]

/-- The basis equivalence is literal multiplication by the minimal monomial. -/
theorem pairedWeightSpaceEquiv_factor (q : ι → ℤ) (f : MvPolynomial ι K) :
    (pairedWeightSpaceEquiv K q f).1 =
      monomial (normalWeightExponent q 0) (1 : K) * invariantSubstitution K f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [pairedWeightSpaceEquiv_monomial, invariantSubstitution_monomial,
      pairedWeight_monomial_factor]
  | add f g hf hg =>
    simp only [map_add, Submodule.coe_add, hf, hg, mul_add]

/-- Every weight polynomial factors uniquely through the neutral products. -/
theorem pairedWeightSpace_unique_factor (q : ι → ℤ) (P : pairedWeightSpace K q) :
    ∃! f : MvPolynomial ι K,
      P.1 = monomial (normalWeightExponent q 0) (1 : K) * invariantSubstitution K f := by
  refine ⟨(pairedWeightSpaceEquiv K q).symm P, ?_, ?_⟩
  · dsimp only
    rw [← pairedWeightSpaceEquiv_factor, LinearEquiv.apply_symm_apply]
  · intro f hf
    apply (pairedWeightSpaceEquiv K q).injective
    apply Subtype.ext
    rw [pairedWeightSpaceEquiv_factor, LinearEquiv.apply_symm_apply]
    exact hf.symm

/-- Neutral products are algebraically independent. -/
theorem invariantSubstitution_injective : Function.Injective (invariantSubstitution (ι := ι) K) := by
  intro f g h
  apply (pairedWeightSpaceEquiv K (0 : ι → ℤ)).injective
  apply Subtype.ext
  rw [pairedWeightSpaceEquiv_factor, pairedWeightSpaceEquiv_factor, h]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis


