import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralBasis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Neutral extension preserves and reflects exactness

Let `B = K[hᵢ]` act on `P = K[zᵢ,wᵢ]` through `hᵢ = zᵢwᵢ`.
For every `B`-module `M`, the tensor product `P ⊗[B] M` is the module of
finitely supported weight families with entries in `M`. On a pure tensor,
the coefficient at weight `q` is the neutral extraction of its polynomial
factor acting on its module factor.

The relative basis makes `P` faithfully flat over `B`. Extension therefore
preserves and reflects exactness, injectivity, and surjectivity of arbitrary
module maps. The zero-weight coordinate explicitly splits the unit tensor
injection, so no module element disappears under extension.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module
open scoped TensorProduct PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- The nontrivial free paired polynomial module is faithfully flat over neutral variables. -/
theorem pairedNeutral_faithfullyFlat :
    Module.FaithfullyFlat (MvPolynomial ι K) (MvPolynomial (ι ⊕ ι) K) := by
  letI := pairedNeutral_free (ι := ι) K
  infer_instance

variable (M : Type*) [AddCommGroup M] [Module (MvPolynomial ι K) M]

/-- Arbitrary module coefficients may be expanded independently in all integral weights. -/
def pairedNeutralTensorEquiv :
    (MvPolynomial (ι ⊕ ι) K ⊗[MvPolynomial ι K] M) ≃ₗ[MvPolynomial ι K] ((ι → ℤ) →₀ M) :=
  ((pairedNeutralEquiv K).rTensor M).trans
    (TensorProduct.finsuppScalarLeft (MvPolynomial ι K) M (ι → ℤ))

/-- Pure tensors have the expected extracted neutral coefficients. -/
theorem pairedNeutralTensorEquiv_tmul (P : MvPolynomial (ι ⊕ ι) K) (m : M) (q : ι → ℤ) :
    pairedNeutralTensorEquiv K M (P ⊗ₜ[MvPolynomial ι K] m) q =
      pairedWeightExtraction K q P • m := by
  simp only [pairedNeutralTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    TensorProduct.finsuppScalarLeft_apply_tmul_apply, pairedNeutralEquiv_apply]

/-- A single weight coefficient is its minimal monomial tensored with that coefficient. -/
theorem pairedNeutralTensorEquiv_symm_single (q : ι → ℤ) (m : M) :
    (pairedNeutralTensorEquiv K M).symm (Finsupp.single q m) =
      minimalPairedMonomial K q ⊗ₜ[MvPolynomial ι K] m := by
  simp only [pairedNeutralTensorEquiv, LinearEquiv.symm_trans_apply,
    TensorProduct.finsuppScalarLeft_symm_apply_single, LinearEquiv.symm_rTensor,
    LinearEquiv.rTensor_tmul]
  congr 1
  change pairedNeutralAssembly K (Finsupp.single q 1) = _
  simp [pairedNeutralAssembly]

/-- Vanishing after extension is exactly coefficientwise vanishing. -/
theorem pairedNeutralTensor_eq_zero_iff
    (t : MvPolynomial (ι ⊕ ι) K ⊗[MvPolynomial ι K] M) :
    t = 0 ↔ ∀ q, pairedNeutralTensorEquiv K M t q = 0 := by
  constructor
  · rintro rfl q
    simp
  · intro h
    apply (pairedNeutralTensorEquiv K M).injective
    ext q
    simpa only [map_zero, Finsupp.zero_apply] using h q

/-- Extracting the zero weight recovers an element tensored with the constant polynomial one. -/
theorem pairedNeutral_one_tmul_injective :
    Function.Injective (fun m : M => (1 : MvPolynomial (ι ⊕ ι) K) ⊗ₜ[MvPolynomial ι K] m) := by
  intro m n h
  have he := congrArg (fun t => pairedNeutralTensorEquiv K M t (0 : ι → ℤ)) h
  have hx : pairedWeightExtraction K (0 : ι → ℤ) (1 : MvPolynomial (ι ⊕ ι) K) = 1 := by
    have hz := pairedWeightExtraction_smul_minimal K (0 : ι → ℤ) 0 1
    simpa only [minimalPairedMonomial_zero, one_smul, if_pos rfl, ite_true] using hz
  simpa only [pairedNeutralTensorEquiv_tmul, hx, one_smul] using he

variable {M} {N T : Type*} [AddCommGroup N] [AddCommGroup T]
  [Module (MvPolynomial ι K) N] [Module (MvPolynomial ι K) T]

/-- Paired polynomial extension preserves and reflects exact sequences. -/
theorem pairedNeutralTensor_exact_iff (f : M →ₗ[MvPolynomial ι K] N)
    (g : N →ₗ[MvPolynomial ι K] T) :
    Function.Exact (f.lTensor (MvPolynomial (ι ⊕ ι) K))
      (g.lTensor (MvPolynomial (ι ⊕ ι) K)) ↔ Function.Exact f g := by
  letI := pairedNeutral_faithfullyFlat (ι := ι) K
  exact Module.FaithfullyFlat.lTensor_exact_iff_exact _ _ f g

theorem pairedNeutralTensor_injective_iff (f : M →ₗ[MvPolynomial ι K] N) :
    Function.Injective (f.lTensor (MvPolynomial (ι ⊕ ι) K)) ↔ Function.Injective f := by
  letI := pairedNeutral_faithfullyFlat (ι := ι) K
  exact Module.FaithfullyFlat.lTensor_injective_iff_injective _ _ f

theorem pairedNeutralTensor_surjective_iff (f : M →ₗ[MvPolynomial ι K] N) :
    Function.Surjective (f.lTensor (MvPolynomial (ι ⊕ ι) K)) ↔ Function.Surjective f := by
  letI := pairedNeutral_faithfullyFlat (ι := ι) K
  exact Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ _ f

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutral_faithfullyFlat
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralTensorEquiv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralTensor_exact_iff
