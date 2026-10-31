import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import Mathlib.Analysis.Matrix.Order

/-!
# The adelic product state

The candidate carrier of a second bridge between the primes: an adelic state whose archimedean
dilation part is Weil's correlation and whose finite-adelic part is the Haar state at the critical
temperature. On `Aff(ℚ)` it is the pointwise product

  `Φ(x ↦ ax + b) = ratCorr(|a|) · φ_Haar(x ↦ ax + b)`,

the archimedean factor read through the absolute slope and the finite-adelic factor through the
integer successor.

* **Schur products** (`IsPosDefKernel.mul`): the pointwise product of positive-definite kernels on a
  group is positive definite; its Gram matrices are Hadamard products (`posSemidef_gram_iff`).
* **Haar factors decide type** (`negIndex_mul_haarState_eq_zero_or_top`): every product of a
  Hermitian function with the Haar state is Hecke-supported, hence has index `0` or `∞`.
* **The adelic product state** (`negIndex_adelicWeilState_eq_zero_or_top`,
  `negIndex_adelicWeilState_of_riemannHypothesis`): index `0` or `∞`, and `0` under RH. Its successor
  is `W(B,B)·1_ℤ` (`adelicWeilState_translation`); its dilation part is
  `ratCorr(r)·(nd)^{−1/2}` (`adelicWeilState_dilation`), not Weil's correlation.

So the product of the two readings never carries a finite nonzero index. A carrier of the finite
stratum must have a finite-adelic factor outside Hecke support, as `haarOneNegativeSquare`, the Haar
state corrected by an archimedean slope function.
-/

open Complex Finset
open scoped ComplexConjugate ComplexOrder Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Schur products of positive-definite kernels -/

section Schur

variable {G : Type*} [Group G]

/-- A Hermitian kernel has positive semidefinite Gram matrices iff it is positive definite. -/
theorem posSemidef_gram_iff {k : G → ℂ} (hk : IsHermKernel k) :
    IsPosDefKernel k ↔ ∀ (n : ℕ) (x : Fin n → G), (gram k x).PosSemidef := by
  have hform : ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      star c ⬝ᵥ (gram k x *ᵥ c) = ((hermQuad (gram k x) c : ℝ) : ℂ) := by
    intro n x c
    have e : star c ⬝ᵥ (gram k x *ᵥ c) = ∑ a, ∑ b, conj (c a) * k ((x a)⁻¹ * x b) * c b := by
      simp only [dotProduct, Matrix.mulVec, gram, Pi.star_apply, Finset.mul_sum, Complex.star_def]
      exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    rw [e, hermQuad_gram]
    exact (Complex.conj_eq_iff_re.mp (conj_gramForm hk x c)).symm
  constructor
  · intro h n x
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨gram_isHermitian hk x, fun c => ?_⟩
    rw [hform]
    exact Complex.zero_le_real.mpr (h.hermQuad_nonneg x c)
  · intro h
    refine ⟨hk, fun n x c => ?_⟩
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (h n x)).2 c
    rw [hform] at this
    exact Complex.zero_le_real.mp this

/-- **Schur product.** -/
theorem IsPosDefKernel.mul {k₁ k₂ : G → ℂ} (h₁ : IsPosDefKernel k₁) (h₂ : IsPosDefKernel k₂) :
    IsPosDefKernel fun g => k₁ g * k₂ g := by
  have hk : IsHermKernel fun g => k₁ g * k₂ g := fun g => by
    show k₁ g⁻¹ * k₂ g⁻¹ = conj (k₁ g * k₂ g)
    rw [h₁.1 g, h₂.1 g, map_mul]
  refine (posSemidef_gram_iff hk).mpr fun n x => ?_
  have e : gram (fun g => k₁ g * k₂ g) x = (gram k₁ x).hadamard (gram k₂ x) := by
    ext a b; rfl
  rw [e]
  exact ((posSemidef_gram_iff h₁.1).mp h₁ n x).hadamard ((posSemidef_gram_iff h₂.1).mp h₂ n x)

end Schur

/-! ### Haar factors -/

theorem isHermKernel_haarState : IsHermKernel haarState := fun g =>
  IsPosDefOnGroup.map_inv isPosDefOnGroup_haarState g

theorem isPosDefKernel_haarState : IsPosDefKernel haarState :=
  isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState

theorem isHeckeSupported_haarState : IsHeckeSupported haarState := fun g hg => by
  by_contra h
  exact hg (by simp [haarState, haarWeight, h])

/-- **Haar factors decide type.** The product of any Hermitian function with the Haar state has
index `0` or `∞`. -/
theorem negIndex_mul_haarState_eq_zero_or_top {φ : AffineGroupQ → ℂ} (hφ : IsHermKernel φ) :
    negIndex (fun g => φ g * haarState g) = 0 ∨ negIndex (fun g => φ g * haarState g) = ⊤ := by
  refine negIndex_eq_zero_or_top_of_isHeckeSupported (fun g => ?_) fun g hg =>
    isHeckeSupported_haarState g (right_ne_zero_of_mul hg)
  show φ g⁻¹ * haarState g⁻¹ = conj (φ g * haarState g)
  rw [hφ g, isHermKernel_haarState g, map_mul]

/-! ### The adelic product state -/

/-- The **adelic product state**: Weil's correlation of the absolute slope times the Haar state. -/
def adelicWeilState (g : AffineGroupQ) : ℂ := ratCorr (slopeAbs g) * haarState g

theorem isHermKernel_blindWeilState : IsHermKernel blindWeilState :=
  isHermKernel_ratCorr.comp slopeAbs

/-- The adelic product state has index `0` or `∞`. -/
theorem negIndex_adelicWeilState_eq_zero_or_top :
    negIndex adelicWeilState = 0 ∨ negIndex adelicWeilState = ⊤ :=
  negIndex_mul_haarState_eq_zero_or_top isHermKernel_blindWeilState

/-- Under RH the adelic product state is positive. -/
theorem negIndex_adelicWeilState_of_riemannHypothesis (hRH : RiemannHypothesis) :
    negIndex adelicWeilState = 0 := by
  have hW : IsPosDefKernel ratCorr :=
    isPosDefKernel_iff_isPosDefOnGroup.mpr (riemannHypothesis_iff_isPosDefOnGroup_ratCorr.mp hRH)
  exact (IsPosDefKernel.mul (hW.comp slopeAbs) isPosDefKernel_haarState).negIndex_eq_zero

/-- The successor of the adelic product state is the Haar successor scaled by `W(B, B)`. -/
theorem adelicWeilState_translation (b : ℚ) :
    adelicWeilState (translation b) = splineCorr 0 * if b.den = 1 then 1 else 0 := by
  rw [adelicWeilState, haarState_hasIntegerSuccessor, slopeAbs_translation]
  simp [ratCorr, logPos]

/-- The dilation part of the adelic product state is `ratCorr(r)·(nd)^{−1/2}`. -/
theorem adelicWeilState_dilation (u : posUnits) :
    adelicWeilState (dilation u) = ratCorr u * haarState (dilation u) := by
  rw [adelicWeilState, slopeAbs_dilation]

end GaloisForLFunctions.AdelicKreinGeometry
