import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsGramLimits

/-!
# Quadratic observables of the actual Gibbs Gram limit

Every fixed finite complex coefficient packet has a nonnegative real
limiting quadratic form, because the limiting kernel is a genuine
quantum fidelity Gram matrix. The actual form converges with o(d)
error. The construction does not assume finite-state Gibbs matrices
are Hermitian or positive semidefinite.
-/
noncomputable section
open Real Filter Set Matrix
open scoped Topology BigOperators ComplexOrder
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeACriticalGramForm (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) : ℂ :=
  star z ⬝ᵥ (egbFixedChargeACriticalGram n x *ᵥ z)

def egbFixedChargeAGibbsGramForm (w φ τ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) : ℂ :=
  star z ⬝ᵥ (egbFixedChargeAGibbsGram w φ τ l₁ l₂ n x *ᵥ z)

theorem egbFixedChargeACriticalGramForm_nonneg (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    0 ≤ egbFixedChargeACriticalGramForm n x z :=
  (egbFixedChargeACriticalGram_posSemidef n x).dotProduct_mulVec_nonneg z

theorem egbFixedChargeACriticalGramForm_re_nonneg (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    0 ≤ (egbFixedChargeACriticalGramForm n x z).re :=
  (Complex.nonneg_iff.mp (egbFixedChargeACriticalGramForm_nonneg n x z)).1

theorem egbFixedChargeACriticalGramForm_im_zero (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    (egbFixedChargeACriticalGramForm n x z).im = 0 :=
  (Complex.nonneg_iff.mp (egbFixedChargeACriticalGramForm_nonneg n x z)).2.symm

theorem egbFixedChargeAGibbsGramForm_correction_identity (w φ τ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    star z ⬝ᵥ (egbFixedChargeAGibbsGramCorrection w φ τ l₁ l₂ n x *ᵥ z) =
      (egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z - egbFixedChargeACriticalGramForm n x z) /
        (egbCoexistenceASymmetricRatio τ : ℂ) := by
  unfold egbFixedChargeAGibbsGramCorrection egbFixedChargeAGibbsGramForm egbFixedChargeACriticalGramForm
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem egbFixedChargeAGibbsGramForm_critical_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    Tendsto (fun τ => egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z) atBot
      (𝓝 (egbFixedChargeACriticalGramForm n x z)) := by
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => star z ⬝ᵥ (M *ᵥ z)) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  simpa only [Function.comp_def, egbFixedChargeAGibbsGramForm, egbFixedChargeACriticalGramForm] using
    hc.continuousAt.tendsto.comp (egbFixedChargeAGibbsGram_critical_limit w φ l₁ l₂ n x)

theorem egbFixedChargeAGibbsGramForm_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) (z : Fin n → ℂ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsGramForm w φ τ l₁ l₂ n x z - egbFixedChargeACriticalGramForm n x z) /
      (egbCoexistenceASymmetricRatio τ : ℂ)) atBot (𝓝 (0 : ℂ)) := by
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => star z ⬝ᵥ (M *ᵥ z)) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  have h := hc.continuousAt.tendsto.comp (egbFixedChargeAGibbsGramCorrection_zero_limit w φ l₁ l₂ n x)
  simpa only [Function.comp_def, egbFixedChargeAGibbsGramForm_correction_identity, Matrix.zero_mulVec, dotProduct_zero] using h

end GaloisForLFunctions.HTGeometry
