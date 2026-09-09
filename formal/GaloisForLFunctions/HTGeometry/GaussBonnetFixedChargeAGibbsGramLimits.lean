import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalGramRank

/-!
# Finite matrix limits of the actual Gibbs quantum-kernel approximation

Actual aligned Gibbs values on pairwise angle differences converge
to a positive semidefinite quantum Gram matrix of rank at most five.
The entire finite matrix error divided by phase asymmetry tends to
zero. Determinants of every size at least six consequently vanish
in the critical limit. No finite-state positivity is assumed.
-/
noncomputable section
open Real Filter Set
open scoped Topology BigOperators ComplexOrder
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsGram (w φ τ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂ (x i - x j) : ℂ)

def egbFixedChargeAGibbsGramCorrection (w φ τ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (egbCoexistenceASymmetricRatio τ : ℂ)⁻¹ •
    (egbFixedChargeAGibbsGram w φ τ l₁ l₂ n x - egbFixedChargeACriticalGram n x)

theorem egbFixedChargeAGibbsGram_critical_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsGram w φ τ l₁ l₂ n x) atBot (𝓝 (egbFixedChargeACriticalGram n x)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_limit w φ l₁ l₂ 0).tendsto_at (x i - x j)
  simp only [iteratedDeriv_zero] at h
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, egbFixedChargeAGibbsGram, egbFixedChargeACriticalGram, Matrix.of_apply, Complex.ofReal_pow] using hc

theorem egbFixedChargeAGibbsGramCorrection_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsGramCorrection w φ τ l₁ l₂ n x) atBot (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ 0).tendsto_at (x i - x j)
  simp only [iteratedDeriv_zero] at h
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simp only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_zero] at hc
  simpa only [egbFixedChargeAGibbsGramCorrection, egbFixedChargeAGibbsGram, egbFixedChargeACriticalGram,
    Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hc

theorem egbFixedChargeAGibbsGram_large_determinant_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (x : Fin (n + 6) → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsGram w φ τ l₁ l₂ (n + 6) x).det) atBot (𝓝 (0 : ℂ)) := by
  have hc : Continuous (fun M : Matrix (Fin (n + 6)) (Fin (n + 6)) ℂ => M.det) :=
    continuous_id.matrix_det
  have h := hc.continuousAt.tendsto.comp (egbFixedChargeAGibbsGram_critical_limit w φ l₁ l₂ (n + 6) x)
  simpa only [Function.comp_def, egbFixedChargeACriticalGram_det_zero] using h

end GaloisForLFunctions.HTGeometry
