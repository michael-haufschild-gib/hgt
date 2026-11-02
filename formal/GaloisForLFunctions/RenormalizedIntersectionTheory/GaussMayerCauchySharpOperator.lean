import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyL2
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyHighFrequency
import GaloisForLFunctions.HTGeometry.CircleSymbolGroupCStar

/-!
# Sharp norm of actual logarithmic Cauchy averaging

The central Fourier multiplier is the exact operator norm. Its high-height
asymptotic produces amplified fields below real part one. At real part one
every finite height contracts strictly, but a common strict gap exists only above one.
-/

open Complex Set Filter MeasureTheory FourierTransform
open scoped Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open GaloisForLFunctions.HTGeometry
open MayerCauchyL2 MayerCauchyMellinSymbol
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchySharpOperator

/-- The actual Cauchy operator norm is exactly its central Gamma multiplier. -/
theorem operator_norm_eq {w : ℂ} (hw : 0 < w.re) :
    ‖operator hw‖ = ‖symbol w (w/2)‖ := by
  apply le_antisymm (operator_norm_le hw)
  have hc := continuous_fourier_of_integrable' (logKernel_integrable hw)
  have h := le_norm_fourierMulCLM hc.measurable (norm_nonneg (symbol w (w/2)))
    (fourier_logKernel_norm_le hw) (w₀ := 0) hc.continuousAt
  rw [← operator_eq_multiplier hw,fourier_logKernel_symbol hw] at h
  simpa only [mul_zero,ofReal_zero,zero_mul,add_zero] using h

/-- Restrict the actual operator family to a fixed positive spectral abscissa. -/
def verticalOperator {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  operator (w := (σ : ℂ)+(τ : ℂ)*I) (by simpa using hσ)

/-- The high-height Gamma law is the sharp limit of the actual operator norm. -/
theorem tendsto_operator_norm {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun τ : ℝ => ‖verticalOperator hσ τ‖) atTop (𝓝 ((2 : ℝ)^((1-σ)/2))) := by
  have h := MayerCauchyHighFrequency.tendsto_norm_symbol (α := σ/2) hσ
    (by linarith only [hσ]) (by linarith only [hσ])
  apply h.congr'
  filter_upwards [] with τ
  rw [verticalOperator,operator_norm_eq]
  have he : ((σ : ℂ)+(τ : ℂ)*I)/2=((σ/2 : ℝ) : ℂ)+(τ : ℂ)/2*I := by
    push_cast
    ring
  rw [he]

/-- A norm above one produces an actual amplified square-integrable field. -/
theorem exists_amplified_field {w : ℂ} (hw : 0 < w.re) (hamp : 1 < ‖operator hw‖) :
    ∃ f : Lp ℂ 2 (volume : Measure ℝ), ‖f‖ < ‖operator hw f‖ := by
  by_contra h
  push Not at h
  have hn : ‖operator hw‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa only [one_mul] using h f
  exact (not_lt_of_ge hn) hamp

/-- At every abscissa below one, the actual norm eventually exceeds one. -/
theorem eventually_operator_norm_gt_one {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ᶠ τ : ℝ in atTop, 1 < ‖verticalOperator hσ τ‖ := by
  have hlim : 1 < (2 : ℝ)^((1-σ)/2) :=
    Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  exact (tendsto_operator_norm hσ).eventually (lt_mem_nhds hlim)

/-- Scalar amplification is realized by actual logarithmic `L²` fields at every large height. -/
theorem eventually_amplified_field {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ᶠ τ : ℝ in atTop, ∃ f : Lp ℂ 2 (volume : Measure ℝ),
      ‖f‖ < ‖verticalOperator hσ τ f‖ := by
  filter_upwards [eventually_operator_norm_gt_one hσ hσ1] with τ hτ
  exact exists_amplified_field (by simpa using hσ) hτ

/-- Strict contraction at each spectral height has the exact threshold `σ=1`. -/
theorem all_heights_contraction_iff {σ : ℝ} (hσ : 0 < σ) :
    (∀ τ : ℝ, ‖verticalOperator hσ τ‖ < 1) ↔ 1 ≤ σ := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨τ,hτ⟩ := (eventually_operator_norm_gt_one hσ (lt_of_not_ge hn)).exists
    exact (not_lt_of_ge (h τ).le) hτ
  · intro hσ1 τ
    exact operator_contractive (by simpa using hσ1)

/-- A single strict contraction bound valid at every height exists exactly above `σ=1`. -/
theorem uniform_gap_iff {σ : ℝ} (hσ : 0 < σ) :
    (∃ c : ℝ, c < 1 ∧ ∀ τ : ℝ, ‖verticalOperator hσ τ‖ ≤ c) ↔ 1 < σ := by
  constructor
  · rintro ⟨c,hc,hbound⟩
    have hlim : (2 : ℝ)^((1-σ)/2) ≤ c :=
      le_of_tendsto (tendsto_operator_norm hσ) (Eventually.of_forall hbound)
    by_contra hn
    have he : 0 ≤ (1-σ)/2 := by linarith only [le_of_not_gt hn]
    have hp : 1 ≤ (2 : ℝ)^((1-σ)/2) := Real.one_le_rpow (by norm_num) he
    linarith only [hp,hlim,hc]
  · intro hσ1
    have hc : (2 : ℝ)^((1-σ)/2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hσ1])
    refine ⟨(2 : ℝ)^((1-σ)/2),hc,?_⟩
    intro τ
    have h := operator_norm_lt (w := (σ : ℂ)+(τ : ℂ)*I) (by simpa using hσ)
    exact (by simpa only [verticalOperator,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
      Complex.ofReal_im,neg_zero,add_zero] using! h.le)

#print axioms operator_norm_eq
#print axioms tendsto_operator_norm
#print axioms exists_amplified_field
#print axioms eventually_operator_norm_gt_one
#print axioms eventually_amplified_field
#print axioms all_heights_contraction_iff
#print axioms uniform_gap_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchySharpOperator
