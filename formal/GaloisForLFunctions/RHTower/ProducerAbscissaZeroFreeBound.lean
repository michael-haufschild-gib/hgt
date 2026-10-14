import GaloisForLFunctions.RHTower.RelaxedHerglotzProducerFloor
import GaloisForLFunctions.RHTower.XiLogDerivReStripBound
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# A zero-free half-plane carries the von Mangoldt producer

Let `½ ≤ σ₀` and suppose every zero of `ξ` has real part at most `σ₀`.

**Theorem** (`herglotzProducerOn_vonMangoldt_of_xi_zeros_re_le`).  Then `Λ` is a Herglotz producer
on `Re s > σ₀`, with continuation `ξ′/ξ`.  By the functional equation every zero also has real part
at least `1 − σ₀`, so `(Re ρ − ½)² ≤ (σ₀ − ½)² < (Re s − ½)²` for `Re s > σ₀`, and the
line-conjugate pair law (`re_logDeriv_xi_nonneg_of_strip_bound`) gives `Re ξ′/ξ(s) ≥ 0`.

**Corollary** (`producerAbscissa_le_of_xi_zeros_re_le`).  The producer abscissa is at most every
level `σ₀ ≥ ½` to the right of all zeros of `ξ`.  This extends `herglotzProducerOn_one_vonMangoldt`
(the level `1`) to every zero-free half-plane.
-/

open Complex Set

noncomputable section

namespace RHTower.RelaxedHerglotz

/-- **`Λ` is a producer on every half-plane to the right of all zeros of `ξ`.** -/
theorem herglotzProducerOn_vonMangoldt_of_xi_zeros_re_le {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hz : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ₀) :
    IsHerglotzProducerOn σ₀ fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hxi : ∀ s : ℂ, σ₀ < s.re → xi s ≠ 0 := fun s hs h => by linarith [hz s h]
  refine ⟨logDeriv xi, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · exact (((xi_differentiable.analyticAt s).deriv.differentiableAt).div
      (xi_differentiable s) (hxi s hs)).differentiableWithinAt
  · refine re_logDeriv_xi_nonneg_of_strip_bound (by linarith) (hxi s hs) fun q => ?_
    have h1 : ((q.1 : ℂ)).re ≤ σ₀ := hz _ (xi_xiZeroCopy_eq_zero q)
    have h2 : (1 - (q.1 : ℂ)).re ≤ σ₀ := hz _ (by rw [xi_one_sub]; exact xi_xiZeroCopy_eq_zero q)
    rw [Complex.sub_re, Complex.one_re] at h2
    nlinarith
  · rw [WeilSpectral.logDeriv_xi_eq_datum hs, weilFunction_eq_archPart_sub, lamC_vonMangoldt]
    unfold archPart zetaArchimedeanDatum
    ring

/-- **The producer abscissa is at most the zero abscissa**: every level `σ₀ ≥ ½` to the right of
all zeros of `ξ` carries the log-bounded producer `Λ`. -/
theorem producerAbscissa_le_of_xi_zeros_re_le {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hz : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ₀) : producerAbscissa ≤ σ₀ := by
  refine csInf_le bddBelow_producerLevels ⟨fun n => ArithmeticFunction.vonMangoldt n,
    fun n => ?_, herglotzProducerOn_vonMangoldt_of_xi_zeros_re_le hσ₀ hz⟩
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log

end RHTower.RelaxedHerglotz
