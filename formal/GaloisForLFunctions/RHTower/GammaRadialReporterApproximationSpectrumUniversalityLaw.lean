import GaloisForLFunctions.HTGeometry.GammaGaugeClockVarianceSeparation
import GaloisForLFunctions.RHTower.HilbertSchmidtOperatorBridge

/-!
# Gamma radial-reporter approximation-spectrum universality

The Gamma factorial reporter has an exact finite-rank approximation budget at every radial scale:
each approximation number is bounded by the omitted diagonal factorial energy.  Its approximation
spectrum therefore vanishes, while every nonzero-scale reporter remains injective with dense
proper range.
-/

open ContinuousLinearMap Filter

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The approximation number at any finite coordinate cutoff is controlled by the exact omitted
Gamma factorial reporter energy. -/
theorem approxNumber_gammaRadialReporter_le_factorialTail
    (rho : ℝ) (s : Finset ℕ) :
    approxNumber (gammaRadialReporter rho) s.card ≤
      Real.sqrt
        (∑' i : {i // i ∉ s}, ‖gammaRadialReporterCoefficient rho i‖ ^ (2 : ℕ)) := by
  have hHS : IsHilbertSchmidt (gammaRadialReporter rho) :=
    HilbertSchmidt.isHilbertSchmidt_toOperator
      (gammaRadialReporterKernel_isHS rho)
  have htail := approxNumber_le_hsTail hHS (HilbertSchmidt.lpBasis ℕ) s
  convert htail using 1
  apply congrArg Real.sqrt
  apply tsum_congr
  intro i
  rw [HilbertSchmidt.lpBasis_apply, norm_gammaRadialReporter_single]

/-- At every radial scale the Gamma reporter approximation spectrum tends to zero. -/
theorem tendsto_approxNumber_gammaRadialReporter_zero (rho : ℝ) :
    Tendsto (approxNumber (gammaRadialReporter rho)) atTop (nhds 0) := by
  apply tendsto_approxNumber_zero_of_isHilbertSchmidt
  exact HilbertSchmidt.isHilbertSchmidt_toOperator
    (gammaRadialReporterKernel_isHS rho)

/-- **Gamma radial-reporter complete approximation-spectrum universality law.**  Every finite
cutoff has the exact factorial tail as an error majorant.  At nonzero scale, the resulting
vanishing approximation spectrum belongs to a compact injective reporter with dense proper
range. -/
theorem gammaRadialReporter_completeApproximationSpectrumUniversality
    {rho : ℝ} (hrho : rho ≠ 0) :
    (∀ s : Finset ℕ,
      approxNumber (gammaRadialReporter rho) s.card ≤
        Real.sqrt
          (∑' i : {i // i ∉ s}, ‖gammaRadialReporterCoefficient rho i‖ ^ (2 : ℕ))) ∧
      Tendsto (approxNumber (gammaRadialReporter rho)) atTop (nhds 0) ∧
      IsCompactOperator (gammaRadialReporter rho) ∧
      Function.Injective (gammaRadialReporter rho) ∧
      DenseRange (gammaRadialReporter rho) ∧
      ¬ Function.Surjective (gammaRadialReporter rho) := by
  obtain ⟨hcompact, hinjective, hdense, hnonsurjective⟩ :=
    gammaRadialReporter_compact_injective_dense_nonsurjective hrho
  exact ⟨approxNumber_gammaRadialReporter_le_factorialTail rho,
    tendsto_approxNumber_gammaRadialReporter_zero rho,
    hcompact, hinjective, hdense, hnonsurjective⟩

end

end RHTower
