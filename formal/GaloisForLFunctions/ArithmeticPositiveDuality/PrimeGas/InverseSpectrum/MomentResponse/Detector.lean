import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.Critical
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.FunctionalTrace

/-! # Which heat observables measure isometric quantum composition? -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology ContinuousLinearMap

/-- A positive heat observable singles out isometry by its normalized response exactly when it is Hilbert–Schmidt on the surviving gas. -/
theorem moment_detects_isometry_iff_hilbertSchmidt (P : Projection) {r : ℕ} (dim : MissingDimension P r)
    (hc : Conserving (projected P)) (q : GibbsExponent) :
    (∀ s : ℂ, 0 < s.re → (Tendsto (fun t : ℝ => Real.log (normalizedMomentResponse q s.re t)/Real.log t) atTop (𝓝 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x)) ↔ (momentOperator P q.val).IsHilbertSchmidt :=
  (moment_detects_isometry_iff q).trans (momentOperator_hilbertSchmidt_iff P dim hc q).symm

/-- The observable on the full prime gas already determines which orders recognize global composition. -/
theorem native_moment_detector_iff (q : GibbsExponent) :
    (∀ s : ℂ, 0 < s.re → (Tendsto (fun t : ℝ => Real.log (normalizedMomentResponse q s.re t)/Real.log t) atTop (𝓝 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x)) ↔
      (heatPower (criticalOperator^2) q.val).IsHilbertSchmidt := by
  let I : Projection := ⟨1,IsStarProjection.one GasOp⟩
  have hd : MissingDimension I 0 := (missingDimension_zero_iff I).mpr rfl
  have hc : Conserving (projected I) := (projected_conserves_iff I).mpr (by
    change Function.Injective ((1:GasOp)*criticalOperator)
    rw [one_mul]
    exact critical_injective)
  have he := (projected_eq_critical_iff I).mpr rfl
  simpa only [momentOperator,he] using moment_detects_isometry_iff_hilbertSchmidt I hd hc q

/-- Enforcing the measured difference of the two ordinary operator traces gives exactly the spectral amplitude window. -/
theorem momentAmplitudes_eq_trace_window (q : GibbsExponent) (hq : 1 < q.val) (σ t D : ℝ) :
    momentAmplitudes q σ t D = {x | ∃ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
      (riemannZeta (q.val:ℂ)).re - (opTrace (momentOperator P q.val)).re ≤ D ∧
      ‖relativePartition (physicalSpectrum P dim hc) (⟨σ,t⟩:ℂ)‖ = x} := by
  ext x
  constructor
  · rintro ⟨b,⟨P,dim,hc,rfl⟩,hd,he⟩
    exact ⟨P,dim,hc,(momentLoss_eq_fractional_trace P dim hc q hq) ▸ hd,he⟩
  · rintro ⟨P,dim,hc,hd,he⟩
    exact ⟨_,⟨P,dim,hc,rfl⟩,(momentLoss_eq_fractional_trace P dim hc q hq).symm ▸ hd,he⟩

#print axioms moment_detects_isometry_iff_hilbertSchmidt
#print axioms native_moment_detector_iff
#print axioms momentAmplitudes_eq_trace_window

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
