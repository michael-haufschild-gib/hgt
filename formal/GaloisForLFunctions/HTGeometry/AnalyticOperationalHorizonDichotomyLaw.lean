import GaloisForLFunctions.HTGeometry.ObserverTemporalBirthValuationLaw

/-!
# Analytic operational-horizon dichotomy

An analytic response that vanishes at zero has exactly two possibilities.
It is the zero germ, or it unlocks at one finite positive Taylor order.
In the second case it factors as that power of the coupling times a
nonvanishing analytic unit, and the inverse-response observation horizon
has an exact finite nonzero scaling limit.

This separates a permanent analytic operational horizon from every nonzero
analytic weak link.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A response has a permanent analytic operational horizon when it vanishes
identically on some neighborhood of the uncoupled point. -/
def HasPermanentAnalyticHorizon (f : ℂ → ℂ) : Prop :=
  f =ᶠ[𝓝 0] (fun _ : ℂ => 0)

/-- A permanent analytic horizon is exactly a zero Taylor series. -/
theorem hasPermanentAnalyticHorizon_iff_series_eq_zero
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0) :
    HasPermanentAnalyticHorizon f ↔ series = 0 := by
  exact hf.locally_zero_iff

/-- **Permanent-horizon versus finite-unlocking dichotomy.** An analytic
response that vanishes at the uncoupled point is either locally identically
zero, or has one finite positive birth order, a nonvanishing analytic unit,
and an exact inverse-response power-law horizon. -/
theorem hasPermanentAnalyticHorizon_or_finiteUnlocking
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hf0 : f 0 = 0) :
    HasPermanentAnalyticHorizon f ∨
      ∃ (b : ℕ) (u : ℂ → ℂ),
        AnalyticSectorActive f ∧
        0 < b ∧
        AnalyticAt ℂ u 0 ∧
        u 0 ≠ 0 ∧
        (∀ g : ℂ, f g = g ^ b * u g) ∧
        Tendsto
          (fun g : ℂ => ‖g‖ ^ b / ‖f g‖)
          (𝓝[≠] 0)
          (𝓝 (‖u 0‖)⁻¹) := by
  by_cases hhorizon : HasPermanentAnalyticHorizon f
  · exact Or.inl hhorizon
  · have hactive : AnalyticSectorActive f := by
      simpa [HasPermanentAnalyticHorizon, AnalyticSectorActive] using hhorizon
    refine Or.inr
      ⟨analyticBirthOrder series, analyticBirthUnit f series,
        hactive, analyticBirthOrder_pos hf hf0 hactive,
        analyticBirthUnit_analyticAt hf,
        analyticBirthUnit_zero_ne hf hactive, ?_, ?_⟩
    · intro g
      exact analytic_eq_pow_birthOrder_mul_birthUnit hf g
    · exact tendsto_norm_pow_div_norm_analyticBirthOrder hf hactive

/-- Formal capstone joining the exact zero-series criterion to the exhaustive
finite-unlocking alternative. -/
theorem analyticOperationalHorizon_dichotomy_core
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hf0 : f 0 = 0) :
    (HasPermanentAnalyticHorizon f ↔ series = 0) ∧
    (HasPermanentAnalyticHorizon f ∨
      ∃ (b : ℕ) (u : ℂ → ℂ),
        AnalyticSectorActive f ∧
        0 < b ∧
        AnalyticAt ℂ u 0 ∧
        u 0 ≠ 0 ∧
        (∀ g : ℂ, f g = g ^ b * u g) ∧
        Tendsto
          (fun g : ℂ => ‖g‖ ^ b / ‖f g‖)
          (𝓝[≠] 0)
          (𝓝 (‖u 0‖)⁻¹)) := by
  exact
    ⟨hasPermanentAnalyticHorizon_iff_series_eq_zero hf,
      hasPermanentAnalyticHorizon_or_finiteUnlocking hf hf0⟩

end

end GaloisForLFunctions.HTGeometry
