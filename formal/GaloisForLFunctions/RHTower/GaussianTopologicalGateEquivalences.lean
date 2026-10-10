import GaloisForLFunctions.RHTower.GaussianGapSignPhaseTransition
import GaloisForLFunctions.RHTower.GaussianPrimeChebyshevBias
import GaloisForLFunctions.RHTower.FormationAnchoredCubicEndpoint
import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseCauchyCapacityReduction

/-!
# The equivalent forms of the topological gate

With `P(y) = Σ Λ(n) n^{-1/2} e^{-yn²}`, `Π(y) = Σ_p (log p) p^{-1/2} e^{-yp²}` and
`C(y) = ∫₁^∞ u^{-1/2} e^{-yu²} du`, the following are equivalent
(`riemannHypothesis_tfae_gaussianTopologicalGate`):

1. RH;
2. the central budget `P ≤ C + K` on `(0, 1]`;
3. eventual negativity `P(y) < C(y)` for small `y` (complete archimedean bias);
4. the explicit inequality `P(y) − C(y) ≤ −1/10 + 32√y` on `(0, 1]`;
5. the Gaussian Chebyshev conjecture `Π(y) − C(y) → −∞`;
6. the sign abscissa of the Gaussian gaps is `½`;
7. **spectral form**: the Gaussian gap has no Bohr frequency at any weight `θ > ½`, i.e. every
   `θ`-weighted Bohr coefficient vanishes (`riemannHypothesis_iff_forall_weightedBohrCoefficient_eq_zero`);
8. the anchored-cubic sub-unit gate holds on every strict-right rectangle;
9. the base-Cauchy trace capacity law of the Burnol source.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- **Spectral form of RH.**  RH holds iff for every `θ > ½` all `θ`-weighted Bohr coefficients of
the central Gaussian gap vanish: no zero lies on any line `Re ρ = θ > ½`. -/
theorem riemannHypothesis_iff_forall_weightedBohrCoefficient_eq_zero :
    RiemannHypothesis ↔ ∀ θ : ℝ, 1 / 2 < θ → ∀ τ : ℝ, weightedBohrCoefficient θ τ = 0 := by
  constructor
  · intro hRH θ hθ τ
    by_contra h
    have hz := exists_xi_zero_of_weightedBohrCoefficient_ne_zero h
    exact (rh_iff_xi_ne_zero_right.mp hRH) _ (mem_rightHalf.mpr (by simpa using hθ)) hz
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hzero
    have hre := mem_rightHalf.mp hs
    exact weightedBohrCoefficient_ne_zero_of_xi_eq_zero hzero rfl (h s.re hre (s.im / 2))

/-- **The topological gate in nine equivalent forms.** -/
theorem riemannHypothesis_tfae_gaussianTopologicalGate :
    List.TFAE [
      RiemannHypothesis,
      ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        gaussianWeightedPrimeMass (1 / 2) y ≤ gaussianWeightedContinuumMass (1 / 2) y + K,
      ∀ᶠ y in 𝓝[>] 0,
        gaussianWeightedPrimeMass (1 / 2) y < gaussianWeightedContinuumMass (1 / 2) y,
      ∀ y : ℝ, 0 < y → y ≤ 1 →
        gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y ≤
          -1 / 10 + 32 * Real.sqrt y,
      Tendsto (fun y : ℝ =>
        gaussianCentralPrimeOnlyMass y - gaussianWeightedContinuumMass (1 / 2) y) (𝓝[>] 0) atBot,
      gaussianSignAbscissa = 1 / 2,
      ∀ θ : ℝ, 1 / 2 < θ → ∀ τ : ℝ, weightedBohrCoefficient θ τ = 0,
      ∀ R : FormationRectangle, ∃ x : Ioi (0 : ℝ),
        traceNorm CCMCircleL2 (R.anchoredCubicDefect x) < 1,
      RoutePPrimitiveBaseCauchyTraceCapacityLaw] := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_gaussianCentralPrimeBudget
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_eventually_gaussianCentralGap_neg
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_gaussianCentralGap_le_explicit
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_tendsto_gaussianPrimeOnlyGap_atBot
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_gaussianSignAbscissa_eq_half
  tfae_have 1 ↔ 7 := riemannHypothesis_iff_forall_weightedBohrCoefficient_eq_zero
  tfae_have 1 ↔ 8 := riemannHypothesis_iff_forall_exists_traceNorm_anchoredCubicDefect_lt_one
  tfae_have 1 ↔ 9 := routePPrimitiveBaseCauchyTraceCapacityLaw_iff_riemannHypothesis.symm
  tfae_finish

end

end RHTower
