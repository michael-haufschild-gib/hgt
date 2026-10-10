import GaloisForLFunctions.RHTower.GaussianTopologicalGateEquivalences
import GaloisForLFunctions.RHTower.GaussianCentralGapMeanSquareBudget
import GaloisForLFunctions.RHTower.GaussianBudgetSignedMixtureLaw
import GaloisForLFunctions.RHTower.GaussianCentralGapZeroFreeRegionBudget

/-!
# The Gaussian topological gate: equivalent forms, shift no-go and unconditional baseline

With `P_σ(y) = Σ Λ(n) n^{-σ} e^{-yn²}`, `C_σ(y) = ∫₁^∞ u^{-σ} e^{-yu²} du` and the central gap
`G(u) = (P_½ − C_½)(e^{-u})`:

* **Twelve equivalent forms of RH** (`riemannHypothesis_tfae_gaussianTopologicalGateExtended`): the
  nine forms of `riemannHypothesis_tfae_gaussianTopologicalGate`, the two mean-square budgets
  `∫₀^U G² ≤ K(U+1)` and `∫₀^U G² ≤ K_ε e^{εU}`, and the differenced budget
  `(P_½ − C_½) − (P_1 − C_1) ≤ B` of the quotient Euler product `ζ(s)/ζ(s + ½)`.
* **Terminal state** (`gaussianTopologicalGate_terminalState`): unconditionally the central budget holds
  with exponent `1/4` and the Vinogradov–Korobov saving, while for every `0 < a < ½` the central budget
  of the Euler product `ζ(s − a)ζ(s + a)` fails.  The first fact is the producer baseline; the second
  shows that a producer must use the size of the coefficients.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- **The topological gate in twelve equivalent forms.** -/
theorem riemannHypothesis_tfae_gaussianTopologicalGateExtended :
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
      RoutePPrimitiveBaseCauchyTraceCapacityLaw,
      ∃ K : ℝ, ∀ U : ℝ, 0 ≤ U → ∫ u in (0 : ℝ)..U, gaussianCentralGapLog u ^ 2 ≤ K * (U + 1),
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ U : ℝ, 0 ≤ U →
        ∫ u in (0 : ℝ)..U, gaussianCentralGapLog u ^ 2 ≤ K * Real.exp (ε * U),
      ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        (gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y) -
          (gaussianWeightedPrimeMass 1 y - gaussianWeightedContinuumMass 1 y) ≤ B] := by
  have h9 := riemannHypothesis_tfae_gaussianTopologicalGate
  have hL2 := riemannHypothesis_tfae_gaussianCentralGapMeanSquare
  tfae_have 1 ↔ 2 := h9.out 0 1
  tfae_have 1 ↔ 3 := h9.out 0 2
  tfae_have 1 ↔ 4 := h9.out 0 3
  tfae_have 1 ↔ 5 := h9.out 0 4
  tfae_have 1 ↔ 6 := h9.out 0 5
  tfae_have 1 ↔ 7 := h9.out 0 6
  tfae_have 1 ↔ 8 := h9.out 0 7
  tfae_have 1 ↔ 9 := h9.out 0 8
  tfae_have 1 ↔ 10 := hL2.out 0 1
  tfae_have 1 ↔ 11 := hL2.out 0 2
  tfae_have 1 ↔ 12 := riemannHypothesis_iff_gaussianDifferenceBudget (by norm_num) (by norm_num)
  tfae_finish

/-- **Terminal state of the Gaussian topological gate.**  Unconditionally the central budget holds
with exponent `1/4` and the Vinogradov–Korobov saving; for every `0 < a < ½` the central budget of the
non-tempered Euler product `ζ(s − a)ζ(s + a)` fails. -/
theorem gaussianTopologicalGate_terminalState :
    (∃ C U₀ : ℝ, ∀ u : ℝ, U₀ ≤ u →
      |gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))| ≤
        C * Real.exp (u / 4 - u * vinogradovKorobovGaussianWidth u / 2)) ∧
    (∀ a : ℝ, 0 < a → a < 1 / 2 → ¬ ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      (gaussianWeightedPrimeMass (1 / 2 - a) y - gaussianWeightedContinuumMass (1 / 2 - a) y) +
        (gaussianWeightedPrimeMass (1 / 2 + a) y - gaussianWeightedContinuumMass (1 / 2 + a) y)
          ≤ B) :=
  ⟨exists_norm_gaussianCentralGap_le_vinogradovKorobov,
    fun _ ha ha2 => not_exists_gaussianEisensteinBudget ha ha2⟩

end

end RHTower
