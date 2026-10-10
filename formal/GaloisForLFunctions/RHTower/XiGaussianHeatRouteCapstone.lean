import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminants
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalMeanCriterion
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalVinogradovKorobovGrowth

/-!
# Route HCF capstone: every exact reading of the zero heat trace

For the zero heat trace `ν(τ) = Σ_q e^{-τ z_q²}` and any one heat time `a > 0`, the following are
equivalent to RH (`hcf_route_capstone`):

1. `ν` is bounded on the vertical line `Re τ = a`;
2. the vertical Cesàro mean `(1/B)∫₀^B ν(a + ib) db` tends to `0`;
3. `ν` has no zeros in some right half-plane;
4. the vertical heat Gram form `Σ c_s c̄_t ν(a + i(s−t))` is positive semidefinite on `ℂ[ℝ]`;
5. the heat Hankel form of the moments `M_n(a) = Σ_q w_q^n e^{-a w_q}` is positive semidefinite;
6. the arch−prime Hankel form is positive semidefinite on the pole hyperplane `P(−¼) = 0`;
7. every Hankel determinant `det(M_{i+j}(a))_{i,j<N}` is positive.

The unconditional content of the route is the index law (`heatGram_negativeIndex_law`,
`heatHankel_negativeIndex_eq_card`, `archPrimeHankel_negativeIndex_eq_card_add_one`): each form
counts the off-line zero quadruples exactly, with one extra square for the arch−prime form.  On the
producer side, the vertical ceiling is at Vinogradov–Korobov strength
(`exists_norm_xiGaussianHeatTraceC_le_vinogradovKorobov`).
-/

open Complex Filter Topology Set Polynomial

namespace RHTower

/-- **Route HCF capstone.**  Seven exact readings of RH through the zero heat trace at one heat
time. -/
theorem hcf_route_capstone {a : ℝ} (ha : 0 < a) :
    (RiemannHypothesis ↔ ∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C) ∧
    (RiemannHypothesis ↔ Tendsto (fun B : ℝ => (1 / (B : ℂ)) *
      ∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I)) atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔ ∃ a₀ : ℝ, ∀ τ : ℂ, a₀ < τ.re → xiGaussianHeatTraceC τ ≠ 0) ∧
    (RiemannHypothesis ↔ ∀ c : HeatWeights, 0 ≤ (heatGram a c c).re) ∧
    (RiemannHypothesis ↔ ∀ P : ℂ[X], 0 ≤ (heatHankel a P P).re) ∧
    (RiemannHypothesis ↔ ∀ P : ℂ[X], P.eval (-1 / 4) = 0 → 0 ≤ (archPrimeHankel a P P).re) ∧
    (RiemannHypothesis ↔ ∀ N, 0 < (GaloisForLFunctions.HTGeometry.leadingMatrix
      (heatMomentArray a) N).det) :=
  ⟨riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha,
    riemannHypothesis_iff_tendsto_vertical_mean ha,
    riemannHypothesis_iff_xiGaussianHeatTraceC_zeroFree_halfPlane,
    riemannHypothesis_iff_heatGram_nonneg ha,
    riemannHypothesis_iff_heatHankel_nonneg ha,
    riemannHypothesis_iff_archPrimeHankel_nonneg_of_eval_neg_quarter ha,
    riemannHypothesis_iff_heatMomentDet_pos ha⟩

end RHTower
