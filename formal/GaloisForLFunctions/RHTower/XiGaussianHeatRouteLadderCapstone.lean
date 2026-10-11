import GaloisForLFunctions.RHTower.XiGaussianHeatHankelInertia
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelRealNodeWitness
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantBlowup
import GaloisForLFunctions.RHTower.XiGaussianHeatRouteCapstone

/-!
# Route HCF: the heat Hankel ladder capstone

Let `Δ_N(a) = det(M_{i+j}(a))_{i,j<N}` be the heat Hankel determinants of the zero heat trace and
`H_a` the heat Hankel form.

**Unconditional structure** (`hcf_ladder_structure`), for every `a > 0`:

* `H_a` is nondegenerate with infinite positive index (`eq_zero_of_forall_heatHankel_eq_zero`,
  `exists_heatHankel_pos_subspace`); its negative index is the number of off-line zero quadruples;
* the window: `Δ_N(a) > 0` whenever `a N ≤ κ` (`heatMomentDet_pos_of_mul_le`);
* the height horizon: each fixed rank is positive at every heat time once all off-line zeros lie
  above a finite height (`exists_height_forall_le_heatMomentDet_pos`).

**Equivalences** (`hcf_ladder_capstone`): RH holds iff

1. `Re Σ_q e^{-a w_q} ∏_i (w_q − x_i)² ≥ 0` for every finite family of real nodes `x_i`;
2. for every rank `N`, `Δ_N(a) > 0` for all large heat times;
3. no `Δ_N` vanishes at any positive heat time;
4. for every `D` and `a₀ > 0`, some `a ∈ (0, a₀]` has `Δ_M(a) > 0` for all
   `M ≤ D log³(1/a)/a + 1`.

Without RH the window is pinned between `κ/N` and `≍ log³N/N`
(`exists_heatMomentDet_nonpos_small_time`).  The ladder therefore has no intermediate unconditional
statements beyond a polylogarithmic factor.
-/

open Complex Polynomial Filter
open GaloisForLFunctions.HTGeometry (leadingMatrix)

namespace RHTower

/-- **Unconditional structure of the heat Hankel ladder.** -/
theorem hcf_ladder_structure {a : ℝ} (ha : 0 < a) :
    (∀ P : ℂ[X], (∀ R : ℂ[X], heatHankel a P R = 0) → P = 0) ∧
    (∀ n : ℕ, ∃ V : Submodule ℂ ℂ[X], Module.finrank ℂ V = n ∧
      ∀ P ∈ V, P ≠ 0 → 0 < (heatHankel a P P).re) ∧
    (∀ N : ℕ, a * N ≤ routeUCompletedPrimeGammaAperture →
      0 < (leadingMatrix (heatMomentArray a) N).det) ∧
    (∀ N : ℕ, ∃ H : ℝ, (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
      H < |(xiSpectralPoint q).re|) →
      ∀ M ≤ N, ∀ b : ℝ, 0 < b → 0 < (leadingMatrix (heatMomentArray b) M).det) :=
  ⟨fun _ h => eq_zero_of_forall_heatHankel_eq_zero ha h, exists_heatHankel_pos_subspace ha,
    fun _ hN => heatMomentDet_pos_of_mul_le ha hN, exists_height_forall_le_heatMomentDet_pos⟩

/-- **Route HCF ladder capstone.**  Four further exact readings of RH through the heat Hankel
ladder. -/
theorem hcf_ladder_capstone {a : ℝ} (ha : 0 < a) :
    (RiemannHypothesis ↔
      ∀ s : Multiset ℝ, 0 ≤ (heatHankel a (realNodePoly s) (realNodePoly s)).re) ∧
    (RiemannHypothesis ↔
      ∀ N : ℕ, ∀ᶠ b in atTop, 0 < (leadingMatrix (heatMomentArray b) N).det) ∧
    (RiemannHypothesis ↔ ∀ N : ℕ, ∀ b : ℝ, 0 < b → heatMomentDet N b ≠ 0) ∧
    (RiemannHypothesis ↔ ∀ D a₀ : ℝ, 0 < a₀ → ∃ b : ℝ, 0 < b ∧ b ≤ a₀ ∧
      ∀ M : ℕ, (M : ℝ) ≤ D * Real.log (1 / b) ^ 3 / b + 1 →
        0 < (leadingMatrix (heatMomentArray b) M).det) :=
  ⟨riemannHypothesis_iff_realNodes_heatHankel_nonneg ha,
    riemannHypothesis_iff_forall_eventually_heatMomentDet_pos,
    riemannHypothesis_iff_heatMomentDet_ne_zero,
    riemannHypothesis_iff_superPolylog_window⟩

end RHTower
