import GaloisForLFunctions.BezoutValuationIncidence.VonMangoldtReadoutFormOfTheBaezDuarteCriterion
import GaloisForLFunctions.BezoutValuationIncidence.RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence

/-!
# The Báez-Duarte energy of the power-damped Möbius rows

The cofactor row `w_{ε,Q}` carries the power-damped Ramanujan weights `Y_ε(q)` as its Selberg
coordinates at level `Q + 1`. Its prefix discrepancy is the power-damped cumulative prefix. The pronic
mean of that prefix is the energy mean `m(ε, Q)`, and its pronic energy is `m(ε, Q)² + V(ε, Q)` with
`V` the energy variance. For the row `-w_{ε,Q}` the Báez-Duarte residual is therefore

`Σ_M (1 + L_{Q+1}(M, -w_{ε,Q}))² w(M) = (1 - m(ε, Q))² + V(ε, Q)`.

Two consequences in the receiver's own objects:

* **Sufficient condition.** If for every `η > 0` some `ε > 0` and `Q` have
  `(1 - m(ε, Q))² + V(ε, Q) < η`, the Riemann hypothesis holds.
* **Unconditional floor.** For every `ε > 0` and `Q ≥ 1`,
  `(1 - m(ε, Q))² + V(ε, Q) ≥ κ / log(Q + 1)`. The power-damped Möbius source cannot bring its energy mean
  near `1` and its energy variance near `0` faster than `1/log Q`.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

theorem sievePrefixDiscrepancy_neg (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M (fun d => -c d) = -sievePrefixDiscrepancy N M c := by
  rw [sievePrefixDiscrepancy_eq_neg_residue, sievePrefixDiscrepancy_eq_neg_residue, neg_neg,
    ← sum_neg_distrib]
  refine sum_congr rfl fun n _ => ?_
  ring

/-- **The Báez-Duarte energy of `-w_{ε,Q}`.** -/
theorem hasSum_baezDuarte_energy_pmCofactor {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    HasSum (fun M : ℕ => (1 + sievePrefixDiscrepancy (Q + 1) M
        (fun d => -pmCofactorDivisorWeight ε Q d)) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)))
      ((1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 + pmPowerDampedRamanujanEnergyVariance ε Q) := by
  set w := pmCofactorDivisorWeight ε Q
  have hW : HasSum (fun M : ℕ => 1 / ((M : ℝ) * ((M : ℝ) + 1))) 1 := RHTower.hasSum_pm_reciprocal_weight
  -- the pronic mean of the prefix is the energy mean
  have hL : HasSum (fun M : ℕ => sievePrefixDiscrepancy (Q + 1) M w / (pronicSeq M : ℝ))
      (pmPowerDampedRamanujanEnergyMean ε Q) := by
    have h := hasSum_sievePrefixDiscrepancy_div_pronicSeq (Q + 1) w
    rwa [← h.tsum_eq, tsum_sievePrefixDiscrepancy_pmCofactorDivisorWeight_div_pronicSeq] at h
  -- its pronic energy is `m² + V`
  have hL2 : HasSum (fun M : ℕ => sievePrefixDiscrepancy (Q + 1) M w ^ 2 / (pronicSeq M : ℝ))
      (pmPowerDampedRamanujanEnergyMean ε Q ^ 2 + pmPowerDampedRamanujanEnergyVariance ε Q) := by
    have h := hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq (Q + 1) w
    rwa [sievePronicDiscrepancyGramForm_pmCofactorDivisorWeight_eq,
      RHTower.pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance hε] at h
  have htot := (hW.sub (hL.mul_left 2)).add hL2
  have hval : 1 - 2 * pmPowerDampedRamanujanEnergyMean ε Q +
      (pmPowerDampedRamanujanEnergyMean ε Q ^ 2 + pmPowerDampedRamanujanEnergyVariance ε Q) =
      (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 + pmPowerDampedRamanujanEnergyVariance ε Q := by
    ring
  rw [hval] at htot
  refine htot.congr_fun fun M => ?_
  rw [sievePrefixDiscrepancy_neg, cast_pronicSeq_eq M]
  ring

/-- **Sufficient condition for RH in the receiver's objects.** -/
theorem riemannHypothesis_of_energyMean_variance
    (h : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ Q : ℕ,
      (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 + pmPowerDampedRamanujanEnergyVariance ε Q < η) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_pronic_prefix_energy.mpr fun η hη => ?_
  obtain ⟨ε, hε, Q, hlt⟩ := h η hη
  exact ⟨Q + 1, fun d => -pmCofactorDivisorWeight ε Q d, by
    rwa [(hasSum_baezDuarte_energy_pmCofactor hε Q).tsum_eq]⟩

/-- **Unconditional floor for the power-damped Möbius source.** -/
theorem exists_energyMean_variance_floor :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Q : ℕ, 1 ≤ Q →
      κ / Real.log ((Q : ℝ) + 1) ≤
        (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 + pmPowerDampedRamanujanEnergyVariance ε Q := by
  obtain ⟨κ, hκ, hfloor⟩ := exists_readout_centered_energy_floor
  refine ⟨κ, hκ, fun ε hε Q hQ => ?_⟩
  have h := hfloor (Q + 1) (by omega) (fun d => -pmCofactorDivisorWeight ε Q d)
  rw [← (hasSum_one_add_sievePrefixDiscrepancy_sq (Q + 1)
      (fun d => -pmCofactorDivisorWeight ε Q d)).unique (hasSum_baezDuarte_energy_pmCofactor hε Q)] at *
  push_cast at h
  exact h

end

end GaloisForLFunctions.BezoutValuationIncidence
