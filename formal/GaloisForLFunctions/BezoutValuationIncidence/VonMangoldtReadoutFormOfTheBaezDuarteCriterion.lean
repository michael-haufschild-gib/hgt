import GaloisForLFunctions.BezoutValuationIncidence.PronicBaezDuarteCriterion
import GaloisForLFunctions.RHTower.BaezDuarteDistanceLogLowerBound

/-!
# The Báez-Duarte criterion in Selberg coordinates

The pronic mean of the prefix discrepancy is the von Mangoldt readout,
`Σ_M L_N(M, c) w(M) = -Σ_e Λ(e) Y_c(e)`. Its pronic energy is the Gram form
`(Σ_e Λ(e) Y_c(e))² + Q^{ec}(c)`, where `Q^{ec}` is the energy-centered pronic Gram form. Since `w` has
total mass one, the Báez-Duarte residual of a row splits into a readout defect and a centered energy:

`Σ_M (1 + L_N(M, c))² w(M) = (1 - Σ_e Λ(e) Y_c(e))² + Q^{ec}(c)`.

Hence:

* **RH ⟺** for every `ε > 0` some finite row has `(1 - Σ_e Λ(e) Y_c(e))² + Q^{ec}(c) < ε`. The von
  Mangoldt readout must be steered to `1` while the energy-centered pronic energy vanishes.
* **Unconditional floor.** There is `κ > 0` such that every row on `[1, N]`, `N ≥ 2`, has
  `(1 - Σ_e Λ(e) Y_c(e))² + Q^{ec}(c) ≥ κ / log N`. This follows from the zeros on the critical line
  through the Báez-Duarte dual sequence. In the theory's own coordinates, readout and centered energy
  cannot both be made small faster than `1/log N`.
-/

open Finset Filter Topology RHTower ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The von Mangoldt readout `Σ_{2 ≤ e ≤ N} Λ(e) Y_c(e)` of a row. -/
def vonMangoldtReadout (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e

/-- **Readout–energy decomposition of the Báez-Duarte residual.** -/
theorem hasSum_one_add_sievePrefixDiscrepancy_sq (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ => (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)))
      ((1 - vonMangoldtReadout N c) ^ 2 + sieveEnergyCenteredPronicGramForm N c) := by
  have hw : HasSum (fun M : ℕ => 1 / ((M : ℝ) * ((M : ℝ) + 1))) 1 := RHTower.hasSum_pm_reciprocal_weight
  have hL := hasSum_sievePrefixDiscrepancy_div_pronicSeq N c
  have hL2 := hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq N c
  rw [sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered] at hL2
  have htot := (hw.add (hL.mul_left 2)).add hL2
  have hval : 1 + 2 * -∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e +
      ((∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) ^ (2 : ℕ) +
        sieveEnergyCenteredPronicGramForm N c) =
      (1 - vonMangoldtReadout N c) ^ 2 + sieveEnergyCenteredPronicGramForm N c := by
    rw [vonMangoldtReadout]
    ring
  rw [hval] at htot
  refine htot.congr_fun fun M => ?_
  rw [cast_pronicSeq_eq M]
  ring

/-- **The Báez-Duarte criterion in Selberg coordinates.** -/
theorem riemannHypothesis_iff_readout_and_centered_energy :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
      (1 - vonMangoldtReadout N c) ^ 2 + sieveEnergyCenteredPronicGramForm N c < ε := by
  rw [riemannHypothesis_iff_pronic_prefix_energy]
  refine forall₂_congr fun ε _ => exists₂_congr fun N c => ?_
  rw [(hasSum_one_add_sievePrefixDiscrepancy_sq N c).tsum_eq]

/-- **Unconditional floor.** Readout defect plus centered energy is at least `κ / log N`. -/
theorem exists_readout_centered_energy_floor :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 ≤ N → ∀ c : ℕ → ℝ,
      κ / Real.log N ≤ (1 - vonMangoldtReadout N c) ^ 2 + sieveEnergyCenteredPronicGramForm N c := by
  obtain ⟨κ, hκ, hfloor⟩ := exists_div_log_le_bdDistDiscrete_sq
  refine ⟨κ, hκ, fun N hN c => ?_⟩
  have hres := norm_sq_bdResidual_eq_pronicEnergy N c
  rw [(hasSum_one_add_sievePrefixDiscrepancy_sq N c).unique hres]
  have hle := bdDistDiscrete_le_norm_sub_sum N c
  have h0 := bdDistDiscrete_mem_Icc N
  calc κ / Real.log N ≤ bdDistDiscrete N ^ 2 := hfloor N hN
    _ ≤ ‖bdTarget - ∑ n ∈ Icc 1 N, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ ^ 2 :=
        pow_le_pow_left₀ h0.1 hle 2

end

end GaloisForLFunctions.BezoutValuationIncidence
