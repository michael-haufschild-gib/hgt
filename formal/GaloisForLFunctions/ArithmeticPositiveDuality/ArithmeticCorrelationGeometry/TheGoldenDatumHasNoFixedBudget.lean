import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.RHTower.WeilKloostermanBound

/-!
# The golden datum has no fixed budget

The `𝔽_q` calibration of the loss law. For a curve datum the order-`j` observable is the power
sum `Σ_i β_i^j` of the normalized Frobenius eigenvalues.

* **A fixed budget forces purity** (`norm_le_one_of_bounded_powerSum`,
  `unitary_of_bounded_powerSum`). If the power sums are bounded by one constant at every order,
  every eigenvalue has `|β_i| ≤ 1`, and the functional equation `β ↦ β⁻¹` gives `|β_i| = 1`. A loss
  that does not grow with the order excludes every positive depth: this is the shape a sublinear
  loss law takes over `𝔽_q`, and Weil's theorem supplies the budget `2g` through the correspondence
  pairing on `C × C`.
* **The golden datum loses linearly** (`goldenRatio_pow_le_goldenDatum_trace`,
  `goldenDatum_no_fixed_budget`). Its power sums are `φ^j + φ^{−j} ≥ φ^j`: the loss grows with slope
  `log φ` and no budget exists, although all its Künneth counts are positive
  (`ArithmeticKunnethTheory.goldenDatum_kunneth_positive_not_pure`). Positivity of products of
  counts does not produce a fixed budget; a correspondence does.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open ArithmeticCastelnuovoSeveri

/-- **A fixed budget forces `|β_i| ≤ 1`.** -/
theorem norm_le_one_of_bounded_powerSum {ι : Type*} [Fintype ι] (D : CurveDatum ι)
    (hC : ∃ C, ∀ j, ‖D.powerSum j‖ ≤ C) : ∀ i, ‖D.β i‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := hC
  intro i
  exact RHTower.WeilKloosterman.norm_le_of_power_sums_bound (m0 := 0) Finset.univ D.β zero_le_one
    (fun m _ => by simpa [CurveDatum.powerSum] using hC m) i (Finset.mem_univ i)

/-- **A fixed budget forces purity.** With the functional equation, `|β_i| = 1` for every `i`. -/
theorem unitary_of_bounded_powerSum {ι : Type*} [Fintype ι] (D : CurveDatum ι)
    (hC : ∃ C, ∀ j, ‖D.powerSum j‖ ≤ C) : ∀ i, ‖D.β i‖ = 1 := by
  have hle := norm_le_one_of_bounded_powerSum D hC
  intro i
  have hfe := D.β_fePerm i
  have h1 := hle (D.fePerm i)
  have h2 := hle i
  have hprod : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by rw [← norm_mul, hfe, norm_one]
  have hi0 : 0 ≤ ‖D.β i‖ := norm_nonneg _
  have hf0 : 0 ≤ ‖D.β (D.fePerm i)‖ := norm_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi0]

open Real in
/-- **The golden datum loses linearly**: its order-`j` power sum is at least `φ^j`. -/
theorem goldenRatio_pow_le_goldenDatum_trace (j : ℕ) : goldenRatio ^ j ≤ goldenDatum.trace j := by
  rw [goldenDatum_trace]
  have : 0 ≤ (goldenRatio⁻¹) ^ j := pow_nonneg (inv_nonneg.mpr goldenRatio_pos.le) j
  linarith

/-- **The golden datum has no fixed budget.** -/
theorem goldenDatum_no_fixed_budget : ¬ ∃ C, ∀ j, ‖goldenDatum.powerSum j‖ ≤ C :=
  fun h => goldenDatum_not_unitary (unitary_of_bounded_powerSum goldenDatum h)

end GaloisForLFunctions.ArithmeticCorrelationGeometry
