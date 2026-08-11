import GaloisForLFunctions.RHTower.RouteEUniformFibreShuffle
import GaloisForLFunctions.RHTower.RouteEGibbsProductHistoryStability

/-!
# Route E uniform-cell to physical-cell endpoint

This is the exact finite endpoint behind the replica-orbit lane.  A physical conditional mean is
compared cellwise with a declared uniform-orbit mean.  Its weighted uniform-cell energy plus the
sharp comparison defect controls the original signed mean.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

namespace RouteEPhysicalFibreData

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Λ]

/-- Energy of a declared reference mean on each physical fibre, weighted by actual fibre mass. -/
def referenceFibreEnergy (D : RouteEPhysicalFibreData Ω Λ) (theta : Λ → ℝ) : ℝ :=
  ∑ l, D.fibreMass l * theta l ^ 2

theorem referenceFibreEnergy_nonneg
    (D : RouteEPhysicalFibreData Ω Λ) (theta : Λ → ℝ) :
    0 ≤ D.referenceFibreEnergy theta :=
  Finset.sum_nonneg fun l _hl =>
    mul_nonneg (D.fibreMass_pos l).le (sq_nonneg _)

private theorem projectedEnergy_eq_sum_fibreMass_mul_conditionalMean_sq
    (D : RouteEPhysicalFibreData Ω Λ) :
    D.projectedEnergy = ∑ l, D.fibreMass l * D.conditionalMean l ^ 2 := by
  rw [D.projectedEnergy_eq_fibreQuotient]
  apply Finset.sum_congr rfl
  intro l _hl
  unfold conditionalMean
  field_simp [D.fibreMass_ne_zero l]

/-- Cellwise comparison with a reference mean controls physical projected energy. -/
theorem projectedEnergy_le_two_reference_add_two_defect_sq
    (D : RouteEPhysicalFibreData Ω Λ) (theta : Λ → ℝ) (delta : ℝ)
    (_hdelta : 0 ≤ delta)
    (hcompare : ∀ l, |D.conditionalMean l - theta l| ≤ delta) :
    D.projectedEnergy ≤ 2 * D.referenceFibreEnergy theta + 2 * delta ^ 2 := by
  rw [D.projectedEnergy_eq_sum_fibreMass_mul_conditionalMean_sq]
  calc
    (∑ l, D.fibreMass l * D.conditionalMean l ^ 2) ≤
        ∑ l, D.fibreMass l * (2 * theta l ^ 2 + 2 * delta ^ 2) := by
      apply Finset.sum_le_sum
      intro l _hl
      have hlower := (abs_le.mp (hcompare l)).1
      have hupper := (abs_le.mp (hcompare l)).2
      apply mul_le_mul_of_nonneg_left _ (D.fibreMass_pos l).le
      nlinarith [sq_nonneg (D.conditionalMean l - 2 * theta l),
        sq_nonneg (D.conditionalMean l + 2 * theta l)]
    _ = 2 * D.referenceFibreEnergy theta + 2 * delta ^ 2 := by
      unfold referenceFibreEnergy
      calc
        (∑ l, D.fibreMass l * (2 * theta l ^ 2 + 2 * delta ^ 2)) =
            ∑ l, (2 * (D.fibreMass l * theta l ^ 2) +
              (2 * delta ^ 2) * D.fibreMass l) := by
          apply Finset.sum_congr rfl
          intro l _hl
          ring
        _ = 2 * (∑ l, D.fibreMass l * theta l ^ 2) +
            (2 * delta ^ 2) * ∑ l, D.fibreMass l := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = _ := by rw [D.sum_fibreMass]; ring

/-- **Replica-orbit comparison endpoint.** -/
theorem abs_mean_le_sqrt_two_reference_add_two_defect_sq
    (D : RouteEPhysicalFibreData Ω Λ) (theta : Λ → ℝ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hcompare : ∀ l, |D.conditionalMean l - theta l| ≤ delta) :
    |∑ ω, D.mass ω * D.observable ω| ≤
      Real.sqrt (2 * D.referenceFibreEnergy theta + 2 * delta ^ 2) := by
  have hbase := D.abs_mean_le_sqrt_projectedEnergy
  have henergy := D.projectedEnergy_le_two_reference_add_two_defect_sq
    theta delta hdelta hcompare
  have hsqrt := Real.sqrt_le_sqrt henergy
  exact hbase.trans hsqrt

end RouteEPhysicalFibreData

end

end RHTower
