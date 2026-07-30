import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Occupation vacuum--anomaly reciprocity

For a finite family of bosonic nomes, normalized vacuum amplitude and unnormalized
occupation mass are reciprocal records of one occupation line.
-/

namespace HTGeometry

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000 in

private theorem complex_tsum_pi_geometric_fin :
    ∀ (n : ℕ) (q : Fin n → ℂ), (∀ i, ‖q i‖ < 1) →
      Summable (fun ν : Fin n → ℕ => ‖∏ i, q i ^ ν i‖) ∧
      ∑' ν : Fin n → ℕ, ∏ i, q i ^ ν i =
        ∏ i, (1 - q i)⁻¹ := by
  intro n
  induction n with
  | zero =>
      intro q hq
      constructor
      · exact Summable.of_finite
      · simp
  | succ n ih =>
      intro q hq
      let r : Fin n → ℂ := fun i => q i.succ
      obtain ⟨hbNorm, hbValue⟩ := ih r (fun i => hq i.succ)
      let a : ℕ → ℂ := fun k => q 0 ^ k
      let b : (Fin n → ℕ) → ℂ := fun ν => ∏ i, r i ^ ν i
      have haNorm : Summable (fun k => ‖a k‖) := by
        simpa only [a, norm_pow] using
          summable_geometric_of_lt_one (norm_nonneg (q 0)) (hq 0)
      have hbNorm' : Summable (fun ν => ‖b ν‖) := by
        simpa only [b, r] using hbNorm
      have hbSum : HasSum b (∏ i, (1 - r i)⁻¹) := by
        have h := hbNorm'.of_norm.hasSum
        rw [show (∑' ν, b ν) = ∏ i, (1 - r i)⁻¹ by
          simpa only [b] using hbValue] at h
        exact h
      have habNorm :
          Summable (fun x : ℕ × (Fin n → ℕ) => a x.1 * b x.2) :=
        summable_mul_of_summable_norm haNorm hbNorm'
      have habNormReal :
          Summable (fun x : ℕ × (Fin n → ℕ) => ‖a x.1‖ * ‖b x.2‖) := by
        exact Summable.mul_of_nonneg haNorm hbNorm'
          (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have habSum :
          HasSum (fun x : ℕ × (Fin n → ℕ) => a x.1 * b x.2)
            ((1 - q 0)⁻¹ * ∏ i, (1 - r i)⁻¹) :=
        (hasSum_geometric_of_norm_lt_one (hq 0)).mul hbSum habNorm
      constructor
      · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).summable_iff]
        simpa [Function.comp_def, Fin.prod_univ_succ, a, b, r] using habNormReal
      · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).tsum_eq]
        simpa only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ,
          a, b, r] using habSum.tsum_eq

theorem complex_tsum_pi_geometric {ι : Type*} [Fintype ι]
    (q : ι → ℂ) (hq : ∀ i, ‖q i‖ < 1) :
    ∑' ν : ι → ℕ, ∏ i, q i ^ ν i =
      ∏ i, (1 - q i)⁻¹ := by
  let e := Fintype.equivFin ι
  let pe : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℕ) e
  calc
    (∑' ν : ι → ℕ, ∏ i, q i ^ ν i) =
        ∑' ν : Fin (Fintype.card ι) → ℕ,
          ∏ j, q (e.symm j) ^ ν j := by
            rw [← pe.tsum_eq]
            congr 1
            funext ν
            exact Fintype.prod_equiv e
              (fun i => q i ^ ν i)
              (fun j => q (e.symm j) ^ pe ν j) (by simp [pe])
    _ = ∏ j, (1 - q (e.symm j))⁻¹ :=
      (complex_tsum_pi_geometric_fin _ _ (fun j => hq (e.symm j))).2
    _ = ∏ i, (1 - q i)⁻¹ := by
      exact Fintype.prod_equiv e.symm
        (fun j => (1 - q (e.symm j))⁻¹)
        (fun i => (1 - q i)⁻¹) (by simp)

/-- Total unnormalized mass of a finite independent occupation family. -/
def finiteOccupationMass {ι : Type*} [Fintype ι] (q : ι → ℂ) : ℂ :=
  ∑' ν : ι → ℕ, ∏ i, q i ^ ν i

/-- Vacuum amplitude of the normalized occupation family. -/
def finiteOccupationVacuumAmplitude {ι : Type*} [Fintype ι]
    (q : ι → ℂ) : ℂ :=
  ∏ i, (1 - q i)

theorem finiteOccupationMass_eq_inv_vacuumAmplitude
    {ι : Type*} [Fintype ι] (q : ι → ℂ)
    (hq : ∀ i, ‖q i‖ < 1) :
    finiteOccupationMass q =
      (finiteOccupationVacuumAmplitude q)⁻¹ := by
  rw [finiteOccupationMass, finiteOccupationVacuumAmplitude,
    complex_tsum_pi_geometric q hq]
  exact Finset.prod_inv_distrib fun i => 1 - q i

theorem finiteOccupationVacuumAmplitude_ne_zero
    {ι : Type*} [Fintype ι] (q : ι → ℂ)
    (hq : ∀ i, ‖q i‖ < 1) :
    finiteOccupationVacuumAmplitude q ≠ 0 := by
  rw [finiteOccupationVacuumAmplitude]
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  exact sub_ne_zero.mpr fun h => by
    have hqi := hq i
    rw [← h] at hqi
    norm_num at hqi

/-- Vacuum amplitude times raw occupation mass is exactly one. -/
theorem finiteOccupation_vacuum_mul_mass
    {ι : Type*} [Fintype ι] (q : ι → ℂ)
    (hq : ∀ i, ‖q i‖ < 1) :
    finiteOccupationVacuumAmplitude q * finiteOccupationMass q = 1 := by
  rw [finiteOccupationMass_eq_inv_vacuumAmplitude q hq]
  exact mul_inv_cancel₀ (finiteOccupationVacuumAmplitude_ne_zero q hq)

end

end HTGeometry
