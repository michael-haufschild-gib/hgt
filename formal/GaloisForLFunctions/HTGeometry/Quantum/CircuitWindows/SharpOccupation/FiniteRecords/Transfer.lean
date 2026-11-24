import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.LowerTransport
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteIntervals

/-! # Two-sided finite-window occupation at one circuit tolerance -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

private theorem measurable_visits {N : ℕ} (H : selfAdjoint (Register N)) (j : ℕ) (ε : ℝ) :
    MeasurableSet (visitSet H j ε) := by
  have he : visitSet H j ε={v | orbitCircuitDistance H j v ≤ ε} := Set.ext fun _ =>
    hasProjectiveCircuitApproximation_iff_infDist _ _ _
  rw [he]
  exact (isClosed_le (orbitCircuitDistance_lipschitz H j).continuous continuous_const).measurableSet

private theorem translate_visits {N : ℕ} (H : selfAdjoint (Register N)) (j : ℕ)
    {δ G e f : ℝ} (hfit : e+δ ≤ f)
    (hclock : ∀ u : ℝ, ∃ τ ∈ Icc u (u+G), τ ∈ visitSet H 0 δ) :
    ∀ u : ℝ, ∃ τ ∈ Icc u (u+G), ∀ t ∈ visitSet H j e, t+τ ∈ visitSet H j f := by
  intro u
  obtain ⟨τ,hτ,hzero⟩ := hclock u
  refine ⟨τ,hτ,fun t ht => ?_⟩
  have hprod := LocalPatches.approx_product (unitaryEvolution_mem_unitary H.2 τ) ht hzero
  have he := unitaryEvolution_sub_mul H (t+τ) τ
  rw [show t+τ-τ=t by ring] at he
  rw [he,Nat.add_zero] at hprod
  obtain ⟨z,hz,C,hC,hd⟩ := hprod
  exact ⟨z,hz,C,hC,hd.trans hfit⟩

/-- Long-run densities at surrounding tolerances bound the mass in every
finite window. Both errors are relative time corrections, even for rare visits. -/
theorem circuit_window_transfer {N : ℕ} (H : selfAdjoint (Register N)) (j : ℕ)
    {e ε f δ G p q : ℝ} (he : e+δ ≤ ε) (hf : ε+δ ≤ f) (hG : 0 < G)
    (hclock : ∀ u : ℝ, ∃ τ ∈ Icc u (u+G), τ ∈ visitSet H 0 δ)
    (hlo : ∀ᶠ R : ℝ in atTop, p ≤ visitFraction H j e 0 R)
    (hhi : ∀ᶠ R : ℝ in atTop, visitFraction H j f 0 R ≤ q)
    (a T : ℝ) (hT : G < T) :
    p*(T-G) ≤ volume.real (visitSet H j ε ∩ Icc a (a+T)) ∧
    volume.real (visitSet H j ε ∩ Icc a (a+T)) ≤ q*(T+G) := by
  have hl : ∀ᶠ R : ℝ in atTop, p*R ≤ volume.real (visitSet H j e ∩ Icc 0 R) := by
    filter_upwards [hlo,eventually_gt_atTop (0:ℝ)] with R hr hR
    rw [visitFraction,sub_zero] at hr
    exact (le_div_iff₀ hR).mp hr
  have hu : ∀ᶠ R : ℝ in atTop, volume.real (visitSet H j f ∩ Icc 0 R) ≤ q*R := by
    filter_upwards [hhi,eventually_gt_atTop (0:ℝ)] with R hr hR
    rw [visitFraction,sub_zero] at hr
    exact (div_le_iff₀ hR).mp hr
  exact ⟨lower_occupation_from_periods _ _ (measurable_visits H j ε) (translate_visits H j he hclock)
    hl a T hT,occupation_from_periods _ _ (measurable_visits H j ε) hG (translate_visits H j hf hclock)
    hu a T (hG.trans hT).le⟩

#print axioms circuit_window_transfer
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
