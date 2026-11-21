import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.TimeTranslation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.FullBudgetWindows

/-! # Finite observation intervals at a Hilbert-scale gate threshold -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- A spectral return in every interval of length G transfers the entropy
bound at one tenth extra error to every finite interval, with additive
length correction G. The clock works for all gate budgets and errors. -/
theorem gaussian_period_corrected_occupation :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ q : ℕ, 0 < q →
      ∀ x ∈ Ioo (0:ℝ) (1/2), ∀ ε b : ℝ, ε+1/10 ≤ zeroGateArcTolerance x →
      0 < b → Real.log x+32*Real.log 2/q < Real.log b → ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let G := (2:ℝ)^(D^c)
      ∀ j ≤ D/(q*(N+1)), ∀ a T : ℝ, 0 ≤ T →
        volume.real (visitSet H j ε ∩ Icc a (a+T)) ≤ b^D*(T+G) := by
  obtain ⟨c,hclock⟩ := ReturnExcursions.gaussian_full_budget_robust_windows
  refine ⟨c,?_⟩
  filter_upwards [gaussian_hilbert_budget_occupation,hclock] with ω hw hc
  intro q hq x hx ε b htol hb hl
  filter_upwards [hw q hq x hx b hb hl,hc] with k hocc hrec
  intro N D H G j hj a T hT
  have hclosed : IsClosed (visitSet H j ε) := by
    have he : visitSet H j ε = {v | orbitCircuitDistance H j v ≤ ε} := Set.ext fun _ =>
      hasProjectiveCircuitApproximation_iff_infDist _ _ _
    rw [he]
    exact isClosed_le (orbitCircuitDistance_lipschitz H j).continuous continuous_const
  apply occupation_from_periods _ (visitSet H j (zeroGateArcTolerance x)) hclosed.measurableSet
    (by dsimp [G]; positivity) _ _ a T hT
  · intro u
    obtain ⟨τ,hτ,hz⟩ := hrec.1 u
    refine ⟨τ,hτ,?_⟩
    intro t ht
    have hprod := LocalPatches.approx_product (unitaryEvolution_mem_unitary H.2 τ) ht hz
    have he := unitaryEvolution_sub_mul H (t+τ) τ
    rw [show t+τ-τ = t by ring] at he
    rw [he,Nat.add_zero] at hprod
    obtain ⟨z,hz,C,hC,hd⟩ := hprod
    exact ⟨z,hz,C,hC,hd.trans htol⟩
  · filter_upwards [hocc 0,eventually_gt_atTop (0:ℝ)] with R hr hR
    have hh := hr j hj
    rw [visitFraction,sub_zero] at hh
    exact ((div_lt_iff₀ hR).mp hh).le

/-- The same clock and entropy correction work for every gate budget up
to a sixteenth of D/(N+1) and every interval, including the first. -/
theorem gaussian_finite_interval_occupation :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let G := (2:ℝ)^(D^c)
      ∀ j ≤ D/(16*(N+1)), ∀ a T : ℝ, 0 ≤ T →
        volume.real (visitSet H j (1/8) ∩ Icc a (a+T)) ≤ (3/8:ℝ)^D*(T+G) := by
  obtain ⟨c,hc⟩ := gaussian_period_corrected_occupation
  let x : ℝ := 1/12
  have hx : x ∈ Ioo (0:ℝ) (1/2) := by norm_num [x]
  have htol : 1/8+1/10 ≤ zeroGateArcTolerance x :=
    (by norm_num [x] : 1/8+1/10 ≤ 3*x).trans (three_mul_le_arcTolerance hx.1.le (by norm_num [x]))
  have hl : Real.log x+32*Real.log 2/(16:ℕ) < Real.log (3/8) := by
    have hlog := Real.log_lt_log (by norm_num [x] : 0 < x*(2:ℝ)^2)
      (by norm_num [x] : x*(2:ℝ)^2 < 3/8)
    rw [Real.log_mul (by norm_num [x]) (by norm_num),Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at *
    linarith only [hlog]
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hw
  exact hw 16 (by decide) x hx (1/8) (3/8) htol (by norm_num) hl

#print axioms gaussian_period_corrected_occupation
#print axioms gaussian_finite_interval_occupation
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
