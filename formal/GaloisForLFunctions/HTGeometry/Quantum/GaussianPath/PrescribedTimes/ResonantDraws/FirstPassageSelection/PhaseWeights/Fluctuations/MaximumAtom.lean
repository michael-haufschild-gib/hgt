import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.OrbitMaximum.Statistic
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.SelectedFraction

/-! # Frequency of the true maximum and its separation from the Haar mean -/
open Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open JointSpeeds SharpOccupation PhaseFluctuations
open private dimension_tails from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.DimensionBounds.PhysicalTails
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- Excluding the next smaller budget isolates the top gate count. -/
def maximumAtom (k : ℕ) (ε : ℝ) (x : PrefixIndex (k+1)→ℝ) : ℝ :=
  let m := prefixMaximum (k+1) ε x
  if m=0 then 1 else 1-prefixFraction k (m-1) ε x

theorem measurable_maximumAtom (k : ℕ) {ε : ℝ} (hε : 0 < ε) : Measurable (maximumAtom k ε) := by
  let m := prefixMaximum (k+1) ε
  have hm : Measurable m := measurable_prefixMaximum _ hε
  let f (p : (PrefixIndex (k+1)→ℝ)×ℕ) : ℝ :=
    if p.2=0 then 1 else 1-prefixFraction k (p.2-1) ε p.1
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro j
    by_cases hj : j=0
    · simp only [f, hj, if_true]
      exact measurable_const
    · simp only [f, if_neg hj]
      exact measurable_const.sub (measurable_prefixFraction k (j-1) ε)
  change Measurable (f ∘ fun x => (x,m x))
  exact hf.comp (measurable_id.prodMk hm)

/-- A large separation between the same-error maximum and the mean
forces the maximum phase fraction to be small, although it is positive
for every full-rank prefix. -/
theorem maximum_atom_bounds (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let K := k+3
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let m := prefixMaximum (k+1) ε x
      let M := prefixMean k ε x
      let a := maximumAtom k ε x
      0 < a ∧ a ≤ exp (-(max 0 ((m:ℝ)-M))^2/(2*(((2^K-1:ℕ):ℝ)*(((35*2^K:ℕ):ℝ)/2)^2))) := by
  filter_upwards [prefixMean_eq k hε.le,ae_all_iff.mpr (fun j => prefixFraction_eq k j ε),
    ae_all_iff.mpr (fun j => unit_fraction_iff_orbitBudget k j ε)] with ω hM hF hO
  intro K x m M a
  have hpos (s : ℕ) : 0 ≤ prefixFraction k s ε x ∧ prefixFraction k s ε x ≤ 1 := by
    rw [hF s]
    exact ⟨measureReal_nonneg,measureReal_le_one⟩
  have hM₀ : 0 ≤ M := Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (hpos j).2)
  by_cases hm : m=0
  · have ha : a=1 := if_pos hm
    rw [ha,hm,Nat.cast_zero,zero_sub,max_eq_left (neg_nonpos.mpr hM₀)]
    norm_num
  let j := m-1
  have hj : m=j+1 := by dsimp only [j]; omega
  have hf : prefixFraction k j ε x < 1 := by
    apply lt_of_le_of_ne (hpos j).2
    intro he
    have ho := (hO j).mp ((hF j).symm.trans he)
    have hn : x∈(prefixMaximum (k+1) ε) ⁻¹' Iic j := (prefixMaximum_sublevel (k+1) j hε).symm ▸ ho
    exact (show ¬m ≤ j by omega) hn
  have ha : a=1-prefixFraction k j ε x := if_neg hm
  refine ⟨by rw [ha]; exact sub_pos.mpr hf,?_⟩
  by_cases h : M ≤ (m:ℝ)
  · rw [max_eq_right (sub_nonneg.mpr h),ha]
    let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
    let e := (qubitConfigFin K).trans (prefixPhaseEnergyEquiv k)
    have ht := (dimension_tails (by dsimp only [K]; omega : 2 ≤ K) e
      (hermitianEigenbasisUnitary H.2.isHermitian) hε.le (sub_nonneg.mpr h) j).2
    rw [hF j]
    apply ht
    change meanCost _ _ _ _+((m:ℝ)-M) ≤ (j:ℝ)+1
    rw [←hM]
    have hmj : (m:ℝ)=(j:ℝ)+1 := by exact_mod_cast hj
    linarith only [hmj]
  · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),ha]
    simpa only [zero_pow (by decide : (2:ℕ)≠0),neg_zero,zero_div,exp_zero] using sub_le_self 1 (hpos j).1

#print axioms maximum_atom_bounds
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
