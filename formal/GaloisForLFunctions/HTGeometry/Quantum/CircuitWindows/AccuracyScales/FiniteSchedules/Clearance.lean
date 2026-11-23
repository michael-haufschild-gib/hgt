import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.FrozenClearance

/-! # Uniform accuracy margins on exponentially many physical dates -/
open Set Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.FiniteSchedules
open MaximumIntervals
noncomputable section

/-- Encode a date and a gate budget in one index. The extra zero height
ensures the improved tolerance is nonnegative. -/
def scheduleHeight (ω : PathPauliDisorder) (τ : ℕ → ℕ → ℝ) (k j : ℕ) : ℝ :=
  let B := 2^(6*(k+3))
  if j=0 then 0 else orbitCircuitDistance (chainGenerator ω k) ((j-1)%B) (τ k ((j-1)/B))

/-- For any frozen path and schedule, every budget at every scheduled
date can be repaired across an exponential error margin, off a single
zero-dimensional set of tolerances. There are 2^N dates at each size. -/
theorem schedule_clearance (ω : PathPauliDisorder) (τ : ℕ → ℕ → ℝ) :
    ∀ e > (0:ℝ), e∉exceptionalTolerances (scheduleHeight ω τ) → ∃ c : ℕ, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let δ := 1/(2:ℝ)^(c*N)
      let H := chainGenerator ω k
      ∀ i < 2^N, ∀ j : ℕ,
        HasProjectiveCircuitApproximation N (e+δ) j (unitaryEvolution H.val (τ k i)) →
        HasProjectiveCircuitApproximation N (e-δ) j (unitaryEvolution H.val (τ k i)) := by
  let g := scheduleHeight ω τ
  intro e he hreg
  obtain ⟨c,hc⟩ := not_forall.mp hreg
  refine ⟨c,?_⟩
  filter_upwards [not_frequently.mp hc] with k hfar
  intro N δ H i hi j hfit
  let B := 2^(6*N)
  let r := 1/(2:ℝ)^(c*k)
  have hδr : δ ≤ r := one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.mul_le_mul_left c (by dsimp [N]; omega)))
  have heδ : δ ≤ e := by
    by_contra! hlt
    apply hfar ⟨0,by positivity,?_⟩
    simpa only [g,scheduleHeight,if_pos rfl,sub_zero,abs_of_pos he] using hlt.le.trans hδr
  by_cases hj : j < B
  · let idx := B*i+j+1
    have hB : 0 < B := by dsimp only [B]; positivity
    have hidx : idx < 2^(8*N) := by
      have h₁ : B*i+j < B*(i+1) := by rw [Nat.mul_succ]; omega
      have h₂ := h₁.trans_le (Nat.mul_le_mul_left B (Nat.succ_le_of_lt hi))
      have h₃ : B*2^N < 2^(8*N) := by
        dsimp only [B]
        rw [←pow_add]
        exact Nat.pow_lt_pow_right (by decide) (by dsimp only [N]; omega)
      dsimp only [idx]; omega
    have hmem : g k idx=orbitCircuitDistance H j (τ k i) := by
      simp only [g,scheduleHeight,idx,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,
        Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hj,B,N,H]
      rw [Nat.mul_add_div (by positivity),Nat.div_eq_of_lt hj,add_zero]
    have hu := (hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
    by_contra! h
    apply hfar ⟨idx,hidx,?_⟩
    rw [hmem]
    exact (abs_le.mpr ⟨by linarith only [hu],by linarith only [h]⟩).trans hδr
  · have hN : 2 ≤ N := by dsimp only [N]; omega
    obtain ⟨z,hz,C,hC,herror⟩ := (DiagonalSynthesis.exact_evolution_gate_cap hN H (τ k i)).approx
      (sub_nonneg.mpr heδ)
    exact ⟨z,hz,C,hC.trans ((exact_gate_cap_le hN).trans (Nat.le_of_not_gt hj)),herror⟩

#print axioms schedule_clearance
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.FiniteSchedules
