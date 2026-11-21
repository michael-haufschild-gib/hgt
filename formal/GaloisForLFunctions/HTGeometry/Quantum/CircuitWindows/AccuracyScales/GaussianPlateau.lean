import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.Counting
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactSynthesis.QuadraticBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Eigenphases

/-! # Time occupation relative to the same-error maximum across physical accuracies -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales
open DiagonalSynthesis
noncomputable section

/-- Successive accuracies differ by exactly the factor in the hard-lag bound. -/
def gateTolerance (q : ℕ) : ℕ → ℝ
  | 0 => 1/5
  | i+1 => gateTolerance q i/(2*(q:ℝ))

private theorem tolerance_bounds {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    gateTolerance q i ∈ Ioc (0:ℝ) (11/25) := by
  have h : (1:ℝ) ≤ q := by exact_mod_cast hq
  induction i with
  | zero => constructor <;> norm_num [gateTolerance]
  | succ i ih =>
    exact ⟨div_pos ih.1 (by linarith only [h]),
      (div_le_self ih.1.le (by linarith only [h])).trans ih.2⟩

private theorem max_le_uniform {N m p : ℕ} (H : selfAdjoint (Register N)) {η : ℝ}
    (hm : IsRecurrentOrbitCircuitMaximumAt H η m)
    (h : ∀ t, HasProjectiveCircuitApproximation N η p (unitaryEvolution H.val t)) : m ≤ p := by
  obtain ⟨_,w,_,hw,hvisit⟩ := hm.2
  obtain ⟨t,_,ht⟩ := hvisit 0
  obtain ⟨z,hz,C,hC,he⟩ := h t
  exact (ht t ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C he).trans hC

private theorem max_mono {N m p : ℕ} (H : selfAdjoint (Register N)) {ε η : ℝ}
    (h : ε ≤ η) (hm : IsRecurrentOrbitCircuitMaximumAt H η m)
    (hp : IsRecurrentOrbitCircuitMaximumAt H ε p) : m ≤ p := by
  apply max_le_uniform H hm
  intro t
  obtain ⟨z,hz,C,hC,he⟩ := hp.1 t
  exact ⟨z,hz,C,hC,he.trans h⟩

private theorem cubic_max {N m : ℕ} (hn : 256 ≤ N) (H : selfAdjoint (Register N))
    {ε : ℝ} (hε : 0 ≤ ε) (hm : IsRecurrentOrbitCircuitMaximumAt H ε m) :
    m ≤ (nearHilbertContinuousCircuitBudget N + 1)^3 := by
  have hcap := max_le_uniform H hm (fun t => (exact_evolution_gate_cap (by omega : 2 ≤ N) H t).approx hε)
  by_contra! h
  have hf := budget_of_quadratic_cap hn hcap (Or.inl h)
  change nearHilbertContinuousCircuitBudget N+1 ≤ nearHilbertContinuousCircuitBudget N/2 at hf
  omega

/-- Uniform length-T occupation bound with limiting affordable fraction 1/(q+1). -/
def affordableFractionBound {N : ℕ} (H : selfAdjoint (Register N)) (ε : ℝ) (s q : ℕ) (B : ℝ) : Prop :=
  ∀ a T : ℝ, 0 ≤ T → ((q:ℝ)+1)*volume.real
    ({t | HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+B

/-- At all but 2(N+1) steps, a budget below the same-error maximum divided
by 4q occupies at most 1/(q+1) of long-window time. At all but 2j steps
the analogous statement holds below the (1−1/j) power divided by 2q.
The exceptions are counted on every initial segment of the accuracy sequence. -/
theorem gaussian_same_error_plateau_across_accuracies :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ q : ℕ, 1 ≤ q → ∃ m : ℕ → ℕ, ∃ U : ℕ → ℝ,
        (∀ i, nearHilbertContinuousCircuitBudget N < m i ∧
          IsRecurrentOrbitCircuitMaximumAt H (gateTolerance q i) (m i) ∧ 0 ≤ U i) ∧
        (∀ L, ((Finset.range L).filter fun i => 2*m i < m (i+1)).card ≤ 2*(N+1)) ∧
        (∀ i, m (i+1) ≤ 2*m i → ∀ s, 4*s*q < m (i+1) →
          affordableFractionBound H (gateTolerance q (i+1)) s q (U i)) ∧
        ∀ j : ℕ, 2 ≤ j →
          (∀ L, ((Finset.range L).filter fun i => m i^j < m (i+1)^(j-1)).card ≤ 2*j) ∧
          ∀ i, m (i+1)^(j-1) ≤ m i^j → ∀ s, (2*s*q)^j < m (i+1)^(j-1) →
            affordableFractionBound H (gateTolerance q (i+1)) s q (U i) := by
  filter_upwards [gaussian_pauli_prefix_maximum_and_occupation_quantiles] with ω hω
  filter_upwards [hω,eventually_ge_atTop 256] with k hk hlarge
  intro N u H q hq
  have hN : 256 ≤ N := by dsimp [N]; omega
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  choose m hmin hm U hU hocc using fun i => hk (gateTolerance q i) (tolerance_bounds hq i)
  let B := nearHilbertContinuousCircuitBudget N+1
  have hsize : B ≤ 2^(N+1) := by
    have hp : nearHilbertContinuousCircuitBudget N ≤ 2^N := Nat.div_le_self _ _
    have hd : 0 < (2:ℕ)^N := by positivity
    dsimp only [B]; rw [pow_succ]; omega
  have hmono : Monotone m := monotone_nat_of_le_succ fun i =>
    max_mono H (div_le_self (tolerance_bounds hq i).1.le (by linarith only [hq'])) (hm i) (hm (i+1))
  have hcap (i) : m i ≤ B^3 := cubic_max hN H (tolerance_bounds hq i).1.le (hm i)
  have htime (i s) (hb : 2*s*q < m i) :
      affordableFractionBound H (gateTolerance q (i+1)) s q (U i) := by
    have herr : 2*(q:ℝ)*gateTolerance q (i+1) ≤ gateTolerance q i := by
      change 2*(q:ℝ)*(gateTolerance q i/(2*(q:ℝ))) ≤ _
      rw [mul_comm,div_mul_cancel₀ _ (by linarith only [hq'] : 2*(q:ℝ) ≠ 0)]
    exact hocc i q s (by omega) hb _ (tolerance_bounds hq (i+1)).1.le herr
  refine ⟨m,U,fun i => ⟨hmin i,hm i,hU i⟩,doubling_count (Nat.succ_pos _) hsize m hmono hmin hcap,?_,?_⟩
  · intro i hi s hs
    apply htime
    rw [show 4*s*q = 2*(2*s*q) by ring] at hs
    omega
  · intro j hj
    refine ⟨large_step_count B (Nat.succ_pos _) m hmono hmin hcap j (by omega),?_⟩
    intro i hi s hs
    apply htime
    by_contra! hh
    exact (hs.trans_le hi).not_ge (Nat.pow_le_pow_left hh j)

#print axioms gaussian_same_error_plateau_across_accuracies
end
end GaloisForLFunctions.HTGeometry.AccuracyScales
