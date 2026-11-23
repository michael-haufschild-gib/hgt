import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.OrbitMaximumAtError
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Eigenphases

/-! # Critical errors for the maximum gate count on a physical orbit -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
open DiagonalSynthesis (Register)
noncomputable section

/-- The least tolerance at which a given budget covers the whole orbit. -/
def criticalHeight {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) : ℝ :=
  sSup (range (orbitCircuitDistance H s))

/-- A recurrent maximum is attained as a lower bound on all fits at some physical date. -/
theorem required_at_some_date {N : ℕ} {H : selfAdjoint (Register N)} {e : ℝ} {m : ℕ}
    (hm : IsRecurrentOrbitCircuitMaximumAt H e m) :
    ∃ t : ℝ, ∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val t) → m ≤ j := by
  obtain ⟨_,w,_,hw,hr⟩ := hm.2
  obtain ⟨t,_,ht⟩ := hr 0
  refine ⟨t,?_⟩
  rintro j ⟨z,hz,C,hC,he⟩
  exact (ht t ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C he).trans hC

/-- A binary envelope for the exact diagonal-synthesis gate budget. -/
theorem exact_gate_cap_le {N : ℕ} (hn : 2 ≤ N) :
    (4*N+1)*(2*N+2)*(2^N)^2 ≤ 2^(6*N) := by
  have h (n : ℕ) : n+1 ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega
  calc
    _ ≤ (4*2^N)*(2*2^N)*(2^N)^2 := by
      have hN := h N
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
    _ = 2^(3+N+N+N*2) := by rw [pow_add,pow_add,pow_add,pow_mul]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The same envelope bounds the true orbit maximum at every nonnegative error. -/
theorem max_cap {N m : ℕ} (hn : 2 ≤ N) (H : selfAdjoint (Register N)) {e : ℝ}
    (he : 0 ≤ e) (hm : IsRecurrentOrbitCircuitMaximumAt H e m) : m ≤ 2^(6*N) := by
  obtain ⟨t,ht⟩ := required_at_some_date hm
  exact (ht _ ((DiagonalSynthesis.exact_evolution_gate_cap hn H t).approx he)).trans (exact_gate_cap_le hn)

/-- A drop in actual maximum between two tolerances locates a critical
height in their half-open interval. Its budget is below the exact synthesis cap. -/
theorem criticalHeight_of_maximum_drop {N m j : ℕ} (hn : 2 ≤ N) (H : selfAdjoint (Register N))
    {e δ : ℝ} (he : 0 ≤ e) (hf : IsRecurrentOrbitCircuitMaximumAt H e m)
    (hc : IsRecurrentOrbitCircuitMaximumAt H (e+δ) j) (hjm : j < m) :
    j < 2^(8*N) ∧ e < criticalHeight H j ∧ criticalHeight H j ≤ e+δ := by
  have hupper (t : ℝ) : orbitCircuitDistance H j t ≤ e+δ :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mp (hc.1 t)
  have hu : e+δ ∈ upperBounds (range (orbitCircuitDistance H j)) := by
    rintro _ ⟨t,rfl⟩
    exact hupper t
  obtain ⟨t,ht⟩ := required_at_some_date hf
  have hfar : e < orbitCircuitDistance H j t := lt_of_not_ge fun h =>
    hjm.not_ge (ht _ ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h))
  exact ⟨(hjm.trans_le (max_cap hn H he hf)).trans_le (Nat.pow_le_pow_right (by decide) (by omega)),
    hfar.trans_le (le_csSup ⟨_,hu⟩ (mem_range_self t)),
    csSup_le (range_nonempty _) hu⟩

/-- A compiled reverse increment transports the coarser maximum's gate
requirement to an entire interval at the finer error. -/
theorem recurrent_floor_of_compiler {N m L : ℕ} (H : selfAdjoint (Register N)) {e δ T : ℝ}
    (hm : IsRecurrentOrbitCircuitMaximumAt H (e+δ) m)
    (hs : ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation N δ L (unitaryEvolution H.val t)) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ u ∈ Icc a (a+G),
      ∀ t : ℝ, |t| ≤ T → ∀ j, HasProjectiveCircuitApproximation N e j
        (unitaryEvolution H.val (u+t)) → m ≤ j+L := by
  obtain ⟨G,w,hG,hw,hr⟩ := hm.2
  refine ⟨G,hG,?_⟩
  intro a
  obtain ⟨u,hu,hf⟩ := hr a
  refine ⟨u,hu,?_⟩
  intro t ht j hfit
  have hh := affordable_add_time H hfit (hs (-t) (by rwa [abs_neg]))
  rw [show u+t+ -t=u by ring] at hh
  obtain ⟨z,hz,C,hC,he⟩ := hh
  exact (hf u ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C he).trans hC

#print axioms criticalHeight_of_maximum_drop
#print axioms recurrent_floor_of_compiler
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
