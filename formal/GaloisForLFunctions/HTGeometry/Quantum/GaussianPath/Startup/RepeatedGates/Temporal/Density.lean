import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.CircuitSupport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.ShortSignals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.SecondOrderBand

/-! # A positive density of excess gates in the second precision band -/
open Filter MeasureTheory Matrix Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
noncomputable section

/-- On either side of every half-tolerance scalar visit, precision between
cubic and quadratic forces at least one extra gate per two disjoint triples. -/
theorem gaussian_excess_gate_band : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
    let N := n+3
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (n+1)),isSelfAdjoint_pathHamiltonian _⟩
    ∃ A a : ℝ, 0<A ∧ 0<a ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ ε∈Icc (A*|t|^3) (a*t^2), ∀ v : ℝ,
      HasProjectiveCircuitApproximation N (ε/2) 0 (unitaryEvolution H.val v) →
      let U := unitaryEvolution H.val (v+t)
      (∀ s : ℕ, HasProjectiveCircuitApproximation N ε s U → 2*N+N/3 ≤ 2*(s+1)) ∧
        HasProjectiveCircuitApproximation N ε ((n+2)+(n+2)/2) U := by
  filter_upwards [gaussian_missing_pair_floor,gaussian_second_order_band] with ω hf hb n
  intro N H
  obtain ⟨c,hc,ht⟩ := hf n
  obtain ⟨A,b,hA,hb,hupper⟩ := hb n
  refine ⟨A,min b (c/2),hA,lt_min hb (half_pos hc),?_⟩
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds,hupper,self_mem_nhdsWithin] with t hf hu ht
  intro ε hε v hv U
  have clip (d) (hd : min b (c/2)≤d) : ε≤d*t^2 :=
    hε.2.trans (mul_le_mul_of_nonneg_right hd (sq_nonneg t))
  refine ⟨?_,(hu ε ⟨hε.1,clip b (min_le_left ..)⟩ v hv).2⟩
  intro s hfit
  by_contra! hcost
  have h := affordable_add_time H hfit (hv.neg_time H)
  simp only [Nat.add_zero,show v+t+-v=t by ring] at h
  obtain ⟨z,hz,C,hC,he⟩ := h
  have hbad : 2*(C.gateCount+1)<2*N+N/3 := by omega
  have hh := (hf C (missing_short_signal C hbad) z hz).trans he
  have hpos := mul_pos hc (sq_pos_of_ne_zero (show t≠0 from ht))
  linarith only [hh,clip (c/2) (min_le_right ..),hpos]

#print axioms gaussian_excess_gate_band
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
