import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.LastPair
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PauliWitnesses
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.SignalCurve
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.Threshold

/-! # Sharp quadratic error at one gate per physical bond -/
open Filter MeasureTheory Matrix Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section
open UntouchedSites

private theorem spin_support {N : ℕ} (i : Fin N) : IsSiteSupported {i} (spin i 2) := by
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro j hj
  simp only [Finset.mem_singleton] at hj
  simp [siteLabel,hj]

private theorem all_short_jets :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n, ∀ i j : Fin (n+2), i ≠ j →
      i.val ≤ j.val+2 → j.val ≤ i.val+2 →
      signal₂ (spin i 2) (spin j 2) (pathHamiltonian (pathPauliDisorderShell ω n)) ≠ 0 := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases h : i ≠ j ∧ i.val ≤ j.val+2 ∧ j.val ≤ i.val+2
  · filter_upwards [gaussian_short_signal₂ h.1 h.2.1 h.2.2] with ω hw
    exact fun _ _ _ => hw
  · exact Eventually.of_forall fun _ hij hl hr => (h ⟨hij,hl,hr⟩).elim

private def nearby {N : ℕ} (p : Fin N×Fin N) :=
  p.1 ≠ p.2 ∧ p.1.val ≤ p.2.val+2 ∧ p.2.val ≤ p.1.val+2

/-- Take one positive coefficient for the finitely many short signals. -/
private theorem uniform_signals {n : ℕ} (H : Register (n+3))
    (hj : ∀ i j : Fin (n+3), i ≠ j → i.val ≤ j.val+2 → j.val ≤ i.val+2 →
      signal₂ (spin i 2) (spin j 2) H ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ t : ℝ in 𝓝 0, ∀ p : Fin (n+3)×Fin (n+3), nearby p →
      m*t^2 ≤ ‖signal H (spin p.1 2) (spin p.2 2) t‖ := by
  classical
  have each (p : Fin (n+3)×Fin (n+3)) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in 𝓝 0, nearby p →
      c*t^2 ≤ ‖signal H (spin p.1 2) (spin p.2 2) t‖ := by
    by_cases hp : nearby p
    · obtain ⟨c,hc,ht⟩ := quadratic_signal_floor H (spin p.1 2) (spin p.2 2) (spin_comm hp.1 2 2)
        (hj p.1 p.2 hp.1 hp.2.1 hp.2.2)
      exact ⟨c,hc,ht.mono fun _ h _ => h⟩
    · exact ⟨1,zero_lt_one,Eventually.of_forall fun _ he => (hp he).elim⟩
  choose c hc ht using each
  let m := Finset.univ.inf' Finset.univ_nonempty c
  refine ⟨m,(Finset.lt_inf'_iff _).mpr (fun p _ => hc p),?_⟩
  filter_upwards [eventually_all.mpr ht] with t h
  intro p hp
  exact (mul_le_mul_of_nonneg_right (Finset.inf'_le c (Finset.mem_univ p)) (sq_nonneg t)).trans (h p hp)

/-- A missed direction converts the uniform signal coefficient to a
lower bound for every circuit, including its optimized global phase. -/
private theorem error_of_short_signals {n : ℕ} (H : selfAdjoint (Register (n+3))) (m t : ℝ)
    (hs : ∀ p : Fin (n+3)×Fin (n+3), nearby p →
      m*t^2 ≤ ‖signal H.val (spin p.1 2) (spin p.2 2) t‖)
    (C : TwoQubitCircuit (n+3)) (hC : C.gateCount ≤ n+2) (z : ℂ) (hz : ‖z‖=1) :
    m/4*t^2 ≤ ‖unitaryEvolution H.val t-z • C.eval.val‖ := by
  obtain ⟨i,j,hij,hl,hr,hmiss⟩ := short_missing_ordered_pair C hC
  let U : Matrix.unitaryGroup (Fin (n+3)→Bool) ℂ :=
    ⟨unitaryEvolution H.val t,unitaryEvolution_mem_unitary H.property t⟩
  have hn (k : Fin (n+3)) : ‖spin k 2‖ ≤ 1 := (norm_finitePauliMatrix (siteLabel k 2)).le
  have he := SpanningDensity.missing_signal_bound C U z hz (spin i 2) (spin j 2) (hn i) (hn j)
    (hmiss (spin i 2) (spin j 2) (spin_support i) (spin_support j))
  have h := hs (i,j) ⟨hij,hl,hr⟩
  change m*t^2 ≤ ‖signal H.val (spin i 2) (spin j 2) t‖ at h
  rw [signal,EigenlineSignals.adjoint_evolution H,bracket] at h
  have hfinal : m*t^2 ≤ 4*‖unitaryEvolution H.val t-z • C.eval.val‖ := h.trans he
  linarith only [hfinal]

/-- For almost every Gaussian chain, on each fixed N≥3 prefix the
best error of N−1 gates has exact order t² on both sides of zero. -/
theorem gaussian_quadratic_bond_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
      let N := n+3
      let H := pathHamiltonian (pathPauliDisorderShell ω (n+1))
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        (∀ t : ℝ, HasProjectiveCircuitApproximation N (b*t^2) (n+2) (unitaryEvolution H t)) ∧
        ∀ᶠ t : ℝ in 𝓝 0, ∀ C : TwoQubitCircuit N, C.gateCount ≤ n+2 →
          ∀ z : ℂ, ‖z‖=1 → a*t^2 ≤ ‖unitaryEvolution H t-z • C.eval.val‖ := by
  filter_upwards [all_short_jets,ConnectedGates.gaussian_minimum_bond_count] with ω hj hfit n
  intro N H
  let K : selfAdjoint (Register (n+3)) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  obtain ⟨b,_,hb,_,hu,_⟩ := hfit (n+1)
  obtain ⟨a,ha,ht⟩ := uniform_signals H (hj (n+1))
  refine ⟨a/4,b,by positivity,hb,hu,?_⟩
  exact ht.mono (fun t hs => error_of_short_signals K a t hs)

#print axioms gaussian_quadratic_bond_floor
end
end GaloisForLFunctions.HTGeometry.RepeatedGates
