import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.Reflection

/-! # The first cheap date reproduces the entire initial ascent on both sides -/

open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open PrescribedTimes
open private continuous_budget_distance from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Adding an approximated increment increases the best error by at most its fitting error. -/
theorem distance_add (H : selfAdjoint (Reg n)) (j : ℕ) (t : ℝ) {s : ℕ} {v e : ℝ}
    (hv : HasProjectiveCircuitApproximation n e s (unitaryEvolution H.val v)) :
    orbitCircuitDistance H (j+s) (t+v) ≤ orbitCircuitDistance H j t + e := by
  have ht := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val t)
    j (orbitCircuitDistance H j t)).mpr le_rfl
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp (affordable_add_time H ht hv)

/-- Both sides of a cheap date contain a copy of the whole initial ascent,
with the closing error and budget added only once. -/
private theorem initial_block (H : selfAdjoint (Reg n)) {P s : ℕ} {σ v : ℝ}
    (hinit : ∀ u ∈ Icc 0 σ, orbitCircuitDistance H P u ≤ 9/80)
    (hv : HasProjectiveCircuitApproximation n (1/10) s (unitaryEvolution H.val v))
    {t : ℝ} (ht : t ∈ Icc (v-σ) (v+σ)) : orbitCircuitDistance H (P+s) t ≤ 17/80 := by
  by_cases h : t ≤ v
  · have hu := hinit (v-t) ⟨sub_nonneg.mpr h,by linarith only [ht.1]⟩
    have hf := (reflected_distances H hv P (v-t)).1
    rw [sub_sub_cancel,Nat.add_comm s P] at hf
    linarith only [hu,hf]
  · have hu := hinit (t-v) ⟨sub_nonneg.mpr (le_of_not_ge h),by linarith only [ht.2]⟩
    have hf := distance_add H P (t-v) hv
    rw [sub_add_cancel] at hf
    linarith only [hu,hf]

private theorem close_initial_interval (f : ℝ → ℝ) (hf : Continuous f) {r σ : ℝ}
    (hs : (0:ℝ) ≠ σ) (h : Ico 0 σ ⊆ {t | f t ≤ r}) : Icc 0 σ ⊆ {t | f t ≤ r} := by
  have hc := (isClosed_le hf (continuous_const (y:=r))).closure_subset_iff.mpr h
  rwa [closure_Ico hs] at hc

/-- Up to and including its first crossing, the path lies in the closed
sublevel set. When the crossing set is empty the convention selects zero. -/
private theorem initial_sublevel (n P : ℕ) (x : PrefixIndex n → ℝ) :
    Icc 0 (crossingOrigin n P (9/80) x) ⊆ {t | pathGateDistance n P x t ≤ 9/80} := by
  let σ := crossingOrigin n P (9/80) x
  have prior : Ico 0 σ ⊆ {t | pathGateDistance n P x t ≤ 9/80} := by
    intro t ht
    change pathGateDistance n P x t ≤ 9/80
    apply le_of_not_gt
    intro h
    have ho : σ ≤ t := csInf_le (s := {u : ℝ | 0 ≤ u ∧ 9/80 ≤ pathGateDistance n P x u})
      ⟨0,fun _ hu => hu.1⟩ ⟨ht.1,h.le⟩
    exact ht.2.not_ge ho
  by_cases hs : (0:ℝ) = σ
  · intro t ht
    have hzero : t=0 := le_antisymm (ht.2.trans_eq hs.symm) ht.1
    rw [hzero]
    apply (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution (numberedGenerator n x) 0)
      P (9/80:ℝ)).mp
    refine ⟨1,norm_one,TwoQubitCircuit.one _,Nat.zero_le _,?_⟩
    norm_num [TwoQubitCircuit.one_eval,unitaryEvolution]
  · exact close_initial_interval (orbitCircuitDistance (prefixGenerator n x) P)
      (continuous_budget_distance (prefixGenerator n x) P) hs prior

/-- At the actual elapsed wait, a full interval of length twice the first
crossing time fits with the sum of the crossing and return budgets.
This holds for every prefix, including degenerate coefficient choices. -/
theorem reflected_initial_segment (n P s : ℕ) (x : PrefixIndex n → ℝ) :
    let σ := crossingOrigin n P (9/80) x
    let Δ := crossingWait n P s x
    ∀ t ∈ Icc Δ (Δ+2*σ), pathGateDistance n (P+s) x t ≤ 17/80 := by
  intro σ Δ t ht
  let H := prefixGenerator n x
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val (σ+Δ))
    s (1/10:ℝ)).mpr (first_wait_fit n P s x).2
  exact initial_block H (fun _ hu => initial_sublevel n P x hu) hfit
    ⟨by linarith only [ht.1],by linarith only [ht.2]⟩

#print axioms reflected_initial_segment
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
