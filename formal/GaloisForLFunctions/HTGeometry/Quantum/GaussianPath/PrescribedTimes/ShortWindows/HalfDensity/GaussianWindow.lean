import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.AllDelays
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.HalfDensity

/-! # Half-density budget windows after the actual first robust crossing -/
open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
open RepeatedGates.PhysicalBlocks
noncomputable section

/-- Every fixed-width observation at any prescribed nonnegative delay
from the first crossing excludes half the bond count plus o(N) gates
with probability tending to one. -/
theorem gaussian_half_density_delayed_window (s : ℕ → ℕ) (W : ℝ) (hW : 0≤W)
    (hs : ∀ c : ℝ, 0<c → ∀ᶠ k : ℕ in atTop, 2*(s k:ℝ)≤(1+c)*(k+2:ℕ)) (d : ℕ → ℝ) :
    Tendsto (fun k => pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
      hitWindow (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (s k) (max (d k) 0) W)) atTop (𝓝 0) := by
  let L (k : ℕ) := max (max (d k) 0) (((k+3:ℕ):ℝ)^2)
  let E (k : ℕ) := hitWindow (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (s k) (L k) W
  let g := 8*(W+1)
  have hg : 0<g := by dsimp only [g]; positivity
  have price (m : ℕ) : ∀ᶠ k : ℕ in atTop, 16*((m:ℝ)*g) ≤ ((k+3:ℕ):ℝ) := by
    obtain ⟨K,hK⟩ := exists_nat_gt (16*((m:ℝ)*g))
    filter_upwards [eventually_ge_atTop K] with k hk
    exact hK.le.trans (Nat.cast_le.mpr (by omega))
  apply remove_initial_delay_cutoff s (fun _ => W) d
  · filter_upwards [hs 1 zero_lt_one,eventually_ge_atTop 64] with k hk hlarge
    have hsc : s k ≤ k+2 := by exact_mod_cast (show (s k:ℝ) ≤ (k+2:ℕ) by linarith only [hk])
    have hpow := Nat.mul_le_mul_right 2 (ReturnExcursions.dimension_dominates_speed (n:=k+2) (by omega))
    rw [←Nat.pow_succ] at hpow
    change 64*(k+3)^2*2 ≤ 2^(k+3) at hpow
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 2 hsc)).trans
      ((by nlinarith only : (k+2)*2*(64*(k+3+1)) ≤ 64*(k+3)^2*2).trans hpow)
  · obtain ⟨K,hK⟩ := exists_nat_gt W
    filter_upwards [eventually_ge_atTop K] with k hk
    exact hK.le.trans (Nat.cast_le.mpr (by omega))
  apply prefix_probability_of_isolation E (fun _ => measurable_hitWindow ..)
    (fun m k => factor (m:=m) g (L k))
  · intro m
    filter_upwards [price m] with k hk
    exact (grid_price (k:=k) hg.le (le_max_right ..) hk).2
  intro m
  obtain ⟨c,hc,hgap⟩ := gaussian_excluded_compact_lags (a:=1) (T:=(m:ℝ)*g+2*W) zero_lt_one
  filter_upwards [hgap] with ω hw
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,hs c hc,price m] with k hn hcost hp
  intro hx
  have hL : 0<L k := (sq_pos_of_pos (by positivity : 0<((k+3:ℕ):ℝ))).trans_le (le_max_right ..)
  apply isolated_of_gap hg.le hL (grid_price (k:=k) hg.le (le_max_right ..) hp).1 hW _ hx
  intro t v ht hv hlo hhi
  let H : selfAdjoint (Matrix (Fin (k+3)→Bool) (Fin (k+3)→Bool) ℂ) :=
    ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  have fit (x : ℝ) (hx : pathGateDistance (k+1) (s k) (prefixPoint k ω) x ≤ 1/10) :
      HasProjectiveCircuitApproximation (k+3) (1/10) (s k) (unitaryEvolution H.val x) := by
    apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr
    rwa [pathGateDistance,show numberedGenerator (k+1) (prefixPoint k ω)=H.val from numberedGenerator_shell _] at hx
  have hl : 1≤|v-t| := by dsimp only [g] at hlo; linarith only [hlo,hW]
  have h := hn t v ⟨hl,hhi⟩ (s k) (s k) (1/10) (1/10) (by norm_num) (fit t ht) (fit v hv)
  rw [show s k+s k=2*s k by omega,Nat.cast_mul,Nat.cast_ofNat] at h
  exact h.not_ge hcost

#print axioms gaussian_half_density_delayed_window
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
