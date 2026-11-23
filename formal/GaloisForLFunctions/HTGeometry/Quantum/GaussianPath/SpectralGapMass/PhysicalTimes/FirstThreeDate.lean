import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.ThreeGateUpper
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.GaussianFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.BasisCost

/-! # The first return to three gates after a freely chosen basis change -/
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- First physical date after A/(n+1) when some basis allows three gates. -/
def firstThreeDate (A : ℝ) (ω : PathPauliDisorder) (n : ℕ) : ℝ :=
  SpectralApproximation.firstVisit ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
    (A/(n+1:ℕ)) 3 (1/10)

private theorem least_three (A : ℝ) (ω : PathPauliDisorder) (n : ℕ) :
    IsLeast (Ici (A/(n+1:ℕ)) ∩ SpectralApproximation.affordableDates
      ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩ 3 (1/10))
      (firstThreeDate A ω n) :=
  SpectralApproximation.firstVisit_isLeast _ _ _ (by norm_num)

/-- The first three-gate date tends to zero, while its square times
the number of spins stays bounded away from zero. -/
theorem gaussian_first_three_date :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      Tendsto (firstThreeDate A ω) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop, 1 ≤ B*(n+2:ℕ)*(firstThreeDate A ω n)^2) ∧
      Tendsto (fun n => firstThreeDate A ω n*(n+1:ℕ)) atTop atTop := by
  obtain ⟨A,b,hA,hb,hfloor⟩ := SpectatorCost.gaussian_spectator_variance_floor
  let B := 64*b
  have hB : 0 < B := mul_pos (by norm_num) hb
  refine ⟨A,B,hA,hB,?_⟩
  filter_upwards [gaussian_three_gate_conjugate_upper,hfloor] with ω hup hf
  let u := firstThreeDate A ω
  have hpos (n : ℕ) : 0 < u n := (div_pos hA (by positivity)).trans_le (least_three A ω n).1.1
  have hlim : Tendsto u atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let a := δ/2
    have ha := half_pos hδ
    obtain ⟨k,hk⟩ := exists_nat_gt (A/a)
    filter_upwards [hup a a ha,eventually_ge_atTop k] with n hn hnk
    have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hkn : (k:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (show k≤n+1 by omega)
    have hstart : A/(n+1:ℕ) ≤ a := (div_le_iff₀ hN).mpr (by
      have hh := (div_le_iff₀ ha).mp (hk.le.trans hkn)
      rwa [mul_comm a])
    have hdate := (least_three A ω n).2 (show a∈_ from ⟨hstart,hn a ⟨le_rfl,le_rfl⟩⟩)
    rw [Real.dist_eq,sub_zero,abs_of_pos (hpos n)]
    exact hdate.trans_lt (half_lt_self hδ)
  have hmass : ∀ᶠ n : ℕ in atTop, 1 ≤ B*(n+2:ℕ)*(u n)^2 := by
    filter_upwards [hf 1,hlim.eventually_lt_const zero_lt_one] with n hn hsmall
    obtain ⟨hs,W,hw⟩ := (least_three A ω n).1
    have hlate : A ≤ |u n| *(n+1:ℕ) := by
      rw [abs_of_pos (hpos n)]
      exact (div_le_iff₀ (by positivity : 0 < ((n+1:ℕ):ℝ))).mp hs
    have hh := hn (u n) hlate ((abs_of_pos (hpos n)).le.trans hsmall.le) W 3 hw
    exact hh.trans_eq (by dsimp only [B]; ring)
  refine ⟨hlim,hmass,tendsto_atTop.mpr ?_⟩
  intro y
  let K := max y 1
  have hK : 0 < K := zero_lt_one.trans_le (le_max_right ..)
  have hδ : 0 < 1/(2*B*K) := by positivity
  filter_upwards [hmass,hlim.eventually_lt_const hδ] with n hn hsmall
  apply (le_max_left y 1).trans
  by_contra! hshort
  have hN : ((n+2:ℕ):ℝ) ≤ 2*(n+1:ℕ) := by push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  have h₁ := mul_le_mul_of_nonneg_right hN (mul_nonneg hB.le (sq_nonneg (u n)))
  have h₂ := mul_le_mul_of_nonneg_right hshort.le (mul_nonneg hB.le (hpos n).le)
  have h₃ := (lt_div_iff₀ (show 0 < 2*B*K by positivity)).mp hsmall
  nlinarith only [hn,h₁,h₂,h₃]

#print axioms gaussian_first_three_date

/-- At the first three-gate spectral date, the physical gate density
still exceeds every fixed density below one. Any basis realizing the
three-gate fit therefore costs almost half a gate per bond. -/
theorem gaussian_first_three_physical_cost :
    ∃ A > 0, ∀ η : ℝ, 0 < η → ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let U := unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (firstThreeDate A ω n)
      (∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
        HasProjectiveCircuitApproximation (n+2) (1/10) 3 (W.val*U*star W.val)) ∧
      (∀ s : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) s U → (1-η)*(n+1:ℕ) < (s:ℝ)) ∧
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (b : ℕ),
        HasProjectiveCircuitApproximation (n+2) (3/40) b W.val →
        HasProjectiveCircuitApproximation (n+2) (1/10) 3 (W.val*U*star W.val) →
        (1-η)*(n+1:ℕ) < ((2*b+3:ℕ):ℝ) := by
  obtain ⟨A,_,hA,_,h⟩ := gaussian_first_three_date
  refine ⟨A,hA,?_⟩
  intro η hη
  obtain ⟨a,_,hf⟩ := SpanningDensity.FixedHorizon.gaussian_all_bounded_horizons hη
  filter_upwards [h,hf] with ω hω hf
  filter_upwards [hω.1.eventually_lt_const zero_lt_one,hω.2.2.eventually (eventually_ge_atTop a),hf 1]
    with n hsmall hlarge hn
  intro U
  let t := firstThreeDate A ω n
  have ht : 0 < t := (div_pos hA (by positivity)).trans_le (least_three A ω n).1.1
  have hcost := hn t (by rw [abs_of_pos ht]; exact hlarge)
    (by rw [abs_of_pos ht]; exact hsmall.le)
  refine ⟨(least_three A ω n).1.2,hcost,?_⟩
  intro W b hW hfit
  let V : unitaryGroup (Fin (n+2) → Bool) ℂ := ⟨U,unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian _) t⟩
  have hh := SpectralApproximation.cost_in_physical_basis V W hW hfit
  rw [show (1/10:ℝ)+2*(3/40)=1/4 by norm_num] at hh
  exact hcost _ hh

#print axioms gaussian_first_three_physical_cost
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
