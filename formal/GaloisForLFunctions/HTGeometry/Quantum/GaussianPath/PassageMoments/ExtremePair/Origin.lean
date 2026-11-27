import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ResonantReturns.PairDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Return from a measured origin using the extreme energy gap -/
open Real Finset Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair
open PrecisionReturns
noncomputable section

/-- One tick synchronizes both extreme energy levels. Among the first
Q^(D−2) such ticks an empty circuit attains error 2π/Q. -/
theorem first_visit_by_extreme_period {n : ℕ} (H : selfAdjoint (Register n)) {a : ℝ}
    (ha : 0<a) (hw : 0<circuitHamiltonianSpectralWidth H) (s : ℕ) {Q : ℕ} (hQ : 0<Q) :
    let W := circuitHamiltonianSpectralWidth H
    firstVisit H a s (2*π/(Q:ℝ)) ≤ (a+2*π/W)*((Q:ℝ)^(2^n-2)) := by
  intro W
  let E := H.2.isHermitian.eigenvalues
  obtain ⟨b,_,hb⟩ := exists_mem_eq_sup' univ_nonempty E
  obtain ⟨c,_,hc⟩ := exists_mem_eq_inf' univ_nonempty E
  have he : W=E b-E c := congrArg₂ (·-·) hb hc
  have hbc : c≠b := by
    intro h
    rw [h,sub_self] at he
    exact hw.ne' he
  let P := 2*π/W
  have hP : 0<P := div_pos two_pi_pos hw
  let m := ⌈a/P⌉₊
  let τ := (m:ℝ)*P
  have hlo : a≤τ := (div_le_iff₀ hP).mp (Nat.le_ceil _)
  have hhi : τ≤a+P := by
    have h := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg ha.le hP.le)).le hP.le
    simpa only [τ,m,add_mul,one_mul,div_mul_cancel₀ _ hP.ne'] using h
  have hclock : (1:ℝ)*τ*(E b-E c)/(2*π)=(m:ℤ) := by
    rw [one_mul,←he,Int.cast_natCast]
    dsimp only [τ,P]
    field_simp [show W≠0 from hw.ne',pi_ne_zero]
  obtain ⟨l,hl,hmax,hfit⟩ := ResonantReturns.rational_pair_deadline H τ c b hbc
    (L:=1) (by decide) (m:ℤ) (by simpa only [Nat.cast_one] using hclock) hQ
  have hl₁ : (1:ℝ)≤l := by exact_mod_cast hl
  have hturn : a≤(l:ℝ)*τ := hlo.trans (le_mul_of_one_le_left (ha.le.trans hlo) hl₁)
  obtain ⟨z,hz,C,hC,herr⟩ := hfit
  have hmem : (l:ℝ)*τ ∈ visitSet H a s (2*π/(Q:ℝ)) :=
    ⟨hturn,z,hz,C,hC.trans (Nat.zero_le _),herr⟩
  have hindex : (l:ℝ)≤(Q:ℝ)^(2^n-2) := by
    rw [one_mul] at hmax
    exact_mod_cast hmax
  exact ((firstVisit_isLeast H a s (div_pos two_pi_pos (Nat.cast_pos.mpr hQ))).2 hmem).trans
    ((mul_le_mul hindex hhi (ha.le.trans hlo) (by positivity)).trans_eq (mul_comm ..))

/-- The distance paid by any budget at an origin controls the ratio of
one extreme-gap period to that origin, uniformly over register sizes. -/
theorem width_at_origin {n : ℕ} (H : selfAdjoint (Register n)) (j : ℕ) {a : ℝ} (ha : 0≤a) :
    2*orbitCircuitDistance H j a ≤ a*circuitHamiltonianSpectralWidth H := by
  obtain ⟨L,hL,hlip⟩ := orbitCircuitDistance_lipschitz_spectralWidth H j
  have hzero : orbitCircuitDistance H j 0=0 := by
    apply le_antisymm _ Metric.infDist_nonneg
    apply (hasProjectiveCircuitApproximation_iff_infDist _ j 0).mp
    exact ⟨1,by simp,TwoQubitCircuit.one n,Nat.zero_le _,by simp [TwoQubitCircuit.one_eval,unitaryEvolution]⟩
  have h := hlip.dist_le_mul a 0
  rw [hzero,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,
    abs_of_nonneg (show 0≤orbitCircuitDistance H j a from Metric.infDist_nonneg),abs_of_nonneg ha,hL] at h
  linarith only [h]

#print axioms first_visit_by_extreme_period
end
end GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair
