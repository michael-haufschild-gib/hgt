import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BondSamples
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.IntegerScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianMass
import Mathlib.Analysis.PSeries

/-! # Simultaneous weak buffers and coefficient caps on one frozen chain -/

open Real Filter MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private def failedBuffers (n : ℕ) : Set PathPauliDisorder :=
  let q := sizeRoot (n+2)
  let N := q^62
  ⋃ i : Fin ((n+1)/(3*N)), {ω | ∀ j : Fin N,
    (fun k => ω (candidateIndex (3*N*i.val) (j,k)))∉weakBond (((q:ℝ)^6)⁻¹)}

private theorem failed_mass :
    ∀ᶠ n : ℕ in atTop, pathPauliDisorderLaw.real (failedBuffers n)≤1/((n+2:ℕ):ℝ)^3 := by
  let c := (2*gaussianDensityFloor)^9
  have hc : 0<c := pow_pos (mul_pos two_pos gaussianDensityFloor_pos) _
  have hl := (tendsto_add_atTop_nat 2).eventually (log_root_eventually hc 4 0)
  filter_upwards [hl] with n hn
  let K : ℝ := (n+2:ℕ)
  let q := sizeRoot (n+2)
  let N := q^62
  let b := (n+1)/(3*N)
  have hK : 0<K := by dsimp only [K]; positivity
  have hq : 1≤q := (root_bounds (by omega : 0<n+2)).1
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have hprice : pathPauliDisorderLaw.real (failedBuffers n)≤(b:ℝ)*exp (-c*(q:ℝ)^8) := by
    change pathPauliDisorderLaw.real (⋃ i : Fin b, {ω | ∀ j : Fin (q^62),
      (fun l => ω (candidateIndex (3*q^62*i.val) (j,l)))∉weakBond (((q:ℝ)^6)⁻¹)})≤_
    rw [hk]
    exact all_buffer_miss_bound b k
  have hlarge : 4*log K≤c*(q:ℝ)^8 := (by simpa only [add_zero] using hn : 4*log K≤c*(q:ℝ)^2).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq' (by decide : 2≤8)) hc.le)
  have htail : exp (-c*(q:ℝ)^8)≤1/K^4 := by
    apply (exp_le_exp.mpr (show -c*(q:ℝ)^8≤ -(4*log K) by linarith only [hlarge])).trans_eq
    rw [exp_neg,show (4:ℝ)*log K=(4:ℕ)*log K by norm_num,exp_nat_mul,exp_log hK,one_div]
  have hb : (b:ℝ)≤K := by exact_mod_cast ((Nat.div_le_self (n+1) (3*N)).trans (by omega : n+1≤n+2))
  apply (hprice.trans (mul_le_mul hb htail (exp_pos _).le hK.le)).trans_eq
  field_simp

/-- Every full buffer on every sufficiently long prefix contains a
bond whose nine couplings are all at most q⁻⁶ in absolute value.
Concurrently every coefficient on the whole prefix is at most q. -/
theorem gaussian_all_weak_buffers :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let q := sizeRoot (n+2)
      let N := q^62
      (∀ i : Fin ((n+1)/(3*N)), ∃ j : Fin N,
        (fun l => ω (candidateIndex (3*N*i.val) (j,l)))∈weakBond (((q:ℝ)^6)⁻¹)) ∧
        ∀ l : PathLabel n, |pathPauliDisorderShell ω n l|≤q := by
  have hs : Summable fun n => pathPauliDisorderLaw.real (failedBuffers n) := by
    apply (Real.summable_one_div_nat_pow.mpr (by decide : 1<3)).of_norm_bounded_eventually_nat
    filter_upwards [failed_mass,eventually_gt_atTop 0] with n hn hpos
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact hn.trans (div_le_div_of_nonneg_left zero_le_one (pow_pos (Nat.cast_pos.mpr hpos) 3)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega : n≤n+2)) _))
  have hgood : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉failedBuffers n := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hs.tsum_ofReal_ne_top
  obtain ⟨B,hB,hm⟩ := FirstAscent.gaussian_subset_mass
  have hl := (tendsto_add_atTop_nat 2).eventually (log_root_eventually zero_lt_one 4 (4*log B))
  filter_upwards [hgood,hm] with ω hg hm
  filter_upwards [hg,hm,hl] with n hn hm hl
  intro q N
  constructor
  · intro i
    by_contra! h
    exact hn (mem_iUnion.mpr ⟨i,h⟩)
  · intro l
    have hh := hm {l} (Finset.singleton_nonempty l)
    simp only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,one_pow,mul_one,div_one] at hh
    have hK : 0<((n+2:ℕ):ℝ) := by positivity
    rw [log_mul hB.ne' hK.ne'] at hh
    have hq : (0:ℝ)≤q := Nat.cast_nonneg _
    nlinarith only [hh,hl,abs_nonneg (pathPauliDisorderShell ω n l),hq]

#print axioms gaussian_all_weak_buffers
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
