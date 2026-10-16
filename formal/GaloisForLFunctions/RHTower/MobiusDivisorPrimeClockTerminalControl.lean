import GaloisForLFunctions.RHTower.MobiusDivisorPrimeClockRealization
import GaloisForLFunctions.RHTower.MobiusDivisorAdaptiveTerminalCriticalSource

/-!
# Actual terminal fibres realize compact-clock controls

A single processed small-prime core works throughout the prescribed clock
interval. The same distinct fresh primes control the literal singleton
fibres uniformly, with arbitrarily small normalized diagonal energy.
-/

noncomputable section
open Finset Set Filter Topology
open scoped NNReal

namespace RHTower

/-- The complete small-prime core, including the square boundary. -/
def criticalPrimeClockTerminalCore (N : ℕ) : Finset ℕ :=
  (mobiusDivisorSelectionPrimes N).filter fun p => p * p ≤ N

private lemma square_gt_of_sqrt_lt {N p : ℕ} (hp : Real.sqrt N < p) : N < p * p := by
  have hp0 : (0 : ℝ) < p := (Real.sqrt_nonneg _).trans_lt hp
  have hh := mul_pos (sub_pos.mpr hp)
    (add_pos_of_pos_of_nonneg hp0 (Real.sqrt_nonneg (N : ℝ)))
  have he := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsq : (N : ℝ) < (p : ℝ) * p := by nlinarith only [hh, he]
  exact_mod_cast hsq

theorem criticalPrimeClockTerminalCore_fresh {N p : ℕ} (hp : Real.sqrt N < p) :
    p ∉ criticalPrimeClockTerminalCore N := by
  intro h
  exact (not_lt_of_ge (Finset.mem_filter.mp h).2) (square_gt_of_sqrt_lt hp)

/-- The common small-prime core gives the exact complete child at every
smaller cutoff containing the selected terminal prime. -/
theorem criticalPrimeClockTerminalCore_singleton {N M p : ℕ}
    (hMN : M ≤ N) (hp : p.Prime) (hpM : p < M) (hNp : Real.sqrt N < p) :
    mobiusDivisorSelectionFibre M (criticalPrimeClockTerminalCore N) {p} =
      -Real.sqrt p * criticalContinuousAbel ((M : ℝ) / p) := by
  have hcover : ∀ q ∈ mobiusDivisorSelectionPrimes M, q * q ≤ M →
      q ∈ criticalPrimeClockTerminalCore N := by
    intro q hq hsq
    obtain ⟨hqr, hqp⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hqr).trans_le hMN),
        hqp⟩, hsq.trans hMN⟩
  apply adaptive_terminal_singleton_source M (criticalPrimeClockTerminalCore N) hcover
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpM, hp⟩,
      criticalPrimeClockTerminalCore_fresh hNp⟩

/-- Exact normalization, retaining the unmodified continuous Abel child. -/
theorem criticalPrimeClockAtom_apply (a : ℝ≥0) {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (u : CriticalClockWindow a) :
    criticalPrimeClockAtom a N p u =
      (Real.exp ((3 / 2 : ℝ) * (u : ℝ)) / N) * Real.sqrt p *
        criticalContinuousAbel ((N : ℝ) * Real.exp (-u) / p) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hx : 0 < (N : ℝ) / p := div_pos hN0 hp0
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
  have hsp : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  have harg : Real.exp (Real.log ((N : ℝ) / p) - u) =
      (N : ℝ) * Real.exp (-u) / p := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx]
    ring
  have hexp : -(3 / 2 : ℝ) * (Real.log ((N : ℝ) / p) - u) =
      (3 / 2 : ℝ) * (u : ℝ) - Real.log ((N : ℝ) / p) -
        Real.log ((N : ℝ) / p) / 2 := by ring
  change (Real.sqrt N / p) *
    (Real.exp (-(3 / 2 : ℝ) * (Real.log ((N : ℝ) / p) - u)) *
      criticalContinuousAbel (Real.exp (Real.log ((N : ℝ) / p) - u))) = _
  rw [harg, hexp, Real.exp_sub, Real.exp_sub, Real.exp_half,
    Real.exp_log hx, Real.sqrt_div hN0.le]
  field_simp [hN0.ne', hp0.ne', hs, hsp]

/-- Uniform control of the actual divisor singleton fibres, using one
constructively specified processed core and one finite set of distinct
fresh primes throughout the whole clock interval. The approximation and
small quadratic cost hold for that same set. -/
theorem eventually_exists_terminalPrimeClock_control
    (a : ℝ≥0) (f : C(CriticalClockWindow a, ℝ)) (ε : Set.Ioi (0 : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p) ∧
      Disjoint S (criticalPrimeClockTerminalCore N) ∧
      ∀ (u : CriticalClockWindow a) (M : ℕ),
        (M : ℝ) = (N : ℝ) * Real.exp (-u) →
        |(∑ p ∈ S, -(Real.exp ((3 / 2 : ℝ) * (u : ℝ)) / N) *
            mobiusDivisorSelectionFibre M (criticalPrimeClockTerminalCore N) {p}) - f u| < ε ∧
        (∑ p ∈ S, ((Real.exp ((3 / 2 : ℝ) * (u : ℝ)) / N) *
            mobiusDivisorSelectionFibre M (criticalPrimeClockTerminalCore N) {p}) ^ 2) < ε := by
  have he := eventually_exists_criticalPrimeClock_realization a ((a : ℝ) + 1) f ε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  obtain ⟨S, hS, happ, hdiag⟩ := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  refine ⟨S, fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun p hp =>
      criticalPrimeClockTerminalCore_fresh (hS p hp).2.1
  intro u M hM
  have hMN : M ≤ N := by
    have he1 : Real.exp (-(u : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr u.property.1)
    have hh := mul_le_mul_of_nonneg_left he1 hN0.le
    rw [mul_one, ← hM] at hh
    exact_mod_cast hh
  have hpM (p : ℕ) (hp : p ∈ S) : p < M := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    have hul : (u : ℝ) < Real.log ((N : ℝ) / p) :=
      (u.property.2.trans_lt (lt_add_one (a : ℝ))).trans (hS p hp).2.2
    have he' := Real.exp_lt_exp.mpr hul
    rw [Real.exp_log (div_pos hN0 hp0)] at he'
    have hh : (p : ℝ) < (N : ℝ) * Real.exp (-(u : ℝ)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      apply (lt_div_iff₀ (Real.exp_pos (u : ℝ))).mpr
      simpa only [mul_comm] using (lt_div_iff₀ hp0).mp he'
    rw [← hM] at hh
    exact_mod_cast hh
  have hfibre (p : ℕ) (hp : p ∈ S) :
      criticalPrimeClockAtom a N p u =
        -(Real.exp ((3 / 2 : ℝ) * (u : ℝ)) / N) *
          mobiusDivisorSelectionFibre M (criticalPrimeClockTerminalCore N) {p} := by
    rw [criticalPrimeClockTerminalCore_singleton hMN (hS p hp).1
      (hpM p hp) (hS p hp).2.1,
      criticalPrimeClockAtom_apply a hNpos (hS p hp).1.pos u, ← hM]
    ring
  constructor
  · have hh := ContinuousMap.norm_coe_le_norm
      ((∑ p ∈ S, criticalPrimeClockAtom a N p) - f) u
    rw [ContinuousMap.sub_apply, ContinuousMap.sum_apply, Real.norm_eq_abs] at hh
    rw [Finset.sum_congr rfl hfibre] at hh
    exact hh.trans_lt happ
  · apply lt_of_le_of_lt _ hdiag
    apply Finset.sum_le_sum
    intro p hp
    have hh := pow_le_pow_left₀ (norm_nonneg (criticalPrimeClockAtom a N p u))
      (ContinuousMap.norm_coe_le_norm (criticalPrimeClockAtom a N p) u) 2
    rw [hfibre p hp, Real.norm_eq_abs, sq_abs] at hh
    convert hh using 1
    ring

end RHTower
