import GaloisForLFunctions.RHTower.WeilLogShiftRecoveryHomeomorphism

/-!
# Moment-domain density in recovery-history space

Every finite prescribed recovery history can be realized while retaining the
entire signed, excess, and deficit moment profile of any chosen baseline.
These realizations approach every history coordinatewise. Consequently every
realized moment profile is dense in the product topology, despite exact recovery
of all coefficients from the complete history. In particular arbitrary finite
prefixes coexist with every open or closed symmetric moment domain.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- Match the first N recovery samples and retain the baseline coefficient tail. -/
def weilLogShiftRecoverySplice (base height : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  weilLogShiftRecoveryPrefix base (weilLogShiftRecoveryInverse height) (N + 2)

theorem weilLogShiftRecoverySplice_tail (base height : ℕ → ℝ) (N n : ℕ)
    (hn : N + 2 ≤ n) : weilLogShiftRecoverySplice base height N n = base n := by
  simp only [weilLogShiftRecoverySplice, weilLogShiftRecoveryPrefix,
    if_neg (show ¬ n < N + 2 by omega)]

/-- Arbitrary finite data are matched exactly, not only approximated. -/
theorem weilLogShiftRecoverySplice_history (base height : ℕ → ℝ) (N k : ℕ)
    (hk : k < N) :
    weilLogShiftRecoveryHistory (weilLogShiftRecoverySplice base height N) k = height k := by
  have hp := (weilLogShiftRecoveryProbe_prefix_iff
    (weilLogShiftRecoverySplice base height N) (weilLogShiftRecoveryInverse height)
    (k + 2)).mpr (fun n _ hn => by
      simp only [weilLogShiftRecoverySplice, weilLogShiftRecoveryPrefix,
        if_pos (show n < N + 2 by omega)])
  change weilLogShiftRecoveryProbe (weilLogShiftRecoverySplice base height N) (k + 2) = _
  rw [hp (k + 2) (by omega) le_rfl]
  exact congrFun (weilLogShiftRecoveryHistory_inverse height) k

/-- Any coefficientwise series retains summability under recovery-prefix splicing. -/
theorem summable_weilLogShiftRecoverySplice_terms_iff (base height : ℕ → ℝ) (N : ℕ)
    (term : ℕ → ℝ → ℝ) :
    (Summable fun n => term n (weilLogShiftRecoverySplice base height N n)) ↔
      Summable (fun n => term n (base n)) := by
  rw [← summable_nat_add_iff (N + 2)
      (f := fun n => term n (weilLogShiftRecoverySplice base height N n)),
    ← summable_nat_add_iff (N + 2) (f := fun n => term n (base n))]
  have htail (n : ℕ) : weilLogShiftRecoverySplice base height N (n + (N + 2)) =
      base (n + (N + 2)) :=
    weilLogShiftRecoverySplice_tail base height N _ (by omega)
  simp only [htail]

/-- The complete signed, excess, and deficit convergence domains agree. -/
def WeilLogShiftMomentEquivalent (lam base : ℕ → ℝ) : Prop :=
  ∀ y : ℝ,
    ((Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔
      Summable (fun n => weilDeviation base n * pairedLogKernel y n)) ∧
    ((Summable fun n => deviationExcess lam n * pairedLogKernel y n) ↔
      Summable (fun n => deviationExcess base n * pairedLogKernel y n)) ∧
    ((Summable fun n => deviationDeficit lam n * pairedLogKernel y n) ↔
      Summable (fun n => deviationDeficit base n * pairedLogKernel y n))

theorem weilLogShiftRecoverySplice_momentEquivalent (base height : ℕ → ℝ) (N : ℕ) :
    WeilLogShiftMomentEquivalent (weilLogShiftRecoverySplice base height N) base := by
  intro y
  refine ⟨?_, ?_, ?_⟩
  · exact summable_weilLogShiftRecoverySplice_terms_iff base height N
      (fun n x => (if 2 ≤ n then (x - ArithmeticFunction.vonMangoldt n) / sqrt n else 0) *
        pairedLogKernel y n)
  · exact summable_weilLogShiftRecoverySplice_terms_iff base height N
      (fun n x => max (if 2 ≤ n then
        (x - ArithmeticFunction.vonMangoldt n) / sqrt n else 0) 0 * pairedLogKernel y n)
  · exact summable_weilLogShiftRecoverySplice_terms_iff base height N
      (fun n x => max (-(if 2 ≤ n then
        (x - ArithmeticFunction.vonMangoldt n) / sqrt n else 0)) 0 * pairedLogKernel y n)

/-- Every target history is a coordinatewise limit of histories with one fixed moment profile. -/
theorem tendsto_weilLogShiftRecoverySplice_history (base height : ℕ → ℝ) :
    Tendsto (fun N => weilLogShiftRecoveryHistory (weilLogShiftRecoverySplice base height N))
      atTop (𝓝 height) := by
  apply tendsto_pi_nhds.mpr
  intro k
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => height k) atTop (𝓝 (height k))).congr'
  apply eventually_atTop.mpr
  refine ⟨k + 1, fun N hN => ?_⟩
  exact (weilLogShiftRecoverySplice_history base height N k (by omega)).symm

/-- Each realized triple of moment domains is dense among all recovery histories. -/
theorem dense_weilLogShiftRecoveryHistory_momentClass (base : ℕ → ℝ) :
    Dense {height : ℕ → ℝ | ∃ lam : ℕ → ℝ,
      weilLogShiftRecoveryHistory lam = height ∧ WeilLogShiftMomentEquivalent lam base} := by
  intro height
  apply mem_closure_of_tendsto (tendsto_weilLogShiftRecoverySplice_history base height)
  filter_upwards with N
  exact ⟨weilLogShiftRecoverySplice base height N, rfl,
    weilLogShiftRecoverySplice_momentEquivalent base height N⟩

private theorem summable_excess_of_zero (base : ℕ → ℝ)
    (hzero : ∀ n, deviationExcess base n = 0) (y : ℝ) :
    Summable (fun n => deviationExcess base n * pairedLogKernel y n) := by
  simpa only [hzero, zero_mul] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

private theorem summable_splice_excess_of_zero (base height : ℕ → ℝ) (N : ℕ)
    (hzero : ∀ n, deviationExcess base n = 0) :
    Summable (deviationExcess (weilLogShiftRecoverySplice base height N)) := by
  apply (summable_weilLogShiftRecoverySplice_terms_iff base height N
    (fun n x => max (if 2 ≤ n then
      (x - ArithmeticFunction.vonMangoldt n) / sqrt n else 0) 0)).mpr
  change Summable (deviationExcess base)
  rw [show deviationExcess base = (fun _ => 0) from funext hzero]
  exact summable_zero

/-- No finite recovery prefix restricts the radius of an open moment domain,
even when every local excess moment is finite. Radius zero gives the empty domain. -/
theorem exists_weilLogShiftRecoveryPrefix_open_domain (height : ℕ → ℝ) (N : ℕ) (R : ℝ) :
    ∃ lam : ℕ → ℝ,
      (∀ k : ℕ, k < N → weilLogShiftRecoveryHistory lam k = height k) ∧
      Summable (deviationExcess lam) ∧
      (∀ y : ℝ, Summable fun n => deviationExcess lam n * pairedLogKernel y n) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔ |y| < |R| := by
  obtain ⟨base, _, hzero, hdomain⟩ :=
    exists_minorant_with_open_potential_domain |R| (abs_nonneg R)
  refine ⟨weilLogShiftRecoverySplice base height N,
    weilLogShiftRecoverySplice_history base height N,
    summable_splice_excess_of_zero base height N hzero, ?_, ?_⟩
  · intro y
    exact (weilLogShiftRecoverySplice_momentEquivalent base height N y).2.1.mpr
      (summable_excess_of_zero base hzero y)
  · intro y
    exact (weilLogShiftRecoverySplice_momentEquivalent base height N y).1.trans (hdomain y)

/-- Every finite prefix also admits each closed symmetric domain, including
the singleton origin. Thus finite data do not determine endpoint inclusion. -/
theorem exists_weilLogShiftRecoveryPrefix_closed_domain (height : ℕ → ℝ) (N : ℕ) (R : ℝ) :
    ∃ lam : ℕ → ℝ,
      (∀ k : ℕ, k < N → weilLogShiftRecoveryHistory lam k = height k) ∧
      Summable (deviationExcess lam) ∧
      (∀ y : ℝ, Summable fun n => deviationExcess lam n * pairedLogKernel y n) ∧
      ∀ y : ℝ, (Summable fun n => weilDeviation lam n * pairedLogKernel y n) ↔ |y| ≤ |R| := by
  obtain ⟨base, _, hzero, hdomain⟩ :=
    exists_minorant_with_closed_potential_domain |R| (abs_nonneg R)
  refine ⟨weilLogShiftRecoverySplice base height N,
    weilLogShiftRecoverySplice_history base height N,
    summable_splice_excess_of_zero base height N hzero, ?_, ?_⟩
  · intro y
    exact (weilLogShiftRecoverySplice_momentEquivalent base height N y).2.1.mpr
      (summable_excess_of_zero base hzero y)
  · intro y
    exact (weilLogShiftRecoverySplice_momentEquivalent base height N y).1.trans (hdomain y)

/-- The entire real-shift convergence domain also coexists with every finite prefix. -/
theorem exists_weilLogShiftRecoveryPrefix_entire_domain (height : ℕ → ℝ) (N : ℕ) :
    ∃ lam : ℕ → ℝ,
      (∀ k : ℕ, k < N → weilLogShiftRecoveryHistory lam k = height k) ∧
      ∀ y : ℝ, Summable fun n => weilDeviation lam n * pairedLogKernel y n := by
  let base : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n
  refine ⟨weilLogShiftRecoverySplice base height N,
    weilLogShiftRecoverySplice_history base height N, ?_⟩
  intro y
  apply (weilLogShiftRecoverySplice_momentEquivalent base height N y).1.mpr
  simpa only [weilDeviation, base, sub_self, zero_div, ite_self, zero_mul] using
    (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

end RHTower
