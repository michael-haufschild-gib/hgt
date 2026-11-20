import GaloisForLFunctions.GaloisTheoryOfZeros.OneRationalHeightComparisonPerJensenDegree

/-!
# Error tolerance and density in the two-evaluation Jensen test

A strict reversal persists along a full arithmetic progression. It
therefore occupies a positive proportion of every sufficiently long
initial segment. Conversely, on RH every comparison succeeds. Vanishing
absolute errors in the two-point readings preserve the test.
-/

open Filter Topology Finset
noncomputable section
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Proportion of the first N observations with a strict reversal of
margin ε. -/
def jensenReversalRate (ε : ℝ) (N : ℕ) : ℝ :=
  (((range N).filter (fun d => jensenHeightGain d (scheduledRationalHeights d) < -ε)).card:ℝ)/N

private theorem reversalRate_zero (h : RiemannHypothesis) {ε : ℝ} (hε : 0≤ε) (N : ℕ) :
    jensenReversalRate ε N=0 := by
  have none : ((range N).filter (fun d => jensenHeightGain d (scheduledRationalHeights d) < -ε))=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact (neg_nonpos.mpr hε |>.trans (jensen_height_gain_nonneg_of_rh h _ _)).not_gt (mem_filter.mp hd).2
  simp [jensenReversalRate,none]

/-- Failure of RH forces a fixed positive fraction of observations,
through every large cutoff, to reverse by the same fixed margin. -/
theorem not_rh_iff_positive_lower_density_reversals :
    ¬ RiemannHypothesis ↔ ∃ ε c : ℝ, 0<ε ∧ 0<c ∧ ∀ᶠ N in atTop, c≤jensenReversalRate ε N := by
  constructor
  · intro hn
    obtain ⟨a,D,hD,ε,hε,hcount⟩ := scheduled_reversal_count_of_not_rh hn
    have hD' : 0<(D:ℝ) := Nat.cast_pos.mpr hD
    refine ⟨ε,1/(2*(D:ℝ)),hε,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop (2*(a+D))] with N hN
    let m := (N-a)/D
    have split := Nat.div_add_mod (N-a) D
    change D*m+(N-a)%D=N-a at split
    have rem := Nat.mod_lt (N-a) hD
    have left : a+D*m≤N := by omega
    have half : N≤2*(D*m) := by omega
    let S (L : ℕ) := (range L).filter (fun d => jensenHeightGain d (scheduledRationalHeights d) < -ε)
    have incl : S (a+D*m)⊆S N := filter_subset_filter _ (range_mono left)
    have size : m≤(S N).card := (hcount m).trans (card_le_card incl)
    have full : N≤2*(D*(S N).card) := half.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left D size))
    have realBound : (N:ℝ)≤2*((D:ℝ)*(S N).card) := by exact_mod_cast full
    have hN' : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
    change 1/(2*(D:ℝ)) ≤ ((S N).card:ℝ)/N
    apply (div_le_div_iff₀ (by positivity) hN').mpr
    linarith only [realBound]
  · rintro ⟨ε,c,hε,hc,ev⟩ h
    obtain ⟨N,hN⟩ := ev.exists
    rw [reversalRate_zero h hε.le] at hN
    exact hc.not_ge hN

/-- It suffices that each positive-margin failure rate approaches zero
along a subsequence. The subsequence may depend on the margin. -/
theorem rh_iff_arbitrarily_small_reversal_rates :
    RiemannHypothesis ↔ ∀ ε c : ℝ, 0<ε → 0<c →
      ∃ᶠ N in atTop, jensenReversalRate ε N<c := by
  constructor
  · intro h ε c hε hc
    exact Frequently.of_forall fun n => (reversalRate_zero h hε.le n).trans_lt hc
  · intro small
    by_contra hn
    obtain ⟨ε,c,hε,hc,ev⟩ := not_rh_iff_positive_lower_density_reversals.mp hn
    obtain ⟨_,lo,hi⟩ := ((small ε c hε hc).and_eventually ev).exists
    exact lo.not_ge hi

/-- Any readings with vanishing absolute error give the same RH test:
their negative parts must tend to zero. No prescribed convergence rate
and no exact decisions at near-zero comparisons are needed. -/
theorem rh_iff_approximate_height_defects_tend_to_zero (F : ℕ → ℝ)
    (err : Tendsto (fun d => |F d-jensenHeightGain d (scheduledRationalHeights d)|) atTop (𝓝 0)) :
    RiemannHypothesis ↔ Tendsto (fun d => max 0 (-(F d))) atTop (𝓝 0) := by
  let G (d : ℕ) := jensenHeightGain d (scheduledRationalHeights d)
  constructor
  · intro h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds err
    · exact fun d => le_max_left _ _
    · intro d
      apply max_le (abs_nonneg _)
      have hg : 0≤G d := jensen_height_gain_nonneg_of_rh h d _
      change -F d≤|F d-G d|
      linarith only [hg,neg_le_abs (F d-G d)]
  · intro ht
    by_contra hn
    obtain ⟨v,ε,hε,bad⟩ := not_rh_iff_persistent_rational_height_reversal.mp hn
    have small := err.eventually_lt_const (show 0<ε/2 by linarith only [hε])
    have good := ht.eventually_lt_const (show 0<ε/2 by linarith only [hε])
    obtain ⟨d,hv,hbad,hsmall,hgood⟩ :=
      ((scheduledRationalHeights_recurrent v).and_eventually (bad.and (small.and good))).exists
    rw [hv] at hsmall
    linarith only [hbad,(abs_lt.mp hsmall).2,le_max_right (0:ℝ) (-(F d)),hgood]

end GaloisForLFunctions.GaloisTheoryOfZeros
