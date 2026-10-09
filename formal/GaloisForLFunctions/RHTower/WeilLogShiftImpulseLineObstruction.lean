import GaloisForLFunctions.RHTower.WeilLogShiftLateColumnRunaway
import GaloisForLFunctions.RHTower.WeilLogShiftUniformBallGenericity

/-!
# At most one exceptional amplitude on each late impulse line

Distinct amplitudes at one sufficiently late history coordinate have moment
differences whose norms tend to infinity at every real shift. Thus at most
one amplitude can have eventually bounded moments at some shift, and at most one can admit
a summable moment series at any shift.
-/

open Filter Topology Real
open scoped BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- Change one recovery-history coordinate by a real amplitude. -/
def weilLogShiftRecoveryImpulseHistory (center : ℕ →ᵇ ℝ) (k : ℕ) (t : ℝ) : ℕ →ᵇ ℝ :=
  center + t • weilLogShiftRecoveryUnitHistory k

theorem weilLogShiftRecoveryImpulseHistory_apply (center : ℕ →ᵇ ℝ) (k : ℕ) (t : ℝ)
    (j : ℕ) :
    weilLogShiftRecoveryImpulseHistory center k t j = center j + if j = k then t else 0 := by
  change center j + t * weilLogShiftRecoveryUnitHistory k j = _
  rw [weilLogShiftRecoveryUnitHistory_apply]
  split_ifs <;> ring

/-- Subtracting two impulse histories cancels their common center. -/
theorem weilLogShiftRecoveryImpulseHistory_sub (center : ℕ →ᵇ ℝ) (k : ℕ) (t u : ℝ) :
    weilLogShiftRecoveryImpulseHistory center k t - weilLogShiftRecoveryImpulseHistory center k u =
      (t - u) • weilLogShiftRecoveryUnitHistory k := by
  unfold weilLogShiftRecoveryImpulseHistory
  module

/-- The difference along an impulse line is the exact fixed-column response. -/
theorem weilLogShiftRecoveryImpulseHistory_moment_sub (center : ℕ →ᵇ ℝ) (k : ℕ)
    (t u y : ℝ) (n : ℕ) :
    weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t) n -
      weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k u) n =
        (t - u) * weilLogShiftRecoveryMomentResponse y n k := by
  rw [weilLogShiftRecoveryMoment_sub_eq, weilLogShiftRecoveryImpulseHistory_sub,
    map_smul, smul_eq_mul]
  rfl

/-- Failure of unbounded moment tails at every shift has a finite eventual certificate
already at the origin. -/
theorem weilLogShiftUniform_not_nowhere_bounded_iff_origin_eventually_bounded (h : ℕ →ᵇ ℝ) :
    ¬ WeilLogShiftUniformNowhereBounded h ↔
      ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖weilLogShiftRecoveryMoment 0 h n‖ ≤ B := by
  constructor
  · intro hh
    have hnot : ¬ ∀ (B : ℝ) (N : ℕ), ∃ n : ℕ,
        N ≤ n ∧ B < ‖weilLogShiftRecoveryMoment 0 h n‖ := by
      intro hlarge
      exact hh (weilLogShiftUniformNowhereBounded_of_origin h hlarge)
    push Not at hnot
    exact hnot
  · rintro ⟨B, N, hbound⟩ hlarge
    obtain ⟨n, hn, hgt⟩ := hlarge 0 B N
    exact (not_lt_of_ge (hbound n hn)) hgt

/-- Distinct amplitudes on every sufficiently late impulse line separate
without bound at each real-shift moment. The threshold is independent of center. -/
theorem exists_weilLogShiftRecoveryImpulse_moment_separation :
    ∃ K : ℕ, ∀ center : ℕ →ᵇ ℝ, ∀ k : ℕ, K ≤ k → ∀ t u : ℝ, t ≠ u → ∀ y : ℝ,
      Tendsto (fun n : ℕ =>
        ‖weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t) n -
          weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k u) n‖)
        atTop atTop := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryMomentResponse_fixed_column_runaway
  refine ⟨K, fun center k hk t u htu y => ?_⟩
  have hpos : 0 < |t - u| := abs_pos.mpr (sub_ne_zero.mpr htu)
  simpa only [weilLogShiftRecoveryImpulseHistory_moment_sub, Real.norm_eq_abs, abs_mul] using
    (hK k hk y).const_mul_atTop hpos

/-- At most one amplitude on any sufficiently late impulse line can have
eventually bounded moment terms at even one real shift. -/
theorem exists_weilLogShiftRecoveryImpulse_exceptional_subsingleton :
    ∃ K : ℕ, ∀ center : ℕ →ᵇ ℝ, ∀ k : ℕ, K ≤ k →
      Set.Subsingleton {t : ℝ |
        ¬ WeilLogShiftUniformNowhereBounded (weilLogShiftRecoveryImpulseHistory center k t)} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_moment_separation
  refine ⟨K, fun center k hk t ht u hu => ?_⟩
  by_contra htu
  obtain ⟨Bt, Nt, hBt⟩ :=
    (weilLogShiftUniform_not_nowhere_bounded_iff_origin_eventually_bounded _).mp ht
  obtain ⟨Bu, Nu, hBu⟩ :=
    (weilLogShiftUniform_not_nowhere_bounded_iff_origin_eventually_bounded _).mp hu
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hK center k hk t u htu 0).eventually_ge_atTop (Bt + Bu + 1))
  let n := max N (max Nt Nu)
  have hnN : N ≤ n := le_max_left _ _
  have hnNt : Nt ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hnNu : Nu ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  have hsep := hN n hnN
  have htbound := hBt n hnNt
  have hubound := hBu n hnNu
  have htriangle := norm_sub_le
    (weilLogShiftRecoveryMoment 0 (weilLogShiftRecoveryImpulseHistory center k t) n)
    (weilLogShiftRecoveryMoment 0 (weilLogShiftRecoveryImpulseHistory center k u) n)
  linarith only [hsep, htbound, hubound, htriangle]

/-- Moment summability at even one history-dependent shift identifies at
most one amplitude on a sufficiently late impulse line. -/
theorem exists_weilLogShiftRecoveryImpulse_summable_subsingleton :
    ∃ K : ℕ, ∀ center : ℕ →ᵇ ℝ, ∀ k : ℕ, K ≤ k →
      Set.Subsingleton {t : ℝ | ∃ y : ℝ,
        Summable (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t))} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_exceptional_subsingleton
  refine ⟨K, fun center k hk t ht u hu => ?_⟩
  apply hK center k hk
  · intro hlarge
    obtain ⟨y, hy⟩ := ht
    exact weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hlarge y hy
  · intro hlarge
    obtain ⟨y, hy⟩ := hu
    exact weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hlarge y hy

end RHTower
