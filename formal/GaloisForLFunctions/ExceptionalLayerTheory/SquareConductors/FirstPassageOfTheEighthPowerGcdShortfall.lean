import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CountingLargeEighthPowerGcdDeficits
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CumulativeQuadratureOfTheGcdDeficit

/-!
# First passage of the eighth-power gcd shortfall

The inverse of the cumulative shortfall grows exponentially in the
target. Microscopically its rounding error has a whole interval of
possible limits, determined by the individual arithmetic jumps.
-/

noncomputable section
open Filter Finset Set
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private abbrev D := powerGridGcdDeficit 8

private theorem mass_top : Tendsto D atTop atTop := by
  obtain ⟨c,h⟩ := eighth_gcd_deficit_centered_converges
  have logtop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [logtop.eventually_ge_atTop (2*(B-c+1)),
    h.eventually_const_lt (sub_one_lt c)] with n hn hh
  change c-1 < D n-(1/2)*Real.log n at hh
  change 2*(B-c+1) ≤ Real.log n at hn
  linarith only [hn,hh]

private theorem reached (h : ℝ) : ∃ k : ℕ, h ≤ D (k+1) :=
  ((mass_top.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop h).exists

/-- First positive endpoint whose total shortfall reaches a prescribed level. -/
def eighthPassage (h : ℝ) : ℕ := Nat.find (reached h)+1

private abbrev prev (h : ℝ) := Nat.find (reached h)

theorem eighth_passage_le_iff (h : ℝ) (k : ℕ) :
    eighthPassage h ≤ k+1 ↔ h ≤ D (k+1) := by
  refine ⟨fun hk => (Nat.find_spec (reached h)).trans (monotone_gcd_deficit 8 hk),?_⟩
  exact fun hh => Nat.succ_le_succ (Nat.find_min' _ hh)

private theorem prev_top : Tendsto prev atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_gt_atTop (D (k+1))] with h hh
  have hnot := mt ((eighth_passage_le_iff h k).mp) hh.not_ge
  change ¬ prev h+1 ≤ k+1 at hnot
  omega

private theorem between_passages {h : ℝ} (hp : 0 < h) :
    D (prev h) < h ∧ h ≤ D (eighthPassage h) := by
  refine ⟨?_,Nat.find_spec (reached h)⟩
  cases hk : prev h with
  | zero => simpa [D,powerGridGcdDeficit] using hp
  | succ k =>
    exact lt_of_not_ge fun hh => by
      have hm := (eighth_passage_le_iff h k).mpr hh
      change prev h+1 ≤ k+1 at hm
      omega

private abbrev jump (k : ℕ) := D (k+1)-D k

/-- Each positive jump has limiting harmonic coefficient one half. -/
theorem eighth_gcd_jump_law :
    Tendsto (fun k : ℕ => ((k+1:ℕ):ℝ)*jump k) atTop (𝓝 (1/2:ℝ)) := by
  have h := (eighth_reading_harmonic_limit false).comp (tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards [h.eventually_const_lt (by norm_num : (0:ℝ)<1/2)] with k hk
  change 0 < ((k+1:ℕ):ℝ)*eighthReading false (k+1) at hk
  have hr := pos_of_mul_pos_right hk (Nat.cast_nonneg _)
  change _ = ((k+1:ℕ):ℝ)*(D (k+1)-D k)
  simp only [D,powerGridGcdDeficit,sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le k)),
    add_sub_cancel_left]
  change _ = _ * max (eighthReading false (k+1)) 0
  rw [max_eq_left hr.le]
  rfl

private theorem jump_zero : Tendsto jump atTop (𝓝 0) := by
  have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)
  exact (eighth_gcd_jump_law.div_atTop ht).congr fun k => by
    change ((k+1:ℕ):ℝ)*jump k/((k+1:ℕ):ℝ)=jump k
    field_simp

/-- The level error at first passage tends to zero despite the discrete
arithmetic endpoints. -/
theorem eighth_passage_overshoot :
    Tendsto (fun h : ℝ => D (eighthPassage h)-h) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (jump_zero.comp prev_top)
  · exact .of_forall fun h => sub_nonneg.mpr (Nat.find_spec (reached h))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with h hp
    exact sub_le_sub_left (between_passages hp).1.le _

/-- The first crossing index is asymptotic to a fixed positive multiple
of exp(2h), with h ranging over all real targets. -/
theorem eighth_passage_exponential_law :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun h : ℝ => (eighthPassage h:ℝ)/Real.exp (2*h)) atTop (𝓝 A) := by
  obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
  have ht := (tendsto_add_atTop_nat 1).comp prev_top
  have diff := (eighth_passage_overshoot.sub (hc.comp ht)).const_mul 2
  refine ⟨Real.exp (2*(0-c)),Real.exp_pos _,(Real.continuous_exp.continuousAt.tendsto.comp diff).congr ?_⟩
  intro h
  change Real.exp (2*((D (eighthPassage h)-h)-(D (eighthPassage h)-(1/2)*Real.log (eighthPassage h))))=_
  rw [show 2*((D (eighthPassage h)-h)-(D (eighthPassage h)-(1/2)*Real.log (eighthPassage h))) =
    Real.log (eighthPassage h)-2*h by ring,Real.exp_sub,
    Real.exp_log (Nat.cast_pos.mpr (Nat.succ_pos (prev h)) : (0:ℝ) < eighthPassage h)]

/-- The scaled first-passage error has exactly [0,1/2] as its set of
subsequential limits. The upper endpoint uses targets approaching a
jump from its interior. -/
theorem eighth_scaled_overshoot_cluster_iff (z : ℝ) :
    (∃ h : ℕ → ℝ, Tendsto h atTop atTop ∧ Tendsto
      (fun n => (eighthPassage (h n):ℝ)*(D (eighthPassage (h n))-h n)) atTop (𝓝 z)) ↔
      z ∈ Icc 0 (1/2:ℝ) := by
  constructor
  · rintro ⟨h,ht,hl⟩
    refine ⟨ge_of_tendsto hl (.of_forall fun n => mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (Nat.find_spec (reached _)))),?_⟩
    apply le_of_tendsto_of_tendsto hl (eighth_gcd_jump_law.comp (prev_top.comp ht))
    filter_upwards [ht.eventually_gt_atTop 0] with n hp
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left (between_passages hp).1.le _) (Nat.cast_nonneg _)
  · rintro ⟨hz,hz'⟩
    let r := fun n : ℕ => (2*z)*(1-1/((n:ℝ)+1))
    let h := fun n : ℕ => D (n+1)-r n*jump n
    have rn (n : ℕ) : 0 ≤ r n ∧ r n < 1 := by
      have den : 0 < (n:ℝ)+1 := by positivity
      have u := (one_div_le_one_div_of_le zero_lt_one (by linarith only [Nat.cast_nonneg (α:=ℝ) n] : (1:ℝ) ≤ n+1))
      rw [div_one] at u
      have v := one_div_pos.mpr den
      have w : 0 ≤ 1-1/((n:ℝ)+1) := sub_nonneg.mpr u
      exact ⟨mul_nonneg (by linarith only [hz]) w, (mul_le_mul_of_nonneg_right
        (by linarith only [hz'] : 2*z ≤ 1) w).trans_lt (by linarith only [v])⟩
    have rlim : Tendsto r atTop (𝓝 (2*z)) := by
      have hu := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop
        (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R:=ℝ)))
      simpa only [r,sub_zero,mul_one] using ((tendsto_const_nhds (x:=(1:ℝ))).sub hu).const_mul (2*z)
    have inside : ∀ᶠ n : ℕ in atTop, D n < h n ∧ h n ≤ D (n+1) := by
      filter_upwards [eighth_gcd_jump_law.eventually_const_lt (by norm_num : (0:ℝ)<1/2)] with n hn
      have hj := pos_of_mul_pos_right hn (Nat.cast_nonneg _)
      have d := mul_lt_mul_of_pos_right (rn n).2 hj
      have p := mul_nonneg (rn n).1 hj.le
      dsimp only [h,jump] at *
      constructor <;> linarith only [d,p]
    have peq : ∀ᶠ n : ℕ in atTop, eighthPassage (h n)=n+1 := by
      filter_upwards [inside] with n hn
      have up := (eighth_passage_le_iff (h n) n).mpr hn.2
      have low : n < eighthPassage (h n) := by
        by_contra! hle
        exact hn.1.not_ge ((Nat.find_spec (reached (h n))).trans (monotone_gcd_deficit 8 hle))
      omega
    refine ⟨h,tendsto_atTop_mono' atTop (inside.mono fun _ hn => hn.1.le) mass_top,?_⟩
    have lim := rlim.mul eighth_gcd_jump_law
    rw [show 2*z*(1/2)=z by ring] at lim
    apply lim.congr'
    filter_upwards [peq] with n hn
    rw [hn]
    dsimp only [h]
    ring

#print axioms eighth_passage_exponential_law
#print axioms eighth_scaled_overshoot_cluster_iff

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
