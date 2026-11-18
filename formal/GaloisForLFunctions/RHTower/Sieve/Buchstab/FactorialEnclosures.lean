import GaloisForLFunctions.RHTower.Sieve.Buchstab.DelayIntervals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Nested factorial enclosures for the Buchstab profile

The integral recurrence expresses the new profile as an average whose
fresh mass has weight at most `1/(n+3)`. Both ends of the old enclosure
can therefore be contracted towards the common endpoint by that factor.
-/

namespace RHTower.Sieve.Buchstab
open MeasureTheory Set Filter Topology
noncomputable section

/-- Update a bound about the right endpoint of the preceding cell. -/
private def shrink (n : ℕ) (v : ℝ) : ℝ :=
  profile n 1 + (v - profile n 1) / ((n:ℝ) + 3)

/-- Recursively propagated lower and upper bounds. -/
def enclosure : ℕ → ℝ × ℝ
  | 0 => (1/2, 1)
  | n+1 => (shrink n (enclosure n).1, shrink n (enclosure n).2)

private theorem integral_bounds (n : ℕ) {l u x : ℝ} (hx : x ∈ Icc 0 1)
    (hb : ∀ y ∈ Icc (0:ℝ) 1, profile n y ∈ Icc l u) :
    x * l ≤ ∫ y in (0:ℝ)..x, profile n y ∧ (∫ y in (0:ℝ)..x, profile n y) ≤ x * u := by
  have hi := (profile_continuous n).intervalIntegrable (μ := volume) 0 x
  constructor
  · have h := intervalIntegral.integral_mono_on hx.1 (intervalIntegrable_const) hi
      (fun y hy => (hb y ⟨hy.1, hy.2.trans hx.2⟩).1)
    simpa using h
  · have h := intervalIntegral.integral_mono_on hx.1 hi (intervalIntegrable_const)
      (fun y hy => (hb y ⟨hy.1, hy.2.trans hx.2⟩).2)
    simpa using h

/-- Uniform enclosures on each closed cell, including both junctions. -/
theorem profile_mem_enclosure (n : ℕ) : ∀ x ∈ Icc (0:ℝ) 1,
    profile n x ∈ Icc (enclosure n).1 (enclosure n).2 := by
  induction n with
  | zero =>
    intro x hx
    simp only [Set.mem_Icc, enclosure, profile, intervalMass, Nat.cast_zero, zero_add, max_eq_left hx.1]
    have hd : 0 < 1+x := by linarith [hx.1]
    constructor
    · rw [le_div_iff₀ hd]
      linarith [hx.2]
    · rw [div_le_iff₀ hd]
      linarith [hx.1]
  | succ n ih =>
    intro x hx
    have he := ih 1 ⟨zero_le_one, le_rfl⟩
    obtain ⟨hl,hu⟩ := integral_bounds n hx ih
    let e := profile n 1
    let c : ℝ := (n:ℝ)+2
    have hc : 0 < c := by dsimp [c]; positivity
    have hd : 0 < c+x := by linarith [hx.1]
    have hratio : x / (c+x) ≤ 1 / (c+1) := by
      rw [div_le_div_iff₀ hd (by linarith)]
      nlinarith only [mul_nonneg hc.le (sub_nonneg.mpr hx.2)]
    rw [profile_succ_mean n hx.1]
    change e + ((enclosure n).1-e)/((n:ℝ)+3) ≤
        (c*e + (∫ y in (0:ℝ)..x, profile n y))/(c+x) ∧
      (c*e + (∫ y in (0:ℝ)..x, profile n y))/(c+x) ≤ e + ((enclosure n).2-e)/((n:ℝ)+3)
    rw [show (n:ℝ)+3 = c+1 by dsimp [c]; ring]
    have splitMean (v : ℝ) : (c*e+x*v)/(c+x) = e+(v-e)*(x/(c+x)) := by
      field_simp [hd.ne']
      ring
    constructor
    · calc
        _ ≤ e + ((enclosure n).1-e)*(x/(c+x)) := by
          have h := mul_le_mul_of_nonpos_left hratio (sub_nonpos.mpr he.1)
          simpa only [div_eq_mul_inv, one_mul] using add_le_add_right h e
        _ = _ := (splitMean _).symm
        _ ≤ _ := div_le_div_of_nonneg_right (add_le_add_right hl _) hd.le
    · calc
        _ ≤ (c*e+x*(enclosure n).2)/(c+x) :=
          div_le_div_of_nonneg_right (add_le_add_right hu _) hd.le
        _ = _ := splitMean _
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr he.2)
          simpa only [div_eq_mul_inv, one_mul] using add_le_add_right h e

/-- The width is exactly reciprocal factorial, independently of the intervening endpoints. -/
theorem enclosure_width (n : ℕ) :
    (enclosure n).2 - (enclosure n).1 = 1 / ((n+2).factorial : ℝ) := by
  induction n with
  | zero => norm_num [enclosure, Nat.factorial]
  | succ n ih =>
    change shrink n (enclosure n).2 - shrink n (enclosure n).1 = _
    unfold shrink
    have hfac : (((n+1+2).factorial : ℕ) : ℝ) =
        ((n:ℝ)+3) * ((n+2).factorial : ℝ) := by
      change (((n+2).succ.factorial : ℕ) : ℝ) = _
      rw [Nat.factorial_succ, Nat.cast_mul]
      push_cast
      ring
    rw [show profile n 1 + ((enclosure n).2-profile n 1)/((n:ℝ)+3) -
        (profile n 1 + ((enclosure n).1-profile n 1)/((n:ℝ)+3)) =
        ((enclosure n).2 - (enclosure n).1)/((n:ℝ)+3) by ring, ih, div_div, hfac, mul_comm]

/-- The enclosure contracts by inclusion, so the factorial error also controls
profiles on every later interval. -/
theorem enclosure_nested (n : ℕ) :
    Icc (enclosure (n+1)).1 (enclosure (n+1)).2 ⊆
      Icc (enclosure n).1 (enclosure n).2 := by
  have he := profile_mem_enclosure n 1 ⟨zero_le_one, le_rfl⟩
  have hd : (1:ℝ) ≤ (n:ℝ)+3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (0:ℝ) < (n:ℝ)+3 := by positivity
  apply Icc_subset_Icc
  · change _ ≤ profile n 1 + ((enclosure n).1-profile n 1)/((n:ℝ)+3)
    have h : (enclosure n).1-profile n 1 ≤ ((enclosure n).1-profile n 1)/((n:ℝ)+3) := by
      apply (le_div_iff₀ hp).mpr
      nlinarith only [mul_nonneg (sub_nonneg.mpr he.1) (sub_nonneg.mpr hd)]
    linarith only [h]
  · change profile n 1 + ((enclosure n).2-profile n 1)/((n:ℝ)+3) ≤ _
    have h : ((enclosure n).2-profile n 1)/((n:ℝ)+3) ≤ (enclosure n).2-profile n 1 := by
      apply (div_le_iff₀ hp).mpr
      nlinarith only [mul_nonneg (sub_nonneg.mpr he.2) (sub_nonneg.mpr hd)]
    linarith only [h]

/-- Arbitrarily far apart cells beyond the same cutoff differ by at most its factorial width. -/
theorem profile_tail_difference (n a b : ℕ) (x y : Icc (0:ℝ) 1) :
    |profile (n+a) x - profile (n+b) y| ≤ 1 / ((n+2).factorial : ℝ) := by
  have nest (k : ℕ) : Icc (enclosure (n+k)).1 (enclosure (n+k)).2 ⊆
      Icc (enclosure n).1 (enclosure n).2 := by
    induction k with
    | zero => exact Subset.rfl
    | succ k ih => exact (enclosure_nested (n+k)).trans ih
  have hx := nest a (profile_mem_enclosure _ x x.property)
  have hy := nest b (profile_mem_enclosure _ y y.property)
  rw [← enclosure_width n, abs_le]
  constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]

private theorem enclosure_ordered (n : ℕ) : (enclosure n).1 ≤ (enclosure n).2 :=
  let h := profile_mem_enclosure n 1 ⟨zero_le_one, le_rfl⟩
  h.1.trans h.2

private theorem enclosure_monotonicity :
    Monotone (fun n => (enclosure n).1) ∧ Antitone (fun n => (enclosure n).2) := by
  have h (n : ℕ) := (Icc_subset_Icc_iff (enclosure_ordered (n+1))).mp (enclosure_nested n)
  exact ⟨monotone_nat_of_le_succ (fun n => (h n).1), antitone_nat_of_succ_le (fun n => (h n).2)⟩

/-- The common limit of the shrinking real intervals. -/
def enclosureLimit : ℝ := sSup (Set.range (fun n => (enclosure n).1))

theorem enclosureLimit_mem (n : ℕ) :
    enclosureLimit ∈ Icc (enclosure n).1 (enclosure n).2 := by
  obtain ⟨hl,hu⟩ := enclosure_monotonicity
  have hcross (i j : ℕ) : (enclosure i).1 ≤ (enclosure j).2 := by
    rcases le_total i j with h | h
    · exact (hl h).trans (enclosure_ordered j)
    · exact (enclosure_ordered i).trans (hu h)
  exact ⟨le_csSup ⟨(enclosure 0).2, fun _ ⟨i,hi⟩ => hi ▸ hcross i 0⟩ ⟨n,rfl⟩,
    csSup_le (Set.range_nonempty _) (fun _ ⟨i,hi⟩ => hi ▸ hcross i n)⟩

/-- Certified uniform factorial error throughout each cell. -/
theorem profile_limit_error (n : ℕ) (x : Icc (0:ℝ) 1) :
    |profile n x - enclosureLimit| ≤ 1 / ((n+2).factorial : ℝ) := by
  have hx := profile_mem_enclosure n x x.property
  have hl := enclosureLimit_mem n
  rw [← enclosure_width n, abs_le]
  constructor <;> linarith only [hx.1, hx.2, hl.1, hl.2]

/-- Sampling anywhere in each cell gives the same real limit. -/
theorem tendsto_profile_samples (x : ℕ → Icc (0:ℝ) 1) :
    Tendsto (fun n => profile n (x n)) atTop (𝓝 enclosureLimit) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfac : Tendsto (fun n : ℕ => ((n+2).factorial : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 2))
  have hnull : Tendsto (fun n : ℕ => 1 / ((n+2).factorial : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp hfac)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hnull
  simpa only [Real.norm_eq_abs] using profile_limit_error n (x n)

#print axioms tendsto_profile_samples
#print axioms profile_tail_difference

end
end RHTower.Sieve.Buchstab
