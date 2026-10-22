import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A smooth compact exhaustion whose topological support stays strictly in the physical half-plane. -/

open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMJointSource
noncomputable section

/-- Two-sided smooth compact window with plateau `[-n,n]`. -/
def compactWindow (n : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (x + n + 1) * (1 - Real.smoothTransition (x - n))

/-- Joint cutoff for a time/radius event. Its shifted final transition places its closed support
below `-1/(n+1)`, rather than merely forcing pointwise vanishing at the physical boundary. -/
def physicalWindow (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  compactWindow n p.1 * compactWindow n p.2 *
    Real.smoothTransition (-((n + 1 : ℕ) : ℝ) * p.2 - 1)

def physicalBoundary (n : ℕ) : ℝ := -(((n + 1 : ℕ) : ℝ)⁻¹)

theorem compactWindow_smooth (n : ℕ) : ContDiff ℝ ∞ (compactWindow n) := by
  unfold compactWindow
  fun_prop

theorem compactWindow_eq_one (n : ℕ) {x : ℝ} (hx : |x| ≤ n) : compactWindow n x = 1 := by
  have hleft : 1 ≤ x + n + 1 := by
    rw [abs_le] at hx
    linarith
  have hright : x - n ≤ 0 := by
    rw [abs_le] at hx
    linarith
  unfold compactWindow
  rw [Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.zero_of_nonpos hright]
  ring

theorem compactWindow_nonneg (n : ℕ) (x : ℝ) : 0 ≤ compactWindow n x := by
  unfold compactWindow
  exact mul_nonneg (Real.smoothTransition.nonneg _)
    (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem compactWindow_le_one (n : ℕ) (x : ℝ) : compactWindow n x ≤ 1 := by
  unfold compactWindow
  calc
    Real.smoothTransition (x + n + 1) * (1 - Real.smoothTransition (x - n)) ≤
        1 * (1 - Real.smoothTransition (x - n)) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (sub_nonneg.mpr (Real.smoothTransition.le_one _))
    _ = 1 - Real.smoothTransition (x - n) := by ring
    _ ≤ 1 := sub_le_self _ (Real.smoothTransition.nonneg _)

theorem compactWindow_zero_of_outside (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (-(n : ℝ) - 1) ((n : ℝ) + 1)) : compactWindow n x = 0 := by
  by_cases hleft : x < -(n : ℝ) - 1
  · have harg : x + n + 1 ≤ 0 := by linarith
    unfold compactWindow
    rw [Real.smoothTransition.zero_of_nonpos harg]
    ring
  · have hleft' : -(n : ℝ) - 1 ≤ x := le_of_not_gt hleft
    have hright : ¬ x ≤ (n : ℝ) + 1 := fun h => hx ⟨hleft', h⟩
    have harg : 1 ≤ x - n := by linarith [lt_of_not_ge hright]
    unfold compactWindow
    rw [Real.smoothTransition.one_of_one_le harg]
    ring

theorem compactWindow_hasCompactSupport (n : ℕ) : HasCompactSupport (compactWindow n) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => compactWindow_zero_of_outside n hx)

theorem physicalWindow_smooth (n : ℕ) : ContDiff ℝ ∞ (physicalWindow n) := by
  unfold physicalWindow
  have hfst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => compactWindow n p.1) :=
    (compactWindow_smooth n).comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ))
  have hsnd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => compactWindow n p.2) :=
    (compactWindow_smooth n).comp (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ))
  exact (hfst.mul hsnd).mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ))).sub contDiff_const))

theorem physicalWindow_nonneg (n : ℕ) (p : ℝ × ℝ) : 0 ≤ physicalWindow n p := by
  unfold physicalWindow
  exact mul_nonneg (mul_nonneg (compactWindow_nonneg n p.1) (compactWindow_nonneg n p.2))
    (Real.smoothTransition.nonneg _)

theorem physicalWindow_le_one (n : ℕ) (p : ℝ × ℝ) : physicalWindow n p ≤ 1 := by
  unfold physicalWindow
  have h12 : compactWindow n p.1 * compactWindow n p.2 ≤ 1 := by
    calc
      compactWindow n p.1 * compactWindow n p.2 ≤ 1 * compactWindow n p.2 :=
        mul_le_mul_of_nonneg_right (compactWindow_le_one n p.1) (compactWindow_nonneg n p.2)
      _ = compactWindow n p.2 := by ring
      _ ≤ 1 := compactWindow_le_one n p.2
  calc
    compactWindow n p.1 * compactWindow n p.2 *
        Real.smoothTransition (-((n + 1 : ℕ) : ℝ) * p.2 - 1) ≤
        1 * Real.smoothTransition (-((n + 1 : ℕ) : ℝ) * p.2 - 1) :=
      mul_le_mul_of_nonneg_right h12 (Real.smoothTransition.nonneg _)
    _ = Real.smoothTransition (-((n + 1 : ℕ) : ℝ) * p.2 - 1) := by ring
    _ ≤ 1 := Real.smoothTransition.le_one _

theorem physicalWindow_hasCompactSupport (n : ℕ) : HasCompactSupport (physicalWindow n) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc)
  intro p hp
  by_cases hp1 : p.1 ∈ Icc (-(n : ℝ) - 1) ((n : ℝ) + 1)
  · have hp2 : p.2 ∉ Icc (-(n : ℝ) - 1) ((n : ℝ) + 1) := fun h => hp ⟨hp1, h⟩
    unfold physicalWindow
    rw [compactWindow_zero_of_outside n hp2]
    ring
  · unfold physicalWindow
    rw [compactWindow_zero_of_outside n hp1]
    ring

theorem physicalWindow_zero_above_boundary (n : ℕ) (p : ℝ × ℝ)
    (hp : physicalBoundary n < p.2) : physicalWindow n p = 0 := by
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul : ((n + 1 : ℕ) : ℝ) * physicalBoundary n <
      ((n + 1 : ℕ) : ℝ) * p.2 := mul_lt_mul_of_pos_left hp hn
  have hcancel : ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hn.ne'
  have hprod : -1 < ((n + 1 : ℕ) : ℝ) * p.2 := by
    rw [physicalBoundary, mul_neg, hcancel] at hmul
    exact hmul
  have harg : -((n + 1 : ℕ) : ℝ) * p.2 - 1 ≤ 0 := by linarith
  unfold physicalWindow
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

/-- The physical cutoff has closed support strictly below the radial boundary. -/
theorem physicalWindow_tsupport_subset_physical (n : ℕ) :
    tsupport (physicalWindow n) ⊆ {p : ℝ × ℝ | p.2 < 0} := by
  let S : Set (ℝ × ℝ) := {p | p.2 ≤ physicalBoundary n}
  have hsupp : Function.support (physicalWindow n) ⊆ S := by
    intro p hp
    by_contra hbound
    have hgt : physicalBoundary n < p.2 := lt_of_not_ge hbound
    exact hp (physicalWindow_zero_above_boundary n p hgt)
  have hclosed : IsClosed S := isClosed_le continuous_snd continuous_const
  intro p hp
  have hbound : p ∈ S := closure_minimal hsupp hclosed hp
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  exact lt_of_le_of_lt hbound (neg_lt_zero.mpr (inv_pos.mpr hn))

/-- Every physical event is eventually in the unit plateau. -/
theorem physicalWindow_eventually_eq_one (p : ℝ × ℝ) (hp : p.2 < 0) :
    ∀ᶠ n in atTop, physicalWindow n p = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (max |p.1| |p.2|) (2 / (-p.2)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : max (max |p.1| |p.2|) (2 / (-p.2)) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hn)
  have h1 : |p.1| ≤ (n : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn'.le
  have h2 : |p.2| ≤ (n : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn'.le
  have hrate : 2 / (-p.2) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn'
  have hpos : 0 < -p.2 := neg_pos.mpr hp
  have hprod : 2 < (n : ℝ) * (-p.2) := (div_lt_iff₀ hpos).mp hrate
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  have htime : 1 ≤ -((n + 1 : ℕ) : ℝ) * p.2 - 1 := by
    rw [hcast]
    nlinarith
  unfold physicalWindow
  rw [compactWindow_eq_one n h1, compactWindow_eq_one n h2,
    Real.smoothTransition.one_of_one_le htime]
  ring

end
end RHTower.D4BMJointSource
