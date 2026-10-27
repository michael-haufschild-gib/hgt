import GaloisForLFunctions.HTGeometry.QuadraticAscentReachesALocalMaximum
import GaloisForLFunctions.HTGeometry.LogarithmicWindowsAreQuadraticallySparse
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Quadratic terminal zeros of the Xi divisor

Quadratic ascent confines a terminal zero near each Xi zero. The terminal
zero has an empty open quadratic ascent cone.
-/

open Finset Set RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Cover an ordinate window by unit windows and retain the linear dependence
on its radius, including multiplicities. -/
theorem xi_window_card_le_log (R t : ℝ) :
    (((finite_xiOrdinateWindow R t).toFinset.card : ℕ) : ℝ) ≤
      (2 * (⌈R⌉₊ : ℝ) + 1) *
        (16 * (xiLineTwoLogDerivConstant + Real.log (|t| + (⌈R⌉₊ : ℝ) + 4))) := by
  classical
  let M : ℕ := ⌈R⌉₊
  let F : Finset XiZeroCopy := (finite_xiOrdinateWindow R t).toFinset
  let centers : Finset ℕ := range (2 * M + 1)
  let center : ℕ → ℝ := fun k => t - (M : ℝ) + (k : ℝ)
  let windows : ℕ → Finset XiZeroCopy := fun k =>
    (finite_xiOrdinateWindow 1 (center k)).toFinset
  have hRM : R ≤ (M : ℝ) := Nat.le_ceil R
  have hcover : F ⊆ centers.biUnion windows := by
    intro q hq
    have hqt : |(q.1 : ℂ).im - t| ≤ R := by
      have hq' : q ∈ xiOrdinateWindow R t :=
        (Set.Finite.mem_toFinset (finite_xiOrdinateWindow R t)).mp hq
      exact mem_xiOrdinateWindow_iff.mp hq'
    let x : ℝ := (q.1 : ℂ).im - t + (M : ℝ)
    let k : ℕ := ⌊x⌋₊
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      linarith [(abs_le.mp hqt).1]
    have hxM : x ≤ (2 * M : ℕ) := by
      dsimp only [x]
      push_cast
      linarith [(abs_le.mp hqt).2]
    have hkx : (k : ℝ) ≤ x := Nat.floor_le hx0
    have hxk : x < (k : ℝ) + 1 := Nat.lt_floor_add_one x
    have hkM : k ≤ 2 * M := by
      exact_mod_cast hkx.trans hxM
    have hkcenter : k ∈ centers := by
      dsimp only [centers]
      exact mem_range.mpr (by omega)
    refine mem_biUnion.mpr ⟨k, hkcenter, ?_⟩
    apply (Set.Finite.mem_toFinset (finite_xiOrdinateWindow 1 (center k))).mpr
    apply mem_xiOrdinateWindow_iff.mpr
    rw [abs_le]
    dsimp only [center, x] at *
    constructor <;> linarith
  have hcountNat : F.card ≤ ∑ k ∈ centers, (windows k).card :=
    (Finset.card_le_card hcover).trans card_biUnion_le
  have hcount : (F.card : ℝ) ≤ ∑ k ∈ centers, ((windows k).card : ℝ) := by
    exact_mod_cast hcountNat
  have hbound : ∀ k ∈ centers, ((windows k).card : ℝ) ≤
      16 * (xiLineTwoLogDerivConstant + Real.log (|t| + (M : ℝ) + 4)) := by
    intro k hk
    have hkM : (k : ℝ) ≤ 2 * (M : ℝ) := by
      have hkn : k ≤ 2 * M := by
        dsimp only [centers] at hk
        have := mem_range.mp hk
        omega
      exact_mod_cast hkn
    have hcenter : |center k| ≤ |t| + (M : ℝ) := by
      have hkm : |(k : ℝ) - (M : ℝ)| ≤ (M : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k,
          Nat.cast_nonneg (α := ℝ) M]
      have htbound := abs_le.mp (le_refl |t|)
      have hkbound := abs_le.mp hkm
      dsimp only [center]
      rw [abs_le]
      constructor <;> linarith [htbound.1, htbound.2, hkbound.1, hkbound.2]
    have hlog : Real.log (|center k| + 4) ≤ Real.log (|t| + (M : ℝ) + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hcard := ncard_xiOrdinateWindow_one_le_log (center k)
    rw [Set.ncard_eq_toFinset_card (xiOrdinateWindow 1 (center k))
      (finite_xiOrdinateWindow 1 (center k))] at hcard
    dsimp only [windows]
    linarith
  calc
    (F.card : ℝ) ≤ ∑ k ∈ centers, ((windows k).card : ℝ) := hcount
    _ ≤ ∑ _k ∈ centers,
        16 * (xiLineTwoLogDerivConstant + Real.log (|t| + (M : ℝ) + 4)) :=
      sum_le_sum hbound
    _ = (2 * (M : ℝ) + 1) *
        (16 * (xiLineTwoLogDerivConstant + Real.log (|t| + (M : ℝ) + 4))) := by
      dsimp only [centers]
      simp only [sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring

/-- The horizontal distance of a Xi zero from the critical line. -/
def xiZeroDepth (q : XiZeroCopy) : ℝ := |(q.1 : ℂ).re - 1 / 2|

/-- The signed ordinate of a Xi zero. -/
def xiZeroHeight (q : XiZeroCopy) : ℝ := (q.1 : ℂ).im

/-- Every Xi zero has depth at most one half. -/
theorem xiZeroDepth_bounds (q : XiZeroCopy) : 0 ≤ xiZeroDepth q ∧ xiZeroDepth q ≤ 1 / 2 := by
  refine ⟨abs_nonneg _, ?_⟩
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  rw [xiZeroDepth, abs_le]
  constructor <;> linarith

/-- Every Xi zero reaches a terminal depth in a logarithmic ordinate window.
At the terminal point no zero lies in its open quadratic ascent cone. -/
theorem exists_xi_quadratic_terminal_near :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XiZeroCopy, ∃ p : XiZeroCopy,
      |xiZeroHeight p - xiZeroHeight q| ≤ C * Real.log (|xiZeroHeight q| + 3) ∧
      xiZeroDepth q ≤ xiZeroDepth p ∧
      ∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
        xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2 := by
  classical
  obtain ⟨C, hC, hR⟩ :=
    GaloisForLFunctions.HTGeometry.exists_logarithmic_quadratic_window
      |xiLineTwoLogDerivConstant| (abs_nonneg _)
  refine ⟨C, hC, fun q => ?_⟩
  obtain ⟨R, hR0, hRbound, hbudget⟩ := hR (xiZeroHeight q)
  let F : Finset XiZeroCopy := (finite_xiOrdinateWindow R (xiZeroHeight q)).toFinset
  have hcard := xi_window_card_le_log R (xiZeroHeight q)
  have hinner :
      xiLineTwoLogDerivConstant + Real.log (|xiZeroHeight q| + (⌈R⌉₊ : ℝ) + 4) ≤
        |xiLineTwoLogDerivConstant| + Real.log (|xiZeroHeight q| + (⌈R⌉₊ : ℝ) + 4) := by
    linarith [le_abs_self xiLineTwoLogDerivConstant]
  have hcomparison :
      (2 * (⌈R⌉₊ : ℝ) + 1) *
          (16 * (xiLineTwoLogDerivConstant +
            Real.log (|xiZeroHeight q| + (⌈R⌉₊ : ℝ) + 4))) ≤
        (2 * (⌈R⌉₊ : ℝ) + 1) *
          (16 * (|xiLineTwoLogDerivConstant| +
            Real.log (|xiZeroHeight q| + (⌈R⌉₊ : ℝ) + 4))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinner (by norm_num)) (by positivity)
  have hcard' : (F.card : ℝ) ≤
      (2 * (⌈R⌉₊ : ℝ) + 1) *
        (16 * (xiLineTwoLogDerivConstant +
          Real.log (|xiZeroHeight q| + (⌈R⌉₊ : ℝ) + 4))) := by
    simpa only [F] using hcard
  have hFbound : (F.card : ℝ) ≤
      (2 * (⌈R⌉₊ : ℝ) + 1) *
        (16 * (|xiLineTwoLogDerivConstant| +
          Real.log (|xiZeroHeight q| + (⌈R⌉₊ : ℝ) + 4))) :=
    hcard'.trans hcomparison
  have hFbudget : (F.card : ℝ) * (1 / 2) ^ 2 < R ^ 2 :=
    (mul_le_mul_of_nonneg_right hFbound (by positivity)).trans_lt hbudget
  have hwindow : ∀ p : XiZeroCopy,
      |xiZeroHeight p - xiZeroHeight q| ≤ R → p ∈ F := by
    intro p hp
    apply (Set.Finite.mem_toFinset (finite_xiOrdinateWindow R (xiZeroHeight q))).mpr
    exact mem_xiOrdinateWindow_iff.mpr hp
  obtain ⟨p, hpnear, hpdepth, hpterminal⟩ :=
    GaloisForLFunctions.HTGeometry.exists_quadratic_ascent_terminal
      xiZeroDepth xiZeroHeight q F (by norm_num) hR0 xiZeroDepth_bounds hwindow hFbudget
  exact ⟨p, hpnear.trans hRbound, hpdepth, hpterminal⟩

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
