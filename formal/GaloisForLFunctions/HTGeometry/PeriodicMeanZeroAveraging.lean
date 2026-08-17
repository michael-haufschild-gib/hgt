import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Averaging a mean-zero oscillation against a slowly varying weight

A bounded oscillation with zero mean over one period cancels against any weight that is nearly
constant on that period.  Subtracting the value at the left endpoint costs nothing, because the
oscillation integrates to zero, and what remains is bounded by the total variation of the weight:

`|∫ over one period of ψ·S| ≤ M · T · ∫ over the period of |ψ'|`.

No primitive of the oscillation is needed, so the estimate applies verbatim to a square wave, whose
primitive is only Lipschitz.  Summing over consecutive periods gives the same bound on any union of
periods, with the constant unchanged: the total variation is additive.

This is the exact mechanism behind the regular-clock no-go — a phase whose inverse speed becomes
uniformly small and of small variation averages the parity square wave to its mean.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The weight varies by at most its total variation on the period. -/
theorem abs_sub_le_integral_abs_deriv {ψ ψ' : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hy : y ∈ Set.Icc a b)
    (hψ : ∀ x ∈ Set.uIcc a b, HasDerivAt ψ (ψ' x) x)
    (hψ'int : IntervalIntegrable ψ' volume a b) :
    |ψ y - ψ a| ≤ ∫ u in a..b, |ψ' u| := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hay : a ≤ y := hy.1
  have hyb : y ≤ b := hy.2
  have hsub : Set.uIcc a y ⊆ Set.uIcc a b := by
    rw [huIcc, Set.uIcc_of_le hay]
    exact Set.Icc_subset_Icc le_rfl hyb
  have hFTC : ∫ u in a..y, ψ' u = ψ y - ψ a :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hψ x (hsub hx))
      (hψ'int.mono_set hsub)
  rw [← hFTC]
  calc |∫ u in a..y, ψ' u| ≤ ∫ u in a..y, |ψ' u| :=
        abs_integral_le_integral_abs hay
    _ ≤ ∫ u in a..b, |ψ' u| := by
        refine integral_mono_interval le_rfl hay hyb ?_ (hψ'int.abs)
        filter_upwards with u using abs_nonneg _

/-- **One period of a mean-zero oscillation.**  The zero mean removes the constant part of the
weight, and what is left is bounded by the period times the bound times the total variation. -/
theorem abs_integral_mul_meanZero_le
    {S ψ ψ' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hSmean : ∫ y in a..b, S y = 0)
    (hSbound : ∀ y, |S y| ≤ M)
    (hSint : IntervalIntegrable S volume a b)
    (hψ : ∀ x ∈ Set.uIcc a b, HasDerivAt ψ (ψ' x) x)
    (hψ'int : IntervalIntegrable ψ' volume a b) :
    |∫ y in a..b, ψ y * S y| ≤ M * (b - a) * ∫ u in a..b, |ψ' u| := by
  set V : ℝ := ∫ u in a..b, |ψ' u| with hV
  have hV0 : 0 ≤ V := by
    rw [hV]
    refine intervalIntegral.integral_nonneg hab fun u _ => abs_nonneg _
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (S a)) (hSbound a)
  have hψcont : ContinuousOn ψ (Set.uIcc a b) := fun x hx =>
    ((hψ x hx).continuousAt).continuousWithinAt
  have hψint : IntervalIntegrable ψ volume a b := hψcont.intervalIntegrable
  have hprodint : IntervalIntegrable (fun y => ψ y * S y) volume a b := by
    have h := hSint.mul_continuousOn hψcont
    exact h.congr (fun y _ => mul_comm (S y) (ψ y))
  have hconstint : IntervalIntegrable (fun y => ψ a * S y) volume a b := hSint.const_mul _
  have hshift : ∫ y in a..b, ψ y * S y = ∫ y in a..b, (ψ y - ψ a) * S y := by
    have hsub : ∫ y in a..b, ((ψ y * S y) - (ψ a * S y))
        = (∫ y in a..b, ψ y * S y) - ∫ y in a..b, ψ a * S y :=
      intervalIntegral.integral_sub hprodint hconstint
    have hzero : ∫ y in a..b, ψ a * S y = 0 := by
      rw [intervalIntegral.integral_const_mul, hSmean, mul_zero]
    have hcongr : ∫ y in a..b, (ψ y - ψ a) * S y
        = ∫ y in a..b, ((ψ y * S y) - (ψ a * S y)) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      ring
    rw [hcongr, hsub, hzero, sub_zero]
  have hpoint : ∀ y ∈ Set.Icc a b, |(ψ y - ψ a) * S y| ≤ V * M := by
    intro y hy
    rw [abs_mul]
    exact mul_le_mul (abs_sub_le_integral_abs_deriv hab hy hψ hψ'int) (hSbound y)
      (abs_nonneg _) hV0
  have hbound : |∫ y in a..b, (ψ y - ψ a) * S y| ≤ V * M * (b - a) := by
    have hconst : ∀ y ∈ Set.uIoc a b, ‖(ψ y - ψ a) * S y‖ ≤ V * M := by
      intro y hy
      rw [Real.norm_eq_abs]
      refine hpoint y ?_
      rw [Set.uIoc_of_le hab] at hy
      exact ⟨le_of_lt hy.1, hy.2⟩
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hconst
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
    exact h
  rw [hshift]
  calc |∫ y in a..b, (ψ y - ψ a) * S y| ≤ V * M * (b - a) := hbound
    _ = M * (b - a) * V := by ring

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory intervalIntegral

/-- **The averaging bound is additive over a mean-zero partition.**  Summing the one-period bound
over consecutive cells keeps the same constant, because the total variation is additive. -/
theorem abs_integral_mul_meanZero_partition_le
    {S ψ ψ' : ℝ → ℝ} {M T : ℝ} (x : ℕ → ℝ) (n : ℕ)
    (hmono : Monotone x)
    (hlen : ∀ k, x (k + 1) - x k ≤ T)
    (hmean : ∀ k, ∫ y in (x k)..(x (k + 1)), S y = 0)
    (hSbound : ∀ y, |S y| ≤ M)
    (hSint : ∀ u v : ℝ, IntervalIntegrable S volume u v)
    (hψ : ∀ z, HasDerivAt ψ (ψ' z) z)
    (hψ'int : ∀ u v : ℝ, IntervalIntegrable ψ' volume u v) :
    |∫ y in (x 0)..(x n), ψ y * S y| ≤ M * T * ∫ u in (x 0)..(x n), |ψ' u| := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (S 0)) (hSbound 0)
  have hprodint : ∀ u v : ℝ, IntervalIntegrable (fun y => ψ y * S y) volume u v := by
    intro u v
    have hcont : ContinuousOn ψ (Set.uIcc u v) := fun z _ =>
      ((hψ z).continuousAt).continuousWithinAt
    exact ((hSint u v).mul_continuousOn hcont).congr (fun y _ => mul_comm (S y) (ψ y))
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hle1 : x 0 ≤ x n := hmono (Nat.zero_le n)
      have hle2 : x n ≤ x (n + 1) := hmono (Nat.le_succ n)
      have hsplit : (∫ y in (x 0)..(x n), ψ y * S y)
          + (∫ y in (x n)..(x (n + 1)), ψ y * S y)
          = ∫ y in (x 0)..(x (n + 1)), ψ y * S y :=
        intervalIntegral.integral_add_adjacent_intervals (hprodint _ _) (hprodint _ _)
      have hVsplit : (∫ u in (x 0)..(x n), |ψ' u|)
          + (∫ u in (x n)..(x (n + 1)), |ψ' u|)
          = ∫ u in (x 0)..(x (n + 1)), |ψ' u| :=
        intervalIntegral.integral_add_adjacent_intervals
          ((hψ'int _ _).abs) ((hψ'int _ _).abs)
      have hcell : |∫ y in (x n)..(x (n + 1)), ψ y * S y|
          ≤ M * (x (n + 1) - x n) * ∫ u in (x n)..(x (n + 1)), |ψ' u| :=
        abs_integral_mul_meanZero_le hle2 (hmean n) hSbound (hSint _ _)
          (fun z _ => hψ z) (hψ'int _ _)
      have hVcell : 0 ≤ ∫ u in (x n)..(x (n + 1)), |ψ' u| :=
        intervalIntegral.integral_nonneg hle2 fun u _ => abs_nonneg _
      have hcell' : |∫ y in (x n)..(x (n + 1)), ψ y * S y|
          ≤ M * T * ∫ u in (x n)..(x (n + 1)), |ψ' u| := by
        refine le_trans hcell ?_
        have : M * (x (n + 1) - x n) ≤ M * T := by
          exact mul_le_mul_of_nonneg_left (hlen n) hM0
        exact mul_le_mul_of_nonneg_right this hVcell
      calc |∫ y in (x 0)..(x (n + 1)), ψ y * S y|
          = |(∫ y in (x 0)..(x n), ψ y * S y) + ∫ y in (x n)..(x (n + 1)), ψ y * S y| := by
            rw [hsplit]
        _ ≤ |∫ y in (x 0)..(x n), ψ y * S y| + |∫ y in (x n)..(x (n + 1)), ψ y * S y| :=
            abs_add_le _ _
        _ ≤ M * T * (∫ u in (x 0)..(x n), |ψ' u|)
              + M * T * ∫ u in (x n)..(x (n + 1)), |ψ' u| := add_le_add ih hcell'
        _ = M * T * ∫ u in (x 0)..(x (n + 1)), |ψ' u| := by
            rw [← hVsplit]; ring

end GaloisForLFunctions.HTGeometry
