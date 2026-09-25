import GaloisForLFunctions.RHTower.MobiusLaplaceLandauOscillation

/-!
# Unbounded two-sided scale slopes of the literal Möbius–Laplace source

The positive-scale source `Φ(x) = ∑ μ(n) exp(-nx)` has unconditional
two-sided subcritical Landau excursions. Multiplying by the physical
scale does not make it a monotone or locally Lipschitz one-sided current:
on every neighborhood of zero, its secants have arbitrarily large slopes
of both signs. This rules out pointwise slope-sign or bounded-curvature
payment laws for this Route-E source; it does not bound joint signed
covariance or prove RH.
-/

open Complex

namespace RHTower

/-- The real physical-scale Möbius–Laplace current. -/
noncomputable def mobiusScaleCurrent (x : ℝ) : ℝ :=
  x * (mobiusDiscreteLaplaceTransform x).re

private theorem scaleCurrent_pos_of_transform_pos
    {x : ℝ} (hx : 0 < x) (hF : 0 < (mobiusDiscreteLaplaceTransform x).re) :
    0 < mobiusScaleCurrent x := by
  exact mul_pos hx hF

private theorem scaleCurrent_neg_of_transform_neg
    {x : ℝ} (hx : 0 < x) (hF : (mobiusDiscreteLaplaceTransform x).re < 0) :
    mobiusScaleCurrent x < 0 := by
  exact mul_neg_of_pos_of_neg hx hF

private theorem exists_scaleCurrent_increasing_secant
    (B δ : ℝ) (hδ : 0 < δ) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < δ ∧
      B * (b - a) < mobiusScaleCurrent b - mobiusScaleCurrent a := by
  let A := |B| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hmin : 0 < min δ 1 := lt_min hδ zero_lt_one
  obtain ⟨b, hb0, hbmin, hbF⟩ :=
    exists_mobiusDiscreteLaplaceTransform_re_gt_subcritical
      (epsilon := 1 / 4) (A := A) (delta := min δ 1)
      (by norm_num) (by norm_num) hmin
  obtain ⟨a, ha0, hab, haF⟩ :=
    exists_mobiusDiscreteLaplaceTransform_re_lt_neg_subcritical
      (epsilon := 1 / 4) (A := 1) (delta := b)
      (by norm_num) (by norm_num) hb0
  have hbδ : b < δ := hbmin.trans_le (min_le_left _ _)
  have hb1 : b ≤ 1 := hbmin.le.trans (min_le_right _ _)
  have hpow : 1 ≤ b ^ (-(1 / 2 - (1 / 4 : ℝ)) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb0 hb1 (by norm_num)
  have hFb : A < (mobiusDiscreteLaplaceTransform b).re :=
    lt_of_le_of_lt (le_mul_of_one_le_right hA.le hpow) hbF
  have hFa : (mobiusDiscreteLaplaceTransform a).re < 0 := by
    have hp : 0 < a ^ (-(1 / 2 - (1 / 4 : ℝ)) : ℝ) :=
      Real.rpow_pos_of_pos ha0 _
    nlinarith
  have hHa : mobiusScaleCurrent a < 0 :=
    scaleCurrent_neg_of_transform_neg ha0 hFa
  have hHb : A * b < mobiusScaleCurrent b := by
    dsimp [mobiusScaleCurrent]
    calc
      A * b = b * A := mul_comm _ _
      _ < b * (mobiusDiscreteLaplaceTransform b).re :=
        mul_lt_mul_of_pos_left hFb hb0
  refine ⟨a, b, ha0, hab, hbδ, ?_⟩
  have hB : B ≤ |B| := le_abs_self B
  have hBa : B * (b - a) ≤ |B| * b := by
    have hba : 0 < b - a := sub_pos.mpr hab
    have hbdiff : b - a ≤ b := by linarith
    calc
      B * (b - a) ≤ |B| * (b - a) := mul_le_mul_of_nonneg_right hB hba.le
      _ ≤ |B| * b := mul_le_mul_of_nonneg_left hbdiff (abs_nonneg B)
  dsimp [A] at hHb
  nlinarith

private theorem exists_scaleCurrent_decreasing_secant
    (B δ : ℝ) (hδ : 0 < δ) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < δ ∧
      mobiusScaleCurrent b - mobiusScaleCurrent a < -B * (b - a) := by
  let A := |B| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hmin : 0 < min δ 1 := lt_min hδ zero_lt_one
  obtain ⟨b, hb0, hbmin, hbF⟩ :=
    exists_mobiusDiscreteLaplaceTransform_re_lt_neg_subcritical
      (epsilon := 1 / 4) (A := A) (delta := min δ 1)
      (by norm_num) (by norm_num) hmin
  obtain ⟨a, ha0, hab, haF⟩ :=
    exists_mobiusDiscreteLaplaceTransform_re_gt_subcritical
      (epsilon := 1 / 4) (A := 1) (delta := b)
      (by norm_num) (by norm_num) hb0
  have hbδ : b < δ := hbmin.trans_le (min_le_left _ _)
  have hb1 : b ≤ 1 := hbmin.le.trans (min_le_right _ _)
  have hpow : 1 ≤ b ^ (-(1 / 2 - (1 / 4 : ℝ)) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb0 hb1 (by norm_num)
  have hFb : (mobiusDiscreteLaplaceTransform b).re < -A := by
    have hApow : A ≤ A * b ^ (-(1 / 2 - (1 / 4 : ℝ)) : ℝ) :=
      le_mul_of_one_le_right hA.le hpow
    linarith
  have hFa : 0 < (mobiusDiscreteLaplaceTransform a).re := by
    have hp : 0 < a ^ (-(1 / 2 - (1 / 4 : ℝ)) : ℝ) :=
      Real.rpow_pos_of_pos ha0 _
    nlinarith
  have hHa : 0 < mobiusScaleCurrent a :=
    scaleCurrent_pos_of_transform_pos ha0 hFa
  have hHb : mobiusScaleCurrent b < -A * b := by
    dsimp [mobiusScaleCurrent]
    nlinarith [mul_lt_mul_of_pos_left hFb hb0]
  refine ⟨a, b, ha0, hab, hbδ, ?_⟩
  have hB : B ≤ |B| := le_abs_self B
  have hBa : B * (b - a) ≤ |B| * b := by
    have hba : 0 < b - a := sub_pos.mpr hab
    have hbdiff : b - a ≤ b := by linarith
    calc
      B * (b - a) ≤ |B| * (b - a) := mul_le_mul_of_nonneg_right hB hba.le
      _ ≤ |B| * b := mul_le_mul_of_nonneg_left hbdiff (abs_nonneg B)
  dsimp [A] at hHb
  nlinarith

/-- Every neighborhood of zero contains source secants with arbitrarily
large slopes of both signs. No regular pointwise one-sided scale slope
can pay the Route-E Möbius current. -/
theorem mobiusScaleCurrent_twoSidedUnboundedSlopes :
    ∀ B δ : ℝ, 0 < δ →
      (∃ a b : ℝ, 0 < a ∧ a < b ∧ b < δ ∧
        B * (b - a) < mobiusScaleCurrent b - mobiusScaleCurrent a) ∧
      (∃ a b : ℝ, 0 < a ∧ a < b ∧ b < δ ∧
        mobiusScaleCurrent b - mobiusScaleCurrent a < -B * (b - a)) := by
  intro B δ hδ
  exact ⟨exists_scaleCurrent_increasing_secant B δ hδ,
    exists_scaleCurrent_decreasing_secant B δ hδ⟩

end RHTower
