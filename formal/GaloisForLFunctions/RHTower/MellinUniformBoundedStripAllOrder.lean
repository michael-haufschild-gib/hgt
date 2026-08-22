import GaloisForLFunctions.RHTower.MellinUniformStripAllOrder

open Complex MeasureTheory Filter Set Asymptotics
open scoped FourierTransform Topology BigOperators

namespace RHTower

noncomputable section

/-- Data for a nonnegative bounded Mellin abscissa strip. -/
structure DeningerMeyerBoundedMellinStrip where
  ceiling : ℝ
  nonnegative : 0 ≤ ceiling

/-- An abscissa certified to lie in a bounded Mellin strip. -/
structure DeningerMeyerBoundedMellinAbscissa (S : DeningerMeyerBoundedMellinStrip) where
  value : ℝ
  nonnegative : 0 ≤ value
  le_ceiling : value ≤ S.ceiling

/-- A single integrable majorant for weighted Euler derivatives over a
certified bounded Mellin strip. -/
def deningerMeyerBoundedMellinMajorant
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerBoundedMellinStrip)
    (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * S.ceiling ^ (n - k) *
      (Real.exp (S.ceiling * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)

private theorem deningerMeyerStrongLogDecay_iteratedDeriv_bounded
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g) (n : ℕ) :
    DeningerMeyerStrongLogDecay (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem integrable_deningerMeyerBoundedMellinMajorant
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerBoundedMellinStrip)
    (n : ℕ) :
    Integrable (deningerMeyerBoundedMellinMajorant g S n) := by
  unfold deningerMeyerBoundedMellinMajorant
  have hsum : Integrable (∑ k ∈ Finset.range (n + 1), fun t : ℝ =>
      (n.choose k : ℝ) * S.ceiling ^ (n - k) *
        (Real.exp (S.ceiling * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)) := by
    apply integrable_finsetSum'
    intro k _hk
    have hbase : Integrable (fun t : ℝ =>
        Real.exp (S.ceiling * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖) := by
      convert integrable_deningerMeyerStrongLogAbsMoment
        (deningerMeyerStrongLogDecay_iteratedDeriv_bounded g.property k) 0 S.ceiling using 1
      funext t
      simp
    simpa only [mul_assoc] using
      hbase.const_mul ((n.choose k : ℝ) * S.ceiling ^ (n - k))
  have heq :
      (fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.ceiling ^ (n - k) *
          (Real.exp (S.ceiling * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)) =
        ∑ k ∈ Finset.range (n + 1), fun t : ℝ =>
          (n.choose k : ℝ) * S.ceiling ^ (n - k) *
            (Real.exp (S.ceiling * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖) := by
    funext t
    simp only [Finset.sum_apply]
  rw [heq]
  exact hsum

private theorem norm_deningerMeyerWeightedEulerIterate_le_boundedMajorant
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerBoundedMellinStrip)
    (n : ℕ) (sigma : DeningerMeyerBoundedMellinAbscissa S) (t : ℝ) :
    ‖deningerMeyerWeightedEulerIterate sigma.value n (g : ℝ → ℂ) t‖ ≤
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.ceiling ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
  rw [deningerMeyerWeightedEulerIterate_binomial g sigma.value n]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        ‖(n.choose k : ℂ) * (sigma.value : ℂ) ^ (n - k) *
          iteratedDeriv k (g : ℝ → ℂ) t‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * sigma.value ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg sigma.nonnegative, norm_natCast]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.ceiling ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
      apply Finset.sum_le_sum
      intro k _hk
      have hpow : sigma.value ^ (n - k) ≤ S.ceiling ^ (n - k) := by
        exact pow_le_pow_left₀ sigma.nonnegative sigma.le_ceiling _
      gcongr

/-- Closed all-order Mellin decay on every certified bounded nonnegative strip. -/
theorem abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le_bounded
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerBoundedMellinStrip)
    (n : ℕ) (sigma : DeningerMeyerBoundedMellinAbscissa S) (tau : ℝ) :
    |tau| ^ n * ‖deningerMeyerStrongLogMellin g
        ((sigma.value : ℂ) + (tau : ℂ) * I)‖ ≤
      ∫ t : ℝ, deningerMeyerBoundedMellinMajorant g S n t := by
  have hbase :=
    abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le
      g n sigma.value tau
  have hinterior :=
    integrable_iteratedDeriv_deningerMeyerWeightedLogProfile
      g.property sigma.value n |>.norm
  apply hbase.trans
  apply integral_mono hinterior
    (integrable_deningerMeyerBoundedMellinMajorant g S n)
  intro t
  rw [iteratedDeriv_deningerMeyerWeightedLogProfile g.property sigma.value n]
  simp only [deningerMeyerWeightedLogProfile]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hst : sigma.value * t ≤ S.ceiling * |t| := by
    calc
      sigma.value * t ≤ |sigma.value * t| := le_abs_self _
      _ = sigma.value * |t| := by
        rw [abs_mul, abs_of_nonneg sigma.nonnegative]
      _ ≤ S.ceiling * |t| :=
        mul_le_mul_of_nonneg_right sigma.le_ceiling (abs_nonneg t)
  have hexp : Real.exp (sigma.value * t) ≤ Real.exp (S.ceiling * |t|) :=
    Real.exp_le_exp.mpr hst
  have hEuler := norm_deningerMeyerWeightedEulerIterate_le_boundedMajorant
    g S n sigma t
  have hmajorant_nonneg : 0 ≤
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.ceiling ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
    apply Finset.sum_nonneg
    intro k _hk
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg S.nonnegative _))
      (norm_nonneg _)
  calc
    Real.exp (sigma.value * t) *
        ‖deningerMeyerWeightedEulerIterate sigma.value n (g : ℝ → ℂ) t‖ ≤
      Real.exp (sigma.value * t) *
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * S.ceiling ^ (n - k) *
            ‖iteratedDeriv k (g : ℝ → ℂ) t‖ :=
      mul_le_mul_of_nonneg_left hEuler (Real.exp_pos _).le
    _ ≤ Real.exp (S.ceiling * |t|) *
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * S.ceiling ^ (n - k) *
            ‖iteratedDeriv k (g : ℝ → ℂ) t‖ :=
      mul_le_mul_of_nonneg_right hexp hmajorant_nonneg
    _ = deningerMeyerBoundedMellinMajorant g S n t := by
      unfold deningerMeyerBoundedMellinMajorant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring

end

end RHTower
