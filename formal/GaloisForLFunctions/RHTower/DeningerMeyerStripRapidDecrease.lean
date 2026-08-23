import GaloisForLFunctions.RHTower.LPropertyStrips
import GaloisForLFunctions.RHTower.MellinUniformBoundedStripAllOrder

/-!
# Rapid decrease of the strong logarithmic Mellin transform on arbitrary strips

Existing all-order estimates were uniform only on nonnegative strips.  Contour rotation needs
signed abscissas as well.  A symmetric-strip majorant controls every weighted Euler derivative by
the strip radius, yielding uniform inverse-power bounds of every order and Burnol's exact
`HasStripRapidDecrease` property.
-/

namespace RHTower

open Complex MeasureTheory
open scoped BigOperators

noncomputable section

structure DeningerMeyerSymmetricMellinStrip where
  radius : ℝ
  nonnegative : 0 ≤ radius

structure DeningerMeyerSymmetricMellinAbscissa
    (S : DeningerMeyerSymmetricMellinStrip) where
  value : ℝ
  abs_le : |value| ≤ S.radius

def deningerMeyerSymmetricMellinMajorant
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerSymmetricMellinStrip)
    (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * S.radius ^ (n - k) *
      (Real.exp (S.radius * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)

private theorem deningerMeyerStrongLogDecay_iteratedDeriv_symmetric
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g) (n : ℕ) :
    DeningerMeyerStrongLogDecay (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem integrable_deningerMeyerSymmetricMellinMajorant
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerSymmetricMellinStrip)
    (n : ℕ) :
    Integrable (deningerMeyerSymmetricMellinMajorant g S n) := by
  unfold deningerMeyerSymmetricMellinMajorant
  have hsum : Integrable (∑ k ∈ Finset.range (n + 1), fun t : ℝ =>
      (n.choose k : ℝ) * S.radius ^ (n - k) *
        (Real.exp (S.radius * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)) := by
    apply integrable_finsetSum'
    intro k _
    have hbase : Integrable (fun t : ℝ =>
        Real.exp (S.radius * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖) := by
      convert integrable_deningerMeyerStrongLogAbsMoment
        (deningerMeyerStrongLogDecay_iteratedDeriv_symmetric g.property k) 0 S.radius using 1
      funext t
      simp
    simpa only [mul_assoc] using
      hbase.const_mul ((n.choose k : ℝ) * S.radius ^ (n - k))
  have heq :
      (fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.radius ^ (n - k) *
          (Real.exp (S.radius * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖)) =
      ∑ k ∈ Finset.range (n + 1), fun t : ℝ =>
        (n.choose k : ℝ) * S.radius ^ (n - k) *
          (Real.exp (S.radius * |t|) * ‖iteratedDeriv k (g : ℝ → ℂ) t‖) := by
    funext t
    simp only [Finset.sum_apply]
  rw [heq]
  exact hsum

theorem norm_deningerMeyerWeightedEulerIterate_le_symmetricMajorant
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerSymmetricMellinStrip)
    (n : ℕ) (sigma : DeningerMeyerSymmetricMellinAbscissa S) (t : ℝ) :
    ‖deningerMeyerWeightedEulerIterate sigma.value n (g : ℝ → ℂ) t‖ ≤
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.radius ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
  rw [deningerMeyerWeightedEulerIterate_binomial g sigma.value n]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        ‖(n.choose k : ℂ) * (sigma.value : ℂ) ^ (n - k) *
          iteratedDeriv k (g : ℝ → ℂ) t‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * |sigma.value| ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_natCast]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.radius ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
      apply Finset.sum_le_sum
      intro k _
      have hpow : |sigma.value| ^ (n - k) ≤ S.radius ^ (n - k) :=
        pow_le_pow_left₀ (abs_nonneg _) sigma.abs_le _
      gcongr

theorem abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le_symmetric
    (g : DeningerMeyerStrongLogTarget) (S : DeningerMeyerSymmetricMellinStrip)
    (n : ℕ) (sigma : DeningerMeyerSymmetricMellinAbscissa S) (tau : ℝ) :
    |tau| ^ n * ‖deningerMeyerStrongLogMellin g
        ((sigma.value : ℂ) + (tau : ℂ) * Complex.I)‖ ≤
      ∫ t : ℝ, deningerMeyerSymmetricMellinMajorant g S n t := by
  have hbase := abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le
    g n sigma.value tau
  apply hbase.trans
  apply integral_mono
    (integrable_iteratedDeriv_deningerMeyerWeightedLogProfile
      g.property sigma.value n).norm
    (integrable_deningerMeyerSymmetricMellinMajorant g S n)
  intro t
  rw [iteratedDeriv_deningerMeyerWeightedLogProfile g.property sigma.value n]
  simp only [deningerMeyerWeightedLogProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (sigma.value * t) ≤ Real.exp (S.radius * |t|) := by
    apply Real.exp_le_exp.mpr
    calc
      sigma.value * t ≤ |sigma.value * t| := le_abs_self _
      _ = |sigma.value| * |t| := abs_mul _ _
      _ ≤ S.radius * |t| := mul_le_mul_of_nonneg_right sigma.abs_le (abs_nonneg t)
  have hEuler := norm_deningerMeyerWeightedEulerIterate_le_symmetricMajorant
    g S n sigma t
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * S.radius ^ (n - k) *
        ‖iteratedDeriv k (g : ℝ → ℂ) t‖ := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg S.nonnegative _))
      (norm_nonneg _)
  calc
    Real.exp (sigma.value * t) *
        ‖deningerMeyerWeightedEulerIterate sigma.value n (g : ℝ → ℂ) t‖ ≤
      Real.exp (sigma.value * t) * ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.radius ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ :=
        mul_le_mul_of_nonneg_left hEuler (Real.exp_pos _).le
    _ ≤ Real.exp (S.radius * |t|) * ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * S.radius ^ (n - k) *
          ‖iteratedDeriv k (g : ℝ → ℂ) t‖ :=
        mul_le_mul_of_nonneg_right hexp hsum0
    _ = deningerMeyerSymmetricMellinMajorant g S n t := by
      rw [deningerMeyerSymmetricMellinMajorant, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem hasStripRapidDecrease_deningerMeyerStrongLogMellin
    (g : DeningerMeyerStrongLogTarget) :
    HasStripRapidDecrease (deningerMeyerStrongLogMellin g) := by
  intro a b N
  let S : DeningerMeyerSymmetricMellinStrip :=
    ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _)⟩
  let A : ℝ := ∫ t : ℝ,
    deningerMeyerSymmetricMellinMajorant g S (N + 1) t
  have hA : 0 ≤ A := by
    apply integral_nonneg
    intro t
    apply Finset.sum_nonneg
    intro k _
    positivity
  refine ⟨1, A * 2 ^ N, mul_nonneg hA (by positivity), fun s haS hbS hs => ?_⟩
  let sigma : DeningerMeyerSymmetricMellinAbscissa S :=
    ⟨s.re, by
      rw [abs_le]
      constructor
      · calc
          -S.radius ≤ -|a| := neg_le_neg (le_max_left |a| |b|)
          _ ≤ a := neg_abs_le a
          _ ≤ s.re := haS
      · calc
          s.re ≤ b := hbS
          _ ≤ |b| := le_abs_self b
          _ ≤ S.radius := le_max_right |a| |b|⟩
  have harg : ((sigma.value : ℂ) + (s.im : ℂ) * Complex.I) = s := by
    apply Complex.ext <;> simp [sigma]
  have hraw := abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le_symmetric
    g S (N + 1) sigma s.im
  rw [harg] at hraw
  have himpos : 0 < |s.im| := lt_of_lt_of_le (by norm_num) hs
  have hnorm : ‖deningerMeyerStrongLogMellin g s‖ ≤ A / |s.im| ^ (N + 1) := by
    apply (le_div_iff₀ (pow_pos himpos (N + 1))).mpr
    simpa [A, mul_comm] using hraw
  have hpow : (1 + |s.im|) ^ N ≤ (2 * |s.im|) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have himpow : |s.im| ^ N ≤ |s.im| ^ (N + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) hs
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  apply hnorm.trans
  apply (div_le_div_iff₀ (pow_pos himpos (N + 1)) (pow_pos (by positivity) N)).mpr
  calc
    A * (1 + |s.im|) ^ N ≤ A * (2 * |s.im|) ^ N :=
      mul_le_mul_of_nonneg_left hpow hA
    _ = A * 2 ^ N * |s.im| ^ N := by rw [mul_pow]; ring
    _ ≤ A * 2 ^ N * |s.im| ^ (N + 1) :=
      mul_le_mul_of_nonneg_left himpow (mul_nonneg hA (by positivity))

end

end RHTower
