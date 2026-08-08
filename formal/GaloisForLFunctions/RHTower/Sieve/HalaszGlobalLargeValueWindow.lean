import GaloisForLFunctions.RHTower.Sieve.HalaszGlobalUniqueClose
import GaloisForLFunctions.RHTower.Sieve.HalaszLargeValueWindow

/-!
# The large-value set is one window, with no cell covering

`volume_halaszLargeValues_le` bounds the measure of the large-value set by covering `[-T, T]` with
cells of length `π / log z`, because its diameter estimate needs `|t − u|·log z ≤ π`.  The cell count
`2T log z/π` multiplies the per-cell diameter `≍ δ / log z`, so that bound is of order `T·δ` and
therefore beats the trivial bound `2T` only for `δ < 1/(2√2)`.

The distance growth law needs no relation between `t − u` and `log z`, so the confinement is global:
two frequencies at which the series is large satisfy `charSepLower z (t − u) ≤ 4δ²`, and since
`charSepLower z` increases with `|t − u|`, every large value on the whole range lies within `Δ` of
every other as soon as `4δ² < charSepLower z Δ`.  The measure is then `2Δ` with no cell factor.
Unwinding `charSepLower`, the admissible `Δ` is of order `e^{4δ²}/log z`, so the estimate is
nontrivial in the whole range `4δ² < logLog z − C` — for `δ` up to `≍ √(logLog z)` rather than a
fixed constant.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory

section
variable {f : ℕ → ℂ}

/-- **A large value forces a close frequency.**  The contrapositive of the damped bound. -/
theorem sqrt_mulDistSqPair_le_of_norm_gt
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) {t : ℝ}
    (ht : (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖) :
    Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ := by
  by_contra hfar
  have hsre : (1 : ℝ) < (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re := by
    rw [re_ofReal_add_mul_I]; exact hσ
  have hfar' : δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) :=
    le_of_lt (not_le.mp hfar)
  have hbound := norm_tsum_twistedSummand_le_of_far hf1 hmul hbdd hsre hz hδ
    (by rw [im_ofReal_add_mul_I]; exact hfar')
  rw [re_ofReal_add_mul_I] at hbound
  linarith

/-- **Global confinement of two close frequencies.**  Contrapositive of the monotonicity of
`charSepLower`: no spacing hypothesis and no relation between `t − u` and `log z`. -/
theorem abs_sub_lt_of_both_close (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ} (hz : 3 ≤ z)
    {δ Δ t u : ℝ} (hΔ0 : 0 < Δ) (hd : |t - u| ≤ 2) (hgap : 4 * δ ^ 2 < charSepLower z Δ)
    (ht : Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ)
    (hu : Real.sqrt (mulDistSqPair f (charFn u) (Nat.primesLE z)) ≤ δ) :
    |t - u| < Δ := by
  have hP : ∀ p ∈ Nat.primesLE z, 0 < p := fun p hp => (Nat.prime_of_mem_primesLE hp).pos
  have hsq : ∀ v : ℝ, Real.sqrt (mulDistSqPair f (charFn v) (Nat.primesLE z)) ≤ δ →
      mulDistSqPair f (charFn v) (Nat.primesLE z) ≤ δ ^ 2 := by
    intro v h
    have hnn : 0 ≤ mulDistSqPair f (charFn v) (Nat.primesLE z) :=
      mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => (norm_charFn v p).le) hP
    have hmono := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt hnn] at hmono
  by_contra hle
  rw [not_lt] at hle
  have hd0 : t - u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hle
    linarith
  have hmain := charSepLower_le_four_mul_of_both_close hf hz hd hd0 (hsq t ht) (hsq u hu)
  have hmono : charSepLower z Δ ≤ charSepLower z (t - u) :=
    charSepLower_mono_abs (by rwa [abs_of_pos hΔ0]) (by rwa [abs_of_pos hΔ0])
  linarith

/-- **Two large values are within `Δ`, on any range.**  The diameter bound of
`abs_sub_le_of_norm_gt` without its spacing hypothesis `|t − u|·log z ≤ π`. -/
theorem abs_sub_lt_of_norm_gt
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 3 ≤ z)
    {δ Δ : ℝ} (hδ : 0 ≤ δ) (hΔ0 : 0 < Δ) (hgap : 4 * δ ^ 2 < charSepLower z Δ) {t u : ℝ}
    (hd : |t - u| ≤ 2)
    (ht : (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
    (hu : (1 + 1 / (σ - 1)) *
        Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
      ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((u : ℝ) : ℂ) * Complex.I) n‖) :
    |t - u| < Δ :=
  abs_sub_lt_of_both_close hbdd hz hΔ0 hd hgap
    (sqrt_mulDistSqPair_le_of_norm_gt hf1 hmul hbdd hσ (le_trans (by norm_num) hz) hδ ht)
    (sqrt_mulDistSqPair_le_of_norm_gt hf1 hmul hbdd hσ (le_trans (by norm_num) hz) hδ hu)

/-- **The measure of the large-value set on a unit range.**  One window, no cell covering: the bound
is `2Δ` for every `Δ` with `4δ² < charSepLower z Δ`. -/
theorem volume_halaszLargeValues_le_window
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 3 ≤ z)
    {δ Δ : ℝ} (hδ : 0 ≤ δ) (hΔ0 : 0 < Δ) (hgap : 4 * δ ^ 2 < charSepLower z Δ)
    {T : ℝ} (hT : T ≤ 1) :
    volume ({t : ℝ | (1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
            ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖}
          ∩ Set.Icc (-T) T)
      ≤ ENNReal.ofReal (2 * Δ) := by
  refine GaloisForLFunctions.HTGeometry.volume_le_of_pairwise_dist_le hΔ0.le ?_
  intro x hx y hy
  have hx' := hx.2
  have hy' := hy.2
  rw [Set.mem_Icc] at hx' hy'
  have hd : |x - y| ≤ 2 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hx'.2, hy'.1], by linarith [hy'.2, hx'.1]⟩
  exact le_of_lt (abs_sub_lt_of_norm_gt hf1 hmul hbdd hσ hz hδ hΔ0 hgap hd hx.1 hy.1)

end

end RHTower.Sieve
end
