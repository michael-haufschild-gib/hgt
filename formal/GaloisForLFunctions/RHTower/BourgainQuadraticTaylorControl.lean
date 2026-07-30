/-
# Quantitative quadratic localization for Bourgain's curve

Bourgain's passage from (1.21) to (1.22) replaces a smooth curve by its
quadratic Taylor polynomial on intervals of length `δ`.  This file records
the exact Banach-space remainder estimate, together with its propagation
through a bounded frequency functional.
-/
import GaloisForLFunctions.RHTower.BourgainTaylorWronskian
import Mathlib.Analysis.Calculus.Taylor

namespace RHTower

noncomputable section

open Set

/-- A uniform third-derivative bound controls the quadratic Taylor remainder
by `C (x-a)^3 / 2`. -/
theorem bourgain_quadraticTaylorWithin_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b C x : ℝ}
    (hab : a ≤ b)
    (hf : ContDiffOn ℝ 3 f (Icc a b))
    (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b,
      ‖iteratedDerivWithin 3 f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f 2 (Icc a b) a x‖
      ≤ C * (x - a) ^ (3 : ℕ) / 2 := by
  simpa only [Nat.factorial, Nat.cast_ofNat] using!
    (taylor_mean_remainder_bound (n := 2) hab hf hx hC)

/-- Localized version of the quadratic remainder bound on an interval of
radius at most `δ`. -/
theorem bourgain_quadraticTaylorWithin_remainder_of_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b C x δ : ℝ}
    (hab : a ≤ b)
    (hf : ContDiffOn ℝ 3 f (Icc a b))
    (hx : x ∈ Icc a b)
    (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Icc a b,
      ‖iteratedDerivWithin 3 f (Icc a b) y‖ ≤ C)
    (hδ : x - a ≤ δ) :
    ‖f x - taylorWithinEval f 2 (Icc a b) a x‖
      ≤ C * δ ^ (3 : ℕ) / 2 := by
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hpow : (x - a) ^ (3 : ℕ) ≤ δ ^ (3 : ℕ) :=
    pow_le_pow_left₀ hxa hδ 3
  calc
    ‖f x - taylorWithinEval f 2 (Icc a b) a x‖
        ≤ C * (x - a) ^ (3 : ℕ) / 2 :=
      bourgain_quadraticTaylorWithin_remainder hab hf hx hC
    _ ≤ C * δ ^ (3 : ℕ) / 2 := by
      gcongr

/-- A bounded frequency functional converts curve approximation into phase
approximation, with exactly the expected factor `N`. -/
theorem bourgain_frequency_quadraticTaylorWithin_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ)
    {f : ℝ → E} {a b C N x δ : ℝ}
    (hab : a ≤ b)
    (hf : ContDiffOn ℝ 3 f (Icc a b))
    (hx : x ∈ Icc a b)
    (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Icc a b,
      ‖iteratedDerivWithin 3 f (Icc a b) y‖ ≤ C)
    (hN : ‖L‖ ≤ N)
    (hδ : x - a ≤ δ) :
    ‖L (f x - taylorWithinEval f 2 (Icc a b) a x)‖
      ≤ N * (C * δ ^ (3 : ℕ) / 2) := by
  have hrem :=
    bourgain_quadraticTaylorWithin_remainder_of_sub_le
      hab hf hx hC0 hC hδ
  calc
    ‖L (f x - taylorWithinEval f 2 (Icc a b) a x)‖
        ≤ ‖L‖ * ‖f x - taylorWithinEval f 2 (Icc a b) a x‖ :=
      L.le_opNorm _
    _ ≤ N * (C * δ ^ (3 : ℕ) / 2) := by
      exact mul_le_mul hN hrem (norm_nonneg _) (le_trans (norm_nonneg L) hN)

/-- The cubic localization loss at Bourgain's interval length
`δ = K^{-1/2}` is exactly `K^{-3/2}`. -/
theorem bourgain_half_scale_cube
    {K : ℝ} (hK : 0 ≤ K) :
    (K ^ (-(1 : ℝ) / 2)) ^ (3 : ℕ) = K ^ (-(3 : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
  congr 1
  ring

/-- Equation (1.22)'s phase-error scale, with all constants exposed. -/
theorem bourgain_frequency_halfScale_quadraticTaylorWithin_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ)
    {f : ℝ → E} {a b C N x K : ℝ}
    (hab : a ≤ b)
    (hf : ContDiffOn ℝ 3 f (Icc a b))
    (hx : x ∈ Icc a b)
    (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Icc a b,
      ‖iteratedDerivWithin 3 f (Icc a b) y‖ ≤ C)
    (hN : ‖L‖ ≤ N)
    (hK : 0 ≤ K)
    (hδ : x - a ≤ K ^ (-(1 : ℝ) / 2)) :
    ‖L (f x - taylorWithinEval f 2 (Icc a b) a x)‖
      ≤ N * (C * K ^ (-(3 : ℝ) / 2) / 2) := by
  simpa only [bourgain_half_scale_cube hK] using
    (bourgain_frequency_quadraticTaylorWithin_remainder
      L hab hf hx hC0 hC hN hδ)

end

end RHTower
