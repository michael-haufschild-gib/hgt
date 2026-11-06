import GaloisForLFunctions.RHTower.EulerFisherCurvature
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing coefficient-square diagonals of von Mangoldt moments

For `0 ≤ d < σ-1/2`, the squared coefficients of
`d^(k+1)/k! · Σ Λ(n)(log n)^k n^(-σ-it)` have sum tending to zero.
Exponential domination gives a geometric bound at every intermediate radius.
The bound is independent of the ordinate and does not bound off-diagonal correlations.
-/

open Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Absolute coefficient of the factorially normalized logarithmic moment. -/
noncomputable def normalizedMangoldtCoefficient (σ d : ℝ) (k n : ℕ) : ℝ :=
  d * ((d * Real.log n) ^ k / (k.factorial : ℝ)) * vonMangoldt n *
    (n : ℝ) ^ (-σ)

theorem normalizedMangoldtCoefficient_nonneg {σ d : ℝ} (hd : 0 ≤ d) (k n : ℕ) :
    0 ≤ normalizedMangoldtCoefficient σ d k n := by
  unfold normalizedMangoldtCoefficient
  have := Real.log_natCast_nonneg n
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

/-- Moving the logarithmic power into an exponential gains the factor `(d/R)^k`. -/
theorem normalizedMangoldtCoefficient_le_geometric {σ d R : ℝ}
    (hd : 0 ≤ d) (hR : 0 < R) (k n : ℕ) :
    normalizedMangoldtCoefficient σ d k n ≤
      d * (d / R) ^ k * vonMangoldt n * (n : ℝ) ^ (-(σ - R)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [normalizedMangoldtCoefficient]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : (d * Real.log n) ^ k / (k.factorial : ℝ) =
      (d / R) ^ k * ((R * Real.log n) ^ k / (k.factorial : ℝ)) := by
    rw [← mul_div_assoc, ← mul_pow]
    congr 2
    field_simp
  have hexp := Real.pow_div_factorial_le_exp (R * Real.log n)
    (mul_nonneg hR.le (Real.log_natCast_nonneg n)) k
  have hrpow : Real.exp (R * Real.log n) * (n : ℝ) ^ (-σ) =
      (n : ℝ) ^ (-(σ - R)) := by
    rw [mul_comm R, ← Real.rpow_def_of_pos hnpos, ← Real.rpow_add hnpos]
    congr 1
    ring
  unfold normalizedMangoldtCoefficient
  rw [hsplit]
  calc
    _ ≤ d * ((d / R) ^ k * Real.exp (R * Real.log n)) * vonMangoldt n *
        (n : ℝ) ^ (-σ) := by
      gcongr
    _ = _ := by
      calc
        _ = (d * (d / R) ^ k * vonMangoldt n) *
            (Real.exp (R * Real.log n) * (n : ℝ) ^ (-σ)) := by ring
        _ = _ := by rw [hrpow]

/-- The elementary bound `Λ(n) ≤ log n` gives square summability past abscissa one. -/
theorem summable_vonMangoldt_sq_rpow {α : ℝ} (hα : 1 < α) :
    Summable (fun n : ℕ => vonMangoldt n ^ 2 * (n : ℝ) ^ (-α)) := by
  apply (RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 2 α hα).of_nonneg_of_le
  · intro n
    positivity
  intro n
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [sq_abs]
  exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_le_log 2

theorem normalizedMangoldtCoefficient_sq_le_geometric {σ d R : ℝ}
    (hd : 0 ≤ d) (hR : 0 < R) (k n : ℕ) :
    normalizedMangoldtCoefficient σ d k n ^ 2 ≤
      (d * (d / R) ^ k) ^ 2 *
        (vonMangoldt n ^ 2 * (n : ℝ) ^ (-(2 * (σ - R)))) := by
  have h := pow_le_pow_left₀ (normalizedMangoldtCoefficient_nonneg (σ := σ) hd k n)
    (normalizedMangoldtCoefficient_le_geometric hd hR k n) 2
  refine h.trans_eq ?_
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num only [Nat.cast_ofNat]
  have he : -(σ - R) * (2 : ℝ) = -(2 * (σ - R)) := by ring
  rw [he, mul_assoc]

/-- An explicit geometric upper bound for the complete coefficient-square diagonal. -/
theorem normalizedMangoldtDiagonal_le_geometric {σ d R : ℝ}
    (hd : 0 ≤ d) (hR : 0 < R) (hσR : R < σ - 1 / 2) (k : ℕ) :
    (∑' n : ℕ, normalizedMangoldtCoefficient σ d k n ^ 2) ≤
      (d * (d / R) ^ k) ^ 2 *
        ∑' n : ℕ, vonMangoldt n ^ 2 * (n : ℝ) ^ (-(2 * (σ - R))) := by
  have hsum := (summable_vonMangoldt_sq_rpow
    (α := 2 * (σ - R)) (by linarith only [hσR])).mul_left ((d * (d / R) ^ k) ^ 2)
  have hsum' : Summable (fun n : ℕ => normalizedMangoldtCoefficient σ d k n ^ 2) :=
    hsum.of_nonneg_of_le (fun n => sq_nonneg _)
      (normalizedMangoldtCoefficient_sq_le_geometric hd hR k)
  simpa only [tsum_mul_left] using hsum'.tsum_le_tsum
    (normalizedMangoldtCoefficient_sq_le_geometric hd hR k) hsum

/-- Every radius strictly below `σ-1/2` makes the normalized diagonal vanish. -/
theorem tendsto_normalizedMangoldtDiagonal_zero {σ d : ℝ}
    (hd : 0 ≤ d) (hgap : d < σ - 1 / 2) :
    Tendsto (fun k : ℕ => ∑' n : ℕ, normalizedMangoldtCoefficient σ d k n ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨R, hdR, hRσ⟩ := exists_between hgap
  have hR : 0 < R := lt_of_le_of_lt hd hdR
  have hq0 : 0 ≤ d / R := div_nonneg hd hR.le
  have hq1 : d / R < 1 := (div_lt_one hR).mpr hdR
  have hlim := (((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul d).pow 2).mul_const
    (∑' n : ℕ, vonMangoldt n ^ 2 * (n : ℝ) ^ (-(2 * (σ - R))))
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_mul] at hlim
  exact squeeze_zero (fun k => tsum_nonneg fun n => sq_nonneg _)
    (normalizedMangoldtDiagonal_le_geometric hd hR hRσ) hlim

#print axioms tendsto_normalizedMangoldtDiagonal_zero

/-- The real coefficient agrees with the norm of the actual L-series term. -/
theorem norm_normalizedMangoldtTerm (s : ℂ) (k n : ℕ) :
    ‖LSeries.term (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s n /
      (k.factorial : ℂ)‖ = normalizedMangoldtCoefficient s.re 1 k n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [normalizedMangoldtCoefficient]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) n =
      (Complex.log n) ^ k * (vonMangoldt n : ℂ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change Complex.log n * _ = _
      rw [ih, pow_succ]
      ring
  have hnormpow : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.norm_cpow_eq_rpow_re_of_pos (y := s) hnpos)
  rw [LSeries.term_of_ne_zero hn, hlog, norm_div, norm_div, norm_mul, norm_pow,
    hnormpow, ← Complex.natCast_log]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)), Complex.norm_natCast]
  unfold normalizedMangoldtCoefficient
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  simp only [one_mul]
  ring

/-- The coefficient-square diagonal of the actual normalized von Mangoldt series
vanishes on every line `Re s > 3/2`, uniformly in the imaginary part. -/
theorem tendsto_normalizedMangoldtTermDiagonal_zero {s : ℂ} (hs : 3 / 2 < s.re) :
    Tendsto (fun k : ℕ => ∑' n : ℕ,
      ‖LSeries.term (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s n /
        (k.factorial : ℂ)‖ ^ 2) atTop (𝓝 0) := by
  simpa only [norm_normalizedMangoldtTerm] using
    (tendsto_normalizedMangoldtDiagonal_zero (σ := s.re) (d := 1)
      (by norm_num) (by linarith only [hs]))

#print axioms tendsto_normalizedMangoldtTermDiagonal_zero

end GaloisForLFunctions.ZeroConfigurationGeometry
