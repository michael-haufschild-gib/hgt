import GaloisForLFunctions.HTGeometry.PoissonRadialChamber

/-!
# Finite-Euler one-Cauchy phase chambers

For a prime `p` and an upper centered point `x + iy`, the reflected finite-Euler radii are
`p^(-1/2+y)` and `p^(-1/2-y)`.  The literal one-sided Cauchy diagonal is the radial difference of
their disk Euler responses.  It therefore has a complete, exact phase chamber rather than a fixed
sign.

The negative witness is not merely a no-go: at phase `pi`, any remainder that restores a
nonnegative completed diagonal must make a strictly positive contribution.  This is the local,
source-facing compensation obligation.
-/

namespace GaloisForLFunctions.RHTower

open HTGeometry

noncomputable section

/-- The outer reflected finite-Euler radius at centered height `y`. -/
def primeEulerOuterRadius (p : ℕ) (y : ℝ) : ℝ :=
  (p : ℝ) ^ (-1 / 2 + y)

/-- The inner reflected finite-Euler radius at centered height `y`. -/
def primeEulerInnerRadius (p : ℕ) (y : ℝ) : ℝ :=
  (p : ℝ) ^ (-1 / 2 - y)

/-- The phase read by the prime-log clock. -/
def primeEulerClockPhase (p : ℕ) (x : ℝ) : ℝ :=
  x * Real.log p

/-- The exact cosine boundary between positive and negative finite-Euler chambers. -/
def primeEulerCauchyThreshold (p : ℕ) (y : ℝ) : ℝ :=
  poissonRadialThreshold (primeEulerOuterRadius p y) (primeEulerInnerRadius p y)

/-- The literal one-sided local finite-Euler Cauchy diagonal, expressed through its two disk
rational responses. -/
def primeEulerOneSidedCauchyDiagonal (p : ℕ) (x y : ℝ) : ℝ :=
  Real.log p / (2 * y) *
    ((diskEulerResponse (primeEulerOuterRadius p y) (primeEulerClockPhase p x)).re -
      (diskEulerResponse (primeEulerInnerRadius p y) (primeEulerClockPhase p x)).re)

/-- The centered functional-equation-paired diagonal contributes the reflected copy as well. -/
def primeEulerFEPairedCauchyDiagonal (p : ℕ) (x y : ℝ) : ℝ :=
  2 * primeEulerOneSidedCauchyDiagonal p x y

/-- In the upper centered strip, the reflected finite-Euler radii are strictly ordered inside the
unit disk. -/
theorem primeEuler_radii {p : ℕ} (hp : 1 < p) {y : ℝ}
    (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    0 < primeEulerInnerRadius p y ∧
      primeEulerInnerRadius p y < primeEulerOuterRadius p y ∧
      primeEulerOuterRadius p y < 1 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := zero_lt_one.trans hpR
  exact ⟨Real.rpow_pos_of_pos hp0 _,
    Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith),
    Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)⟩

/-- The product of the reflected radii is independent of the centered height. -/
theorem primeEuler_radius_mul {p : ℕ} (hp : 1 < p) (y : ℝ) :
    primeEulerOuterRadius p y * primeEulerInnerRadius p y = (p : ℝ) ^ (-1 : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  rw [primeEulerOuterRadius, primeEulerInnerRadius, ← Real.rpow_add hp0]
  congr 1
  ring

/-- Explicit prime form of the radial cosine threshold. -/
theorem primeEulerCauchyThreshold_eq {p : ℕ} (hp : 1 < p) (y : ℝ) :
    primeEulerCauchyThreshold p y =
      (primeEulerOuterRadius p y + primeEulerInnerRadius p y) /
        (1 + (p : ℝ) ^ (-1 : ℝ)) := by
  rw [primeEulerCauchyThreshold, poissonRadialThreshold, primeEuler_radius_mul hp y]

/-- The finite-Euler chamber boundary is a genuine cosine level in `(0,1)`. -/
theorem primeEulerCauchyThreshold_mem_Ioo {p : ℕ} (hp : 1 < p) {y : ℝ}
    (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    primeEulerCauchyThreshold p y ∈ Set.Ioo 0 1 := by
  obtain ⟨hinner0, hord, houter1⟩ := primeEuler_radii hp hy0 hyHalf
  exact ⟨poissonRadialThreshold_pos hinner0 hord,
    poissonRadialThreshold_lt_one hinner0 hord houter1⟩

/-- Exact Poisson radial-difference value law for the literal one-sided local source. -/
theorem primeEulerOneSidedCauchyDiagonal_eq_poisson {p : ℕ} (hp : 1 < p)
    {x y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    primeEulerOneSidedCauchyDiagonal p x y =
      Real.log p / (4 * y) *
        (poissonKer (primeEulerOuterRadius p y) (primeEulerClockPhase p x) -
          poissonKer (primeEulerInnerRadius p y) (primeEulerClockPhase p x)) := by
  obtain ⟨hinner0, hord, houter1⟩ := primeEuler_radii hp hy0 hyHalf
  have houter0 : 0 < primeEulerOuterRadius p y := lt_trans hinner0 hord
  have hinner1 : primeEulerInnerRadius p y < 1 := lt_trans hord houter1
  rw [primeEulerOneSidedCauchyDiagonal,
    diskEulerResponse_re (by simpa [abs_of_pos houter0] using houter1),
    diskEulerResponse_re (by simpa [abs_of_pos hinner0] using hinner1)]
  ring

/-- The centered functional-equation-paired source has exactly twice the one-sided value. -/
theorem primeEulerFEPairedCauchyDiagonal_eq_poisson {p : ℕ} (hp : 1 < p)
    {x y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    primeEulerFEPairedCauchyDiagonal p x y =
      Real.log p / (2 * y) *
        (poissonKer (primeEulerOuterRadius p y) (primeEulerClockPhase p x) -
          poissonKer (primeEulerInnerRadius p y) (primeEulerClockPhase p x)) := by
  rw [primeEulerFEPairedCauchyDiagonal,
    primeEulerOneSidedCauchyDiagonal_eq_poisson hp hy0 hyHalf]
  ring

/-- Complete positive phase chamber of the one-sided finite-Euler diagonal. -/
theorem primeEulerOneSidedCauchyDiagonal_pos_iff {p : ℕ} (hp : 1 < p)
    {x y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    0 < primeEulerOneSidedCauchyDiagonal p x y ↔
      primeEulerCauchyThreshold p y < Real.cos (primeEulerClockPhase p x) := by
  obtain ⟨hinner0, hord, houter1⟩ := primeEuler_radii hp hy0 hyHalf
  rw [primeEulerOneSidedCauchyDiagonal_eq_poisson hp hy0 hyHalf]
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hscale : 0 < Real.log p / (4 * y) :=
    div_pos (Real.log_pos hpR) (mul_pos (by norm_num) hy0)
  rw [mul_pos_iff_of_pos_left hscale,
    poissonKer_sub_pos_iff hinner0 hord houter1]
  rfl

/-- Exact seam between the positive and negative finite-Euler phase chambers. -/
theorem primeEulerOneSidedCauchyDiagonal_eq_zero_iff {p : ℕ} (hp : 1 < p)
    {x y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    primeEulerOneSidedCauchyDiagonal p x y = 0 ↔
      Real.cos (primeEulerClockPhase p x) = primeEulerCauchyThreshold p y := by
  obtain ⟨hinner0, hord, houter1⟩ := primeEuler_radii hp hy0 hyHalf
  rw [primeEulerOneSidedCauchyDiagonal_eq_poisson hp hy0 hyHalf, mul_eq_zero]
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hscale : 0 < Real.log p / (4 * y) :=
    div_pos (Real.log_pos hpR) (mul_pos (by norm_num) hy0)
  simp only [ne_of_gt hscale, false_or]
  rw [poissonKer_sub_eq_zero_iff hinner0 hord houter1]
  rfl

/-- Complete negative phase chamber of the one-sided finite-Euler diagonal. -/
theorem primeEulerOneSidedCauchyDiagonal_neg_iff {p : ℕ} (hp : 1 < p)
    {x y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    primeEulerOneSidedCauchyDiagonal p x y < 0 ↔
      Real.cos (primeEulerClockPhase p x) < primeEulerCauchyThreshold p y := by
  obtain ⟨hinner0, hord, houter1⟩ := primeEuler_radii hp hy0 hyHalf
  rw [primeEulerOneSidedCauchyDiagonal_eq_poisson hp hy0 hyHalf]
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hscale : 0 < Real.log p / (4 * y) :=
    div_pos (Real.log_pos hpR) (mul_pos (by norm_num) hy0)
  rw [mul_neg_iff]
  simp only [hscale, true_and, lt_asymm hscale, false_and, or_false]
  rw [poissonKer_sub_neg_iff hinner0 hord houter1]
  rfl

/-- Every prime has a strict positive source witness at clock phase zero. -/
theorem primeEulerOneSidedCauchyDiagonal_pos_at_zero {p : ℕ} (hp : 1 < p)
    {y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    0 < primeEulerOneSidedCauchyDiagonal p 0 y := by
  rw [primeEulerOneSidedCauchyDiagonal_pos_iff hp hy0 hyHalf,
    primeEulerClockPhase, zero_mul, Real.cos_zero]
  exact (primeEulerCauchyThreshold_mem_Ioo hp hy0 hyHalf).2

/-- Every prime has a strict negative source witness at clock phase `pi`. -/
theorem primeEulerOneSidedCauchyDiagonal_neg_at_pi_div_log {p : ℕ} (hp : 1 < p)
    {y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    primeEulerOneSidedCauchyDiagonal p (Real.pi / Real.log p) y < 0 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlog : Real.log p ≠ 0 := (Real.log_pos hpR).ne'
  rw [primeEulerOneSidedCauchyDiagonal_neg_iff hp hy0 hyHalf,
    primeEulerClockPhase, div_mul_cancel₀ Real.pi hlog, Real.cos_pi]
  have hthreshold := (primeEulerCauchyThreshold_mem_Ioo hp hy0 hyHalf).1
  linarith

/-- Positive residue of the negative-chamber no-go: if the completed diagonal is nonnegative at
the explicit negative finite-Euler phase, its complementary remainder is strictly positive. -/
theorem primeEuler_remainder_pos_at_pi_div_log {p : ℕ} (hp : 1 < p)
    {y remainder : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2)
    (hcompleted :
      0 ≤ primeEulerOneSidedCauchyDiagonal p (Real.pi / Real.log p) y + remainder) :
    0 < remainder := by
  have hnegative := primeEulerOneSidedCauchyDiagonal_neg_at_pi_div_log hp hy0 hyHalf
  linarith

end

end GaloisForLFunctions.RHTower
