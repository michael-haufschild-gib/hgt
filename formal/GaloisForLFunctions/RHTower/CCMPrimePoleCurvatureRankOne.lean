import GaloisForLFunctions.RHTower.CCMPrimePoleNegativeCurvature

/-!
# Exact one-direction compensation of literal prime curvature

At `log 2` in aperture `log(21/10)`, four positive squares and one
negative sample-difference square give the complete iterated prime energy.
The negative channel is the difference between the samples at
`log(2/3)` and `log 2`. All coefficients retain the actual cutoff prime rates.
-/

noncomputable section
set_option autoImplicit false
namespace RHTower.PrimeCurvatureRankOne
open PrimeCurvatureCounterexample HTGeometry.JumpBochner

def curvatureAtTwo (f : ℝ → ℝ) : ℝ :=
  gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
    ccmPrimePoleJumpShift f (Real.log 2)

def sampleDelta (f : ℝ → ℝ) (q : ℝ) : ℝ := f (Real.log q) - f (Real.log 2)

def alpha : ℝ := 31 * (Real.log 2)^2 / 36 - 5 * Real.log 2 * Real.log 3 / 54
def beta : ℝ := 53 * (Real.log 3)^2 / 162 - 7 * Real.log 2 * Real.log 3 / 27
def gamma : ℝ := 13 * (Real.log 2)^2 / 24 - 5 * Real.log 2 * Real.log 3 / 36
def crossAB : ℝ := 10 * Real.log 2 * Real.log 3 / 27
def crossAC : ℝ := -(Real.log 2)^2 / 2
def crossBC : ℝ := 5 * Real.log 2 * Real.log 3 / 18
def delta : ℝ := gamma - crossAC^2 / (4 * alpha)
def residualBC : ℝ := crossBC - crossAB * crossAC / (2 * alpha)
def kappa : ℝ := beta - crossAB^2 / (4 * alpha) - residualBC^2 / (4 * delta)
def penalty : ℝ := -kappa

private theorem generator_row (f : ℝ → ℝ) (q : ℝ) :
    generator (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f (Real.log q) = row (fun y => f y - f (Real.log q)) q := rfl

private theorem energy_row (f g : ℝ → ℝ) (q : ℝ) :
    energyDensity (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f g (Real.log q) =
        row (fun y => (f y - f (Real.log q)) * (g y - g (Real.log q))) q / 2 := by
  simp only [energyDensity, row, difference, mul_assoc]

/-- Exact elimination of the two freely prescribed second-shell values. -/
theorem curvatureAtTwo_eq_reduced (f : ℝ → ℝ) :
    curvatureAtTwo f =
      (7 * Real.log 2 * Real.log 3 / 72) *
        (sampleDelta f (4/3) - 2 * sampleDelta f (2/3))^2 +
      (5 * Real.log 2 * Real.log 3 / 72) *
        (sampleDelta f (3/2) - 2 * sampleDelta f (1/2))^2 +
      alpha * (sampleDelta f 1)^2 + beta * (sampleDelta f (2/3))^2 +
      gamma * (sampleDelta f (1/2))^2 +
      crossAB * sampleDelta f 1 * sampleDelta f (2/3) +
      crossAC * sampleDelta f 1 * sampleDelta f (1/2) +
      crossBC * sampleDelta f (2/3) * sampleDelta f (1/2) := by
  simp only [curvatureAtTwo, gammaTwo, generator_row, energy_row,
    row_two, row_one, row_two_thirds, row_half]
  dsimp [sampleDelta, alpha, beta, gamma, crossAB, crossAC, crossBC]
  ring

private theorem log_bounds :
    0 < Real.log 2 ∧ 0 < Real.log 3 ∧ 5 * Real.log 3 < 8 * Real.log 2 := by
  refine ⟨Real.log_pos (by norm_num), Real.log_pos (by norm_num), ?_⟩
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3^5)
    (by norm_num : (3 : ℝ)^5 < 2^8)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  exact h

private theorem pivot_bounds :
    (7/10 : ℝ) * (Real.log 2)^2 < alpha ∧
    (3/10 : ℝ) * (Real.log 2)^2 < gamma := by
  obtain ⟨hl, _, hm⟩ := log_bounds
  have hp := mul_lt_mul_of_pos_left hm hl
  dsimp [alpha, gamma]
  constructor <;> nlinarith [sq_pos_of_pos hl]

theorem alpha_pos : 0 < alpha := by
  exact (by positivity : 0 ≤ (7/10 : ℝ) * (Real.log 2)^2).trans_lt pivot_bounds.1

private theorem blockDet_pos : 0 < 4 * alpha * gamma - crossAC^2 := by
  obtain ⟨hl, _, _⟩ := log_bounds
  have hs : 0 < (Real.log 2)^2 := sq_pos_of_pos hl
  have hprod₁ := mul_lt_mul_of_pos_left pivot_bounds.2 alpha_pos
  have hprod₂ := mul_lt_mul_of_pos_right pivot_bounds.1
    (by positivity : 0 < (3/10 : ℝ) * (Real.log 2)^2)
  have hprod := hprod₂.trans hprod₁
  dsimp [crossAC]
  nlinarith [sq_pos_of_pos hs]

theorem delta_pos : 0 < delta := by
  have heq : delta = (4 * alpha * gamma - crossAC^2) / (4 * alpha) := by
    unfold delta
    field_simp [alpha_pos.ne']
  rw [heq]
  exact div_pos blockDet_pos (mul_pos (by norm_num) alpha_pos)

private theorem reduced_complete (A B C : ℝ) :
    alpha * A^2 + beta * B^2 + gamma * C^2 + crossAB * A * B +
      crossAC * A * C + crossBC * B * C =
    alpha * (A + (crossAB * B + crossAC * C) / (2 * alpha))^2 +
      delta * (C + residualBC * B / (2 * delta))^2 + kappa * B^2 := by
  have ha := alpha_pos.ne'
  have hg : gamma = delta + crossAC^2 / (4 * alpha) := by
    unfold delta
    ring
  rw [hg]
  unfold kappa residualBC
  field_simp [ha, delta_pos.ne']
  ring

/-- Four positive squares expose the sole possible negative sample direction. -/
theorem curvatureAtTwo_eq_four_squares (f : ℝ → ℝ) :
    curvatureAtTwo f =
      (7 * Real.log 2 * Real.log 3 / 72) *
        (sampleDelta f (4/3) - 2 * sampleDelta f (2/3))^2 +
      (5 * Real.log 2 * Real.log 3 / 72) *
        (sampleDelta f (3/2) - 2 * sampleDelta f (1/2))^2 +
      alpha * (sampleDelta f 1 +
        (crossAB * sampleDelta f (2/3) + crossAC * sampleDelta f (1/2)) / (2 * alpha))^2 +
      delta * (sampleDelta f (1/2) + residualBC * sampleDelta f (2/3) / (2 * delta))^2 +
      kappa * (sampleDelta f (2/3))^2 := by
  rw [curvatureAtTwo_eq_reduced]
  have h := reduced_complete (sampleDelta f 1) (sampleDelta f (2/3)) (sampleDelta f (1/2))
  linarith

/-- Exact rank-one lower bound, with no independent curvature premise. -/
theorem curvatureAtTwo_ge_rankOne (f : ℝ → ℝ) :
    -penalty * (sampleDelta f (2/3))^2 ≤ curvatureAtTwo f := by
  obtain ⟨hl, hm, _⟩ := log_bounds
  have hα := alpha_pos
  have hδ := delta_pos
  rw [curvatureAtTwo_eq_four_squares]
  dsimp only [penalty]
  have h₁ : 0 ≤ (7 * Real.log 2 * Real.log 3 / 72) *
      (sampleDelta f (4/3) - 2 * sampleDelta f (2/3))^2 := by positivity
  have h₂ : 0 ≤ (5 * Real.log 2 * Real.log 3 / 72) *
      (sampleDelta f (3/2) - 2 * sampleDelta f (1/2))^2 := by positivity
  have h₃ := mul_nonneg hα.le (sq_nonneg
    (sampleDelta f 1 + (crossAB * sampleDelta f (2/3) + crossAC * sampleDelta f (1/2)) / (2 * alpha)))
  have h₄ := mul_nonneg hδ.le (sq_nonneg
    (sampleDelta f (1/2) + residualBC * sampleDelta f (2/3) / (2 * delta)))
  linarith

theorem penalty_pos : 0 < penalty := by
  have h := curvatureAtTwo_ge_rankOne witness
  have hn : curvatureAtTwo witness < 0 := gammaTwo_witness_neg
  by_contra hp
  have hp' : penalty ≤ 0 := le_of_not_gt hp
  have : 0 ≤ -penalty * (sampleDelta witness (2/3))^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- Equal samples at `log(2/3)` and `log 2` eliminate every negative curvature direction. -/
theorem curvatureAtTwo_nonneg_of_sample_eq (f : ℝ → ℝ)
    (h : f (Real.log (2/3)) = f (Real.log 2)) : 0 ≤ curvatureAtTwo f := by
  simpa [sampleDelta, h] using curvatureAtTwo_ge_rankOne f

private theorem four_squares_zero_iff (w₁ w₂ w₃ w₄ A B C D : ℝ)
    (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃) (h₄ : 0 < w₄) :
    w₁*A^2 + w₂*B^2 + w₃*C^2 + w₄*D^2 = 0 ↔
      A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hn₁ := mul_nonneg h₁.le (sq_nonneg A)
  have hn₂ := mul_nonneg h₂.le (sq_nonneg B)
  have hn₃ := mul_nonneg h₃.le (sq_nonneg C)
  have hn₄ := mul_nonneg h₄.le (sq_nonneg D)
  constructor
  · intro h
    have hz₁ : w₁*A^2 = 0 := le_antisymm (by linarith) hn₁
    have hz₂ : w₂*B^2 = 0 := le_antisymm (by linarith) hn₂
    have hz₃ : w₃*C^2 = 0 := le_antisymm (by linarith) hn₃
    have hz₄ : w₄*D^2 = 0 := le_antisymm (by linarith) hn₄
    exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp hz₁).resolve_left h₁.ne'),
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hz₂).resolve_left h₂.ne'),
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hz₃).resolve_left h₃.ne'),
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hz₄).resolve_left h₄.ne')⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ring

private theorem sum_last_eq_zero (X r : ℝ) : X + r = r ↔ X = 0 := by
  constructor <;> intro h <;> linarith

/-- Complete equality classification for the optimal compensated curvature. -/
theorem curvatureAtTwo_eq_rankOne_iff (f : ℝ → ℝ) :
    curvatureAtTwo f = -penalty * (sampleDelta f (2/3))^2 ↔
      sampleDelta f (4/3) = 2 * sampleDelta f (2/3) ∧
      sampleDelta f (3/2) = 2 * sampleDelta f (1/2) ∧
      sampleDelta f 1 +
        (crossAB * sampleDelta f (2/3) + crossAC * sampleDelta f (1/2)) / (2 * alpha) = 0 ∧
      sampleDelta f (1/2) + residualBC * sampleDelta f (2/3) / (2 * delta) = 0 := by
  obtain ⟨hl, hm, _⟩ := log_bounds
  rw [curvatureAtTwo_eq_four_squares]
  dsimp only [penalty]
  simp only [neg_neg]
  rw [sum_last_eq_zero,
    four_squares_zero_iff _ _ _ _ _ _ _ _ (by positivity) (by positivity) alpha_pos delta_pos]
  constructor
  · rintro ⟨hD, hE, hA, hC⟩
    exact ⟨by linarith, by linarith, hA, hC⟩
  · rintro ⟨hD, hE, hA, hC⟩
    exact ⟨by linarith, by linarith, hA, hC⟩

/-- On the repaired sector, zero curvature is exactly constancy on all six samples. -/
theorem curvatureAtTwo_flat_zero_iff (f : ℝ → ℝ) :
    sampleDelta f (2/3) = 0 ∧ curvatureAtTwo f = 0 ↔
      ∀ q ∈ ({1/2, 2/3, 1, 4/3, 3/2, 2} : Finset ℝ),
        f (Real.log q) = f (Real.log 2) := by
  constructor
  · rintro ⟨hB, hzero⟩
    have heq : curvatureAtTwo f = -penalty * (sampleDelta f (2/3))^2 := by simp [hzero, hB]
    obtain ⟨hD, hE, hA, hC⟩ := (curvatureAtTwo_eq_rankOne_iff f).mp heq
    have hC₀ : sampleDelta f (1/2) = 0 := by
      simpa only [hB, mul_zero, zero_div, add_zero] using hC
    have hA₀ : sampleDelta f 1 = 0 := by
      simpa only [hB, hC₀, mul_zero, zero_add, zero_div, add_zero] using hA
    have hD₀ : sampleDelta f (4/3) = 0 := by simpa only [hB, mul_zero] using hD
    have hE₀ : sampleDelta f (3/2) = 0 := by simpa only [hC₀, mul_zero] using hE
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp [sampleDelta] at hC₀; linarith
    · dsimp [sampleDelta] at hB; linarith
    · dsimp [sampleDelta] at hA₀; linarith
    · dsimp [sampleDelta] at hD₀; linarith
    · dsimp [sampleDelta] at hE₀; linarith
    · rfl
  · intro h
    have hd : ∀ q ∈ ({1/2, 2/3, 1, 4/3, 3/2, 2} : Finset ℝ), sampleDelta f q = 0 := by
      intro q hq
      simp [sampleDelta, h q hq]
    have hA := hd 1 (by simp)
    have hB := hd (2/3) (by simp)
    have hC := hd (1/2) (by simp)
    have hD := hd (4/3) (by simp)
    have hE := hd (3/2) (by simp)
    refine ⟨hB, ?_⟩
    rw [curvatureAtTwo_eq_four_squares]
    simp only [hA, hB, hC, hD, hE, mul_zero, add_zero, zero_div, pow_two, sub_self]

end RHTower.PrimeCurvatureRankOne
