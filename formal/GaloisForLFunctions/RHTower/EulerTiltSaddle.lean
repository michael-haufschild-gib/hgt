import GaloisForLFunctions.RHTower.EulerTiltMeanEnergy

/-!
# The source-faithful saddle tilt

The physical multiplier of the Euler-tilted Gibbs source is centred at `log(σ/x)`, while the
Bernoulli mean energy at cutoff `Y` is `μ(σ, Y)`.  The source-faithful tilt is the abscissa where
the two agree.  The mean energy is strictly decreasing in the abscissa and the centre is strictly
increasing, so the tilt equation has at most one solution; the cofactor law then pins the solution
to `1 + 2 log log Y / (log Y)²` up to the stated error.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The saddle defect: Bernoulli mean energy minus the physical logarithmic centre. -/
def eulerTiltSaddleDefect (δ Y x : ℝ) : ℝ :=
  eulerTiltMeanEnergy (1 + δ) Y - Real.log ((1 + δ) / x)

/-! ## Strict monotonicity of the mean energy -/

theorem eulerTiltMeanEnergy_term_strictAnti {p : ℕ} (hp : p.Prime) {σ₁ σ₂ : ℝ}
    (hσ : σ₁ < σ₂) :
    (p : ℝ) ^ (-σ₂) * Real.log p / (1 + (p : ℝ) ^ (-σ₂))
      < (p : ℝ) ^ (-σ₁) * Real.log p / (1 + (p : ℝ) ^ (-σ₁)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have ht2 : (p : ℝ) ^ (-σ₂) < (p : ℝ) ^ (-σ₁) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have ht20 : (0 : ℝ) < (p : ℝ) ^ (-σ₂) := Real.rpow_pos_of_pos hp0 _
  have ht10 : (0 : ℝ) < (p : ℝ) ^ (-σ₁) := Real.rpow_pos_of_pos hp0 _
  have hden2 : (0 : ℝ) < 1 + (p : ℝ) ^ (-σ₂) := by linarith
  have hden1 : (0 : ℝ) < 1 + (p : ℝ) ^ (-σ₁) := by linarith
  rw [div_lt_div_iff₀ hden2 hden1]
  nlinarith [ht2, hlog, ht20, ht10]

/-- **The Bernoulli mean energy is strictly decreasing in the abscissa.** -/
theorem eulerTiltMeanEnergy_strictAnti {Y : ℝ} (hY : 2 ≤ Y) {σ₁ σ₂ : ℝ} (hσ : σ₁ < σ₂) :
    eulerTiltMeanEnergy σ₂ Y < eulerTiltMeanEnergy σ₁ Y := by
  have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hmem : 2 ∈ Nat.primesLE ⌊Y⌋₊ := Nat.mem_primesLE.mpr ⟨hfloor, Nat.prime_two⟩
  have hne : (Nat.primesLE ⌊Y⌋₊).Nonempty := ⟨2, hmem⟩
  rw [eulerTiltMeanEnergy, eulerTiltMeanEnergy]
  refine Finset.sum_lt_sum_of_nonempty hne fun p hp => ?_
  exact eulerTiltMeanEnergy_term_strictAnti (Nat.prime_of_mem_primesLE hp) hσ

/-- **The saddle defect is strictly decreasing in the tilt**, so the tilt equation has at most one
solution. -/
theorem eulerTiltSaddleDefect_strictAnti {Y x : ℝ} (hY : 2 ≤ Y) (hx : 0 < x)
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ : δ₁ < δ₂) :
    eulerTiltSaddleDefect δ₂ Y x < eulerTiltSaddleDefect δ₁ Y x := by
  have henergy : eulerTiltMeanEnergy (1 + δ₂) Y < eulerTiltMeanEnergy (1 + δ₁) Y :=
    eulerTiltMeanEnergy_strictAnti hY (by linarith)
  have hcentre : Real.log ((1 + δ₁) / x) < Real.log ((1 + δ₂) / x) := by
    refine Real.log_lt_log (by positivity) ?_
    exact div_lt_div_of_pos_right (by linarith) hx
  rw [eulerTiltSaddleDefect, eulerTiltSaddleDefect]
  linarith

theorem eulerTiltSaddleDefect_injOn {Y x : ℝ} (hY : 2 ≤ Y) (hx : 0 < x) {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (h₁ : eulerTiltSaddleDefect δ₁ Y x = 0) (h₂ : eulerTiltSaddleDefect δ₂ Y x = 0) :
    δ₁ = δ₂ := by
  rcases lt_trichotomy δ₁ δ₂ with h | h | h
  · have := eulerTiltSaddleDefect_strictAnti hY hx hδ₁ h
    rw [h₁, h₂] at this
    exact absurd this (lt_irrefl 0)
  · exact h
  · have := eulerTiltSaddleDefect_strictAnti hY hx hδ₂ h
    rw [h₁, h₂] at this
    exact absurd this (lt_irrefl 0)

/-! ## The saddle expansion -/

/-- **The tilt equation pins the saddle abscissa.**  Every solution of the tilt equation satisfies
the quantitative cofactor relation `δ (log Y)²/2 = log Y - log(1/x) + O(1 + δ²(log Y)³)`. -/
theorem abs_saddle_sub_cofactor_le {δ Y x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hY : 2 ≤ Y)
    (hx : 0 < x) (hroot : eulerTiltSaddleDefect δ Y x = 0) :
    |δ * Real.log Y ^ 2 / 2 - (Real.log Y - Real.log (1 / x))|
      ≤ eulerTiltEnergyConst + 1 + δ ^ 2 * Real.log Y ^ 3 / 6 := by
  have hlaw := abs_eulerTiltMeanEnergy_sub_expansion_le hδ0 hδ1 hY
  have hcentre : Real.log ((1 + δ) / x) = Real.log (1 + δ) + Real.log (1 / x) := by
    rw [Real.log_div (by linarith) (ne_of_gt hx), Real.log_div one_ne_zero (ne_of_gt hx),
      Real.log_one]
    ring
  have henergy : eulerTiltMeanEnergy (1 + δ) Y = Real.log (1 + δ) + Real.log (1 / x) := by
    have := hroot
    rw [eulerTiltSaddleDefect, hcentre] at this
    linarith
  have hlogδ : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have hlogδ1 : Real.log (1 + δ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + δ by linarith)
    linarith
  rw [henergy] at hlaw
  have hbounds := abs_le.mp hlaw
  rw [abs_le]
  constructor
  · linarith [hbounds.1, hbounds.2]
  · linarith [hbounds.1, hbounds.2]

end

end RHTower
