import GaloisForLFunctions.RHTower.XiHeatSamplingEnergyBound
import GaloisForLFunctions.RHTower.XiHeatQuadraticSamplingBands
import GaloisForLFunctions.RHTower.XiHeatJointDegreeTimeBound

/-!
# A stronger Xi energy floor from quadratic-radius samples

The full polynomial energy is bounded below using actual Xi nodes in a disk
of radius (N+1)²+1. The complete phase debt retains the certified quarter-power
rate. The resulting joint degree/time region has a positive coefficient-uniform
margin, with no all-time Hankel positivity assertion.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

def xiHeatQuadraticEnergyFloor : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      let N := n + 1
      let M := xiHeatQuadraticSamplingRadius N
      let B : ℝ := 1 + N * M
      let C : ℝ := N.factorial * (B ^ (N - 1)) ^ N
      Real.exp (-M) / ((N : ℝ) ^ 3 * C ^ 2)

theorem xiHeatQuadraticEnergyFloor_pos (N : ℕ) : 0 < xiHeatQuadraticEnergyFloor N := by
  cases N with
  | zero => exact one_pos
  | succ n =>
    have hM := xiHeatQuadraticSamplingRadius_pos (n + 1)
    dsimp [xiHeatQuadraticEnergyFloor]
    positivity

theorem xiHeatQuadraticSamplingRadius_le (N : ℕ) :
    xiHeatQuadraticSamplingRadius N ≤ xiHeatSamplingRadius N := by
  have hpow : (N : ℝ) + 1 ≤ (4 : ℝ) ^ N := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have hp : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by linarith)
      nlinarith only [ih, hp]
  have hp : 1 ≤ (4 : ℝ) ^ N := one_le_pow₀ (by linarith)
  have h3 : (N : ℝ) + 1 ≤ 3 * (4 : ℝ) ^ N := by linarith only [hpow, hp]
  have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 h3
  unfold xiHeatQuadraticSamplingRadius xiHeatSamplingRadius
  linarith only [hs]

/-- The new floor is at least the previously certified exponential-radius floor. -/
theorem xiHeatSamplingEnergyFloor_le_quadratic (N : ℕ) :
    xiHeatSamplingEnergyFloor N ≤ xiHeatQuadraticEnergyFloor N := by
  cases N with
  | zero => exact le_rfl
  | succ n =>
    let N := n + 1
    let M := xiHeatQuadraticSamplingRadius N
    let R := xiHeatSamplingRadius N
    let B : ℝ := 1 + N * M
    let B' : ℝ := 1 + N * R
    let C : ℝ := N.factorial * (B ^ (N - 1)) ^ N
    let C' : ℝ := N.factorial * (B' ^ (N - 1)) ^ N
    have hN : (0 : ℝ) < N := by dsimp [N]; positivity
    have hM : 0 < M := xiHeatQuadraticSamplingRadius_pos N
    have hR : 0 < R := xiHeatSamplingRadius_pos N
    have hB : 0 < B := by dsimp [B]; positivity
    have hB' : 0 < B' := by dsimp [B']; positivity
    have hC : 0 < C := by dsimp [C]; positivity
    have hC' : 0 < C' := by dsimp [C']; positivity
    have hMR : M ≤ R := xiHeatQuadraticSamplingRadius_le N
    have hBB : B ≤ B' := by
      have h := mul_le_mul_of_nonneg_left hMR (Nat.cast_nonneg (α := ℝ) N)
      dsimp only [B, B']
      linarith only [h]
    have hCC : C ≤ C' :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (pow_nonneg hB.le (N - 1))
          (pow_le_pow_left₀ hB.le hBB (N - 1)) N) (Nat.cast_nonneg N.factorial)
    have hden : (N : ℝ) ^ 3 * C ^ 2 ≤ (N : ℝ) ^ 3 * C' ^ 2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ hC.le hC'.le).2 hCC) (by positivity)
    change Real.exp (-R) / ((N : ℝ) ^ 3 * C' ^ 2) ≤
      Real.exp (-M) / ((N : ℝ) ^ 3 * C ^ 2)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hMR)) hden
      (by positivity) (Real.exp_pos _).le

/-- A common heat cutoff gives every order the independent quadratic-radius energy floor. -/
theorem xiHeatFiniteNormEnergy_eventually_quadratic_floor :
    ∀ᶠ τ : ℝ in atBot, ∀ (N : ℕ) (a : Fin N → ℝ),
      xiHeatQuadraticEnergyFloor N * (∑ j, a j ^ 2) ≤ xiHeatFiniteNormEnergy a τ := by
  classical
  filter_upwards [eventually_forall_exists_xiHeat_quadratic_sampling_determinant] with τ hτ N
  cases N with
  | zero =>
    intro a
    simpa using xiHeatFiniteNormEnergy_nonneg a τ
  | succ n =>
    let N := n + 1
    let M := xiHeatQuadraticSamplingRadius N
    let B : ℝ := 1 + N * M
    let C : ℝ := N.factorial * (B ^ (N - 1)) ^ N
    have hN : (0 : ℝ) < N := by dsimp [N]; positivity
    have hM : 0 < M := xiHeatQuadraticSamplingRadius_pos N
    have hB : 0 < B := by dsimp [B]; positivity
    have hC : 0 < C := by dsimp [C]; positivity
    change ∀ a : Fin N → ℝ,
      Real.exp (-M) / ((N : ℝ) ^ 3 * C ^ 2) * (∑ j, a j ^ 2) ≤ xiHeatFiniteNormEnergy a τ
    obtain ⟨q, hq, hdet⟩ := hτ N
    let z : Fin N → ℂ := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
    change (∀ i, ‖z i‖ ≤ M) at hq
    change 1 ≤ ‖(Matrix.vandermonde z).det‖ at hdet
    have hcap : polynomialSamplingCap z ≤ C := by
      have hs : ∑ i, ‖z i‖ ≤ (N : ℝ) * M := by
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
          Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hq i)
      have hscale : phaseFrequencyScale z ≤ B := by
        unfold phaseFrequencyScale
        dsimp [B]
        linarith only [hs]
      have hz0 : 0 ≤ phaseFrequencyScale z := zero_le_one.trans (one_le_phaseFrequencyScale z)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (pow_nonneg hz0 (N - 1))
          (pow_le_pow_left₀ hz0 hscale (N - 1)) N) (Nat.cast_nonneg N.factorial)
    have hweight : ∑ i, Real.exp (z i).re ≤ N * Real.exp M := by
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hq i)))
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
    intro a
    have hK := xiHeatFiniteNormEnergy_nonneg a τ
    have hsample := xiHeatFiniteNormEnergy_sampling_bound a τ q
    change ‖(Matrix.vandermonde z).det‖ ^ 2 * (∑ j, a j ^ 2) ≤
      (N : ℝ) ^ 2 * polynomialSamplingCap z ^ 2 *
        (∑ i, Real.exp (z i).re) * xiHeatFiniteNormEnergy a τ at hsample
    have hcap0 : 0 ≤ polynomialSamplingCap z := by
      unfold polynomialSamplingCap
      positivity [one_le_phaseFrequencyScale z]
    have hupper :
        (N : ℝ) ^ 2 * polynomialSamplingCap z ^ 2 * (∑ i, Real.exp (z i).re) *
          xiHeatFiniteNormEnergy a τ ≤
        ((N : ℝ) ^ 3 * C ^ 2 * Real.exp M) * xiHeatFiniteNormEnergy a τ := by
      apply mul_le_mul_of_nonneg_right _ hK
      calc
        _ ≤ ((N : ℝ) ^ 2 * C ^ 2) * (N * Real.exp M) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hcap0 hC.le).2 hcap) (sq_nonneg (N : ℝ)))
            hweight (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (by positivity)
        _ = _ := by ring
    have hdet2 : 1 ≤ ‖(Matrix.vandermonde z).det‖ ^ 2 := by nlinarith only [hdet]
    have hcoeff : (∑ j, a j ^ 2) ≤
        ((N : ℝ) ^ 3 * C ^ 2 * Real.exp M) * xiHeatFiniteNormEnergy a τ := by
      calc
        _ ≤ ‖(Matrix.vandermonde z).det‖ ^ 2 * (∑ j, a j ^ 2) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hdet2
            (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => sq_nonneg (a j))
        _ ≤ _ := hsample.trans hupper
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < (N : ℝ) ^ 3 * C ^ 2 by positivity)).2
    have hexp : Real.exp (-M) * Real.exp M = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ ≤ Real.exp (-M) * (((N : ℝ) ^ 3 * C ^ 2 * Real.exp M) *
          xiHeatFiniteNormEnergy a τ) := mul_le_mul_of_nonneg_left hcoeff (Real.exp_pos _).le
      _ = (Real.exp (-M) * Real.exp M) *
          (xiHeatFiniteNormEnergy a τ * ((N : ℝ) ^ 3 * C ^ 2)) := by ring
      _ = _ := by rw [hexp, one_mul]

/-- Improved complete-form margin, simultaneous in degree and coefficient vector. -/
theorem xiHeatHankelForm_eventually_quadratic_lower_bound :
    ∀ᶠ τ : ℝ in atBot, ∀ (N : ℕ) (a : Fin N → ℝ),
      (xiHeatQuadraticEnergyFloor N -
        xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass) *
          (∑ j, a j ^ 2) ≤
        xiHeatHankelForm N (xiHeatScaledCoefficients a τ) (Real.exp τ) := by
  filter_upwards [xiHeatFiniteNormEnergy_eventually_quadratic_floor] with τ hK N a
  have hD := xiHeatFinitePhaseDebt_le_quarter a τ
  have hK' := hK N a
  rw [xiHeatHankelForm_scaled_eq_energy_sub_debt]
  nlinarith only [hD, hK']

def xiHeatQuadraticLogTime (N : ℕ) : ℝ :=
  4 * Real.log (xiHeatQuadraticEnergyFloor N / (2 * xiHeatJointDebtConstant N))

/-- The explicit degree-dependent part of the certified time range increases. -/
theorem xiHeatJointLogTime_le_quadratic (N : ℕ) :
    xiHeatJointLogTime N ≤ xiHeatQuadraticLogTime N := by
  have hD : 0 < 2 * xiHeatJointDebtConstant N :=
    mul_pos (by positivity) (xiHeatJointDebtConstant_pos N)
  have h := div_le_div_of_nonneg_right (xiHeatSamplingEnergyFloor_le_quadratic N) hD.le
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (div_pos (xiHeatSamplingEnergyFloor_pos N) hD) h)
    (show (0 : ℝ) ≤ 4 by positivity)

/-- An explicit positive region using the stronger independent energy floor. -/
theorem xiHeatHankelForm_quadratic_degree_time_coercive :
    ∃ τ₀ : ℝ, ∀ (N : ℕ) (τ : ℝ), τ ≤ min τ₀ (xiHeatQuadraticLogTime N) →
      ∀ a : Fin N → ℝ,
        (xiHeatQuadraticEnergyFloor N / 2) * (∑ j, a j ^ 2) ≤
          xiHeatHankelForm N (xiHeatScaledCoefficients a τ) (Real.exp τ) := by
  obtain ⟨τ₀, hτ₀⟩ := eventually_atBot.mp xiHeatHankelForm_eventually_quadratic_lower_bound
  refine ⟨τ₀, ?_⟩
  intro N τ hτ a
  have htime : τ ≤ xiHeatQuadraticLogTime N := hτ.trans (min_le_right _ _)
  have hratio : 0 < xiHeatQuadraticEnergyFloor N / (2 * xiHeatJointDebtConstant N) :=
    div_pos (xiHeatQuadraticEnergyFloor_pos N) (mul_pos (by positivity) (xiHeatJointDebtConstant_pos N))
  have hexp : Real.exp (τ / 4) ≤
      xiHeatQuadraticEnergyFloor N / (2 * xiHeatJointDebtConstant N) := by
    rw [← Real.exp_log hratio]
    apply Real.exp_le_exp.mpr
    dsimp only [xiHeatQuadraticLogTime] at htime
    linarith only [htime]
  have hsmall := (le_div_iff₀
    (mul_pos (show (0 : ℝ) < 2 by positivity) (xiHeatJointDebtConstant_pos N))).mp hexp
  have hdom : xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass ≤
      xiHeatJointDebtConstant N * Real.exp (τ / 4) := by
    dsimp only [xiHeatJointDebtConstant]
    nlinarith only [Real.exp_pos (τ / 4)]
  have hmargin : xiHeatQuadraticEnergyFloor N / 2 ≤ xiHeatQuadraticEnergyFloor N -
      xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass := by
    nlinarith only [hsmall, hdom]
  exact (mul_le_mul_of_nonneg_right hmargin
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
      (hτ₀ τ (hτ.trans (min_le_left _ _)) N a)

end
end RHTower
