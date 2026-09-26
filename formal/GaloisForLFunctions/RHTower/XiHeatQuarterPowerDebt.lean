import GaloisForLFunctions.RHTower.XiHeatMonomialPhaseBudget
import GaloisForLFunctions.RHTower.XiThreeHalvesSummability

/-!
# A quantitative common heat-time modulus for Xi phase debt

Three-halves summability of the actual Xi divisor improves the qualitative
vanishing norm-moment bounds to an explicit quarter-power rate. The same
time factor serves every degree; all degree dependence is in stated constants.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

def xiHeatThreeHalvesMass : ℝ :=
  ∑' q : XiZeroCopy, 1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)

theorem xiHeatThreeHalvesMass_nonneg : 0 ≤ xiHeatThreeHalvesMass :=
  tsum_nonneg fun _ => by positivity

def xiHeatQuarterPowerConstant (k : ℕ) : ℝ := ((4 * k + 3).factorial : ℝ) + 1

theorem xiHeatQuarterPowerConstant_pos (k : ℕ) : 0 < xiHeatQuarterPowerConstant k := by
  unfold xiHeatQuarterPowerConstant
  positivity

/-- An explicit common quarter-power rate, pointwise on the actual divisor. -/
theorem xiHeatNormMoment_quarter_atom_le (k : ℕ) (τ : ℝ) (q : XiZeroCopy) :
    (Real.exp τ) ^ (k + 1) *
        (‖xiSpectralPoint q ^ 2‖ ^ k *
          Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))) ≤
      xiHeatQuarterPowerConstant k * Real.exp (τ / 4) *
        (1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) := by
  let t := Real.exp τ
  let A := ‖xiSpectralPoint q‖
  let u := (xiSpectralPoint q ^ 2).re
  let F : ℝ := ((4 * k + 3).factorial : ℝ)
  let C := xiHeatQuarterPowerConstant k
  have ht : 0 < t := Real.exp_pos τ
  have hA : 0 < A := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hsector : A ^ 2 < 2 * u := by
    simpa only [A, u, Complex.sq_norm] using xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hF : 0 < F := by dsimp [F]; positivity
  have hC : 0 < C := xiHeatQuarterPowerConstant_pos k
  have hC1 : 1 ≤ C := by
    dsimp [C, xiHeatQuarterPowerConstant]
    have hf := Nat.cast_nonneg (α := ℝ) (4 * k + 3).factorial
    linarith
  have hFC : F ≤ C ^ 4 :=
    (show F ≤ C by dsimp [F, C, xiHeatQuarterPowerConstant]; linarith).trans
      (le_self_pow₀ hC1 (by omega))
  have hpoly : (t * A ^ 2) ^ (4 * k + 3) ≤ Real.exp (t * A ^ 2) * F := by
    exact (div_le_iff₀ hF).mp
      (Real.pow_div_factorial_le_exp (t * A ^ 2) (by positivity) (4 * k + 3))
  have hprod : (t * A ^ 2) ^ (4 * k + 3) * Real.exp (-(t * A ^ 2)) ≤ F := by
    calc
      _ ≤ (Real.exp (t * A ^ 2) * F) * Real.exp (-(t * A ^ 2)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = F := by rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hdecay : Real.exp (-(4 * (t * u))) ≤ Real.exp (-(t * A ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hu : 0 < u := by nlinarith only [hsector, sq_nonneg A]
    have hm := mul_le_mul_of_nonneg_left hsector.le ht.le
    nlinarith only [hm, mul_pos ht hu]
  have hbound := (mul_le_mul_of_nonneg_left hdecay
    (show 0 ≤ (t * A ^ 2) ^ (4 * k + 3) by positivity)).trans hprod
  have hscaled := mul_le_mul_of_nonneg_left (hbound.trans hFC) ht.le
  let V := t ^ (k + 1) * (A ^ (2 * k) * Real.exp (-(t * u)))
  have hsqrt : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
  have hexp : Real.exp (-(t * u)) ^ 4 = Real.exp (-(4 * (t * u))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have htime : Real.exp (τ / 4) ^ 4 = t := by
    rw [← Real.exp_nat_mul]
    dsimp [t]
    congr 1
    ring
  have hid : (V * (A * Real.sqrt A)) ^ 4 =
      t * ((t * A ^ 2) ^ (4 * k + 3) * Real.exp (-(4 * (t * u)))) := by
    dsimp [V]
    simp only [mul_pow, pow_add, pow_mul]
    rw [hexp]
    have hsqrt4 : Real.sqrt A ^ 4 = A ^ 2 := by
      calc _ = ((Real.sqrt A) ^ 2) ^ 2 := by ring
           _ = _ := by rw [hsqrt]
    rw [hsqrt4]
    ring
  have hfour : (V * (A * Real.sqrt A)) ^ 4 ≤ (C * Real.exp (τ / 4)) ^ 4 := by
    rw [hid, mul_pow C (Real.exp (τ / 4)) 4, htime]
    simpa only [mul_comm] using hscaled
  have hroot : V * (A * Real.sqrt A) ≤ C * Real.exp (τ / 4) :=
    (pow_le_pow_iff_left₀ (by dsimp [V]; positivity) (by positivity) (by omega)).mp hfour
  have hfinal := (le_div_iff₀ (mul_pos hA (Real.sqrt_pos.2 hA))).mpr hroot
  simpa only [V, t, A, u, C, norm_pow, ← pow_mul, div_eq_mul_inv, one_div, one_mul] using hfinal

/-- Every normalized actual norm moment has a certified explicit heat-time rate. -/
theorem xiHeatNormMoment_scaled_le_quarter (k : ℕ) (τ : ℝ) :
    (Real.exp τ) ^ (k + 1) * xiHeatNormMoment k τ ≤
      xiHeatQuarterPowerConstant k * Real.exp (τ / 4) * xiHeatThreeHalvesMass := by
  have h := Summable.tsum_le_tsum (xiHeatNormMoment_quarter_atom_le k τ)
    ((summable_xiHeatNormMoment k τ).mul_left ((Real.exp τ) ^ (k + 1)))
    (xiSpectralPoint_inv_three_halves_summable.mul_left
      (xiHeatQuarterPowerConstant k * Real.exp (τ / 4)))
  simpa only [tsum_mul_left, xiHeatNormMoment, xiHeatThreeHalvesMass] using h

def xiHeatMonomialQuarterConstant : ℕ → ℝ
  | 0 => xiHeatQuarterPowerConstant 1
  | n + 1 => 4 * (n + 1 : ℝ) ^ 2 * xiHeatQuarterPowerConstant (2 * n + 1) +
      xiHeatQuarterPowerConstant (2 * n + 3)

def xiHeatFiniteQuarterConstant (N : ℕ) : ℝ :=
  ∑ j : Fin N, xiHeatMonomialQuarterConstant j

theorem xiHeatMonomialQuarterConstant_nonneg (n : ℕ) :
    0 ≤ xiHeatMonomialQuarterConstant n := by
  cases n with
  | zero => exact (xiHeatQuarterPowerConstant_pos 1).le
  | succ n =>
    have h1 := (xiHeatQuarterPowerConstant_pos (2 * n + 1)).le
    have h3 := (xiHeatQuarterPowerConstant_pos (2 * n + 3)).le
    dsimp only [xiHeatMonomialQuarterConstant]
    positivity

theorem xiHeatFiniteQuarterConstant_nonneg (N : ℕ) : 0 ≤ xiHeatFiniteQuarterConstant N :=
  Finset.sum_nonneg fun _ _ => xiHeatMonomialQuarterConstant_nonneg _

theorem xiHeatMonomialPhaseBudget_le_quarter (n : ℕ) (τ : ℝ) :
    xiHeatMonomialPhaseBudget n τ ≤
      xiHeatMonomialQuarterConstant n * Real.exp (τ / 4) * xiHeatThreeHalvesMass := by
  cases n with
  | zero => exact xiHeatNormMoment_scaled_le_quarter 1 τ
  | succ n =>
    have h1 := mul_le_mul_of_nonneg_left (xiHeatNormMoment_scaled_le_quarter (2 * n + 1) τ)
      (show 0 ≤ 4 * (n + 1 : ℝ) ^ 2 by positivity)
    have h3 := xiHeatNormMoment_scaled_le_quarter (2 * n + 3) τ
    dsimp only [xiHeatMonomialPhaseBudget, xiHeatMonomialQuarterConstant]
    calc
      _ = 4 * (n + 1 : ℝ) ^ 2 *
          ((Real.exp τ) ^ (2 * n + 2) * xiHeatNormMoment (2 * n + 1) τ) +
          (Real.exp τ) ^ (2 * n + 4) * xiHeatNormMoment (2 * n + 3) τ := by ring
      _ ≤ 4 * (n + 1 : ℝ) ^ 2 *
          (xiHeatQuarterPowerConstant (2 * n + 1) * Real.exp (τ / 4) * xiHeatThreeHalvesMass) +
          xiHeatQuarterPowerConstant (2 * n + 3) * Real.exp (τ / 4) * xiHeatThreeHalvesMass :=
        add_le_add h1 h3
      _ = _ := by ring

/-- One explicit modulus controls every finite-degree budget simultaneously. -/
theorem xiHeatFinitePhaseBudget_le_quarter (N : ℕ) (τ : ℝ) :
    xiHeatFinitePhaseBudget N τ ≤
      xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
    xiHeatMonomialPhaseBudget_le_quarter j τ)
  simpa only [xiHeatFinitePhaseBudget, xiHeatFiniteQuarterConstant,
    Finset.sum_mul] using h

/-- Full coefficient-uniform phase debt with a certified power rate; no cross term is omitted. -/
theorem xiHeatFinitePhaseDebt_le_quarter {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    xiHeatFinitePhaseDebt a τ ≤ (∑ j, a j ^ 2) *
      (xiHeatFiniteQuarterConstant N * Real.exp (τ / 4) * xiHeatThreeHalvesMass) :=
  (xiHeatFinitePhaseDebt_le_budget a τ).trans
    (mul_le_mul_of_nonneg_left (xiHeatFinitePhaseBudget_le_quarter N τ)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end
end RHTower
