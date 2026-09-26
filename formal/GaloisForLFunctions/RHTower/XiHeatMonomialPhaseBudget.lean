import GaloisForLFunctions.RHTower.XiHeatThirdVanishingDebt
import GaloisForLFunctions.HTGeometry.MonomialHeatPhaseDefect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Vanishing phase budgets for every Xi monomial degree

Each heat-scaled monomial has a phase debt controlled by two scaled positive
norm moments. Their dominated-convergence limits give a vanishing budget at
every degree. This is the degree-independent construction behind finite
polynomial coefficient-uniform phase control.
-/

namespace RHTower
noncomputable section
open Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

def xiHeatMonomialAmplitude (n : ℕ) (τ : ℝ) (q : XiZeroCopy) : ℂ :=
  let z := (Real.exp τ : ℂ) * xiSpectralPoint q ^ 2
  heatPhaseAmplitude (z ^ n) 1 z

theorem xiHeatMonomialAmplitude_norm_sq (n : ℕ) (τ : ℝ) (q : XiZeroCopy) :
    ‖xiHeatMonomialAmplitude n τ q‖ ^ 2 =
      (Real.exp τ) ^ (2 * n) * (‖xiSpectralPoint q ^ 2‖ ^ (2 * n) *
        Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))) := by
  rw [xiHeatMonomialAmplitude, heatPhaseAmplitude_norm_sq]
  simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos τ), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, one_mul]
  rw [← pow_mul, Nat.mul_comm n 2, mul_pow]
  ring

theorem summable_xiHeatMonomialAmplitude_im_sq (n : ℕ) (τ : ℝ) :
    Summable (fun q => (xiHeatMonomialAmplitude n τ q).im ^ 2) := by
  have hn : Summable (fun q => ‖xiHeatMonomialAmplitude n τ q‖ ^ 2) := by
    simpa only [xiHeatMonomialAmplitude_norm_sq] using
      (summable_xiHeatNormMoment (2 * n) τ).mul_left ((Real.exp τ) ^ (2 * n))
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun _ => heatPhaseAmplitude_im_sq_le_norm_sq _ _ _) hn

def xiHeatMonomialPhaseBudget : ℕ → ℝ → ℝ
  | 0, τ => (Real.exp τ) ^ 2 * xiHeatNormMoment 1 τ
  | n + 1, τ =>
      4 * (n + 1 : ℝ) ^ 2 * (Real.exp τ) ^ (2 * n + 2) * xiHeatNormMoment (2 * n + 1) τ +
        (Real.exp τ) ^ (2 * n + 4) * xiHeatNormMoment (2 * n + 3) τ

theorem xiHeatMonomialPhaseBudget_nonneg (n : ℕ) (τ : ℝ) :
    0 ≤ xiHeatMonomialPhaseBudget n τ := by
  cases n with
  | zero =>
    exact mul_nonneg (sq_nonneg _) (xiHeatNormMoment_nonneg 1 τ)
  | succ n =>
    have h1 := xiHeatNormMoment_nonneg (2 * n + 1) τ
    have h3 := xiHeatNormMoment_nonneg (2 * n + 3) τ
    dsimp [xiHeatMonomialPhaseBudget]
    positivity

theorem xiHeatMonomialPhaseBudget_tendsto_zero (n : ℕ) :
    Tendsto (xiHeatMonomialPhaseBudget n) atBot (𝓝 0) := by
  cases n with
  | zero => exact xiHeatNormMoment_scaled_tendsto_zero 1
  | succ n =>
    have h := ((xiHeatNormMoment_scaled_tendsto_zero (2 * n + 1)).const_mul
      (4 * (n + 1 : ℝ) ^ 2)).add (xiHeatNormMoment_scaled_tendsto_zero (2 * n + 3))
    simp only [mul_zero, zero_add] at h
    convert h using 1
    ext τ
    dsimp [xiHeatMonomialPhaseBudget]
    simp only [Nat.add_assoc]
    ring

theorem xiHeatMonomialAmplitude_zero_debt_bound (τ : ℝ) (q : XiZeroCopy) :
    2 * (xiHeatMonomialAmplitude 0 τ q).im ^ 2 ≤
      (Real.exp τ) ^ 2 * (‖xiSpectralPoint q ^ 2‖ *
        Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))) := by
  let z := xiSpectralPoint q ^ 2
  have h := heatPhaseAmplitude_im_sq_bound (1 : ℂ) 1 ((Real.exp τ : ℂ) * z)
  simp only [Complex.one_im, Complex.one_re, zero_pow (by omega : 2 ≠ 0), one_pow,
    mul_zero, zero_add, mul_one, one_mul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at h
  have hs := mul_le_mul_of_nonneg_left (xiSpectralSq_im_sq_le_norm q)
    (show 0 ≤ (Real.exp τ) ^ 2 * Real.exp (-(Real.exp τ * z.re)) by positivity)
  change 2 * (heatPhaseAmplitude (1 : ℂ) 1 ((Real.exp τ : ℂ) * z)).im ^ 2 ≤ _
  dsimp only [z] at h hs ⊢
  nlinarith only [h, hs]

theorem xiHeatMonomialAmplitude_succ_debt_bound (n : ℕ) (τ : ℝ) (q : XiZeroCopy) :
    2 * (xiHeatMonomialAmplitude (n + 1) τ q).im ^ 2 ≤
      4 * (n + 1 : ℝ) ^ 2 * (Real.exp τ) ^ (2 * n + 2) *
        (‖xiSpectralPoint q ^ 2‖ ^ (2 * n + 1) *
          Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))) +
      (Real.exp τ) ^ (2 * n + 4) *
        (‖xiSpectralPoint q ^ 2‖ ^ (2 * n + 3) *
          Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))) := by
  let t := Real.exp τ
  let z := xiSpectralPoint q ^ 2
  have ht : 0 < t := Real.exp_pos _
  have h := monomialHeatPhaseDebt_bound n 1 ((t : ℂ) * z)
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, one_mul, one_pow, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow] at h
  have hs := mul_le_mul_of_nonneg_left (xiSpectralSq_im_sq_le_norm q)
    (show 0 ≤ Real.exp (-(t * z.re)) * t ^ 2 *
      (4 * (n + 1 : ℝ) ^ 2 * (t ^ (2 * n) * ‖z‖ ^ (2 * n)) +
        t ^ (2 * (n + 1)) * ‖z‖ ^ (2 * (n + 1))) by positivity)
  calc
    2 * (xiHeatMonomialAmplitude (n + 1) τ q).im ^ 2 ≤
        Real.exp (-(t * z.re)) * (t ^ 2 * z.im ^ 2) *
          (4 * (n + 1 : ℝ) ^ 2 * (t ^ (2 * n) * ‖z‖ ^ (2 * n)) +
            t ^ (2 * (n + 1)) * ‖z‖ ^ (2 * (n + 1))) := by
      simpa only [xiHeatMonomialAmplitude, t, z, mul_pow] using h
    _ ≤ Real.exp (-(t * z.re)) * (t ^ 2 * ‖z‖) *
          (4 * (n + 1 : ℝ) ^ 2 * (t ^ (2 * n) * ‖z‖ ^ (2 * n)) +
            t ^ (2 * (n + 1)) * ‖z‖ ^ (2 * (n + 1))) := by
      nlinarith only [hs]
    _ = _ := by
      dsimp [t, z]
      simp only [Nat.mul_add, Nat.mul_one, pow_add]
      ring

/-- Actual monomial phase debt is bounded at every degree by a vanishing scalar. -/
theorem xiHeatMonomialPhaseDebt_le_budget (n : ℕ) (τ : ℝ) :
    2 * ∑' q, (xiHeatMonomialAmplitude n τ q).im ^ 2 ≤
      xiHeatMonomialPhaseBudget n τ := by
  cases n with
  | zero =>
    have hs : Summable (fun q : XiZeroCopy => (Real.exp τ) ^ 2 *
        (‖xiSpectralPoint q ^ 2‖ * Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re)))) := by
      simpa only [pow_one] using
        (summable_xiHeatNormMoment 1 τ).mul_left ((Real.exp τ) ^ 2)
    have h := Summable.tsum_le_tsum (xiHeatMonomialAmplitude_zero_debt_bound τ)
      ((summable_xiHeatMonomialAmplitude_im_sq 0 τ).mul_left 2)
      hs
    simpa only [tsum_mul_left, xiHeatMonomialPhaseBudget, xiHeatNormMoment, pow_one] using h
  | succ n =>
    have hs1 := (summable_xiHeatNormMoment (2 * n + 1) τ).mul_left
      (4 * (n + 1 : ℝ) ^ 2 * (Real.exp τ) ^ (2 * n + 2))
    have hs3 := (summable_xiHeatNormMoment (2 * n + 3) τ).mul_left
      ((Real.exp τ) ^ (2 * n + 4))
    have h := Summable.tsum_le_tsum (xiHeatMonomialAmplitude_succ_debt_bound n τ)
      ((summable_xiHeatMonomialAmplitude_im_sq (n + 1) τ).mul_left 2) (hs1.add hs3)
    rw [Summable.tsum_add hs1 hs3] at h
    simpa only [tsum_mul_left, xiHeatMonomialPhaseBudget, xiHeatNormMoment, mul_assoc] using h

theorem xiHeatMonomialPhaseDebt_tendsto_zero (n : ℕ) :
    Tendsto (fun τ => 2 * ∑' q, (xiHeatMonomialAmplitude n τ q).im ^ 2) atBot (𝓝 0) :=
  squeeze_zero (fun _ => mul_nonneg (by positivity) (tsum_nonneg fun _ => sq_nonneg _))
    (xiHeatMonomialPhaseDebt_le_budget n) (xiHeatMonomialPhaseBudget_tendsto_zero n)

def xiHeatFinitePhaseBudget (N : ℕ) (τ : ℝ) : ℝ :=
  ∑ j : Fin N, xiHeatMonomialPhaseBudget j τ

def xiHeatFinitePhaseDebt {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) : ℝ :=
  2 * ∑' q, (∑ j, a j * (xiHeatMonomialAmplitude j τ q).im) ^ 2

theorem xiHeatFinitePhaseBudget_tendsto_zero (N : ℕ) :
    Tendsto (xiHeatFinitePhaseBudget N) atBot (𝓝 0) := by
  change Tendsto (fun τ => ∑ j : Fin N, xiHeatMonomialPhaseBudget j τ) atBot (𝓝 0)
  have h := tendsto_finsetSum Finset.univ
    (fun (j : Fin N) _ => xiHeatMonomialPhaseBudget_tendsto_zero j)
  simpa only [Finset.sum_const_zero] using h

/-- Full polynomial phase debt has a vanishing majorant uniform in its coefficient vector. -/
theorem xiHeatFinitePhaseDebt_le_budget {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    xiHeatFinitePhaseDebt a τ ≤ (∑ j, a j ^ 2) * xiHeatFinitePhaseBudget N τ := by
  classical
  let A := ∑ j, a j ^ 2
  let f : XiZeroCopy → ℝ := fun q => ∑ j : Fin N, (xiHeatMonomialAmplitude j τ q).im ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpoint (q : XiZeroCopy) :
      (∑ j, a j * (xiHeatMonomialAmplitude j τ q).im) ^ 2 ≤ A * f q := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a
      (fun j : Fin N => (xiHeatMonomialAmplitude j τ q).im)
  have hs : Summable f := summable_sum fun j _ => summable_xiHeatMonomialAmplitude_im_sq j τ
  have hl : Summable (fun q => (∑ j, a j * (xiHeatMonomialAmplitude j τ q).im) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint (hs.mul_left A)
  have h := Summable.tsum_le_tsum hpoint hl (hs.mul_left A)
  rw [tsum_mul_left] at h
  have he : (∑' q, f q) = ∑ j : Fin N, ∑' q, (xiHeatMonomialAmplitude j τ q).im ^ 2 := by
    exact Summable.tsum_finsetSum (fun j _ => summable_xiHeatMonomialAmplitude_im_sq j τ)
  rw [he] at h
  have hb : 2 * (∑ j : Fin N, ∑' q, (xiHeatMonomialAmplitude j τ q).im ^ 2) ≤
      xiHeatFinitePhaseBudget N τ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => xiHeatMonomialPhaseDebt_le_budget j τ)
  have hm := mul_le_mul_of_nonneg_left hb hA
  unfold xiHeatFinitePhaseDebt
  change 2 * _ ≤ A * _
  nlinarith only [h, hm]

end
end RHTower
