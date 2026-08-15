import GaloisForLFunctions.SelbergClass.MultipleStandardTwistMellinBarnes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Initial-domain Mellin--Barnes Fubini formula for multiple standard twists

This module closes the sum--integral interchange in the initial absolute
convergence domain of the damped multiple standard twist.  Its only majorant
uses the original absolutely summable coefficient series and the existing
integrable Gamma envelope.  It supplies neither a continuation nor an
unbounded regular-part trace.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.SelbergClass

noncomputable def multipleStandardTwistMellinBarnesLine (t : ℝ) : ℂ :=
  (2 : ℂ) + (t : ℂ) * I

noncomputable def multipleStandardTwistMellinBarnesTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) (t : ℝ) : ℂ :=
  (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
    (multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)) ^
      (-multipleStandardTwistMellinBarnesLine t) *
    Complex.Gamma (multipleStandardTwistMellinBarnesLine t)

noncomputable def multipleStandardTwistMellinBarnesIntegrand {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑' n : Fin N → ℕ+,
    multipleStandardTwistMellinBarnesTerm a κ α X s n t

theorem one_le_multipleIndexPower {N : ℕ} (κ : Fin N → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (n : Fin N → ℕ+) :
    1 ≤ multipleIndexPower κ n := by
  unfold multipleIndexPower
  apply Finset.one_le_prod
  intro i hi
  apply Real.one_le_rpow
  · exact_mod_cast (n i).property
  · exact hκ i

/-- Coarse initial-domain Mellin--Barnes majorant.  Positivity of the indices
makes the damping index power at least one, so no shifted coefficient series is
needed. -/
theorem norm_multipleStandardTwistMellinBarnesTerm_le
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) (t : ℝ) :
    ‖multipleStandardTwistMellinBarnesTerm a κ α X s n t‖ ≤
      (‖multipleTwistDampingParameter α X‖ ^ (-2 : ℝ) *
        ‖multipleStandardTwistTerm a κ α s n‖) *
        (‖Complex.Gamma (multipleStandardTwistMellinBarnesLine t)‖ *
          Real.exp (|Complex.arg (multipleTwistDampingParameter α X)| * |t|) *
            (2 + |t|)) := by
  let z : ℂ := multipleTwistDampingParameter α X
  let P : ℝ := multipleIndexPower κ n
  let W : ℝ → ℂ := multipleStandardTwistMellinBarnesLine
  have hPpos : 0 < P := by
    dsimp [P]
    unfold multipleIndexPower
    exact Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos (by exact_mod_cast (n i).property) _
  have hPone : 1 ≤ P := by
    exact one_le_multipleIndexPower κ (fun i => (hκ i).le) n
  have hzre : 0 < z.re := by
    dsimp [z, multipleTwistDampingParameter]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    norm_num
    positivity
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at hzre
    simp at hzre
  have hzP : z * (P : ℂ) ≠ 0 := by
    intro hzero
    have hre : 0 < (z * (P : ℂ)).re := by
      simpa only [z, P] using
        re_multipleTwistDampingParameter_mul_indexPower_pos κ hα hX n
    rw [hzero] at hre
    simp at hre
  have harg : |Complex.arg (z * (P : ℂ))| = |Complex.arg z| := by
    simpa using congrArg abs (Complex.arg_mul_real hPpos z)
  have hnormmono : ‖z‖ ≤ ‖z * (P : ℂ)‖ := by
    calc
      ‖z‖ = ‖z‖ * 1 := by ring
      _ ≤ ‖z‖ * P := mul_le_mul_of_nonneg_left hPone (norm_nonneg _)
      _ = ‖z * (P : ℂ)‖ := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg hPpos.le]
  have hpow : ‖z * (P : ℂ)‖ ^ (-2 : ℝ) ≤ ‖z‖ ^ (-2 : ℝ) := by
    exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) hnormmono (by norm_num)
  have hcp :
      ‖(z * (P : ℂ)) ^ (-W t)‖ ≤
        ‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|) := by
    calc
      ‖(z * (P : ℂ)) ^ (-W t)‖ ≤
          ‖z * (P : ℂ)‖ ^ (-2 : ℝ) *
            Real.exp (|Complex.arg (z * (P : ℂ))| * |t|) := by
              simpa only [W, multipleStandardTwistMellinBarnesLine] using
                norm_cpow_neg_two_add_mul_I_le (z * (P : ℂ)) hzP t
      _ = ‖z * (P : ℂ)‖ ^ (-2 : ℝ) *
            Real.exp (|Complex.arg z| * |t|) := by rw [harg]
      _ ≤ ‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|) := by
            exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
  have hA :
      ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))‖ =
        ‖multipleStandardTwistTerm a κ α s n‖ := by
    simp [multipleStandardTwistTerm, norm_multipleStandardTwistPhase]
  change ‖(∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
      (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))‖ *
          ‖(z * (P : ℂ)) ^ (-W t)‖ * ‖Complex.Gamma (W t)‖ ≤
        ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))‖ *
          (‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|)) *
            ‖Complex.Gamma (W t)‖ := by
          gcongr
    _ = (‖z‖ ^ (-2 : ℝ) * ‖multipleStandardTwistTerm a κ α s n‖) *
          (‖Complex.Gamma (W t)‖ * Real.exp (|Complex.arg z| * |t|)) := by
          rw [hA]
          ring
    _ ≤ (‖z‖ ^ (-2 : ℝ) * ‖multipleStandardTwistTerm a κ α s n‖) *
          (‖Complex.Gamma (W t)‖ * Real.exp (|Complex.arg z| * |t|) *
            (2 + |t|)) := by
          have hlin : 1 ≤ 2 + |t| := by linarith [abs_nonneg t]
          have hleft : 0 ≤ ‖z‖ ^ (-2 : ℝ) *
              ‖multipleStandardTwistTerm a κ α s n‖ := by positivity
          have hright : 0 ≤ ‖Complex.Gamma (W t)‖ *
              Real.exp (|Complex.arg z| * |t|) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hlin hright]
    _ = _ := by
          dsimp only [z, W]

/-- Every Mellin--Barnes term is integrable on the real contour. -/
theorem integrable_multipleStandardTwistMellinBarnesTerm
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    Integrable (fun t : ℝ =>
      multipleStandardTwistMellinBarnesTerm a κ α X s n t) := by
  let z : ℂ := multipleTwistDampingParameter α X
  let P : ℝ := multipleIndexPower κ n
  let W : ℝ → ℂ := multipleStandardTwistMellinBarnesLine
  let G : ℝ → ℝ := fun t =>
    ‖Complex.Gamma (W t)‖ * Real.exp (|Complex.arg z| * |t|) * (2 + |t|)
  have hzre : 0 < z.re := by
    dsimp [z, multipleTwistDampingParameter]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    norm_num
    positivity
  have htheta : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
  have hG : Integrable G := by
    dsimp only [G, W]
    simpa only [multipleStandardTwistMellinBarnesLine] using
      integrable_norm_Gamma_two_mul_exp_abs_mul_linear (abs_nonneg _) htheta
  have hPpos : 0 < P := by
    dsimp [P]
    unfold multipleIndexPower
    exact Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos (by exact_mod_cast (n i).property) _
  have hzP : z * (P : ℂ) ≠ 0 := by
    intro hzero
    have hre : 0 < (z * (P : ℂ)).re := by
      simpa only [z, P] using
        re_multipleTwistDampingParameter_mul_indexPower_pos κ hα hX n
    rw [hzero] at hre
    simp at hre
  have hpow : Continuous (fun t : ℝ => (z * (P : ℂ)) ^ (-W t)) := by
    apply Continuous.const_cpow
    · dsimp only [W, multipleStandardTwistMellinBarnesLine]
      fun_prop
    · exact Or.inl hzP
  have hgamma : Continuous (fun t : ℝ => Complex.Gamma (W t)) := by
    simpa only [W, multipleStandardTwistMellinBarnesLine] using
      RHTower.Sieve.continuous_Gamma_two_line
  have hcont : Continuous (fun t : ℝ =>
      (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
        (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) :=
    (continuous_const.mul hpow).mul hgamma
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      multipleStandardTwistMellinBarnesTerm a κ α X s n t) volume := by
    change AEStronglyMeasurable (fun t : ℝ =>
      (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
        (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) volume
    exact hcont.aestronglyMeasurable
  refine Integrable.mono'
    (hG.const_mul (‖z‖ ^ (-2 : ℝ) * ‖multipleStandardTwistTerm a κ α s n‖))
    hmeas ?_
  filter_upwards with t
  simpa only [G, z, W, multipleStandardTwistMellinBarnesLine] using
    norm_multipleStandardTwistMellinBarnesTerm_le a κ hκ hα hX s n t

/-- The Mellin--Barnes terms have summable `L¹` norms in the original absolute
convergence domain. -/
theorem summable_integral_norm_multipleStandardTwistMellinBarnesTerm
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) (ha : ∀ i, LSeriesSummable (a i) (s i)) :
    Summable (fun n : Fin N → ℕ+ => ∫ t : ℝ,
      ‖multipleStandardTwistMellinBarnesTerm a κ α X s n t‖) := by
  let z : ℂ := multipleTwistDampingParameter α X
  let W : ℝ → ℂ := multipleStandardTwistMellinBarnesLine
  let G : ℝ → ℝ := fun t =>
    ‖Complex.Gamma (W t)‖ * Real.exp (|Complex.arg z| * |t|) * (2 + |t|)
  let B : (Fin N → ℕ+) → ℝ := fun n =>
    ‖multipleStandardTwistTerm a κ α s n‖
  let J : ℝ := ∫ t : ℝ, G t
  have hzre : 0 < z.re := by
    dsimp [z, multipleTwistDampingParameter]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    norm_num
    positivity
  have htheta : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
  have hG : Integrable G := by
    dsimp only [G, W]
    simpa only [multipleStandardTwistMellinBarnesLine] using
      integrable_norm_Gamma_two_mul_exp_abs_mul_linear (abs_nonneg _) htheta
  have hB : Summable B := by
    simpa only [B] using
      summable_norm_multipleStandardTwistTerm_of_lSeries a κ α s ha
  have hmajor : Summable (fun n : Fin N → ℕ+ =>
      (‖z‖ ^ (-2 : ℝ) * J) * B n) :=
    hB.mul_left (‖z‖ ^ (-2 : ℝ) * J)
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := integrable_multipleStandardTwistMellinBarnesTerm
    a κ hκ hα hX s n
  have hdom : Integrable (fun t : ℝ =>
      (‖z‖ ^ (-2 : ℝ) * B n) * G t) :=
    hG.const_mul (‖z‖ ^ (-2 : ℝ) * B n)
  calc
    (∫ t : ℝ, ‖multipleStandardTwistMellinBarnesTerm a κ α X s n t‖) ≤
        ∫ t : ℝ, (‖z‖ ^ (-2 : ℝ) * B n) * G t := by
          apply integral_mono_ae hterm.norm hdom
          filter_upwards with t
          simpa only [B, G, z, W, multipleStandardTwistMellinBarnesLine] using
            norm_multipleStandardTwistMellinBarnesTerm_le a κ hκ hα hX s n t
    _ = (‖z‖ ^ (-2 : ℝ) * J) * B n := by
          rw [MeasureTheory.integral_const_mul]
          dsimp only [J]
          ring

/-- Termwise Mellin inversion rewritten as a scalar multiple of the real-line
integral used by the Fubini theorem. -/
theorem dampedMultipleStandardTwistTerm_eq_smul_integral_mellinBarnes
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    dampedMultipleStandardTwistTerm a κ α X s n =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesTerm a κ α X s n t := by
  let A : ℂ := ∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))
  let K : ℝ → ℂ := fun t =>
    (multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)) ^
      (-multipleStandardTwistMellinBarnesLine t) *
    Complex.Gamma (multipleStandardTwistMellinBarnesLine t)
  rw [dampedMultipleStandardTwistTerm_eq_complexMellinInvTwo_Gamma a κ hα hX s n]
  unfold complexMellinInvTwo
  change A * ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, K t) = _
  calc
    A * ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, K t) =
        (1 / (2 * Real.pi) : ℝ) • (A * ∫ t : ℝ, K t) := by
          rw [Complex.real_smul, Complex.real_smul]
          ring
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, A * K t := by
          rw [MeasureTheory.integral_const_mul]
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesTerm a κ α X s n t := by
          congr 2
          funext t
          dsimp only [A, K, multipleStandardTwistMellinBarnesTerm]
          ring

/-- Initial-domain sum--integral interchange for the damped multiple standard
twist. -/
theorem dampedMultipleStandardTwist_eq_smul_integral_mellinBarnes_of_lSeries
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) (ha : ∀ i, LSeriesSummable (a i) (s i)) :
    dampedMultipleStandardTwist a κ α X s =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesIntegrand a κ α X s t := by
  let F : (Fin N → ℕ+) → ℝ → ℂ := fun n t =>
    multipleStandardTwistMellinBarnesTerm a κ α X s n t
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    simpa only [F] using
      integrable_multipleStandardTwistMellinBarnesTerm a κ hκ hα hX s n
  have hFsum : Summable (fun n : Fin N → ℕ+ => ∫ t : ℝ, ‖F n t‖) := by
    simpa only [F] using
      summable_integral_norm_multipleStandardTwistMellinBarnesTerm
        a κ hκ hα hX s ha
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFsum
  calc
    dampedMultipleStandardTwist a κ α X s =
        ∑' n : Fin N → ℕ+, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, F n t := by
          unfold dampedMultipleStandardTwist
          apply tsum_congr
          intro n
          simpa only [F] using
            dampedMultipleStandardTwistTerm_eq_smul_integral_mellinBarnes
              a κ hα hX s n
    _ = (1 / (2 * Real.pi) : ℝ) • ∑' n : Fin N → ℕ+, ∫ t : ℝ, F n t := by
          exact tsum_const_smul'' (g := (1 / (2 * Real.pi) : ℝ))
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, ∑' n : Fin N → ℕ+, F n t := by
          rw [hswap]
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesIntegrand a κ α X s t := by
          rfl

/-- Concrete initial-domain Fubini formula for source-faithful multiple-twist
data. -/
theorem MultipleStandardTwistData.damped_eq_smul_integral_mellinBarnes
    {N : ℕ} (D : MultipleStandardTwistData N) {X : ℝ} (hX : 0 < X)
    (s : Fin N → ℂ) (hs : ∀ i, 1 < (s i).re) :
    D.damped X s =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesIntegrand D.coeff D.kappa D.alpha X s t := by
  simpa only [MultipleStandardTwistData.damped] using
    dampedMultipleStandardTwist_eq_smul_integral_mellinBarnes_of_lSeries
      D.coeff D.kappa D.kappa_pos D.alpha_pos hX s
      (fun i => (D.factors i).lSeriesSummable (s i) (hs i))

end GaloisForLFunctions.SelbergClass
