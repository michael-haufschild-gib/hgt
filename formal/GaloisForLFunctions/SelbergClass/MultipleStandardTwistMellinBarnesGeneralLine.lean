import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversionGeneralLine
import GaloisForLFunctions.SelbergClass.MultipleStandardTwistMellinBarnes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# General-line Mellin--Barnes formula for multiple standard twists

This module proves the initial-domain Mellin--Barnes formula on every positive
vertical line.  The shifted Dirichlet-series convergence condition supplies the
summable coefficient majorant required for the sum--integral interchange.
It contains no continuation or contour-shift statement.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.SelbergClass

/-- The vertical Mellin--Barnes line with real part `c`. -/
noncomputable def multipleStandardTwistMellinBarnesGeneralLine (c t : ℝ) : ℂ :=
  (c : ℂ) + (t : ℂ) * I

/-- Shifting each Dirichlet variable by the real part of the Mellin line. -/
noncomputable def multipleStandardTwistMellinBarnesShift {N : ℕ}
    (κ : Fin N → ℝ) (c : ℝ) (s : Fin N → ℂ) : Fin N → ℂ :=
  fun i => s i + (κ i * c : ℝ)

/-- One summand of the general-line Mellin--Barnes integrand. -/
noncomputable def multipleStandardTwistMellinBarnesGeneralLineTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X c : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) (t : ℝ) : ℂ :=
  (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
    (multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)) ^
      (-multipleStandardTwistMellinBarnesGeneralLine c t) *
    Complex.Gamma (multipleStandardTwistMellinBarnesGeneralLine c t)

/-- The general-line Mellin--Barnes integrand after summing over all indices. -/
noncomputable def multipleStandardTwistMellinBarnesGeneralLineIntegrand {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X c : ℝ)
    (s : Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑' n : Fin N → ℕ+,
    multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t

/-- The positive-index factor on a line `Re w = c` exactly shifts the
absolute Dirichlet weight by `κᵢ c` in each coordinate. -/
theorem norm_multipleStandardTwistCoefficient_mul_indexPower_neg_eq
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ)
    (α c : ℝ) (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    ‖(∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i)))‖ *
        (multipleIndexPower κ n) ^ (-c) =
      ‖multipleStandardTwistTerm a κ α
        (multipleStandardTwistMellinBarnesShift κ c s) n‖ := by
  have hnpos : ∀ i, (0 : ℝ) < ((n i : ℕ) : ℝ) := by
    intro i
    exact_mod_cast (n i).property
  have hP : (multipleIndexPower κ n) ^ (-c) =
      ∏ i, (((n i : ℕ) : ℝ) ^ κ i) ^ (-c) := by
    unfold multipleIndexPower
    induction (Finset.univ : Finset (Fin N)) using Finset.cons_induction with
    | empty => simp
    | cons i u hi ih =>
      rw [Finset.prod_cons, Real.mul_rpow]
      · rw [ih]
        rw [Finset.prod_cons]
      · positivity
      · exact Finset.prod_nonneg fun j hj => Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [hP, multipleStandardTwistTerm, norm_mul, norm_prod, norm_multipleStandardTwistPhase]
  simp only [mul_one]
  rw [norm_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [norm_mul, norm_mul]
  have hnormLeft : ‖(((n i : ℕ) : ℂ) ^ (-s i))‖ =
      ((n i : ℕ) : ℝ) ^ (-(s i).re) := by
    exact GaloisForLFunctions.norm_cpow_neg_eq_rpow_re
      ((n i : ℕ) : ℝ) (hnpos i) (s i)
  have hnormRight : ‖(((n i : ℕ) : ℂ) ^
      (-(multipleStandardTwistMellinBarnesShift κ c s i)) )‖ =
      ((n i : ℕ) : ℝ) ^
        (-(multipleStandardTwistMellinBarnesShift κ c s i).re) := by
    exact GaloisForLFunctions.norm_cpow_neg_eq_rpow_re
      ((n i : ℕ) : ℝ) (hnpos i)
      (multipleStandardTwistMellinBarnesShift κ c s i)
  rw [hnormLeft, hnormRight]
  rw [← Real.rpow_mul (Nat.cast_nonneg _)]
  calc
    ‖a i (n i : ℕ)‖ * ((n i : ℕ) : ℝ) ^ (-(s i).re) *
          ((n i : ℕ) : ℝ) ^ (κ i * -c) =
        ‖a i (n i : ℕ)‖ *
          (((n i : ℕ) : ℝ) ^ (-(s i).re) *
            ((n i : ℕ) : ℝ) ^ (κ i * -c)) := by ring
    _ = ‖a i (n i : ℕ)‖ *
          ((n i : ℕ) : ℝ) ^ ((-(s i).re) + κ i * -c) := by
        rw [← Real.rpow_add (hnpos i)]
    _ = ‖a i (n i : ℕ)‖ *
          ((n i : ℕ) : ℝ) ^
            (-(multipleStandardTwistMellinBarnesShift κ c s i).re) := by
        congr 2
        simp [multipleStandardTwistMellinBarnesShift]
        ring

/-- Termwise Mellin inversion on an arbitrary positive vertical line. -/
theorem dampedMultipleStandardTwistTerm_eq_smul_integral_mellinBarnesGeneralLine
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X c : ℝ}
    (hα : 0 < α) (hX : 0 < X) (hc : 0 < c)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    dampedMultipleStandardTwistTerm a κ α X s n =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t := by
  let A : ℂ := ∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))
  let z : ℂ := multipleTwistDampingParameter α X
  let P : ℝ := multipleIndexPower κ n
  let W : ℝ → ℂ := multipleStandardTwistMellinBarnesGeneralLine c
  have hzre : 0 < (z * (P : ℂ)).re := by
    dsimp only [z, P]
    exact re_multipleTwistDampingParameter_mul_indexPower_pos κ hα hX n
  have hExp : Complex.exp (-z * (P : ℂ)) =
      complexMellinInvLine c Complex.Gamma (z * (P : ℂ)) := by
    rw [complexMellinInvLine_Gamma_eq_exp_neg hc hzre]
    congr 1
    ring
  rw [dampedMultipleStandardTwistTerm]
  change A * Complex.exp (-z * (P : ℂ)) = _
  rw [hExp]
  unfold complexMellinInvLine
  change A * ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
      (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) = _
  calc
    A * ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) =
        (1 / (2 * Real.pi) : ℝ) •
          (A * ∫ t : ℝ, (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) := by
            rw [Complex.real_smul, Complex.real_smul]
            ring
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        A * ((z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) := by
          rw [MeasureTheory.integral_const_mul]
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t := by
          congr 2
          funext t
          dsimp only [A, z, P, W,
            multipleStandardTwistMellinBarnesGeneralLineTerm]
          ring

/-- General-line Mellin--Barnes majorant in the shifted initial domain. -/
theorem norm_multipleStandardTwistMellinBarnesGeneralLineTerm_le
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) (t : ℝ) :
    ‖multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t‖ ≤
      (‖multipleTwistDampingParameter α X‖ ^ (-c) *
        ‖multipleStandardTwistTerm a κ α
          (multipleStandardTwistMellinBarnesShift κ c s) n‖) *
        (‖Complex.Gamma (multipleStandardTwistMellinBarnesGeneralLine c t)‖ *
          Real.exp (|Complex.arg (multipleTwistDampingParameter α X)| * |t|) *
            (1 + |t|)) := by
  let z : ℂ := multipleTwistDampingParameter α X
  let P : ℝ := multipleIndexPower κ n
  let W : ℝ → ℂ := multipleStandardTwistMellinBarnesGeneralLine c
  let A : ℂ := ∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))
  have hPone : 1 ≤ P := by
    dsimp [P]
    unfold multipleIndexPower
    apply Finset.one_le_prod
    intro i hi
    apply Real.one_le_rpow
    · exact_mod_cast (n i).property
    · exact (hκ i).le
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hPone
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
  have hnorm : ‖z * (P : ℂ)‖ = ‖z‖ * P := by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hPpos.le]
  have hpow : ‖z * (P : ℂ)‖ ^ (-c) = ‖z‖ ^ (-c) * P ^ (-c) := by
    rw [hnorm, Real.mul_rpow (norm_nonneg _) hPpos.le]
  have hshift : ‖A‖ * P ^ (-c) =
      ‖multipleStandardTwistTerm a κ α
        (multipleStandardTwistMellinBarnesShift κ c s) n‖ := by
    simpa only [A, P] using
      norm_multipleStandardTwistCoefficient_mul_indexPower_neg_eq a κ α c s n
  have hcp : ‖(z * (P : ℂ)) ^ (-W t)‖ ≤
      ‖z * (P : ℂ)‖ ^ (-c) *
        Real.exp (|Complex.arg (z * (P : ℂ))| * |t|) := by
    simpa only [W, multipleStandardTwistMellinBarnesGeneralLine] using
      norm_cpow_neg_line_add_mul_I_le c (z * (P : ℂ)) hzP t
  change ‖A * (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    ‖A‖ * ‖(z * (P : ℂ)) ^ (-W t)‖ * ‖Complex.Gamma (W t)‖ ≤
        ‖A‖ *
          (‖z * (P : ℂ)‖ ^ (-c) *
            Real.exp (|Complex.arg (z * (P : ℂ))| * |t|)) *
          ‖Complex.Gamma (W t)‖ := by
            gcongr
    _ = ‖A‖ *
          ((‖z‖ ^ (-c) * P ^ (-c)) *
            Real.exp (|Complex.arg z| * |t|)) *
          ‖Complex.Gamma (W t)‖ := by rw [hpow, harg]
    _ = (‖z‖ ^ (-c) * (‖A‖ * P ^ (-c))) *
          (‖Complex.Gamma (W t)‖ *
            Real.exp (|Complex.arg z| * |t|)) := by ring
    _ = (‖z‖ ^ (-c) *
          ‖multipleStandardTwistTerm a κ α
            (multipleStandardTwistMellinBarnesShift κ c s) n‖) *
          (‖Complex.Gamma (W t)‖ *
            Real.exp (|Complex.arg z| * |t|)) := by rw [hshift]
    _ ≤ (‖z‖ ^ (-c) *
          ‖multipleStandardTwistTerm a κ α
            (multipleStandardTwistMellinBarnesShift κ c s) n‖) *
          (‖Complex.Gamma (W t)‖ *
            Real.exp (|Complex.arg z| * |t|) * (1 + |t|)) := by
          have hlin : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
          have hleft : 0 ≤ ‖z‖ ^ (-c) *
              ‖multipleStandardTwistTerm a κ α
                (multipleStandardTwistMellinBarnesShift κ c s) n‖ := by positivity
          have hright : 0 ≤ ‖Complex.Gamma (W t)‖ *
              Real.exp (|Complex.arg z| * |t|) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hlin hright]
    _ = _ := by
          dsimp only [z, W]

/-- Every general-line Mellin--Barnes term is integrable on the real contour. -/
theorem integrable_multipleStandardTwistMellinBarnesGeneralLineTerm
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X) (hc : 0 < c)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    Integrable (fun t : ℝ =>
      multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t) := by
  let z : ℂ := multipleTwistDampingParameter α X
  let P : ℝ := multipleIndexPower κ n
  let W : ℝ → ℂ := multipleStandardTwistMellinBarnesGeneralLine c
  let A : ℂ := ∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))
  let G : ℝ → ℝ := fun t =>
    ‖Complex.Gamma (W t)‖ * Real.exp (|Complex.arg z| * |t|) * (1 + |t|)
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
    simpa only [multipleStandardTwistMellinBarnesGeneralLine] using
      integrable_norm_Gamma_line_mul_exp_abs_mul_one_add_abs hc (abs_nonneg _) htheta
  have hPpos : 0 < P := by
    dsimp [P]
    unfold multipleIndexPower
    exact Finset.prod_pos fun i hi =>
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
    · dsimp only [W, multipleStandardTwistMellinBarnesGeneralLine]
      fun_prop
    · exact Or.inl hzP
  have hgamma : Continuous (fun t : ℝ => Complex.Gamma (W t)) := by
    simpa only [W, multipleStandardTwistMellinBarnesGeneralLine] using
      continuous_Gamma_line_of_pos hc
  have hcont : Continuous (fun t : ℝ =>
      A * (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) :=
    (continuous_const.mul hpow).mul hgamma
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t) volume := by
    change AEStronglyMeasurable (fun t : ℝ =>
      A * (z * (P : ℂ)) ^ (-W t) * Complex.Gamma (W t)) volume
    exact hcont.aestronglyMeasurable
  refine Integrable.mono'
    (hG.const_mul (‖z‖ ^ (-c) *
      ‖multipleStandardTwistTerm a κ α
        (multipleStandardTwistMellinBarnesShift κ c s) n‖))
    hmeas ?_
  filter_upwards with t
  simpa only [G, z, P, W, multipleStandardTwistMellinBarnesGeneralLine] using
    norm_multipleStandardTwistMellinBarnesGeneralLineTerm_le
      a κ hκ hα hX s n t

/-- The general-line Mellin--Barnes terms have summable `L¹` norms when every
shifted coordinate Dirichlet series converges absolutely. -/
theorem summable_integral_norm_multipleStandardTwistMellinBarnesGeneralLineTerm
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X) (hc : 0 < c)
    (s : Fin N → ℂ)
    (ha : ∀ i, LSeriesSummable (a i)
      (multipleStandardTwistMellinBarnesShift κ c s i)) :
    Summable (fun n : Fin N → ℕ+ => ∫ t : ℝ,
      ‖multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t‖) := by
  let z : ℂ := multipleTwistDampingParameter α X
  let W : ℝ → ℂ := multipleStandardTwistMellinBarnesGeneralLine c
  let G : ℝ → ℝ := fun t =>
    ‖Complex.Gamma (W t)‖ * Real.exp (|Complex.arg z| * |t|) * (1 + |t|)
  let B : (Fin N → ℕ+) → ℝ := fun n =>
    ‖multipleStandardTwistTerm a κ α
      (multipleStandardTwistMellinBarnesShift κ c s) n‖
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
    simpa only [multipleStandardTwistMellinBarnesGeneralLine] using
      integrable_norm_Gamma_line_mul_exp_abs_mul_one_add_abs hc (abs_nonneg _) htheta
  have hB : Summable B := by
    simpa only [B] using
      summable_norm_multipleStandardTwistTerm_of_lSeries a κ α
        (multipleStandardTwistMellinBarnesShift κ c s) ha
  have hmajor : Summable (fun n : Fin N → ℕ+ =>
      (‖z‖ ^ (-c) * J) * B n) :=
    hB.mul_left (‖z‖ ^ (-c) * J)
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := integrable_multipleStandardTwistMellinBarnesGeneralLineTerm
    a κ hκ hα hX hc s n
  have hdom : Integrable (fun t : ℝ =>
      (‖z‖ ^ (-c) * B n) * G t) :=
    hG.const_mul (‖z‖ ^ (-c) * B n)
  calc
    (∫ t : ℝ,
        ‖multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t‖) ≤
        ∫ t : ℝ, (‖z‖ ^ (-c) * B n) * G t := by
          apply integral_mono_ae hterm.norm hdom
          filter_upwards with t
          simpa only [B, G, z, W, multipleStandardTwistMellinBarnesGeneralLine] using
            norm_multipleStandardTwistMellinBarnesGeneralLineTerm_le
              a κ hκ hα hX s n t
    _ = (‖z‖ ^ (-c) * J) * B n := by
          rw [MeasureTheory.integral_const_mul]
          dsimp only [J]
          ring

/-- Initial-domain sum--integral interchange on an arbitrary positive
Mellin--Barnes line. -/
theorem dampedMultipleStandardTwist_eq_smul_integral_mellinBarnesGeneralLine_of_lSeries
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hα : 0 < α) (hX : 0 < X) (hc : 0 < c)
    (s : Fin N → ℂ)
    (ha : ∀ i, LSeriesSummable (a i)
      (multipleStandardTwistMellinBarnesShift κ c s i)) :
    dampedMultipleStandardTwist a κ α X s =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesGeneralLineIntegrand a κ α X c s t := by
  let F : (Fin N → ℕ+) → ℝ → ℂ := fun n t =>
    multipleStandardTwistMellinBarnesGeneralLineTerm a κ α X c s n t
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    simpa only [F] using
      integrable_multipleStandardTwistMellinBarnesGeneralLineTerm
        a κ hκ hα hX hc s n
  have hFsum : Summable (fun n : Fin N → ℕ+ => ∫ t : ℝ, ‖F n t‖) := by
    simpa only [F] using
      summable_integral_norm_multipleStandardTwistMellinBarnesGeneralLineTerm
        a κ hκ hα hX hc s ha
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFsum
  calc
    dampedMultipleStandardTwist a κ α X s =
        ∑' n : Fin N → ℕ+, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, F n t := by
          unfold dampedMultipleStandardTwist
          apply tsum_congr
          intro n
          simpa only [F] using
            dampedMultipleStandardTwistTerm_eq_smul_integral_mellinBarnesGeneralLine
              a κ hα hX hc s n
    _ = (1 / (2 * Real.pi) : ℝ) • ∑' n : Fin N → ℕ+, ∫ t : ℝ, F n t := by
          exact tsum_const_smul'' (g := (1 / (2 * Real.pi) : ℝ))
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, ∑' n : Fin N → ℕ+, F n t := by
          rw [hswap]
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesGeneralLineIntegrand a κ α X c s t := by
          rfl

/-- Concrete general-line Mellin--Barnes formula in the exact shifted
initial domain of a multiple standard twist. -/
theorem MultipleStandardTwistData.damped_eq_smul_integral_mellinBarnes_generalLine
    {N : ℕ} (D : MultipleStandardTwistData N) {X c : ℝ}
    (hX : 0 < X) (hc : 0 < c) (s : Fin N → ℂ)
    (hs : ∀ i, 1 < (s i).re + D.kappa i * c) :
    D.damped X s =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesGeneralLineIntegrand
          D.coeff D.kappa D.alpha X c s t := by
  simpa only [MultipleStandardTwistData.damped,
    multipleStandardTwistMellinBarnesShift, Complex.add_re,
    Complex.ofReal_re] using
    dampedMultipleStandardTwist_eq_smul_integral_mellinBarnesGeneralLine_of_lSeries
      D.coeff D.kappa D.kappa_pos D.alpha_pos hX hc s
      (fun i => (D.factors i).lSeriesSummable
        (multipleStandardTwistMellinBarnesShift D.kappa c s i) (hs i))

/-- A positive initial Mellin line that satisfies every shifted absolute
convergence inequality simultaneously. -/
noncomputable def multipleStandardTwistInitialLine {N : ℕ}
    (κ : Fin N → ℝ) (s : Fin N → ℂ) : ℝ :=
  1 + ∑ j, max 0 ((2 - (s j).re) / κ j)

theorem multipleStandardTwistInitialLine_pos {N : ℕ}
    (κ : Fin N → ℝ) (s : Fin N → ℂ) :
    0 < multipleStandardTwistInitialLine κ s := by
  have hsum : 0 ≤ ∑ j, max 0 ((2 - (s j).re) / κ j) := by
    apply Finset.sum_nonneg
    intro j hj
    exact le_max_left _ _
  unfold multipleStandardTwistInitialLine
  linarith

theorem one_lt_re_add_kappa_mul_multipleStandardTwistInitialLine
    {N : ℕ} (κ : Fin N → ℝ) (hκ : ∀ i, 0 < κ i)
    (s : Fin N → ℂ) (i : Fin N) :
    1 < (s i).re + κ i * multipleStandardTwistInitialLine κ s := by
  let q : Fin N → ℝ := fun j => max 0 ((2 - (s j).re) / κ j)
  have hq : ∀ j, 0 ≤ q j := by
    intro j
    exact le_max_left _ _
  have hsum : q i ≤ ∑ j, q j := by
    exact Finset.single_le_sum (fun j hj => hq j) (Finset.mem_univ _)
  have hline : 1 + q i ≤ multipleStandardTwistInitialLine κ s := by
    dsimp [multipleStandardTwistInitialLine, q]
    linarith
  have hqdiv : (2 - (s i).re) / κ i ≤ q i := by
    exact le_max_right _ _
  have hqmul : 2 - (s i).re ≤ κ i * q i := by
    rw [← mul_comm]
    exact (div_le_iff₀ (hκ i)).mp hqdiv
  have hmul : κ i * (1 + q i) ≤
      κ i * multipleStandardTwistInitialLine κ s := by
    exact mul_le_mul_of_nonneg_left hline (hκ i).le
  have hbase : 1 < (s i).re + κ i * (1 + q i) := by
    nlinarith [hκ i]
  linarith

/-- The general-line formula is available at the explicit common starting
line for every point of the multivariable parameter space. -/
theorem MultipleStandardTwistData.damped_eq_smul_integral_mellinBarnes_initialLine
    {N : ℕ} (D : MultipleStandardTwistData N) {X : ℝ}
    (hX : 0 < X) (s : Fin N → ℂ) :
    D.damped X s =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        multipleStandardTwistMellinBarnesGeneralLineIntegrand D.coeff D.kappa D.alpha X
          (multipleStandardTwistInitialLine D.kappa s) s t := by
  apply D.damped_eq_smul_integral_mellinBarnes_generalLine hX
    (multipleStandardTwistInitialLine_pos D.kappa s) s
  intro i
  exact one_lt_re_add_kappa_mul_multipleStandardTwistInitialLine
    D.kappa D.kappa_pos s i

end GaloisForLFunctions.SelbergClass
