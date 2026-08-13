import GaloisForLFunctions.RHTower.PolynomialGaussianGlobalCompletedSourceEnvelope
import GaloisForLFunctions.RHTower.XiShiftedFilteredGammaTransmutation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open scoped Real
open Real MeasureTheory Set

noncomputable section

namespace RHTower

def routeUParabolicWedgeCoefficient : ℝ :=
  gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / (2 * Real.pi)

def routeUParabolicGlobalCost : ℝ :=
  (|gammaHardyPhaseRate 0| + routeUVonMangoldtSquareMass + 1) / Real.pi

def routeUParabolicCostRatio : ℝ :=
  4 * routeUParabolicGlobalCost / routeUParabolicWedgeCoefficient

def routeUParabolicEntropyCost : ℝ :=
  Real.log (routeUParabolicCostRatio + 1) + 1

def routeUParabolicDegreeHorizon : ℝ :=
  max 16 (max
    (256 / routeUCompletedPrimeGammaAperture)
    (4 * (10 + routeUParabolicEntropyCost) /
      routeUCompletedPrimeGammaAperture))

theorem routeUParabolicWedgeCoefficient_pos :
    0 < routeUParabolicWedgeCoefficient := by
  exact div_pos gammaHardyPhaseRate_routeUCompletedPrimeGammaRadius_pos
    (mul_pos (by norm_num) Real.pi_pos)

theorem routeUParabolicGlobalCost_pos : 0 < routeUParabolicGlobalCost := by
  apply div_pos _ Real.pi_pos
  have hC := routeUVonMangoldtSquareMass_nonneg
  have hg := abs_nonneg (gammaHardyPhaseRate 0)
  linarith

theorem routeUParabolicCostRatio_pos : 0 < routeUParabolicCostRatio := by
  exact div_pos (mul_pos (by norm_num) routeUParabolicGlobalCost_pos)
    routeUParabolicWedgeCoefficient_pos

theorem routeUParabolicEntropyCost_pos : 0 < routeUParabolicEntropyCost := by
  have hlog : 0 < Real.log (routeUParabolicCostRatio + 1) :=
    Real.log_pos (by linarith [routeUParabolicCostRatio_pos])
  exact add_pos hlog zero_lt_one

theorem routeUParabolicDegreeHorizon_pos : 0 < routeUParabolicDegreeHorizon := by
  exact lt_of_lt_of_le (by norm_num) (le_max_left 16 _)

private theorem routeUParabolic_log_le_div_eight {u : ℝ} (hu : 256 ≤ u) :
    Real.log u ≤ u / 8 := by
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hlog := Real.log_le_rpow_div hu0 (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hsqrtSq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0
  have hsqrt16 : 16 ≤ Real.sqrt u := by
    have hsqrt0 := Real.sqrt_nonneg u
    nlinarith only [hsqrtSq, hsqrt0, hu]
  have hsqrtBound : Real.sqrt u / (1 / 2 : ℝ) ≤ u / 8 := by
    nlinarith only [hsqrtSq, hsqrt16]
  exact le_trans hlog hsqrtBound

private theorem routeUParabolic_power_le_exp
    (d : ℕ) {u : ℝ} (hu : 256 ≤ u) :
    u ^ (2 * d) ≤
      Real.exp (((d + 1 : ℕ) : ℝ) * u / 4) := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hlog := routeUParabolic_log_le_div_eight hu
  have hd : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    norm_num
  calc
    u ^ (2 * d) = (Real.exp (Real.log u)) ^ (2 * d) := by
      rw [Real.exp_log hu0]
    _ = Real.exp (((2 * d : ℕ) : ℝ) * Real.log u) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (((d + 1 : ℕ) : ℝ) * u / 4) := by
      rw [Real.exp_le_exp]
      push_cast
      nlinarith only [hlog, hd, hu0.le]

private theorem routeUParabolic_power_exp_tail_le
    (d : ℕ) {y t : ℝ} (hy : 16 ≤ y) (ht : 0 ≤ t)
    (hu : 256 ≤ y * t / ((d + 1 : ℕ) : ℝ)) :
    t ^ (2 * d) * Real.exp (-((y - 8) * t)) ≤
      (((d + 1 : ℕ) : ℝ) / y) ^ (2 * d) *
        Real.exp (-(y * t / 4)) := by
  let n : ℝ := ((d + 1 : ℕ) : ℝ)
  let u : ℝ := y * t / n
  have hn : 0 < n := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hu256 : 256 ≤ u := by simpa only [u, n] using hu
  have hpower := routeUParabolic_power_le_exp d hu256
  have htEq : t = (n / y) * u := by
    dsimp only [u]
    field_simp [hy0.ne', hn.ne']
  have hnu : n * u = y * t := by
    dsimp only [u]
    field_simp [hn.ne']
  have hexponent :
      n * u / 4 + -((y - 8) * t) ≤ -(y * t / 4) := by
    rw [hnu]
    nlinarith only [hy, ht]
  calc
    t ^ (2 * d) * Real.exp (-((y - 8) * t)) =
        (n / y) ^ (2 * d) *
          (u ^ (2 * d) * Real.exp (-((y - 8) * t))) := by
      rw [htEq, mul_pow]
      ring
    _ ≤ (n / y) ^ (2 * d) *
          (Real.exp (n * u / 4) * Real.exp (-((y - 8) * t))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _))
        (pow_nonneg (div_nonneg hn.le hy0.le) _)
    _ = (n / y) ^ (2 * d) *
          Real.exp (n * u / 4 + -((y - 8) * t)) := by
      rw [Real.exp_add]
    _ ≤ (n / y) ^ (2 * d) * Real.exp (-(y * t / 4)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        (pow_nonneg (div_nonneg hn.le hy0.le) _)
    _ = (((d + 1 : ℕ) : ℝ) / y) ^ (2 * d) *
        Real.exp (-(y * t / 4)) := by rfl

private theorem integral_exp_neg_quarter_mul_Ioi {y : ℝ} (hy : 0 < y) (T : ℝ) :
    (∫ t in Ioi T, Real.exp (-(y * t / 4))) =
      (4 / y) * Real.exp (-(y * T / 4)) := by
  have hb : 0 < y / 4 := div_pos hy (by norm_num)
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-x)) T hb
  rw [integral_exp_neg_Ioi] at h
  simp only [smul_eq_mul] at h
  convert h using 1 <;> field_simp [hy.ne']

private theorem integral_const_Ioc_self_two (s C : ℝ) (hs : 0 ≤ s) :
    (∫ _t in Ioc s (2 * s), C) = s * C := by
  rw [MeasureTheory.setIntegral_const, Measure.real, Real.volume_Ioc]
  rw [show 2 * s - s = s by ring, ENNReal.toReal_ofReal hs, smul_eq_mul]

/-- Native polynomial-Gaussian mass decreases with heat time. -/
theorem routeUPolynomialGaussianMass_antitone
    (Q : Polynomial ℝ) {s t : {τ : ℝ // 0 < τ}} (hst : s.1 ≤ t.1) :
    routeUPolynomialGaussianMass Q t ≤ routeUPolynomialGaussianMass Q s := by
  rw [routeUPolynomialGaussianMass, routeUPolynomialGaussianMass]
  apply MeasureTheory.integral_mono
    (integrable_norm_routeUPolynomialGaussianDensity Q t)
    (integrable_norm_routeUPolynomialGaussianDensity Q s)
  intro x
  simp only [routeUPolynomialGaussianDensity, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Real.exp_le_exp]
  nlinarith only [hst, sq_nonneg x]

/-- Quantitative Xi-trace lower bound throughout the completed ultraviolet wedge. -/
theorem xiPolynomialGaussianHeatTraceReal_ge_parabolicWedgeMass
    (Q : Polynomial ℝ) (t : routeUCompletedPrimeGammaWedge Q) :
    routeUParabolicWedgeCoefficient *
        routeUPolynomialGaussianMass Q t.heat ≤
      xiPolynomialGaussianHeatTraceReal Q t.1 := by
  have hformula := pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma Q t.heat
  have hgap := routeUPolynomialGaussianCompletedPrimeGammaGap_ge Q t
  have hsource := re_routeUPolynomialGaussianPrimeSource_le_absoluteTail Q t.prime
  have hsource' :
      (routeUPolynomialGaussianPrimeSource Q t.heat).re ≤
        routeUPolynomialGaussianPrimeAbsoluteTail Q t.prime := by
    have hheat : t.prime.heat = t.heat := by
      apply Subtype.ext
      rfl
    rw [hheat] at hsource
    exact hsource
  have hpolar : 0 ≤
      2 * Real.pi * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t.1 / 4) := by
    positivity
  have hpi :
      gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 2 *
          routeUPolynomialGaussianMass Q t.heat ≤
        Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := by
    calc
      gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 2 *
          routeUPolynomialGaussianMass Q t.heat ≤
        (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t.heat x‖ *
            gammaHardyPhaseRate x) -
          routeUPolynomialGaussianPrimeAbsoluteTail Q t.prime := hgap
      _ ≤ (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t.heat x‖ *
            gammaHardyPhaseRate x) -
          (routeUPolynomialGaussianPrimeSource Q t.heat).re :=
        sub_le_sub_left hsource' _
      _ ≤ (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t.heat x‖ *
            gammaHardyPhaseRate x) +
          2 * Real.pi * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t.1 / 4) -
            (routeUPolynomialGaussianPrimeSource Q t.heat).re := by
        linarith only [hpolar]
      _ = Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := hformula.symm
  have hmul :
      Real.pi * (routeUParabolicWedgeCoefficient *
          routeUPolynomialGaussianMass Q t.heat) ≤
        Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := by
    calc
      Real.pi * (routeUParabolicWedgeCoefficient *
          routeUPolynomialGaussianMass Q t.heat) =
        gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 2 *
          routeUPolynomialGaussianMass Q t.heat := by
        rw [routeUParabolicWedgeCoefficient]
        field_simp [Real.pi_ne_zero]
      _ ≤ Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := hpi
  exact le_of_mul_le_mul_left hmul Real.pi_pos

/-- Arbitrary-time Xi-trace lower bound with the uniform degree cost used by the parabolic tail. -/
theorem xiPolynomialGaussianHeatTraceReal_ge_neg_parabolicGlobalCost
    (Q : Polynomial ℝ) (d : ℕ) (hdeg : Q.natDegree ≤ d)
    (t : {τ : ℝ // 0 < τ}) :
    -(routeUParabolicGlobalCost *
        Real.exp (8 * ((d : ℝ) + t.1)) *
          routeUPolynomialGaussianMass Q t) ≤
      xiPolynomialGaussianHeatTraceReal Q t.1 := by
  have hglobal := pi_mul_xiPolynomialGaussianHeatTraceReal_ge_globalEnvelope Q t
  have hmass := routeUPolynomialGaussianMass_nonneg Q t
  have hC := routeUVonMangoldtSquareMass_nonneg
  have hdegReal : (Q.natDegree : ℝ) ≤ d := by exact_mod_cast hdeg
  have hexpDegree :
      Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) ≤
        Real.exp (8 * ((d : ℝ) + t.1)) := by
    exact Real.exp_le_exp.mpr (by nlinarith only [hdegReal])
  have hexpOne : 1 ≤ Real.exp (8 * ((d : ℝ) + t.1)) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith only [hd0, t.property]
  have hcoeff :
      -(Real.pi * routeUParabolicGlobalCost *
          Real.exp (8 * ((d : ℝ) + t.1))) ≤
        gammaHardyPhaseRate 0 - routeUVonMangoldtSquareMass *
          Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) := by
    rw [routeUParabolicGlobalCost]
    field_simp [Real.pi_ne_zero]
    have habs := neg_abs_le (gammaHardyPhaseRate 0)
    have hCE := mul_le_mul_of_nonneg_left hexpDegree hC
    nlinarith only [habs, hCE, hexpOne, hC,
      abs_nonneg (gammaHardyPhaseRate 0)]
  have hpi :
      Real.pi * (-(routeUParabolicGlobalCost *
          Real.exp (8 * ((d : ℝ) + t.1)) *
            routeUPolynomialGaussianMass Q t)) ≤
        Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := by
    calc
      Real.pi * (-(routeUParabolicGlobalCost *
          Real.exp (8 * ((d : ℝ) + t.1)) *
            routeUPolynomialGaussianMass Q t)) =
        (-(Real.pi * routeUParabolicGlobalCost *
          Real.exp (8 * ((d : ℝ) + t.1)))) *
            routeUPolynomialGaussianMass Q t := by ring
      _ ≤ (gammaHardyPhaseRate 0 - routeUVonMangoldtSquareMass *
          Real.exp (8 * ((Q.natDegree : ℝ) + t.1))) *
            routeUPolynomialGaussianMass Q t :=
        mul_le_mul_of_nonneg_right hcoeff hmass
      _ ≤ Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := hglobal
  exact le_of_mul_le_mul_left hpi Real.pi_pos

theorem natDegree_xiShiftedReversedPolynomial_le
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) :
    (xiShiftedReversedPolynomial y d c).natDegree ≤ d := by
  rw [xiShiftedReversedPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  rw [Polynomial.natDegree_X_add_C]
  omega

private theorem comp_xiShiftedReversedPolynomial_sub_shift
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) :
    (xiShiftedReversedPolynomial y d c).comp
        (Polynomial.X - Polynomial.C y) =
      ∑ i : Fin (d + 1), Polynomial.C (c i) *
        Polynomial.X ^ (d - (i : ℕ)) := by
  simp [xiShiftedReversedPolynomial]

private theorem coeff_unshiftedReversedPolynomial
    (d : ℕ) (c : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    (∑ j : Fin (d + 1), Polynomial.C (c j) *
        Polynomial.X ^ (d - (j : ℕ))).coeff (d - (i : ℕ)) = c i := by
  classical
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro j _ hji
    have hneq : d - (j : ℕ) ≠ d - (i : ℕ) := by
      intro h
      have hj : (j : ℕ) ≤ d := Nat.lt_succ_iff.mp j.isLt
      have hi : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
      have hnat : (j : ℕ) = (i : ℕ) := by omega
      exact hji (Fin.ext hnat)
    have hneq' : d - (i : ℕ) ≠ d - (j : ℕ) := fun h => hneq h.symm
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hneq']
  · intro hi
    simp at hi

theorem xiShiftedReversedPolynomial_ne_zero
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) (hc : c ≠ 0) :
    xiShiftedReversedPolynomial y d c ≠ 0 := by
  intro hQ
  apply hc
  funext i
  have hcomp := congrArg
    (fun P : Polynomial ℝ => P.comp (Polynomial.X - Polynomial.C y)) hQ
  rw [comp_xiShiftedReversedPolynomial_sub_shift] at hcomp
  simp only [Polynomial.zero_comp] at hcomp
  have hcoeff := congrArg (fun P : Polynomial ℝ => P.coeff (d - (i : ℕ))) hcomp
  rw [coeff_unshiftedReversedPolynomial] at hcoeff
  simpa using hcoeff

private theorem routeUParabolic_exp_neg_entropy_lt_inv :
    Real.exp (-routeUParabolicEntropyCost) <
      1 / (routeUParabolicCostRatio + 1) := by
  have hbase : 0 < routeUParabolicCostRatio + 1 := by
    linarith [routeUParabolicCostRatio_pos]
  have harg :
      -routeUParabolicEntropyCost <
        -Real.log (routeUParabolicCostRatio + 1) := by
    rw [routeUParabolicEntropyCost]
    linarith
  calc
    Real.exp (-routeUParabolicEntropyCost) <
        Real.exp (-Real.log (routeUParabolicCostRatio + 1)) :=
      Real.exp_lt_exp.mpr harg
    _ = 1 / (routeUParabolicCostRatio + 1) := by
      rw [Real.exp_neg, Real.exp_log hbase]
      exact inv_eq_one_div _

theorem routeUParabolic_scalar_gap_pos
    (d : ℕ) {y : ℝ}
    (hy : routeUParabolicDegreeHorizon * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ y) :
    0 < routeUParabolicWedgeCoefficient *
          Real.exp (-2 * ((d + 1 : ℕ) : ℝ)) -
        (4 * routeUParabolicGlobalCost / ((d + 1 : ℕ) : ℝ)) *
          Real.exp (8 * (d : ℝ) -
            y * routeUCompletedPrimeGammaAperture /
              (4 * ((d + 1 : ℕ) : ℝ))) := by
  let n : ℝ := ((d + 1 : ℕ) : ℝ)
  have hn : 0 < n := by positivity
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le d))
  have hA : 0 < routeUCompletedPrimeGammaAperture :=
    routeUCompletedPrimeGammaAperture_pos
  have hK :
      4 * (10 + routeUParabolicEntropyCost) /
          routeUCompletedPrimeGammaAperture ≤
        routeUParabolicDegreeHorizon := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKA :
      4 * (10 + routeUParabolicEntropyCost) ≤
        routeUParabolicDegreeHorizon * routeUCompletedPrimeGammaAperture := by
    exact (div_le_iff₀ hA).mp hK
  have hyn : routeUParabolicDegreeHorizon * n ^ 2 ≤ y := by
    simpa only [n] using hy
  have hcut :
      (10 + routeUParabolicEntropyCost) * n ≤
        y * routeUCompletedPrimeGammaAperture / (4 * n) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hn)]
    have hmul := mul_le_mul_of_nonneg_right hKA (sq_nonneg n)
    have hyA := mul_le_mul_of_nonneg_right hyn hA.le
    nlinarith only [hmul, hyA]
  have hdle : (d : ℝ) ≤ n := by
    simp only [n, Nat.cast_add, Nat.cast_one]
    linarith
  have hexponent :
      8 * (d : ℝ) + 2 * n -
          y * routeUCompletedPrimeGammaAperture / (4 * n) ≤
        -routeUParabolicEntropyCost * n := by
    nlinarith only [hcut, hdle]
  have hentropyNonneg : 0 ≤ routeUParabolicEntropyCost :=
    routeUParabolicEntropyCost_pos.le
  have hnegEntropy :
      -routeUParabolicEntropyCost * n ≤ -routeUParabolicEntropyCost := by
    have := mul_le_mul_of_nonneg_left hn1 hentropyNonneg
    nlinarith only [this]
  have hexp :
      Real.exp (8 * (d : ℝ) + 2 * n -
          y * routeUCompletedPrimeGammaAperture / (4 * n)) ≤
        Real.exp (-routeUParabolicEntropyCost) := by
    exact Real.exp_le_exp.mpr (le_trans hexponent hnegEntropy)
  have hratioInv :
      routeUParabolicCostRatio /
          (routeUParabolicCostRatio + 1) < 1 := by
    exact (div_lt_one (by linarith [routeUParabolicCostRatio_pos])).mpr
      (by linarith)
  have hratioExp :
      routeUParabolicCostRatio *
          Real.exp (-routeUParabolicEntropyCost) < 1 := by
    calc
      routeUParabolicCostRatio *
          Real.exp (-routeUParabolicEntropyCost) <
        routeUParabolicCostRatio *
          (1 / (routeUParabolicCostRatio + 1)) :=
        mul_lt_mul_of_pos_left routeUParabolic_exp_neg_entropy_lt_inv
          routeUParabolicCostRatio_pos
      _ = routeUParabolicCostRatio /
          (routeUParabolicCostRatio + 1) := by ring
      _ < 1 := hratioInv
  have hinvN : 1 / n ≤ 1 := (div_le_one hn).mpr hn1
  have hscaled :
      (routeUParabolicCostRatio / n) *
          Real.exp (8 * (d : ℝ) + 2 * n -
            y * routeUCompletedPrimeGammaAperture / (4 * n)) < 1 := by
    calc
      (routeUParabolicCostRatio / n) *
          Real.exp (8 * (d : ℝ) + 2 * n -
            y * routeUCompletedPrimeGammaAperture / (4 * n)) ≤
        routeUParabolicCostRatio *
          Real.exp (-routeUParabolicEntropyCost) := by
        have hratioN : routeUParabolicCostRatio / n ≤
            routeUParabolicCostRatio := by
          calc
            routeUParabolicCostRatio / n =
                routeUParabolicCostRatio * (1 / n) := by ring
            _ ≤ routeUParabolicCostRatio * 1 :=
              mul_le_mul_of_nonneg_left hinvN routeUParabolicCostRatio_pos.le
            _ = routeUParabolicCostRatio := by ring
        exact mul_le_mul hratioN hexp (Real.exp_nonneg _)
          routeUParabolicCostRatio_pos.le
      _ < 1 := hratioExp
  have hfactor :
      (4 * routeUParabolicGlobalCost / n) *
          Real.exp (8 * (d : ℝ) -
            y * routeUCompletedPrimeGammaAperture / (4 * n)) =
        (routeUParabolicWedgeCoefficient * Real.exp (-2 * n)) *
          ((routeUParabolicCostRatio / n) *
            Real.exp (8 * (d : ℝ) + 2 * n -
              y * routeUCompletedPrimeGammaAperture / (4 * n))) := by
    symm
    calc
      (routeUParabolicWedgeCoefficient * Real.exp (-2 * n)) *
          ((routeUParabolicCostRatio / n) *
            Real.exp (8 * (d : ℝ) + 2 * n -
              y * routeUCompletedPrimeGammaAperture / (4 * n))) =
        (4 * routeUParabolicGlobalCost / n) *
          (Real.exp (-2 * n) *
            Real.exp (8 * (d : ℝ) + 2 * n -
              y * routeUCompletedPrimeGammaAperture / (4 * n))) := by
        rw [routeUParabolicCostRatio]
        field_simp [routeUParabolicWedgeCoefficient_pos.ne', hn.ne']
      _ = (4 * routeUParabolicGlobalCost / n) *
          Real.exp (8 * (d : ℝ) -
            y * routeUCompletedPrimeGammaAperture / (4 * n)) := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hpositive :
      0 < routeUParabolicWedgeCoefficient * Real.exp (-2 * n) :=
    mul_pos routeUParabolicWedgeCoefficient_pos (Real.exp_pos _)
  rw [show ((d + 1 : ℕ) : ℝ) = n by rfl]
  rw [sub_pos, hfactor]
  calc
    (routeUParabolicWedgeCoefficient * Real.exp (-2 * n)) *
        ((routeUParabolicCostRatio / n) *
          Real.exp (8 * (d : ℝ) + 2 * n -
            y * routeUCompletedPrimeGammaAperture / (4 * n))) <
      (routeUParabolicWedgeCoefficient * Real.exp (-2 * n)) * 1 :=
        mul_lt_mul_of_pos_left hscaled hpositive
    _ = routeUParabolicWedgeCoefficient * Real.exp (-2 * n) := by ring

/-- **Parabolic filtered-Gamma positivity.** Above the explicit quadratic horizon, every nonzero
shifted-reversal filter has strictly positive literal filtered Xi heat integral. -/
theorem integral_xiShiftedFilteredGammaKernelReal_pos_of_parabolic
    (d : ℕ) (c : Fin (d + 1) → ℝ) (hc : c ≠ 0) {y : ℝ}
    (hy : routeUParabolicDegreeHorizon * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ y) :
    0 < ∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y 0 d c t := by
  let n : ℝ := ((d + 1 : ℕ) : ℝ)
  let T : ℝ := routeUCompletedPrimeGammaAperture / n
  let s : ℝ := n / y
  let Q : Polynomial ℝ := xiShiftedReversedPolynomial y d c
  let massT : ℝ := routeUPolynomialGaussianMass Q ⟨T, by
    dsimp only [T]
    exact div_pos routeUCompletedPrimeGammaAperture_pos (by positivity)⟩
  have hn : 0 < n := by positivity
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le d))
  have hnSqOne : 1 ≤ n ^ 2 := by nlinarith only [hn1]
  have hA : 0 < routeUCompletedPrimeGammaAperture :=
    routeUCompletedPrimeGammaAperture_pos
  have hK : 0 < routeUParabolicDegreeHorizon := routeUParabolicDegreeHorizon_pos
  have hK16 : 16 ≤ routeUParabolicDegreeHorizon :=
    le_max_left 16 _
  have hK256 :
      256 / routeUCompletedPrimeGammaAperture ≤
        routeUParabolicDegreeHorizon :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hKA256 :
      256 ≤ routeUParabolicDegreeHorizon * routeUCompletedPrimeGammaAperture :=
    (div_le_iff₀ hA).mp hK256
  have hyn : routeUParabolicDegreeHorizon * n ^ 2 ≤ y := by
    simpa only [n] using hy
  have hy16 : 16 ≤ y := by
    calc
      16 ≤ routeUParabolicDegreeHorizon := hK16
      _ ≤ routeUParabolicDegreeHorizon * n ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hnSqOne hK.le
      _ ≤ y := hyn
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy16
  have hT : 0 < T := by
    dsimp only [T]
    exact div_pos hA hn
  have hs : 0 < s := by
    dsimp only [s]
    exact div_pos hn hy0
  have hyA : 256 * n ^ 2 ≤ y * routeUCompletedPrimeGammaAperture := by
    have hmulK := mul_le_mul_of_nonneg_right hKA256 (sq_nonneg n)
    have hmulY := mul_le_mul_of_nonneg_right hyn hA.le
    nlinarith only [hmulK, hmulY]
  have hscaledCut :
      256 ≤ y * T / n := by
    dsimp only [T]
    rw [le_div_iff₀ hn]
    rw [show y * (routeUCompletedPrimeGammaAperture / n) =
      (y * routeUCompletedPrimeGammaAperture) / n by ring]
    rw [le_div_iff₀ hn]
    nlinarith only [hyA]
  have htwoST : 2 * s ≤ T := by
    dsimp only [s, T]
    rw [le_div_iff₀ hn]
    rw [show 2 * (n / y) * n = (2 * n ^ 2) / y by ring]
    rw [div_le_iff₀ hy0]
    have htwo : 2 * n ^ 2 ≤ y * routeUCompletedPrimeGammaAperture :=
      le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 256)
        (sq_nonneg n)) hyA
    nlinarith only [htwo]
  have hdegQ : Q.natDegree ≤ d := by
    exact natDegree_xiShiftedReversedPolynomial_le y d c
  have hQ : Q ≠ 0 := by
    exact xiShiftedReversedPolynomial_ne_zero y d c hc
  have hmassT : 0 < massT := by
    exact routeUPolynomialGaussianMass_pos ⟨Q, hQ⟩ ⟨T, hT⟩
  have hkernelInt :
      IntegrableOn (xiShiftedFilteredGammaKernelReal y 0 d c) (Ioi (0 : ℝ)) :=
    integrableOn_xiShiftedFilteredGammaKernelReal hy0 0 d c
  have hkernelIntPos :
      IntegrableOn (xiShiftedFilteredGammaKernelReal y 0 d c) (Ioc 0 T) :=
    hkernelInt.mono_set (by
      intro t ht
      exact ht.1)
  have hkernelIntTail :
      IntegrableOn (xiShiftedFilteredGammaKernelReal y 0 d c) (Ioi T) :=
    hkernelInt.mono_set (by
      intro t ht
      exact lt_trans hT ht)
  have hbefore (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
      routeUParabolicWedgeCoefficient * massT ≤
        xiPolynomialGaussianHeatTraceReal Q t := by
    let tt : {τ : ℝ // 0 < τ} := ⟨t, ht.1⟩
    have hdegSucc : Q.natDegree + 1 ≤ d + 1 := Nat.add_le_add_right hdegQ 1
    have hcutN : t * n ≤ routeUCompletedPrimeGammaAperture := by
      have := (le_div_iff₀ hn).mp ht.2
      simpa only [T] using this
    have hcutQ : t * ((Q.natDegree + 1 : ℕ) : ℝ) ≤
        routeUCompletedPrimeGammaAperture := by
      have hcast : ((Q.natDegree + 1 : ℕ) : ℝ) ≤ n := by
        dsimp only [n]
        exact_mod_cast hdegSucc
      exact le_trans (mul_le_mul_of_nonneg_left hcast ht.1.le) hcutN
    have hcutQ' : t * ((Q.natDegree : ℝ) + 1) ≤
        routeUCompletedPrimeGammaAperture := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcutQ
    let tw : routeUCompletedPrimeGammaWedge Q := ⟨t, ht.1, hcutQ'⟩
    have htrace := xiPolynomialGaussianHeatTraceReal_ge_parabolicWedgeMass Q tw
    have hmassMono : massT ≤ routeUPolynomialGaussianMass Q tt := by
      exact routeUPolynomialGaussianMass_antitone Q (s := tt) (t := ⟨T, hT⟩) ht.2
    calc
      routeUParabolicWedgeCoefficient * massT ≤
          routeUParabolicWedgeCoefficient * routeUPolynomialGaussianMass Q tt :=
        mul_le_mul_of_nonneg_left hmassMono routeUParabolicWedgeCoefficient_pos.le
      _ ≤ xiPolynomialGaussianHeatTraceReal Q t := by
        simpa only [tw, routeUCompletedPrimeGammaWedge.heat] using htrace
  have hkernelNonneg (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
      0 ≤ xiShiftedFilteredGammaKernelReal y 0 d c t := by
    have htrace : 0 ≤ xiPolynomialGaussianHeatTraceReal Q t :=
      le_trans (mul_nonneg routeUParabolicWedgeCoefficient_pos.le hmassT.le)
        (hbefore t ht)
    rw [xiShiftedFilteredGammaKernelReal]
    exact mul_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (Real.exp_nonneg _)) htrace
  let positiveFloor : ℝ := routeUParabolicWedgeCoefficient * massT *
    s ^ (2 * d) * Real.exp (-2 * n)
  have hpositiveFloor : 0 < positiveFloor := by
    dsimp only [positiveFloor]
    exact mul_pos
      (mul_pos
        (mul_pos routeUParabolicWedgeCoefficient_pos hmassT)
        (pow_pos hs _))
      (Real.exp_pos _)
  have hintervalSubset : Ioc s (2 * s) ⊆ Ioc (0 : ℝ) T := by
    intro t ht
    constructor
    · exact lt_of_lt_of_le hs ht.1.le
    · exact le_trans ht.2 htwoST
  have hintervalLower (t : ℝ) (ht : t ∈ Ioc s (2 * s)) :
      positiveFloor ≤ xiShiftedFilteredGammaKernelReal y 0 d c t := by
    have htMain := hintervalSubset ht
    have htrace := hbefore t htMain
    have hpow : s ^ (2 * d) ≤ t ^ (2 * d) :=
      pow_le_pow_left₀ hs.le ht.1.le _
    have hyt : y * t ≤ 2 * n := by
      have := mul_le_mul_of_nonneg_left ht.2 hy0.le
      dsimp only [s] at this
      field_simp [hy0.ne'] at this
      nlinarith only [this]
    have hexp : Real.exp (-2 * n) ≤ Real.exp (-(y * t)) := by
      exact Real.exp_le_exp.mpr (by nlinarith only [hyt])
    rw [xiShiftedFilteredGammaKernelReal]
    dsimp only [positiveFloor]
    have hweight :
        s ^ (2 * d) * Real.exp (-2 * n) ≤
          t ^ (2 * d) * Real.exp (-(y * t)) :=
      mul_le_mul hpow hexp (Real.exp_nonneg _) (pow_nonneg htMain.1.le _)
    have hprod :
        (s ^ (2 * d) * Real.exp (-2 * n)) *
            (routeUParabolicWedgeCoefficient * massT) ≤
          (t ^ (2 * d) * Real.exp (-(y * t))) *
            xiPolynomialGaussianHeatTraceReal Q t :=
      mul_le_mul hweight htrace
        (mul_nonneg routeUParabolicWedgeCoefficient_pos.le hmassT.le)
        (mul_nonneg (pow_nonneg htMain.1.le _) (Real.exp_nonneg _))
    convert hprod using 1 <;> ring
  have hindicatorInt :
      Integrable ((Ioc s (2 * s)).indicator (fun _ : ℝ => positiveFloor))
        (volume.restrict (Ioc (0 : ℝ) T)) := by
    have hbase : IntegrableOn (fun _ : ℝ => positiveFloor) (Ioc s (2 * s)) :=
      MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
    exact (hbase.integrable_indicator measurableSet_Ioc).mono_measure
      (Measure.restrict_le_self)
  have hposIntegral :
      s * positiveFloor ≤
        ∫ t in Ioc (0 : ℝ) T, xiShiftedFilteredGammaKernelReal y 0 d c t := by
    have hmono :
        (Ioc s (2 * s)).indicator (fun _ : ℝ => positiveFloor) ≤ᵐ[
            volume.restrict (Ioc (0 : ℝ) T)]
          xiShiftedFilteredGammaKernelReal y 0 d c := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      by_cases hJ : t ∈ Ioc s (2 * s)
      · simp only [Set.indicator_of_mem hJ]
        exact hintervalLower t hJ
      · simp only [Set.indicator_of_notMem hJ]
        exact hkernelNonneg t ht
    have hle := MeasureTheory.integral_mono_ae hindicatorInt hkernelIntPos hmono
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc] at hle
    have hinter : Ioc (0 : ℝ) T ∩ Ioc s (2 * s) = Ioc s (2 * s) := by
      exact inter_eq_right.mpr hintervalSubset
    rw [hinter, integral_const_Ioc_self_two s positiveFloor hs.le] at hle
    exact hle
  let tailFloor : ℝ := routeUParabolicGlobalCost * Real.exp (8 * (d : ℝ)) *
    massT * s ^ (2 * d)
  have htailFloor : 0 ≤ tailFloor := by
    dsimp only [tailFloor]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg routeUParabolicGlobalCost_pos.le (Real.exp_nonneg _))
        hmassT.le)
      (pow_nonneg hs.le _)
  have htailPoint (t : ℝ) (ht : t ∈ Ioi T) :
      -(tailFloor * Real.exp (-(y * t / 4))) ≤
        xiShiftedFilteredGammaKernelReal y 0 d c t := by
    let tt : {τ : ℝ // 0 < τ} := ⟨t, lt_trans hT ht⟩
    have htrace := xiPolynomialGaussianHeatTraceReal_ge_neg_parabolicGlobalCost
      Q d hdegQ tt
    have hmassMono : routeUPolynomialGaussianMass Q tt ≤ massT := by
      exact routeUPolynomialGaussianMass_antitone Q (s := ⟨T, hT⟩) (t := tt) ht.le
    have htraceMass :
        -(routeUParabolicGlobalCost * Real.exp (8 * ((d : ℝ) + t)) * massT) ≤
          xiPolynomialGaussianHeatTraceReal Q t := by
      calc
        -(routeUParabolicGlobalCost * Real.exp (8 * ((d : ℝ) + t)) * massT) ≤
          -(routeUParabolicGlobalCost * Real.exp (8 * ((d : ℝ) + t)) *
            routeUPolynomialGaussianMass Q tt) := by
          exact neg_le_neg (mul_le_mul_of_nonneg_left hmassMono
            (mul_nonneg routeUParabolicGlobalCost_pos.le (Real.exp_nonneg _)))
        _ ≤ xiPolynomialGaussianHeatTraceReal Q t := by simpa only [tt] using htrace
    have hu : 256 ≤ y * t / n :=
      le_trans hscaledCut (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht.le hy0.le) hn.le)
    have hpowerTail := routeUParabolic_power_exp_tail_le d hy16 (lt_trans hT ht).le hu
    have hpowerTail' :
        t ^ (2 * d) * Real.exp (-((y - 8) * t)) ≤
          (n / y) ^ (2 * d) * Real.exp (-(y * t / 4)) := by
      simpa only [n] using hpowerTail
    rw [xiShiftedFilteredGammaKernelReal]
    dsimp only [tailFloor, s]
    have hweight : 0 ≤ t ^ (2 * d) * Real.exp (-(y * t)) :=
      mul_nonneg (pow_nonneg (lt_trans hT ht).le _) (Real.exp_nonneg _)
    calc
      -(routeUParabolicGlobalCost * Real.exp (8 * (d : ℝ)) * massT *
          (n / y) ^ (2 * d) * Real.exp (-(y * t / 4))) ≤
        -(routeUParabolicGlobalCost * Real.exp (8 * (d : ℝ)) * massT *
          (t ^ (2 * d) * Real.exp (-((y - 8) * t)))) := by
        have hconstant : 0 ≤
            routeUParabolicGlobalCost * Real.exp (8 * (d : ℝ)) * massT :=
          mul_nonneg
            (mul_nonneg routeUParabolicGlobalCost_pos.le (Real.exp_nonneg _))
            hmassT.le
        have hscaled :
            (routeUParabolicGlobalCost * Real.exp (8 * (d : ℝ)) * massT) *
                (t ^ (2 * d) * Real.exp (-((y - 8) * t))) ≤
              (routeUParabolicGlobalCost * Real.exp (8 * (d : ℝ)) * massT) *
                ((n / y) ^ (2 * d) * Real.exp (-(y * t / 4))) :=
          mul_le_mul_of_nonneg_left hpowerTail' hconstant
        simpa only [mul_assoc] using neg_le_neg hscaled
      _ = (t ^ (2 * d) * Real.exp (-(y * t))) *
          (-(routeUParabolicGlobalCost * Real.exp (8 * ((d : ℝ) + t)) * massT)) := by
        have hexpTail : Real.exp (-((y - 8) * t)) =
            Real.exp (-(y * t)) * Real.exp (8 * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hexpSplit : Real.exp (8 * ((d : ℝ) + t)) =
            Real.exp (8 * (d : ℝ)) * Real.exp (8 * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexpTail, hexpSplit]
        ring
      _ ≤ (t ^ (2 * d) * Real.exp (-(y * t))) *
          xiPolynomialGaussianHeatTraceReal Q t :=
        mul_le_mul_of_nonneg_left htraceMass hweight
      _ = xiShiftedFilteredGammaKernelReal y 0 d c t := by
        simp only [xiShiftedFilteredGammaKernelReal, Nat.mul_zero, zero_add, Q]
  have htailCompareInt :
      IntegrableOn (fun t : ℝ => -(tailFloor * Real.exp (-(y * t / 4)))) (Ioi T) := by
    have he : IntegrableOn (fun t : ℝ => Real.exp (-(y / 4) * t)) (Ioi T) :=
      exp_neg_integrableOn_Ioi T (div_pos hy0 (by norm_num))
    have he' : IntegrableOn (fun t : ℝ => Real.exp (-(y * t / 4))) (Ioi T) := by
      convert he using 1
      funext t
      congr 1
      ring
    have hmul := ((he' : Integrable _ (volume.restrict (Ioi T))).const_mul (-tailFloor))
    change Integrable (fun t : ℝ => -(tailFloor * Real.exp (-(y * t / 4))))
      (volume.restrict (Ioi T))
    convert hmul using 1
    funext t
    ring
  have htailIntegral :
      -(tailFloor * ((4 / y) * Real.exp (-(y * T / 4)))) ≤
        ∫ t in Ioi T, xiShiftedFilteredGammaKernelReal y 0 d c t := by
    have hmono :
        (fun t : ℝ => -(tailFloor * Real.exp (-(y * t / 4)))) ≤ᵐ[
            volume.restrict (Ioi T)]
          xiShiftedFilteredGammaKernelReal y 0 d c := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htailPoint t ht
    have hle := MeasureTheory.integral_mono_ae htailCompareInt hkernelIntTail hmono
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul,
      integral_exp_neg_quarter_mul_Ioi hy0 T] at hle
    simpa only [neg_mul] using hle
  have hsplit :
      (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y 0 d c t) =
        (∫ t in Ioc (0 : ℝ) T, xiShiftedFilteredGammaKernelReal y 0 d c t) +
          ∫ t in Ioi T, xiShiftedFilteredGammaKernelReal y 0 d c t := by
    have hdisjoint : Disjoint (Ioc (0 : ℝ) T) (Ioi T) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact (not_lt_of_ge ht1.2) ht2
    have hunion : Ioc (0 : ℝ) T ∪ Ioi T = Ioi (0 : ℝ) := by
      ext t
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · intro h
        rcases h with h | h
        · exact h.1
        · exact lt_trans hT h
      · intro ht
        by_cases hle : t ≤ T
        · exact Or.inl ⟨ht, hle⟩
        · exact Or.inr (lt_of_not_ge hle)
    have h := MeasureTheory.setIntegral_union₀ hdisjoint.aedisjoint
      measurableSet_Ioi.nullMeasurableSet hkernelIntPos hkernelIntTail
    rw [hunion] at h
    exact h
  have hsumLower :
      s * positiveFloor - tailFloor * ((4 / y) * Real.exp (-(y * T / 4))) ≤
        ∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y 0 d c t := by
    rw [hsplit]
    linarith only [hposIntegral, htailIntegral]
  have hscalar := routeUParabolic_scalar_gap_pos d hy
  have hfourOverY : (4 / y : ℝ) = s * (4 / n) := by
    dsimp only [s]
    field_simp [hy0.ne', hn.ne']
  have hexpTailAtT :
      Real.exp (8 * (d : ℝ)) * Real.exp (-(y * T / 4)) =
        Real.exp (8 * (d : ℝ) -
          y * routeUCompletedPrimeGammaAperture / (4 * n)) := by
    dsimp only [T]
    rw [← Real.exp_add]
    congr 1
    field_simp [hn.ne']
    ring
  have hpositiveFactor :
      s * positiveFloor =
        massT * s ^ (2 * d + 1) *
          (routeUParabolicWedgeCoefficient * Real.exp (-2 * n)) := by
    dsimp only [positiveFloor]
    rw [pow_succ]
    ring
  have htailFactor :
      tailFloor * ((4 / y) * Real.exp (-(y * T / 4))) =
        massT * s ^ (2 * d + 1) *
          ((4 * routeUParabolicGlobalCost / n) *
            Real.exp (8 * (d : ℝ) -
              y * routeUCompletedPrimeGammaAperture / (4 * n))) := by
    dsimp only [tailFloor]
    rw [hfourOverY, pow_succ]
    calc
      routeUParabolicGlobalCost * Real.exp (8 * (d : ℝ)) * massT *
          s ^ (2 * d) *
          (s * (4 / n) * Real.exp (-(y * T / 4))) =
        massT * (s ^ (2 * d) * s) *
          ((4 * routeUParabolicGlobalCost / n) *
            (Real.exp (8 * (d : ℝ)) * Real.exp (-(y * T / 4)))) := by ring
      _ = massT * (s ^ (2 * d) * s) *
          ((4 * routeUParabolicGlobalCost / n) *
            Real.exp (8 * (d : ℝ) -
              y * routeUCompletedPrimeGammaAperture / (4 * n))) := by
        rw [hexpTailAtT]
  have hfactor :
      s * positiveFloor - tailFloor * ((4 / y) * Real.exp (-(y * T / 4))) =
        massT * s ^ (2 * d + 1) *
          (routeUParabolicWedgeCoefficient * Real.exp (-2 * n) -
            (4 * routeUParabolicGlobalCost / n) *
              Real.exp (8 * (d : ℝ) -
                y * routeUCompletedPrimeGammaAperture / (4 * n))) := by
    rw [hpositiveFactor, htailFactor]
    ring
  have hlowerPos :
      0 < s * positiveFloor -
        tailFloor * ((4 / y) * Real.exp (-(y * T / 4))) := by
    rw [hfactor]
    exact mul_pos (mul_pos hmassT (pow_pos hs _)) hscalar
  exact lt_of_lt_of_le hlowerPos hsumLower

/-- **Parabolic degree horizon (PDH.1).**  Above the universal quadratic shift threshold,
every nonzero coefficient vector has strictly positive shifted-Xi reciprocal Hankel form. -/
theorem xiShiftedReciprocalHankelQuadratic_pos_of_parabolic
    (d : ℕ) (c : Fin (d + 1) → ℝ) (hc : c ≠ 0) {y : ℝ}
    (hy : routeUParabolicDegreeHorizon * ((d + 1 : ℕ) : ℝ) ^ 2 ≤ y) :
    0 < xiShiftedReciprocalHankelQuadratic y c := by
  have hn : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le
    (mul_pos routeUParabolicDegreeHorizon_pos (sq_pos_of_pos hn)) hy
  rw [xiShiftedReciprocalHankelQuadratic_eq_normalizedFilteredGamma hy0 d c]
  exact mul_pos (one_div_pos.mpr (by positivity))
    (integral_xiShiftedFilteredGammaKernelReal_pos_of_parabolic d c hc hy)

end RHTower
