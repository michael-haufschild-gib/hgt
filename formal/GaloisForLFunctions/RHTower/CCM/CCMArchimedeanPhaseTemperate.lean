import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanInfiniteOrder
import GaloisForLFunctions.RHTower.HardyZ
import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.GammaJetProjectiveBoundary
import GaloisForLFunctions.HTGeometry.LineJetTransfer
import GaloisForLFunctions.HTGeometry.LogDerivBellTransfer
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Order.Compact

/-!
# Temperate growth of the CCM archimedean phase

Connes--Consani's archimedean quantized-calculus argument uses that multiplication by the
scattering phase preserves Schwartz space.  This file proves that analytic input from the Gamma
factor itself.  No regularity or growth assumption on the phase is introduced: logarithmic growth
of digamma, all-order vertical polygamma bounds, and the exact Bell identity imply polynomial
bounds for every derivative of the unimodular critical-line phase.
-/

open Complex Real Set Filter Topology
open scoped SchwartzMap

noncomputable section

namespace RHTower

open GaloisForLFunctions

private def ccmDigammaLine (sigma : ℝ) (t : ℝ) : ℂ :=
  Complex.digamma ((sigma : ℂ) + (t : ℂ) * Complex.I)

private theorem ccmDigammaLine_contDiff (sigma : ℝ) (hsigma : 0 < sigma) :
    ContDiff ℝ (⊤ : ℕ∞) (ccmDigammaLine sigma) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hz : 0 < (((sigma : ℂ) + (t : ℂ) * Complex.I).re) := by
    simpa using hsigma
  have hpsi := (digamma_analyticOnNhd_re_pos
    ((sigma : ℂ) + (t : ℂ) * Complex.I) hz).contDiffAt (n := (⊤ : ℕ∞))
  have hline : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (sigma : ℂ) + (s : ℂ) * Complex.I) t := by
    have hofReal : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => (s : ℂ)) t :=
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).contDiffAt
    exact contDiffAt_const.add (hofReal.mul contDiffAt_const)
  exact (hpsi.restrict_scalars ℝ).comp t hline

private theorem iteratedDeriv_complexConj
    (n : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    iteratedDeriv n (fun x => (starRingEnd ℂ) (f x)) =
      fun x => (starRingEnd ℂ) (iteratedDeriv n f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hdiff : DifferentiableAt ℝ (iteratedDeriv n f) x :=
        (hf.differentiable_iteratedDeriv n
          (compareOfLessAndEq_eq_lt.mp rfl)).differentiableAt
      exact ((Complex.conjCLE.hasFDerivAt).comp_hasDerivAt
        x hdiff.hasDerivAt).deriv

private theorem norm_iteratedDeriv_ccmDigammaLine_neg
    (n : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) (t : ℝ) :
    ‖iteratedDeriv n (ccmDigammaLine sigma) (-t)‖ =
      ‖iteratedDeriv n (ccmDigammaLine sigma) t‖ := by
  have hsmooth := ccmDigammaLine_contDiff sigma hsigma
  have href : (fun x : ℝ => ccmDigammaLine sigma (-x)) =
      fun x : ℝ => (starRingEnd ℂ) (ccmDigammaLine sigma x) := by
    funext x
    rw [ccmDigammaLine, ccmDigammaLine,
      show ((sigma : ℂ) + ((-x : ℝ) : ℂ) * Complex.I) =
        (starRingEnd ℂ) ((sigma : ℂ) + (x : ℂ) * Complex.I) by
          apply Complex.ext <;> simp]
    exact ReflectedDigammaAnomaly.digamma_conj _
  have hjet := congrFun (congrArg (iteratedDeriv n) href) t
  rw [iteratedDeriv_comp_neg, iteratedDeriv_complexConj n hsmooth] at hjet
  have hnorm := congrArg norm hjet
  simpa using hnorm

private theorem ccmDigammaLine_iteratedDeriv_eq
    (n : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) (t : ℝ) :
    iteratedDeriv n (ccmDigammaLine sigma) t =
      Complex.I ^ n * iteratedDeriv n Complex.digamma
        ((sigma : ℂ) + (t : ℂ) * Complex.I) := by
  have hR : 0 < sigma / 2 := half_pos hsigma
  have hdiff : DifferentiableOn ℂ Complex.digamma
      (verticalStrip sigma (sigma / 2)) := by
    intro z hz
    have hzabs : |z.re - sigma| < sigma / 2 := hz
    have hzre : 0 < z.re := by
      rw [abs_lt] at hzabs
      linarith
    exact (digamma_analyticOnNhd_re_pos z hzre).differentiableAt.differentiableWithinAt
  exact GaloisForLFunctions.iteratedDeriv_line_restriction hR hdiff n t

private theorem ccmDigammaLine_hasTemperateGrowth
    (sigma : ℝ) (hsigma : 0 < sigma) :
    Function.HasTemperateGrowth (ccmDigammaLine sigma) := by
  have hsmooth := ccmDigammaLine_contDiff sigma hsigma
  refine ⟨hsmooth, fun n => ?_⟩
  have hcontinuous : Continuous (fun t : ℝ =>
      ‖iteratedDeriv n (ccmDigammaLine sigma) t‖) :=
    (hsmooth.continuous_iteratedDeriv n (by exact_mod_cast le_top)).norm
  let A : ℝ := max 1 sigma
  have hA1 : 1 ≤ A := le_max_left _ _
  have hsigmaA : sigma ≤ A := le_max_right _ _
  obtain ⟨Ccompact, hCcompact⟩ :=
    (isCompact_Icc : IsCompact (Icc (-A) A)).bddAbove_image hcontinuous.continuousOn
  rcases n with _ | m
  · let Ctail : ℝ := 1 + GaloisForLFunctions.digammaVerticalLogConstant
    let C : ℝ := max Ccompact Ctail
    refine ⟨1, C, fun t => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hCtail_pos : 0 < Ctail := by
      dsimp [Ctail, GaloisForLFunctions.digammaVerticalLogConstant]
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [Real.pi_pos]
    have hC_nonneg : 0 ≤ C :=
      le_trans hCtail_pos.le (le_max_right _ _)
    by_cases htpos : A ≤ t
    · rw [ccmDigammaLine_iteratedDeriv_eq 0 sigma hsigma t]
      simp only [pow_zero, one_mul]
      have hlog := GaloisForLFunctions.norm_digamma_vertical_le_log
        hsigma (hA1.trans htpos) (hsigmaA.trans htpos)
      have hlogt : Real.log t ≤ t := Real.log_le_sub_one_of_pos
        (zero_lt_one.trans_le (hA1.trans htpos)) |>.trans (by linarith)
      have htail :
          ‖Complex.digamma ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Ctail * (1 + |t|) := by
        rw [abs_of_nonneg (zero_le_one.trans (hA1.trans htpos))]
        dsimp [Ctail]
        have hKnonneg : 0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
          dsimp [GaloisForLFunctions.digammaVerticalLogConstant]
          have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith [Real.pi_pos]
        nlinarith
      simpa [pow_one, Real.norm_eq_abs] using
        htail.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · by_cases htneg : t ≤ -A
      · have hposA : A ≤ -t := by linarith
        have hpos : 1 ≤ -t := hA1.trans hposA
        rw [← norm_iteratedDeriv_ccmDigammaLine_neg 0 sigma hsigma t,
          ccmDigammaLine_iteratedDeriv_eq 0 sigma hsigma (-t)]
        simp only [pow_zero, one_mul]
        have hlog := GaloisForLFunctions.norm_digamma_vertical_le_log
          hsigma hpos (hsigmaA.trans hposA)
        have hlogt : Real.log (-t) ≤ -t := Real.log_le_sub_one_of_pos
          (zero_lt_one.trans_le hpos) |>.trans (by linarith)
        have htail :
            ‖Complex.digamma ((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ≤
              Ctail * (1 + |t|) := by
          rw [abs_of_nonpos (by linarith : t ≤ 0)]
          dsimp [Ctail]
          have hKnonneg : 0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
            dsimp [GaloisForLFunctions.digammaVerticalLogConstant]
            have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            nlinarith [Real.pi_pos]
          nlinarith
        simpa [pow_one, Real.norm_eq_abs] using
          htail.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      · have htIcc : t ∈ Icc (-A) A := by constructor <;> linarith
        have hcompact : ‖iteratedDeriv 0 (ccmDigammaLine sigma) t‖ ≤ Ccompact :=
          hCcompact ⟨t, htIcc, rfl⟩
        have hcompactC : ‖iteratedDeriv 0 (ccmDigammaLine sigma) t‖ ≤ C :=
          hcompact.trans (le_max_left _ _)
        exact hcompactC.trans (by
          have hbase : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
          rw [pow_one, Real.norm_eq_abs]
          exact le_mul_of_one_le_right hC_nonneg hbase)
  · let Ctail : ℝ := (m + 1).factorial * (1 + Real.pi / 2)
    let C : ℝ := max Ccompact Ctail
    refine ⟨1, C, fun t => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hCtail_nonneg : 0 ≤ Ctail := by
      dsimp [Ctail]
      positivity
    have hC_nonneg : 0 ≤ C := hCtail_nonneg.trans (le_max_right _ _)
    by_cases htpos : A ≤ t
    · rw [ccmDigammaLine_iteratedDeriv_eq (m + 1) sigma hsigma t,
        norm_mul, norm_pow, norm_I, one_pow, one_mul]
      have hpoly := GaloisForLFunctions.norm_iteratedDeriv_digamma_vertical_le
        m hsigma (hA1.trans htpos)
      have herror : 1 / t ^ (2 : ℕ) + Real.pi / (2 * t) ≤ 1 + Real.pi / 2 := by
        have ht0 : 0 < t := zero_lt_one.trans_le (hA1.trans htpos)
        have ht_sq : 1 ≤ t ^ (2 : ℕ) := one_le_pow₀ (hA1.trans htpos)
        have h1 : 1 / t ^ (2 : ℕ) ≤ 1 := (div_le_one (sq_pos_of_pos ht0)).2 ht_sq
        have h2 : Real.pi / (2 * t) ≤ Real.pi / 2 := by
          apply (div_le_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)).2
          linarith
        linarith
      have htail :
          ‖iteratedDeriv (m + 1) Complex.digamma
              ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Ctail := by
        exact hpoly.trans (mul_le_mul_of_nonneg_left herror (by positivity))
      exact htail.trans ((le_max_right _ _).trans (by
        have hbase : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
        rw [pow_one, Real.norm_eq_abs]
        exact le_mul_of_one_le_right hC_nonneg hbase))
    · by_cases htneg : t ≤ -A
      · have hposA : A ≤ -t := by linarith
        have hpos : 1 ≤ -t := hA1.trans hposA
        rw [← norm_iteratedDeriv_ccmDigammaLine_neg (m + 1) sigma hsigma t,
          ccmDigammaLine_iteratedDeriv_eq (m + 1) sigma hsigma (-t),
          norm_mul, norm_pow, norm_I, one_pow, one_mul]
        have hpoly := GaloisForLFunctions.norm_iteratedDeriv_digamma_vertical_le
          m hsigma hpos
        have herror : 1 / (-t) ^ (2 : ℕ) + Real.pi / (2 * (-t)) ≤ 1 + Real.pi / 2 := by
          have ht0 : 0 < -t := zero_lt_one.trans_le hpos
          have ht_sq : 1 ≤ (-t) ^ (2 : ℕ) := one_le_pow₀ hpos
          have h1 : 1 / (-t) ^ (2 : ℕ) ≤ 1 := (div_le_one (sq_pos_of_pos ht0)).2 ht_sq
          have h2 : Real.pi / (2 * (-t)) ≤ Real.pi / 2 := by
            apply (div_le_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)).2
            linarith
          linarith
        have htail :
            ‖iteratedDeriv (m + 1) Complex.digamma
                ((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ≤ Ctail := by
          exact hpoly.trans (mul_le_mul_of_nonneg_left herror (by positivity))
        exact htail.trans ((le_max_right _ _).trans (by
          have hbase : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
          rw [pow_one, Real.norm_eq_abs]
          exact le_mul_of_one_le_right hC_nonneg hbase))
      · have htIcc : t ∈ Icc (-A) A := by constructor <;> linarith
        have hcompact :
            ‖iteratedDeriv (m + 1) (ccmDigammaLine sigma) t‖ ≤ Ccompact :=
          hCcompact ⟨t, htIcc, rfl⟩
        have hcompactC :
            ‖iteratedDeriv (m + 1) (ccmDigammaLine sigma) t‖ ≤ C :=
          hcompact.trans (le_max_left _ _)
        exact hcompactC.trans (by
          have hbase : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
          rw [pow_one, Real.norm_eq_abs]
          exact le_mul_of_one_le_right hC_nonneg hbase)

private theorem gammaHardyPhaseRate_hasTemperateGrowth :
    Function.HasTemperateGrowth (gammaHardyPhaseRate : ℝ → ℝ) := by
  have hpsi : Function.HasTemperateGrowth (ccmDigammaLine (1 / 4 : ℝ)) :=
    ccmDigammaLine_hasTemperateGrowth (1 / 4) (by norm_num)
  have hhalf : Function.HasTemperateGrowth (fun t : ℝ => t / 2) := by
    have h := ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
    convert h using 1
    funext t
    simp [div_eq_mul_inv, mul_comm]
  have hcomp : Function.HasTemperateGrowth
      (fun t : ℝ => ccmDigammaLine (1 / 4 : ℝ) (t / 2)) := by
    simpa [Function.comp_def] using hpsi.comp hhalf
  have hre : Function.HasTemperateGrowth
      (fun t : ℝ => (ccmDigammaLine (1 / 4 : ℝ) (t / 2)).re) := by
    simpa [Function.comp_def] using Complex.reCLM.hasTemperateGrowth.comp hcomp
  have hscaled : Function.HasTemperateGrowth
      (fun t : ℝ => (ccmDigammaLine (1 / 4 : ℝ) (t / 2)).re / 2) := by
    have hscale := ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth.comp hre
    simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using hscale
  have hrate : Function.HasTemperateGrowth
      (fun t : ℝ => (ccmDigammaLine (1 / 4 : ℝ) (t / 2)).re / 2 -
        Real.log Real.pi / 2) :=
    hscaled.sub (Function.HasTemperateGrowth.const (Real.log Real.pi / 2))
  convert hrate using 1
  funext t
  simp only [gammaHardyPhaseRate, ccmDigammaLine]
  congr 3
  unfold linePt
  push_cast
  ring_nf

/-- The exact Gamma Hardy phase rate, viewed as a complex scalar multiplier, has temperate
growth.  This exposes the unconditional Gamma estimate needed to multiply arbitrary Schwartz
spectral tests by the phase density. -/
theorem gammaHardyPhaseRate_complex_hasTemperateGrowth :
    Function.HasTemperateGrowth
      (fun t : ℝ => (gammaHardyPhaseRate t : ℂ)) := by
  simpa [Function.comp_def] using
    Complex.ofRealCLM.hasTemperateGrowth.comp
      gammaHardyPhaseRate_hasTemperateGrowth

/-- Complex digamma on the Fourier-normalized quarter line used by the CCM archimedean
distribution.  Exposing temperate growth here makes the Gauss-to-Weil passage available for an
arbitrary Schwartz test, rather than only for the special rectangular probes. -/
theorem digamma_oneQuarter_piLine_hasTemperateGrowth :
    Function.HasTemperateGrowth
      (fun ξ : ℝ => Complex.digamma
        (((1 / 4 : ℝ) : ℂ) + ((Real.pi * ξ : ℝ) : ℂ) * Complex.I)) := by
  have hpsi : Function.HasTemperateGrowth (ccmDigammaLine (1 / 4 : ℝ)) :=
    ccmDigammaLine_hasTemperateGrowth (1 / 4) (by norm_num)
  have hscale : Function.HasTemperateGrowth (fun ξ : ℝ => Real.pi * ξ) := by
    have h := (Real.pi • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
    convert h using 1
    funext ξ
    simp
  simpa only [Function.comp_def, ccmDigammaLine] using hpsi.comp hscale

private theorem hasDerivAt_mvEval_jet_real {n : ℕ}
    (Q : MvPolynomial (Fin n) ℂ) (g : Fin n → ℝ → ℂ)
    (g' : Fin n → ℂ) (x : ℝ) (hg : ∀ j, HasDerivAt (g j) (g' j) x) :
    HasDerivAt (fun s => MvPolynomial.eval (fun j => g j s) Q)
      (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j Q) * g' j) x := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      have hcf : (fun s => MvPolynomial.eval (fun j => g j s) (MvPolynomial.C a)) =
          fun _ => a := by
        funext s
        simp
      rw [hcf]
      simp only [MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
      exact hasDerivAt_const x a
  | add p q hp hq =>
      have hfun : (fun s => MvPolynomial.eval (fun j => g j s) (p + q)) =
          (fun s => MvPolynomial.eval (fun j => g j s) p) +
            fun s => MvPolynomial.eval (fun j => g j s) q := by
        funext s
        simp
      rw [hfun]
      have hcoef :
          (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j (p + q)) * g' j) =
            (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j p) * g' j) +
              ∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j q) * g' j := by
        simp only [map_add, add_mul, Finset.sum_add_distrib]
      rw [hcoef]
      exact hp.add hq
  | mul_X p i hp =>
      have hfun :
          (fun s => MvPolynomial.eval (fun j => g j s) (p * MvPolynomial.X i)) =
            (fun s => MvPolynomial.eval (fun j => g j s) p) * g i := by
        funext s
        simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [hfun]
      have hcoef :
          (∑ j, MvPolynomial.eval (fun j => g j x)
              (MvPolynomial.pderiv j (p * MvPolynomial.X i)) * g' j) =
            (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j p) * g' j) *
                g i x + MvPolynomial.eval (fun j => g j x) p * g' i := by
        simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_X, MvPolynomial.pderiv_X, Pi.single_apply, mul_ite, mul_one,
          mul_zero, add_mul, Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        · rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            simp [Ne.symm hj]
          · intro h
            simp at h
      rw [hcoef]
      exact hp.mul (hg i)

private theorem iteratedDeriv_eq_bellCore_real_ode
    {f a : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hode : ∀ x, deriv f x = a x * f x) :
    ∀ (n : ℕ) (x : ℝ),
      iteratedDeriv n f x = f x *
        MvPolynomial.eval (fun j : Fin n => iteratedDeriv (j : ℕ) a x)
          (GaloisForLFunctions.bellCore n) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [GaloisForLFunctions.bellCore_zero, iteratedDeriv_zero]
  | succ n ih =>
      intro x
      have hfun : iteratedDeriv n f = fun y => f y *
          MvPolynomial.eval (fun j : Fin n => iteratedDeriv (j : ℕ) a y)
            (GaloisForLFunctions.bellCore n) := by
        funext y
        exact ih y
      have hjet : ∀ j : Fin n,
          HasDerivAt (fun y => iteratedDeriv (j : ℕ) a y)
            (iteratedDeriv ((j : ℕ) + 1) a x) x := by
        intro j
        have hd : HasDerivAt (iteratedDeriv (j : ℕ) a)
            (deriv (iteratedDeriv (j : ℕ) a) x) x :=
          (ha.differentiable_iteratedDeriv (j : ℕ)
            (compareOfLessAndEq_eq_lt.mp rfl) x).hasDerivAt
        rw [iteratedDeriv_succ]
        exact hd
      have hchain := hasDerivAt_mvEval_jet_real (GaloisForLFunctions.bellCore n)
        (fun j => fun y => iteratedDeriv (j : ℕ) a y)
        (fun j => iteratedDeriv ((j : ℕ) + 1) a x) x hjet
      have hfderiv : HasDerivAt f (deriv f x) x :=
        (hf.differentiable (by simp) x).hasDerivAt
      have hproduct := hfderiv.mul hchain
      rw [iteratedDeriv_succ, hfun]
      change deriv (f * fun y =>
        MvPolynomial.eval (fun j : Fin n => iteratedDeriv (j : ℕ) a y)
          (GaloisForLFunctions.bellCore n)) x = _
      rw [hproduct.deriv, hode]
      rw [GaloisForLFunctions.bellCore_succ]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_succ,
        Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero]
      ring

private theorem bellCore_eq_gammaBell : ∀ n : ℕ,
    GaloisForLFunctions.bellCore n = GaloisForLFunctions.gammaBell n
  | 0 => rfl
  | n + 1 => by
      rw [GaloisForLFunctions.bellCore_succ]
      simp only [GaloisForLFunctions.gammaBell]
      rw [bellCore_eq_gammaBell n]

private theorem contDiff_infty_of_deriv_eq_mul
    {f a : ℝ → ℂ} (hf : Differentiable ℝ f)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hode : ∀ x, deriv f x = a x * f x) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  have hnat : ∀ n : ℕ, ContDiff ℝ n f := by
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr hf.continuous
    | succ n ih =>
        have hsucc : ContDiff ℝ ((n : ℕ∞) + 1) f := by
          rw [contDiff_succ_iff_deriv]
          refine ⟨hf, by simp, ?_⟩
          have hfun : deriv f = a * f := by
            funext x
            exact hode x
          rw [hfun]
          exact (ha.of_le (by exact_mod_cast le_top)).mul ih
        simpa using hsucc
  exact contDiff_iff_forall_nat_le.mpr fun n _ => hnat n

/-- A unit-modulus solution of a temperate scalar ODE has temperate growth at every order. -/
theorem hasTemperateGrowth_of_unitary_ode
    {f a : ℝ → ℂ} (hf : Differentiable ℝ f)
    (ha : Function.HasTemperateGrowth a)
    (hode : ∀ x, deriv f x = a x * f x)
    (hunit : ∀ x, ‖f x‖ = 1) :
    Function.HasTemperateGrowth f := by
  have hsmooth := contDiff_infty_of_deriv_eq_mul hf ha.1 hode
  refine ⟨hsmooth, fun n => ?_⟩
  obtain ⟨k, C, hC, hjet⟩ := ha.norm_iteratedFDeriv_le_uniform n
  let C1 : ℝ := max 1 C
  let S : ℝ := ∑ d ∈ (GaloisForLFunctions.bellCore n).support,
    ‖MvPolynomial.coeff d (GaloisForLFunctions.bellCore n)‖
  refine ⟨k * n, S * C1 ^ n, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_bellCore_real_ode hsmooth ha.1 hode n x, norm_mul, hunit]
  simp only [one_mul]
  let B : ℝ := C1 * (1 + ‖x‖) ^ k
  have hC1 : 1 ≤ C1 := le_max_left _ _
  have hbase : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hbasePow : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ hbase
  have hB : 1 ≤ B := by
    dsimp [B]
    exact hC1.trans (le_mul_of_one_le_right (zero_le_one.trans hC1) hbasePow)
  have hv : ∀ j : Fin n,
      ‖iteratedDeriv (j : ℕ) a x‖ ≤ B := by
    intro j
    have hj := hjet (j : ℕ) (Nat.le_of_lt j.isLt) x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hj
    exact hj.trans (by
      dsimp [B, C1]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have heval := GaloisForLFunctions.norm_eval_le_pow
    (GaloisForLFunctions.bellCore n)
    (fun j : Fin n => iteratedDeriv (j : ℕ) a x) B hB hv
  have hdegree : (GaloisForLFunctions.bellCore n).totalDegree ≤ n := by
    rw [bellCore_eq_gammaBell]
    exact GaloisForLFunctions.totalDegree_gammaBell_le n
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hpow : B ^ (GaloisForLFunctions.bellCore n).totalDegree ≤ B ^ n :=
    pow_le_pow_right₀ hB hdegree
  refine heval.trans ((mul_le_mul_of_nonneg_left hpow hS).trans ?_)
  dsimp [S, B, C1]
  rw [mul_pow, ← pow_mul, mul_assoc]

private def gammaHardyPhaseCoefficient (t : ℝ) : ℂ :=
  -Complex.I * (gammaHardyPhaseRate t : ℂ)

private theorem gammaHardyPhaseCoefficient_hasTemperateGrowth :
    Function.HasTemperateGrowth gammaHardyPhaseCoefficient := by
  have hrate := gammaHardyPhaseRate_hasTemperateGrowth
  have hcast : Function.HasTemperateGrowth
      (fun t : ℝ => (gammaHardyPhaseRate t : ℂ)) := by
    simpa [Function.comp_def] using Complex.ofRealCLM.hasTemperateGrowth.comp hrate
  let L : ℂ →L[ℝ] ℂ :=
    ((-Complex.I : ℂ) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ
  have hL := L.hasTemperateGrowth.comp hcast
  change Function.HasTemperateGrowth
    (fun t : ℝ => -Complex.I * (gammaHardyPhaseRate t : ℂ))
  convert hL using 1
  funext t
  simp [L]

/-- The canonical normalized Gamma square-root phase has polynomially bounded derivatives of
every order.  The proof uses its exact phase ODE and the all-order digamma bounds above. -/
theorem gammaHardyPhase_hasTemperateGrowth :
    Function.HasTemperateGrowth (gammaHardyPhase : ℝ → ℂ) := by
  apply hasTemperateGrowth_of_unitary_ode differentiable_gammaHardyPhase
    gammaHardyPhaseCoefficient_hasTemperateGrowth
  · intro t
    exact deriv_gammaHardyPhase t
  · intro t
    exact (gammaHardyPhase_isUnitary t).norm_eq_one

/-- The critical-line Gamma ratio `zetaChi` is a temperate multiplier. -/
theorem zetaChi_line_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun t : ℝ => zetaChi (linePt t)) := by
  have hsquare := (ContinuousLinearMap.mul ℝ ℂ).bilinear_hasTemperateGrowth
    gammaHardyPhase_hasTemperateGrowth gammaHardyPhase_hasTemperateGrowth
  have hfun : (fun t : ℝ => zetaChi (linePt t)) =
      fun t : ℝ => gammaHardyPhase t * gammaHardyPhase t := by
    funext t
    exact (gammaHardyPhase_sq t).symm
  rw [hfun]
  exact hsquare

/-- Connes--Consani's archimedean scattering phase `u_infinity = exp(2 i theta)` in the paper's
Fourier convention.  Since `zetaChi(1/2+it) = exp(-2 i theta(t))`, it is its conjugate. -/
def ccmArchimedeanScatteringPhase (t : ℝ) : ℂ :=
  (starRingEnd ℂ) (zetaChi (linePt t))

@[simp]
theorem norm_ccmArchimedeanScatteringPhase (t : ℝ) :
    ‖ccmArchimedeanScatteringPhase t‖ = 1 := by
  rw [ccmArchimedeanScatteringPhase, Complex.norm_conj, norm_zetaChi_line]

/-- The literal Connes--Consani archimedean phase has temperate growth, with no assumed Gamma
estimate or regularity premise. -/
theorem ccmArchimedeanScatteringPhase_hasTemperateGrowth :
    Function.HasTemperateGrowth ccmArchimedeanScatteringPhase := by
  have hconj := Complex.conjCLE.hasTemperateGrowth.comp zetaChi_line_hasTemperateGrowth
  change Function.HasTemperateGrowth
    (fun t : ℝ => (starRingEnd ℂ) (zetaChi (linePt t)))
  simpa [Function.comp_def] using hconj

/-- Multiplication by the literal archimedean scattering phase on Schwartz space. -/
def ccmArchimedeanScatteringPhaseMul (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ ccmArchimedeanScatteringPhase g

@[simp]
theorem ccmArchimedeanScatteringPhaseMul_apply (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ccmArchimedeanScatteringPhaseMul g t =
      ccmArchimedeanScatteringPhase t * g t := by
  rw [ccmArchimedeanScatteringPhaseMul,
    SchwartzMap.smulLeftCLM_apply_apply ccmArchimedeanScatteringPhase_hasTemperateGrowth]
  exact smul_eq_mul _ _

/-- Source Proposition 7(iv), analytic core: for every Schwartz Mellin symbol, multiplication by
`u_infinity` stays in Schwartz space and its quantized differential is an infinitesimal of every
order.  Trace class follows as the order-one case, but the conclusion records the stronger
Connes--Consani `quantsmooth` statement. -/
theorem ccmArchimedeanScatteringPhase_quantizedDifferential_isInfinitesimalOfInfiniteOrder
    (g : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder
      (ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)) :=
  ccmQuantizedDifferential_isInfinitesimalOfInfiniteOrder _

end RHTower
