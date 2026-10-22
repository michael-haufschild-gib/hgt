import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCesaroSourceRelativeGlobalNormalization
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Complex source-relative CCM-FU global normalization

Complexifies literal finite-aperture reporter before completion. Cubic exponential terminal
asymptotic gives canonical limiting complex transfer symbol. Omitted positive-lower-wall tail is
an exact difference of two compact head integrals multiplied by cofinal decays at rates z+1 and
z+1/2. Therefore every nonzero complex Mellin mode with Re z > -1/2 survives completion with
nonzero coefficient.

All results are unconditional and source-side. This closes complex modal normalization; passage
from actual infinite arithmetic source to its modal expansion remains separate RH-bearing step.
-/

open Set MeasureTheory Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem integral_cpow_three_mul_cexp
    {c : ℂ} (hc : c ≠ 0) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, ((s : ℂ) ^ (3 : ℕ)) * Complex.exp (c * (s : ℂ))) =
      Complex.exp (c * (t : ℂ)) *
          ((t : ℂ) ^ (3 : ℕ) / c - 3 * (t : ℂ) ^ (2 : ℕ) / c ^ (2 : ℕ) +
            6 * (t : ℂ) / c ^ (3 : ℕ) - 6 / c ^ (4 : ℕ)) +
        6 / c ^ (4 : ℕ) := by
  have hA (x : ℝ) :
      GaloisForLFunctions.HTGeometry.cexpAntider (-c) 3 x =
        Complex.exp (c * (x : ℂ)) *
          ((x : ℂ) ^ (3 : ℕ) / c - 3 * (x : ℂ) ^ (2 : ℕ) / c ^ (2 : ℕ) +
            6 * (x : ℂ) / c ^ (3 : ℕ) - 6 / c ^ (4 : ℕ)) := by
    simp only [GaloisForLFunctions.HTGeometry.cexpAntider]
    have he : Complex.exp (-(-c * (x : ℂ))) = Complex.exp (c * (x : ℂ)) := by
      congr 1
      ring
    rw [he]
    field_simp [hc]
    ring
  have hderiv (s : ℝ) : HasDerivAt
      (GaloisForLFunctions.HTGeometry.cexpAntider (-c) 3)
      (((s : ℂ) ^ (3 : ℕ)) * Complex.exp (c * (s : ℂ))) s := by
    have h := GaloisForLFunctions.HTGeometry.hasDerivAt_cexpAntider
      (c := -c) (neg_ne_zero.mpr hc) 3 s
    convert h using 1
    congr 2
    ring
  have hint : IntervalIntegrable
      (fun s : ℝ => ((s : ℂ) ^ (3 : ℕ)) * Complex.exp (c * (s : ℂ))) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) hint
  rw [hA t, hA 0] at hftc
  norm_num [Complex.exp_zero] at hftc
  linear_combination hftc

private theorem tendsto_cexp_mul_real_atTop_zero
    {q : ℂ} (hq : q.re < 0) :
    Tendsto (fun t : ℝ => Complex.exp (q * (t : ℂ))) atTop (nhds 0) := by
  simpa [Complex.tendsto_exp_nhds_zero_iff] using
    tendsto_const_nhds.neg_mul_atTop hq tendsto_id

private def complexCubicExponentialTerminal (c : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(c * (t : ℂ))) / (t : ℂ) ^ (3 : ℕ) *
    ∫ s in (0 : ℝ)..t, ((s : ℂ) ^ (3 : ℕ)) * Complex.exp (c * (s : ℂ))

private theorem tendsto_complexCubicExponentialTerminal
    {c : ℂ} (hc : 0 < c.re) :
    Tendsto (complexCubicExponentialTerminal c) atTop (nhds (1 / c)) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    norm_num at hc
  have hinvR : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
  have hexp : Tendsto (fun t : ℝ => Complex.exp (-(c * (t : ℂ)))) atTop (nhds 0) := by
    convert tendsto_cexp_mul_real_atTop_zero (q := -c) (by simp; linarith) using 1
    funext t
    congr 1
    ring
  have h1 : Tendsto (fun t : ℝ => 3 / (c ^ (2 : ℕ) * (t : ℂ))) atTop (nhds 0) := by
    convert hinv.const_mul (3 / c ^ (2 : ℕ)) using 1
    · funext t
      push_cast
      ring
    · simp
  have h2 : Tendsto (fun t : ℝ => 6 / (c ^ (3 : ℕ) * (t : ℂ) ^ (2 : ℕ))) atTop (nhds 0) := by
    convert (hinv.pow 2).const_mul (6 / c ^ (3 : ℕ)) using 1
    · funext t
      push_cast
      ring
    · simp
  have h3 : Tendsto (fun t : ℝ => 6 / (c ^ (4 : ℕ) * (t : ℂ) ^ (3 : ℕ))) atTop (nhds 0) := by
    convert (hinv.pow 3).const_mul (6 / c ^ (4 : ℕ)) using 1
    · funext t
      push_cast
      ring
    · simp
  have h4 : Tendsto (fun t : ℝ =>
      6 * Complex.exp (-(c * (t : ℂ))) / (c ^ (4 : ℕ) * (t : ℂ) ^ (3 : ℕ)))
      atTop (nhds 0) := by
    convert (hexp.mul (hinv.pow 3)).const_mul (6 / c ^ (4 : ℕ)) using 1
    · funext t
      push_cast
      ring
    · ring
  have hsum : Tendsto (fun t : ℝ =>
      1 / c - 3 / (c ^ (2 : ℕ) * (t : ℂ)) + 6 / (c ^ (3 : ℕ) * (t : ℂ) ^ (2 : ℕ)) -
        6 / (c ^ (4 : ℕ) * (t : ℂ) ^ (3 : ℕ)) +
          6 * Complex.exp (-(c * (t : ℂ))) / (c ^ (4 : ℕ) * (t : ℂ) ^ (3 : ℕ)))
      atTop (nhds (1 / c)) := by
    convert (((tendsto_const_nhds.sub h1).add h2).sub h3).add h4 using 1
    all_goals ring_nf
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [complexCubicExponentialTerminal, integral_cpow_three_mul_cexp hc0 t]
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : Complex.exp (-(c * (t : ℂ))) * Complex.exp (c * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add, show -(c * (t : ℂ)) + c * (t : ℂ) = 0 by ring,
      Complex.exp_zero]
  field_simp [hc0, ht0]
  linear_combination
    -(((c * (t : ℂ)) * ((c * (t : ℂ)) * (c * (t : ℂ) - 3) + 6) - 6)) * he

/-- Full finite-aperture complex Mellin symbol. -/
def unitRieszCesaroComplexFiniteCompletedReporterSymbol (t : ℝ) (z : ℂ) : ℂ :=
  (∫ u in (0 : ℝ)..t,
    Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroApertureKernel t u : ℂ)) - 3 / 64

private theorem unitRieszCesaroComplexFiniteCompletedReporterSymbol_eq
    {t : ℝ} (ht : 0 < t) (z : ℂ) :
    unitRieszCesaroComplexFiniteCompletedReporterSymbol t z =
      -((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) * z ^ (2 : ℕ) *
        ∫ s in (0 : ℝ)..t,
          Complex.exp (-(z * ((t - s : ℝ) : ℂ))) * (unitRieszCesaroTest t s : ℂ) := by
  let f : ℝ → ℂ := fun s => Complex.exp (-(z * ((t - s : ℝ) : ℂ)))
  let G : ℝ → ℂ := fun s => (unitRieszCesaroTest t s : ℂ)
  let G' : ℝ → ℂ := fun s => (unitRieszCesaroTestDeriv t s : ℂ)
  let G'' : ℝ → ℂ := fun s => (unitRieszCesaroTestSecondDeriv t s : ℂ)
  have hf (s : ℝ) : HasDerivAt f (z * f s) s := by
    have hsub : HasDerivAt (fun x : ℝ => ((t - x : ℝ) : ℂ)) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub t).ofReal_comp
    have hinner : HasDerivAt (fun x : ℝ => -(z * ((t - x : ℝ) : ℂ))) z s := by
      have h := (hsub.const_mul z).neg
      exact h.congr_deriv (by ring)
    simpa only [f] using (hinner.cexp.congr_deriv (by ring))
  have hG (s : ℝ) : HasDerivAt G (G' s) s := by
    exact (hasDerivAt_unitRieszCesaroTest t s).ofReal_comp
  have hG' (s : ℝ) : HasDerivAt G' (G'' s) s := by
    exact (hasDerivAt_unitRieszCesaroTestDeriv t s).ofReal_comp
  let F : ℝ → ℂ := fun s => f s * G' s - z * f s * G s
  have hF (s : ℝ) : HasDerivAt F
      (f s * G'' s - z ^ (2 : ℕ) * f s * G s) s := by
    have hleft := (hf s).mul (hG' s)
    have hright := ((hf s).mul (hG s)).const_mul z
    have hraw := hleft.sub hright
    have hraw' := hraw.congr_deriv (show
        z * f s * G' s + f s * G'' s -
            z * (z * f s * G s + f s * G' s) =
          f s * G'' s - z ^ (2 : ℕ) * f s * G s by ring)
    change HasDerivAt (fun x => f x * G' x - z * f x * G x)
      (f s * G'' s - z ^ (2 : ℕ) * f s * G s) s
    apply hraw'.congr_of_eventuallyEq
    filter_upwards with x
    simp only [Pi.mul_apply, Pi.sub_apply, mul_assoc]
  have hfirstInt : IntervalIntegrable (fun s : ℝ => f s * G'' s) volume 0 t := by
    have hfcont : Continuous f := by
      dsimp only [f]
      fun_prop
    have hGcont : Continuous G'' := by
      dsimp only [G'']
      exact Complex.continuous_ofReal.comp (continuous_unitRieszCesaroTestSecondDeriv t)
    exact (hfcont.mul hGcont).intervalIntegrable _ _
  have hsecondInt : IntervalIntegrable
      (fun s : ℝ => z ^ (2 : ℕ) * f s * G s) volume 0 t := by
    have hfcont : Continuous f := by
      dsimp only [f]
      fun_prop
    have hGcont : Continuous G := by
      dsimp only [G]
      exact Complex.continuous_ofReal.comp (continuous_unitRieszCesaroTest t)
    have hc : Continuous (fun s : ℝ => z ^ (2 : ℕ) * (f s * G s)) :=
      continuous_const.mul (hfcont.mul hGcont)
    exact hc.congr (fun s => by ring) |>.intervalIntegrable _ _
  have hderivInt : IntervalIntegrable
      (fun s : ℝ => f s * G'' s - z ^ (2 : ℕ) * f s * G s) volume 0 t :=
    hfirstInt.sub hsecondInt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hF s) hderivInt
  rw [intervalIntegral.integral_sub hfirstInt hsecondInt] at hftc
  have hsecondEq :
      (∫ s in (0 : ℝ)..t, z ^ (2 : ℕ) * f s * G s) =
        z ^ (2 : ℕ) * ∫ s in (0 : ℝ)..t, f s * G s := by
    rw [show (fun s : ℝ => z ^ (2 : ℕ) * f s * G s) =
        fun s : ℝ => z ^ (2 : ℕ) * (f s * G s) by funext s; ring,
      intervalIntegral.integral_const_mul]
  rw [hsecondEq] at hftc
  have hGt : G t = 0 := by simp [G, unitRieszCesaroTest_self]
  have hG0 : G 0 = 0 := by simp [G, unitRieszCesaroTest_zero]
  have hG'0 : G' 0 = 0 := by simp [G', unitRieszCesaroTestDeriv_zero]
  have hG't : G' t = (-(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2) : ℝ) := by
    dsimp only [G']
    rw [unitRieszCesaroTestDeriv_endpoint]
  have hft : f t = 1 := by simp [f]
  have hftc' :
      (∫ s in (0 : ℝ)..t, f s * G'' s) =
        (-(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2) : ℝ) +
          z ^ (2 : ℕ) * ∫ s in (0 : ℝ)..t, f s * G s := by
    dsimp only [F] at hftc
    rw [hGt, hG0, hG'0, hG't, hft] at hftc
    simp only [mul_zero, sub_zero] at hftc
    linear_combination hftc
  let H : ℝ → ℂ := fun u =>
    Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroApertureKernel t u : ℂ)
  have hcv : (∫ u in (0 : ℝ)..t, H u) =
      ∫ s in (0 : ℝ)..t, H (t - s) := by
    simpa using (intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t) H t).symm
  have hkernel : ∀ s : ℝ,
      H (t - s) = -((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) * (f s * G'' s) := by
    intro s
    dsimp only [H, f, G'']
    rw [unitRieszCesaroApertureKernel_eq_secondDeriv]
    rw [show t - (t - s) = s by ring]
    push_cast
    ring
  rw [unitRieszCesaroComplexFiniteCompletedReporterSymbol]
  change (∫ u in (0 : ℝ)..t, H u) - 3 / 64 = _
  rw [hcv]
  simp_rw [hkernel]
  rw [intervalIntegral.integral_const_mul, hftc']
  have ht3 : t ^ (3 : ℕ) ≠ 0 := by positivity
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, show t / 2 + -t / 2 = (0 : ℝ) by ring, Real.exp_zero]
  dsimp only [f, G]
  have hboundary :
      -((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) *
          ((-(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2) : ℝ) : ℂ) = 3 / 64 := by
    have hreal :
        -(Real.exp (t / 2) / t ^ (3 : ℕ)) *
            (-(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2)) = (3 / 64 : ℝ) := by
      calc
        _ = (3 / 64 : ℝ) *
            (Real.exp (t / 2) * Real.exp (-t / 2)) * (t ^ (3 : ℕ) / t ^ (3 : ℕ)) := by ring
        _ = _ := by rw [hexp, div_self ht3]; ring
    calc
      _ = ((-(Real.exp (t / 2) / t ^ (3 : ℕ)) *
          (-(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2)) : ℝ) : ℂ) := by
        push_cast
        ring
      _ = (3 / 64 : ℝ) := by rw [hreal]
      _ = _ := by norm_num
  rw [mul_add, hboundary]
  ring

private theorem complexWeighted_unitRieszCesaroTest_eq_twoChannels
    (t s : ℝ) (z : ℂ) :
    Complex.exp (-(z * ((t - s : ℝ) : ℂ))) * (unitRieszCesaroTest t s : ℂ) =
      (3 / 32 : ℂ) *
        (Complex.exp (-((z + 1) * (t : ℂ))) *
            ((s : ℂ) ^ (3 : ℕ) * Complex.exp ((z + 1 / 2) * (s : ℂ))) -
          Complex.exp (-((z + 3 / 2) * (t : ℂ))) *
            ((s : ℂ) ^ (3 : ℕ) * Complex.exp ((z + 1) * (s : ℂ)))) := by
  rw [unitRieszCesaroTest]
  push_cast
  have hslow :
      Complex.exp (-(z * ((t : ℂ) - (s : ℂ)))) *
          Complex.exp (-(t : ℂ) + (s : ℂ) / 2) =
        Complex.exp (-((z + 1) * (t : ℂ))) *
          Complex.exp ((z + 1 / 2) * (s : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hfast :
      Complex.exp (-(z * ((t : ℂ) - (s : ℂ)))) *
          Complex.exp (-3 * (t : ℂ) / 2 + (s : ℂ)) =
        Complex.exp (-((z + 3 / 2) * (t : ℂ))) *
          Complex.exp ((z + 1) * (s : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [show Complex.exp (-(z * ((t : ℂ) - (s : ℂ)))) *
        ((3 / 32 : ℂ) * ((s : ℂ) ^ (3 : ℕ) *
          (Complex.exp (-(t : ℂ) + (s : ℂ) / 2) -
            Complex.exp (-3 * (t : ℂ) / 2 + (s : ℂ))))) =
      (3 / 32 : ℂ) * (s : ℂ) ^ (3 : ℕ) *
        (Complex.exp (-(z * ((t : ℂ) - (s : ℂ)))) *
            Complex.exp (-(t : ℂ) + (s : ℂ) / 2) -
          Complex.exp (-(z * ((t : ℂ) - (s : ℂ)))) *
            Complex.exp (-3 * (t : ℂ) / 2 + (s : ℂ))) by ring,
    hslow, hfast]
  ring

private theorem integral_complexWeighted_unitRieszCesaroTest_eq_twoChannels
    (r t : ℝ) (z : ℂ) :
    (∫ s in (0 : ℝ)..r,
        Complex.exp (-(z * ((t - s : ℝ) : ℂ))) * (unitRieszCesaroTest t s : ℂ)) =
      (3 / 32 : ℂ) *
        (Complex.exp (-((z + 1) * (t : ℂ))) *
            (∫ s in (0 : ℝ)..r,
              ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1 / 2) * (s : ℂ))) -
          Complex.exp (-((z + 3 / 2) * (t : ℂ))) *
            (∫ s in (0 : ℝ)..r,
              ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1) * (s : ℂ)))) := by
  have hslowInt : IntervalIntegrable
      (fun s : ℝ => ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1 / 2) * (s : ℂ)))
      volume 0 r := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfastInt : IntervalIntegrable
      (fun s : ℝ => ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1) * (s : ℂ)))
      volume 0 r := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    _ = ∫ s in (0 : ℝ)..r, (3 / 32 : ℂ) *
        (Complex.exp (-((z + 1) * (t : ℂ))) *
            ((s : ℂ) ^ (3 : ℕ) * Complex.exp ((z + 1 / 2) * (s : ℂ))) -
          Complex.exp (-((z + 3 / 2) * (t : ℂ))) *
            ((s : ℂ) ^ (3 : ℕ) * Complex.exp ((z + 1) * (s : ℂ)))) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact complexWeighted_unitRieszCesaroTest_eq_twoChannels t s z
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (hslowInt.const_mul _) (hfastInt.const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

private theorem unitRieszCesaroComplexFiniteCompletedReporterSymbol_eq_terminals
    {t : ℝ} (ht : 0 < t) (z : ℂ) :
    unitRieszCesaroComplexFiniteCompletedReporterSymbol t z =
      -(3 / 32 : ℂ) * z ^ (2 : ℕ) *
        (complexCubicExponentialTerminal (z + 1 / 2) t -
          complexCubicExponentialTerminal (z + 1) t) := by
  rw [unitRieszCesaroComplexFiniteCompletedReporterSymbol_eq ht,
    integral_complexWeighted_unitRieszCesaroTest_eq_twoChannels]
  have hslowShift :
      ((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) *
          Complex.exp (-((z + 1) * (t : ℂ))) =
        Complex.exp (-((z + 1 / 2) * (t : ℂ))) / (t : ℂ) ^ (3 : ℕ) := by
    push_cast
    rw [show Complex.exp ((t : ℂ) / 2) / (t : ℂ) ^ (3 : ℕ) *
          Complex.exp (-((z + 1) * (t : ℂ))) =
        (Complex.exp ((t : ℂ) / 2) *
          Complex.exp (-((z + 1) * (t : ℂ)))) / (t : ℂ) ^ (3 : ℕ) by ring,
      ← Complex.exp_add]
    congr 2
    ring
  have hfastShift :
      ((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) *
          Complex.exp (-((z + 3 / 2) * (t : ℂ))) =
        Complex.exp (-((z + 1) * (t : ℂ))) / (t : ℂ) ^ (3 : ℕ) := by
    push_cast
    rw [show Complex.exp ((t : ℂ) / 2) / (t : ℂ) ^ (3 : ℕ) *
          Complex.exp (-((z + 3 / 2) * (t : ℂ))) =
        (Complex.exp ((t : ℂ) / 2) *
          Complex.exp (-((z + 3 / 2) * (t : ℂ)))) / (t : ℂ) ^ (3 : ℕ) by ring,
      ← Complex.exp_add]
    congr 2
    ring
  simp only [complexCubicExponentialTerminal]
  rw [show -((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) * z ^ (2 : ℕ) *
        ((3 / 32 : ℂ) *
          (Complex.exp (-((z + 1) * (t : ℂ))) *
              (∫ s in (0 : ℝ)..t,
                ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1 / 2) * (s : ℂ))) -
            Complex.exp (-((z + 3 / 2) * (t : ℂ))) *
              (∫ s in (0 : ℝ)..t,
                ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1) * (s : ℂ))))) =
      -(3 / 32 : ℂ) * z ^ (2 : ℕ) *
        ((((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) *
            Complex.exp (-((z + 1) * (t : ℂ)))) *
              (∫ s in (0 : ℝ)..t,
                ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1 / 2) * (s : ℂ))) -
          (((Real.exp (t / 2) / t ^ (3 : ℕ) : ℝ) : ℂ) *
            Complex.exp (-((z + 3 / 2) * (t : ℂ)))) *
              (∫ s in (0 : ℝ)..t,
                ((s : ℂ) ^ (3 : ℕ)) * Complex.exp ((z + 1) * (s : ℂ)))) by ring,
    hslowShift, hfastShift]

/-- Complex full finite-aperture reporter converges on the critical-Mellin half-plane. -/
theorem tendsto_unitRieszCesaroComplexFiniteCompletedReporterSymbol
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    Tendsto (fun t : ℝ => unitRieszCesaroComplexFiniteCompletedReporterSymbol t z)
      atTop (nhds (unitRieszCesaroComplexCompletedReporterSymbol z)) := by
  have hslowPos : 0 < (z + 1 / 2).re := by
    norm_num [Complex.add_re, Complex.div_re]
    linarith
  have hfastPos : 0 < (z + 1).re := by
    change 0 < z.re + 1
    linarith
  have hslow := tendsto_complexCubicExponentialTerminal hslowPos
  have hfast := tendsto_complexCubicExponentialTerminal hfastPos
  have hcombo : Tendsto (fun t : ℝ =>
      -(3 / 32 : ℂ) * z ^ (2 : ℕ) *
        (complexCubicExponentialTerminal (z + 1 / 2) t -
          complexCubicExponentialTerminal (z + 1) t)) atTop
      (nhds (-(3 / 32 : ℂ) * z ^ (2 : ℕ) *
        (1 / (z + 1 / 2) - 1 / (z + 1)))) := by
    exact (hslow.sub hfast).const_mul (-(3 / 32 : ℂ) * z ^ (2 : ℕ))
  have hslow0 : z + 1 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.div_re] at hre
    linarith
  have hfast0 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have htwo0 : 2 * z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re] at hre
    linarith
  have htwo0' : 1 + z * 2 ≠ 0 := by
    intro h
    apply htwo0
    linear_combination h
  have hdiff : 1 / (z + 1 / 2) - 1 / (z + 1) =
      1 / ((z + 1) * (2 * z + 1)) := by
    field_simp [hslow0, hfast0, htwo0, htwo0']
    have hunit : (1 + z * 2) * (1 + z * 2)⁻¹ = (1 : ℂ) :=
      mul_inv_cancel₀ htwo0'
    linear_combination hunit
  have hlimit :
      -(3 / 32 : ℂ) * z ^ (2 : ℕ) * (1 / (z + 1 / 2) - 1 / (z + 1)) =
        unitRieszCesaroComplexCompletedReporterSymbol z := by
    rw [hdiff, unitRieszCesaroComplexCompletedReporterSymbol_eq hz]
    ring
  rw [← hlimit]
  apply hcombo.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (unitRieszCesaroComplexFiniteCompletedReporterSymbol_eq_terminals ht z).symm

/-- Literal positive-lower-wall complex reporter. -/
def unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol
    (b t : ℝ) (z : ℂ) : ℂ :=
  (∫ u in (0 : ℝ)..(t - b),
    Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroApertureKernel t u : ℂ)) - 3 / 64

private def complexCofinalDecay (c : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(c * (t : ℂ))) / (t : ℂ) ^ (3 : ℕ)

private theorem tendsto_complexCofinalDecay_zero
    {c : ℂ} (hc : 0 < c.re) :
    Tendsto (complexCofinalDecay c) atTop (nhds 0) := by
  have hinvR : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
  have hexp : Tendsto (fun t : ℝ => Complex.exp (-(c * (t : ℂ)))) atTop (nhds 0) := by
    convert tendsto_cexp_mul_real_atTop_zero (q := -c) (by simp; linarith) using 1
    funext t
    congr 1
    ring
  change Tendsto (fun t : ℝ =>
    Complex.exp (-(c * (t : ℂ))) / (t : ℂ) ^ (3 : ℕ)) atTop (nhds 0)
  convert hexp.mul (hinv.pow 3) using 1
  · funext t
    push_cast
    ring
  · simp

private def unitRieszCesaroComplexSourceRelativeTail
    (b t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (t - b)..t,
    Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroApertureKernel t u : ℂ)

private theorem unitRieszCesaroComplexSourceRelativeTail_eq_twoFixedHeads
    (b t : ℝ) (z : ℂ) :
    unitRieszCesaroComplexSourceRelativeTail b t z =
      (3 / 32 : ℂ) *
        (complexCofinalDecay (z + 1) t *
            (∫ s in (0 : ℝ)..b,
              Complex.exp ((z + 1) * (s : ℂ)) *
                (unitRieszCesaroFastPolynomial s : ℂ)) -
          complexCofinalDecay (z + 1 / 2) t *
            (∫ s in (0 : ℝ)..b,
              Complex.exp ((z + 1 / 2) * (s : ℂ)) *
                (unitRieszCesaroSlowPolynomial s : ℂ))) := by
  let H : ℝ → ℂ := fun u =>
    Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroApertureKernel t u : ℂ)
  have hcv : (∫ u in (t - b)..t, H u) =
      ∫ s in (0 : ℝ)..b, H (t - s) := by
    simpa using (intervalIntegral.integral_comp_sub_left
      (a := t - b) (b := t) H t).symm
  have hpoint (s : ℝ) :
      H (t - s) = (3 / 32 : ℂ) *
        (complexCofinalDecay (z + 1) t *
            (Complex.exp ((z + 1) * (s : ℂ)) *
              (unitRieszCesaroFastPolynomial s : ℂ)) -
          complexCofinalDecay (z + 1 / 2) t *
            (Complex.exp ((z + 1 / 2) * (s : ℂ)) *
              (unitRieszCesaroSlowPolynomial s : ℂ))) := by
    dsimp only [H, complexCofinalDecay]
    rw [unitRieszCesaroApertureKernel]
    rw [show t - (t - s) = s by ring]
    push_cast
    have hfast :
        Complex.exp (-(z * ((t : ℂ) - (s : ℂ)))) *
            Complex.exp (-((t : ℂ) - (s : ℂ))) =
          Complex.exp (-((z + 1) * (t : ℂ))) *
            Complex.exp ((z + 1) * (s : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    have hslow :
        Complex.exp (-(z * ((t : ℂ) - (s : ℂ)))) *
            Complex.exp (-((t : ℂ) - (s : ℂ)) / 2) =
          Complex.exp (-((z + 1 / 2) * (t : ℂ))) *
            Complex.exp ((z + 1 / 2) * (s : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    let Ez : ℂ := Complex.exp (-(z * ((t : ℂ) - (s : ℂ))))
    let Ef : ℂ := Complex.exp (-((t : ℂ) - (s : ℂ)))
    let Es : ℂ := Complex.exp (-((t : ℂ) - (s : ℂ)) / 2)
    let R : ℂ := unitRieszCesaroFastPolynomial s
    let P : ℂ := unitRieszCesaroSlowPolynomial s
    change Ez * ((3 / 32 : ℂ) * (Ef * R - Es * P) / (t : ℂ) ^ (3 : ℕ)) = _
    have hfast' : Ez * Ef =
        Complex.exp (-((z + 1) * (t : ℂ))) *
          Complex.exp ((z + 1) * (s : ℂ)) := hfast
    have hslow' : Ez * Es =
        Complex.exp (-((z + 1 / 2) * (t : ℂ))) *
          Complex.exp ((z + 1 / 2) * (s : ℂ)) := hslow
    calc
      Ez * ((3 / 32 : ℂ) * (Ef * R - Es * P) / (t : ℂ) ^ (3 : ℕ)) =
          (3 / 32 : ℂ) / (t : ℂ) ^ (3 : ℕ) * (Ez * Ef * R - Ez * Es * P) := by ring
      _ = _ := by
        rw [hfast', hslow']
        dsimp only [complexCofinalDecay, R, P]
        ring
  have hfastInt : IntervalIntegrable
      (fun s : ℝ => Complex.exp ((z + 1) * (s : ℂ)) *
        (unitRieszCesaroFastPolynomial s : ℂ)) volume 0 b := by
    apply Continuous.intervalIntegrable
    have hExp : Continuous (fun s : ℝ => Complex.exp ((z + 1) * (s : ℂ))) := by
      fun_prop
    have hPoly : Continuous (fun s : ℝ => (unitRieszCesaroFastPolynomial s : ℂ)) :=
      Complex.continuous_ofReal.comp (by unfold unitRieszCesaroFastPolynomial; fun_prop)
    exact hExp.mul hPoly
  have hslowInt : IntervalIntegrable
      (fun s : ℝ => Complex.exp ((z + 1 / 2) * (s : ℂ)) *
        (unitRieszCesaroSlowPolynomial s : ℂ)) volume 0 b := by
    apply Continuous.intervalIntegrable
    have hExp : Continuous (fun s : ℝ => Complex.exp ((z + 1 / 2) * (s : ℂ))) := by
      fun_prop
    have hPoly : Continuous (fun s : ℝ => (unitRieszCesaroSlowPolynomial s : ℂ)) :=
      Complex.continuous_ofReal.comp (by unfold unitRieszCesaroSlowPolynomial; fun_prop)
    exact hExp.mul hPoly
  rw [unitRieszCesaroComplexSourceRelativeTail, hcv]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (hfastInt.const_mul _) (hslowInt.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

private theorem tendsto_unitRieszCesaroComplexSourceRelativeTail_zero
    (b : ℝ) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    Tendsto (fun t : ℝ => unitRieszCesaroComplexSourceRelativeTail b t z)
      atTop (nhds 0) := by
  have hfast : Tendsto (complexCofinalDecay (z + 1)) atTop (nhds 0) :=
    tendsto_complexCofinalDecay_zero (by change 0 < z.re + 1; linarith)
  have hslow : Tendsto (complexCofinalDecay (z + 1 / 2)) atTop (nhds 0) :=
    tendsto_complexCofinalDecay_zero (by
      norm_num [Complex.add_re, Complex.div_re]
      linarith)
  let Ifast : ℂ := ∫ s in (0 : ℝ)..b,
    Complex.exp ((z + 1) * (s : ℂ)) * (unitRieszCesaroFastPolynomial s : ℂ)
  let Islow : ℂ := ∫ s in (0 : ℝ)..b,
    Complex.exp ((z + 1 / 2) * (s : ℂ)) * (unitRieszCesaroSlowPolynomial s : ℂ)
  have hcombo := ((hfast.const_mul Ifast).sub (hslow.const_mul Islow)).const_mul
    (3 / 32 : ℂ)
  have hcombo' : Tendsto (fun t : ℝ => (3 / 32 : ℂ) *
      (complexCofinalDecay (z + 1) t * Ifast -
        complexCofinalDecay (z + 1 / 2) t * Islow)) atTop (nhds 0) := by
    convert hcombo using 1
    · funext t
      ring
    · simp
  apply hcombo'.congr'
  filter_upwards with t
  exact (unitRieszCesaroComplexSourceRelativeTail_eq_twoFixedHeads b t z).symm

private theorem unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol_eq_finite_sub_tail
    (b t : ℝ) (z : ℂ) :
    unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol b t z =
      unitRieszCesaroComplexFiniteCompletedReporterSymbol t z -
        unitRieszCesaroComplexSourceRelativeTail b t z := by
  let H : ℝ → ℂ := fun u =>
    Complex.exp (-(z * (u : ℂ))) * (unitRieszCesaroApertureKernel t u : ℂ)
  have hH : Continuous H := by
    dsimp only [H]
    have hExp : Continuous (fun u : ℝ => Complex.exp (-(z * (u : ℂ)))) := by
      fun_prop
    exact hExp.mul
      (Complex.continuous_ofReal.comp (continuous_unitRieszCesaroApertureKernel t))
  have hleft : IntervalIntegrable H volume 0 (t - b) := hH.intervalIntegrable _ _
  have hright : IntervalIntegrable H volume (t - b) t := hH.intervalIntegrable _ _
  rw [unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol,
    unitRieszCesaroComplexFiniteCompletedReporterSymbol,
    unitRieszCesaroComplexSourceRelativeTail]
  change (∫ u in (0 : ℝ)..(t - b), H u) - 3 / 64 =
    ((∫ u in (0 : ℝ)..t, H u) - 3 / 64) - ∫ u in (t - b)..t, H u
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  ring

/-- Complex source-relative reporter converges coefficient-faithfully on the whole half-plane. -/
theorem tendsto_unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol
    (b : ℝ) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    Tendsto (fun t : ℝ =>
      unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol b t z)
      atTop (nhds (unitRieszCesaroComplexCompletedReporterSymbol z)) := by
  have hfinite := tendsto_unitRieszCesaroComplexFiniteCompletedReporterSymbol hz
  have htail := tendsto_unitRieszCesaroComplexSourceRelativeTail_zero b hz
  have hdiff := hfinite.sub htail
  have hdiff' : Tendsto (fun t : ℝ =>
      unitRieszCesaroComplexFiniteCompletedReporterSymbol t z -
        unitRieszCesaroComplexSourceRelativeTail b t z) atTop
      (nhds (unitRieszCesaroComplexCompletedReporterSymbol z)) := by
    simpa using hdiff
  apply hdiff'.congr'
  filter_upwards with t
  exact (unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol_eq_finite_sub_tail
    b t z).symm

/-- Closed complex source-relative normalization with no hidden zero mode. -/
def CCMUnitRieszCesaroComplexSourceRelativeGlobalNormalization : Prop :=
  ∀ b : ℝ, ∀ z : ℂ, -(1 / 2 : ℝ) < z.re → z ≠ 0 →
    Tendsto (fun t : ℝ =>
      unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol b t z)
      atTop (nhds (unitRieszCesaroComplexCompletedReporterSymbol z)) ∧
    unitRieszCesaroComplexCompletedReporterSymbol z ≠ 0

/-- Complex modes survive literal source-wall completion coefficient-faithfully. -/
theorem ccmUnitRieszCesaroComplexSourceRelativeGlobalNormalization :
    CCMUnitRieszCesaroComplexSourceRelativeGlobalNormalization := by
  intro b z hz hz0
  exact ⟨tendsto_unitRieszCesaroComplexSourceRelativeCompletedReporterSymbol b hz,
    (unitRieszCesaroComplexCompletedReporterSymbol_eq_zero_iff hz).not.mpr hz0⟩

end GaloisForLFunctions.RHTower

