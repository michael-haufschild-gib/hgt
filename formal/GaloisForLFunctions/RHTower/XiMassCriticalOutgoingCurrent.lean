import GaloisForLFunctions.RHTower.XiMassCriticalErrorFlux
import GaloisForLFunctions.RHTower.CCM.CCMSawtoothDilationMean

/-!
# Critical outgoing-current transference for the Xi mass face

The completed critical-Mellin error is a causal Volterra transform of normalized Chebyshev error.
This module moves that Volterra primitive onto the smooth mass Fourier profile by an exact complex
integration-by-parts/Fubini identity.  On every finite positive logarithmic interval, the completed
error current becomes the sum of:

* mass-profile value at zero;
* an explicit exponentially damped Fourier integral;
* normalized Chebyshev error paired with the outgoing operator `1/2 - d/dh`;
* an exact terminal boundary term.

All estimates and identities are unconditional.  No RH hypothesis, numerical computation, or
assumed source bound occurs.  This identifies the precise source functional left in the
mass-shifted spectral-face open core.
-/

open Filter MeasureTheory Set Topology

namespace RHTower

theorem complex_integral_deriv_mul_primitive {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} {phi phi' : ℝ → ℂ}
    (hg : Measurable g) {Cg : ℝ} (hgb : ∀ t, |g t| ≤ Cg)
    (hphi'meas : Measurable phi')
    (hphi : ∀ u ∈ Icc a b, HasDerivAt phi (phi' u) u) {Cd : ℝ}
    (hphi'b : ∀ u ∈ Icc a b, ‖phi' u‖ ≤ Cd)
    (hleft : IntegrableOn (fun u => phi' u * ((∫ t in a..u, g t : ℝ) : ℂ)) (Ioc a b))
    (hright : IntegrableOn (fun t => phi t * (g t : ℂ)) (Ioc a b)) :
    (∫ u in a..b, phi' u * ((∫ t in a..u, g t : ℝ) : ℂ)) =
      phi b * ((∫ t in a..b, g t : ℝ) : ℂ) - ∫ t in a..b, phi t * (g t : ℂ) := by
  have hre := GaloisForLFunctions.RHTower.integral_deriv_mul_primitive hab hg hgb
    (hphi'meas.re) (fun u hu =>
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hphi u hu))
    (fun u hu => (Complex.abs_re_le_norm (phi' u)).trans (hphi'b u hu))
  have him := GaloisForLFunctions.RHTower.integral_deriv_mul_primitive hab hg hgb
    (hphi'meas.im) (fun u hu =>
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt u (hphi u hu))
    (fun u hu => (Complex.abs_im_le_norm (phi' u)).trans (hphi'b u hu))
  change (∫ u in a..b, (phi' u).re * ∫ t in a..u, g t) =
      (phi b).re * (∫ t in a..b, g t) - ∫ t in a..b, (phi t).re * g t at hre
  change (∫ u in a..b, (phi' u).im * ∫ t in a..u, g t) =
      (phi b).im * (∫ t in a..b, g t) - ∫ t in a..b, (phi t).im * g t at him
  apply Complex.ext
  · have hLre :
        (∫ u in a..b, phi' u * ((∫ t in a..u, g t : ℝ) : ℂ)).re =
          ∫ u in a..b, (phi' u * ((∫ t in a..u, g t : ℝ) : ℂ)).re := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact (integral_re hleft).symm
    have hRre :
        (∫ t in a..b, phi t * (g t : ℂ)).re =
          ∫ t in a..b, (phi t * (g t : ℂ)).re := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact (integral_re hright).symm
    rw [hLre, Complex.sub_re, Complex.mul_re, hRre]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      zero_mul, add_zero, Function.comp_apply] using hre
  · have hLim :
        (∫ u in a..b, phi' u * ((∫ t in a..u, g t : ℝ) : ℂ)).im =
          ∫ u in a..b, (phi' u * ((∫ t in a..u, g t : ℝ) : ℂ)).im := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact (integral_im hleft).symm
    have hRim :
        (∫ t in a..b, phi t * (g t : ℂ)).im =
          ∫ t in a..b, (phi t * (g t : ℂ)).im := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact (integral_im hright).symm
    rw [hLim, Complex.sub_im, Complex.mul_im, hRim]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      add_zero, zero_add, Function.comp_apply] using him

end RHTower

namespace RHTower

open ArithmeticFunction Finset

theorem measurable_criticalMellinNormalizedChebyshevError :
    Measurable criticalMellinNormalizedChebyshevError := by
  let C : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 0 m, ArithmeticFunction.vonMangoldt k
  have hC : Measurable C := measurable_of_countable C
  have hfloor : Measurable (fun h : ℝ => ⌊Real.exp h⌋₊) :=
    Real.measurable_exp.nat_floor
  change Measurable (fun h : ℝ => (C ⌊Real.exp h⌋₊ - Real.exp h) /
    Real.sqrt (Real.exp h))
  exact ((hC.comp hfloor).sub Real.measurable_exp).div
    (Real.continuous_sqrt.comp Real.continuous_exp).measurable

theorem criticalCumulative_vonMangoldt_nonneg (t : ℝ) :
    0 ≤ criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) t := by
  rw [criticalCumulative]
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem criticalCumulative_vonMangoldt_mono :
    Monotone (criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k)) := by
  intro a b hab
  rw [criticalCumulative, criticalCumulative]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans (Nat.floor_mono hab)⟩
  · intro k _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The critical cumulative von Mangoldt mass is Chebyshev's `psi`. -/
theorem criticalCumulative_vonMangoldt_eq_psi (X : ℝ) :
    criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X =
      Chebyshev.psi X := by
  rw [criticalCumulative, Chebyshev.psi_eq_sum_Icc]

/-- Unconditional global square-root-scale bound for normalized Chebyshev error.  It uses only the
corpus inequalities `psi(X)/sqrt(X) ≤ primeMassHalf(X)` and
`primeMassHalf(X) ≤ 2 log(X) sqrt(X)`; no PNT remainder enters. -/
theorem abs_criticalMellinNormalizedChebyshevError_le_log_sqrt
    {h : ℝ} (hh : 0 ≤ h) :
    |criticalMellinNormalizedChebyshevError h| ≤
      (2 * h + 1) * Real.exp (h / 2) := by
  let X : ℝ := Real.exp h
  have hX0 : 0 ≤ X := (Real.exp_pos h).le
  have hX1 : 1 ≤ X := Real.one_le_exp hh
  have hsqrt : Real.sqrt X = Real.exp (h / 2) := by
    dsimp only [X]
    rw [← Real.exp_half]
  have hsqrt0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr (Real.exp_pos h)
  have hcum0 :
      0 ≤ criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X :=
    criticalCumulative_vonMangoldt_nonneg X
  have hcumDiv :
      criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X /
          Real.sqrt X ≤ primeMassHalf X := by
    rw [criticalCumulative_vonMangoldt_eq_psi]
    exact psi_div_sqrt_le_primeMassHalf hX0
  have hmainDiv : X / Real.sqrt X = Real.exp (h / 2) := by
    rw [hsqrt]
    dsimp only [X]
    rw [← Real.exp_sub]
    congr 1
    ring
  have hmass := primeMassHalf_le hX1
  rw [show Real.log X = h by simp [X], hsqrt] at hmass
  rw [criticalMellinNormalizedChebyshevError, criticalMellinError, abs_div,
    abs_of_pos hsqrt0]
  change |criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X - X| /
      Real.sqrt X ≤ _
  calc
    |criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X - X| /
          Real.sqrt X ≤
        (criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X + X) /
          Real.sqrt X := by
            apply div_le_div_of_nonneg_right _ hsqrt0.le
            simpa [abs_of_nonneg hcum0, abs_of_nonneg hX0] using
              (abs_sub_le
                (criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X)
                0 X)
    _ = criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) X /
          Real.sqrt X + X / Real.sqrt X := by ring
    _ ≤ primeMassHalf X + Real.exp (h / 2) := add_le_add hcumDiv (le_of_eq hmainDiv)
    _ ≤ 2 * h * Real.exp (h / 2) + Real.exp (h / 2) :=
      add_le_add hmass le_rfl
    _ = (2 * h + 1) * Real.exp (h / 2) := by ring

theorem abs_criticalMellinNormalizedChebyshevError_le_endpoint
    {H h : ℝ} (hh : h ∈ Icc (0 : ℝ) H) :
    |criticalMellinNormalizedChebyshevError h| ≤
      criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp H) +
        Real.exp H := by
  have hcum0 := criticalCumulative_vonMangoldt_nonneg (Real.exp h)
  have hcum := criticalCumulative_vonMangoldt_mono (Real.exp_le_exp.mpr hh.2)
  have hexp0 : 0 ≤ Real.exp h := (Real.exp_pos h).le
  have hexp := Real.exp_le_exp.mpr hh.2
  have hsqrt1 : 1 ≤ Real.sqrt (Real.exp h) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (Real.one_le_exp hh.1)
  have hsqrt0 : 0 < Real.sqrt (Real.exp h) := Real.sqrt_pos.mpr (Real.exp_pos h)
  rw [criticalMellinNormalizedChebyshevError, abs_div]
  calc
    |criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h)| /
          |Real.sqrt (Real.exp h)|
        ≤ (criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) +
            Real.exp h) / Real.sqrt (Real.exp h) := by
          rw [abs_of_pos hsqrt0]
          apply div_le_div_of_nonneg_right _ hsqrt0.le
          rw [criticalMellinError]
          calc
            |criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) -
                Real.exp h| ≤
                |criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h)| +
                  |Real.exp h| := by
                    simpa only [sub_zero, zero_sub, abs_neg] using
                      (abs_sub_le
                        (criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k)
                          (Real.exp h)) 0 (Real.exp h))
            _ = criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) +
                  Real.exp h := by rw [abs_of_nonneg hcum0, abs_of_pos (Real.exp_pos h)]
    _ ≤ criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) +
          Real.exp h := by
          exact (div_le_iff₀ hsqrt0).2
            (le_mul_of_one_le_right (add_nonneg hcum0 hexp0) hsqrt1)
    _ ≤ criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp H) +
          Real.exp H := add_le_add hcum hexp

noncomputable def criticalMellinNormalizedErrorCutoff (H h : ℝ) : ℝ :=
  if h ∈ Icc (0 : ℝ) H then criticalMellinNormalizedChebyshevError h else 0

theorem measurable_criticalMellinNormalizedErrorCutoff (H : ℝ) :
    Measurable (criticalMellinNormalizedErrorCutoff H) := by
  exact Measurable.ite measurableSet_Icc measurable_criticalMellinNormalizedChebyshevError
    measurable_const

theorem abs_criticalMellinNormalizedErrorCutoff_le (H h : ℝ) :
    |criticalMellinNormalizedErrorCutoff H h| ≤
      criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp H) +
        Real.exp H := by
  rw [criticalMellinNormalizedErrorCutoff]
  split_ifs with hh
  · exact abs_criticalMellinNormalizedChebyshevError_le_endpoint hh
  · rw [abs_zero]
    exact add_nonneg (criticalCumulative_vonMangoldt_nonneg _) (Real.exp_pos H).le

theorem integral_criticalMellinNormalizedErrorCutoff_eq
    {H u : ℝ} (hu : u ∈ Icc (0 : ℝ) H) :
    (∫ t in (0 : ℝ)..u, criticalMellinNormalizedErrorCutoff H t) =
      ∫ t in (0 : ℝ)..u, criticalMellinNormalizedChebyshevError t := by
  apply GaloisForLFunctions.RHTower.integral_congr_of_Ioo hu.1
  intro t ht
  rw [criticalMellinNormalizedErrorCutoff, if_pos]
  exact ⟨ht.1.le, ht.2.le.trans hu.2⟩

theorem criticalMellinCompletedError_eq_cutoff_volterra
    {H h : ℝ} (hh : h ∈ Icc (0 : ℝ) H) :
    criticalMellinCompletedError h =
      1 - 2 * Real.exp (-h / 2) - criticalMellinNormalizedErrorCutoff H h -
        (1 / 2 : ℝ) *
          ∫ t in (0 : ℝ)..h, criticalMellinNormalizedErrorCutoff H t := by
  rw [criticalMellinCompletedError_eq_volterraPotential hh.1,
    criticalMellinChebyshevVolterraPotential,
    criticalMellinNormalizedErrorCutoff, if_pos hh,
    integral_criticalMellinNormalizedErrorCutoff_eq hh]
  have hsqrt : Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
    rw [← Real.exp_half]
  have hinv : (Real.exp (h / 2))⁻¹ = Real.exp (-h / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hsqrt, div_eq_mul_inv, hinv]
  rw [intervalIntegral.integral_of_le hh.1]

noncomputable def xiMassCriticalOutgoingDerivative (a sigma u h : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * Complex.I)) (h : ℂ) -
    xiMassFourierDerivative a sigma u h

theorem integral_xiMassCompletedError_mul_deriv_eq_outgoing
    {a sigma H : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (hH : 0 ≤ H) (u : ℝ) :
    (∫ h in (0 : ℝ)..H,
        (criticalMellinCompletedError h : ℂ) * xiMassFourierDerivative a sigma u h) =
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * Complex.I)) 0 -
        (∫ h in (0 : ℝ)..H,
          (Real.exp (-h / 2) : ℂ) *
            stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * Complex.I)) (h : ℂ)) +
        (∫ h in (0 : ℝ)..H,
          (criticalMellinNormalizedChebyshevError h : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h) +
        ((criticalMellinCompletedError H +
            criticalMellinNormalizedChebyshevError H : ℝ) : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * Complex.I)) (H : ℂ) := by
  let g : ℝ → ℝ := criticalMellinNormalizedErrorCutoff H
  let F : ℝ → ℂ := fun h =>
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * Complex.I)) (h : ℂ)
  let F' : ℝ → ℂ := xiMassFourierDerivative a sigma u
  let V : ℝ → ℝ := fun h => ∫ t in (0 : ℝ)..h, g t
  let w : ℝ → ℂ := fun h => (Real.exp (-h / 2) : ℂ)
  have hgmeas : Measurable g := measurable_criticalMellinNormalizedErrorCutoff H
  let C : ℝ := criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp H) +
    Real.exp H
  have hgbound : ∀ h, |g h| ≤ C := abs_criticalMellinNormalizedErrorCutoff_le H
  have hgint : ∀ x y : ℝ, IntervalIntegrable g volume x y :=
    fun x y => GaloisForLFunctions.RHTower.intervalIntegrable_of_bound hgmeas hgbound x y
  have hgintC : ∀ x y : ℝ, IntervalIntegrable (fun h => (g h : ℂ)) volume x y := by
    intro x y
    constructor
    · exact Complex.ofRealCLM.integrable_comp (hgint x y).1
    · exact Complex.ofRealCLM.integrable_comp (hgint x y).2
  have hFderiv : ∀ h, HasDerivAt F (F' h) h := fun h =>
    hasDerivAt_xiMassRealFourierProfile ha hsigma u h
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr fun h => (hFderiv h).continuousAt
  have hF'cont : Continuous F' := continuous_xiMassFourierDerivative ha hsigma u
  have hVcont : Continuous V := intervalIntegral.continuous_primitive hgint 0
  have hwcont : Continuous w := by
    dsimp only [w]
    fun_prop
  have hF'int : IntervalIntegrable F' volume 0 H := hF'cont.intervalIntegrable _ _
  have hwint : IntervalIntegrable w volume 0 H := hwcont.intervalIntegrable _ _
  have hVint : IntervalIntegrable (fun h => (V h : ℂ)) volume 0 H :=
    (Complex.continuous_ofReal.comp hVcont).intervalIntegrable _ _
  have hwF'int : IntervalIntegrable (fun h => w h * F' h) volume 0 H :=
    (hwcont.mul hF'cont).intervalIntegrable _ _
  have hwFint : IntervalIntegrable (fun h => w h * F h) volume 0 H :=
    (hwcont.mul hFcont).intervalIntegrable _ _
  have hVF'int : IntervalIntegrable (fun h => (V h : ℂ) * F' h) volume 0 H :=
    ((Complex.continuous_ofReal.comp hVcont).mul hF'cont).intervalIntegrable _ _
  have hgF'int : IntervalIntegrable (fun h => (g h : ℂ) * F' h) volume 0 H :=
    (hgintC 0 H).mul_continuousOn hF'cont.continuousOn
  have hgFint : IntervalIntegrable (fun h => (g h : ℂ) * F h) volume 0 H :=
    (hgintC 0 H).mul_continuousOn hFcont.continuousOn
  have hleftOn : IntegrableOn (fun h => F' h * (V h : ℂ)) (Ioc (0 : ℝ) H) := by
    exact (((hF'cont.mul (Complex.continuous_ofReal.comp hVcont)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self)
  have hrightOn : IntegrableOn (fun h => F h * (g h : ℂ)) (Ioc (0 : ℝ) H) := by
    exact (hgFint.congr (fun h _ => mul_comm (g h : ℂ) (F h))).1
  have hVadj :
      (∫ h in (0 : ℝ)..H, F' h * (V h : ℂ)) =
        F H * ((∫ h in (0 : ℝ)..H, g h : ℝ) : ℂ) -
          ∫ h in (0 : ℝ)..H, F h * (g h : ℂ) := by
    apply complex_integral_deriv_mul_primitive hH hgmeas hgbound hF'cont.measurable
      (fun h _ => hFderiv h)
      (Cd := ∫ x : ℝ, (|x| + 0) * Real.exp (-(sigma * |x|)))
    · intro h _
      simpa using norm_xiMassFourierDerivative_deepShift_le
        (a := a) (σ := sigma) (d := 0) (by norm_num) ha hsigma u h
    · simpa only [V] using hleftOn
    · exact hrightOn
  have hFTC : (∫ h in (0 : ℝ)..H, F' h) = F H - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun h _ => hFderiv h) hF'int
  have hwderiv : ∀ h, HasDerivAt w ((-1 / 2 : ℂ) * w h) h := by
    intro h
    have hlin : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2 : ℝ) h := by
      simpa using (hasDerivAt_id h).neg.div_const (2 : ℝ)
    have hr : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
        ((-1 / 2 : ℝ) * Real.exp (-h / 2)) h := by
      have hraw : HasDerivAt (Real.exp ∘ fun x : ℝ => -x / 2)
          ((-1 / 2 : ℝ) * Real.exp (-h / 2)) h :=
        ((Real.hasDerivAt_exp (-h / 2)).comp h hlin).congr_deriv (by ring)
      apply hraw.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun _ => rfl
    change HasDerivAt (fun x : ℝ => (Real.exp (-x / 2) : ℂ))
      ((-1 / 2 : ℂ) * (Real.exp (-h / 2) : ℂ)) h
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_ofNat] using hr.ofReal_comp
  have hw'int : IntervalIntegrable (fun h => (-1 / 2 : ℂ) * w h) volume 0 H :=
    hwint.const_mul _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := H) (u := w) (v := F)
    (fun h _ => hwderiv h) (fun h _ => hFderiv h) hw'int hF'int
  have hmodel :
      (∫ h in (0 : ℝ)..H,
          (criticalMellinCompletedError h : ℂ) * F' h) =
        ∫ h in (0 : ℝ)..H,
          (F' h - 2 * (w h * F' h) - (g h : ℂ) * F' h -
            (1 / 2 : ℂ) * ((V h : ℂ) * F' h)) := by
    apply intervalIntegral.integral_congr
    intro h hh
    have hh' : h ∈ Icc (0 : ℝ) H := by
      rw [uIcc_of_le hH] at hh
      exact hh
    change (criticalMellinCompletedError h : ℂ) * F' h = _
    rw [criticalMellinCompletedError_eq_cutoff_volterra hh']
    simp only [F', V, w, g]
    push_cast
    ring
  rw [hmodel]
  rw [intervalIntegral.integral_sub
      (((hF'int.sub (hwF'int.const_mul (2 : ℂ)))).sub hgF'int)
      (hVF'int.const_mul (1 / 2 : ℂ))]
  rw [intervalIntegral.integral_sub (hF'int.sub (hwF'int.const_mul (2 : ℂ))) hgF'int]
  rw [intervalIntegral.integral_sub hF'int (hwF'int.const_mul (2 : ℂ))]
  simp only [intervalIntegral.integral_const_mul]
  rw [hFTC]
  have hIBP' :
      (∫ h in (0 : ℝ)..H, w h * F' h) =
        w H * F H - w 0 * F 0 + (1 / 2 : ℂ) * ∫ h in (0 : ℝ)..H, w h * F h := by
    rw [hIBP]
    have hneg :
        (∫ h in (0 : ℝ)..H, ((-1 / 2 : ℂ) * w h) * F h) =
          -(1 / 2 : ℂ) * ∫ h in (0 : ℝ)..H, w h * F h := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro h _
      ring
    rw [hneg]
    ring
  rw [hIBP']
  have hVadj' :
      (∫ h in (0 : ℝ)..H, (V h : ℂ) * F' h) =
        F H * ((∫ h in (0 : ℝ)..H, g h : ℝ) : ℂ) -
          ∫ h in (0 : ℝ)..H, (g h : ℂ) * F h := by
    rw [show (fun h => (V h : ℂ) * F' h) = fun h => F' h * (V h : ℂ) by
      funext h; ring, hVadj]
    congr 1
    rw [show (fun h => F h * (g h : ℂ)) = fun h => (g h : ℂ) * F h by
      funext h; ring]
  rw [hVadj']
  have hgintEq :
      (∫ h in (0 : ℝ)..H, g h) =
        ∫ h in (0 : ℝ)..H, criticalMellinNormalizedChebyshevError h :=
    integral_criticalMellinNormalizedErrorCutoff_eq ⟨hH, le_rfl⟩
  have hgF'Eq :
      (∫ h in (0 : ℝ)..H, (g h : ℂ) * F' h) =
        ∫ h in (0 : ℝ)..H,
          (criticalMellinNormalizedChebyshevError h : ℂ) * F' h := by
    apply intervalIntegral.integral_congr
    intro h hh
    have hh' : h ∈ Icc (0 : ℝ) H := by
      rw [uIcc_of_le hH] at hh
      exact hh
    dsimp only [g]
    rw [criticalMellinNormalizedErrorCutoff, if_pos hh']
  have hgFEq :
      (∫ h in (0 : ℝ)..H, (g h : ℂ) * F h) =
        ∫ h in (0 : ℝ)..H,
          (criticalMellinNormalizedChebyshevError h : ℂ) * F h := by
    apply intervalIntegral.integral_congr
    intro h hh
    have hh' : h ∈ Icc (0 : ℝ) H := by
      rw [uIcc_of_le hH] at hh
      exact hh
    dsimp only [g]
    rw [criticalMellinNormalizedErrorCutoff, if_pos hh']
  rw [hgintEq, hgF'Eq, hgFEq]
  have heF'int : IntervalIntegrable
      (fun h => (criticalMellinNormalizedChebyshevError h : ℂ) * F' h) volume 0 H := by
    refine IntervalIntegrable.congr ?_ hgF'int
    intro h hh
    have hu : h ∈ uIcc (0 : ℝ) H := uIoc_subset_uIcc hh
    have hh' : h ∈ Icc (0 : ℝ) H := by
      rw [uIcc_of_le hH] at hu
      exact hu
    dsimp only [g]
    rw [criticalMellinNormalizedErrorCutoff, if_pos hh']
  have heFint : IntervalIntegrable
      (fun h => (criticalMellinNormalizedChebyshevError h : ℂ) * F h) volume 0 H := by
    refine IntervalIntegrable.congr ?_ hgFint
    intro h hh
    have hu : h ∈ uIcc (0 : ℝ) H := uIoc_subset_uIcc hh
    have hh' : h ∈ Icc (0 : ℝ) H := by
      rw [uIcc_of_le hH] at hu
      exact hu
    dsimp only [g]
    rw [criticalMellinNormalizedErrorCutoff, if_pos hh']
  have hout :
      (∫ h in (0 : ℝ)..H,
          (criticalMellinNormalizedChebyshevError h : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h) =
        (1 / 2 : ℂ) * (∫ h in (0 : ℝ)..H,
            (criticalMellinNormalizedChebyshevError h : ℂ) * F h) -
          (∫ h in (0 : ℝ)..H,
            (criticalMellinNormalizedChebyshevError h : ℂ) * F' h) := by
    calc
      _ = ∫ h in (0 : ℝ)..H,
          (1 / 2 : ℂ) *
              ((criticalMellinNormalizedChebyshevError h : ℂ) * F h) -
            (criticalMellinNormalizedChebyshevError h : ℂ) * F' h := by
            apply intervalIntegral.integral_congr
            intro h _
            dsimp only [xiMassCriticalOutgoingDerivative, F, F']
            ring
      _ = (1 / 2 : ℂ) * (∫ h in (0 : ℝ)..H,
            (criticalMellinNormalizedChebyshevError h : ℂ) * F h) -
          (∫ h in (0 : ℝ)..H,
            (criticalMellinNormalizedChebyshevError h : ℂ) * F' h) := by
            rw [intervalIntegral.integral_sub
              (heFint.const_mul (1 / 2 : ℂ)) heF'int]
            rw [intervalIntegral.integral_const_mul]
  calc
    _ = F 0 - (∫ h in (0 : ℝ)..H, w h * F h) +
          ((1 / 2 : ℂ) * (∫ h in (0 : ℝ)..H,
              (criticalMellinNormalizedChebyshevError h : ℂ) * F h) -
            (∫ h in (0 : ℝ)..H,
              (criticalMellinNormalizedChebyshevError h : ℂ) * F' h)) +
          ((criticalMellinCompletedError H +
              criticalMellinNormalizedChebyshevError H : ℝ) : ℂ) * F H := by
        have hw0 : w 0 = 1 := by simp [w]
        have hwH : w H = (Real.exp (-H / 2) : ℂ) := rfl
        rw [hw0, hwH]
        rw [criticalMellinCompletedError_eq_cutoff_volterra ⟨hH, le_rfl⟩]
        rw [integral_criticalMellinNormalizedErrorCutoff_eq ⟨hH, le_rfl⟩]
        simp only [criticalMellinNormalizedErrorCutoff, if_pos, Set.mem_Icc,
          le_refl, and_true, hH]
        push_cast
        ring
    _ = _ := by
      rw [← hout]
      rfl

theorem tendsto_xiMassNormalizedChebyshevError_terminal_zero
    {a sigma : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Tendsto
      (fun H : ℝ =>
        (criticalMellinNormalizedChebyshevError H : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (H : ℂ))
      atTop (𝓝 0) := by
  let d : ℝ := (a + 1 / 2) / 2
  let delta : ℝ := d - 1 / 2
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  let K : ℝ := Real.exp (|u| * d) * J
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have hdelta : 0 < delta := by dsimp [delta, d]; linarith
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun _ => Real.exp_nonneg _
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hpoint : ∀ H : ℝ, 0 ≤ H →
      ‖(criticalMellinNormalizedChebyshevError H : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (H : ℂ)‖ ≤
        K * ((2 * H + 1) * Real.exp (-delta * H)) := by
    intro H hH
    have he := abs_criticalMellinNormalizedChebyshevError_le_log_sqrt hH
    have hF := norm_stripFourier_xiMass_deepShift_le hd0 hda hsigma u H
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |criticalMellinNormalizedChebyshevError H| *
          ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (H : ℂ)‖ ≤
        ((2 * H + 1) * Real.exp (H / 2)) *
          (Real.exp (|u| * d - H * d) * J) := by
            apply mul_le_mul he hF (norm_nonneg _)
            positivity
      _ = K * ((2 * H + 1) * Real.exp (-delta * H)) := by
        have hexpid : Real.exp (H / 2) * Real.exp (|u| * d - H * d) =
            Real.exp (|u| * d) * Real.exp (-(d - 1 / 2) * H) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        dsimp only [K, delta]
        rw [show (2 * H + 1) * Real.exp (H / 2) *
            (Real.exp (|u| * d - H * d) * J) =
            (2 * H + 1) * J *
              (Real.exp (H / 2) * Real.exp (|u| * d - H * d)) by ring,
          hexpid]
        ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun H => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    exact hpoint H hH
  · have hcoef : -delta < 0 := by linarith
    have harg : Tendsto (fun H : ℝ => (-delta) * H) atTop atBot := by
      simpa only [id_eq] using tendsto_id.const_mul_atTop_of_neg hcoef
    have hexp : Tendsto (fun H : ℝ => Real.exp (-delta * H)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    have hlinear := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 delta hdelta
    have hsum : Tendsto
        (fun H : ℝ => 2 * (H ^ (1 : ℝ) * Real.exp (-delta * H)) +
          Real.exp (-delta * H)) atTop (𝓝 0) := by
      simpa using (hlinear.const_mul 2).add hexp
    have hpoly : Tendsto (fun H : ℝ => (2 * H + 1) * Real.exp (-delta * H))
        atTop (𝓝 0) := by
      refine hsum.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
      rw [Real.rpow_one]
      ring
    simpa using hpoly.const_mul K

theorem integrableOn_expNegHalf_mul_xiMassFourier
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    IntegrableOn
      (fun h : ℝ => (Real.exp (-h / 2) : ℂ) *
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (h : ℂ))
      (Ioi 0) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun _ => Real.exp_nonneg _
  have hexp : IntegrableOn (fun h : ℝ => Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0
  have hmajor : IntegrableOn (fun h : ℝ => J * Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) :=
    hexp.const_mul J
  have hcont : Continuous (fun h : ℝ =>
      (Real.exp (-h / 2) : ℂ) *
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (h : ℂ)) := by
    have hwcont : Continuous (fun h : ℝ => (Real.exp (-h / 2) : ℂ)) := by fun_prop
    have hFcont : Continuous (fun h : ℝ =>
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (h : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro h
      exact (hasDerivAt_xiMassRealFourierProfile ha hsigma u h).continuousAt
    exact hwcont.mul hFcont
  apply Integrable.mono' hmajor hcont.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hF := norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-h / 2) *
        ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * Complex.I)) ↑h‖ ≤
      Real.exp (-h / 2) * J :=
        mul_le_mul_of_nonneg_left (by simpa [J] using hF) (Real.exp_nonneg _)
    _ = J * Real.exp ((-1 / 2 : ℝ) * h) := by ring

theorem norm_xiMassCriticalOutgoingDerivative_deepShift_le
    {a sigma d : ℝ} (hd0 : 0 ≤ d) (hda : d < a) (hsigma : 0 < sigma)
    (u h : ℝ) :
    ‖xiMassCriticalOutgoingDerivative a sigma u h‖ ≤
      Real.exp (|u| * d - h * d) *
        ((1 / 2 : ℝ) * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
          ∫ x : ℝ, (|x| + d) * Real.exp (-(sigma * |x|))) := by
  have hF := norm_stripFourier_xiMass_deepShift_le hd0 hda hsigma u h
  have hF' := norm_xiMassFourierDerivative_deepShift_le hd0 hda hsigma u h
  rw [xiMassCriticalOutgoingDerivative]
  calc
    ‖(1 / 2 : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * Complex.I)) ↑h -
        xiMassFourierDerivative a sigma u h‖ ≤
      ‖(1 / 2 : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * Complex.I)) ↑h‖ +
        ‖xiMassFourierDerivative a sigma u h‖ := norm_sub_le _ _
    _ = (1 / 2 : ℝ) *
          ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * Complex.I)) ↑h‖ +
        ‖xiMassFourierDerivative a sigma u h‖ := by norm_num
    _ ≤ (1 / 2 : ℝ) *
          (Real.exp (|u| * d - h * d) *
            (∫ x : ℝ, Real.exp (-(sigma * |x|)))) +
        Real.exp (|u| * d - h * d) *
          (∫ x : ℝ, (|x| + d) * Real.exp (-(sigma * |x|))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hF (by norm_num)) hF'
    _ = _ := by ring

theorem integrableOn_xiMassCriticalOutgoingFlux
    {a sigma : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    IntegrableOn
      (fun h : ℝ => (criticalMellinNormalizedChebyshevError h : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h)
      (Ioi 0) := by
  let d : ℝ := (a + 1 / 2) / 2
  let delta : ℝ := d - 1 / 2
  let J : ℝ := (1 / 2 : ℝ) * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
    ∫ x : ℝ, (|x| + d) * Real.exp (-(sigma * |x|))
  let K : ℝ := Real.exp (|u| * d) * J
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have hdelta : 0 < delta := by dsimp [delta, d]; linarith
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (integral_nonneg fun _ => Real.exp_nonneg _)
    · exact integral_nonneg fun x =>
        mul_nonneg (add_nonneg (abs_nonneg x) hd0) (Real.exp_nonneg _)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hlin0 := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (1 : ℝ)) (p := (1 : ℝ)) (b := delta) (by norm_num) (by norm_num) hdelta
  have hlinear : IntegrableOn (fun h : ℝ => h * Real.exp (-delta * h)) (Ioi 0) := by
    refine hlin0.congr_fun ?_ measurableSet_Ioi
    intro h hh
    simp
  have hexp : IntegrableOn (fun h : ℝ => Real.exp (-delta * h)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (show -delta < 0 by linarith) 0
  have hpoly : IntegrableOn
      (fun h : ℝ => (2 * h + 1) * Real.exp (-delta * h)) (Ioi 0) := by
    rw [show (fun h : ℝ => (2 * h + 1) * Real.exp (-delta * h)) =
        (fun h : ℝ => 2 * (h * Real.exp (-delta * h))) +
          fun h : ℝ => Real.exp (-delta * h) by
      funext h
      simp only [Pi.add_apply]
      ring]
    exact (hlinear.const_mul 2).add hexp
  have hmajor : IntegrableOn
      (fun h : ℝ => K * ((2 * h + 1) * Real.exp (-delta * h))) (Ioi 0) :=
    hpoly.const_mul K
  have hOcont : Continuous (xiMassCriticalOutgoingDerivative a sigma u) := by
    change Continuous (fun h : ℝ =>
      (1 / 2 : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * Complex.I)) (h : ℂ) -
        xiMassFourierDerivative a sigma u h)
    apply Continuous.sub
    · apply Continuous.const_mul
      rw [continuous_iff_continuousAt]
      intro h
      exact (hasDerivAt_xiMassRealFourierProfile (by linarith) hsigma u h).continuousAt
    · exact continuous_xiMassFourierDerivative (by linarith) hsigma u
  have hmeas : AEStronglyMeasurable
      (fun h : ℝ => (criticalMellinNormalizedChebyshevError h : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h) :=
    ((Complex.measurable_ofReal.comp measurable_criticalMellinNormalizedChebyshevError).mul
      hOcont.measurable).aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [Set.mem_Ioi] at hh
  have he := abs_criticalMellinNormalizedChebyshevError_le_log_sqrt hh.le
  have hO := norm_xiMassCriticalOutgoingDerivative_deepShift_le hd0 hda hsigma u h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |criticalMellinNormalizedChebyshevError h| *
        ‖xiMassCriticalOutgoingDerivative a sigma u h‖ ≤
      ((2 * h + 1) * Real.exp (h / 2)) *
        (Real.exp (|u| * d - h * d) * J) := by
          apply mul_le_mul he (by simpa [J] using hO) (norm_nonneg _)
          positivity
    _ = K * ((2 * h + 1) * Real.exp (-delta * h)) := by
      have hexpid : Real.exp (h / 2) * Real.exp (|u| * d - h * d) =
          Real.exp (|u| * d) * Real.exp (-(d - 1 / 2) * h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      dsimp only [K, delta]
      rw [show (2 * h + 1) * Real.exp (h / 2) *
          (Real.exp (|u| * d - h * d) * J) =
          (2 * h + 1) * J *
            (Real.exp (h / 2) * Real.exp (|u| * d - h * d)) by ring,
        hexpid]
      ring

noncomputable def xiMassExpDampedFourier (a sigma u : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), (Real.exp (-h / 2) : ℂ) *
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (h : ℂ)

noncomputable def xiMassCriticalOutgoingFlux (a sigma u : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ),
    (criticalMellinNormalizedChebyshevError h : ℂ) *
      xiMassCriticalOutgoingDerivative a sigma u h

/-- Infinite-ray Volterra-adjoint law for the completed critical-error flux. It isolates the
unique non-explicit term as normalized Chebyshev error paired with the outgoing derivative
`1 / 2 - d / dh` of the mass Fourier profile. -/
theorem xiMassCompletedErrorFlux_eq_criticalOutgoingFlux
    {a sigma : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    xiMassCompletedErrorFlux a sigma u =
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) 0 -
        xiMassExpDampedFourier a sigma u +
        xiMassCriticalOutgoingFlux a sigma u := by
  let F : ℝ → ℂ := fun h =>
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) (h : ℂ)
  let F' : ℝ → ℂ := xiMassFourierDerivative a sigma u
  let D : ℝ → ℂ := xiMassCriticalOutgoingDerivative a sigma u
  let w : ℝ → ℂ := fun h => (Real.exp (-h / 2) : ℂ)
  have ha : 0 < a := lt_trans (by norm_num) hhalf
  have hleft0 := tendsto_xiMassCompletedErrorFluxPartial_atTop hhalf hsigma u
  have hleft : Tendsto
      (fun H : ℝ => ∫ h in (0 : ℝ)..H,
        (criticalMellinCompletedError h : ℂ) * F' h)
      atTop (𝓝 (xiMassCompletedErrorFlux a sigma u)) := by
    refine hleft0.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    rw [xiMassCompletedErrorFluxPartial, intervalIntegral.integral_of_le hH]
  have hdamped0 := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_expNegHalf_mul_xiMassFourier ha hsigma u) tendsto_id
  have hdamped : Tendsto
      (fun H : ℝ => ∫ h in (0 : ℝ)..H, w h * F h)
      atTop (𝓝 (xiMassExpDampedFourier a sigma u)) := by
    simpa only [id_eq, w, F, xiMassExpDampedFourier] using hdamped0
  have hout0 := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_xiMassCriticalOutgoingFlux hhalf hsigma u) tendsto_id
  have hout : Tendsto
      (fun H : ℝ => ∫ h in (0 : ℝ)..H,
        (criticalMellinNormalizedChebyshevError h : ℂ) * D h)
      atTop (𝓝 (xiMassCriticalOutgoingFlux a sigma u)) := by
    simpa only [id_eq, D, xiMassCriticalOutgoingFlux] using hout0
  have hterminalE := tendsto_xiMassCompletedError_terminal_zero hhalf hsigma u
  have hterminale := tendsto_xiMassNormalizedChebyshevError_terminal_zero hhalf hsigma u
  have hterminal : Tendsto
      (fun H : ℝ =>
        ((criticalMellinCompletedError H +
            criticalMellinNormalizedChebyshevError H : ℝ) : ℂ) * F H)
      atTop (𝓝 0) := by
    have hsum := hterminalE.add hterminale
    have hsum' : Tendsto
        (fun H : ℝ =>
          (criticalMellinCompletedError H : ℂ) * F H +
            (criticalMellinNormalizedChebyshevError H : ℂ) * F H)
        atTop (𝓝 (0 + 0)) := by
      simpa only [F] using hsum
    simpa only [zero_add] using hsum'.congr' (Eventually.of_forall fun H => by
      dsimp only [F]
      push_cast
      ring)
  have hrhs : Tendsto
      (fun H : ℝ => F 0 - (∫ h in (0 : ℝ)..H, w h * F h) +
        (∫ h in (0 : ℝ)..H,
          (criticalMellinNormalizedChebyshevError h : ℂ) * D h) +
        ((criticalMellinCompletedError H +
            criticalMellinNormalizedChebyshevError H : ℝ) : ℂ) * F H)
      atTop
      (𝓝 (stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * Complex.I)) 0 -
        xiMassExpDampedFourier a sigma u + xiMassCriticalOutgoingFlux a sigma u)) := by
    have hconst : Tendsto (fun _ : ℝ => F 0) atTop (𝓝 (F 0)) := tendsto_const_nhds
    have hsum := ((hconst.sub hdamped).add hout).add hterminal
    simpa only [F, zero_add, add_zero, Complex.ofReal_zero] using hsum
  have hfinite :
      (fun H : ℝ => ∫ h in (0 : ℝ)..H,
        (criticalMellinCompletedError h : ℂ) * F' h) =ᶠ[atTop]
      (fun H : ℝ =>
        F 0 - (∫ h in (0 : ℝ)..H, w h * F h) +
          (∫ h in (0 : ℝ)..H,
            (criticalMellinNormalizedChebyshevError h : ℂ) * D h) +
          ((criticalMellinCompletedError H +
              criticalMellinNormalizedChebyshevError H : ℝ) : ℂ) * F H) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    simpa only [F, F', D, w, Complex.ofReal_zero] using
      integral_xiMassCompletedError_mul_deriv_eq_outgoing ha hsigma hH u
  have hrightAsLeft := hrhs.congr' hfinite.symm
  exact tendsto_nhds_unique hleft hrightAsLeft

end RHTower
