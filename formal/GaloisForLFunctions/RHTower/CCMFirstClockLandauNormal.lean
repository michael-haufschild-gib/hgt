import GaloisForLFunctions.RHTower.CCMFirstClockLandauCompleteness

/-!
# Normal convergence of the first-clock CCM continuation

The literal first-clock Laplace atoms have cubic denominators.  Two exact integrations by parts
use the endpoint cancellation of `sin (2πu)` to expose a reciprocal-square spectral factor.
Combined with the strict `9/2` source-height gap, this gives a uniform majorant on the universal
slope-eight cone.  This is the infinite-divisor input missing from mere cone nonintersection.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

private theorem cubic_sine_integral_ibp
    {s lam : ℂ} (hlam : lam ≠ 0)
    (hden : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → s - lam * (u : ℂ) ≠ 0) :
    (∫ u : ℝ in (0 : ℝ)..1,
      Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
        (s - lam * (u : ℂ)) ^ 3) =
      1 / (2 * lam ^ 2) *
        ((2 * (Real.pi : ℂ)) *
            (1 / s - 1 / (s - lam)) -
          (2 * (Real.pi : ℂ)) ^ 2 *
            ∫ u : ℝ in (0 : ℝ)..1,
              Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
                (s - lam * (u : ℂ))) := by
  let c : ℂ := 2 * (Real.pi : ℂ)
  let f : ℝ → ℂ := fun u => Complex.sin (c * (u : ℂ))
  let g : ℝ → ℂ := fun u => 1 / (s - lam * (u : ℂ))
  let J : ℝ → ℂ := fun u =>
    f u * (lam / (s - lam * (u : ℂ)) ^ 2) -
      (c * Complex.cos (c * (u : ℂ))) * g u
  let J' : ℝ → ℂ := fun u =>
    2 * lam ^ 2 * (f u / (s - lam * (u : ℂ)) ^ 3) +
      c ^ 2 * (f u / (s - lam * (u : ℂ)))
  have hJderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt J (J' u) u := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by simpa using hu
    have hne := hden u huIcc
    have hcast : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
      (hasDerivAt_id u).ofReal_comp
    have hcline : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c u := by
      simpa using hcast.const_mul c
    have hsin : HasDerivAt
        (fun v : ℝ => Complex.sin (c * (v : ℂ)))
        (Complex.cos (c * (u : ℂ)) * c) u := by
      simpa only [Function.comp_apply] using
        (Complex.hasDerivAt_sin _).comp u hcline
    have hcos : HasDerivAt
        (fun v : ℝ => Complex.cos (c * (v : ℂ)))
        (-Complex.sin (c * (u : ℂ)) * c) u := by
      simpa only [Function.comp_apply] using
        (Complex.hasDerivAt_cos _).comp u hcline
    have hdenDeriv : HasDerivAt
        (fun v : ℝ => s - lam * (v : ℂ)) (-lam) u := by
      convert (hasDerivAt_const u s).sub (hcast.const_mul lam) using 1 <;> ring
    have hdenSqInv : HasDerivAt
        (fun v : ℝ => 1 / (s - lam * (v : ℂ)) ^ 2)
        (2 * lam / (s - lam * (u : ℂ)) ^ 3) u := by
      have hout : HasDerivAt
          (fun z : ℂ => 1 / z ^ 2)
          (-2 / (s - lam * (u : ℂ)) ^ 3)
          (s - lam * (u : ℂ)) := by
        have hp := hasDerivAt_id (s - lam * (u : ℂ)) |>.pow 2
        have hi := hp.inv (pow_ne_zero 2 hne)
        have hi' : HasDerivAt (fun z : ℂ => 1 / z ^ 2)
            (-(2 * (s - lam * (u : ℂ))) /
              ((s - lam * (u : ℂ)) ^ 2) ^ 2)
            (s - lam * (u : ℂ)) := by
          simpa [id_eq, div_eq_mul_inv] using hi
        convert hi' using 1 <;> field_simp [hne] <;> ring
      convert hout.comp u hdenDeriv using 1 <;> field_simp [hne] <;> ring
    have hdenInv : HasDerivAt
        (fun v : ℝ => 1 / (s - lam * (v : ℂ)))
        (lam / (s - lam * (u : ℂ)) ^ 2) u := by
      have hout : HasDerivAt
          (fun z : ℂ => 1 / z)
          (-1 / (s - lam * (u : ℂ)) ^ 2)
          (s - lam * (u : ℂ)) := by
        have hi := (hasDerivAt_id (s - lam * (u : ℂ))).inv hne
        simpa [one_div, id_eq, div_eq_mul_inv] using hi
      convert hout.comp u hdenDeriv using 1 <;> field_simp [hne] <;> ring
    dsimp only [J, J', f, g]
    have hfirst := hsin.mul (hdenSqInv.const_mul lam)
    have hsecond := (hcos.const_mul c).mul hdenInv
    convert hfirst.sub hsecond using 1
    · funext v
      simp only [Pi.sub_apply, Pi.mul_apply, div_eq_mul_inv]
      ring
    · field_simp [hne]
      ring
  have hJ'int : IntervalIntegrable J' volume (0 : ℝ) 1 := by
    have hsinCont : Continuous (fun u : ℝ =>
        Complex.sin (c * (u : ℂ))) := by fun_prop
    have hdenCont : Continuous (fun u : ℝ =>
        s - lam * (u : ℂ)) := by fun_prop
    have hcubic : IntervalIntegrable
        (fun u : ℝ => Complex.sin (c * (u : ℂ)) /
          (s - lam * (u : ℂ)) ^ 3) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      exact hsinCont.continuousOn.div
        (hdenCont.continuousOn.pow 3)
        (fun u hu => pow_ne_zero 3 (hden u (by simpa using hu)))
    have hlinear : IntervalIntegrable
        (fun u : ℝ => Complex.sin (c * (u : ℂ)) /
          (s - lam * (u : ℂ))) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      exact hsinCont.continuousOn.div hdenCont.continuousOn
        (fun u hu => hden u (by simpa using hu))
    exact (hcubic.const_mul _).add (hlinear.const_mul _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hJderiv hJ'int
  have hs0 : s ≠ 0 := by
    simpa using hden 0 (by simp)
  have hs1 : s - lam ≠ 0 := by simpa using hden 1 (by simp)
  have hcoss : Complex.cos c = 1 := by
    dsimp only [c]
    simpa only [Int.cast_one, one_mul] using Complex.cos_int_mul_two_pi 1
  have hsins : Complex.sin c = 0 := by
    dsimp only [c]
    exact Complex.sin_two_pi
  have hJ0 : J 0 = -(c / s) := by
    dsimp only [J, f, g]
    simp [div_eq_mul_inv]
  have hJ1 : J 1 = -(c / (s - lam)) := by
    dsimp only [J, f, g]
    simp only [Complex.ofReal_one, mul_one, hsins, zero_mul,
      hcoss, zero_sub]
    simp [div_eq_mul_inv]
  rw [hJ0, hJ1] at hFTC
  dsimp only [J', f, c] at hFTC ⊢
  have hsinCont : Continuous (fun u : ℝ =>
      Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))) := by fun_prop
  have hdenCont : Continuous (fun u : ℝ =>
      s - lam * (u : ℂ)) := by fun_prop
  have hcubic : IntervalIntegrable
      (fun u : ℝ => Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
        (s - lam * (u : ℂ)) ^ 3) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hsinCont.continuousOn.div
      (hdenCont.continuousOn.pow 3)
      (fun u hu => pow_ne_zero 3 (hden u (by simpa using hu)))
  have hlinear : IntervalIntegrable
      (fun u : ℝ => Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
        (s - lam * (u : ℂ))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hsinCont.continuousOn.div hdenCont.continuousOn
      (fun u hu => hden u (by simpa using hu))
  rw [intervalIntegral.integral_add
      (hcubic.const_mul _) (hlinear.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  have hFTC' :
      2 * lam ^ 2 *
          (∫ u : ℝ in (0 : ℝ)..1,
            Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
              (s - lam * (u : ℂ)) ^ 3) +
        (2 * (Real.pi : ℂ)) ^ 2 *
          (∫ u : ℝ in (0 : ℝ)..1,
            Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
              (s - lam * (u : ℂ))) =
        (2 * (Real.pi : ℂ)) * (1 / s - 1 / (s - lam)) := by
    convert hFTC using 1 <;> ring
  have hcoef : 2 * lam ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hlam)
  rw [show 1 / (2 * lam ^ 2) *
      ((2 * (Real.pi : ℂ)) * (1 / s - 1 / (s - lam)) -
        (2 * (Real.pi : ℂ)) ^ 2 *
          ∫ u : ℝ in (0 : ℝ)..1,
            Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
              (s - lam * (u : ℂ))) =
      ((2 * (Real.pi : ℂ)) * (1 / s - 1 / (s - lam)) -
        (2 * (Real.pi : ℂ)) ^ 2 *
          ∫ u : ℝ in (0 : ℝ)..1,
            Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
              (s - lam * (u : ℂ))) / (2 * lam ^ 2) by
    field_simp [hcoef]]
  apply (eq_div_iff hcoef).2
  linear_combination hFTC'

/-- Cubic continuation atom obtained by Laplace transforming one dilated first-clock kernel. -/
def ccmFirstClockLaplaceContinuationAtom (s z : ℂ) : ℂ :=
  -(1 / (2 * (Real.pi : ℂ))) *
    ∫ u : ℝ in (0 : ℝ)..1,
      Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
        (1 / (s - I * z * (u : ℂ)) ^ 3 +
          1 / (s + I * z * (u : ℂ)) ^ 3)

/-- **First-clock endpoint-cancellation law.**  Two integrations by parts factor one full
reciprocal square of the spectral point out of every cubic continuation atom. -/
theorem ccmFirstClockLaplaceContinuationAtom_ibp
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) :
    ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q) =
      1 / (4 * (Real.pi : ℂ) * xiSpectralPoint q ^ 2) *
        ((2 * (Real.pi : ℂ)) *
            (2 / s -
              1 / (s - I * xiSpectralPoint q) -
              1 / (s + I * xiSpectralPoint q)) -
          (2 * (Real.pi : ℂ)) ^ 2 *
            ∫ u : ℝ in (0 : ℝ)..1,
              Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
                (1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
                  1 / (s + I * xiSpectralPoint q * (u : ℂ)))) := by
  let z : ℂ := xiSpectralPoint q
  have hz : z ≠ 0 := xiSpectralPoint_ne_zero q
  have hminusDen : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 →
      s - (I * z) * (u : ℂ) ≠ 0 := by
    intro u hu
    exact ccmFirstClockLaplaceCone_sub_ne_zero hsre hscone q hu.1
  have hplusDen : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 →
      s - (-I * z) * (u : ℂ) ≠ 0 := by
    intro u hu
    have h := ccmFirstClockLaplaceCone_add_ne_zero hsre hscone q hu.1
    convert h using 1 <;> ring
  have hminus := cubic_sine_integral_ibp
    (s := s) (lam := I * z) (mul_ne_zero I_ne_zero hz) hminusDen
  have hplus := cubic_sine_integral_ibp
    (s := s) (lam := -I * z)
    (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz) hplusDen
  have hminusInt : IntervalIntegrable
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
          (s - I * z * (u : ℂ)) ^ 3) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)))).continuousOn.div
      (by fun_prop : Continuous
        (fun u : ℝ => (s - I * z * (u : ℂ)) ^ 3)).continuousOn
      (fun u hu => pow_ne_zero 3 (hminusDen u (by simpa using hu)))
  have hplusInt : IntervalIntegrable
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
          (s + I * z * (u : ℂ)) ^ 3) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)))).continuousOn.div
      (by fun_prop : Continuous
        (fun u : ℝ => (s + I * z * (u : ℂ)) ^ 3)).continuousOn
      (fun u hu => pow_ne_zero 3
        (ccmFirstClockLaplaceCone_add_ne_zero hsre hscone q
          (show 0 ≤ u by simpa using hu.1)))
  have hsplit :
      (∫ u : ℝ in (0 : ℝ)..1,
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
          (1 / (s - I * z * (u : ℂ)) ^ 3 +
            1 / (s + I * z * (u : ℂ)) ^ 3)) =
        (∫ u : ℝ in (0 : ℝ)..1,
          Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
            (s - I * z * (u : ℂ)) ^ 3) +
        ∫ u : ℝ in (0 : ℝ)..1,
          Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
            (s + I * z * (u : ℂ)) ^ 3 := by
    rw [← intervalIntegral.integral_add hminusInt hplusInt]
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  dsimp only [ccmFirstClockLaplaceContinuationAtom]
  rw [show xiSpectralPoint q = z by rfl, hsplit]
  rw [hminus]
  have hplus' :
      (∫ u : ℝ in (0 : ℝ)..1,
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
          (s + I * z * (u : ℂ)) ^ 3) =
      1 / (2 * (-I * z) ^ 2) *
        ((2 * (Real.pi : ℂ)) *
            (1 / s - 1 / (s + I * z)) -
          (2 * (Real.pi : ℂ)) ^ 2 *
            ∫ u : ℝ in (0 : ℝ)..1,
              Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
                (s + I * z * (u : ℂ))) := by
    simpa only [neg_mul, sub_neg_eq_add] using hplus
  rw [hplus']
  have hlinearMinus : IntervalIntegrable
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
          (s - I * z * (u : ℂ))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)))).continuousOn.div
      (by fun_prop : Continuous
        (fun u : ℝ => s - I * z * (u : ℂ))).continuousOn
      (fun u hu => hminusDen u (by simpa using hu))
  have hlinearPlus : IntervalIntegrable
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
          (s + I * z * (u : ℂ))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)))).continuousOn.div
      (by fun_prop : Continuous
        (fun u : ℝ => s + I * z * (u : ℂ))).continuousOn
      (fun u hu =>
        ccmFirstClockLaplaceCone_add_ne_zero hsre hscone q
          (show 0 ≤ u by
            have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by simpa using hu
            exact hu'.1))
  have hlinearSplit :
      (∫ u : ℝ in (0 : ℝ)..1,
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
          (1 / (s - I * z * (u : ℂ)) +
            1 / (s + I * z * (u : ℂ)))) =
        (∫ u : ℝ in (0 : ℝ)..1,
          Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
            (s - I * z * (u : ℂ))) +
        ∫ u : ℝ in (0 : ℝ)..1,
          Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) /
            (s + I * z * (u : ℂ)) := by
    rw [← intervalIntegral.integral_add hlinearMinus hlinearPlus]
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  rw [hlinearSplit]
  have hfacMinus :
      1 / (2 * (I * z) ^ 2) = -(1 / (2 * z ^ 2)) := by
    field_simp [hz]
    rw [I_sq]
    ring
  have hfacPlus :
      1 / (2 * (-I * z) ^ 2) = -(1 / (2 * z ^ 2)) := by
    field_simp [hz]
    rw [I_sq]
    ring
  rw [hfacMinus, hfacPlus]
  field_simp [hz, Real.pi_ne_zero]
  ring

private theorem norm_inv_ccmFirstClockLaplaceCone_sub_le
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    ‖1 / (s - I * xiSpectralPoint q * (u : ℂ))‖ ≤ 10 / s.re := by
  have hsep := ccmFirstClockLaplaceCone_norm_sub hsre hscone q hu
  have hdenpos : 0 < ‖s - I * xiSpectralPoint q * (u : ℂ)‖ := by
    have : 0 < s.re / 10 := by positivity
    exact this.trans_le hsep
  rw [norm_div, norm_one]
  exact (div_le_div_iff₀ hdenpos hsre).2 (by nlinarith)

private theorem norm_inv_ccmFirstClockLaplaceCone_add_le
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    ‖1 / (s + I * xiSpectralPoint q * (u : ℂ))‖ ≤ 10 / s.re := by
  have hsep := ccmFirstClockLaplaceCone_norm_add hsre hscone q hu
  have hdenpos : 0 < ‖s + I * xiSpectralPoint q * (u : ℂ)‖ := by
    have : 0 < s.re / 10 := by positivity
    exact this.trans_le hsep
  rw [norm_div, norm_one]
  exact (div_le_div_iff₀ hdenpos hsre).2 (by nlinarith)

/-- **Universal reciprocal-square majorant.**  On the complete slope-eight continuation cone,
every first-clock atom is bounded by an explicit `s`-dependent constant times `‖z_q‖⁻²`.
Consequently the infinite Xi divisor has a normally convergent first-clock continuation on every
compact subset of this cone. -/
theorem norm_ccmFirstClockLaplaceContinuationAtom_le
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) :
    ‖ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q)‖ ≤
      (‖1 / (4 * (Real.pi : ℂ))‖ *
          (‖(2 * (Real.pi : ℂ))‖ * (22 / s.re) +
            ‖(2 * (Real.pi : ℂ)) ^ 2‖ * (20 / s.re))) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  rw [ccmFirstClockLaplaceContinuationAtom_ibp hsre hscone q]
  have hsinNorm (u : ℝ) :
      ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) * (u : ℂ) =
        ((2 * Real.pi * u : ℝ) : ℂ) by
      push_cast
      ring]
    rw [← Complex.ofReal_sin, norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hsNorm : ‖1 / s‖ ≤ 1 / s.re := by
    have hsNormPos : 0 < ‖s‖ :=
      hsre.trans_le ((le_abs_self s.re).trans
        (Complex.abs_re_le_norm s))
    rw [norm_div, norm_one]
    exact (div_le_div_iff₀ hsNormPos hsre).2
      (by simpa using
        ((le_abs_self s.re).trans (Complex.abs_re_le_norm s)))
  have hboundary :
      ‖2 / s -
          1 / (s - I * xiSpectralPoint q) -
          1 / (s + I * xiSpectralPoint q)‖ ≤ 22 / s.re := by
    have hsub := norm_inv_ccmFirstClockLaplaceCone_sub_le
      hsre hscone q (u := 1) (by norm_num)
    have hadd := norm_inv_ccmFirstClockLaplaceCone_add_le
      hsre hscone q (u := 1) (by norm_num)
    have htwo : ‖(2 : ℂ) / s‖ ≤ 2 / s.re := by
      calc
        ‖(2 : ℂ) / s‖ = 2 * ‖1 / s‖ := by
          rw [norm_div, norm_ofNat, norm_div, norm_one]
          ring
        _ ≤ 2 * (1 / s.re) := by gcongr
        _ = 2 / s.re := by ring
    calc
      ‖2 / s -
          1 / (s - I * xiSpectralPoint q) -
          1 / (s + I * xiSpectralPoint q)‖ ≤
          ‖(2 : ℂ) / s - 1 / (s - I * xiSpectralPoint q)‖ +
            ‖1 / (s + I * xiSpectralPoint q)‖ := norm_sub_le _ _
      _ ≤ (‖(2 : ℂ) / s‖ +
            ‖1 / (s - I * xiSpectralPoint q)‖) +
            ‖1 / (s + I * xiSpectralPoint q)‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right
            (norm_sub_le ((2 : ℂ) / s)
              (1 / (s - I * xiSpectralPoint q)))
            ‖1 / (s + I * xiSpectralPoint q)‖)
      _ ≤ 2 / s.re + 10 / s.re + 10 / s.re := by
        exact add_le_add
          (add_le_add htwo (by simpa using hsub))
          (by simpa using hadd)
      _ = 22 / s.re := by ring
  have hintegrand (u : ℝ) (hu : u ∈ Set.uIoc (0 : ℝ) 1) :
      ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
          (1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
            1 / (s + I * xiSpectralPoint q * (u : ℂ)))‖ ≤
        20 / s.re := by
    have hu0 : 0 ≤ u := by
      have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hu
      exact hu'.1.le
    rw [norm_mul]
    have hsum :
        ‖1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
          1 / (s + I * xiSpectralPoint q * (u : ℂ))‖ ≤
          10 / s.re + 10 / s.re := by
      exact (norm_add_le _ _).trans (add_le_add
        (norm_inv_ccmFirstClockLaplaceCone_sub_le
          hsre hscone q hu0)
        (norm_inv_ccmFirstClockLaplaceCone_add_le
          hsre hscone q hu0))
    calc
      ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ *
          ‖1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
            1 / (s + I * xiSpectralPoint q * (u : ℂ))‖ ≤
          1 * (10 / s.re + 10 / s.re) := by
        gcongr
        exact hsinNorm u
      _ = 20 / s.re := by ring
  have hintegral :
      ‖∫ u : ℝ in (0 : ℝ)..1,
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
          (1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
            1 / (s + I * xiSpectralPoint q * (u : ℂ)))‖ ≤
        20 / s.re := by
    simpa using
      intervalIntegral.norm_integral_le_of_norm_le_const hintegrand
  rw [norm_mul, norm_div, norm_one, norm_mul, norm_mul, norm_pow]
  have hzNorm : 0 < ‖xiSpectralPoint q‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hbracket :
      ‖(2 * (Real.pi : ℂ)) *
            (2 / s -
              1 / (s - I * xiSpectralPoint q) -
              1 / (s + I * xiSpectralPoint q)) -
          (2 * (Real.pi : ℂ)) ^ 2 *
            ∫ u : ℝ in (0 : ℝ)..1,
              Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
                (1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
                  1 / (s + I * xiSpectralPoint q * (u : ℂ)))‖ ≤
        ‖(2 * (Real.pi : ℂ))‖ * (22 / s.re) +
          ‖(2 * (Real.pi : ℂ)) ^ 2‖ * (20 / s.re) := by
    calc
      _ ≤ ‖(2 * (Real.pi : ℂ)) *
            (2 / s - 1 / (s - I * xiSpectralPoint q) -
              1 / (s + I * xiSpectralPoint q))‖ +
            ‖(2 * (Real.pi : ℂ)) ^ 2 *
              ∫ u : ℝ in (0 : ℝ)..1,
                Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
                  (1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
                    1 / (s + I * xiSpectralPoint q * (u : ℂ)))‖ :=
        norm_sub_le _ _
      _ = ‖(2 * (Real.pi : ℂ))‖ * ‖2 / s -
              1 / (s - I * xiSpectralPoint q) -
              1 / (s + I * xiSpectralPoint q)‖ +
            ‖(2 * (Real.pi : ℂ)) ^ 2‖ *
              ‖∫ u : ℝ in (0 : ℝ)..1,
                Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
                  (1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
                    1 / (s + I * xiSpectralPoint q * (u : ℂ)))‖ := by
        simp only [norm_mul]
      _ ≤ _ := by
        gcongr
  have houter :
      1 / (‖(4 : ℂ)‖ * ‖(Real.pi : ℂ)‖ *
          ‖xiSpectralPoint q‖ ^ 2) =
        ‖1 / (4 * (Real.pi : ℂ))‖ *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    rw [norm_div, norm_one, norm_mul, norm_ofNat]
    field_simp [Real.pi_ne_zero, hzNorm.ne']
  rw [houter]
  calc
    ‖1 / (4 * (Real.pi : ℂ))‖ *
          (1 / ‖xiSpectralPoint q‖ ^ 2) *
        ‖(2 * (Real.pi : ℂ)) *
            (2 / s - 1 / (s - I * xiSpectralPoint q) -
              1 / (s + I * xiSpectralPoint q)) -
          (2 * (Real.pi : ℂ)) ^ 2 *
            ∫ u : ℝ in (0 : ℝ)..1,
              Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
                (1 / (s - I * xiSpectralPoint q * (u : ℂ)) +
                  1 / (s + I * xiSpectralPoint q * (u : ℂ)))‖ ≤
        ‖1 / (4 * (Real.pi : ℂ))‖ *
          (1 / ‖xiSpectralPoint q‖ ^ 2) *
          (‖(2 * (Real.pi : ℂ))‖ * (22 / s.re) +
            ‖(2 * (Real.pi : ℂ)) ^ 2‖ * (20 / s.re)) := by
      gcongr
    _ = _ := by ring

end

end RHTower
