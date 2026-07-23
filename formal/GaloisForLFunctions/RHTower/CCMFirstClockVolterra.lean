import GaloisForLFunctions.RHTower.CCMRectangularScrewCurvature
import GaloisForLFunctions.RHTower.CCMRectangularAutocorrelation
import GaloisForLFunctions.RHTower.CCMPublishedSourceSineCoefficient
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaCancellation
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFullFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Universal first-clock Volterra law

The apparent moving spectral denominator in the first physical CCM clock coordinate is exactly
a signed Volterra filter of the reciprocal-square screw kernel.  A second identity synthesizes
the physical sine test from triangular autocorrelation kernels.  These are the two algebraic
bridges needed to reduce the first published clock coordinate to the already formalized sharp
rectangular Guinand--Weil source law.
-/

open Complex intervalIntegral MeasureTheory Set

namespace RHTower

noncomputable section

private theorem xiDivisorSupport_countable_for_firstClock :
    (Set.univ : Set XiDivisorSupport).Countable := by
  have hlocal : LocallyFiniteSupport
      (fun z : ℂ => MeromorphicOn.divisor xi Set.univ z) := by
    intro z
    exact (MeromorphicOn.divisor xi Set.univ).supportLocallyFiniteWithinDomain'
      z (Set.mem_univ z)
  apply hlocal.locallyFinite_support.countable_univ
  intro rho
  exact ⟨(rho : ℂ), rfl⟩

noncomputable local instance : Countable XiDivisorSupport :=
  Set.countable_univ_iff.mp xiDivisorSupport_countable_for_firstClock

noncomputable local instance : Countable XiZeroCopy := inferInstance

/-- Closed integral of a complex sine with nonzero linear rate. -/
theorem integral_complex_sin_linear
    {k : ℂ} (hk : k ≠ 0) (L : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..L, Complex.sin (k * (t : ℂ))) =
      (1 - Complex.cos (k * (L : ℂ))) / k := by
  let F : ℝ → ℂ := fun t => -Complex.cos (k * (t : ℂ)) / k
  have hderiv : ∀ t : ℝ,
      HasDerivAt F (Complex.sin (k * (t : ℂ))) t := by
    intro t
    have a : HasDerivAt (fun y : ℂ => y * k) k (t : ℂ) :=
      hasDerivAt_mul_const _
    have b : HasDerivAt
        (Complex.cos ∘ fun y : ℂ => y * k)
        (-Complex.sin ((t : ℂ) * k) * k) (t : ℂ) :=
      HasDerivAt.comp (𝕜 := ℂ) (t : ℂ)
        (Complex.hasDerivAt_cos ((t : ℂ) * k)) a
    have c := (b.comp_ofReal.div_const k).fun_neg
    have hfun :
        (fun i : ℝ => -((Complex.cos ∘ fun y : ℂ => y * k) (i : ℂ) / k)) =
          F := by
      funext i
      simp only [Function.comp_apply, F]
      rw [mul_comm (i : ℂ) k]
      ring
    rw [hfun] at c
    convert c using 1
    field_simp [hk]
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.sin (k * (t : ℂ))) volume 0 L := by
    exact (by fun_prop : Continuous
      (fun t : ℝ => Complex.sin (k * (t : ℂ)))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint]
  dsimp only [F]
  simp only [Complex.ofReal_zero, mul_zero, Complex.cos_zero]
  field_simp [hk]
  ring

/-- Complex product-to-sum identity in the orientation used by the clock kernel. -/
theorem complex_sin_mul_cos_product_to_sum (x y : ℂ) :
    Complex.sin x * Complex.cos y =
      (Complex.sin (x + y) + Complex.sin (x - y)) / 2 := by
  rw [Complex.sin_add, Complex.sin_sub]
  ring

/-- Exact sine--cosine integral when the sine rate completes one full physical period. -/
theorem integral_complex_sin_mul_cos_of_period
    {w z : ℂ} {L : ℝ}
    (hwL : w * (L : ℂ) = 2 * Real.pi)
    (hplus : w + z ≠ 0) (hminus : w - z ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..L,
      Complex.sin (w * (t : ℂ)) * Complex.cos (z * (t : ℂ))) =
        w * (1 - Complex.cos ((L : ℂ) * z)) / (w ^ 2 - z ^ 2) := by
  have hpoint (t : ℝ) :
      Complex.sin (w * (t : ℂ)) * Complex.cos (z * (t : ℂ)) =
        (Complex.sin ((w + z) * (t : ℂ)) +
          Complex.sin ((w - z) * (t : ℂ))) / 2 := by
    rw [complex_sin_mul_cos_product_to_sum]
    congr 2 <;> ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  rw [intervalIntegral.integral_div]
  have hIntPlus : IntervalIntegrable
      (fun t : ℝ => Complex.sin ((w + z) * (t : ℂ))) volume 0 L :=
    (by fun_prop : Continuous
      (fun t : ℝ => Complex.sin ((w + z) * (t : ℂ)))).intervalIntegrable 0 L
  have hIntMinus : IntervalIntegrable
      (fun t : ℝ => Complex.sin ((w - z) * (t : ℂ))) volume 0 L :=
    (by fun_prop : Continuous
      (fun t : ℝ => Complex.sin ((w - z) * (t : ℂ)))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_add hIntPlus hIntMinus,
    integral_complex_sin_linear hplus,
    integral_complex_sin_linear hminus]
  have hcosPlus :
      Complex.cos ((w + z) * (L : ℂ)) =
        Complex.cos ((L : ℂ) * z) := by
    rw [show (w + z) * (L : ℂ) =
        w * (L : ℂ) + (L : ℂ) * z by ring, hwL, Complex.cos_add]
    have hcos : Complex.cos (2 * (Real.pi : ℂ)) = 1 := by
      simpa only [Int.cast_one, one_mul] using Complex.cos_int_mul_two_pi 1
    have hsin : Complex.sin (2 * (Real.pi : ℂ)) = 0 := by
      simpa only [Nat.cast_ofNat] using Complex.sin_nat_mul_pi 2
    rw [hcos, hsin]
    ring
  have hcosMinus :
      Complex.cos ((w - z) * (L : ℂ)) =
        Complex.cos ((L : ℂ) * z) := by
    rw [show (w - z) * (L : ℂ) =
        w * (L : ℂ) - (L : ℂ) * z by ring, hwL, Complex.cos_sub]
    have hcos : Complex.cos (2 * (Real.pi : ℂ)) = 1 := by
      simpa only [Int.cast_one, one_mul] using Complex.cos_int_mul_two_pi 1
    have hsin : Complex.sin (2 * (Real.pi : ℂ)) = 0 := by
      simpa only [Nat.cast_ofNat] using Complex.sin_nat_mul_pi 2
    rw [hcos, hsin]
    ring
  rw [hcosPlus, hcosMinus]
  have hquad : w ^ 2 - z ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  field_simp [hplus, hminus, hquad]
  ring

/-- Reciprocal-square screw kernel in the spectral coordinate. -/
def ccmFirstClockScrewKernel (t : ℝ) (z : ℂ) : ℂ :=
  (1 - Complex.cos ((t : ℂ) * z)) / z ^ 2

/-- The generic reciprocal-square screw kernel is exactly the summand already used by the
multiplicity-exact Xi screw divisor. -/
theorem xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel
    (t : ℝ) (q : XiZeroCopy) :
    xiScrewDivisorTerm t q =
      ccmFirstClockScrewKernel t (xiSpectralPoint q) := by
  rw [xiScrewDivisorTerm, ccmFirstClockScrewKernel]
  rw [show (t : ℂ) * (I * xiSpectralPoint q) =
      ((t : ℂ) * xiSpectralPoint q) * I by ring,
    Complex.cosh_mul_I]
  field_simp [xiSpectralPoint_ne_zero q]
  rw [Complex.I_sq]
  ring

/-- The centered Xi screw divisor vanishes at the origin. -/
theorem xiScrewDivisor_zero : xiScrewDivisor 0 = 0 := by
  simp [xiScrewDivisor, xiScrewDivisorTerm]

/-- Unconditional low-height gap in centered spectral coordinates, extracted from the verified
zero-free interval for `XiC`. -/
theorem four_lt_norm_xiSpectralPoint (q : XiZeroCopy) :
    4 < ‖xiSpectralPoint q‖ := by
  by_contra h
  have hre : |(xiSpectralPoint q).re| ≤ 4 :=
    (Complex.abs_re_le_norm _).trans (le_of_not_gt h)
  exact (XiC_ne_zero_of_abs_re_le_four hre)
    (XiC_xiSpectralPoint_eq_zero q)

/-- At every aperture at least `π/2`, the first physical clock cannot collide with a Xi divisor
point. -/
theorem xiSpectralPoint_sq_ne_firstClockSq
    {L : ℝ} (hL : Real.pi / 2 ≤ L) (q : XiZeroCopy) :
    xiSpectralPoint q ^ 2 ≠
      (((2 * Real.pi / L : ℝ) : ℂ)) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  have hr0 : 0 ≤ 2 * Real.pi / L := by positivity
  have hr4 : 2 * Real.pi / L ≤ 4 := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  intro hsq
  have hnorm := congrArg norm hsq
  rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0] at hnorm
  have hgap := four_lt_norm_xiSpectralPoint q
  nlinarith [sq_nonneg ‖xiSpectralPoint q‖,
    sq_nonneg (2 * Real.pi / L)]

/-- A central rectangular two-edge Weil value is exactly twice one Xi screw value.  Thus the
triangular autocorrelation source has no residual finite-difference contamination. -/
theorem xiWeilPolarization_central_rectangular_eq_two_mul_screw (T : ℝ) :
    xiWeilPolarization
        (xiRectangularTwoEdgeTransform (T / 2) (T / 2))
        (xiRectangularTwoEdgeTransform (T / 2) (T / 2)) =
      2 * xiScrewDivisor T := by
  rw [xiWeilPolarization_rectangular_eq_screwCurvature]
  rw [show 2 * (T / 2) = T by ring,
    show T - T = 0 by ring,
    show T - T / 2 = T / 2 by ring]
  rw [xiScrewDivisor_zero]
  ring

/-- At a central aperture the nominal two-edge profile is one contiguous interval, so its
positive-lag autocorrelation is the universal triangular kernel. -/
theorem rectangularTwoEdgeAutocorrelation_central_eq_triangle
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h) :
    rectangularTwoEdgeAutocorrelation (T / 2) (T / 2) h =
      max 0 (T - h) := by
  rw [rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent
    (by positivity : 0 ≤ T / 2) (le_refl (T / 2)) hh]
  rw [show 2 * (T / 2) - T / 2 = T / 2 by ring]
  by_cases hmid : h ≤ T / 2
  · rw [abs_of_nonpos (by linarith : h - T / 2 ≤ 0)]
    rw [max_eq_right (by linarith : 0 ≤ T / 2 - h),
      max_eq_right (by linarith : 0 ≤ T / 2 - -(h - T / 2)),
      max_eq_right (by linarith : 0 ≤ T - h)]
    ring
  · rw [abs_of_nonneg (by linarith : 0 ≤ h - T / 2)]
    rw [max_eq_left (by linarith : T / 2 - h ≤ 0)]
    ring

/-- Rational-entire kernel selected by the first physical CCM clock frequency. -/
def ccmFirstClockRationalKernel (L : ℝ) (z : ℂ) : ℂ :=
  (1 - Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 - (((2 * Real.pi / L : ℝ) : ℂ)) ^ 2)

/-- One aperture-independent compact Fourier kernel.  Every physical first-clock kernel is a
dilation of this single function. -/
def ccmFirstClockFixedCompactKernel (x : ℂ) : ℂ :=
  (1 - Complex.cos x) / (x ^ 2 - (2 * (Real.pi : ℂ)) ^ 2)

/-- Exact dilation law removing the apparent moving denominator. -/
theorem ccmFirstClockRationalKernel_eq_dilation
    {L : ℝ} (hL : L ≠ 0) (z : ℂ) :
    ccmFirstClockRationalKernel L z =
      (L : ℂ) ^ 2 * ccmFirstClockFixedCompactKernel ((L : ℂ) * z) := by
  unfold ccmFirstClockRationalKernel ccmFirstClockFixedCompactKernel
  have hcast : (((2 * Real.pi / L : ℝ) : ℂ)) =
      2 * (Real.pi : ℂ) / (L : ℂ) := by
    push_cast
    ring
  rw [hcast]
  have hrel :
      ((L : ℂ) * z) ^ 2 - (2 * (Real.pi : ℂ)) ^ 2 =
        (L : ℂ) ^ 2 *
          (z ^ 2 - (2 * (Real.pi : ℂ) / (L : ℂ)) ^ 2) := by
    field_simp [hL]
  rw [hrel]
  by_cases hden :
      z ^ 2 - (2 * (Real.pi : ℂ) / (L : ℂ)) ^ 2 = 0
  · simp [hden]
  · field_simp [hL, hden]

/-- Exact one-sided compact cosine representation of the fixed first-clock kernel.  The two
excluded points are removable; the rational identity is all that the Xi divisor needs because
its unconditional height gap avoids them at large aperture. -/
theorem ccmFirstClockFixedCompactKernel_eq_cosineIntegral
    {x : ℂ} (hden : x ^ 2 ≠ (2 * (Real.pi : ℂ)) ^ 2) :
    ccmFirstClockFixedCompactKernel x =
      -(1 / (2 * (Real.pi : ℂ))) *
        ∫ u : ℝ in (0 : ℝ)..1,
          Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
            Complex.cos (x * (u : ℂ)) := by
  let w : ℂ := 2 * (Real.pi : ℂ)
  have hwL : w * (1 : ℂ) = 2 * Real.pi := by
    dsimp only [w]
    ring
  have hplus : w + x ≠ 0 := by
    intro hx
    apply hden
    have : x = -w := by
      apply add_left_cancel (a := w)
      simpa using hx
    rw [this]
    dsimp only [w]
    ring
  have hminus : w - x ≠ 0 := by
    intro hx
    apply hden
    have : x = w := sub_eq_zero.mp hx |>.symm
    rw [this]
  have hdenOpp : w ^ 2 - x ^ 2 ≠ 0 := by
    intro hx
    apply hden
    dsimp only [w] at hx ⊢
    linear_combination -hx
  have hint := integral_complex_sin_mul_cos_of_period
    (w := w) (z := x) (L := 1) hwL hplus hminus
  have hint' :
      (∫ u : ℝ in (0 : ℝ)..1,
        Complex.sin (w * (u : ℂ)) * Complex.cos (x * (u : ℂ))) =
          w * (1 - Complex.cos x) / (w ^ 2 - x ^ 2) := by
    simpa only [Complex.ofReal_one, one_mul] using hint
  rw [hint']
  change (1 - Complex.cos x) / (x ^ 2 - w ^ 2) =
    -(1 / w) * (w * (1 - Complex.cos x) / (w ^ 2 - x ^ 2))
  have hw : w ≠ 0 := by
    dsimp only [w]
    exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hdenSub : x ^ 2 - w ^ 2 ≠ 0 := sub_ne_zero.mpr (by
    simpa only [w] using hden)
  field_simp [hw, hdenSub, hdenOpp]
  ring

/-- **Universal first-clock Volterra law.**  Away from the removable points, the first physical
clock kernel is the screw kernel at the aperture endpoint plus one exact signed Volterra average
of all earlier screw kernels. -/
theorem ccmFirstClockRationalKernel_eq_screw_add_volterra
    {L : ℝ} (hL : 0 < L) {z : ℂ}
    (hz : z ≠ 0)
    (hden : z ^ 2 ≠ (((2 * Real.pi / L : ℝ) : ℂ)) ^ 2) :
    ccmFirstClockRationalKernel L z =
      ccmFirstClockScrewKernel L z +
        ∫ t : ℝ in (0 : ℝ)..L,
          (((2 * Real.pi / L : ℝ) : ℂ) *
            Real.sin ((2 * Real.pi / L) * t)) *
              ccmFirstClockScrewKernel t z := by
  let w : ℂ := ((2 * Real.pi / L : ℝ) : ℂ)
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact_mod_cast div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL.ne'
  have hwL : w * (L : ℂ) = 2 * Real.pi := by
    dsimp only [w]
    push_cast
    field_simp [hL.ne']
  have hplus : w + z ≠ 0 := by
    intro h
    have hzneg : z = -w := by
      apply add_left_cancel (a := w)
      simpa using h
    apply hden
    rw [hzneg]
    ring
  have hminus : w - z ≠ 0 := by
    intro h
    have hzeq : z = w := (sub_eq_zero.mp h).symm
    apply hden
    rw [hzeq]
  have hsin :
      (∫ t : ℝ in (0 : ℝ)..L, Complex.sin (w * (t : ℂ))) = 0 := by
    rw [integral_complex_sin_linear hw0, hwL]
    have hcos : Complex.cos (2 * (Real.pi : ℂ)) = 1 := by
      simpa only [Int.cast_one, one_mul] using Complex.cos_int_mul_two_pi 1
    rw [hcos, sub_self, zero_div]
  have hsincos :=
    integral_complex_sin_mul_cos_of_period hwL hplus hminus
  have hquad : w ^ 2 - z ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hquad' : z ^ 2 - w ^ 2 ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa only [w] using hden)
  have hcast (t : ℝ) :
      ((Real.sin ((2 * Real.pi / L) * t) : ℝ) : ℂ) =
        Complex.sin (w * (t : ℂ)) := by
    rw [Complex.ofReal_sin]
    congr 1
    dsimp only [w]
    push_cast
    ring
  have hint :
      (∫ t : ℝ in (0 : ℝ)..L,
        (w * Real.sin ((2 * Real.pi / L) * t)) *
          ccmFirstClockScrewKernel t z) =
        w ^ 2 / z ^ 2 *
          (1 - Complex.cos ((L : ℂ) * z)) / (z ^ 2 - w ^ 2) := by
    simp_rw [show ∀ t : ℝ,
        (w * Real.sin ((2 * Real.pi / L) * t)) *
            ccmFirstClockScrewKernel t z =
          w / z ^ 2 * (Complex.sin (w * (t : ℂ)) -
            Complex.sin (w * (t : ℂ)) *
              Complex.cos (z * (t : ℂ))) by
        intro t
        rw [hcast]
        unfold ccmFirstClockScrewKernel
        ring]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub
        ((by fun_prop : Continuous
          (fun t : ℝ => Complex.sin (w * (t : ℂ)))).intervalIntegrable 0 L)
        ((by fun_prop : Continuous
          (fun t : ℝ => Complex.sin (w * (t : ℂ)) *
            Complex.cos (z * (t : ℂ)))).intervalIntegrable 0 L)]
    rw [hsin, hsincos]
    field_simp [hz, hplus, hminus, hquad, hquad']
    ring
  change (1 - Complex.cos ((L : ℂ) * z)) / (z ^ 2 - w ^ 2) =
    (1 - Complex.cos ((L : ℂ) * z)) / z ^ 2 + _
  rw [hint]
  field_simp [hz, hden, hquad']
  ring

/-- Pointwise reciprocal-square bound for the Xi first-clock Volterra integrand. -/
theorem norm_ccmFirstClockXiVolterraIntegrand_le
    {L t : ℝ} (hL : 0 < L) (ht0 : 0 ≤ t) (htL : t ≤ L)
    (q : XiZeroCopy) :
    ‖((((2 * Real.pi / L : ℝ) : ℂ) *
        Real.sin ((2 * Real.pi / L) * t)) *
          ccmFirstClockScrewKernel t (xiSpectralPoint q))‖ ≤
      (2 * Real.pi / L) * (Real.exp (L / 2) + 1) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  have hr0 : 0 ≤ 2 * Real.pi / L := by positivity
  have hscrew := norm_xiScrewDivisorTerm_le t q
  rw [xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel] at hscrew
  have hexp : Real.exp (|t| / 2) ≤ Real.exp (L / 2) := by
    rw [abs_of_nonneg ht0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hkernel :
      ‖ccmFirstClockScrewKernel t (xiSpectralPoint q)‖ ≤
        (Real.exp (L / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2 :=
    hscrew.trans (by gcongr)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr0]
  calc
    (2 * Real.pi / L) *
        |Real.sin ((2 * Real.pi / L) * t)| *
          ‖ccmFirstClockScrewKernel t (xiSpectralPoint q)‖ ≤
      (2 * Real.pi / L) * 1 *
        ((Real.exp (L / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2) := by
          gcongr
          exact Real.abs_sin_le_one _
    _ = _ := by ring

/-- Uniform reciprocal-square bound for one Xi Volterra correction term. -/
theorem norm_ccmFirstClockXiVolterraTerm_le
    {L : ℝ} (hL : 0 < L) (q : XiZeroCopy) :
    ‖∫ t : ℝ in (0 : ℝ)..L,
        (((2 * Real.pi / L : ℝ) : ℂ) *
          Real.sin ((2 * Real.pi / L) * t)) *
            ccmFirstClockScrewKernel t (xiSpectralPoint q)‖ ≤
      (2 * Real.pi) * (Real.exp (L / 2) + 1) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  let C : ℝ :=
    (2 * Real.pi / L) * (Real.exp (L / 2) + 1) /
      ‖xiSpectralPoint q‖ ^ 2
  have hpoint : ∀ t ∈ uIoc (0 : ℝ) L,
      ‖((((2 * Real.pi / L : ℝ) : ℂ) *
          Real.sin ((2 * Real.pi / L) * t)) *
            ccmFirstClockScrewKernel t (xiSpectralPoint q))‖ ≤ C := by
    intro t ht
    rw [uIoc_of_le hL.le] at ht
    simpa only [C] using
      norm_ccmFirstClockXiVolterraIntegrand_le hL (le_of_lt ht.1) ht.2 q
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ =>
      (((2 * Real.pi / L : ℝ) : ℂ) *
        Real.sin ((2 * Real.pi / L) * t)) *
          ccmFirstClockScrewKernel t (xiSpectralPoint q))
    (a := (0 : ℝ)) (b := L) (C := C) hpoint
  calc
    ‖∫ t : ℝ in (0 : ℝ)..L,
        (((2 * Real.pi / L : ℝ) : ℂ) *
          Real.sin ((2 * Real.pi / L) * t)) *
            ccmFirstClockScrewKernel t (xiSpectralPoint q)‖ ≤
      C * L := by
        simpa only [sub_zero, abs_of_pos hL] using hraw
    _ = (2 * Real.pi) * (Real.exp (L / 2) + 1) /
        ‖xiSpectralPoint q‖ ^ 2 := by
      dsimp only [C]
      field_simp [hL.ne']

/-- The integrated norm of one Xi Volterra correction has the same reciprocal-square majorant.
This is the Tonelli certificate for exchanging the divisor sum and aperture integral. -/
theorem integral_norm_ccmFirstClockXiVolterraIntegrand_le
    {L : ℝ} (hL : 0 < L) (q : XiZeroCopy) :
    (∫ t : ℝ in (0 : ℝ)..L,
      ‖((((2 * Real.pi / L : ℝ) : ℂ) *
        Real.sin ((2 * Real.pi / L) * t)) *
          ccmFirstClockScrewKernel t (xiSpectralPoint q))‖) ≤
      (2 * Real.pi) * (Real.exp (L / 2) + 1) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  let C : ℝ :=
    (2 * Real.pi / L) * (Real.exp (L / 2) + 1) /
      ‖xiSpectralPoint q‖ ^ 2
  have hint : IntervalIntegrable (fun t : ℝ =>
      ‖((((2 * Real.pi / L : ℝ) : ℂ) *
        Real.sin ((2 * Real.pi / L) * t)) *
          ccmFirstClockScrewKernel t (xiSpectralPoint q))‖)
      volume 0 L := by
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ‖((((2 * Real.pi / L : ℝ) : ℂ) *
        Real.sin ((2 * Real.pi / L) * t)) *
          ((1 - Complex.cos ((t : ℂ) * xiSpectralPoint q)) /
            xiSpectralPoint q ^ 2))‖)).intervalIntegrable 0 L
  have hmono :
      (∫ t : ℝ in (0 : ℝ)..L,
        ‖((((2 * Real.pi / L : ℝ) : ℂ) *
          Real.sin ((2 * Real.pi / L) * t)) *
            ccmFirstClockScrewKernel t (xiSpectralPoint q))‖) ≤
        ∫ _t : ℝ in (0 : ℝ)..L, C := by
    apply intervalIntegral.integral_mono_on hL.le hint
      intervalIntegral.intervalIntegrable_const
    intro t ht
    have ht' := mem_Icc.mp ht
    simpa only [C] using
      norm_ccmFirstClockXiVolterraIntegrand_le hL ht'.1 ht'.2 q
  calc
    (∫ t : ℝ in (0 : ℝ)..L,
      ‖((((2 * Real.pi / L : ℝ) : ℂ) *
        Real.sin ((2 * Real.pi / L) * t)) *
          ccmFirstClockScrewKernel t (xiSpectralPoint q))‖) ≤
      C * L := by
        simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
          mul_comm] using hmono
    _ = (2 * Real.pi) * (Real.exp (L / 2) + 1) /
        ‖xiSpectralPoint q‖ ^ 2 := by
      dsimp only [C]
      field_simp [hL.ne']

/-- Uniform reciprocal-square domination of the first physical clock kernel on the Xi divisor. -/
theorem norm_ccmFirstClockRationalKernel_xiSpectralPoint_le
    {L : ℝ} (hL : Real.pi / 2 ≤ L) (q : XiZeroCopy) :
    ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
      (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  rw [ccmFirstClockRationalKernel_eq_screw_add_volterra hLpos
    (xiSpectralPoint_ne_zero q)
    (xiSpectralPoint_sq_ne_firstClockSq hL q)]
  calc
    ‖ccmFirstClockScrewKernel L (xiSpectralPoint q) +
        ∫ t : ℝ in (0 : ℝ)..L,
          (((2 * Real.pi / L : ℝ) : ℂ) *
            Real.sin ((2 * Real.pi / L) * t)) *
              ccmFirstClockScrewKernel t (xiSpectralPoint q)‖ ≤
      ‖ccmFirstClockScrewKernel L (xiSpectralPoint q)‖ +
        ‖∫ t : ℝ in (0 : ℝ)..L,
          (((2 * Real.pi / L : ℝ) : ℂ) *
            Real.sin ((2 * Real.pi / L) * t)) *
              ccmFirstClockScrewKernel t (xiSpectralPoint q)‖ :=
        norm_add_le _ _
    _ ≤ (Real.exp (L / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2 +
        (2 * Real.pi) * (Real.exp (L / 2) + 1) /
          ‖xiSpectralPoint q‖ ^ 2 := by
      gcongr
      · rw [← xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel]
        simpa only [abs_of_pos hLpos] using norm_xiScrewDivisorTerm_le L q
      · exact norm_ccmFirstClockXiVolterraTerm_le hLpos q
    _ = _ := by ring

/-- Multiplicity-exact zero-side first-clock carrier. -/
def ccmFirstClockXiRationalDivisor (L : ℝ) : ℂ :=
  ∑' q : XiZeroCopy,
    ccmFirstClockRationalKernel L (xiSpectralPoint q)

/-- The zero-side first-clock carrier is absolutely summable at every physical aperture
`L ≥ π/2`. -/
theorem summable_ccmFirstClockRationalKernel_xiSpectralPoint
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    Summable (fun q : XiZeroCopy =>
      ccmFirstClockRationalKernel L (xiSpectralPoint q)) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left
      ((1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)))
  intro q
  calc
    ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
        (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1) /
          ‖xiSpectralPoint q‖ ^ 2 :=
      norm_ccmFirstClockRationalKernel_xiSpectralPoint_le hL q
    _ = (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

/-- **Multiplicity-exact Xi first-clock Volterra law.**  Sum--integral exchange is discharged by
the reciprocal-square divisor majorant.  Thus the complete first clock is exactly one signed
Volterra filter of the already formalized Xi screw divisor. -/
theorem ccmFirstClockXiRationalDivisor_eq_screw_add_volterra
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    ccmFirstClockXiRationalDivisor L =
      xiScrewDivisor L +
        ∫ t : ℝ in (0 : ℝ)..L,
          (((2 * Real.pi / L : ℝ) : ℂ) *
            Real.sin ((2 * Real.pi / L) * t)) *
              xiScrewDivisor t := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  let F : XiZeroCopy → ℝ → ℂ := fun q t =>
    (((2 * Real.pi / L : ℝ) : ℂ) *
      Real.sin ((2 * Real.pi / L) * t)) *
        ccmFirstClockScrewKernel t (xiSpectralPoint q)
  have hFint : ∀ q : XiZeroCopy,
      Integrable (F q) (volume.restrict (Ioc (0 : ℝ) L)) := by
    intro q
    have hcont : Continuous (F q) := by
      dsimp only [F]
      unfold ccmFirstClockScrewKernel
      fun_prop
    have hint : IntervalIntegrable (F q) volume 0 L :=
      hcont.intervalIntegrable 0 L
    rw [intervalIntegrable_iff] at hint
    simpa only [uIoc_of_le hLpos.le] using hint
  have hnormInterval : Summable (fun q : XiZeroCopy =>
      ∫ t : ℝ in (0 : ℝ)..L, ‖F q t‖) := by
    apply Summable.of_norm_bounded
      (xiSpectralPoint_inv_sq_summable.mul_left
        ((2 * Real.pi) * (Real.exp (L / 2) + 1)))
    intro q
    have hnonneg : 0 ≤ ∫ t : ℝ in (0 : ℝ)..L, ‖F q t‖ :=
      intervalIntegral.integral_nonneg hLpos.le (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      (∫ t : ℝ in (0 : ℝ)..L, ‖F q t‖) ≤
          (2 * Real.pi) * (Real.exp (L / 2) + 1) /
            ‖xiSpectralPoint q‖ ^ 2 := by
        simpa only [F] using
          integral_norm_ccmFirstClockXiVolterraIntegrand_le hLpos q
      _ = (2 * Real.pi) * (Real.exp (L / 2) + 1) *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
  have hnormRestrict : Summable (fun q : XiZeroCopy =>
      ∫ t in Ioc (0 : ℝ) L, ‖F q t‖) := by
    apply hnormInterval.congr
    intro q
    exact intervalIntegral.integral_of_le hLpos.le
  have hswap :
      (∫ t : ℝ in (0 : ℝ)..L, ∑' q : XiZeroCopy, F q t) =
        ∑' q : XiZeroCopy, ∫ t : ℝ in (0 : ℝ)..L, F q t := by
    rw [intervalIntegral.integral_of_le hLpos.le]
    calc
      (∫ t in Ioc (0 : ℝ) L, ∑' q : XiZeroCopy, F q t) =
          ∑' q : XiZeroCopy, ∫ t in Ioc (0 : ℝ) L, F q t :=
        (MeasureTheory.integral_tsum_of_summable_integral_norm
          hFint hnormRestrict).symm
      _ = ∑' q : XiZeroCopy,
          ∫ t : ℝ in (0 : ℝ)..L, F q t := by
        apply tsum_congr
        intro q
        exact (intervalIntegral.integral_of_le hLpos.le).symm
  have hIntegralSummable : Summable (fun q : XiZeroCopy =>
      ∫ t : ℝ in (0 : ℝ)..L, F q t) := by
    apply Summable.of_norm_bounded hnormInterval
    intro q
    exact intervalIntegral.norm_integral_le_integral_norm hLpos.le
  have hpoint (t : ℝ) :
      (∑' q : XiZeroCopy, F q t) =
        (((2 * Real.pi / L : ℝ) : ℂ) *
          Real.sin ((2 * Real.pi / L) * t)) *
            xiScrewDivisor t := by
    rw [xiScrewDivisor, ← tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp only [F]
    rw [xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel]
  rw [ccmFirstClockXiRationalDivisor]
  calc
    (∑' q : XiZeroCopy,
        ccmFirstClockRationalKernel L (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy,
        (xiScrewDivisorTerm L q +
          ∫ t : ℝ in (0 : ℝ)..L, F q t) := by
        apply tsum_congr
        intro q
        rw [ccmFirstClockRationalKernel_eq_screw_add_volterra hLpos
          (xiSpectralPoint_ne_zero q)
          (xiSpectralPoint_sq_ne_firstClockSq hL q),
          ← xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel]
    _ = (∑' q : XiZeroCopy, xiScrewDivisorTerm L q) +
        ∑' q : XiZeroCopy, ∫ t : ℝ in (0 : ℝ)..L, F q t := by
          rw [Summable.tsum_add (xiScrewDivisorTerm_summable L)
            hIntegralSummable]
    _ = xiScrewDivisor L +
        ∫ t : ℝ in (0 : ℝ)..L,
          (((2 * Real.pi / L : ℝ) : ℂ) *
            Real.sin ((2 * Real.pi / L) * t)) *
              xiScrewDivisor t := by
      rw [← hswap]
      simp_rw [hpoint]
      rfl

/-- Under RH every first-clock zero-side summand is nonnegative. -/
theorem ccmFirstClockRationalKernel_xiSpectralPoint_re_nonneg_of_rh
    (hRH : RiemannHypothesis)
    {L : ℝ} (hL : Real.pi / 2 ≤ L) (q : XiZeroCopy) :
    0 ≤ (ccmFirstClockRationalKernel L (xiSpectralPoint q)).re := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  have hr0 : 0 ≤ 2 * Real.pi / L := by positivity
  have hr4 : 2 * Real.pi / L ≤ 4 := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have ht4 : 4 < |t| := by
    have hgap := four_lt_norm_xiSpectralPoint q
    rw [ht, norm_real, Real.norm_eq_abs] at hgap
    exact hgap
  have hdenpos : 0 < t ^ 2 - (2 * Real.pi / L) ^ 2 := by
    nlinarith [sq_abs t, sq_nonneg (2 * Real.pi / L)]
  have hkernel :
      ccmFirstClockRationalKernel L (xiSpectralPoint q) =
        (((1 - Real.cos (L * t)) /
          (t ^ 2 - (2 * Real.pi / L) ^ 2) : ℝ) : ℂ) := by
    rw [ht]
    unfold ccmFirstClockRationalKernel
    push_cast
    rfl
  rw [hkernel]
  simp only [Complex.ofReal_re]
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) hdenpos.le

/-- **RH-side first-clock law.**  On RH the complete multiplicity-exact first-clock divisor is
nonnegative at every aperture `L ≥ π/2`. -/
theorem ccmFirstClockXiRationalDivisor_re_nonneg_of_rh
    (hRH : RiemannHypothesis)
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    0 ≤ (ccmFirstClockXiRationalDivisor L).re := by
  rw [ccmFirstClockXiRationalDivisor,
    Complex.re_tsum
      (summable_ccmFirstClockRationalKernel_xiSpectralPoint hL)]
  exact tsum_nonneg fun q =>
    ccmFirstClockRationalKernel_xiSpectralPoint_re_nonneg_of_rh hRH hL q

/-- **Physical sine/triangle synthesis.**  A one-period sine test is exactly one endpoint
triangle plus a signed Volterra superposition of shorter triangles.  This is the source-side
counterpart of `ccmFirstClockRationalKernel_eq_screw_add_volterra`. -/
theorem ccmPhysicalSine_eq_triangleVolterra
    {L xi h : ℝ} (hxi : xi ≠ 0)
    (hperiod : xi * L = 2 * Real.pi) :
    Real.sin (xi * h) =
      -xi * (L - h) -
        xi ^ 2 * ∫ t : ℝ in h..L,
          Real.sin (xi * t) * (t - h) := by
  let F : ℝ → ℝ := fun t =>
    -(t - h) * Real.cos (xi * t) / xi +
      Real.sin (xi * t) / xi ^ 2
  have hderiv : ∀ t : ℝ,
      HasDerivAt F (Real.sin (xi * t) * (t - h)) t := by
    intro t
    have hlin : HasDerivAt (fun x : ℝ => xi * x) xi t :=
      by simpa using (hasDerivAt_id t).const_mul xi
    have hsub : HasDerivAt (fun x : ℝ => x - h) 1 t :=
      (hasDerivAt_id t).sub_const h
    have hcos := hlin.cos
    have hsin := hlin.sin
    have hfirst := (hsub.mul hcos).neg.div_const xi
    have hsecond := hsin.div_const (xi ^ 2)
    have hsum := hfirst.add hsecond
    convert hsum using 1
    · funext x
      simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, F]
      ring
    · field_simp [hxi]
      ring
  have hint : IntervalIntegrable
      (fun t : ℝ => Real.sin (xi * t) * (t - h)) volume h L :=
    (by fun_prop : Continuous
      (fun t : ℝ => Real.sin (xi * t) * (t - h))).intervalIntegrable h L
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint
  have hcosPeriod : Real.cos (xi * L) = 1 := by
    rw [hperiod, show 2 * Real.pi = (1 : ℤ) * (2 * Real.pi) by ring,
      Real.cos_int_mul_two_pi]
  have hsinPeriod : Real.sin (xi * L) = 0 := by
    rw [hperiod]
    simpa only [Nat.cast_ofNat] using Real.sin_nat_mul_pi 2
  dsimp only [F] at heval
  rw [hcosPeriod, hsinPeriod] at heval
  simp only [sub_self, zero_div, add_zero, neg_zero, zero_mul] at heval
  rw [heval]
  field_simp [hxi]
  ring

/-- The physical sine test is exactly a signed Volterra synthesis of central rectangular
autocorrelations.  This is the literal source kernel consumed by the sharp rectangular
Guinand--Weil formula. -/
theorem ccmPhysicalSine_eq_centralRectangularAutocorrelationVolterra
    {L xi h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hhL : h ≤ L)
    (hxi : xi ≠ 0) (hperiod : xi * L = 2 * Real.pi) :
    Real.sin (xi * h) =
      -xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h -
        xi ^ 2 * ∫ t : ℝ in h..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h := by
  rw [ccmPhysicalSine_eq_triangleVolterra hxi hperiod,
    rectangularTwoEdgeAutocorrelation_central_eq_triangle hL hh,
    max_eq_right (by linarith : 0 ≤ L - h)]
  have hint :
      (∫ t : ℝ in h..L, Real.sin (xi * t) * (t - h)) =
        ∫ t : ℝ in h..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hhL] at ht
    have hht : h ≤ t := (mem_Icc.mp ht).1
    change Real.sin (xi * t) * (t - h) =
      Real.sin (xi * t) *
        rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h
    rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle
      (le_trans hh hht) hh,
      max_eq_right (sub_nonneg.mpr hht)]
  rw [hint]

/-- Central autocorrelation against a sine weight is interval-integrable in the aperture
parameter. -/
theorem intervalIntegrable_sin_mul_centralRectangularAutocorrelation
    {L xi h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) :
    IntervalIntegrable
      (fun t : ℝ => Real.sin (xi * t) *
        rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h)
      volume 0 L := by
  refine IntervalIntegrable.congr ?_
    ((by fun_prop : Continuous (fun t : ℝ =>
      Real.sin (xi * t) * max 0 (t - h))).intervalIntegrable 0 L)
  intro t ht
  rw [uIoc_of_le hL] at ht
  have ht0 : 0 ≤ t := le_of_lt ht.1
  change Real.sin (xi * t) * max 0 (t - h) =
    Real.sin (xi * t) *
      rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h
  rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle ht0 hh]

/-- Zero-extended form of the physical sine/autocorrelation synthesis.  Shorter central
triangles vanish automatically below lag `h`, so the Volterra integral may start at zero. -/
theorem ccmPhysicalSine_eq_centralRectangularAutocorrelationVolterra_zeroStart
    {L xi h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hhL : h ≤ L)
    (hxi : xi ≠ 0) (hperiod : xi * L = 2 * Real.pi) :
    Real.sin (xi * h) =
      -xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h -
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h := by
  have hzero :
      (∫ t : ℝ in (0 : ℝ)..h,
        Real.sin (xi * t) * max 0 (t - h)) = 0 := by
    calc
      (∫ t : ℝ in (0 : ℝ)..h,
        Real.sin (xi * t) * max 0 (t - h)) =
          ∫ _t : ℝ in (0 : ℝ)..h, 0 := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le hh] at ht
            have hth : t ≤ h := (mem_Icc.mp ht).2
            change Real.sin (xi * t) * max 0 (t - h) = 0
            rw [max_eq_left (sub_nonpos.mpr hth), mul_zero]
      _ = 0 := by simp
  have htail :
      (∫ t : ℝ in h..L,
        Real.sin (xi * t) * max 0 (t - h)) =
      ∫ t : ℝ in h..L, Real.sin (xi * t) * (t - h) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hhL] at ht
    have hht : h ≤ t := (mem_Icc.mp ht).1
    change Real.sin (xi * t) * max 0 (t - h) =
      Real.sin (xi * t) * (t - h)
    rw [max_eq_right (sub_nonneg.mpr hht)]
  have hsplit :
      (∫ t : ℝ in (0 : ℝ)..h,
        Real.sin (xi * t) * max 0 (t - h)) +
        (∫ t : ℝ in h..L,
          Real.sin (xi * t) * max 0 (t - h)) =
        ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * max 0 (t - h) :=
    intervalIntegral.integral_add_adjacent_intervals
      ((by fun_prop : Continuous (fun t : ℝ =>
        Real.sin (xi * t) * max 0 (t - h))).intervalIntegrable 0 h)
      ((by fun_prop : Continuous (fun t : ℝ =>
        Real.sin (xi * t) * max 0 (t - h))).intervalIntegrable h L)
  have htriangle :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) =
      ∫ t : ℝ in h..L, Real.sin (xi * t) * (t - h) := by
    calc
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) =
        ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * max 0 (t - h) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le hL] at ht
            have ht0 : 0 ≤ t := (mem_Icc.mp ht).1
            change Real.sin (xi * t) *
                rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h =
              Real.sin (xi * t) * max 0 (t - h)
            rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle ht0 hh]
      _ = (∫ t : ℝ in (0 : ℝ)..h,
          Real.sin (xi * t) * max 0 (t - h)) +
          ∫ t : ℝ in h..L,
            Real.sin (xi * t) * max 0 (t - h) := hsplit.symm
      _ = _ := by rw [hzero, zero_add, htail]
  rw [ccmPhysicalSine_eq_triangleVolterra hxi hperiod, htriangle,
    rectangularTwoEdgeAutocorrelation_central_eq_triangle hL hh,
    max_eq_right (sub_nonneg.mpr hhL)]

/-- Zero-start triangle form of the physical sine synthesis. -/
theorem ccmPhysicalSine_eq_triangleVolterra_zeroStart
    {L xi h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hhL : h ≤ L)
    (hxi : xi ≠ 0) (hperiod : xi * L = 2 * Real.pi) :
    Real.sin (xi * h) =
      -xi * max 0 (L - h) -
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * max 0 (t - h) := by
  have hsynth :=
    ccmPhysicalSine_eq_centralRectangularAutocorrelationVolterra_zeroStart
      hL hh hhL hxi hperiod
  rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle hL hh] at hsynth
  have hint :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) =
        ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * max 0 (t - h) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL] at ht
    have ht0 : 0 ≤ t := (mem_Icc.mp ht).1
    change Real.sin (xi * t) *
        rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h =
      Real.sin (xi * t) * max 0 (t - h)
    rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle ht0 hh]
  rw [hint] at hsynth
  exact hsynth

/-- Every shorter central prime autocorrelation can be reindexed in the one fixed terminal
atom set.  Atoms not yet reached vanish by triangular support. -/
theorem rectangularPrimeAutocorrelationSum_central_eq_commonTriangle
    {L t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    rectangularPrimeAutocorrelationSum (t / 2) (t / 2) =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k * max 0 (t - Real.log k) := by
  calc
    rectangularPrimeAutocorrelationSum (t / 2) (t / 2) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
          ArithmeticFunction.vonMangoldt k / Real.sqrt k *
            max 0 (t - Real.log k) := by
      rw [rectangularPrimeAutocorrelationSum,
        show 2 * (t / 2) = t by ring]
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hlog0 : 0 ≤ Real.log k :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
      rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle ht0 hlog0]
    _ = _ := by
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_Icc] at hk ⊢
        exact ⟨hk.1, hk.2.trans
          (Nat.floor_mono (Real.exp_le_exp.mpr htL))⟩
      · intro k hk hnot
        simp only [Finset.mem_Icc] at hk
        have hkfloor : ⌊Real.exp t⌋₊ < k := by
          by_contra hkle
          exact hnot (Finset.mem_Icc.mpr ⟨hk.1, by omega⟩)
        have hkexp : Real.exp t < (k : ℝ) :=
          (Nat.floor_lt (Real.exp_pos t).le).mp hkfloor
        have hkpos : (0 : ℝ) < k := (Real.exp_pos t).trans hkexp
        have hlog : t < Real.log k :=
          (Real.lt_log_iff_exp_lt hkpos).mpr hkexp
        rw [max_eq_left (sub_nonpos.mpr hlog.le), mul_zero]

/-- Exact finite-atom transport at one physical period.  The moving central prime
autocorrelations become the literal prime sine term of the published CCM source. -/
theorem ccmFirstClockPrimeAutocorrelation_superposition
    {L xi : ℝ} (hL : 0 < L) (hperiod : xi * L = 2 * Real.pi) :
    xi * rectangularPrimeAutocorrelationSum (L / 2) (L / 2) +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularPrimeAutocorrelationSum (t / 2) (t / 2) =
      -∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        criticalMellinAtomWeight k * Real.sin (xi * Real.log k) := by
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp L⌋₊
  let w : ℕ → ℝ := fun k =>
    ArithmeticFunction.vonMangoldt k / Real.sqrt k
  let J : ℕ → ℝ := fun k =>
    ∫ t : ℝ in (0 : ℝ)..L,
      Real.sin (xi * t) * max 0 (t - Real.log k)
  have hxi : xi ≠ 0 := by
    intro hxi0
    rw [hxi0, zero_mul] at hperiod
    linarith [Real.pi_pos]
  have hterminal :
      rectangularPrimeAutocorrelationSum (L / 2) (L / 2) =
        ∑ k ∈ K, w k * max 0 (L - Real.log k) := by
    simpa only [K, w] using
      rectangularPrimeAutocorrelationSum_central_eq_commonTriangle
        hL.le (le_refl L)
  have hintegral :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularPrimeAutocorrelationSum (t / 2) (t / 2)) =
        ∑ k ∈ K, w k * J k := by
    calc
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularPrimeAutocorrelationSum (t / 2) (t / 2)) =
          ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              ∑ k ∈ K, w k * max 0 (t - Real.log k) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hL.le] at ht
        have htmem := mem_Icc.mp ht
        change Real.sin (xi * t) *
            rectangularPrimeAutocorrelationSum (t / 2) (t / 2) =
          Real.sin (xi * t) *
            ∑ k ∈ K, w k * max 0 (t - Real.log k)
        rw [rectangularPrimeAutocorrelationSum_central_eq_commonTriangle
          htmem.1 htmem.2]
      _ = ∫ t : ℝ in (0 : ℝ)..L,
          ∑ k ∈ K, w k *
            (Real.sin (xi * t) * max 0 (t - Real.log k)) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change Real.sin (xi * t) *
            (∑ k ∈ K, w k * max 0 (t - Real.log k)) =
          ∑ k ∈ K, w k *
            (Real.sin (xi * t) * max 0 (t - Real.log k))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = ∑ k ∈ K, ∫ t : ℝ in (0 : ℝ)..L,
          w k * (Real.sin (xi * t) * max 0 (t - Real.log k)) := by
        apply intervalIntegral.integral_finsetSum
        intro k _hk
        exact (by fun_prop : Continuous (fun t : ℝ =>
          w k * (Real.sin (xi * t) * max 0 (t - Real.log k))))
          |>.intervalIntegrable 0 L
      _ = ∑ k ∈ K, w k * J k := by
        apply Finset.sum_congr rfl
        intro k _hk
        dsimp only [J]
        rw [intervalIntegral.integral_const_mul]
  rw [hterminal, hintegral, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ k ∈ K, w k *
        (xi * max 0 (L - Real.log k) +
          xi ^ 2 * J k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ∑ k ∈ K, w k * (-Real.sin (xi * Real.log k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp (by simpa only [K] using hk)).1
      have hlog0 : 0 ≤ Real.log k :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
      have hkfloor :
          k ≤ ⌊Real.exp L⌋₊ :=
        (Finset.mem_Icc.mp (by simpa only [K] using hk)).2
      have hkexp : (k : ℝ) ≤ Real.exp L :=
        (Nat.le_floor_iff (Real.exp_pos L).le).mp hkfloor
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hlogL : Real.log k ≤ L :=
        (Real.log_le_iff_le_exp hkpos).mpr hkexp
      have hsynth := ccmPhysicalSine_eq_triangleVolterra_zeroStart
        hL.le hlog0 hlogL hxi hperiod
      rw [show xi * max 0 (L - Real.log k) +
          xi ^ 2 * J k = -Real.sin (xi * Real.log k) by
            dsimp only [J]
            linarith [hsynth]]
    _ = -∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        criticalMellinAtomWeight k * Real.sin (xi * Real.log k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hweight : w k = criticalMellinAtomWeight k := by
        dsimp only [w, criticalMellinAtomWeight]
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hk0]
        ring
      rw [hweight]
      ring

/-- **First-clock Gamma singularity cancellation.**  In the sine-synthesized central family,
the lag-zero Gamma numerator cancels identically.  What survives is exactly the published
archimedean sine density before the change of variables `s = 2h`. -/
theorem ccmFirstClockGammaCancellationKernel_superposition
    {L xi s : ℝ} (hL : 0 < L) (hxi : xi ≠ 0)
    (hperiod : xi * L = 2 * Real.pi)
    (hs : 0 < s) (hsL : s / 2 ≤ L) :
    xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s +
        xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s =
      Real.exp (-(s / 4)) / (2 * (1 - Real.exp (-s))) *
        Real.sin (xi * (s / 2)) := by
  let h : ℝ := s / 2
  let A : ℝ := Real.exp (-s) / (1 - Real.exp (-s))
  let B : ℝ := -Real.exp (-(s / 4)) / (1 - Real.exp (-s))
  have hh : 0 ≤ h := by dsimp only [h]; linarith
  have hhL : h ≤ L := by simpa only [h] using hsL
  have hden : 1 - Real.exp (-s) ≠ 0 := by
    have : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hsynth0 :=
    ccmPhysicalSine_eq_centralRectangularAutocorrelationVolterra_zeroStart
      hL.le (le_refl 0) hL.le hxi hperiod
  have hsynthH :=
    ccmPhysicalSine_eq_centralRectangularAutocorrelationVolterra_zeroStart
      hL.le hh hhL hxi hperiod
  have hcomb0 :
      xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) 0 +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0 = 0 := by
    have hsynth0' :
        0 = -xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) 0 -
          xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0 := by
      simpa using hsynth0
    linarith [hsynth0']
  have hcombH :
      xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h =
        -Real.sin (xi * h) := by
    linarith [hsynthH]
  have hK (t : ℝ) :
      rectangularGammaCancellationKernel (t / 2) (t / 2) s =
        A * rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0 +
          B * rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h := by
    unfold rectangularGammaCancellationKernel
      rectangularGammaCancellationNumerator
    dsimp only [A, B, h]
    field_simp [hden]
    ring
  have hInt0 :=
    intervalIntegrable_sin_mul_centralRectangularAutocorrelation
      (xi := xi) hL.le (le_refl 0)
  have hIntH :=
    intervalIntegrable_sin_mul_centralRectangularAutocorrelation
      (xi := xi) hL.le hh
  have hIntK :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularGammaCancellationKernel (t / 2) (t / 2) s) =
        A * (∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
        B * (∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) := by
    calc
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularGammaCancellationKernel (t / 2) (t / 2) s) =
        ∫ t : ℝ in (0 : ℝ)..L,
          (A * (Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
          B * (Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h)) := by
              apply intervalIntegral.integral_congr
              intro t _ht
              change Real.sin (xi * t) *
                  rectangularGammaCancellationKernel (t / 2) (t / 2) s =
                A * (Real.sin (xi * t) *
                  rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
                B * (Real.sin (xi * t) *
                  rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h)
              rw [hK]
              ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (hInt0.const_mul A) (hIntH.const_mul B),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  calc
    xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s +
        xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s =
      A / 2 * (xi *
        rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) 0 +
          xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
      B / 2 * (xi *
        rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h +
          xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) := by
        rw [hK, hIntK]
        ring
    _ = _ := by
      rw [hcomb0, hcombH, mul_zero, zero_add]
      dsimp only [B, h]
      field_simp [hden]

/-- A lag beyond the terminal aperture is annihilated by every central triangle in the
first-clock superposition. -/
theorem ccmFirstClockCentralAutocorrelation_superposition_eq_zero_of_lt
    {L xi h : ℝ} (hL : 0 < L) (hhL : L < h) :
    xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h = 0 := by
  have hh : 0 ≤ h := by linarith
  have hterminal :
      rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h = 0 := by
    rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle hL.le hh,
      max_eq_left (sub_nonpos.mpr hhL.le)]
  have hintegral :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) = 0 := by
    calc
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) =
          ∫ _t : ℝ in (0 : ℝ)..L, 0 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hL.le] at ht
        have htmem := mem_Icc.mp ht
        change Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h = 0
        rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle htmem.1 hh,
          max_eq_left (sub_nonpos.mpr (by linarith [htmem.2, hhL]))]
        ring
      _ = 0 := by simp
  rw [hterminal, hintegral]
  ring

/-- Beyond twice the terminal aperture, the full Gamma superposition vanishes.  This closes the
support complement omitted from the local density formula. -/
theorem ccmFirstClockGammaCancellationKernel_superposition_eq_zero_of_lt
    {L xi s : ℝ} (hL : 0 < L) (hxi : xi ≠ 0)
    (hperiod : xi * L = 2 * Real.pi) (hs : 0 < s) (hLs : L < s / 2) :
    xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s +
        xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s = 0 := by
  let h : ℝ := s / 2
  let A : ℝ := Real.exp (-s) / (1 - Real.exp (-s))
  let B : ℝ := -Real.exp (-(s / 4)) / (1 - Real.exp (-s))
  have hh : 0 ≤ h := by dsimp only [h]; linarith
  have hden : 1 - Real.exp (-s) ≠ 0 := by
    have : Real.exp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hsynth0 :=
    ccmPhysicalSine_eq_centralRectangularAutocorrelationVolterra_zeroStart
      hL.le (le_refl 0) hL.le hxi hperiod
  have hcomb0 :
      xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) 0 +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0 = 0 := by
    have hsynth0' :
        0 = -xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) 0 -
          xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0 := by
      simpa using hsynth0
    linarith [hsynth0']
  have hcombH :
      xi * rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h = 0 :=
    ccmFirstClockCentralAutocorrelation_superposition_eq_zero_of_lt
      hL (by simpa only [h] using hLs)
  have hK (t : ℝ) :
      rectangularGammaCancellationKernel (t / 2) (t / 2) s =
        A * rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0 +
          B * rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h := by
    unfold rectangularGammaCancellationKernel
      rectangularGammaCancellationNumerator
    dsimp only [A, B, h]
    field_simp [hden]
    ring
  have hInt0 :=
    intervalIntegrable_sin_mul_centralRectangularAutocorrelation
      (xi := xi) hL.le (le_refl 0)
  have hIntH :=
    intervalIntegrable_sin_mul_centralRectangularAutocorrelation
      (xi := xi) hL.le hh
  have hIntK :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularGammaCancellationKernel (t / 2) (t / 2) s) =
        A * (∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
        B * (∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) := by
    calc
      _ = ∫ t : ℝ in (0 : ℝ)..L,
          (A * (Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
          B * (Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h)) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s =
          A * (Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
          B * (Real.sin (xi * t) *
            rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h)
        rw [hK]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (hInt0.const_mul A) (hIntH.const_mul B),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  calc
    xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s +
        xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s =
      A / 2 * (xi *
        rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) 0 +
          xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) 0) +
      B / 2 * (xi *
        rectangularTwoEdgeAutocorrelation (L / 2) (L / 2) h +
          xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) h) := by
        rw [hK, hIntK]
        ring
    _ = 0 := by
      rw [hcomb0, hcombH]
      ring

/-- Global pointwise Gamma synthesis: published density inside the aperture and exact zero
outside it. -/
theorem ccmFirstClockGammaCancellationKernel_superposition_global
    {L xi s : ℝ} (hL : 0 < L) (hxi : xi ≠ 0)
    (hperiod : xi * L = 2 * Real.pi) (hs : 0 < s) :
    xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s +
        xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s =
      if s ≤ 2 * L then
        Real.exp (-(s / 4)) / (2 * (1 - Real.exp (-s))) *
          Real.sin (xi * (s / 2))
      else 0 := by
  by_cases hsL : s ≤ 2 * L
  · rw [if_pos hsL]
    exact ccmFirstClockGammaCancellationKernel_superposition
      hL hxi hperiod hs (by linarith)
  · rw [if_neg hsL]
    exact ccmFirstClockGammaCancellationKernel_superposition_eq_zero_of_lt
      hL hxi hperiod hs (by linarith)

/-- One-sided CCM Gamma density in the form naturally produced by the rectangular cancellation
kernel. -/
theorem ccmPublishedArchimedeanDensity_eq_exp_neg_half_div
    {h : ℝ} (hh : 0 < h) :
    ccmPublishedArchimedeanDensity h =
      Real.exp (-h / 2) / (1 - Real.exp (-2 * h)) := by
  have hden : 1 - Real.exp (-2 * h) ≠ 0 := by
    have : Real.exp (-2 * h) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [ccmPublishedArchimedeanDensity]
  rw [show Real.exp (-h) = Real.exp h * Real.exp (-2 * h) by
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [show Real.exp (h / 2) = Real.exp (-h / 2) * Real.exp h by
    rw [← Real.exp_add]
    congr 1
    ring]
  field_simp [hden, ne_of_gt (Real.exp_pos h)]

/-- The globally synthesized Gamma kernel integrates to the literal finite archimedean sine
coordinate before the `π⁻¹` normalization. -/
theorem integral_ccmFirstClockGammaCancellationKernel_superposition_eq_arch
    {L xi : ℝ} (hL : 0 < L) (hxi : xi ≠ 0)
    (hperiod : xi * L = 2 * Real.pi) :
    (∫ s : ℝ in Ioi 0,
      (xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s +
        xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s)) =
      ∫ h : ℝ in Ioc 0 L,
        Real.sin (xi * h) * ccmPublishedArchimedeanDensity h := by
  let R : ℝ → ℝ := fun s =>
    Real.exp (-(s / 4)) / (2 * (1 - Real.exp (-s))) *
      Real.sin (xi * (s / 2))
  have hsupport :
      (∫ s : ℝ in Ioi 0,
        (xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s +
          xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularGammaCancellationKernel (t / 2) (t / 2) s)) =
        ∫ s : ℝ in Ioc 0 (2 * L), R s := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    by_cases hs0 : 0 < s
    · have hglobal :=
        ccmFirstClockGammaCancellationKernel_superposition_global
          hL hxi hperiod hs0
      by_cases hsL : s ≤ 2 * L
      · have hsIoi : s ∈ Ioi (0 : ℝ) := hs0
        have hsIoc : s ∈ Ioc (0 : ℝ) (2 * L) := ⟨hs0, hsL⟩
        simp only [Set.indicator, hsIoi, hsIoc, if_true]
        rw [hglobal, if_pos hsL]
      · have hsIoc : s ∉ Ioc (0 : ℝ) (2 * L) := by
          intro hmem
          exact hsL hmem.2
        simp only [Set.indicator, hsIoc, if_false]
        by_cases hsIoi : s ∈ Ioi (0 : ℝ)
        · simp only [hsIoi, if_true]
          rw [hglobal, if_neg hsL]
        · simp only [hsIoi, if_false]
    · have hsIoi : s ∉ Ioi (0 : ℝ) := by
        simpa only [mem_Ioi, not_lt] using le_of_not_gt hs0
      have hsIoc : s ∉ Ioc (0 : ℝ) (2 * L) := by
        intro hmem
        exact hs0 hmem.1
      simp only [Set.indicator, hsIoi, hsIoc, if_false]
  rw [hsupport]
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * L),
    ← intervalIntegral.integral_of_le hL.le]
  have hscale := intervalIntegral.integral_comp_mul_left
    (fun s : ℝ => R s) (show (2 : ℝ) ≠ 0 by norm_num)
    (a := 0) (b := L)
  have hdouble :
      (∫ s : ℝ in (0 : ℝ)..(2 * L), R s) =
        2 * ∫ h : ℝ in (0 : ℝ)..L, R (2 * h) := by
    have hscale' :
        (∫ h : ℝ in (0 : ℝ)..L, R (2 * h)) =
          (2 : ℝ)⁻¹ * ∫ s : ℝ in (0 : ℝ)..(2 * L), R s := by
      simpa only [smul_eq_mul, mul_zero] using hscale
    rw [hscale']
    ring
  rw [hdouble, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro h _hhmem
  by_cases hh0 : h = 0
  · subst h
    simp [R, ccmPublishedArchimedeanDensity]
  · have hhpos : 0 < h := by
      rw [uIcc_of_le hL.le] at _hhmem
      exact lt_of_le_of_ne (mem_Icc.mp _hhmem).1 (Ne.symm hh0)
    change 2 * R (2 * h) =
      Real.sin (xi * h) * ccmPublishedArchimedeanDensity h
    rw [ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hhpos]
    dsimp only [R]
    rw [show -(2 * h / 4) = -h / 2 by ring,
      show -(2 * h) = -2 * h by ring,
      show 2 * h / 2 = h by ring]
    have hden : 1 - Real.exp (-2 * h) ≠ 0 := by
      have : Real.exp (-2 * h) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    field_simp [hden]

/-- Fubini law for the sine-weighted central Gamma cancellation family.  The existing sharp
near-zero and exponential-tail bounds give an integrable product majorant uniformly over the
compact aperture parameter. -/
theorem ccmFirstClockGammaCancellationKernel_fubini_and_integrable
    {L xi : ℝ} (hL : 0 < L) :
    ((∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          (∫ s : ℝ in Ioi 0,
            rectangularGammaCancellationKernel (t / 2) (t / 2) s)) =
        ∫ s : ℝ in Ioi 0,
          ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularGammaCancellationKernel (t / 2) (t / 2) s) ∧
      (IntegrableOn
          (fun s : ℝ => ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularGammaCancellationKernel (t / 2) (t / 2) s)
          (Ioi 0) ∧
        IntervalIntegrable
          (fun t : ℝ => Real.sin (xi * t) *
            (∫ s : ℝ in Ioi 0,
              rectangularGammaCancellationKernel (t / 2) (t / 2) s))
          volume 0 L) := by
  let mu : Measure ℝ := volume.restrict (Ioc (0 : ℝ) L)
  let nu : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun t s =>
    Real.sin (xi * t) *
      rectangularGammaCancellationKernel (t / 2) (t / 2) s
  let M : ℝ → ℝ := fun s =>
    (Ioc (0 : ℝ) 1).indicator (fun _ => 4 * L + 3) s +
      (5 * (L / 2) / (1 - Real.exp (-1))) * Real.exp (-(s / 4))
  have hd : 0 < 1 - Real.exp (-1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hM : Integrable M nu := by
    have hnearGlobal :
        Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => 4 * L + 3)) :=
      (integrableOn_const (s := Ioc (0 : ℝ) 1)
        (ne_of_lt measure_Ioc_lt_top)).integrable_indicator measurableSet_Ioc
    have hnear :
        Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => 4 * L + 3)) nu :=
      hnearGlobal.mono_measure Measure.restrict_le_self
    have htailExp :
        Integrable (fun s : ℝ => Real.exp (-(s / 4))) nu := by
      show IntegrableOn (fun s : ℝ => Real.exp (-(s / 4))) (Ioi 0)
      convert (integrableOn_exp_mul_Ioi (a := (-1 / 4 : ℝ))
        (by norm_num) 0) using 1 <;> ring
    have htail :
        Integrable (fun s : ℝ =>
          (5 * (L / 2) / (1 - Real.exp (-1))) * Real.exp (-(s / 4))) nu :=
      htailExp.const_mul _
    exact hnear.add htail
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (mu.prod nu) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    unfold rectangularGammaCancellationKernel
      rectangularGammaCancellationNumerator
    simp_rw [rectangularTwoEdgeAutocorrelation_eq_four_tents]
    fun_prop
  have hKbound :
      ∀ t ∈ Ioc (0 : ℝ) L, ∀ s ∈ Ioi (0 : ℝ),
        |rectangularGammaCancellationKernel (t / 2) (t / 2) s| ≤ M s := by
    intro t ht s hs
    by_cases hs1 : s ≤ 1
    · have hbase :=
        abs_rectangularGammaCancellationKernel_le_near_zero
          (L := t / 2) (a := t / 2) (by linarith [ht.1])
          (le_refl (t / 2)) hs hs1
      have htail0 :
          0 ≤ (5 * (L / 2) / (1 - Real.exp (-1))) * Real.exp (-(s / 4)) := by
        positivity
      dsimp only [M]
      rw [Set.indicator_of_mem (show s ∈ Ioc (0 : ℝ) 1 from ⟨hs, hs1⟩)]
      have hbase' :
          |rectangularGammaCancellationKernel (t / 2) (t / 2) s| ≤
            4 * L + 3 := by
        calc
          _ ≤ 8 * (t / 2) + 3 := hbase
          _ ≤ 4 * L + 3 := by linarith [ht.2]
      linarith
    · have hs1' : 1 ≤ s := by linarith
      have hbase :=
        abs_rectangularGammaCancellationKernel_le_tail
          (L := t / 2) (a := t / 2) (by linarith [ht.1])
          (le_refl (t / 2)) hs1'
      have hcoef :
          5 * (t / 2) / (1 - Real.exp (-1)) ≤
            5 * (L / 2) / (1 - Real.exp (-1)) :=
        div_le_div_of_nonneg_right (by linarith [ht.2]) hd.le
      have htail :
          5 * (t / 2) / (1 - Real.exp (-1)) * Real.exp (-(s / 4)) ≤
            5 * (L / 2) / (1 - Real.exp (-1)) * Real.exp (-(s / 4)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-(s / 4))).le
      dsimp only [M]
      have hsnot : s ∉ Ioc (0 : ℝ) 1 := by
        intro hmem
        exact hs1 hmem.2
      simp only [Set.indicator, hsnot, if_false, zero_add]
      exact hbase.trans htail
  have hFbound :
      ∀ t ∈ Ioc (0 : ℝ) L, ∀ s ∈ Ioi (0 : ℝ), ‖F t s‖ ≤ M s := by
    intro t ht s hs
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |Real.sin (xi * t)| *
          |rectangularGammaCancellationKernel (t / 2) (t / 2) s| ≤
        1 * |rectangularGammaCancellationKernel (t / 2) (t / 2) s| :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ M s := by simpa using hKbound t ht s hs
  have hslice : ∀ᵐ t ∂mu, Integrable (F t) nu := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hK :=
      integrableOn_rectangularGammaCancellationKernel
        (L := t / 2) (a := t / 2) (by linarith [ht.1])
        (le_refl (t / 2))
    simpa only [F, nu] using hK.const_mul (Real.sin (xi * t))
  have hnormint : Integrable (fun t => ∫ s, ‖F t s‖ ∂nu) mu := by
    have hconst :
        Integrable (fun _ : ℝ => ∫ s, M s ∂nu) mu := by
      dsimp only [mu]
      exact integrableOn_const (ne_of_lt measure_Ioc_lt_top)
    refine Integrable.mono' hconst (hmeas.norm.integral_prod_right') ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnonneg : 0 ≤ ∫ s, ‖F t s‖ ∂nu :=
      integral_nonneg fun s => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun s => norm_nonneg _
    · exact hM
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hFbound t ht s hs
  have hprod : Integrable (Function.uncurry F) (mu.prod nu) :=
    (integrable_prod_iff hmeas).mpr ⟨hslice, hnormint⟩
  have hswap := integral_integral_swap hprod
  have heq :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          (∫ s : ℝ in Ioi 0,
            rectangularGammaCancellationKernel (t / 2) (t / 2) s)) =
        ∫ s : ℝ in Ioi 0,
          ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) *
              rectangularGammaCancellationKernel (t / 2) (t / 2) s := by
    calc
    (∫ t : ℝ in (0 : ℝ)..L,
      Real.sin (xi * t) *
        (∫ s : ℝ in Ioi 0,
          rectangularGammaCancellationKernel (t / 2) (t / 2) s)) =
      ∫ t : ℝ in Ioc 0 L,
        Real.sin (xi * t) *
          (∫ s : ℝ in Ioi 0,
            rectangularGammaCancellationKernel (t / 2) (t / 2) s) :=
        intervalIntegral.integral_of_le hL.le
    _ = ∫ t : ℝ in Ioc 0 L,
        ∫ s : ℝ in Ioi 0, F t s := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      dsimp only [F]
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ s : ℝ in Ioi 0,
        ∫ t : ℝ in Ioc 0 L, F t s := by
      simpa only [mu, nu, Function.uncurry_apply_pair] using hswap
    _ = ∫ s : ℝ in Ioi 0,
        ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [intervalIntegral.integral_of_le hL.le]
  have hinnerSet :
      Integrable (fun s : ℝ => ∫ t : ℝ in Ioc 0 L, F t s) nu := by
    simpa only [mu, nu, Function.uncurry_apply_pair] using
      hprod.integral_prod_right
  have hinner :
      IntegrableOn
        (fun s : ℝ => ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s)
        (Ioi 0) := by
    apply hinnerSet.congr
    filter_upwards with s
    rw [intervalIntegral.integral_of_le hL.le]
  have htinnerSet :
      Integrable (fun t : ℝ => ∫ s : ℝ in Ioi 0, F t s) mu := by
    simpa only [mu, nu, Function.uncurry_apply_pair] using
      hprod.integral_prod_left
  have htinnerSet' :
      IntegrableOn
        (fun t : ℝ => Real.sin (xi * t) *
          (∫ s : ℝ in Ioi 0,
            rectangularGammaCancellationKernel (t / 2) (t / 2) s))
        (Ioc 0 L) := by
    apply htinnerSet.congr
    filter_upwards with t
    dsimp only [F]
    rw [MeasureTheory.integral_const_mul]
  have htinner :
      IntervalIntegrable
        (fun t : ℝ => Real.sin (xi * t) *
          (∫ s : ℝ in Ioi 0,
            rectangularGammaCancellationKernel (t / 2) (t / 2) s))
        volume 0 L := by
    rw [intervalIntegrable_iff]
    simpa only [uIoc_of_le hL.le] using htinnerSet'
  exact ⟨heq, hinner, htinner⟩

/-- Fubini equality extracted from the product-integrability theorem. -/
theorem ccmFirstClockGammaCancellationKernel_fubini
    {L xi : ℝ} (hL : 0 < L) :
    (∫ t : ℝ in (0 : ℝ)..L,
      Real.sin (xi * t) *
        (∫ s : ℝ in Ioi 0,
          rectangularGammaCancellationKernel (t / 2) (t / 2) s)) =
      ∫ s : ℝ in Ioi 0,
        ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s :=
  (ccmFirstClockGammaCancellationKernel_fubini_and_integrable hL).1

/-- Integrability of the Gamma inner aperture integral. -/
theorem integrableOn_ccmFirstClockGammaCancellationKernel_inner
    {L xi : ℝ} (hL : 0 < L) :
    IntegrableOn
      (fun s : ℝ => ∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularGammaCancellationKernel (t / 2) (t / 2) s)
      (Ioi 0) :=
  (ccmFirstClockGammaCancellationKernel_fubini_and_integrable hL).2.1

/-- Interval integrability of the aperture-side Gamma integral. -/
theorem intervalIntegrable_sin_mul_integral_ccmFirstClockGammaCancellationKernel
    {L xi : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (fun t : ℝ => Real.sin (xi * t) *
        (∫ s : ℝ in Ioi 0,
          rectangularGammaCancellationKernel (t / 2) (t / 2) s))
      volume 0 L :=
  (ccmFirstClockGammaCancellationKernel_fubini_and_integrable hL).2.2

/-- Integrated Gamma superposition with the individual integrals restored. -/
theorem ccmFirstClockGammaCancellationIntegral_superposition_eq_arch
    {L xi : ℝ} (hL : 0 < L) (hxi : xi ≠ 0)
    (hperiod : xi * L = 2 * Real.pi) :
    xi / 2 * (∫ s : ℝ in Ioi 0,
        rectangularGammaCancellationKernel (L / 2) (L / 2) s) +
      xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          (∫ s : ℝ in Ioi 0,
            rectangularGammaCancellationKernel (t / 2) (t / 2) s) =
      ∫ h : ℝ in Ioc 0 L,
        Real.sin (xi * h) * ccmPublishedArchimedeanDensity h := by
  let A : ℝ → ℝ := fun s =>
    xi / 2 * rectangularGammaCancellationKernel (L / 2) (L / 2) s
  let B : ℝ → ℝ := fun s =>
    xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
      Real.sin (xi * t) *
        rectangularGammaCancellationKernel (t / 2) (t / 2) s
  have hA : IntegrableOn A (Ioi 0) := by
    dsimp only [A]
    exact (integrableOn_rectangularGammaCancellationKernel
      (L := L / 2) (a := L / 2) (by positivity) (le_refl (L / 2))).const_mul _
  have hB : IntegrableOn B (Ioi 0) := by
    dsimp only [B]
    exact (integrableOn_ccmFirstClockGammaCancellationKernel_inner
      (xi := xi) hL).const_mul _
  have hfubini :=
    ccmFirstClockGammaCancellationKernel_fubini (xi := xi) hL
  calc
    xi / 2 * (∫ s : ℝ in Ioi 0,
        rectangularGammaCancellationKernel (L / 2) (L / 2) s) +
      xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          (∫ s : ℝ in Ioi 0,
            rectangularGammaCancellationKernel (t / 2) (t / 2) s) =
      xi / 2 * (∫ s : ℝ in Ioi 0,
        rectangularGammaCancellationKernel (L / 2) (L / 2) s) +
      xi ^ 2 / 2 * ∫ s : ℝ in Ioi 0,
        ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularGammaCancellationKernel (t / 2) (t / 2) s := by
        rw [hfubini]
    _ = (∫ s : ℝ in Ioi 0, A s) + ∫ s : ℝ in Ioi 0, B s := by
      dsimp only [A, B]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = ∫ s : ℝ in Ioi 0, A s + B s := by
      exact (MeasureTheory.integral_add hA hB).symm
    _ = _ := by
      simpa only [A, B] using
        integral_ccmFirstClockGammaCancellationKernel_superposition_eq_arch
          hL hxi hperiod

/-- Real central form of the exact rectangular archimedean edge. -/
theorem normalizedRectangularBottomArchContribution_central_re
    {t : ℝ} (ht : 0 ≤ t) :
    (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re =
      (∫ s : ℝ in Ioi 0,
        rectangularGammaCancellationKernel (t / 2) (t / 2) s) +
      2 * rectangularEvenPolarFeature (t / 2) (t / 2) ^ 2 -
      (Real.eulerMascheroniConstant + Real.log Real.pi) * t := by
  rw [normalizedRectangularBottomArchContribution_eq_two_mul_eulerIntegral,
    two_mul_integral_rectangularEulerArchIntegrand_eq
      (by positivity : 0 ≤ t / 2) (le_refl (t / 2))]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The linear boundary charge is killed by one full physical period. -/
theorem ccmFirstClockLinearBoundary_superposition
    {L xi : ℝ} (hL : 0 ≤ L) (hxi : xi ≠ 0)
    (hperiod : xi * L = 2 * Real.pi) :
    xi * L + xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
      Real.sin (xi * t) * t = 0 := by
  have hsynth :=
    ccmPhysicalSine_eq_triangleVolterra_zeroStart
      hL (le_refl 0) hL hxi hperiod
  have hint :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * max 0 (t - 0)) =
        ∫ t : ℝ in (0 : ℝ)..L, Real.sin (xi * t) * t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL] at ht
    have ht0 := (mem_Icc.mp ht).1
    change Real.sin (xi * t) * max 0 (t - 0) =
      Real.sin (xi * t) * t
    rw [sub_zero, max_eq_right ht0]
  rw [hint] at hsynth
  simp only [sub_zero, max_eq_right hL, mul_zero, Real.sin_zero] at hsynth
  linarith [hsynth]

/-- Closed central polar-square law.  The nominal rank-two feature collapses to the hyperbolic
second primitive of the central triangular autocorrelation. -/
theorem rectangularEvenPolarFeature_central_sq
    {t : ℝ} (ht : 0 ≤ t) :
    rectangularEvenPolarFeature (t / 2) (t / 2) ^ 2 =
      8 * (Real.cosh (t / 2) - 1) := by
  rw [rectangularEvenPolarFeature_eq (by positivity : 0 ≤ t / 2)]
  rw [show (t / 2 - t / 2) / 2 = 0 by ring, Real.sinh_zero, sub_zero]
  rw [show t / 2 / 2 = t / 4 by ring]
  rw [show t / 2 = 2 * (t / 4) by ring, Real.cosh_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq (t / 4)]

/-- Universal twofold integration-by-parts law at one full physical period. -/
theorem ccmFirstClockHyperbolicSecondPrimitive_superposition
    {L xi : ℝ} (hL : 0 ≤ L) (hperiod : xi * L = 2 * Real.pi) :
    xi * (8 * (Real.cosh (L / 2) - 1)) +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * (8 * (Real.cosh (t / 2) - 1)) =
      -∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * (2 * Real.cosh (t / 2)) := by
  let Q : ℝ → ℝ := fun t => 8 * (Real.cosh (t / 2) - 1)
  let Q' : ℝ → ℝ := fun t => 4 * Real.sinh (t / 2)
  let Q'' : ℝ → ℝ := fun t => 2 * Real.cosh (t / 2)
  let S : ℝ → ℝ := fun t => Real.sin (xi * t)
  let S' : ℝ → ℝ := fun t => xi * Real.cos (xi * t)
  let C : ℝ → ℝ := fun t => Real.cos (xi * t)
  let C' : ℝ → ℝ := fun t => -xi * Real.sin (xi * t)
  have hQ : ∀ t : ℝ, HasDerivAt Q (Q' t) t := by
    intro t
    dsimp only [Q, Q']
    convert ((((hasDerivAt_id t).div_const 2).cosh.sub_const 1).const_mul 8) using 1 <;>
      simp only [id_eq] <;> ring
  have hQ' : ∀ t : ℝ, HasDerivAt Q' (Q'' t) t := by
    intro t
    dsimp only [Q', Q'']
    convert (((hasDerivAt_id t).div_const 2).sinh.const_mul 4) using 1 <;>
      simp only [id_eq] <;> ring
  have hS : ∀ t : ℝ, HasDerivAt S (S' t) t := by
    intro t
    dsimp only [S, S']
    convert ((hasDerivAt_id t).const_mul xi).sin using 1 <;>
      simp only [id_eq] <;> ring
  have hC : ∀ t : ℝ, HasDerivAt C (C' t) t := by
    intro t
    dsimp only [C, C']
    convert ((hasDerivAt_id t).const_mul xi).cos using 1 <;>
      simp only [id_eq] <;> ring
  have hQInt : IntervalIntegrable Q volume 0 L :=
    (by dsimp only [Q]; fun_prop : Continuous Q).intervalIntegrable 0 L
  have hQ'Int : IntervalIntegrable Q' volume 0 L :=
    (by dsimp only [Q']; fun_prop : Continuous Q').intervalIntegrable 0 L
  have hQ''Int : IntervalIntegrable Q'' volume 0 L :=
    (by dsimp only [Q'']; fun_prop : Continuous Q'').intervalIntegrable 0 L
  have hS'Int : IntervalIntegrable S' volume 0 L :=
    (by dsimp only [S']; fun_prop : Continuous S').intervalIntegrable 0 L
  have hC'Int : IntervalIntegrable C' volume 0 L :=
    (by dsimp only [C']; fun_prop : Continuous C').intervalIntegrable 0 L
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := S) (v := Q') (u' := S') (v' := Q'')
    (fun t _ => hS t) (fun t _ => hQ' t) hS'Int hQ''Int
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := C) (v := Q) (u' := C') (v' := Q')
    (fun t _ => hC t) (fun t _ => hQ t) hC'Int hQ'Int
  have hsinL : Real.sin (xi * L) = 0 := by
    rw [hperiod]
    simpa only [Nat.cast_ofNat] using Real.sin_nat_mul_pi 2
  have hcosL : Real.cos (xi * L) = 1 := by
    rw [hperiod, show 2 * Real.pi = (1 : ℤ) * (2 * Real.pi) by ring,
      Real.cos_int_mul_two_pi]
  dsimp only [S, S', C, C', Q, Q', Q''] at hfirst hsecond ⊢
  rw [hsinL] at hfirst
  rw [hcosL] at hsecond
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_mul, zero_div,
    Real.cosh_zero, sub_self, one_mul, sub_zero, zero_sub] at hfirst hsecond
  have hpullFirst :
      (∫ x : ℝ in (0 : ℝ)..L,
        xi * Real.cos (xi * x) * (4 * Real.sinh (x / 2))) =
        xi * ∫ x : ℝ in (0 : ℝ)..L,
          Real.cos (xi * x) * (4 * Real.sinh (x / 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hpullSecond :
      (∫ x : ℝ in (0 : ℝ)..L,
        -xi * Real.sin (xi * x) *
          (8 * (Real.cosh (x / 2) - 1))) =
        -xi * ∫ x : ℝ in (0 : ℝ)..L,
          Real.sin (xi * x) * (8 * (Real.cosh (x / 2) - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hpullFirst] at hfirst
  rw [hpullSecond] at hsecond
  linear_combination hfirst - xi * hsecond

/-- Exact even-polar component of the first-clock source synthesis. -/
theorem ccmFirstClockEvenPolarFeature_superposition
    {L xi : ℝ} (hL : 0 ≤ L) (hperiod : xi * L = 2 * Real.pi) :
    xi * rectangularEvenPolarFeature (L / 2) (L / 2) ^ 2 +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularEvenPolarFeature (t / 2) (t / 2) ^ 2 =
      -2 * ∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * Real.cosh (t / 2) := by
  rw [rectangularEvenPolarFeature_central_sq hL]
  have hint :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          rectangularEvenPolarFeature (t / 2) (t / 2) ^ 2) =
        ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * (8 * (Real.cosh (t / 2) - 1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL] at ht
    have ht0 : 0 ≤ t := (mem_Icc.mp ht).1
    change Real.sin (xi * t) *
        rectangularEvenPolarFeature (t / 2) (t / 2) ^ 2 =
      Real.sin (xi * t) * (8 * (Real.cosh (t / 2) - 1))
    rw [rectangularEvenPolarFeature_central_sq ht0]
  rw [hint]
  calc
    xi * (8 * (Real.cosh (L / 2) - 1)) +
          xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
            Real.sin (xi * t) * (8 * (Real.cosh (t / 2) - 1)) =
        -∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * (2 * Real.cosh (t / 2)) :=
      ccmFirstClockHyperbolicSecondPrimitive_superposition hL hperiod
    _ = -2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * Real.cosh (t / 2) := by
      rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _ht
      ring

/-- Exact central archimedean source synthesis.  Gamma, even-polar, and boundary pieces combine
to the literal published density minus the continuous polar Stieltjes term. -/
theorem ccmFirstClockNormalizedArchContribution_superposition
    {L xi : ℝ} (hL : 0 < L) (hperiod : xi * L = 2 * Real.pi) :
    xi / 2 *
        (normalizedRectangularBottomArchContribution (L / 2) (L / 2)).re +
      xi ^ 2 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re =
      (∫ h : ℝ in Ioc 0 L,
        Real.sin (xi * h) * ccmPublishedArchimedeanDensity h) -
      ∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * (2 * Real.cosh (t / 2)) := by
  let c : ℝ := Real.eulerMascheroniConstant + Real.log Real.pi
  let K : ℝ → ℝ := fun t =>
    ∫ s : ℝ in Ioi 0,
      rectangularGammaCancellationKernel (t / 2) (t / 2) s
  let P : ℝ → ℝ := fun t =>
    rectangularEvenPolarFeature (t / 2) (t / 2) ^ 2
  have hxi : xi ≠ 0 := by
    intro hxi0
    rw [hxi0, zero_mul] at hperiod
    linarith [Real.pi_pos]
  have hKInt :
      IntervalIntegrable (fun t : ℝ => Real.sin (xi * t) * K t)
        volume 0 L := by
    simpa only [K] using
      intervalIntegrable_sin_mul_integral_ccmFirstClockGammaCancellationKernel
        (xi := xi) hL
  have hPInt :
      IntervalIntegrable (fun t : ℝ => Real.sin (xi * t) * P t)
        volume 0 L := by
    refine IntervalIntegrable.congr ?_
      ((by fun_prop : Continuous (fun t : ℝ =>
        Real.sin (xi * t) * (8 * (Real.cosh (t / 2) - 1))))
        |>.intervalIntegrable 0 L)
    intro t ht
    rw [uIoc_of_le hL.le] at ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    dsimp only [P]
    rw [rectangularEvenPolarFeature_central_sq ht0]
  have hTInt :
      IntervalIntegrable (fun t : ℝ => Real.sin (xi * t) * t)
        volume 0 L :=
    (by fun_prop : Continuous (fun t : ℝ => Real.sin (xi * t) * t))
      |>.intervalIntegrable 0 L
  have hArchIntegral :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) *
          (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re) =
        (∫ t : ℝ in (0 : ℝ)..L, Real.sin (xi * t) * K t) +
          2 * (∫ t : ℝ in (0 : ℝ)..L, Real.sin (xi * t) * P t) -
          c * ∫ t : ℝ in (0 : ℝ)..L, Real.sin (xi * t) * t := by
    calc
      _ = ∫ t : ℝ in (0 : ℝ)..L,
          ((Real.sin (xi * t) * K t +
            2 * (Real.sin (xi * t) * P t)) -
            c * (Real.sin (xi * t) * t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hL.le] at ht
        have ht0 := (mem_Icc.mp ht).1
        change Real.sin (xi * t) *
            (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re =
          (Real.sin (xi * t) * K t + 2 * (Real.sin (xi * t) * P t)) -
            c * (Real.sin (xi * t) * t)
        rw [normalizedRectangularBottomArchContribution_central_re ht0]
        dsimp only [K, P, c]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
          (hKInt.add (hPInt.const_mul 2)) (hTInt.const_mul c),
          intervalIntegral.integral_add hKInt (hPInt.const_mul 2),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [normalizedRectangularBottomArchContribution_central_re hL.le,
    hArchIntegral]
  have hGamma :=
    ccmFirstClockGammaCancellationIntegral_superposition_eq_arch
      hL hxi hperiod
  have hPolar :=
    ccmFirstClockEvenPolarFeature_superposition hL.le hperiod
  have hBoundary :=
    ccmFirstClockLinearBoundary_superposition hL.le hxi hperiod
  have hcosPull :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * (2 * Real.cosh (t / 2))) =
        2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * Real.cosh (t / 2) := by
    calc
      _ = ∫ t : ℝ in (0 : ℝ)..L,
          2 * (Real.sin (xi * t) * Real.cosh (t / 2)) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hcosPull]
  dsimp only [K, P, c] at hGamma hPolar hBoundary ⊢
  linear_combination hGamma + hPolar -
    (Real.eulerMascheroniConstant + Real.log Real.pi) / 2 * hBoundary

/-- Real central prime--arch form of the sharp rectangular Guinand--Weil identity. -/
theorem two_mul_xiScrewDivisor_re_eq_central_prime_add_arch
    {t : ℝ} (ht : 0 ≤ t) :
    2 * (xiScrewDivisor t).re =
      -2 * rectangularPrimeAutocorrelationSum (t / 2) (t / 2) +
        (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re := by
  have hfull := xiWeilPolarization_rectangular_eq_prime_add_arch
    (L := t / 2) (a := t / 2) (by positivity) (le_refl (t / 2))
  rw [xiWeilPolarization_central_rectangular_eq_two_mul_screw] at hfull
  have hre := congrArg Complex.re hfull
  norm_num at hre
  convert hre using 1 <;> ring

/-- Sine-weighted central prime autocorrelation is interval-integrable. -/
theorem intervalIntegrable_sin_mul_centralPrimeAutocorrelation
    {L xi : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (fun t : ℝ => Real.sin (xi * t) *
        rectangularPrimeAutocorrelationSum (t / 2) (t / 2))
      volume 0 L := by
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp L⌋₊
  let w : ℕ → ℝ := fun k =>
    ArithmeticFunction.vonMangoldt k / Real.sqrt k
  refine IntervalIntegrable.congr ?_
    ((by fun_prop : Continuous (fun t : ℝ =>
      Real.sin (xi * t) *
        ∑ k ∈ K, w k * max 0 (t - Real.log k))).intervalIntegrable 0 L)
  intro t ht
  rw [uIoc_of_le hL.le] at ht
  have ht0 : 0 ≤ t := le_of_lt ht.1
  change Real.sin (xi * t) * ∑ k ∈ K, w k * max 0 (t - Real.log k) =
    Real.sin (xi * t) *
      rectangularPrimeAutocorrelationSum (t / 2) (t / 2)
  rw [rectangularPrimeAutocorrelationSum_central_eq_commonTriangle
    ht0 ht.2]

/-- Sine-weighted central normalized arch contribution is interval-integrable. -/
theorem intervalIntegrable_sin_mul_centralNormalizedArchContribution
    {L xi : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (fun t : ℝ => Real.sin (xi * t) *
        (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re)
      volume 0 L := by
  let K : ℝ → ℝ := fun t =>
    ∫ s : ℝ in Ioi 0,
      rectangularGammaCancellationKernel (t / 2) (t / 2) s
  let P : ℝ → ℝ := fun t =>
    rectangularEvenPolarFeature (t / 2) (t / 2) ^ 2
  let c : ℝ := Real.eulerMascheroniConstant + Real.log Real.pi
  have hKInt :
      IntervalIntegrable (fun t : ℝ => Real.sin (xi * t) * K t)
        volume 0 L := by
    simpa only [K] using
      intervalIntegrable_sin_mul_integral_ccmFirstClockGammaCancellationKernel
        (xi := xi) hL
  have hPInt :
      IntervalIntegrable (fun t : ℝ => Real.sin (xi * t) * P t)
        volume 0 L := by
    refine IntervalIntegrable.congr ?_
      ((by fun_prop : Continuous (fun t : ℝ =>
        Real.sin (xi * t) * (8 * (Real.cosh (t / 2) - 1))))
        |>.intervalIntegrable 0 L)
    intro t ht
    rw [uIoc_of_le hL.le] at ht
    dsimp only [P]
    rw [rectangularEvenPolarFeature_central_sq (le_of_lt ht.1)]
  have hTInt :
      IntervalIntegrable (fun t : ℝ => Real.sin (xi * t) * t)
        volume 0 L :=
    (by fun_prop : Continuous (fun t : ℝ => Real.sin (xi * t) * t))
      |>.intervalIntegrable 0 L
  refine IntervalIntegrable.congr ?_
    ((hKInt.add (hPInt.const_mul 2)).sub (hTInt.const_mul c))
  intro t ht
  rw [uIoc_of_le hL.le] at ht
  have ht0 : 0 ≤ t := le_of_lt ht.1
  change (Real.sin (xi * t) * K t + 2 * (Real.sin (xi * t) * P t)) -
      c * (Real.sin (xi * t) * t) =
    Real.sin (xi * t) *
      (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re
  rw [normalizedRectangularBottomArchContribution_central_re ht0]
  dsimp only [K, P, c]
  ring

/-- Literal real expansion of the polar--prime Stieltjes pairing on the physical sine test. -/
theorem criticalMellinStieltjesPairing_sine_re
    {L xi : ℝ} (hL : 0 ≤ L) :
    (criticalMellinStieltjesPairing (L / 2)
      (fun h => (Real.sin (xi * h) : ℂ))).re =
      (∫ h : ℝ in Ioc 0 L,
        Real.sin (xi * h) * (2 * Real.cosh (h / 2))) -
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        criticalMellinAtomWeight k * Real.sin (xi * Real.log k) := by
  have hInt :
      Integrable (fun h : ℝ =>
        (Real.sin (xi * h) : ℂ) * (2 * Real.cosh (h / 2) : ℂ))
        (volume.restrict (Ioc 0 L)) := by
    have hcont : Continuous (fun h : ℝ =>
        (Real.sin (xi * h) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)) := by
      fun_prop
    exact (hcont.continuousOn.integrableOn_Icc).mono_set fun h hh =>
      ⟨hh.1.le, hh.2⟩
  have hintRe :
      (∫ h : ℝ in Ioc 0 L,
        (Real.sin (xi * h) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)).re =
        ∫ h : ℝ in Ioc 0 L,
          Real.sin (xi * h) * (2 * Real.cosh (h / 2)) := by
    calc
      _ = ∫ h : ℝ in Ioc 0 L,
          ((Real.sin (xi * h) : ℂ) *
            (2 * Real.cosh (h / 2) : ℂ)).re :=
        (integral_re hInt).symm
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with h
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        norm_num
  rw [criticalMellinStieltjesPairing, show 2 * (L / 2) = L by ring,
    Complex.sub_re, hintRe]
  simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- **Literal CCM source/Xi bridge.**  The published first physical source numerator is exactly
the first-clock Volterra coordinate of the complete Xi screw divisor. -/
theorem ccmFirstClockWeightedScrew_re_eq_pi_mul_publishedSource
    {L xi : ℝ} (hL : 0 < L) (hperiod : xi * L = 2 * Real.pi) :
    xi * (xiScrewDivisor L).re +
      xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * (xiScrewDivisor t).re =
      Real.pi * ccmPublishedSourceSineCoefficient (L / 2) xi := by
  have hPrimeInt :=
    intervalIntegrable_sin_mul_centralPrimeAutocorrelation (xi := xi) hL
  have hArchInt :=
    intervalIntegrable_sin_mul_centralNormalizedArchContribution (xi := xi) hL
  have hScrewIntegral :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * (xiScrewDivisor t).re) =
        -(∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            rectangularPrimeAutocorrelationSum (t / 2) (t / 2)) +
        1 / 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) *
            (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re := by
    calc
      _ = ∫ t : ℝ in (0 : ℝ)..L,
          (-(Real.sin (xi * t) *
            rectangularPrimeAutocorrelationSum (t / 2) (t / 2)) +
          (1 / 2) * (Real.sin (xi * t) *
            (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hL.le] at ht
        have hcentral :=
          two_mul_xiScrewDivisor_re_eq_central_prime_add_arch
            (mem_Icc.mp ht).1
        linear_combination Real.sin (xi * t) / 2 * hcentral
      _ = _ := by
        have hadd := intervalIntegral.integral_add hPrimeInt.neg
          (hArchInt.const_mul (1 / 2))
        simp only [Pi.neg_apply] at hadd
        rw [intervalIntegral.integral_neg,
          intervalIntegral.integral_const_mul] at hadd
        exact hadd
  have hcentralL :=
    two_mul_xiScrewDivisor_re_eq_central_prime_add_arch hL.le
  have hPrime :=
    ccmFirstClockPrimeAutocorrelation_superposition hL hperiod
  have hArch :=
    ccmFirstClockNormalizedArchContribution_superposition hL hperiod
  have hpair :=
    criticalMellinStieltjesPairing_sine_re (L := L) (xi := xi) hL.le
  have hpolarSet :
      (∫ t : ℝ in (0 : ℝ)..L,
        Real.sin (xi * t) * (2 * Real.cosh (t / 2))) =
        ∫ t : ℝ in Ioc 0 L,
          Real.sin (xi * t) * (2 * Real.cosh (t / 2)) :=
    intervalIntegral.integral_of_le hL.le
  rw [hpolarSet] at hArch
  have hpolarAssoc :
      (∫ t : ℝ in Ioc 0 L,
        Real.sin (xi * t) * (2 * Real.cosh (t / 2))) =
        ∫ t : ℝ in Ioc 0 L,
          Real.sin (xi * t) * 2 * Real.cosh (t / 2) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  rw [hpolarAssoc] at hpair
  rw [hpolarAssoc] at hArch
  have hraw :
      xi * (xiScrewDivisor L).re +
        xi ^ 2 * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * (xiScrewDivisor t).re =
        (∫ h : ℝ in Ioc 0 L,
          Real.sin (xi * h) * ccmPublishedArchimedeanDensity h) -
        (criticalMellinStieltjesPairing (L / 2)
          (fun h => (Real.sin (xi * h) : ℂ))).re := by
    rw [hScrewIntegral]
    linear_combination xi / 2 * hcentralL - hPrime + hArch + hpair
  rw [hraw, ccmPublishedSourceSineCoefficient,
    ccmPublishedArchimedeanSineCoefficient,
    ccmPublishedPolarPrimeSineCoefficient,
    show 2 * (L / 2) = L by ring]
  field_simp [Real.pi_ne_zero]
  ring

/-- Real-part form of the multiplicity-exact Xi first-clock Volterra law. -/
theorem ccmFirstClockXiRationalDivisor_re_eq_screw_re_add_volterra
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    (ccmFirstClockXiRationalDivisor L).re =
      (xiScrewDivisor L).re +
        (2 * Real.pi / L) * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin ((2 * Real.pi / L) * t) * (xiScrewDivisor t).re := by
  let xi : ℝ := 2 * Real.pi / L
  have hcomplex :=
    ccmFirstClockXiRationalDivisor_eq_screw_add_volterra hL
  have hIntegral :
      (∫ t : ℝ in (0 : ℝ)..L,
        (((xi : ℝ) : ℂ) * Real.sin (xi * t)) * xiScrewDivisor t) =
        ((xi * ∫ t : ℝ in (0 : ℝ)..L,
          Real.sin (xi * t) * (xiScrewDivisor t).re : ℝ) : ℂ) := by
    calc
      _ = ∫ t : ℝ in (0 : ℝ)..L,
          ((xi * (Real.sin (xi * t) * (xiScrewDivisor t).re) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        have hscrew :
            xiScrewDivisor t = ((xiScrewDivisor t).re : ℂ) := by
          apply Complex.ext
          · simp
          · simp [xiScrewDivisor_im_eq_zero]
        change
          ((xi : ℂ) * (Real.sin (xi * t) : ℂ)) * xiScrewDivisor t =
            ((xi * (Real.sin (xi * t) * (xiScrewDivisor t).re) : ℝ) : ℂ)
        rw [hscrew]
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        congr 1
        simp
        ring
      _ = ((∫ t : ℝ in (0 : ℝ)..L,
          xi * (Real.sin (xi * t) * (xiScrewDivisor t).re) : ℝ) : ℂ) := by
        exact integral_ofReal
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  rw [show (2 * Real.pi / L : ℝ) = xi by rfl] at hcomplex ⊢
  rw [hIntegral] at hcomplex
  have hre := congrArg Complex.re hcomplex
  simpa only [Complex.add_re, Complex.ofReal_re] using hre

/-- **Published first-clock identity.**  The literal CCM source coefficient is exactly the
normalized multiplicity-exact Xi rational divisor. -/
theorem ccmPublishedSourceSineCoefficient_firstClock_eq_xiRationalDivisor
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) =
      (2 / L) * (ccmFirstClockXiRationalDivisor L).re := by
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  let xi : ℝ := 2 * Real.pi / L
  have hperiod : xi * L = 2 * Real.pi := by
    dsimp only [xi]
    field_simp
  have hsource :=
    ccmFirstClockWeightedScrew_re_eq_pi_mul_publishedSource hLpos hperiod
  have hvolterra :=
    ccmFirstClockXiRationalDivisor_re_eq_screw_re_add_volterra hL
  dsimp only [xi] at hsource
  have hweighted :
      (2 * Real.pi / L) * (ccmFirstClockXiRationalDivisor L).re =
        Real.pi *
          ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) := by
    rw [hvolterra]
    linear_combination hsource
  field_simp [hLpos.ne', Real.pi_ne_zero] at hweighted
  rw [show (2 / L) * (ccmFirstClockXiRationalDivisor L).re =
      (2 * (ccmFirstClockXiRationalDivisor L).re) / L by ring]
  rw [eq_div_iff hLpos.ne']
  linear_combination -hweighted

/-- **Literal CCM first-clock RH sign law.**  Under RH, the first physical sine coordinate of
the published CCM source is nonnegative at every aperture `L ≥ π/2`. -/
theorem ccmPublishedSourceSineCoefficient_firstClock_nonneg_of_rh
    (hRH : RiemannHypothesis)
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    0 ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) := by
  rw [ccmPublishedSourceSineCoefficient_firstClock_eq_xiRationalDivisor hL]
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  exact mul_nonneg (by positivity)
    (ccmFirstClockXiRationalDivisor_re_nonneg_of_rh hRH hL)

end

end RHTower
