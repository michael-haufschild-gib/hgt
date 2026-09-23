import GaloisForLFunctions.RHTower.EisensteinLineModeSizeBounds
import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative

/-!
# The nonconstant part of `E*(·, 1/2 + it)`: Parseval on a period

The nonconstant part `T(x, Y) = 2 Σ_N (a_N e(-(N+1)x) + b_N e((N+1)x))` of the completed
Eisenstein series on the line is an absolutely convergent Fourier series in `x` whose
coefficients all have modulus equal to the mode size of the previous module.  This module records
the three period-averaged facts the mean-square bound of the Eisenstein source needs:

* `T(·, Y)` has zero mean over a period;
* Parseval: `∫_0^(1 : ℕ) ‖T(x, Y)‖² dx = 8 Σ_N mode_N(Y)²`;
* `‖T(x, Y)‖ ≤ 4 Σ_N mode_N(Y)` pointwise;

together with joint continuity of `T` above height `1/2`, which makes the source a measurable
function on the fundamental domain.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Modes as coefficient times phase -/

/-- The coefficient of the `N`-th mode at height `Y`: `σ_{2it}(N+1) √Y K_{2π(N+1)Y}(it)`. -/
def eisensteinLineModeCoeff (t Y : ℝ) (N : ℕ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient ((t : ℂ) * I) ⟨N + 1, by omega⟩ *
    (Real.sqrt Y : ℂ) * modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) ((t : ℂ) * I)

theorem norm_eisensteinLineModeCoeff (t Y : ℝ) (N : ℕ) :
    ‖eisensteinLineModeCoeff t Y N‖ = eisensteinLineModeSize t Y N := by
  unfold eisensteinLineModeCoeff eisensteinLineModeSize
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg Y)]

theorem eisensteinLineTailTerm_eq_coeff_mul_phase (t : ℝ) (negative : Bool) (x Y : ℝ) (N : ℕ) :
    eisensteinLineTailTerm t negative x Y N =
      eisensteinLineModeCoeff t Y N * d4BMCompletedEisensteinFourierPhase negative N x := by
  unfold eisensteinLineTailTerm eisensteinLineModeCoeff
  simp only [pow_zero, mul_one]
  ring

/-- The phase as a complex exponential `exp(c x)` with `c = ±2π(N+1) i`. -/
def eisensteinPhaseRate (negative : Bool) (N : ℕ) : ℂ :=
  ((d4BMFourierSign negative * (2 * Real.pi * ((N : ℝ) + 1)) : ℝ) : ℂ) * I

theorem eisensteinPhaseRate_ne_zero (negative : Bool) (N : ℕ) : eisensteinPhaseRate negative N ≠ 0 := by
  unfold eisensteinPhaseRate
  refine mul_ne_zero ?_ I_ne_zero
  rw [Complex.ofReal_ne_zero]
  have hpos : (0 : ℝ) < 2 * Real.pi * ((N : ℝ) + 1) := by positivity
  cases negative
  · simp only [d4BMFourierSign, Bool.false_eq_true, ↓reduceIte, one_mul]
    exact hpos.ne'
  · simp only [d4BMFourierSign, ↓reduceIte]
    intro h; linarith

theorem fourierPhase_eq_exp_rate (negative : Bool) (N : ℕ) (x : ℝ) :
    d4BMCompletedEisensteinFourierPhase negative N x =
      Complex.exp (eisensteinPhaseRate negative N * (x : ℂ)) := by
  unfold d4BMCompletedEisensteinFourierPhase eisensteinPhaseRate
  congr 1
  push_cast
  ring

/-- `exp(c) = 1` for the phase rate: it is `2πi` times the integer `±(N+1)`. -/
theorem exp_eisensteinPhaseRate (negative : Bool) (N : ℕ) :
    Complex.exp (eisensteinPhaseRate negative N) = 1 := by
  unfold eisensteinPhaseRate d4BMFourierSign
  cases negative
  · have := Complex.exp_int_mul_two_pi_mul_I ((N : ℤ) + 1)
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at *
    rw [← this]; congr 1; push_cast; ring
  · have := Complex.exp_int_mul_two_pi_mul_I (-((N : ℤ) + 1))
    simp only [↓reduceIte] at *
    rw [← this]; congr 1; push_cast; ring

/-- The mean of a phase over a period vanishes. -/
theorem intervalIntegral_fourierPhase (negative : Bool) (N : ℕ) :
    ∫ x in (0 : ℝ)..1, d4BMCompletedEisensteinFourierPhase negative N x = 0 := by
  simp_rw [fourierPhase_eq_exp_rate]
  rw [integral_exp_mul_complex (eisensteinPhaseRate_ne_zero negative N)]
  simp [exp_eisensteinPhaseRate]

/-- Twisted phases: `∫_0^(1 : ℕ) exp(2πi m x) · phase = [m + rate = 0]`.  Stated with the product rate
`c + c'`. -/
theorem intervalIntegral_exp_mul_fourierPhase (c : ℂ) (negative : Bool) (N : ℕ)
    (hc : Complex.exp c = 1) :
    ∫ x in (0 : ℝ)..1, Complex.exp (c * (x : ℂ)) * d4BMCompletedEisensteinFourierPhase negative N x =
      if c + eisensteinPhaseRate negative N = 0 then 1 else 0 := by
  simp_rw [fourierPhase_eq_exp_rate, ← Complex.exp_add, ← add_mul]
  split_ifs with h
  · rw [h]; simp
  · rw [integral_exp_mul_complex h]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      Complex.exp_add, hc, exp_eisensteinPhaseRate]
    simp

/-! ## The tails as functions of `x` -/

/-- The signed tail at height `Y`, as a function of the horizontal coordinate. -/
def eisensteinLineTail (t : ℝ) (negative : Bool) (Y x : ℝ) : ℂ :=
  ∑' N : ℕ, eisensteinLineTailTerm t negative x Y N

theorem eisensteinLineTail_eq (t : ℝ) (negative : Bool) (Y x : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail ((t : ℂ) * I) ((t : ℂ) * I) negative x 0 0 Y =
      eisensteinLineTail t negative Y x :=
  signedSqrtWhittakerTail_eq_tsum t negative x Y

/-- `T(x, Y) = 2 (tail₊ + tail₋)`. -/
theorem cuspTailPart_eq_tails (t x Y : ℝ) :
    d4BMCompletedEisensteinCuspTailPart .scalar ((t : ℂ) * I) x Y =
      2 * (eisensteinLineTail t false Y x + eisensteinLineTail t true Y x) := by
  unfold d4BMCompletedEisensteinCuspTailPart d4BMCompletedEisensteinFullSignedZeroWord
  rw [eisensteinLineTail_eq, eisensteinLineTail_eq]

theorem summable_norm_eisensteinLineTailTerm' (t : ℝ) (negative : Bool) (x : ℝ) {Y : ℝ}
    (hY : 1 / 2 ≤ Y) :
    Summable (fun N => ‖eisensteinLineTailTerm t negative x Y N‖) := by
  simp_rw [norm_eisensteinLineTailTerm_eq_modeSize]
  exact summable_eisensteinLineModeSize hY

theorem summable_eisensteinLineTailTerm (t : ℝ) (negative : Bool) (x : ℝ) {Y : ℝ}
    (hY : 1 / 2 ≤ Y) :
    Summable (fun N => eisensteinLineTailTerm t negative x Y N) :=
  (summable_norm_eisensteinLineTailTerm' t negative x hY).of_norm

/-- The pointwise bound by the `ℓ¹` sum of mode sizes. -/
theorem norm_eisensteinLineTail_le (t : ℝ) (negative : Bool) {Y : ℝ} (hY : 1 / 2 ≤ Y) (x : ℝ) :
    ‖eisensteinLineTail t negative Y x‖ ≤ ∑' N : ℕ, eisensteinLineModeSize t Y N := by
  unfold eisensteinLineTail
  refine (norm_tsum_le_tsum_norm (summable_norm_eisensteinLineTailTerm' t negative x hY)).trans ?_
  simp_rw [norm_eisensteinLineTailTerm_eq_modeSize]
  exact le_rfl

theorem norm_cuspTailPart_le (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) (x : ℝ) :
    ‖d4BMCompletedEisensteinCuspTailPart .scalar ((t : ℂ) * I) x Y‖ ≤
      4 * ∑' N : ℕ, eisensteinLineModeSize t Y N := by
  rw [cuspTailPart_eq_tails, norm_mul, Complex.norm_ofNat]
  have h1 := norm_eisensteinLineTail_le t false hY x
  have h2 := norm_eisensteinLineTail_le t true hY x
  have h := norm_add_le (eisensteinLineTail t false Y x) (eisensteinLineTail t true Y x)
  linarith

/-! ## Continuity in `x` and integrability on a period -/

theorem continuous_eisensteinLineTailTerm_x (t : ℝ) (negative : Bool) (Y : ℝ) (N : ℕ) :
    Continuous (fun x : ℝ => eisensteinLineTailTerm t negative x Y N) := by
  simp_rw [eisensteinLineTailTerm_eq_coeff_mul_phase, fourierPhase_eq_exp_rate]
  fun_prop

theorem continuous_eisensteinLineTail_x (t : ℝ) (negative : Bool) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    Continuous (eisensteinLineTail t negative Y) := by
  unfold eisensteinLineTail
  refine continuous_tsum (fun N => continuous_eisensteinLineTailTerm_x t negative Y N)
    (summable_eisensteinLineModeSize (t := t) hY) fun N x => ?_
  rw [norm_eisensteinLineTailTerm_eq_modeSize]

theorem continuous_cuspTailPart_x (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    Continuous (fun x => d4BMCompletedEisensteinCuspTailPart .scalar ((t : ℂ) * I) x Y) := by
  simp_rw [cuspTailPart_eq_tails]
  have h1 := continuous_eisensteinLineTail_x t false hY
  have h2 := continuous_eisensteinLineTail_x t true hY
  fun_prop

/-- The integral over a period of a mode is the coefficient times the phase integral. -/
theorem setIntegral_Ioc_eisensteinLineTailTerm (t : ℝ) (negative : Bool) (Y : ℝ) (N : ℕ) :
    ∫ x in Ioc (0 : ℝ) 1, eisensteinLineTailTerm t negative x Y N = 0 := by
  rw [← integral_of_le zero_le_one]
  simp_rw [eisensteinLineTailTerm_eq_coeff_mul_phase]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_fourierPhase, mul_zero]

/-- Interchange of sum and period integral for a twisted tail. -/
theorem setIntegral_Ioc_tsum_mul_eisensteinLineTailTerm (t : ℝ) (negative : Bool) {Y : ℝ}
    (hY : 1 / 2 ≤ Y) {g : ℝ → ℂ} (hg : Continuous g) (hg1 : ∀ x, ‖g x‖ ≤ 1) :
    ∫ x in Ioc (0 : ℝ) 1, g x * ∑' N : ℕ, eisensteinLineTailTerm t negative x Y N =
      ∑' N : ℕ, ∫ x in Ioc (0 : ℝ) 1, g x * eisensteinLineTailTerm t negative x Y N := by
  have hint : ∀ N : ℕ, Integrable (fun x => g x * eisensteinLineTailTerm t negative x Y N)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun N => (hg.mul (continuous_eisensteinLineTailTerm_x t negative Y N)).integrableOn_Ioc
  have hsum : Summable (fun N : ℕ =>
      ∫ x in Ioc (0 : ℝ) 1, ‖g x * eisensteinLineTailTerm t negative x Y N‖) := by
    refine Summable.of_nonneg_of_le (fun N => integral_nonneg fun x => norm_nonneg _)
      (fun N => ?_) (summable_eisensteinLineModeSize (t := t) hY)
    calc ∫ x in Ioc (0 : ℝ) 1, ‖g x * eisensteinLineTailTerm t negative x Y N‖
        ≤ ∫ x in Ioc (0 : ℝ) 1, eisensteinLineModeSize t Y N := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun x _ => ?_
          · exact (hint N).norm
          · exact integrableOn_const (by simp)
          · rw [norm_mul, norm_eisensteinLineTailTerm_eq_modeSize]
            have := hg1 x
            have := eisensteinLineModeSize_nonneg t Y N
            nlinarith
      _ = eisensteinLineModeSize t Y N := by simp
  have h := integral_tsum_of_summable_integral_norm hint hsum
  calc ∫ x in Ioc (0 : ℝ) 1, g x * ∑' N : ℕ, eisensteinLineTailTerm t negative x Y N
      = ∫ x in Ioc (0 : ℝ) 1, ∑' N : ℕ, g x * eisensteinLineTailTerm t negative x Y N :=
        setIntegral_congr_fun measurableSet_Ioc fun x _ => (tsum_mul_left).symm
    _ = _ := h.symm

/-- **Zero mean of the tails over a period.** -/
theorem setIntegral_Ioc_eisensteinLineTail (t : ℝ) (negative : Bool) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ∫ x in Ioc (0 : ℝ) 1, eisensteinLineTail t negative Y x = 0 := by
  unfold eisensteinLineTail
  have h := setIntegral_Ioc_tsum_mul_eisensteinLineTailTerm t negative hY (g := fun _ => 1)
    continuous_const (fun _ => by simp)
  simp only [one_mul] at h
  rw [h]
  simp_rw [setIntegral_Ioc_eisensteinLineTailTerm]
  exact tsum_zero

theorem setIntegral_Ioc_cuspTailPart (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ∫ x in Ioc (0 : ℝ) 1, d4BMCompletedEisensteinCuspTailPart .scalar ((t : ℂ) * I) x Y = 0 := by
  simp_rw [cuspTailPart_eq_tails]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add,
    setIntegral_Ioc_eisensteinLineTail t false hY,
    setIntegral_Ioc_eisensteinLineTail t true hY]
  · simp
  · exact (continuous_eisensteinLineTail_x t false hY).integrableOn_Ioc
  · exact (continuous_eisensteinLineTail_x t true hY).integrableOn_Ioc

/-! ## Fourier coefficients of the nonconstant part -/

/-- The nonconstant part at height `Y`, as a function of `x`. -/
def eisensteinLineTailPart (t Y x : ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspTailPart .scalar ((t : ℂ) * I) x Y

theorem eisensteinLineTailPart_eq (t Y x : ℝ) :
    eisensteinLineTailPart t Y x =
      2 * (eisensteinLineTail t false Y x + eisensteinLineTail t true Y x) :=
  cuspTailPart_eq_tails t x Y

/-- `fourier (-n)` on `AddCircle 1` at a real point is `exp(-2πi n x)`. -/
theorem fourier_neg_coe_eq (n : ℤ) (x : ℝ) :
    (fourier (-n) : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) =
      Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- The twisted period integral of a mode: `[c + rate = 0]` times the coefficient. -/
theorem setIntegral_Ioc_exp_mul_eisensteinLineTailTerm (n : ℤ) (t : ℝ) (negative : Bool) (Y : ℝ)
    (N : ℕ) :
    ∫ x in Ioc (0 : ℝ) 1, Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) *
        eisensteinLineTailTerm t negative x Y N =
      eisensteinLineModeCoeff t Y N *
        (if -(n : ℂ) * (2 * Real.pi * I) + eisensteinPhaseRate negative N = 0 then 1 else 0) := by
  rw [← integral_of_le zero_le_one]
  simp_rw [eisensteinLineTailTerm_eq_coeff_mul_phase]
  have hc : Complex.exp (-(n : ℂ) * (2 * Real.pi * I)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-n)
    rw [← this]; congr 1; push_cast; ring
  rw [show (fun x : ℝ => Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) *
      (eisensteinLineModeCoeff t Y N * d4BMCompletedEisensteinFourierPhase negative N x)) =
      fun x : ℝ => eisensteinLineModeCoeff t Y N *
        (Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) *
          d4BMCompletedEisensteinFourierPhase negative N x) by funext x; ring]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_exp_mul_fourierPhase _ negative N hc]

/-- The selector `-(n)(2πi) + rate(neg, N) = 0` holds iff `n = ±(N+1)` with the sign of `neg`. -/
theorem rate_selector_false (n : ℤ) (N : ℕ) :
    (-(n : ℂ) * (2 * Real.pi * I) + eisensteinPhaseRate false N = 0) ↔ n = (N : ℤ) + 1 := by
  unfold eisensteinPhaseRate d4BMFourierSign
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  have hπ : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  constructor
  · intro h
    have h' : ((((N : ℝ) + 1 : ℝ) : ℂ) - (n : ℂ)) * (2 * (Real.pi : ℂ) * I) = 0 := by
      rw [← h]; push_cast; ring
    rcases mul_eq_zero.mp h' with h'' | h''
    · have h3 : ((n : ℝ) : ℂ) = (((N : ℝ) + 1 : ℝ) : ℂ) := by
        push_cast at h'' ⊢; linear_combination -h''
      have h4 : (n : ℝ) = (N : ℝ) + 1 := by exact_mod_cast h3
      exact_mod_cast h4
    · exact absurd h'' hπ
  · intro h
    subst h
    push_cast
    ring

theorem rate_selector_true (n : ℤ) (N : ℕ) :
    (-(n : ℂ) * (2 * Real.pi * I) + eisensteinPhaseRate true N = 0) ↔ n = -((N : ℤ) + 1) := by
  unfold eisensteinPhaseRate d4BMFourierSign
  simp only [↓reduceIte]
  have hπ : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  constructor
  · intro h
    have h' : (-(((N : ℝ) + 1 : ℝ) : ℂ) - (n : ℂ)) * (2 * (Real.pi : ℂ) * I) = 0 := by
      rw [← h]; push_cast; ring
    rcases mul_eq_zero.mp h' with h'' | h''
    · have h3 : ((n : ℝ) : ℂ) = -(((N : ℝ) + 1 : ℝ) : ℂ) := by
        push_cast at h'' ⊢; linear_combination -h''
      have h4 : (n : ℝ) = -((N : ℝ) + 1) := by exact_mod_cast h3
      exact_mod_cast h4
    · exact absurd h'' hπ
  · intro h
    subst h
    push_cast
    ring

/-- The `n`-th Fourier coefficient of a signed tail on the period. -/
theorem setIntegral_Ioc_exp_mul_eisensteinLineTail (n : ℤ) (t : ℝ) (negative : Bool) {Y : ℝ}
    (hY : 1 / 2 ≤ Y) :
    ∫ x in Ioc (0 : ℝ) 1, Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) *
        eisensteinLineTail t negative Y x =
      ∑' N : ℕ, eisensteinLineModeCoeff t Y N *
        (if -(n : ℂ) * (2 * Real.pi * I) + eisensteinPhaseRate negative N = 0 then 1 else 0) := by
  unfold eisensteinLineTail
  have hg : Continuous (fun x : ℝ => Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ))) := by
    fun_prop
  have hg1 : ∀ x : ℝ, ‖Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ))‖ ≤ 1 := by
    intro x
    rw [show (-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ) = ((-(n : ℝ) * (2 * Real.pi) * x : ℝ) : ℂ) * I
      by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [setIntegral_Ioc_tsum_mul_eisensteinLineTailTerm t negative hY hg hg1]
  simp_rw [setIntegral_Ioc_exp_mul_eisensteinLineTailTerm]

/-- The Fourier coefficients of the nonconstant part on the period `[0, 1]`. -/
theorem fourierCoeffOn_eisensteinLineTailPart (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) (n : ℤ) :
    fourierCoeffOn (zero_lt_one' ℝ) (eisensteinLineTailPart t Y) n =
      2 * ((∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if n = (N : ℤ) + 1 then 1 else 0)) +
        ∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if n = -((N : ℤ) + 1) then 1 else 0)) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul, smul_eq_mul]
  rw [integral_of_le zero_le_one]
  have hfun : ∀ x : ℝ, (fourier (-n) : AddCircle (1 - 0 : ℝ) → ℂ) (x : AddCircle (1 - 0 : ℝ)) *
      eisensteinLineTailPart t Y x =
      2 * (Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) * eisensteinLineTail t false Y x +
        Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) * eisensteinLineTail t true Y x) := by
    intro x
    rw [eisensteinLineTailPart_eq, fourier_coe_apply]
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * I * (((-n : ℤ) : ℤ) : ℂ) * (x : ℂ) / ((1 - 0 : ℝ) : ℂ)) =
        Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ)) := by
      congr 1; push_cast; ring
    rw [hexp]; ring
  simp_rw [hfun]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add]
  · rw [setIntegral_Ioc_exp_mul_eisensteinLineTail n t false hY,
      setIntegral_Ioc_exp_mul_eisensteinLineTail n t true hY]
    simp_rw [rate_selector_false, rate_selector_true]
  · exact ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ))).mul
        (continuous_eisensteinLineTail_x t false hY)).integrableOn_Ioc
  · exact ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp ((-(n : ℂ) * (2 * Real.pi * I)) * (x : ℂ))).mul
        (continuous_eisensteinLineTail_x t true hY)).integrableOn_Ioc

/-- Selecting a single mode from the coefficient series. -/
theorem tsum_coeff_select_pos (t Y : ℝ) (M : ℕ) :
    ∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if ((M : ℤ) + 1) = (N : ℤ) + 1 then 1 else 0) =
      eisensteinLineModeCoeff t Y M := by
  rw [tsum_eq_single M]
  · rw [if_pos rfl, mul_one]
  · intro N hN
    have : ((M : ℤ) + 1) ≠ (N : ℤ) + 1 := by omega
    rw [if_neg this, mul_zero]

theorem tsum_coeff_select_neg (t Y : ℝ) (M : ℕ) :
    ∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if -((M : ℤ) + 1) = -((N : ℤ) + 1) then 1 else 0) =
      eisensteinLineModeCoeff t Y M := by
  rw [tsum_eq_single M]
  · rw [if_pos rfl, mul_one]
  · intro N hN
    have : -((M : ℤ) + 1) ≠ -((N : ℤ) + 1) := by omega
    rw [if_neg this, mul_zero]

theorem tsum_coeff_select_pos_of_neg (t Y : ℝ) (M : ℕ) :
    ∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if -((M : ℤ) + 1) = (N : ℤ) + 1 then 1 else 0) = 0 := by
  have h : ∀ N : ℕ, (if -((M : ℤ) + 1) = (N : ℤ) + 1 then (1 : ℂ) else 0) = 0 := fun N => by
    have : -((M : ℤ) + 1) ≠ (N : ℤ) + 1 := by omega
    rw [if_neg this]
  simp_rw [h, mul_zero, tsum_zero]

theorem tsum_coeff_select_neg_of_pos (t Y : ℝ) (M : ℕ) :
    ∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if ((M : ℤ) + 1) = -((N : ℤ) + 1) then 1 else 0) = 0 := by
  have h : ∀ N : ℕ, (if ((M : ℤ) + 1) = -((N : ℤ) + 1) then (1 : ℂ) else 0) = 0 := fun N => by
    have : ((M : ℤ) + 1) ≠ -((N : ℤ) + 1) := by omega
    rw [if_neg this]
  simp_rw [h, mul_zero, tsum_zero]

theorem tsum_coeff_select_zero_pos (t Y : ℝ) :
    ∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if (0 : ℤ) = (N : ℤ) + 1 then 1 else 0) = 0 := by
  have h : ∀ N : ℕ, (if (0 : ℤ) = (N : ℤ) + 1 then (1 : ℂ) else 0) = 0 := fun N => by
    have : (0 : ℤ) ≠ (N : ℤ) + 1 := by omega
    rw [if_neg this]
  simp_rw [h, mul_zero, tsum_zero]

theorem tsum_coeff_select_zero_neg (t Y : ℝ) :
    ∑' N : ℕ, eisensteinLineModeCoeff t Y N * (if (0 : ℤ) = -((N : ℤ) + 1) then 1 else 0) = 0 := by
  have h : ∀ N : ℕ, (if (0 : ℤ) = -((N : ℤ) + 1) then (1 : ℂ) else 0) = 0 := fun N => by
    have : (0 : ℤ) ≠ -((N : ℤ) + 1) := by omega
    rw [if_neg this]
  simp_rw [h, mul_zero, tsum_zero]

theorem fourierCoeffOn_eisensteinLineTailPart_pos (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) (M : ℕ) :
    fourierCoeffOn (zero_lt_one' ℝ) (eisensteinLineTailPart t Y) ((M : ℤ) + 1) =
      2 * eisensteinLineModeCoeff t Y M := by
  rw [fourierCoeffOn_eisensteinLineTailPart t hY, tsum_coeff_select_pos, tsum_coeff_select_neg_of_pos,
    add_zero]

theorem fourierCoeffOn_eisensteinLineTailPart_neg (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) (M : ℕ) :
    fourierCoeffOn (zero_lt_one' ℝ) (eisensteinLineTailPart t Y) (-((M : ℤ) + 1)) =
      2 * eisensteinLineModeCoeff t Y M := by
  rw [fourierCoeffOn_eisensteinLineTailPart t hY, tsum_coeff_select_pos_of_neg, tsum_coeff_select_neg,
    zero_add]

theorem fourierCoeffOn_eisensteinLineTailPart_zero (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    fourierCoeffOn (zero_lt_one' ℝ) (eisensteinLineTailPart t Y) 0 = 0 := by
  rw [fourierCoeffOn_eisensteinLineTailPart t hY, tsum_coeff_select_zero_pos,
    tsum_coeff_select_zero_neg]
  simp

/-- **Parseval for the nonconstant part on a period.** -/
theorem intervalIntegral_normSq_eisensteinLineTailPart (t : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t Y x‖ ^ (2 : ℕ) =
      8 * ∑' N : ℕ, eisensteinLineModeSize t Y N ^ (2 : ℕ) := by
  have hcont : Continuous (eisensteinLineTailPart t Y) := continuous_cuspTailPart_x t hY
  have hL2 : MemLp (eisensteinLineTailPart t Y) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hcont.aestronglyMeasurable (4 * ∑' N, eisensteinLineModeSize t Y N)
      (Filter.Eventually.of_forall fun x => norm_cuspTailPart_le t hY x)
  have hP := tsum_sq_fourierCoeffOn (zero_lt_one' ℝ) hL2
  simp only [sub_zero, inv_one, one_smul] at hP
  rw [← hP]
  have hsq := summable_eisensteinLineModeSize_sq (t := t) hY
  have hpos : ∀ n : ℕ, ‖fourierCoeffOn (zero_lt_one' ℝ) (eisensteinLineTailPart t Y) ((n : ℤ) + 1)‖ ^ (2 : ℕ) =
      4 * eisensteinLineModeSize t Y n ^ (2 : ℕ) := by
    intro n
    rw [fourierCoeffOn_eisensteinLineTailPart_pos t hY, norm_mul, Complex.norm_ofNat,
      norm_eisensteinLineModeCoeff]
    ring
  have hneg : ∀ n : ℕ, ‖fourierCoeffOn (zero_lt_one' ℝ) (eisensteinLineTailPart t Y) (-((n : ℤ) + 1))‖ ^ (2 : ℕ) =
      4 * eisensteinLineModeSize t Y n ^ (2 : ℕ) := by
    intro n
    rw [fourierCoeffOn_eisensteinLineTailPart_neg t hY, norm_mul, Complex.norm_ofNat,
      norm_eisensteinLineModeCoeff]
    ring
  rw [tsum_of_add_one_of_neg_add_one]
  · simp_rw [hpos, hneg]
    rw [fourierCoeffOn_eisensteinLineTailPart_zero t hY, tsum_mul_left]
    simp
    ring
  · simp_rw [hpos]; exact hsq.mul_left 4
  · simp_rw [hneg]; exact hsq.mul_left 4

/-! ## Joint continuity above height one half -/

/-- Continuity of `Y ↦ K_{cY}(ν)` on `Y > 0`. -/
theorem continuousOn_modifiedBesselKOrder_scaled {c : ℝ} (hc : 0 < c) (ν : ℂ) :
    ContinuousOn (fun Y : ℝ => modifiedBesselKOrder (c * Y) ν) (Ioi 0) := by
  intro Y hY
  have hs : 0 < c * Y := mul_pos hc hY
  have h := (d4BM_hasDerivAt_modifiedBesselKOrder_argument hs ν).continuousAt
  have h2 : ContinuousAt (fun Y : ℝ => c * Y) Y := by fun_prop
  exact (h.comp h2).continuousWithinAt

theorem continuousOn_eisensteinLineTailTerm_pair (t : ℝ) (negative : Bool) (N : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => eisensteinLineTailTerm t negative p.1 p.2 N)
      {p : ℝ × ℝ | 0 < p.2} := by
  simp_rw [eisensteinLineTailTerm_eq_coeff_mul_phase, fourierPhase_eq_exp_rate]
  unfold eisensteinLineModeCoeff
  have hK : ContinuousOn (fun p : ℝ × ℝ =>
      modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * p.2) ((t : ℂ) * I))
      {p : ℝ × ℝ | 0 < p.2} := by
    have := continuousOn_modifiedBesselKOrder_scaled (c := 2 * Real.pi * ((N : ℝ) + 1))
      (by positivity) ((t : ℂ) * I)
    exact this.comp continuous_snd.continuousOn (fun p hp => hp)
  have hs : Continuous (fun p : ℝ × ℝ => ((Real.sqrt p.2 : ℝ) : ℂ)) := by fun_prop
  have hph : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (eisensteinPhaseRate negative N * (p.1 : ℂ))) := by fun_prop
  exact ((continuousOn_const.mul hs.continuousOn).mul hK).mul hph.continuousOn

theorem continuousOn_eisensteinLineTail_pair (t : ℝ) (negative : Bool) :
    ContinuousOn (fun p : ℝ × ℝ => eisensteinLineTail t negative p.2 p.1)
      {p : ℝ × ℝ | 1 / 2 < p.2} := by
  intro p₀ hp₀
  simp only [mem_setOf_eq] at hp₀
  set Y₁ : ℝ := p₀.2 + 1 with hY₁
  set S : Set (ℝ × ℝ) := {p | 1 / 2 ≤ p.2 ∧ p.2 ≤ Y₁} with hSdef
  have hY₁0 : 0 ≤ Y₁ := by linarith
  have hS : ContinuousOn (fun p : ℝ × ℝ => eisensteinLineTail t negative p.2 p.1) S := by
    unfold eisensteinLineTail
    have hmaj := (summable_succ_mul_exp_neg_and_tsum_le (a := Real.pi) Real.pi_pos).1
    refine continuousOn_tsum (fun N => (continuousOn_eisensteinLineTailTerm_pair t negative N).mono
      (fun p hp => by rw [hSdef] at hp; simp only [mem_setOf_eq] at hp ⊢; linarith [hp.1]))
      (u := fun N : ℕ => Real.sqrt Y₁ * Real.exp 1 *
        (((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1)))))
      (hmaj.mul_left _) fun N p hp => ?_
    rw [hSdef] at hp
    simp only [mem_setOf_eq] at hp
    rw [norm_eisensteinLineTailTerm_eq_modeSize]
    refine (eisensteinLineModeSize_le_exp hp.1 N).trans ?_
    have hd : ((N + 1 : ℕ).divisors.card : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast Nat.card_divisors_le_self (N + 1)
    have hsq : Real.sqrt p.2 ≤ Real.sqrt Y₁ := Real.sqrt_le_sqrt hp.2
    have hexp : Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * p.2)) ≤
        Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
      apply Real.exp_le_exp.mpr
      have hp' : (0 : ℝ) ≤ Real.pi * ((N : ℝ) + 1) := by positivity
      have h2Y : (1 : ℝ) ≤ 2 * p.2 := by linarith [hp.1]
      nlinarith [mul_le_mul_of_nonneg_left h2Y hp']
    calc ((N + 1 : ℕ).divisors.card : ℝ) * Real.sqrt p.2 *
          (Real.exp 1 * Real.exp (-(2 * Real.pi * ((N : ℝ) + 1) * p.2)))
        ≤ ((N : ℝ) + 1) * Real.sqrt Y₁ * (Real.exp 1 * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
          gcongr
      _ = Real.sqrt Y₁ * Real.exp 1 * (((N : ℝ) + 1) * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) := by
          ring
  have hmem : S ∈ 𝓝 p₀ := by
    refine mem_nhds_iff.mpr ⟨{p : ℝ × ℝ | 1 / 2 < p.2 ∧ p.2 < Y₁}, ?_, ?_, ?_⟩
    · intro p hp; simp only [mem_setOf_eq, hSdef] at hp ⊢; exact ⟨hp.1.le, hp.2.le⟩
    · exact (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
    · simp only [mem_setOf_eq]; exact ⟨hp₀, by linarith⟩
  exact (hS.continuousAt hmem).continuousWithinAt

theorem continuousOn_eisensteinLineTailPart_pair (t : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => eisensteinLineTailPart t p.2 p.1) {p : ℝ × ℝ | 1 / 2 < p.2} := by
  simp_rw [eisensteinLineTailPart_eq]
  have h1 := continuousOn_eisensteinLineTail_pair t false
  have h2 := continuousOn_eisensteinLineTail_pair t true
  exact continuousOn_const.mul (h1.add h2)

end

end RHTower
