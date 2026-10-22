import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveDefectBoundary
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiTargetFlatPencil
import GaloisForLFunctions.RHTower.SlabMassSquareCertificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Suzuki exterior pole tomography

Suzuki's source substitution has two exact features that are easy to lose in a formal Fourier
multiplier heuristic.

First, if `hPlus = g * vPlus` and `hMinus = g * vMinus`, the division-free identity is

`g * ((z-i)vPlus + q(z+i)vMinus) = (z-i)hPlus + q(z+i)hMinus`.

Thus the bracket on the right must use the `h` channels, not the original `v` channels.  Second,
on a finite Neumann interval the symbol of `-d²/dx²` has an exact endpoint flux.  It is not the
bare whole-line multiplier `z²`.

Combining the corrected factorization with the shifted Xi target from
`SuzukiShiftedXiTargetFlatPencil` isolates the exterior channel

`E = R_eta⁻¹ W - I`,

where `W` is a Suzuki characteristic function and `I` is its entire finite-interval part.  At
every Xi zero `z`, if `W z` is nonzero, `E` has an uncancellable simple pole with exact trailing
coefficient

`ord_z(XiC) * W(z) / z²`.

Suzuki's all-angle real-zero theorem makes `W z` nonzero at every nonreal `z`.  Consequently RH is
equivalent to off-real holomorphy of this corrected exterior remainder.  This does not prove that
holomorphy; it identifies the precise source-defined continuation theorem that would prove RH.

All results are exact.  No limit, estimate, zero simplicity, RH assumption, or numerical
computation is used.
-/

open Complex Set MeasureTheory

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-! ## Corrected two-channel factorization -/

/-- Suzuki's two-channel characteristic bracket. -/
def suzukiTwoChannelBracket
    (plus minus : ℂ → ℂ) (q z : ℂ) : ℂ :=
  (z - I) * plus z + q * (z + I) * minus z

/-- Division-free corrected `v`/`h` substitution.  The output bracket necessarily uses the
`h` channels. -/
theorem suzukiTwoChannelBracket_corrected_cross
    {g vPlus vMinus hPlus hMinus : ℂ → ℂ}
    (q z : ℂ)
    (hPlusEq : hPlus z = g z * vPlus z)
    (hMinusEq : hMinus z = g z * vMinus z) :
    g z * suzukiTwoChannelBracket vPlus vMinus q z =
      suzukiTwoChannelBracket hPlus hMinus q z := by
  simp only [suzukiTwoChannelBracket, hPlusEq, hMinusEq]
  ring

/-- Corrected reciprocal factorization away from a zero of the common multiplier. -/
theorem suzukiTwoChannelBracket_corrected_factorization
    {g vPlus vMinus hPlus hMinus : ℂ → ℂ}
    (q z : ℂ)
    (hPlusEq : hPlus z = g z * vPlus z)
    (hMinusEq : hMinus z = g z * vMinus z)
    (hg : g z ≠ 0) :
    suzukiTwoChannelBracket vPlus vMinus q z =
      (g z)⁻¹ * suzukiTwoChannelBracket hPlus hMinus q z := by
  have hcross := suzukiTwoChannelBracket_corrected_cross q z hPlusEq hMinusEq
  calc
    suzukiTwoChannelBracket vPlus vMinus q z =
        (g z)⁻¹ * (g z * suzukiTwoChannelBracket vPlus vMinus q z) := by
          field_simp
    _ = (g z)⁻¹ * suzukiTwoChannelBracket hPlus hMinus q z := by rw [hcross]

/-! ## Exact finite-Neumann boundary flux -/

/-- The oscillatory kernel for the Fourier convention `∫ f(x) exp(i x z) dx`. -/
def suzukiOscillatoryKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * (I * z))

theorem hasDerivAt_suzukiOscillatoryKernel (z : ℂ) (x : ℝ) :
    HasDerivAt (suzukiOscillatoryKernel z)
      ((I * z) * suzukiOscillatoryKernel z x) x := by
  have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * (I * z)) (I * z) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (I * z)
  unfold suzukiOscillatoryKernel
  simpa only [mul_comm] using hlin.cexp

/-- Exact Fourier law for the inverse finite Neumann Laplacian.  The last term is endpoint flux;
dropping it is precisely the invalid whole-line-multiplier substitution. -/
theorem neumannFourierBoundaryLaw
    (f f' f'' : ℝ → ℂ) (a : ℝ) (z : ℂ)
    (hf : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt f' (f'' x) x)
    (hf'i : IntervalIntegrable f' MeasureTheory.volume (-a) a)
    (hf''i : IntervalIntegrable f'' MeasureTheory.volume (-a) a)
    (hplus : f' a = 0) (hminus : f' (-a) = 0) :
    (∫ x in -a..a, (-f'' x) * suzukiOscillatoryKernel z x) =
      z ^ (2 : ℕ) * (∫ x in -a..a, f x * suzukiOscillatoryKernel z x) +
        I * z *
          (f a * suzukiOscillatoryKernel z a -
            f (-a) * suzukiOscillatoryKernel z (-a)) := by
  let K : ℝ → ℂ := suzukiOscillatoryKernel z
  let K' : ℝ → ℂ := fun x => (I * z) * K x
  have hK : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt K (K' x) x := by
    intro x hx
    exact hasDerivAt_suzukiOscillatoryKernel z x
  have hKc : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_suzukiOscillatoryKernel z x).continuousAt
  have hK'c : Continuous K' := by
    fun_prop
  have hK'i : IntervalIntegrable K' MeasureTheory.volume (-a) a :=
    hK'c.intervalIntegrable _ _
  have hfirst := intervalIntegral.integral_deriv_mul_eq_sub hf' hK hf''i hK'i
  have hsecond := intervalIntegral.integral_deriv_mul_eq_sub hf hK hf'i hK'i
  have hfppK : IntervalIntegrable (fun x => f'' x * K x) MeasureTheory.volume (-a) a :=
    hf''i.mul_continuousOn hKc.continuousOn
  have hfpKp : IntervalIntegrable (fun x => f' x * K' x) MeasureTheory.volume (-a) a :=
    hK'i.continuousOn_mul (fun x hx => (hf' x hx).continuousAt.continuousWithinAt)
  have hfpK : IntervalIntegrable (fun x => f' x * K x) MeasureTheory.volume (-a) a :=
    hf'i.mul_continuousOn hKc.continuousOn
  have hfKp : IntervalIntegrable (fun x => f x * K' x) MeasureTheory.volume (-a) a :=
    hK'i.continuousOn_mul (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  rw [intervalIntegral.integral_add hfppK hfpKp, hplus, hminus] at hfirst
  simp only [zero_mul, sub_self] at hfirst
  rw [intervalIntegral.integral_add hfpK hfKp] at hsecond
  have hfpKp_const :
      (∫ x in -a..a, f' x * K' x) =
        (I * z) * (∫ x in -a..a, f' x * K x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [K']
    ring
  have hfKp_const :
      (∫ x in -a..a, f x * K' x) =
        (I * z) * (∫ x in -a..a, f x * K x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [K']
    ring
  have hneg :
      (∫ x in -a..a, (-f'' x) * K x) =
        (I * z) * (∫ x in -a..a, f' x * K x) := by
    rw [show (fun x => (-f'' x) * K x) = fun x => -(f'' x * K x) by
      funext x
      ring, intervalIntegral.integral_neg, ← hfpKp_const]
    exact neg_eq_of_add_eq_zero_right hfirst
  rw [show suzukiOscillatoryKernel z = K by rfl, hneg, ← hsecond, hfKp_const]
  simp only [K]
  have hIzsq : (I * z) * (I * z) = -(z ^ (2 : ℕ)) := by
    rw [mul_mul_mul_comm, I_mul_I]
    ring
  let A : ℂ := ∫ x in -a..a, f' x * suzukiOscillatoryKernel z x
  let B : ℂ := ∫ x in -a..a, f x * suzukiOscillatoryKernel z x
  change I * z * A = z ^ (2 : ℕ) * B + I * z * (A + I * z * B)
  have hzero : z ^ (2 : ℕ) * B + (I * z) * (I * z) * B = 0 := by
    rw [hIzsq]
    ring
  calc
    I * z * A = I * z * A +
        (z ^ (2 : ℕ) * B + (I * z) * (I * z) * B) := by rw [hzero, add_zero]
    _ = z ^ (2 : ℕ) * B + I * z * (A + I * z * B) := by ring

/-! ## Exact differential elimination of the Neumann clock -/

/-- The two-dimensional trigonometric core of every finite-Neumann endpoint flux. -/
def suzukiNeumannBoundaryClockCore (a A B z : ℂ) : ℂ :=
  A * Complex.cos (a * z) + B * Complex.sin (a * z)

/-- Every finite-Neumann endpoint flux is a member of this two-dimensional clock module. -/
def suzukiNeumannBoundaryClock (a A B z : ℂ) : ℂ :=
  z * suzukiNeumannBoundaryClockCore a A B z

private def suzukiNeumannBoundaryClockCorePrime (a A B z : ℂ) : ℂ :=
  a * (-A * Complex.sin (a * z) + B * Complex.cos (a * z))

private def suzukiNeumannBoundaryClockPrime (a A B z : ℂ) : ℂ :=
  suzukiNeumannBoundaryClockCore a A B z +
    z * suzukiNeumannBoundaryClockCorePrime a A B z

private def suzukiNeumannBoundaryClockSecond (a A B z : ℂ) : ℂ :=
  2 * suzukiNeumannBoundaryClockCorePrime a A B z -
    a ^ (2 : ℕ) * z * suzukiNeumannBoundaryClockCore a A B z

private theorem hasDerivAt_suzukiNeumannBoundaryClockCore (a A B z : ℂ) :
    HasDerivAt (suzukiNeumannBoundaryClockCore a A B)
      (suzukiNeumannBoundaryClockCorePrime a A B z) z := by
  have hlin : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have hcos := (Complex.hasDerivAt_cos (a * z)).comp z hlin
  have hsin := (Complex.hasDerivAt_sin (a * z)).comp z hlin
  convert (hcos.const_mul A).add (hsin.const_mul B) using 1
  all_goals
    first
    | rfl
    | (simp only [suzukiNeumannBoundaryClockCorePrime]; first | rfl | ring)

private theorem hasDerivAt_suzukiNeumannBoundaryClockCorePrime (a A B z : ℂ) :
    HasDerivAt (suzukiNeumannBoundaryClockCorePrime a A B)
      (-a ^ (2 : ℕ) * suzukiNeumannBoundaryClockCore a A B z) z := by
  have hlin : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have hsin := (Complex.hasDerivAt_sin (a * z)).comp z hlin
  have hcos := (Complex.hasDerivAt_cos (a * z)).comp z hlin
  convert (((hsin.const_mul (-A)).add (hcos.const_mul B)).const_mul a) using 1
  all_goals
    first
    | rfl
    | (simp only [suzukiNeumannBoundaryClockCore]; first | rfl | ring)

private theorem hasDerivAt_suzukiNeumannBoundaryClock (a A B z : ℂ) :
    HasDerivAt (suzukiNeumannBoundaryClock a A B)
      (suzukiNeumannBoundaryClockPrime a A B z) z := by
  convert (hasDerivAt_id z).mul
      (hasDerivAt_suzukiNeumannBoundaryClockCore a A B z) using 1
  all_goals
    first
    | rfl
    | (simp only [suzukiNeumannBoundaryClockPrime, id_eq]; first | rfl | ring)

private theorem hasDerivAt_suzukiNeumannBoundaryClockPrime (a A B z : ℂ) :
    HasDerivAt (suzukiNeumannBoundaryClockPrime a A B)
      (suzukiNeumannBoundaryClockSecond a A B z) z := by
  convert (hasDerivAt_suzukiNeumannBoundaryClockCore a A B z).add
      ((hasDerivAt_id z).mul
        (hasDerivAt_suzukiNeumannBoundaryClockCorePrime a A B z)) using 1
  all_goals
    first
    | rfl
    | (simp only [suzukiNeumannBoundaryClockSecond, id_eq]; first | rfl | ring)

/-- Polynomial second-order annihilator of the complete Neumann boundary-clock module. -/
def suzukiNeumannBoundaryAnnihilator (a : ℂ) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (2 : ℕ) * deriv (deriv H) z - 2 * z * deriv H z +
    (2 + a ^ (2 : ℕ) * z ^ (2 : ℕ)) * H z

/-- The complete rank-two endpoint clock is killed exactly, with no estimate on its coefficients. -/
theorem suzukiNeumannBoundaryAnnihilator_clock (a A B z : ℂ) :
    suzukiNeumannBoundaryAnnihilator a (suzukiNeumannBoundaryClock a A B) z = 0 := by
  have hfirst : deriv (suzukiNeumannBoundaryClock a A B) =
      suzukiNeumannBoundaryClockPrime a A B := by
    funext w
    exact (hasDerivAt_suzukiNeumannBoundaryClock a A B w).deriv
  rw [suzukiNeumannBoundaryAnnihilator, hfirst,
    (hasDerivAt_suzukiNeumannBoundaryClockPrime a A B z).deriv]
  simp only [suzukiNeumannBoundaryClock, suzukiNeumannBoundaryClockPrime,
    suzukiNeumannBoundaryClockSecond]
  ring

/-- Exact output of the annihilator on the boundary-free inverse-Laplacian symbol. -/
theorem suzukiNeumannBoundaryAnnihilator_sq_mul
    (a : ℂ) (F : ℂ → ℂ) (z : ℂ)
    (hF : ∀ w, AnalyticAt ℂ F w) :
    suzukiNeumannBoundaryAnnihilator a (fun w => w ^ (2 : ℕ) * F w) z =
      z ^ (4 : ℕ) * deriv (deriv F) z + 2 * z ^ (3 : ℕ) * deriv F z +
        a ^ (2 : ℕ) * z ^ (4 : ℕ) * F z := by
  have hfirstFun : deriv (fun w : ℂ => w ^ (2 : ℕ) * F w) =
      fun w => 2 * w * F w + w ^ (2 : ℕ) * deriv F w := by
    funext w
    have hsq : HasDerivAt (fun v : ℂ => v ^ (2 : ℕ)) (2 * w) w := by
      convert (hasDerivAt_id w).pow 2 using 1
      all_goals
        first
        | rfl
        | (simp only [id_eq]; first | rfl | ring)
    exact (hsq.mul (hF w).differentiableAt.hasDerivAt).deriv
  rw [suzukiNeumannBoundaryAnnihilator, hfirstFun]
  have hsq : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ)) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1
    all_goals
      first
      | rfl
      | (simp only [id_eq]; first | rfl | ring)
  have hterm1 : HasDerivAt (fun w : ℂ => 2 * w * F w)
      (2 * F z + 2 * z * deriv F z) z := by
    convert (((hasDerivAt_id z).const_mul 2).mul
      (hF z).differentiableAt.hasDerivAt) using 1
    all_goals
      first
      | rfl
      | (simp only [id_eq]; first | rfl | ring)
  have hterm2 : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) * deriv F w)
      (2 * z * deriv F z + z ^ (2 : ℕ) * deriv (deriv F) z) z := by
    exact hsq.mul (hF z).deriv.differentiableAt.hasDerivAt
  have hsumFun :
      (fun w : ℂ => 2 * w * F w + w ^ (2 : ℕ) * deriv F w) =
        (fun w : ℂ => 2 * w * F w) +
          (fun w : ℂ => w ^ (2 : ℕ) * deriv F w) := by
    funext w
    simp only [Pi.add_apply]
  have hsecond : deriv (fun w : ℂ => 2 * w * F w + w ^ (2 : ℕ) * deriv F w) z =
      2 * F z + 4 * z * deriv F z + z ^ (2 : ℕ) * deriv (deriv F) z := by
    rw [hsumFun]
    convert (hterm1.add hterm2).deriv using 1
    all_goals first | rfl | ring
  rw [hsecond]
  ring

/-- The endpoint flux in the integration-by-parts law is exactly one boundary clock. -/
theorem suzukiNeumannBoundaryFlux_eq_clock (a : ℝ) (p m z : ℂ) :
    I * z *
        (p * suzukiOscillatoryKernel z a -
          m * suzukiOscillatoryKernel z (-a)) =
      suzukiNeumannBoundaryClock (a : ℂ)
        (I * (p - m)) (-(p + m)) z := by
  simp only [suzukiOscillatoryKernel]
  rw [show (a : ℂ) * (I * z) = ((a : ℂ) * z) * I by ring,
    show (((-a : ℝ) : ℂ)) * (I * z) = (-((a : ℂ) * z)) * I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  simp only [suzukiNeumannBoundaryClock,
    suzukiNeumannBoundaryClockCore]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Function-level form of the exact Neumann defect: it belongs to the two-clock module, with
coefficients determined only by endpoint values. -/
theorem neumannFourierBoundaryDifference_eq_clock
    (f f' f'' : ℝ → ℂ) (a : ℝ)
    (hf : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt f' (f'' x) x)
    (hf'i : IntervalIntegrable f' MeasureTheory.volume (-a) a)
    (hf''i : IntervalIntegrable f'' MeasureTheory.volume (-a) a)
    (hplus : f' a = 0) (hminus : f' (-a) = 0) :
    (fun z => ∫ x in -a..a, (-f'' x) * suzukiOscillatoryKernel z x) -
        (fun z => z ^ (2 : ℕ) * (∫ x in -a..a, f x * suzukiOscillatoryKernel z x)) =
      suzukiNeumannBoundaryClock (a : ℂ)
        (I * (f a - f (-a))) (-(f a + f (-a))) := by
  funext z
  rw [Pi.sub_apply,
    neumannFourierBoundaryLaw f f' f'' a z hf hf' hf'i hf''i hplus hminus]
  simp only [add_sub_cancel_left]
  exact suzukiNeumannBoundaryFlux_eq_clock a (f a) (f (-a)) z

/-- **Exact finite-Neumann boundary elimination.**  The annihilator kills the complete Fourier
defect before any aperture limit, regardless of endpoint growth. -/
theorem suzukiNeumannBoundaryAnnihilator_fourierDefect_eq_zero
    (f f' f'' : ℝ → ℂ) (a : ℝ) (z : ℂ)
    (hf : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt f' (f'' x) x)
    (hf'i : IntervalIntegrable f' MeasureTheory.volume (-a) a)
    (hf''i : IntervalIntegrable f'' MeasureTheory.volume (-a) a)
    (hplus : f' a = 0) (hminus : f' (-a) = 0) :
    suzukiNeumannBoundaryAnnihilator (a : ℂ)
      ((fun w => ∫ x in -a..a, (-f'' x) * suzukiOscillatoryKernel w x) -
        (fun w => w ^ (2 : ℕ) * (∫ x in -a..a, f x * suzukiOscillatoryKernel w x))) z = 0 := by
  rw [neumannFourierBoundaryDifference_eq_clock f f' f'' a
    hf hf' hf'i hf''i hplus hminus]
  exact suzukiNeumannBoundaryAnnihilator_clock _ _ _ _

/-! ## Interior plateau cancellation -/

/-- The differential residual of Suzuki's known `hPlus(x)=exp(x)+i` plateau. -/
def suzukiPlateauPlusResidual (x : ℝ) : ℂ :=
  I * (Complex.exp (x : ℂ) - (Complex.exp (x : ℂ) + I))

/-- The differential residual of Suzuki's known `hMinus(x)=exp(-x)-i` plateau. -/
def suzukiPlateauMinusResidual (x : ℝ) : ℂ :=
  I * (-Complex.exp (-(x : ℂ)) + (Complex.exp (-(x : ℂ)) - I))

@[simp] theorem suzukiPlateauPlusResidual_eq_one (x : ℝ) :
    suzukiPlateauPlusResidual x = 1 := by
  simp only [suzukiPlateauPlusResidual]
  rw [show Complex.exp (x : ℂ) - (Complex.exp (x : ℂ) + I) = -I by ring,
    mul_neg, I_mul_I]
  ring

@[simp] theorem suzukiPlateauMinusResidual_eq_one (x : ℝ) :
    suzukiPlateauMinusResidual x = 1 := by
  simp only [suzukiPlateauMinusResidual]
  rw [show -Complex.exp (-(x : ℂ)) + (Complex.exp (-(x : ℂ)) - I) = -I by ring,
    mul_neg, I_mul_I]
  ring

/-- At the distinguished phase `q=-1`, the known interior first-order source cancels pointwise.
Any surviving global channel is therefore carried by endpoint gluing and exterior continuation. -/
theorem suzukiPlateauResidual_neg_one_cancellation (x : ℝ) :
    suzukiPlateauPlusResidual x - suzukiPlateauMinusResidual x = 0 := by
  simp

/-! ## Xi multiplier and exterior pole tomography -/

/-- Reciprocal of Suzuki's shifted target: the multiplier carrying the corrected `h` bracket. -/
def suzukiShiftedXiMultiplier (eta z : ℂ) : ℂ :=
  (suzukiShiftedXiTarget eta z)⁻¹

theorem suzukiShiftedXiMultiplier_eq (eta z : ℂ) :
    suzukiShiftedXiMultiplier eta z =
      suzukiShiftedXiDenominator eta z / (z ^ (2 : ℕ) * XiC z) := by
  simp only [suzukiShiftedXiMultiplier, suzukiShiftedXiTarget]
  field_simp

/-- Corrected exterior remainder after subtracting an entire finite-interval contribution. -/
def suzukiExteriorRemainder
    (eta : ℂ) (W intervalPart : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiShiftedXiMultiplier eta z * W z - intervalPart z

theorem meromorphicAt_suzukiShiftedXiMultiplier (eta z : ℂ) :
    MeromorphicAt (suzukiShiftedXiMultiplier eta) z := by
  have hnum : AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ) * XiC w) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ)) z).mul
      (XiC_analytic z (Set.mem_univ z))
  have hden : AnalyticAt ℂ (suzukiShiftedXiDenominator eta) z :=
    (XiC_analytic z (Set.mem_univ z)).deriv.sub
      (analyticAt_const.mul (XiC_analytic z (Set.mem_univ z)))
  change MeromorphicAt (fun w => (suzukiShiftedXiTarget eta w)⁻¹) z
  exact (hnum.meromorphicAt.div hden.meromorphicAt).inv

/-- The corrected Xi multiplier has a simple pole at every Xi zero, regardless of multiplicity. -/
theorem meromorphicOrderAt_suzukiShiftedXiMultiplier_eq_neg_one_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    meromorphicOrderAt (suzukiShiftedXiMultiplier eta) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt (suzukiShiftedXiTarget eta)⁻¹ z = _
  rw [meromorphicOrderAt_inv,
    meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero hz]
  norm_num

/-- The multiplier residue records the full Xi multiplicity. -/
theorem meromorphicTrailingCoeffAt_suzukiShiftedXiMultiplier_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    meromorphicTrailingCoeffAt (suzukiShiftedXiMultiplier eta) z =
      (((analyticOrderAt XiC z).toNat : ℂ) / z ^ (2 : ℕ)) := by
  change meromorphicTrailingCoeffAt (fun w => (suzukiShiftedXiTarget eta w)⁻¹) z = _
  rw [meromorphicTrailingCoeffAt_fun_inv,
    meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero hz]
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact XiC_zero_ne hz
  have hm0Nat : (analyticOrderAt XiC z).toNat ≠ 0 := by
    have hne : analyticOrderAt XiC z ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨XiC_analytic z (Set.mem_univ z), hz⟩
    have htop : analyticOrderAt XiC z ≠ ⊤ := XiC_order_ne_top z
    intro hm
    rcases ENat.toNat_eq_zero.mp hm with hzero | htop'
    · exact hne hzero
    · exact htop htop'
  have hm0 : ((analyticOrderAt XiC z).toNat : ℂ) ≠ 0 := by
    exact_mod_cast hm0Nat
  field_simp

/-- An analytic nonzero characteristic factor and an entire interval correction cannot hide the
Xi pole in the exterior remainder. -/
theorem meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one
    {eta z : ℂ} {W intervalPart : ℂ → ℂ}
    (hz : XiC z = 0)
    (hW : AnalyticAt ℂ W z) (hW0 : W z ≠ 0)
    (hI : AnalyticAt ℂ intervalPart z) :
    meromorphicOrderAt (suzukiExteriorRemainder eta W intervalPart) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  let singular : ℂ → ℂ := fun w => suzukiShiftedXiMultiplier eta w * W w
  have hmult : MeromorphicAt (suzukiShiftedXiMultiplier eta) z :=
    meromorphicAt_suzukiShiftedXiMultiplier eta z
  have hmultOrder : meromorphicOrderAt (suzukiShiftedXiMultiplier eta) z =
      ((-1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_suzukiShiftedXiMultiplier_eq_neg_one_of_XiC_zero hz
  have hWOrder : meromorphicOrderAt W z = 0 := by
    rw [hW.meromorphicOrderAt_eq, hW.analyticOrderAt_eq_zero.mpr hW0]
    simp
  have hsing : MeromorphicAt singular z := hmult.mul hW.meromorphicAt
  have hsingOrder : meromorphicOrderAt singular z = ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [singular]
    rw [fun_meromorphicOrderAt_mul hmult hW.meromorphicAt, hmultOrder, hWOrder]
    norm_num
  have hlt : meromorphicOrderAt singular z < meromorphicOrderAt intervalPart z := by
    rw [hsingOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hI.meromorphicOrderAt_nonneg
  have hltNeg : meromorphicOrderAt singular z < meromorphicOrderAt (-intervalPart) z := by
    rw [← meromorphicOrderAt_neg (f := intervalPart) (x := z)]
    exact hlt
  change meromorphicOrderAt (singular + -intervalPart) z = _
  rw [meromorphicOrderAt_add_eq_left_of_lt hI.neg.meromorphicAt hltNeg,
    hsingOrder]

/-- Exact pole tomography: the exterior residue is Xi multiplicity times the nonvanishing Suzuki
characteristic value, divided by `z²`. -/
theorem meromorphicTrailingCoeffAt_suzukiExteriorRemainder
    {eta z : ℂ} {W intervalPart : ℂ → ℂ}
    (hz : XiC z = 0)
    (hW : AnalyticAt ℂ W z) (hW0 : W z ≠ 0)
    (hI : AnalyticAt ℂ intervalPart z) :
    meromorphicTrailingCoeffAt (suzukiExteriorRemainder eta W intervalPart) z =
      ((analyticOrderAt XiC z).toNat : ℂ) * W z / z ^ (2 : ℕ) := by
  let singular : ℂ → ℂ := fun w => suzukiShiftedXiMultiplier eta w * W w
  have hmult : MeromorphicAt (suzukiShiftedXiMultiplier eta) z :=
    meromorphicAt_suzukiShiftedXiMultiplier eta z
  have hsing : MeromorphicAt singular z := hmult.mul hW.meromorphicAt
  have hsingOrder : meromorphicOrderAt singular z = ((-1 : ℤ) : WithTop ℤ) := by
    have hmultOrder : meromorphicOrderAt (suzukiShiftedXiMultiplier eta) z =
        ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_suzukiShiftedXiMultiplier_eq_neg_one_of_XiC_zero hz
    have hWOrder : meromorphicOrderAt W z = 0 := by
      rw [hW.meromorphicOrderAt_eq, hW.analyticOrderAt_eq_zero.mpr hW0]
      simp
    dsimp only [singular]
    rw [fun_meromorphicOrderAt_mul hmult hW.meromorphicAt, hmultOrder, hWOrder]
    norm_num
  have hlt : meromorphicOrderAt singular z < meromorphicOrderAt intervalPart z := by
    rw [hsingOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hI.meromorphicOrderAt_nonneg
  change meromorphicTrailingCoeffAt (fun w => singular w - intervalPart w) z = _
  rw [hI.meromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt hlt]
  dsimp only [singular]
  rw [hmult.meromorphicTrailingCoeffAt_fun_mul hW.meromorphicAt,
    meromorphicTrailingCoeffAt_suzukiShiftedXiMultiplier_of_XiC_zero hz,
    hW.meromorphicTrailingCoeffAt_of_ne_zero hW0]
  ring

/-! ## All-real characteristic family and the RH frontier -/

theorem suzukiCharacteristicPencil_ne_zero_of_im_ne_zero
    {A E : ℂ → ℂ} (hreal : SuzukiAllAngleRealZeros A E)
    {u z : ℂ} (hu : ‖u‖ = 1) (hz : z.im ≠ 0) :
    suzukiCharacteristicPencil A E u z ≠ 0 := by
  intro hzero
  exact hz (hreal u hu z hzero)

theorem analyticAt_suzukiShiftedXiMultiplier_of_XiC_ne_zero
    {eta z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    AnalyticAt ℂ (suzukiShiftedXiMultiplier eta) z := by
  rw [show suzukiShiftedXiMultiplier eta = fun w =>
      suzukiShiftedXiDenominator eta w / (w ^ (2 : ℕ) * XiC w) by
    funext w
    exact suzukiShiftedXiMultiplier_eq eta w]
  have hnum : AnalyticAt ℂ (suzukiShiftedXiDenominator eta) z :=
    (XiC_analytic z (Set.mem_univ z)).deriv.sub
      (analyticAt_const.mul (XiC_analytic z (Set.mem_univ z)))
  have hden : AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ) * XiC w) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ)) z).mul
      (XiC_analytic z (Set.mem_univ z))
  exact hnum.div hden (mul_ne_zero (pow_ne_zero 2 hz) hXi)

/-- **Source-defined exterior criterion for RH.**  For one entire member of Suzuki's all-real
characteristic circle and any entire finite-interval contribution, RH is equivalent to off-real
holomorphy of the corrected exterior remainder.  The reverse implication is forced by the simple
pole theorem above, not by a convergence estimate. -/
theorem riemannHypothesis_iff_suzukiExteriorRemainder_analytic_offReal
    {A E intervalPart : ℂ → ℂ} {eta u : ℂ}
    (hA : ∀ z, AnalyticAt ℂ A z) (hE : ∀ z, AnalyticAt ℂ E z)
    (hI : ∀ z, AnalyticAt ℂ intervalPart z)
    (hreal : SuzukiAllAngleRealZeros A E) (hu : ‖u‖ = 1) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ
          (suzukiExteriorRemainder eta
            (suzukiCharacteristicPencil A E u) intervalPart) z := by
  constructor
  · intro hRH z hzIm
    have hXi : XiC z ≠ 0 := by
      intro hzero
      exact hzIm
        ((SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero.mp hRH) z hzero)
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      exact hzIm (by simp)
    have hmult := analyticAt_suzukiShiftedXiMultiplier_of_XiC_ne_zero
      (eta := eta) hz0 hXi
    have hW : AnalyticAt ℂ (suzukiCharacteristicPencil A E u) z :=
      (hA z).add (analyticAt_const.mul (hE z))
    exact hmult.mul hW |>.sub (hI z)
  · intro han
    rw [SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]
    intro z hzero
    by_contra hzIm
    have hW : AnalyticAt ℂ (suzukiCharacteristicPencil A E u) z :=
      (hA z).add (analyticAt_const.mul (hE z))
    have hW0 : suzukiCharacteristicPencil A E u z ≠ 0 :=
      suzukiCharacteristicPencil_ne_zero_of_im_ne_zero hreal hu hzIm
    have hpole := meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one
      (eta := eta) (W := suzukiCharacteristicPencil A E u)
      (intervalPart := intervalPart) hzero hW hW0 (hI z)
    have hnonneg := (han z hzIm).meromorphicOrderAt_nonneg
    rw [hpole] at hnonneg
    have hnot : ¬ (0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact hnot hnonneg

end

end RHTower
