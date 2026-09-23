import GaloisForLFunctions.RHTower.EulerPositiveFisherFourUnit

/-!
# Full-Euler pole cancellation before scalarization

The scalar Gamma--Xi graph combines the centered full-Euler Fisher score
with the polar current.  On the source Hilbert space this cancellation has
only one literal vector form:

`2 m_sigma psi_sigma - (sigma - 1)⁻¹ phi_sigma = 2 log(n) psi_sigma`.

Thus the pole is cancelled algebraically, but centering is lost.  The
resulting raw-clock vector has energy of exact order
`8 / (sigma - 1)^(2 : ℕ)`.  In particular the direct fixed-carrier vector
completion cannot be the missing uniformly contractive CCM incidence.

All statements are unconditional.
-/

open Complex Filter Set
open scoped Topology

noncomputable section
namespace RHTower

/-- Raw logarithmic Euler clock forced by cancelling the polar current
against the centered Fisher tangent. -/
def eulerPositiveGammaPoleCancelledWeight
    (sigma : ℝ) (n : ℕ+) : ℂ :=
  ((2 * Real.log (n : ℕ) : ℝ) : ℂ) *
    eulerPositiveStateWeight sigma n

private theorem summable_norm_sq_eulerPositiveGammaPoleCancelledWeight
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ+ =>
      ‖eulerPositiveGammaPoleCancelledWeight sigma n‖ ^ (2 : ℕ)) := by
  have h := (summable_eulerPositiveLogMoment 2 hsigma).mul_left 4
  apply h.congr
  intro n
  rw [eulerPositiveGammaPoleCancelledWeight, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs,
    norm_eulerPositiveStateWeight_sq hsigma]
  ring

/-- The pole-cancelled raw clock as an actual full-Euler Hilbert vector. -/
def eulerPositiveGammaPoleCancelledLp
    (sigma : ℝ) (hsigma : 1 < sigma) : EulerPositiveL2 :=
  ⟨eulerPositiveGammaPoleCancelledWeight sigma,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerPositiveGammaPoleCancelledWeight hsigma)⟩

/-- **Vector pole-cancellation identity.**  Adding the polar base component
to the graph-normalized centered tangent removes the pole pointwise and
forces the raw logarithmic clock. -/
theorem eulerPositive_pole_base_sub_normalized_tangent
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (((2 * eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) •
          eulerPositiveStateLp sigma hsigma) -
        ((((sigma - 1)⁻¹ : ℝ) : ℂ) •
          eulerPositiveCriticalFisherTangentLp sigma hsigma) =
      eulerPositiveGammaPoleCancelledLp sigma hsigma := by
  apply lp.ext
  funext n
  change
    ((2 * eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) *
          eulerPositiveStateWeight sigma n -
        (((sigma - 1)⁻¹ : ℝ) : ℂ) *
          eulerPositiveCriticalFisherTangentWeight sigma n =
      eulerPositiveGammaPoleCancelledWeight sigma n
  rw [eulerPositiveCriticalFisherTangentWeight,
    eulerPositiveGammaPoleCancelledWeight]
  have heps : sigma - 1 ≠ 0 := sub_ne_zero.mpr hsigma.ne'
  have hreal :
      2 * eulerPositiveLogMoment 1 sigma -
          (sigma - 1)⁻¹ *
            (-2 * (sigma - 1) *
              (Real.log (n : ℕ) -
                eulerPositiveLogMoment 1 sigma)) =
        2 * Real.log (n : ℕ) := by
    field_simp [heps]
    ring
  have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) hreal
  push_cast at hcomplex
  push_cast
  linear_combination
    eulerPositiveStateWeight sigma n * hcomplex

/-- Exact energy of the pole-cancelled vector. -/
theorem norm_eulerPositiveGammaPoleCancelledLp_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositiveGammaPoleCancelledLp sigma hsigma‖ ^ (2 : ℕ) =
      4 * eulerPositiveLogMoment 2 sigma := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  simp only [eulerPositiveGammaPoleCancelledLp]
  rw [show (∑' n : ℕ+,
      ‖eulerPositiveGammaPoleCancelledWeight sigma n‖ ^ (2 : ℕ)) =
      4 * ∑' n : ℕ+,
        eulerPositiveProbability sigma n *
          Real.log (n : ℕ) ^ (2 : ℕ) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [eulerPositiveGammaPoleCancelledWeight, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs,
      norm_eulerPositiveStateWeight_sq hsigma]
    ring]
  rfl

/-- The rescaled direct Euler first moment is the affine critical-clock
mean. -/
theorem sub_one_mul_eulerPositiveLogMoment_one_eq_affineMean
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (sigma - 1) * eulerPositiveLogMoment 1 sigma =
      eulerSquarefreeAffineCriticalClockMean sigma := by
  rw [eulerPositiveLogMoment_one_eq_affine hsigma]
  unfold eulerSquarefreeAffineCriticalClockMean
  rw [eulerSquareResidualCriticalClockMoment_eq]
  ring

/-- The rescaled direct Euler second moment is the affine critical-clock
second moment. -/
theorem sub_one_sq_mul_eulerPositiveLogMoment_two_eq_affineSecondMoment
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (sigma - 1) ^ (2 : ℕ) * eulerPositiveLogMoment 2 sigma =
      eulerSquarefreeAffineCriticalClockSecondMoment sigma := by
  rw [eulerPositiveLogMoment_two_eq_affine hsigma]
  unfold eulerSquarefreeAffineCriticalClockSecondMoment
  rw [eulerSquareResidualCriticalClockMoment_eq 1,
    eulerSquareResidualCriticalClockMoment_eq 2]
  ring

/-- The full-Euler raw second clock moment tends to `2` after critical
rescaling. -/
theorem tendsto_sub_one_sq_mul_eulerPositiveLogMoment_two :
    Tendsto
      (fun sigma : ℝ =>
        (sigma - 1) ^ (2 : ℕ) * eulerPositiveLogMoment 2 sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := by
  have hsecond :
      Tendsto eulerSquarefreeAffineCriticalClockSecondMoment
        (nhdsWithin 1 (Ioi 1)) (nhds 2) := by
    have h :=
      tendsto_eulerSquarefreeAffineCriticalClockVariance.add
        (tendsto_eulerSquarefreeAffineCriticalClockMean.pow 2)
    convert h using 1
    · funext sigma
      simp [eulerSquarefreeAffineCriticalClockVariance]
    · norm_num
  apply hsecond.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  exact
    (sub_one_sq_mul_eulerPositiveLogMoment_two_eq_affineSecondMoment
      hsigma).symm

/-- **Eight-unit blow-up law.**  After pole cancellation the vector has
scaled energy `8`; equivalently its unscaled energy is of exact order
`8 / (sigma - 1)^(2 : ℕ)`, not four-unit bounded. -/
theorem tendsto_sub_one_sq_mul_norm_eulerPositiveGammaPoleCancelledLp_sq :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          (sigma - 1) ^ (2 : ℕ) *
            ‖eulerPositiveGammaPoleCancelledLp sigma hsigma‖ ^ (2 : ℕ)
        else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 8) := by
  have h :
      Tendsto
        (fun sigma : ℝ =>
          4 * ((sigma - 1) ^ (2 : ℕ) *
            eulerPositiveLogMoment 2 sigma))
        (nhdsWithin 1 (Ioi 1)) (nhds 8) := by
    convert
      tendsto_sub_one_sq_mul_eulerPositiveLogMoment_two.const_mul 4 using 1
    norm_num
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [dif_pos hsigma,
    norm_eulerPositiveGammaPoleCancelledLp_sq hsigma]
  ring

end RHTower
