import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit

/-!
# Critical squarefree-Mobius Fisher tangent

The centered logarithmic score of the normalized signed squarefree source is constructed as an
actual `ℓ²` vector.  Its squared Hilbert norm is exactly the projective Fisher energy, it is
orthogonal to the normalized source state, and its critical norm tends to four.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Coordinate of the completed critical Fisher tangent. -/
def infiniteMobiusCriticalFisherTangentWeight
    (sigma : ℝ) (n : ℕ) : ℂ :=
  ((-2 * (sigma - 1) *
    (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
      infiniteMobiusSignedWeight sigma n

theorem norm_infiniteMobiusCriticalFisherTangentWeight_sq
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ (2 : ℕ) =
      4 * (sigma - 1) ^ (2 : ℕ) * squarefreeMobiusProbability sigma n *
        (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ (2 : ℕ) := by
  rw [infiniteMobiusCriticalFisherTangentWeight, norm_mul, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  ring

private theorem summable_squarefreeMobiusCenteredLogSq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ => squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ (2 : ℕ)) := by
  let m := squarefreeMobiusLogMoment 1 sigma
  have h2 := summable_squarefreeMobiusLogMoment 2 hsigma
  have h1 := (summable_squarefreeMobiusLogMoment 1 hsigma).mul_left (-2 * m)
  have h0 := (summable_squarefreeMobiusProbability hsigma).mul_left (m ^ (2 : ℕ))
  apply (h2.add h1 |>.add h0).congr
  intro n
  dsimp [m]
  ring

private theorem tsum_squarefreeMobiusCenteredLogSq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ (2 : ℕ)) =
      squarefreeMobiusLogMoment 2 sigma - squarefreeMobiusLogMoment 1 sigma ^ (2 : ℕ) := by
  let m := squarefreeMobiusLogMoment 1 sigma
  have h2 := summable_squarefreeMobiusLogMoment 2 hsigma
  have h1base : Summable (fun n : ℕ =>
      squarefreeMobiusProbability sigma n * Real.log n) := by
    simpa only [pow_one] using summable_squarefreeMobiusLogMoment 1 hsigma
  have h1 := h1base.mul_left (-2 * m)
  have h0base := summable_squarefreeMobiusProbability hsigma
  have h0 := h0base.mul_left (m ^ (2 : ℕ))
  rw [show (fun n : ℕ => squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ (2 : ℕ)) =
      fun n => squarefreeMobiusProbability sigma n * Real.log n ^ (2 : ℕ) +
        (-2 * m) * (squarefreeMobiusProbability sigma n * Real.log n) +
          m ^ (2 : ℕ) * squarefreeMobiusProbability sigma n by
    funext n
    dsimp [m]
    ring]
  rw [Summable.tsum_add (h2.add h1) h0, Summable.tsum_add h2 h1,
    tsum_mul_left, tsum_mul_left]
  rw [show (∑' n : ℕ, squarefreeMobiusProbability sigma n * Real.log n ^ (2 : ℕ)) =
      squarefreeMobiusLogMoment 2 sigma by rfl]
  rw [show (∑' n : ℕ, squarefreeMobiusProbability sigma n * Real.log n) =
      squarefreeMobiusLogMoment 1 sigma by
    unfold squarefreeMobiusLogMoment
    simp only [pow_one]]
  rw [tsum_squarefreeMobiusProbability hsigma]
  dsimp [m]
  ring

private theorem summable_norm_sq_infiniteMobiusCriticalFisherTangentWeight
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ (2 : ℕ)) := by
  have h := (summable_squarefreeMobiusCenteredLogSq hsigma).mul_left
    (4 * (sigma - 1) ^ (2 : ℕ))
  apply h.congr
  intro n
  rw [norm_infiniteMobiusCriticalFisherTangentWeight_sq hsigma]
  ring

/-- The completed critical Fisher tangent as an actual square-summable Hilbert vector. -/
def infiniteMobiusCriticalFisherTangentLp
    (sigma : ℝ) (hsigma : 1 < sigma) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalFisherTangentWeight sigma,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCriticalFisherTangentWeight hsigma)⟩

/-- Exact Fisher-energy identity for the Hilbert tangent. -/
theorem norm_infiniteMobiusCriticalFisherTangentLp_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ (2 : ℕ) =
      squarefreeMobiusCriticalProjectiveFisherEnergy sigma := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  simp only [infiniteMobiusCriticalFisherTangentLp]
  rw [show (∑' n : ℕ, ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ (2 : ℕ)) =
      4 * (sigma - 1) ^ (2 : ℕ) *
        ∑' n : ℕ, squarefreeMobiusProbability sigma n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ (2 : ℕ) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [norm_infiniteMobiusCriticalFisherTangentWeight_sq hsigma]
    ring]
  rw [tsum_squarefreeMobiusCenteredLogSq hsigma]
  unfold squarefreeMobiusCriticalProjectiveFisherEnergy
    squarefreeMobiusCriticalClockVariance
  ring

/-- The squared Hilbert norm of the critical tangent tends to four. -/
theorem tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ (2 : ℕ)
      else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  apply tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hgt : 1 < sigma := hsigma
  simp only [dif_pos hgt]
  exact (norm_infiniteMobiusCriticalFisherTangentLp_sq hgt).symm

/-- The normalized signed source state is orthogonal to its centered Fisher tangent. -/
theorem inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma) = 0 := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusSignedWeightLp, infiniteMobiusCriticalFisherTangentLp,
    RCLike.inner_apply]
  rw [show (∑' n : ℕ,
      infiniteMobiusCriticalFisherTangentWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) =
      ((-2 * (sigma - 1) : ℝ) : ℂ) *
        ∑' n : ℕ, ((squarefreeMobiusProbability sigma n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [infiniteMobiusCriticalFisherTangentWeight]
    have hnorm : infiniteMobiusSignedWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
        (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ (2 : ℕ)) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by
          rw [← Complex.ofReal_pow,
            norm_infiniteMobiusSignedWeight_sq hsigma]
    calc
      _ = ((-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
            (infiniteMobiusSignedWeight sigma n *
              (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) := by ring
      _ = _ := by rw [hnorm]; push_cast; ring]
  have hsumReal : Summable (fun n : ℕ => squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
    have h1 := summable_squarefreeMobiusLogMoment 1 hsigma
    have h0 := (summable_squarefreeMobiusProbability hsigma).mul_left
      (-squarefreeMobiusLogMoment 1 sigma)
    apply (h1.add h0).congr
    intro n
    ring
  have hsumZero : (∑' n : ℕ, squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) = 0 := by
    have h1 : Summable (fun n : ℕ =>
        squarefreeMobiusProbability sigma n * Real.log n) := by
      simpa only [pow_one] using summable_squarefreeMobiusLogMoment 1 hsigma
    rw [show (fun n : ℕ => squarefreeMobiusProbability sigma n *
        (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
        fun n => squarefreeMobiusProbability sigma n * Real.log n +
          (-squarefreeMobiusLogMoment 1 sigma) *
            squarefreeMobiusProbability sigma n by
      funext n
      ring]
    rw [Summable.tsum_add h1
      ((summable_squarefreeMobiusProbability hsigma).mul_left _), tsum_mul_left]
    rw [show (∑' n : ℕ, squarefreeMobiusProbability sigma n * Real.log n) =
        squarefreeMobiusLogMoment 1 sigma by
      unfold squarefreeMobiusLogMoment
      simp only [pow_one]]
    rw [tsum_squarefreeMobiusProbability hsigma]
    ring
  have hcast : (∑' n : ℕ, ((squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ)) = 0 := by
    rw [← Complex.ofReal_tsum (fun n : ℕ =>
      squarefreeMobiusProbability sigma n *
        (Real.log n - squarefreeMobiusLogMoment 1 sigma)), hsumZero]
    norm_num
  rw [hcast]
  norm_num

end RHTower
