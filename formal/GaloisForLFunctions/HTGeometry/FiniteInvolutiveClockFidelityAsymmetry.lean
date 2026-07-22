import GaloisForLFunctions.HTGeometry.FiniteClockOrbitAsymmetry
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue
import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison

/-!
# Fidelity asymmetry of an involutive clock

For an arbitrary state and an involutive isometric clock, projective asymmetry and the homogeneous
fidelity deficit are exactly four times the product of its invariant and anti-invariant sector
weights.  The normalized pure-state fidelity law follows as a corollary.  Thus the fidelity-based
asymmetry resource used by quantitative Wigner--Araki--Yanase bounds is already a native
finite-clock value; no generator or temporal flow is required.

Physics provenance: A. Hokkyo and H. Tajima, *Quantitative Wigner-Araki-Yanase Theorems for
Unitary and Antiunitary Symmetries*, arXiv:2607.09075, bounds the error of symmetry-breaking
measurements and gates by the fidelity between an apparatus state and its symmetry transform.
The results below do not formalize their channel inequalities.  They identify that fidelity
resource exactly for the two-sector clock geometry used in this corpus.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The overlap with an involutive clock transform is the invariant-sector weight minus the
anti-invariant-sector weight.  In particular, the overlap is real without a separate hypothesis. -/
theorem inner_finiteInvolutiveClockTransform_eq_sectorNormSq_sub
    (U : E →L[ℂ] E) (hadjoint_mul : U.adjoint * U = 1) (hsq : U ^ 2 = 1)
    (ψ : E) :
    inner ℂ ψ (U ψ) =
      (‖finiteCyclicGaugeAverage U 2 ψ‖ ^ 2 -
        ‖(1 - finiteCyclicGaugeAverage U 2) ψ‖ ^ 2 : ℝ) := by
  let P : E →L[ℂ] E := finiteCyclicGaugeAverage U 2
  let a : E := P ψ
  let b : E := (1 - P) ψ
  have hPadj : P.adjoint = P := by
    simpa only [P, ContinuousLinearMap.star_eq_adjoint] using
      (finiteInvolutiveGaugeAverage_isSelfAdjoint U hadjoint_mul hsq).star_eq
  have hP2 : P * P = P := finiteInvolutiveGaugeAverage_isIdempotentElem U hsq
  have hPb : P b = 0 := by
    rw [show b = (1 - P) ψ by rfl, ← ContinuousLinearMap.mul_apply]
    have : P * (1 - P) = 0 := by noncomm_ring [hP2]
    rw [this]
    simp
  have hab : inner ℂ a b = 0 := by
    calc
      inner ℂ a b = inner ℂ (P ψ) b := rfl
      _ = inner ℂ ψ (P.adjoint b) := (P.adjoint_inner_right ψ b).symm
      _ = 0 := by rw [hPadj, hPb, inner_zero_right]
  have hba : inner ℂ b a = 0 := by
    rw [← inner_conj_symm]
    simp [hab]
  have hψ : ψ = a + b := by
    simp only [a, b, P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    module
  have hUψ : U ψ = a - b := by
    have hPapply := finiteInvolutiveGaugeAverage_apply U ψ
    change P ψ = ((2 : ℂ)⁻¹) • (ψ + U ψ) at hPapply
    change U ψ = P ψ - (ψ - P ψ)
    rw [hPapply]
    norm_num
    module
  change inner ℂ ψ (U ψ) = (‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ)
  rw [hUψ, hψ, inner_add_left, inner_sub_right, inner_sub_right,
    hab, hba, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp [a, b, P]
  ring

/-- The projective distance from any state to its clock transform is the exact product of the
invariant and anti-invariant clock-sector weights.  Homogeneity removes any normalization
hypothesis. -/
theorem finiteInvolutiveClock_projectiveAsymmetry_eq_four_mul_sectorWeights
    (U : E →L[ℂ] E) (hadjoint_mul : U.adjoint * U = 1) (hsq : U ^ 2 = 1)
    (ψ : E) :
    projectiveGramTangentEnergy (𝕜 := ℂ) ψ (U ψ) =
      4 * ‖finiteCyclicGaugeAverage U 2 ψ‖ ^ 2 *
        ‖(1 - finiteCyclicGaugeAverage U 2) ψ‖ ^ 2 := by
  have hinner := inner_finiteInvolutiveClockTransform_eq_sectorNormSq_sub
    U hadjoint_mul hsq ψ
  have hsum := norm_finiteInvolutiveGaugeAverage_sq_add_complement_sq
    U hadjoint_mul hsq ψ
  have hUnormSq : ‖U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    simpa using (norm_pow_apply_sq_eq_of_adjoint_mul_self U 1 hadjoint_mul ψ)
  unfold projectiveGramTangentEnergy
  rw [hinner, Complex.norm_real, Real.norm_eq_abs, sq_abs, hUnormSq]
  nlinarith

/-- **Homogeneous fidelity-sector identity.**  Before unit normalization, the fourth-power mass
minus squared clock overlap is exactly the same invariant/anti-invariant sector product. -/
theorem finiteInvolutiveClock_homogeneousFidelityDeficit_eq_four_mul_sectorWeights
    (U : E →L[ℂ] E) (hadjoint_mul : U.adjoint * U = 1) (hsq : U ^ 2 = 1)
    (ψ : E) :
    ‖ψ‖ ^ 4 - ‖inner ℂ ψ (U ψ)‖ ^ 2 =
      4 * ‖finiteCyclicGaugeAverage U 2 ψ‖ ^ 2 *
        ‖(1 - finiteCyclicGaugeAverage U 2) ψ‖ ^ 2 := by
  rw [← finiteInvolutiveClock_projectiveAsymmetry_eq_four_mul_sectorWeights
    U hadjoint_mul hsq ψ]
  unfold projectiveGramTangentEnergy
  have hUnormSq : ‖U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    simpa using (norm_pow_apply_sq_eq_of_adjoint_mul_self U 1 hadjoint_mul ψ)
  rw [hUnormSq]
  ring

/-- **Pure-state fidelity-sector identity.**  The squared-fidelity deficit under an involutive
clock equals four times the product of its two sector weights.  This is the exact apparatus
asymmetry value required by fidelity-based discrete-symmetry WAY bounds. -/
theorem finiteInvolutiveClock_pureStateFidelityDeficit_eq_four_mul_sectorWeights
    (U : E →L[ℂ] E) (hadjoint_mul : U.adjoint * U = 1) (hsq : U ^ 2 = 1)
    {ψ : E} (hψnorm : ‖ψ‖ = 1) :
    1 - ‖inner ℂ ψ (U ψ)‖ ^ 2 =
      4 * ‖finiteCyclicGaugeAverage U 2 ψ‖ ^ 2 *
        ‖(1 - finiteCyclicGaugeAverage U 2) ψ‖ ^ 2 := by
  rw [← finiteInvolutiveClock_homogeneousFidelityDeficit_eq_four_mul_sectorWeights
    U hadjoint_mul hsq ψ, hψnorm]
  norm_num

end

end HTGeometry
