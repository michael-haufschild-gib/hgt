import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.DampedGapResponse

/-!
# Inverting the Abel response

At positive width the zero-centered Abel response has a two-sided
linear inverse. The difference between a prescribed output and its
preimage gives the Hamiltonian commutator on that output.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The nonreal Green parameter of the zero-centered filter. -/
def hamiltonianAbelShift (ε : Ioi (0 : ℝ)) : ℂ := ⟨0, (ε : ℝ)⟩

theorem hamiltonianAbelShift_im_ne_zero (ε : Ioi (0 : ℝ)) :
    (hamiltonianAbelShift ε).im ≠ 0 :=
  (show 0 < (ε : ℝ) from ε.2).ne'

theorem hamiltonianAbelShift_ne_zero (ε : Ioi (0 : ℝ)) : hamiltonianAbelShift ε ≠ 0 :=
  fun he => hamiltonianAbelShift_im_ne_zero ε (congrArg Complex.im he)

/-- The forcing needed to produce a prescribed output under Abel
averaging. -/
def hamiltonianAbelInverse (H : Matrix ι ι ℂ) (ε : Ioi (0 : ℝ)) (Y : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  let z := hamiltonianAbelShift ε
  (-z)⁻¹ • (H * Y - Y * H - z • Y)

private theorem shiftedCommutator_smul (H Y : Matrix ι ι ℂ) (z r : ℂ) :
    H * (r • Y) - (r • Y) * H - z • (r • Y) =
      r • (H * Y - Y * H - z • Y) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_sub, smul_smul, smul_smul, mul_comm z r]

section

variable [DecidableEq ι]

theorem hamiltonianAbelInverse_leftInverse {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ε : Ioi (0 : ℝ)) :
    Function.LeftInverse (hamiltonianAbelInverse H ε) (hamiltonianDampedGapResponse hH 0 ε) := by
  intro X
  let z := hamiltonianAbelShift ε
  let G := hamiltonianCommutatorGreen hH z X
  have hg : H * G - G * H - z • G = X :=
    (shiftedCommutator_eq_iff_of_nonreal hH ⟨z, hamiltonianAbelShift_im_ne_zero ε⟩ X G).mpr rfl
  have hz : -z ≠ 0 := neg_ne_zero.mpr (hamiltonianAbelShift_ne_zero ε)
  simp only [hamiltonianAbelInverse, hamiltonianDampedGapResponse, Complex.ofReal_zero, zero_sub]
  change (-z)⁻¹ • (H * ((-z) • G) - ((-z) • G) * H - z • ((-z) • G)) = X
  rw [shiftedCommutator_smul, hg, smul_smul, inv_mul_cancel₀ hz, one_smul]

theorem hamiltonianAbelInverse_rightInverse {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ε : Ioi (0 : ℝ)) :
    Function.RightInverse (hamiltonianAbelInverse H ε) (hamiltonianDampedGapResponse hH 0 ε) := by
  intro Y
  let z := hamiltonianAbelShift ε
  have hz : -z ≠ 0 := neg_ne_zero.mpr (hamiltonianAbelShift_ne_zero ε)
  have hc : H * ((-z)⁻¹ • Y) - ((-z)⁻¹ • Y) * H - z • ((-z)⁻¹ • Y) =
      hamiltonianAbelInverse H ε Y :=
    shiftedCommutator_smul H Y z (-z)⁻¹
  have he : (-z)⁻¹ • Y = hamiltonianCommutatorGreen hH z (hamiltonianAbelInverse H ε Y) :=
    (shiftedCommutator_eq_iff_of_nonreal hH ⟨z, hamiltonianAbelShift_im_ne_zero ε⟩ _ _).mp hc
  simp only [hamiltonianDampedGapResponse, Complex.ofReal_zero, zero_sub]
  change (-z) • hamiltonianCommutatorGreen hH z (hamiltonianAbelInverse H ε Y) = Y
  rw [← he, smul_smul, mul_inv_cancel₀ hz, one_smul]

theorem dampedGapResponse_zero_eq_iff_abelInverse_eq
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (X Y : Matrix ι ι ℂ) :
    hamiltonianDampedGapResponse hH 0 ε X = Y ↔ hamiltonianAbelInverse H ε Y = X := by
  constructor
  · rintro rfl
    exact hamiltonianAbelInverse_leftInverse hH ε X
  · rintro rfl
    exact hamiltonianAbelInverse_rightInverse hH ε Y

theorem hamiltonianAbelInverse_eq_iff_response_eq {H K : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (ε : Ioi (0 : ℝ)) :
    hamiltonianAbelInverse H ε = hamiltonianAbelInverse K ε ↔
      hamiltonianDampedGapResponse hH 0 ε = hamiltonianDampedGapResponse hK 0 ε := by
  constructor
  · intro h
    apply Function.LeftInverse.eq_rightInverse (hamiltonianAbelInverse_rightInverse hH ε)
    rw [h]
    exact hamiltonianAbelInverse_leftInverse hK ε
  · intro h
    apply Function.LeftInverse.eq_rightInverse (hamiltonianAbelInverse_leftInverse hH ε)
    rw [h]
    exact hamiltonianAbelInverse_rightInverse hK ε

end

theorem hamiltonianAbelInverse_eq_sub (H : Matrix ι ι ℂ) (ε : Ioi (0 : ℝ))
    (Y : Matrix ι ι ℂ) :
    hamiltonianAbelInverse H ε Y =
      Y - (hamiltonianAbelShift ε)⁻¹ • (H * Y - Y * H) := by
  let z := hamiltonianAbelShift ε
  have hz : z ≠ 0 := hamiltonianAbelShift_ne_zero ε
  change (-z)⁻¹ • (H * Y - Y * H - z • Y) = Y - z⁻¹ • (H * Y - Y * H)
  rw [smul_sub, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hz, neg_smul, neg_smul, one_smul]
  abel

theorem trace_hamiltonianAbelInverse (H : Matrix ι ι ℂ) (ε : Ioi (0 : ℝ))
    (Y : Matrix ι ι ℂ) : (hamiltonianAbelInverse H ε Y).trace = Y.trace := by
  rw [hamiltonianAbelInverse_eq_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_mul_comm H Y, sub_self, smul_zero, sub_zero]

/-- Subtracting the forcing from the target extracts its commutator
after multiplication by the Green parameter. -/
def abelCommutatorReadout (ε : Ioi (0 : ℝ)) (target forcing : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  hamiltonianAbelShift ε • (target - forcing)

theorem abelCommutatorReadout_inverse (H : Matrix ι ι ℂ) (ε : Ioi (0 : ℝ))
    (Y : Matrix ι ι ℂ) :
    abelCommutatorReadout ε Y (hamiltonianAbelInverse H ε Y) = H * Y - Y * H := by
  rw [abelCommutatorReadout, hamiltonianAbelInverse_eq_sub, sub_sub_cancel, smul_smul,
    mul_inv_cancel₀ (hamiltonianAbelShift_ne_zero ε), one_smul]

theorem hamiltonianAbelInverse_eq_iff_commutators (H K : Matrix ι ι ℂ)
    (ε : Ioi (0 : ℝ)) (Y : Matrix ι ι ℂ) :
    hamiltonianAbelInverse H ε Y = hamiltonianAbelInverse K ε Y ↔
      H * Y - Y * H = K * Y - Y * K := by
  constructor
  · intro h
    rw [← abelCommutatorReadout_inverse H ε Y, ← abelCommutatorReadout_inverse K ε Y, h]
  · intro h
    rw [hamiltonianAbelInverse_eq_sub, hamiltonianAbelInverse_eq_sub, h]

#print axioms hamiltonianAbelInverse_leftInverse
#print axioms hamiltonianAbelInverse_rightInverse
#print axioms abelCommutatorReadout_inverse

end

end GaloisForLFunctions.HTGeometry
