import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelSymmetricResolvent

/-!
# Visibility in the even and odd readings

Coercivity of the inverse response prevents a nonzero transfer from
vanishing at the next transfer. Thus even data detect a perturbation
precisely when the perturbation fails to commute with the base reading.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H T : Matrix ι ι ℂ}

/-- Hermitian commutator multiplication is self-adjoint for the trace pairing. -/
theorem trace_conjTranspose_mul_commutator (hH : H.IsHermitian) (W Y : Matrix ι ι ℂ) :
    (Wᴴ * (H * Y - Y * H)).trace = ((H * W - W * H)ᴴ * Y).trace := by
  have hc : (Wᴴ * (Y * H)).trace = (H * Wᴴ * Y).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (Wᴴ * Y) H, ← Matrix.mul_assoc]
  simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.sub_mul, show Hᴴ = H from hH]
  rw [hc, Matrix.mul_assoc Wᴴ H Y]

/-- The real part of the inverse-response pairing is the squared
Hilbert–Schmidt norm, since its commutator term is skew-adjoint. -/
theorem re_trace_conjTranspose_mul_abelInverse (hH : H.IsHermitian)
    (ε : Ioi (0 : ℝ)) (W : Matrix ι ι ℂ) :
    (Wᴴ * hamiltonianAbelInverse H ε W).trace.re = hsSqRe W := by
  let C := H * W - W * H
  have hstar : star ((Wᴴ * C).trace) = (Wᴴ * C).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact (trace_conjTranspose_mul_commutator hH W W).symm
  have him : ((Wᴴ * C).trace).im = 0 := by
    have he := congrArg Complex.im hstar
    rw [Complex.star_def, Complex.conj_im] at he
    linarith only [he]
  have hγ : ((hamiltonianAbelShift ε)⁻¹).re = 0 := by
    rw [Complex.inv_re]
    change (0 : ℝ) / _ = 0
    exact zero_div _
  change (Wᴴ * hamiltonianAbelInverse H ε W).trace.re = (Wᴴ * W).trace.re
  rw [hamiltonianAbelInverse_eq_sub]
  change (Wᴴ * (W - (hamiltonianAbelShift ε)⁻¹ • C)).trace.re = _
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
    smul_eq_mul, Complex.mul_re, hγ, him, zero_mul, mul_zero, sub_self, sub_zero]

private theorem eq_zero_of_hsSqRe_eq_zero (W : Matrix ι ι ℂ) (hW : hsSqRe W = 0) : W = 0 := by
  rw [hsSqRe_eq_sum] at hW
  apply Matrix.ext
  intro i j
  have hle : ‖W i j‖ ^ 2 ≤ 0 := calc
    _ ≤ ∑ k, ‖W k j‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖W k j‖) (Finset.mem_univ i)
    _ ≤ ∑ l, ∑ k, ‖W k l‖ ^ 2 :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg ‖W k l‖))
        (Finset.mem_univ j)
    _ = 0 := hW
  change W i j = 0
  apply norm_eq_zero.mp
  exact (sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)))

/-- A transfer cannot become zero on the second application unless it
was already zero on the first. -/
theorem abelPerturbationTransfer_twice_eq_zero_iff (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (Y : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    B (B Y) = 0 ↔ B Y = 0 := by
  let B := abelPerturbationTransfer hH ε T
  let W := B Y
  let γ := (hamiltonianAbelShift ε)⁻¹
  change B W = 0 ↔ W = 0
  constructor
  · intro h
    have hF : γ • (T * W - W * T) = 0 := by
      have he := congrArg (hamiltonianAbelInverse H ε) h
      rw [abelPerturbationTransfer_apply, hamiltonianAbelInverse_leftInverse hH ε,
        hamiltonianAbelInverse_eq_sub H ε 0, Matrix.mul_zero, Matrix.zero_mul, sub_self,
        smul_zero, sub_self] at he
      exact he
    have hTW := (smul_eq_zero.mp hF).resolve_left (inv_ne_zero (hamiltonianAbelShift_ne_zero ε))
    have hW : hamiltonianAbelInverse H ε W = γ • (T * Y - Y * T) := by
      change hamiltonianAbelInverse H ε (B Y) = _
      rw [abelPerturbationTransfer_apply, hamiltonianAbelInverse_leftInverse hH ε]
    apply eq_zero_of_hsSqRe_eq_zero W
    rw [← re_trace_conjTranspose_mul_abelInverse hH ε W, hW, Matrix.mul_smul, Matrix.trace_smul,
      trace_conjTranspose_mul_commutator hT W Y, hTW, Matrix.conjTranspose_zero,
      Matrix.zero_mul, Matrix.trace_zero, smul_zero, Complex.zero_re]
  · intro h
    rw [h, map_zero]

/-- The symmetric observation equals the unperturbed reading exactly
when the perturbation commutes with that reading. -/
theorem abelSymmetricResponse_eq_base_iff_commute (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    abelSymmetricResponse hH hT ε X = hamiltonianDampedGapResponse hH 0 ε X ↔
      Commute T (hamiltonianDampedGapResponse hH 0 ε X) := by
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let S := abelSymmetricResponse hH hT ε X
  let B := abelPerturbationTransfer hH ε T
  have he : R = S ↔ R = R + B (B R) := eq_abelSymmetricResponse_iff hH hT ε X R
  have hcomm : B R = 0 ↔ Commute T R := abelResponseVariation_eq_zero_iff_commute hH ε T X
  change S = R ↔ Commute T R
  constructor
  · intro h
    have h0 : B (B R) = 0 := add_left_cancel ((he.mp h.symm).symm.trans (add_zero R).symm)
    exact hcomm.mp ((abelPerturbationTransfer_twice_eq_zero_iff hH hT ε R).mp h0)
  · intro h
    symm
    apply he.mpr
    rw [hcomm.mpr h, map_zero, add_zero]

/-- The antisymmetric reading vanishes under the same commutation
criterion, so it detects the sign of every visible perturbation. -/
theorem abelAntisymmetricResponse_eq_zero_iff_commute (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    abelAntisymmetricResponse hH hT ε X = 0 ↔ Commute T (hamiltonianDampedGapResponse hH 0 ε X) := by
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let S := abelSymmetricResponse hH hT ε X
  let O := abelAntisymmetricResponse hH hT ε X
  let B := abelPerturbationTransfer hH ε T
  obtain ⟨hs, ho⟩ := abelSymmetricAntisymmetricResponse_coupled hH hT ε X
  change S = R + B O at hs
  change O = B S at ho
  change O = 0 ↔ Commute T R
  have hcomm : B R = 0 ↔ Commute T R := abelResponseVariation_eq_zero_iff_commute hH ε T X
  constructor
  · intro h
    rw [h, map_zero, add_zero] at hs
    exact hcomm.mp ((congrArg B hs).symm.trans (ho.symm.trans h))
  · intro h
    have he : S = R := (abelSymmetricResponse_eq_base_iff_commute hH hT ε X).mpr h
    rw [ho, he, hcomm.mpr h]

#print axioms trace_conjTranspose_mul_commutator
#print axioms re_trace_conjTranspose_mul_abelInverse
#print axioms abelSymmetricResponse_eq_base_iff_commute
#print axioms abelAntisymmetricResponse_eq_zero_iff_commute

end

end GaloisForLFunctions.HTGeometry
