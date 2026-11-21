import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelResponsePerturbation

/-!
# The even and odd parts of a perturbed resolvent

Averaging the responses at opposite perturbations eliminates the
linear term. Their mean solves an exact Schur-complement equation in
the square of the perturbation transfer.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H K T : Matrix ι ι ℂ}

/-- A commutator with the perturbation, followed by the base response. -/
def abelPerturbationTransfer (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (T : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  (abelResponseLinearEquiv hH ε).toLinearMap.comp
    (show Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ from {
      toFun := fun Y => (hamiltonianAbelShift ε)⁻¹ • (T * Y - Y * T)
      map_add' := by
        intro Y Z
        rw [Matrix.mul_add, Matrix.add_mul, add_sub_add_comm, smul_add]
      map_smul' := by
        intro c Y
        simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub c]
        rw [smul_comm (hamiltonianAbelShift ε)⁻¹ c] })

theorem abelPerturbationTransfer_apply (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T Y : Matrix ι ι ℂ) :
    abelPerturbationTransfer hH ε T Y =
      hamiltonianDampedGapResponse hH 0 ε ((hamiltonianAbelShift ε)⁻¹ • (T * Y - Y * T)) := rfl

theorem abelPerturbationTransfer_neg_apply (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T Y : Matrix ι ι ℂ) :
    abelPerturbationTransfer hH ε (-T) Y = -abelPerturbationTransfer hH ε T Y := by
  have h : (-T) * Y - Y * (-T) = -(T * Y - Y * T) := by
    rw [Matrix.neg_mul, Matrix.mul_neg]
    abel
  rw [abelPerturbationTransfer_apply, abelPerturbationTransfer_apply, h, smul_neg]
  exact (abelResponseLinearEquiv hH ε).map_neg _

/-- The response at a perturbed Hamiltonian solves a fixed-point
equation formed from the base response. -/
theorem eq_abelResponse_iff_base_add_transfer (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X Y : Matrix ι ι ℂ) :
    Y = hamiltonianDampedGapResponse hK 0 ε X ↔
      Y = hamiltonianDampedGapResponse hH 0 ε X + abelPerturbationTransfer hH ε (K - H) Y := by
  let R := abelResponseLinearEquiv hH ε
  let F := (hamiltonianAbelShift ε)⁻¹ • ((K - H) * Y - Y * (K - H))
  have hInv : hamiltonianAbelInverse K ε Y = hamiltonianAbelInverse H ε Y - F := by
    simp only [hamiltonianAbelInverse_eq_sub, F, Matrix.sub_mul, Matrix.mul_sub, smul_sub]
    abel
  have hR : R.symm (R X + abelPerturbationTransfer hH ε (K - H) Y) = X + F := by
    change R.symm (R X + R F) = _
    rw [map_add, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  calc
    _ ↔ hamiltonianAbelInverse K ε Y = X :=
      eq_comm.trans (dampedGapResponse_zero_eq_iff_abelInverse_eq hK ε X Y)
    _ ↔ hamiltonianAbelInverse H ε Y = X + F := by
      rw [hInv, sub_eq_iff_eq_add]
    _ ↔ _ := by
      change R.symm Y = X + F ↔ Y = R X + abelPerturbationTransfer hH ε (K - H) Y
      rw [← hR]
      exact R.symm.injective.eq_iff

/-- The mean of the two opposite perturbation readings. -/
def abelSymmetricResponse (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (hamiltonianDampedGapResponse (hH.add hT) 0 ε X +
    hamiltonianDampedGapResponse (hH.sub hT) 0 ε X)

/-- The half-difference of the two opposite perturbation readings. -/
def abelAntisymmetricResponse (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (hamiltonianDampedGapResponse (hH.add hT) 0 ε X -
    hamiltonianDampedGapResponse (hH.sub hT) 0 ε X)

theorem abelSymmetricAntisymmetricResponse_coupled (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    let S := abelSymmetricResponse hH hT ε X
    let O := abelAntisymmetricResponse hH hT ε X
    S = hamiltonianDampedGapResponse hH 0 ε X + B O ∧ O = B S := by
  let B := abelPerturbationTransfer hH ε T
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let Yp := hamiltonianDampedGapResponse (hH.add hT) 0 ε X
  let Ym := hamiltonianDampedGapResponse (hH.sub hT) 0 ε X
  have hp : Yp = R + B Yp := by
    have he := (eq_abelResponse_iff_base_add_transfer hH (hH.add hT) ε X Yp).mp rfl
    rw [show H + T - H = T from by abel] at he
    exact he
  have hm : Ym = R - B Ym := by
    have he := (eq_abelResponse_iff_base_add_transfer hH (hH.sub hT) ε X Ym).mp rfl
    rw [show H - T - H = -T from by abel, abelPerturbationTransfer_neg_apply, ← sub_eq_add_neg] at he
    exact he
  have hs : Yp + Ym = (2 : ℂ) • R + (B Yp - B Ym) := by
    calc
      _ = (R + B Yp) + (R - B Ym) := congrArg₂ (· + ·) hp hm
      _ = _ := by rw [two_smul]; abel
  have hd : Yp - Ym = B Yp + B Ym := by
    calc
      _ = (R + B Yp) - (R - B Ym) := congrArg₂ (· - ·) hp hm
      _ = _ := by abel
  constructor
  · change (2 : ℂ)⁻¹ • (Yp + Ym) = R + B ((2 : ℂ)⁻¹ • (Yp - Ym))
    rw [map_smul, map_sub, hs, smul_add, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  · change (2 : ℂ)⁻¹ • (Yp - Ym) = B ((2 : ℂ)⁻¹ • (Yp + Ym))
    rw [map_smul, map_add, hd]

/-- The even response is the unique solution of its Schur-complement
equation. -/
theorem eq_abelSymmetricResponse_iff (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X Y : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    Y = abelSymmetricResponse hH hT ε X ↔
      Y = hamiltonianDampedGapResponse hH 0 ε X + B (B Y) := by
  let B := abelPerturbationTransfer hH ε T
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let S := abelSymmetricResponse hH hT ε X
  change Y = S ↔ Y = R + B (B Y)
  constructor
  · rintro rfl
    obtain ⟨he, ho⟩ := abelSymmetricAntisymmetricResponse_coupled hH hT ε X
    exact he.trans (congrArg (fun Z => R + B Z) ho)
  · intro h
    have hp : Y + B Y = hamiltonianDampedGapResponse (hH.add hT) 0 ε X := by
      apply (eq_abelResponse_iff_base_add_transfer hH (hH.add hT) ε X _).mpr
      rw [show H + T - H = T from by abel]
      change Y + B Y = R + B (Y + B Y)
      calc
        _ = (R + B (B Y)) + B Y := congrArg (fun Z => Z + B Y) h
        _ = _ := by rw [map_add]; abel
    have hm : Y - B Y = hamiltonianDampedGapResponse (hH.sub hT) 0 ε X := by
      apply (eq_abelResponse_iff_base_add_transfer hH (hH.sub hT) ε X _).mpr
      rw [show H - T - H = -T from by abel, abelPerturbationTransfer_neg_apply, ← sub_eq_add_neg]
      change Y - B Y = R - B (Y - B Y)
      calc
        _ = (R + B (B Y)) - B Y := congrArg (fun Z => Z - B Y) h
        _ = _ := by rw [map_sub]; abel
    change Y = (2 : ℂ)⁻¹ •
      (hamiltonianDampedGapResponse (hH.add hT) 0 ε X + hamiltonianDampedGapResponse (hH.sub hT) 0 ε X)
    rw [← hp, ← hm, show Y + B Y + (Y - B Y) = (2 : ℂ) • Y from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- Subtracting the base reading leaves the exact second-order feedback. -/
theorem abelSymmetricResponse_sub_base (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    let S := abelSymmetricResponse hH hT ε X
    S - hamiltonianDampedGapResponse hH 0 ε X = B (B S) := by
  have he := (eq_abelSymmetricResponse_iff hH hT ε X (abelSymmetricResponse hH hT ε X)).mp rfl
  exact sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))

/-- After the quadratic term, the even remainder is exactly fourth order. -/
theorem abelSymmetricResponse_fourth_remainder (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    let R := hamiltonianDampedGapResponse hH 0 ε X
    let S := abelSymmetricResponse hH hT ε X
    S - R - B (B R) = B (B (B (B S))) := by
  let B := abelPerturbationTransfer hH ε T
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let S := abelSymmetricResponse hH hT ε X
  have he : S - R = B (B S) := abelSymmetricResponse_sub_base hH hT ε X
  change S - R - B (B R) = _
  calc
    _ = B (B S) - B (B R) := congrArg (fun Z => Z - B (B R)) he
    _ = B (B (S - R)) := by rw [map_sub B S R, map_sub B (B S) (B R)]
    _ = _ := congrArg (fun Z => B (B Z)) he

/-- The odd response keeps the linear variation with an exact cubic remainder. -/
theorem abelAntisymmetricResponse_cubic_remainder (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    let R := hamiltonianDampedGapResponse hH 0 ε X
    let S := abelSymmetricResponse hH hT ε X
    abelAntisymmetricResponse hH hT ε X - B R = B (B (B S)) := by
  let B := abelPerturbationTransfer hH ε T
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let S := abelSymmetricResponse hH hT ε X
  obtain ⟨_, ho⟩ := abelSymmetricAntisymmetricResponse_coupled hH hT ε X
  change abelAntisymmetricResponse hH hT ε X = B S at ho
  change abelAntisymmetricResponse hH hT ε X - B R = _
  rw [ho, ← map_sub, abelSymmetricResponse_sub_base hH hT ε X]

#print axioms eq_abelResponse_iff_base_add_transfer
#print axioms abelSymmetricAntisymmetricResponse_coupled
#print axioms eq_abelSymmetricResponse_iff
#print axioms abelSymmetricResponse_fourth_remainder
#print axioms abelAntisymmetricResponse_cubic_remainder

end

end GaloisForLFunctions.HTGeometry
