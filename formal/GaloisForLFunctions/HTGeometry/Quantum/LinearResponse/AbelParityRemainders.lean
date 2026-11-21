import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelSymmetricResolvent
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelPerturbationBounds
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeStability

/-!
# Norm bounds for parity remainders

The transfer estimate and endpoint contractivity give uniform bounds
on the cubic odd remainder and the quartic even remainder.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H T : Matrix ι ι ℂ}

theorem hsSqRe_abelPerturbationTransfer_le (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T Y : Matrix ι ι ℂ) :
    hsSqRe (abelPerturbationTransfer hH ε T Y) ≤
      (4 * hsSqRe T / (ε : ℝ) ^ 2) * hsSqRe Y := by
  rw [abelPerturbationTransfer_apply]
  refine (hsSqRe_hamiltonianDampedGapResponse_le hH 0 ε _).trans ?_
  rw [hsSqRe_complex_smul, norm_inv, norm_hamiltonianAbelShift, inv_pow]
  calc
    _ ≤ ((ε : ℝ) ^ 2)⁻¹ * ((4 * hsSqRe T) * hsSqRe Y) :=
      mul_le_mul_of_nonneg_left (hsSqRe_commutator_le_hsSqRe T Y)
        (inv_nonneg.mpr (sq_nonneg (ε : ℝ)))
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem hsSqRe_abelPerturbationTransfer_iterate_le (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T Y : Matrix ι ι ℂ) (k : ℕ) :
    hsSqRe ((abelPerturbationTransfer hH ε T)^[k] Y) ≤
      (4 * hsSqRe T / (ε : ℝ) ^ 2) ^ k * hsSqRe Y := by
  let L := 4 * hsSqRe T / (ε : ℝ) ^ 2
  have hL : 0 ≤ L :=
    div_nonneg (mul_nonneg (by positivity) (hsSqRe_nonneg T)) (sq_nonneg (ε : ℝ))
  change _ ≤ L ^ k * hsSqRe Y
  induction k with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul, le_refl]
  | succ k hk =>
      rw [Function.iterate_succ_apply', pow_succ' L k, mul_assoc]
      exact (hsSqRe_abelPerturbationTransfer_le hH ε T _).trans (mul_le_mul_of_nonneg_left hk hL)

theorem hsSqRe_abelSymmetricResponse_le (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hsSqRe (abelSymmetricResponse hH hT ε X) ≤ hsSqRe X := by
  let Yp := hamiltonianDampedGapResponse (hH.add hT) 0 ε X
  let Ym := hamiltonianDampedGapResponse (hH.sub hT) 0 ε X
  have hn : hsSqRe (-Ym) = hsSqRe Ym := by
    simp only [hsSqRe_eq_sum, Matrix.neg_apply, norm_neg]
  have hsum : hsSqRe (Yp + Ym) ≤ 2 * hsSqRe Yp + 2 * hsSqRe Ym := by
    have he := hsSqRe_sub_le Yp (-Ym)
    rwa [sub_neg_eq_add, hn] at he
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := Complex.norm_natCast 2
  change hsSqRe ((2 : ℂ)⁻¹ • (Yp + Ym)) ≤ _
  rw [hsSqRe_complex_smul, norm_inv, htwo]
  calc
    _ ≤ (2 : ℝ)⁻¹ ^ 2 * (2 * hsSqRe Yp + 2 * hsSqRe Ym) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ (2 : ℝ)⁻¹ ^ 2 * (2 * hsSqRe X + 2 * hsSqRe X) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact add_le_add (mul_le_mul_of_nonneg_left
        (hsSqRe_hamiltonianDampedGapResponse_le (hH.add hT) 0 ε X) zero_le_two)
        (mul_le_mul_of_nonneg_left
          (hsSqRe_hamiltonianDampedGapResponse_le (hH.sub hT) 0 ε X) zero_le_two)
    _ = _ := by ring

/-- The squared Hilbert–Schmidt energy of the even remainder is
bounded by the eighth power of the perturbation norm. -/
theorem hsSqRe_abelSymmetricResponse_fourth_remainder_le
    (hH : H.IsHermitian) (hT : T.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    let R := hamiltonianDampedGapResponse hH 0 ε X
    hsSqRe (abelSymmetricResponse hH hT ε X - R - B (B R)) ≤
      (4 * hsSqRe T / (ε : ℝ) ^ 2) ^ 4 * hsSqRe X := by
  let B := abelPerturbationTransfer hH ε T
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let S := abelSymmetricResponse hH hT ε X
  let L := 4 * hsSqRe T / (ε : ℝ) ^ 2
  have hL : 0 ≤ L :=
    div_nonneg (mul_nonneg (by positivity) (hsSqRe_nonneg T)) (sq_nonneg (ε : ℝ))
  change hsSqRe (S - R - B (B R)) ≤ L ^ 4 * hsSqRe X
  have he : S - R - B (B R) = B (B (B (B S))) := abelSymmetricResponse_fourth_remainder hH hT ε X
  rw [he]
  have hb := hsSqRe_abelPerturbationTransfer_iterate_le hH ε T S 4
  change hsSqRe (B (B (B (B S)))) ≤ L ^ 4 * hsSqRe S at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hsSqRe_abelSymmetricResponse_le hH hT ε X)
    (pow_nonneg hL _))

/-- The squared Hilbert–Schmidt energy of the odd remainder is
bounded by the sixth power of the perturbation norm. -/
theorem hsSqRe_abelAntisymmetricResponse_cubic_remainder_le
    (hH : H.IsHermitian) (hT : T.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    let B := abelPerturbationTransfer hH ε T
    let R := hamiltonianDampedGapResponse hH 0 ε X
    hsSqRe (abelAntisymmetricResponse hH hT ε X - B R) ≤
      (4 * hsSqRe T / (ε : ℝ) ^ 2) ^ 3 * hsSqRe X := by
  let B := abelPerturbationTransfer hH ε T
  let R := hamiltonianDampedGapResponse hH 0 ε X
  let S := abelSymmetricResponse hH hT ε X
  let L := 4 * hsSqRe T / (ε : ℝ) ^ 2
  have hL : 0 ≤ L :=
    div_nonneg (mul_nonneg (by positivity) (hsSqRe_nonneg T)) (sq_nonneg (ε : ℝ))
  change hsSqRe (abelAntisymmetricResponse hH hT ε X - B R) ≤ L ^ 3 * hsSqRe X
  have he : abelAntisymmetricResponse hH hT ε X - B R = B (B (B S)) :=
    abelAntisymmetricResponse_cubic_remainder hH hT ε X
  rw [he]
  have hb := hsSqRe_abelPerturbationTransfer_iterate_le hH ε T S 3
  change hsSqRe (B (B (B S))) ≤ L ^ 3 * hsSqRe S at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hsSqRe_abelSymmetricResponse_le hH hT ε X)
    (pow_nonneg hL _))

#print axioms hsSqRe_abelSymmetricResponse_fourth_remainder_le
#print axioms hsSqRe_abelAntisymmetricResponse_cubic_remainder_le

end

end GaloisForLFunctions.HTGeometry
