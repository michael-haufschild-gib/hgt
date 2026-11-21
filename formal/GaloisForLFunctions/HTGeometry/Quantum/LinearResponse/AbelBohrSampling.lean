import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelBohrPolynomials
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardFibers
import GaloisForLFunctions.HTGeometry.LagrangeNodeBounds

/-!
# Interpolation at the supported Bohr frequencies

Cleared commutators are polynomial in the inverse shift. Distinct
widths recover these polynomials from one more sample than the number
of nonzero gaps carried by the probe.
-/

open Matrix Polynomial Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- The interpolation node belonging to a positive width. -/
def abelWidthNode (ε : Ioi (0 : ℝ)) : ℂ := (hamiltonianAbelShift ε)⁻¹

theorem abelWidthNode_injective : Function.Injective abelWidthNode := by
  intro ε η h
  apply Subtype.ext
  exact congrArg Complex.im (inv_injective h)

/-- The Lagrange weight of the selected width at the inverse shift `γ`. -/
def abelWidthLagrangeWeight {n : ℕ} (widths : Fin n → Ioi (0 : ℝ)) (k : Fin n) (γ : ℂ) : ℂ :=
  ∏ l ∈ Finset.univ.erase k,
    (abelWidthNode (widths k) - abelWidthNode (widths l))⁻¹ * (γ - abelWidthNode (widths l))

/-- The commutator numerator in energy coordinates. -/
def abelBohrCommutatorNumerator (hH : H.IsHermitian) (T X : Matrix ι ι ℂ) :
    Matrix ι ι (Polynomial ℂ) :=
  let A := (hamiltonianEnergyCoordinates hH T).map Polynomial.C
  let B := abelBohrNumerator hH X
  A * B - B * A

theorem natDegree_abelBohrCommutatorNumerator_apply_le (hH : H.IsHermitian)
    (T X : Matrix ι ι ℂ) (i j : ι) :
    (abelBohrCommutatorNumerator hH T X i j).natDegree ≤ (abelProbeBohrGaps hH X).card := by
  rw [abelBohrCommutatorNumerator, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l _ => ?_)
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Matrix.map_apply, Polynomial.natDegree_C, zero_add]
    exact natDegree_abelBohrNumerator_apply_le hH X l j
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l _ => ?_)
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Matrix.map_apply, Polynomial.natDegree_C, add_zero]
    exact natDegree_abelBohrNumerator_apply_le hH X i l

private theorem map_abelBohrCommutatorNumerator (hH : H.IsHermitian) (T X M : Matrix ι ι ℂ)
    (γ : ℂ) (hM : (Polynomial.evalRingHom γ).mapMatrix (abelBohrNumerator hH X) = M) :
    (Polynomial.evalRingHom γ).mapMatrix (abelBohrCommutatorNumerator hH T X) =
      hamiltonianEnergyCoordinates hH T * M - M * hamiltonianEnergyCoordinates hH T := by
  let f := Polynomial.evalRingHom γ
  have hT : f.mapMatrix ((hamiltonianEnergyCoordinates hH T).map Polynomial.C) =
      hamiltonianEnergyCoordinates hH T := Matrix.ext fun _ _ => Polynomial.eval_C
  change f.mapMatrix (_ - _) = _
  rw [map_sub, map_mul, map_mul, hT, hM]

theorem map_abelBohrCommutatorNumerator_zero (hH : H.IsHermitian) (T X : Matrix ι ι ℂ) :
    (Polynomial.evalRingHom 0).mapMatrix (abelBohrCommutatorNumerator hH T X) =
      hamiltonianEnergyCoordinates hH (T * X - X * T) := by
  rw [map_abelBohrCommutatorNumerator hH T X (hamiltonianEnergyCoordinates hH X) 0
    (Matrix.ext (eval_abelBohrNumerator_zero hH X)), map_sub, map_mul, map_mul]

theorem map_abelBohrCommutatorNumerator_width (hH : H.IsHermitian) (T X : Matrix ι ι ℂ)
    (ε : Ioi (0 : ℝ)) :
    (Polynomial.evalRingHom (abelWidthNode ε)).mapMatrix (abelBohrCommutatorNumerator hH T X) =
      (abelBohrDenominator hH X).eval (abelWidthNode ε) •
        hamiltonianEnergyCoordinates hH (T * hamiltonianDampedGapResponse hH 0 ε X -
          hamiltonianDampedGapResponse hH 0 ε X * T) := by
  let γ := abelWidthNode ε
  let q := (abelBohrDenominator hH X).eval γ
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  have hY : (Polynomial.evalRingHom γ).mapMatrix (abelBohrNumerator hH X) =
      q • hamiltonianEnergyCoordinates hH Y := Matrix.ext (eval_abelBohrNumerator hH X ε)
  rw [map_abelBohrCommutatorNumerator hH T X _ γ hY, Matrix.mul_smul, Matrix.smul_mul,
    ← smul_sub, map_sub, map_mul, map_mul]

private theorem interpolate_abelBohrCommutatorNumerator {n : ℕ}
    (hH : H.IsHermitian) (T X : Matrix ι ι ℂ)
    (widths : Fin n → Ioi (0 : ℝ)) (hwidths : Function.Injective widths)
    (hn : (abelProbeBohrGaps hH X).card < n) (γ : ℂ) :
    (Polynomial.evalRingHom γ).mapMatrix (abelBohrCommutatorNumerator hH T X) =
      ∑ k, (abelWidthLagrangeWeight widths k γ *
        (abelBohrDenominator hH X).eval (abelWidthNode (widths k))) •
        hamiltonianEnergyCoordinates hH (T * hamiltonianDampedGapResponse hH 0 (widths k) X -
          hamiltonianDampedGapResponse hH 0 (widths k) X * T) := by
  let W := abelBohrCommutatorNumerator hH T X
  let v := fun k => abelWidthNode (widths k)
  apply Matrix.ext
  intro i j
  have hdeg : (W i j).degree < (n : WithBot ℕ) :=
    (Polynomial.natDegree_le_iff_degree_le.mp
      (natDegree_abelBohrCommutatorNumerator_apply_le hH T X i j)).trans_lt
      (WithBot.coe_lt_coe.mpr hn)
  have he (k : Fin n) : (W i j).eval (v k) =
      (abelBohrDenominator hH X).eval (v k) *
        hamiltonianEnergyCoordinates hH (T * hamiltonianDampedGapResponse hH 0 (widths k) X -
          hamiltonianDampedGapResponse hH 0 (widths k) X * T) i j :=
    congrArg (fun M : Matrix ι ι ℂ => M i j)
      (map_abelBohrCommutatorNumerator_width hH T X (widths k))
  change (W i j).eval γ = _
  rw [eval_eq_sum_lagrange v (abelWidthNode_injective.comp hwidths) _ hdeg γ, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k, Matrix.smul_apply, smul_eq_mul]
  change _ * abelWidthLagrangeWeight widths k γ = _
  ring

/-- Interpolation at inverse shift zero recovers the unfiltered commutator. -/
theorem abelCommuteProbe_eq_sum_width_samples {n : ℕ} (hH : H.IsHermitian)
    (T X : Matrix ι ι ℂ) (widths : Fin n → Ioi (0 : ℝ)) (hwidths : Function.Injective widths)
    (hn : (abelProbeBohrGaps hH X).card < n) :
    T * X - X * T =
      ∑ k, (abelWidthLagrangeWeight widths k 0 *
        (abelBohrDenominator hH X).eval (abelWidthNode (widths k))) •
        (T * hamiltonianDampedGapResponse hH 0 (widths k) X -
          hamiltonianDampedGapResponse hH 0 (widths k) X * T) := by
  have he := interpolate_abelBohrCommutatorNumerator hH T X widths hwidths hn 0
  rw [map_abelBohrCommutatorNumerator_zero] at he
  apply (hamiltonianEnergyCoordinates hH).injective
  change hamiltonianEnergyCoordinates hH _ = hamiltonianEnergyCoordinates hH _
  simpa only [map_sum, map_smul] using he

/-- Interpolation recovers every cleared commutator from the sampled widths. -/
theorem abelCommuteResponse_eq_sum_width_samples {n : ℕ} (hH : H.IsHermitian)
    (T X : Matrix ι ι ℂ) (widths : Fin n → Ioi (0 : ℝ)) (hwidths : Function.Injective widths)
    (hn : (abelProbeBohrGaps hH X).card < n) (ε : Ioi (0 : ℝ)) :
    (abelBohrDenominator hH X).eval (abelWidthNode ε) •
      (T * hamiltonianDampedGapResponse hH 0 ε X - hamiltonianDampedGapResponse hH 0 ε X * T) =
      ∑ k, (abelWidthLagrangeWeight widths k (abelWidthNode ε) *
        (abelBohrDenominator hH X).eval (abelWidthNode (widths k))) •
        (T * hamiltonianDampedGapResponse hH 0 (widths k) X -
          hamiltonianDampedGapResponse hH 0 (widths k) X * T) := by
  have he := interpolate_abelBohrCommutatorNumerator hH T X widths hwidths hn (abelWidthNode ε)
  rw [map_abelBohrCommutatorNumerator_width] at he
  apply (hamiltonianEnergyCoordinates hH).injective
  change hamiltonianEnergyCoordinates hH _ = hamiltonianEnergyCoordinates hH _
  simpa only [map_sum, map_smul] using he

/-- Agreement at one more width than the number of supported nonzero
gaps forces agreement at every positive width. -/
theorem abelForwardReading_eq_all_widths_of_gap_samples {n : ℕ} {K : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (X : Matrix ι ι ℂ)
    (widths : Fin n → Ioi (0 : ℝ)) (hwidths : Function.Injective widths)
    (hn : (abelProbeBohrGaps hH X).card < n)
    (h : ∀ k, hamiltonianDampedGapResponse hH 0 (widths k) X =
      hamiltonianDampedGapResponse hK 0 (widths k) X) (ε : Ioi (0 : ℝ)) :
    hamiltonianDampedGapResponse hH 0 ε X = hamiltonianDampedGapResponse hK 0 ε X := by
  let T := H - K
  have he := abelCommuteResponse_eq_sum_width_samples hH T X widths hwidths hn ε
  have hz (k : Fin n) :
      T * hamiltonianDampedGapResponse hH 0 (widths k) X -
        hamiltonianDampedGapResponse hH 0 (widths k) X * T = 0 :=
    sub_eq_zero.mpr ((abelForwardReading_eq_iff_commute hH hK (widths k) X).mp (h k)).eq
  simp only [hz, smul_zero, Finset.sum_const_zero] at he
  apply (abelForwardReading_eq_iff_commute hH hK ε X).mpr
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left
    (eval_abelBohrDenominator_ne_zero hH X ε))

#print axioms abelCommuteProbe_eq_sum_width_samples
#print axioms abelCommuteResponse_eq_sum_width_samples
#print axioms abelForwardReading_eq_all_widths_of_gap_samples

end

end GaloisForLFunctions.HTGeometry
