import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel
import GaloisForLFunctions.HTGeometry.RealPositiveConeDeterminantMonotone

/-!
# First-two-atom lower bounds for every shifted theta Hankel determinant

The full theta source and its first two integer atoms define positive weighted Gram matrices
on the positive logarithmic half-line.  The exact tail past the second atom is pointwise
nonnegative there.  Integrating its rank-one matrix kernel gives a positive semidefinite
matrix at every size, so determinant monotonicity retains the two-atom determinant as an
unconditional lower bound for the full source.  No moment-by-moment interval estimate is used.
-/

open MeasureTheory Set Matrix
namespace RHTower
noncomputable section

private theorem thetaTail_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ thetaCuspFullSource x - thetaCuspSourceTerm x 1 - thetaCuspSourceTerm x 2 := by
  have hs := summable_thetaCuspSourceTerm x
  have ht : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 3)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hhead : (∑ n ∈ Finset.range 3, thetaCuspSourceTerm x n) =
      thetaCuspSourceTerm x 1 + thetaCuspSourceTerm x 2 := by
    simp [Finset.sum_range_succ, thetaCuspSourceTerm, thetaCuspSeed]
  have heq : thetaCuspFullSource x - thetaCuspSourceTerm x 1 -
      thetaCuspSourceTerm x 2 =
      ∑' k : ℕ, thetaCuspSourceTerm x (k + 3) := by
    rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 3, hhead]
    ring
  rw [heq]
  exact tsum_nonneg (fun k => thetaCuspSourceTerm_nonneg_of_pos hx (k + 3))

/-- The raw even moment of a half-line density before normalization. -/
def weightedRawEvenMoment (w : ℝ → ℝ) (j : ℕ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) * w x

private def weightedShiftedKernel (w : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (if 0 < x then 2 * w x else 0) •
    Matrix.vecMulVec (fun i : Fin n => x ^ (2 * (i : ℕ) + 1))
      (fun i : Fin n => x ^ (2 * (i : ℕ) + 1))

private theorem weightedShiftedKernel_posSemidef
    (w : ℝ → ℝ) (n : ℕ) (hw : ∀ x, 0 < x → 0 ≤ w x) (x : ℝ) :
    (weightedShiftedKernel w n x).PosSemidef := by
  classical
  by_cases hx : 0 < x
  · have hbase : (Matrix.vecMulVec
        (fun i : Fin n => x ^ (2 * (i : ℕ) + 1))
        (fun i : Fin n => x ^ (2 * (i : ℕ) + 1))).PosSemidef := by
      simpa only [star_trivial] using
        Matrix.posSemidef_vecMulVec_self_star
          (fun i : Fin n => x ^ (2 * (i : ℕ) + 1))
    simpa only [weightedShiftedKernel, if_pos hx] using
      hbase.smul (mul_nonneg (by norm_num) (hw x hx))
  · simpa [weightedShiftedKernel, hx] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)

private theorem weightedShiftedKernel_entry_integrable
    (w : ℝ → ℝ) (n : ℕ)
    (hw : ∀ j, IntegrableOn (fun x : ℝ => x ^ (2 * j) * w x) (Ioi 0))
    (i j : Fin n) :
    Integrable (fun x => weightedShiftedKernel w n x i j)
      (volume.restrict (Ioi 0)) := by
  have h := (hw ((i : ℕ) + (j : ℕ) + 1)).const_mul 2
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 0 < x := hx
  simp only [weightedShiftedKernel, if_pos hx', Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have he : (2 * (i : ℕ) + 1) + (2 * (j : ℕ) + 1) =
      2 * ((i : ℕ) + (j : ℕ) + 1) := by omega
  rw [← pow_add, he]
  ring

private theorem weightedShiftedHankel_posSemidef
    (w : ℝ → ℝ) (n : ℕ)
    (hw : ∀ j, IntegrableOn (fun x : ℝ => x ^ (2 * j) * w x) (Ioi 0))
    (hn : ∀ x, 0 < x → 0 ≤ w x) :
    (HTGeometry.momentHankelMatrix (weightedRawEvenMoment w ∘ Nat.succ) n).PosSemidef := by
  classical
  have hk := HTGeometry.integralMatrixKernel_posSemidef
    (volume.restrict (Ioi 0)) (weightedShiftedKernel w n)
    (weightedShiftedKernel_entry_integrable w n hw)
    (weightedShiftedKernel_posSemidef w n hn)
  convert hk using 1
  ext i j
  change weightedRawEvenMoment w ((i : ℕ) + (j : ℕ) + 1) =
    ∫ x in Ioi (0 : ℝ), weightedShiftedKernel w n x i j
  rw [weightedRawEvenMoment, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 0 < x := hx
  simp only [weightedShiftedKernel, if_pos hx', Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have he : (2 * (i : ℕ) + 1) + (2 * (j : ℕ) + 1) =
      2 * ((i : ℕ) + (j : ℕ) + 1) := by omega
  rw [← pow_add, he]
  ring

private theorem weightedRawEvenMoment_sub
    (w v : ℝ → ℝ) (j : ℕ)
    (hw : IntegrableOn (fun x : ℝ => x ^ (2 * j) * w x) (Ioi 0))
    (hv : IntegrableOn (fun x : ℝ => x ^ (2 * j) * v x) (Ioi 0)) :
    weightedRawEvenMoment (fun x => v x - w x) j =
      weightedRawEvenMoment v j - weightedRawEvenMoment w j := by
  unfold weightedRawEvenMoment
  have heq : (fun x : ℝ => x ^ (2 * j) * (v x - w x)) =
      (fun x => x ^ (2 * j) * v x) - (fun x => x ^ (2 * j) * w x) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  change 2 * (∫ x : ℝ in Ioi 0,
      x ^ (2 * j) * v x - x ^ (2 * j) * w x) = _
  rw [integral_sub hv hw]
  ring

/-- Pointwise domination of nonnegative half-line densities increases every shifted Hankel
determinant. -/
theorem weightedShiftedHankel_det_mono
    (w v : ℝ → ℝ) (n : ℕ)
    (hw : ∀ j, IntegrableOn (fun x : ℝ => x ^ (2 * j) * w x) (Ioi 0))
    (hv : ∀ j, IntegrableOn (fun x : ℝ => x ^ (2 * j) * v x) (Ioi 0))
    (hwn : ∀ x, 0 < x → 0 ≤ w x)
    (hvw : ∀ x, 0 < x → 0 ≤ v x - w x) :
    (HTGeometry.momentHankelMatrix (weightedRawEvenMoment w ∘ Nat.succ) n).det ≤
      (HTGeometry.momentHankelMatrix (weightedRawEvenMoment v ∘ Nat.succ) n).det := by
  classical
  have hdint : ∀ j, IntegrableOn
      (fun x : ℝ => x ^ (2 * j) * (v x - w x)) (Ioi 0) := by
    intro j
    apply ((hv j).sub (hw j)).congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  have hA := weightedShiftedHankel_posSemidef w n hw hwn
  have hC := weightedShiftedHankel_posSemidef v n hv (by
    intro x hx
    have h₁ := hwn x hx
    have h₂ := hvw x hx
    linarith)
  have hDiff := weightedShiftedHankel_posSemidef
    (fun x => v x - w x) n hdint hvw
  have hEq : HTGeometry.momentHankelMatrix
      (weightedRawEvenMoment v ∘ Nat.succ) n -
      HTGeometry.momentHankelMatrix
      (weightedRawEvenMoment w ∘ Nat.succ) n =
      HTGeometry.momentHankelMatrix
      (weightedRawEvenMoment (fun x => v x - w x) ∘ Nat.succ) n := by
    ext i j
    exact (weightedRawEvenMoment_sub w v ((i : ℕ) + (j : ℕ) + 1)
      (hw _) (hv _)).symm
  exact GaloisForLFunctions.HTGeometry.real_det_le_det_of_loewner
    hA hC (hEq ▸ hDiff)

theorem firstTwoAtom_shiftedRawHankel_det_le_full (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (fun j => thetaCuspAtomRawEvenMoment (j + 1) 1 +
        thetaCuspAtomRawEvenMoment (j + 1) 2) n).det ≤
    (HTGeometry.momentHankelMatrix
      (fun j => thetaCuspRawEvenMoment (j + 1)) n).det := by
  let w : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1 + thetaCuspSourceTerm x 2
  have hw : ∀ j, IntegrableOn (fun x : ℝ => x ^ (2 * j) * w x) (Ioi 0) := by
    intro j
    apply ((integrableOn_pow_mul_thetaCuspSourceTerm j 1).add
      (integrableOn_pow_mul_thetaCuspSourceTerm j 2)).congr
    filter_upwards [] with x
    dsimp [w]
    ring
  have hv : ∀ j, IntegrableOn
      (fun x : ℝ => x ^ (2 * j) * thetaCuspFullSource x) (Ioi 0) := by
    intro j
    exact integrableOn_thetaCuspRawMoment (2 * j)
  have hwn : ∀ x, 0 < x → 0 ≤ w x := by
    intro x hx
    exact add_nonneg (thetaCuspSourceTerm_nonneg_of_pos hx 1)
      (thetaCuspSourceTerm_nonneg_of_pos hx 2)
  have hvw : ∀ x, 0 < x → 0 ≤ thetaCuspFullSource x - w x := by
    intro x hx
    dsimp [w]
    convert thetaTail_nonneg hx using 1
    ring
  have hmono := weightedShiftedHankel_det_mono w thetaCuspFullSource n hw hv hwn hvw
  have hheadMom (j : ℕ) : weightedRawEvenMoment w j =
      thetaCuspAtomRawEvenMoment j 1 + thetaCuspAtomRawEvenMoment j 2 := by
    unfold weightedRawEvenMoment thetaCuspAtomRawEvenMoment
    have heq : (fun x : ℝ => x ^ (2 * j) * w x) =
        (fun x => x ^ (2 * j) * thetaCuspSourceTerm x 1) +
        (fun x => x ^ (2 * j) * thetaCuspSourceTerm x 2) := by
      funext x
      dsimp [w]
      ring
    rw [heq]
    change 2 * (∫ x : ℝ in Ioi 0,
      x ^ (2 * j) * thetaCuspSourceTerm x 1 +
      x ^ (2 * j) * thetaCuspSourceTerm x 2) = _
    rw [integral_add
      (integrableOn_pow_mul_thetaCuspSourceTerm j 1)
      (integrableOn_pow_mul_thetaCuspSourceTerm j 2)]
    ring
  convert hmono using 1
  · congr 1
    ext i j
    simp only [HTGeometry.momentHankelMatrix, Function.comp_apply, hheadMom]
  · rfl

end
end RHTower
