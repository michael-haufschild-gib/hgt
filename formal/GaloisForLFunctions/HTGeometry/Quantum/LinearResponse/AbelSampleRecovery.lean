import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelSampleStability
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelWidthScaling

/-!
# Stable recovery relative to a diagonal anchor

Diagonal and all-ones probes may be sampled on different schedules.
The diagonal probe controls off-diagonal entries. One entry of the
all-ones commutator then controls each diagonal difference.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d n m : ℕ} {H K : Matrix (Fin d) (Fin d) ℂ}

private def sampleRecoveryUnitWidth : Ioi (0 : ℝ) :=
  ⟨1, by
    change (0 : ℝ) < 1
    exact zero_lt_one⟩

private theorem norm_abelInverse_unit_sub_zero_apply (T X : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    ‖hamiltonianAbelInverse T sampleRecoveryUnitWidth X i j -
      hamiltonianAbelInverse 0 sampleRecoveryUnitWidth X i j‖ =
      ‖(T * X - X * T) i j‖ := by
  let z := hamiltonianAbelShift sampleRecoveryUnitWidth
  rw [hamiltonianAbelInverse_eq_sub, hamiltonianAbelInverse_eq_sub,
    Matrix.zero_mul, Matrix.mul_zero, sub_self, smul_zero, sub_zero]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  change ‖X i j - z⁻¹ * (T * X - X * T) i j - X i j‖ = _
  rw [show X i j - z⁻¹ * (T * X - X * T) i j - X i j =
      -(z⁻¹ * (T * X - X * T) i j) from by abel,
    norm_neg, norm_mul, norm_inv, norm_hamiltonianAbelShift]
  change (1 : ℝ)⁻¹ * ‖(T * X - X * T) i j‖ = _
  rw [inv_one, one_mul, Matrix.sub_apply]

/-- An off-diagonal error is controlled by the sampled diagonal probe alone. -/
theorem norm_abelAnchoredDifference_offDiag_le (o : Fin d)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (widths : Fin n → Ioi (0 : ℝ)) (hwidths : Function.Injective widths)
    (hn : (abelProbeBohrGaps hH (abelDiagonalProbe d)).card < n) (δ : Fin n → ℝ)
    (hδ : ∀ k i j, ‖(hamiltonianDampedGapResponse hK 0 (widths k) (abelDiagonalProbe d) -
        hamiltonianDampedGapResponse hH 0 (widths k) (abelDiagonalProbe d)) i j‖ ≤ δ k)
    {i j : Fin d} (hij : i ≠ j) :
    ‖((K - H) - (K - H) o o • 1) i j‖ ≤
      abelSampleReadoutBound hH K (abelDiagonalProbe d) widths δ i j := by
  let T := K - H
  let D := abelDiagonalProbe d
  let J := abelSumProbe d
  have he := norm_abelRelativeRecovery_sub_apply_le_of_ne o sampleRecoveryUnitWidth
    (hamiltonianAbelInverse T sampleRecoveryUnitWidth (abelDiagonalProbe d))
    (hamiltonianAbelInverse T sampleRecoveryUnitWidth (abelSumProbe d))
    (hamiltonianAbelInverse 0 sampleRecoveryUnitWidth (abelDiagonalProbe d))
    (hamiltonianAbelInverse 0 sampleRecoveryUnitWidth (abelSumProbe d)) hij
  rw [abelRelativeRecovery_exact, abelRelativeRecovery_exact] at he
  simp only [norm_abelInverse_unit_sub_zero_apply] at he
  have hb : ‖(T - T o o • 1) i j‖ ≤ ‖(T * D - D * T) i j‖ := by
    simpa only [sampleRecoveryUnitWidth, Subtype.coe_mk, Matrix.zero_apply, zero_smul,
      sub_zero, one_mul] using he
  exact hb.trans
    (norm_abelCommuteProbe_apply_le_of_width_samples hH hK D widths hwidths hn δ hδ i j)

/-- Diagonal error uses the row and anchor column of the diagonal-probe
bound and one entry of the independently sampled all-ones probe. -/
theorem norm_abelAnchoredDifference_diag_le (o : Fin d)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (widthsD : Fin n → Ioi (0 : ℝ)) (hD : Function.Injective widthsD)
    (widthsJ : Fin m → Ioi (0 : ℝ)) (hJ : Function.Injective widthsJ)
    (hn : (abelProbeBohrGaps hH (abelDiagonalProbe d)).card < n)
    (hm : (abelProbeBohrGaps hH (abelSumProbe d)).card < m) (δD : Fin n → ℝ) (δJ : Fin m → ℝ)
    (hδD : ∀ k i j, ‖(hamiltonianDampedGapResponse hK 0 (widthsD k) (abelDiagonalProbe d) -
        hamiltonianDampedGapResponse hH 0 (widthsD k) (abelDiagonalProbe d)) i j‖ ≤ δD k)
    (hδJ : ∀ k i j, ‖(hamiltonianDampedGapResponse hK 0 (widthsJ k) (abelSumProbe d) -
        hamiltonianDampedGapResponse hH 0 (widthsJ k) (abelSumProbe d)) i j‖ ≤ δJ k)
    (i : Fin d) :
    ‖((K - H) - (K - H) o o • 1) i i‖ ≤
      abelSampleReadoutBound hH K (abelSumProbe d) widthsJ δJ i o +
      (∑ k, abelSampleReadoutBound hH K (abelDiagonalProbe d) widthsD δD i k) +
      ∑ k, abelSampleReadoutBound hH K (abelDiagonalProbe d) widthsD δD k o := by
  let T := K - H
  let D := abelDiagonalProbe d
  let J := abelSumProbe d
  have he := norm_abelRelativeRecovery_sub_diag_le o sampleRecoveryUnitWidth
    (hamiltonianAbelInverse T sampleRecoveryUnitWidth (abelDiagonalProbe d))
    (hamiltonianAbelInverse T sampleRecoveryUnitWidth (abelSumProbe d))
    (hamiltonianAbelInverse 0 sampleRecoveryUnitWidth (abelDiagonalProbe d))
    (hamiltonianAbelInverse 0 sampleRecoveryUnitWidth (abelSumProbe d)) i
  rw [abelRelativeRecovery_exact, abelRelativeRecovery_exact] at he
  simp only [norm_abelInverse_unit_sub_zero_apply] at he
  have hb : ‖(T - T o o • 1) i i‖ ≤
      ‖(T * J - J * T) i o‖ + (∑ k, ‖(T * D - D * T) i k‖) +
        ∑ k, ‖(T * D - D * T) k o‖ := by
    simpa only [sampleRecoveryUnitWidth, Subtype.coe_mk, Matrix.zero_apply, zero_smul,
      sub_zero, one_mul] using he
  have hd := norm_abelCommuteProbe_apply_le_of_width_samples hH hK D widthsD hD hn δD hδD
  have hj := norm_abelCommuteProbe_apply_le_of_width_samples hH hK J widthsJ hJ hm δJ hδJ
  exact hb.trans (add_le_add (add_le_add (hj i o) (Finset.sum_le_sum fun k _ => hd i k))
    (Finset.sum_le_sum fun k _ => hd k o))

/-- The two schedules determine the Hamiltonian up to a real scalar as
soon as each exceeds the gap count of its own probe. -/
theorem abelForwardReadings_eq_scalarDifference_of_gap_samples (o : Fin d)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (widthsD : Fin n → Ioi (0 : ℝ)) (hD : Function.Injective widthsD)
    (widthsJ : Fin m → Ioi (0 : ℝ)) (hJ : Function.Injective widthsJ)
    (hn : (abelProbeBohrGaps hH (abelDiagonalProbe d)).card < n)
    (hm : (abelProbeBohrGaps hH (abelSumProbe d)).card < m)
    (hd : ∀ k, hamiltonianDampedGapResponse hH 0 (widthsD k) (abelDiagonalProbe d) =
      hamiltonianDampedGapResponse hK 0 (widthsD k) (abelDiagonalProbe d))
    (hj : ∀ k, hamiltonianDampedGapResponse hH 0 (widthsJ k) (abelSumProbe d) =
      hamiltonianDampedGapResponse hK 0 (widthsJ k) (abelSumProbe d)) :
    ∃ c : ℝ, H - K = (c : ℂ) • 1 := by
  let T := H - K
  let ε := sampleRecoveryUnitWidth
  have hinv {p : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (widths : Fin p → Ioi (0 : ℝ))
      (hw : Function.Injective widths) (hsize : (abelProbeBohrGaps hH X).card < p)
      (h : ∀ k, hamiltonianDampedGapResponse hH 0 (widths k) X =
        hamiltonianDampedGapResponse hK 0 (widths k) X) :
      hamiltonianAbelInverse T ε X = hamiltonianAbelInverse 0 ε X := by
    have hc (k : Fin p) :
        T * hamiltonianDampedGapResponse hH 0 (widths k) X -
          hamiltonianDampedGapResponse hH 0 (widths k) X * T = 0 :=
      sub_eq_zero.mpr ((abelForwardReading_eq_iff_commute hH hK (widths k) X).mp (h k)).eq
    have he := abelCommuteProbe_eq_sum_width_samples hH T X widths hw hsize
    simp only [hc, smul_zero, Finset.sum_const_zero] at he
    apply (hamiltonianAbelInverse_eq_iff_commutators T 0 ε X).mpr
    rw [Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    exact he
  obtain ⟨c, hc⟩ := (abelProbeReadings_eq_iff_scalarDifference o T 0 ε).mp
    ⟨hinv _ widthsD hD hn hd, hinv _ widthsJ hJ hm hj⟩
  apply (hermitian_scalarDifference_iff_real o hH hK).mp
  exact ⟨c, by simpa only [sub_zero] using hc⟩

/-- A uniform schedule of `d² - d + 1` widths suffices in dimension `d`. -/
theorem abelForwardReadings_eq_scalarDifference_of_offDiag_count (o : Fin d)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (widths : Fin n → Ioi (0 : ℝ)) (hw : Function.Injective widths)
    (hn : d * d - d < n)
    (h : ∀ k, hamiltonianDampedGapResponse hH 0 (widths k) (abelDiagonalProbe d) =
        hamiltonianDampedGapResponse hK 0 (widths k) (abelDiagonalProbe d) ∧
      hamiltonianDampedGapResponse hH 0 (widths k) (abelSumProbe d) =
        hamiltonianDampedGapResponse hK 0 (widths k) (abelSumProbe d)) :
    ∃ c : ℝ, H - K = (c : ℂ) • 1 := by
  have hc (X : Matrix (Fin d) (Fin d) ℂ) : (abelProbeBohrGaps hH X).card < n := by
    have he := card_abelProbeBohrGaps_le hH X
    rw [Fintype.card_fin] at he
    exact he.trans_lt hn
  exact abelForwardReadings_eq_scalarDifference_of_gap_samples o hH hK widths hw widths hw
    (hc _) (hc _) (fun k => (h k).1) (fun k => (h k).2)

#print axioms norm_abelAnchoredDifference_offDiag_le
#print axioms norm_abelAnchoredDifference_diag_le
#print axioms abelForwardReadings_eq_scalarDifference_of_offDiag_count

end

end GaloisForLFunctions.HTGeometry
