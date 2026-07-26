/-
# Dual frequencies under osculating phase coordinates

Linear changes of physical phase variables act contragrediently on frequency
vectors.  This file gives that dual action an explicit finite-dimensional
definition and proves its dot-product identity.  It then defines the exact
local square-root frequencies in Bourgain's scaled osculating coordinates.
-/
import GaloisForLFunctions.RHTower.BourgainAnisotropicCellGrid
import GaloisForLFunctions.RHTower.BourgainIndependentParabolaNearEnergy

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Canonical coordinate vector in four-dimensional phase space. -/
def bourgainPhaseBasis (j : Fin 4) : BourgainPhaseSpace :=
  Pi.single j 1

/-- Frequency pullback dual to a linear equivalence of phase variables. -/
def bourgainDualPullbackFrequency
    (E : BourgainPhaseSpace ≃ₗ[ℝ] BourgainPhaseSpace)
    (u : BourgainPhaseSpace) : BourgainPhaseSpace :=
  fun j => bourgainDot (E.symm (bourgainPhaseBasis j)) u

@[simp] theorem bourgainDot_phaseBasis
    (j : Fin 4) (u : BourgainPhaseSpace) :
    bourgainDot (bourgainPhaseBasis j) u = u j := by
  classical
  unfold bourgainDot bourgainPhaseBasis
  rw [Fintype.sum_eq_single j]
  · simp
  · intro k hkj
    rw [Pi.single_eq_of_ne hkj]
    simp

@[simp] theorem norm_bourgainPhaseBasis
    (j : Fin 4) :
    ‖bourgainPhaseBasis j‖ = 1 := by
  classical
  rw [Pi.norm_def]
  apply le_antisymm
  · rw [NNReal.coe_le_one]
    apply Finset.sup_le
    intro k hk
    by_cases hkj : j = k
    · subst k
      simp [bourgainPhaseBasis]
    · have hkj' : k ≠ j := Ne.symm hkj
      simp [bourgainPhaseBasis, Pi.single_eq_of_ne hkj']
  · have hle :=
      Finset.le_sup
        (f := fun k : Fin 4 => ‖bourgainPhaseBasis j k‖₊)
        (Finset.mem_univ j)
    simpa [bourgainPhaseBasis] using hle

theorem bourgainDot_sum_left
    {ι : Type*} [Fintype ι]
    (u : ι → BourgainPhaseSpace) (v : BourgainPhaseSpace) :
    bourgainDot (∑ i, u i) v = ∑ i, bourgainDot (u i) v := by
  unfold bourgainDot
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem bourgainDot_smul_left
    (r : ℝ) (u v : BourgainPhaseSpace) :
    bourgainDot (r • u) v = r * bourgainDot u v := by
  unfold bourgainDot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Defining contragredient identity for the dual frequency pullback. -/
theorem bourgainDot_dualPullbackFrequency
    (E : BourgainPhaseSpace ≃ₗ[ℝ] BourgainPhaseSpace)
    (y u : BourgainPhaseSpace) :
    bourgainDot y (bourgainDualPullbackFrequency E u) =
      bourgainDot (E.symm y) u := by
  classical
  calc
    bourgainDot y (bourgainDualPullbackFrequency E u) =
        ∑ j : Fin 4,
          y j * bourgainDot (E.symm (bourgainPhaseBasis j)) u := by
      rfl
    _ = ∑ j : Fin 4,
        bourgainDot
          (y j • E.symm (bourgainPhaseBasis j)) u := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [bourgainDot_smul_left]
    _ = bourgainDot
        (∑ j : Fin 4,
          y j • E.symm (bourgainPhaseBasis j)) u :=
      (bourgainDot_sum_left
        (fun j : Fin 4 =>
          y j • E.symm (bourgainPhaseBasis j)) u).symm
    _ = bourgainDot
        (E.symm
          (∑ j : Fin 4, y j • bourgainPhaseBasis j)) u := by
      simp
    _ = bourgainDot (E.symm y) u := by
      rw [show
        (∑ j : Fin 4, y j • bourgainPhaseBasis j) = y by
          simpa [bourgainPhaseBasis] using (pi_eq_sum_univ' y).symm]

/-- Exact left curve increment represented in scaled osculating phase
coordinates. -/
def bourgainExactLeftOsculatingFrequency
    {H : ℕ} {scale a b : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (D : ℝ) (n : Fin H) : BourgainPhaseSpace :=
  bourgainDualPullbackFrequency
    (bourgainScaledOsculatingPhaseContinuousLinearEquiv
      hscale ha hab).toLinearEquiv
    (bourgainSquareRootCurve
        (a ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
      bourgainSquareRootCurve (a ^ (2 : ℕ)))

/-- Exact right curve increment in the same osculating coordinates. -/
def bourgainExactRightOsculatingFrequency
    {H : ℕ} {scale a b : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (D : ℝ) (n : Fin H) : BourgainPhaseSpace :=
  bourgainDualPullbackFrequency
    (bourgainScaledOsculatingPhaseContinuousLinearEquiv
      hscale ha hab).toLinearEquiv
    (bourgainSquareRootCurve
        (b ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
      bourgainSquareRootCurve (b ^ (2 : ℕ)))

/-- Exact phase identity for the left transformed frequency. -/
theorem bourgainDot_exactLeftOsculatingFrequency
    {H : ℕ} {scale a b : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (D : ℝ) (n : Fin H) (y : BourgainPhaseSpace) :
    bourgainDot y
        (bourgainExactLeftOsculatingFrequency
          hscale ha hab D n) =
      bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm y)
          (a ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
        bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm y)
          (a ^ (2 : ℕ)) := by
  unfold bourgainExactLeftOsculatingFrequency
    bourgainSquareRootCurvePhase
  rw [bourgainDot_dualPullbackFrequency]
  unfold bourgainDot
  simp only [Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rfl

/-- Exact phase identity for the right transformed frequency. -/
theorem bourgainDot_exactRightOsculatingFrequency
    {H : ℕ} {scale a b : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (D : ℝ) (n : Fin H) (y : BourgainPhaseSpace) :
    bourgainDot y
        (bourgainExactRightOsculatingFrequency
          hscale ha hab D n) =
      bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm y)
          (b ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
        bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm y)
          (b ^ (2 : ℕ)) := by
  unfold bourgainExactRightOsculatingFrequency
    bourgainSquareRootCurvePhase
  rw [bourgainDot_dualPullbackFrequency]
  unfold bourgainDot
  simp only [Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rfl

end

end RHTower
