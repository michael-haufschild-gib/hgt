/-
# Exact normalized Taylor coordinates for the A6 phase

On a positive interval `N₀ + M t`, Bourgain's literal four-coordinate
`A₆` phase is an affine image of
`(t,t²,φ₃(t),φ₄(t))`.  This module packages the exact Taylor identities in
one matrix statement.  No asymptotic expansion is used.
-/
import GaloisForLFunctions.RHTower.BourgainTaylorScaling
import GaloisForLFunctions.RHTower.BourgainGenericPairedTripleFourierIdentity

namespace RHTower

noncomputable section

/-- Literal unnormalised `A₆` frequency curve on the affine interval
`N₀ + M t`, with the global square-root multiplier in the last two
coordinates. -/
def bourgainA6AffinePhysicalCurve
    (G N₀ M t : ℝ) : BourgainPhaseSpace :=
  ![N₀ + M * t,
    (N₀ + M * t) ^ (2 : ℕ),
    G ^ (1 / 2 : ℝ) * (N₀ + M * t) ^ (3 / 2 : ℝ),
    G ^ (1 / 2 : ℝ) * (N₀ + M * t) ^ (1 / 2 : ℝ)]

/-- Constant term of the affine Taylor-coordinate representation. -/
def bourgainA6AffinePhysicalCurveBase
    (G N₀ : ℝ) : BourgainPhaseSpace :=
  ![N₀,
    N₀ ^ (2 : ℕ),
    G ^ (1 / 2 : ℝ) * N₀ ^ (3 / 2 : ℝ),
    G ^ (1 / 2 : ℝ) * N₀ ^ (1 / 2 : ℝ)]

/-- Lower-triangular coordinate matrix sending Bourgain's normalized
Taylor curve to the nonconstant part of the literal `A₆` phase. -/
def bourgainA6NormalizedTaylorCoordinateMatrix
    (G N₀ M : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let q := M / N₀
  let g := G ^ (1 / 2 : ℝ)
  !![M, 0, 0, 0;
     2 * N₀ * M, M ^ (2 : ℕ), 0, 0;
     g * N₀ ^ (3 / 2 : ℝ) * ((3 / 2 : ℝ) * q),
       g * N₀ ^ (3 / 2 : ℝ) * ((3 / 8 : ℝ) * q ^ (2 : ℕ)),
       g * N₀ ^ (3 / 2 : ℝ) * (-(q ^ (3 : ℕ)) / 16), 0;
     g * N₀ ^ (1 / 2 : ℝ) * ((1 / 2 : ℝ) * q),
       g * N₀ ^ (1 / 2 : ℝ) * (-(1 / 8 : ℝ) * q ^ (2 : ℕ)),
       g * N₀ ^ (1 / 2 : ℝ) * (q ^ (3 : ℕ) / 16),
       g * N₀ ^ (1 / 2 : ℝ) * (-(q ^ (4 : ℕ)) / 64)]

/-- Exact affine curve identity underlying Bourgain (2.18)--(2.22). -/
theorem bourgainA6NormalizedTaylorCoordinateMatrix_mulVec
    {G N₀ M t : ℝ} (hN₀ : 0 < N₀) (hM : 0 < M)
    (ht : 0 ≤ t) :
    (bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M).mulVec
        (bourgainGenericFourCurve
          (bourgainNormalizedCubicRemainder (M / N₀))
          (bourgainNormalizedQuarticRemainder (M / N₀)) t) =
      bourgainA6AffinePhysicalCurve G N₀ M t -
        bourgainA6AffinePhysicalCurveBase G N₀ := by
  have hthree :=
    bourgain_scaled_three_halves_taylor hN₀ hM ht
  have hhalf :=
    bourgain_scaled_half_taylor hN₀ hM ht
  have hhalf' :
      (N₀ + M * t) ^ (2 : ℝ)⁻¹ =
        N₀ ^ (2 : ℝ)⁻¹ *
          (bourgainHalfTaylorPolynomial (M / N₀) t -
            (M / N₀) ^ (3 : ℕ) *
              bourgainCubicTaylorPhase (M / N₀) t +
            (M / N₀) ^ (4 : ℕ) *
              bourgainQuarticTaylorPhase (M / N₀) t) := by
    simpa only [one_div] using hhalf
  ext i
  fin_cases i
  · simp [bourgainA6NormalizedTaylorCoordinateMatrix,
      bourgainGenericFourCurve, bourgainA6AffinePhysicalCurve,
      bourgainA6AffinePhysicalCurveBase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
  · simp [bourgainA6NormalizedTaylorCoordinateMatrix,
      bourgainGenericFourCurve, bourgainA6AffinePhysicalCurve,
      bourgainA6AffinePhysicalCurveBase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    ring
  · simp [bourgainA6NormalizedTaylorCoordinateMatrix,
      bourgainGenericFourCurve, bourgainA6AffinePhysicalCurve,
      bourgainA6AffinePhysicalCurveBase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    rw [hthree]
    unfold bourgainThreeHalvesTaylorPolynomial
      bourgainCubicTaylorPhase
    ring
  · simp [bourgainA6NormalizedTaylorCoordinateMatrix,
      bourgainGenericFourCurve, bourgainA6AffinePhysicalCurve,
      bourgainA6AffinePhysicalCurveBase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    rw [hhalf']
    unfold bourgainHalfTaylorPolynomial bourgainCubicTaylorPhase
      bourgainQuarticTaylorPhase
    ring

/-- Exact determinant of the affine Taylor-coordinate matrix. -/
theorem det_bourgainA6NormalizedTaylorCoordinateMatrix
    (G N₀ M : ℝ) :
    (bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M).det =
      M * M ^ (2 : ℕ) *
        (G ^ (1 / 2 : ℝ) * N₀ ^ (3 / 2 : ℝ) *
          (-((M / N₀) ^ (3 : ℕ)) / 16)) *
        (G ^ (1 / 2 : ℝ) * N₀ ^ (1 / 2 : ℝ) *
          (-((M / N₀) ^ (4 : ℕ)) / 64)) := by
  have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [bourgainA6NormalizedTaylorCoordinateMatrix,
    Matrix.det_fin_three, Fin.sum_univ_four,
    h21, h22, h12, h31, h32]
  ring

/-- The affine Taylor-coordinate matrix is invertible throughout the
positive parameter range used in Bourgain's mean-value argument. -/
theorem isUnit_bourgainA6NormalizedTaylorCoordinateMatrix
    {G N₀ M : ℝ} (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M) :
    IsUnit (bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    det_bourgainA6NormalizedTaylorCoordinateMatrix]
  have hq : M / N₀ ≠ 0 := div_ne_zero hM.ne' hN₀.ne'
  have hGhalf : G ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hG _).ne'
  have hNthree : N₀ ^ (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hN₀ _).ne'
  have hNhalf : N₀ ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hN₀ _).ne'
  have hthird :
      G ^ (1 / 2 : ℝ) * N₀ ^ (3 / 2 : ℝ) *
          (-((M / N₀) ^ (3 : ℕ)) / 16) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hGhalf hNthree)
      (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hq))
        (by norm_num))
  have hfourth :
      G ^ (1 / 2 : ℝ) * N₀ ^ (1 / 2 : ℝ) *
          (-((M / N₀) ^ (4 : ℕ)) / 64) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hGhalf hNhalf)
      (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 4 hq))
        (by norm_num))
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero hM.ne' (pow_ne_zero 2 hM.ne')) hthird)
    hfourth

/-- Exact phase identity: after transposing the affine coordinate matrix,
the literal `A₆` phase is the normalized Taylor-curve phase plus one
sample-independent constant phase. -/
theorem bourgainDot_A6AffinePhysicalCurve_eq_normalized
    {G N₀ M t : ℝ} (hN₀ : 0 < N₀) (hM : 0 < M)
    (ht : 0 ≤ t) (x : BourgainPhaseSpace) :
    bourgainDot x (bourgainA6AffinePhysicalCurve G N₀ M t) =
      bourgainDot
          ((bourgainA6NormalizedTaylorCoordinateMatrix
            G N₀ M).transpose.mulVec x)
          (bourgainGenericFourCurve
            (bourgainNormalizedCubicRemainder (M / N₀))
            (bourgainNormalizedQuarticRemainder (M / N₀)) t) +
        bourgainDot x (bourgainA6AffinePhysicalCurveBase G N₀) := by
  let A := bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M
  let γ :=
    bourgainGenericFourCurve
      (bourgainNormalizedCubicRemainder (M / N₀))
      (bourgainNormalizedQuarticRemainder (M / N₀)) t
  let v := bourgainA6AffinePhysicalCurveBase G N₀
  have hcurve :
      A.mulVec γ =
        bourgainA6AffinePhysicalCurve G N₀ M t - v := by
    exact bourgainA6NormalizedTaylorCoordinateMatrix_mulVec
      hN₀ hM ht
  have hcurve' :
      bourgainA6AffinePhysicalCurve G N₀ M t =
        A.mulVec γ + v :=
    (sub_eq_iff_eq_add.mp hcurve.symm)
  have hmatrix :
      x ⬝ᵥ A.mulVec γ = A.transpose.mulVec x ⬝ᵥ γ := by
    calc
      x ⬝ᵥ A.mulVec γ =
          γ ⬝ᵥ A.transpose.mulVec x :=
        (Matrix.dotProduct_transpose_mulVec A γ x).symm
      _ = A.transpose.mulVec x ⬝ᵥ γ :=
        dotProduct_comm _ _
  change
    x ⬝ᵥ bourgainA6AffinePhysicalCurve G N₀ M t =
      A.transpose.mulVec x ⬝ᵥ γ + x ⬝ᵥ v
  rw [hcurve', dotProduct_add, hmatrix]

/-- Finite exact `A₆` sum on an affine positive interval. -/
def bourgainA6AffinePhysicalLocalSum
    (H : ℕ) (G N₀ M D a : ℝ)
    (c : Fin H → ℂ) (x : BourgainPhaseSpace) : ℂ :=
  ∑ n : Fin H,
    c n * bourgainUnitCharacter
      (bourgainDot x
        (bourgainA6AffinePhysicalCurve G N₀ M
          (a + (bourgainIndex n : ℝ) / D)))

/-- Exact finite-sum form of the Taylor-coordinate phase identity. -/
theorem bourgainA6AffinePhysicalLocalSum_eq_normalized
    {H : ℕ} {G N₀ M D a : ℝ}
    (hN₀ : 0 < N₀) (hM : 0 < M) (hD : 0 < D)
    (ha : 0 ≤ a) (c : Fin H → ℂ) (x : BourgainPhaseSpace) :
    bourgainA6AffinePhysicalLocalSum H G N₀ M D a c x =
      bourgainUnitCharacter
          (bourgainDot x (bourgainA6AffinePhysicalCurveBase G N₀)) *
        bourgainGenericFourCurveExactLocalSum H
          (bourgainNormalizedCubicRemainder (M / N₀))
          (bourgainNormalizedQuarticRemainder (M / N₀))
          D a c
          ((bourgainA6NormalizedTaylorCoordinateMatrix
            G N₀ M).transpose.mulVec x) := by
  unfold bourgainA6AffinePhysicalLocalSum
    bourgainGenericFourCurveExactLocalSum
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro n
  have ht :
      0 ≤ a + (bourgainIndex n : ℝ) / D := by
    have : 0 ≤ (bourgainIndex n : ℝ) / D := by positivity
    linarith
  rw [bourgainDot_A6AffinePhysicalCurve_eq_normalized
    hN₀ hM ht, bourgainUnitCharacter_add]
  ring

/-- The sample-independent affine phase disappears after taking norms. -/
theorem norm_bourgainA6AffinePhysicalLocalSum_eq_normalized
    {H : ℕ} {G N₀ M D a : ℝ}
    (hN₀ : 0 < N₀) (hM : 0 < M) (hD : 0 < D)
    (ha : 0 ≤ a) (c : Fin H → ℂ) (x : BourgainPhaseSpace) :
    ‖bourgainA6AffinePhysicalLocalSum H G N₀ M D a c x‖ =
      ‖bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder (M / N₀))
        (bourgainNormalizedQuarticRemainder (M / N₀))
        D a c
        ((bourgainA6NormalizedTaylorCoordinateMatrix
          G N₀ M).transpose.mulVec x)‖ := by
  rw [bourgainA6AffinePhysicalLocalSum_eq_normalized
    hN₀ hM hD ha]
  simp

end

end RHTower
