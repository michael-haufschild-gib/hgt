/-
# Sharp normalized-cell transfer to the literal A6 phase

The exact affine Taylor-coordinate matrix transports the normalized
exact-curve estimate to Bourgain's literal `A₆` frequency curve.  Both
Jacobians remain explicit.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedCellDecoupling
import GaloisForLFunctions.RHTower.BourgainA6NormalizedTaylorCurve

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Pullback of a normalized phase-space set through the transpose of the
affine Taylor-coordinate matrix. -/
def bourgainA6NormalizedTaylorPullback
    (G N₀ M : ℝ) (S : Set BourgainPhaseSpace) :
    Set BourgainPhaseSpace :=
  (Matrix.toLin'
    (bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M).transpose) ⁻¹' S

/-- Exact nonnegative change of variables through the affine Taylor
coordinates. -/
theorem setLIntegral_bourgainA6NormalizedTaylorPullback_eq
    {G N₀ M : ℝ} (hG : 0 < G) (hN₀ : 0 < N₀) (hM : 0 < M)
    (S : Set BourgainPhaseSpace) (hS : MeasurableSet S)
    (f : BourgainPhaseSpace → ENNReal) (hf : Measurable f) :
    (∫⁻ x in bourgainA6NormalizedTaylorPullback G N₀ M S,
        f ((bourgainA6NormalizedTaylorCoordinateMatrix
          G N₀ M).transpose.mulVec x)) =
      ENNReal.ofReal
          |((bourgainA6NormalizedTaylorCoordinateMatrix
            G N₀ M).det)⁻¹| *
        ∫⁻ y in S, f y := by
  let A := bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M
  let L := Matrix.toLin' A.transpose
  have hA :
      IsUnit (bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M) :=
    isUnit_bourgainA6NormalizedTaylorCoordinateMatrix hG hN₀ hM
  have hdet :
      A.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hA |>
      isUnit_iff_ne_zero.mp
  have hL : Measurable L :=
    L.continuous_of_finiteDimensional.measurable
  have hset :
      bourgainA6NormalizedTaylorPullback G N₀ M S =
        L ⁻¹' S := by
    rfl
  calc
    (∫⁻ x in bourgainA6NormalizedTaylorPullback G N₀ M S,
        f ((bourgainA6NormalizedTaylorCoordinateMatrix
          G N₀ M).transpose.mulVec x)) =
      ∫⁻ x in L ⁻¹' S, f (L x) := by
        rw [hset]
        congr 1
    _ = ∫⁻ y in S, f y ∂Measure.map L volume := by
      symm
      exact setLIntegral_map hS hf hL
    _ = ∫⁻ y in S, f y ∂
        (ENNReal.ofReal |A.transpose.det⁻¹| • volume) := by
      rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
    _ = ENNReal.ofReal |A.transpose.det⁻¹| *
        ∫⁻ y in S, f y := by
      rw [setLIntegral_smul_measure]
      rfl
    _ = _ := by
      rw [Matrix.det_transpose]

/-- Physical pulled-back cell for a normalized Taylor-curve block pair. -/
def bourgainA6AffinePhysicalFundamentalCell
    (H : ℕ) (G N₀ M D a b : ℝ) :
    Set BourgainPhaseSpace :=
  bourgainA6NormalizedTaylorPullback G N₀ M
    (bourgainGenericOsculatingFundamentalCell H
      (bourgainNormalizedCubicRemainder (M / N₀))
      (bourgainNormalizedQuarticRemainder (M / N₀))
      ((H : ℝ) / D) a b)

/-- Sharp bilinear sixth moment for two literal `A₆` affine blocks on one
physical pulled-back period cell. -/
theorem
    setLIntegral_bourgainA6AffinePhysicalLocalSum_fundamentalCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (_hH : 0 < H)
        {G N₀ M D a b : ℝ}
        (_hG : 0 < G) (_hN₀ : 0 < N₀) (_hM : 0 < M)
        (_hq1 : M / N₀ ≤ 1 / 2)
        (_hD : 0 < D) (_hHD : (H : ℝ) ≤ D)
        (_ha0 : 0 ≤ a) (_ha1 : a + (H : ℝ) / D ≤ 1)
        (_hb0 : 0 ≤ b) (_hb1 : b + (H : ℝ) / D ≤ 1)
        (_hab : 1 / 4 ≤ b - a)
        (_hsmall :
          50331648000 * (H : ℝ) ^ (3 : ℕ) / D ≤ 1 / 24)
        (c₁ c₂ : Fin H → ℂ),
        (∫⁻ x in bourgainA6AffinePhysicalFundamentalCell
            H G N₀ M D a b,
          ENNReal.ofReal
            (‖bourgainA6AffinePhysicalLocalSum
                H G N₀ M D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainA6AffinePhysicalLocalSum
                H G N₀ M D b c₂ x‖ ^ (6 : ℕ))) ≤
          ENNReal.ofReal
              |((bourgainA6NormalizedTaylorCoordinateMatrix
                G N₀ M).det)⁻¹| *
            ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (bourgainGenericPhaseCoordinateMatrix
                  (bourgainNormalizedCubicRemainder (M / N₀))
                  (bourgainNormalizedQuarticRemainder (M / N₀))
                  a b).det)⁻¹| *
            ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hnormalized⟩ :=
    setLIntegral_bourgainNormalizedExactLocalSum_fundamentalCell_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro H hH G N₀ M D a b hG hN₀ hM hq1 hD hHD
    ha0 ha1 hb0 hb1 hab hsmall c₁ c₂
  let q := M / N₀
  let φ₃ := bourgainNormalizedCubicRemainder q
  let φ₄ := bourgainNormalizedQuarticRemainder q
  let A := bourgainA6NormalizedTaylorCoordinateMatrix G N₀ M
  let S :=
    bourgainGenericOsculatingFundamentalCell
      H φ₃ φ₄ ((H : ℝ) / D) a b
  let f : BourgainPhaseSpace → ENNReal := fun y =>
    ENNReal.ofReal
      (‖bourgainGenericFourCurveExactLocalSum
          H φ₃ φ₄ D a c₁ y‖ ^ (6 : ℕ) *
        ‖bourgainGenericFourCurveExactLocalSum
          H φ₃ φ₄ D b c₂ y‖ ^ (6 : ℕ))
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have haIcc : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact ha0
    · have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  have hbIcc : b ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact hb0
    · have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  let hunit :=
    isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
      hq hq1 haIcc hbIcc hab
  have hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  have hS : MeasurableSet S :=
    measurableSet_bourgainGenericOsculatingFundamentalCell
      H φ₃ φ₄ hscale hunit
  have hf : Measurable f := by
    unfold f bourgainGenericFourCurveExactLocalSum
      bourgainGenericFourCurve bourgainUnitCharacter bourgainDot
    fun_prop
  have hchange :=
    setLIntegral_bourgainA6NormalizedTaylorPullback_eq
      hG hN₀ hM S hS f hf
  have hcell :=
    hnormalized H hH hq hq1 hD hHD
      ha0 ha1 hb0 hb1 hab hsmall c₁ c₂
  have hcell' :
      (∫⁻ y in S, f y) ≤
        ENNReal.ofReal
            |((((H : ℝ) / D) ^ (6 : ℕ)) *
              (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det)⁻¹| *
          ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
          ENNReal.ofReal
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
    simpa only [S, f, φ₃, φ₄, q] using hcell
  have hpoint (x : BourgainPhaseSpace) :
      ENNReal.ofReal
          (‖bourgainA6AffinePhysicalLocalSum
              H G N₀ M D a c₁ x‖ ^ (6 : ℕ) *
            ‖bourgainA6AffinePhysicalLocalSum
              H G N₀ M D b c₂ x‖ ^ (6 : ℕ)) =
        f (A.transpose.mulVec x) := by
    rw [norm_bourgainA6AffinePhysicalLocalSum_eq_normalized
        hN₀ hM hD ha0,
      norm_bourgainA6AffinePhysicalLocalSum_eq_normalized
        hN₀ hM hD hb0]
  calc
    (∫⁻ x in bourgainA6AffinePhysicalFundamentalCell
        H G N₀ M D a b,
      ENNReal.ofReal
        (‖bourgainA6AffinePhysicalLocalSum
            H G N₀ M D a c₁ x‖ ^ (6 : ℕ) *
          ‖bourgainA6AffinePhysicalLocalSum
            H G N₀ M D b c₂ x‖ ^ (6 : ℕ))) =
      ∫⁻ x in bourgainA6NormalizedTaylorPullback G N₀ M S,
        f (A.transpose.mulVec x) := by
          apply lintegral_congr
          intro x
          exact hpoint x
    _ = ENNReal.ofReal |A.det⁻¹| * ∫⁻ y in S, f y := by
      simpa [A] using hchange
    _ ≤ ENNReal.ofReal |A.det⁻¹| *
        (ENNReal.ofReal
            |((((H : ℝ) / D) ^ (6 : ℕ)) *
              (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b).det)⁻¹| *
          ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
          ENNReal.ofReal
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
        exact mul_le_mul_right hcell' _
    _ = _ := by
      simp only [A, φ₃, φ₄, q]
      ac_rfl

end

end RHTower
