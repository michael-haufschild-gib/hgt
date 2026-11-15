import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovInverseFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.CoordinateCubeCutoff

/-!
# Smooth cutoffs in moment frames

Pulling the coordinate plateau through the explicit inverse frame gives a
smooth cutoff supported in the covering box. Its open plateau contains the
image of the unit cube. Relative integer-grid profiles depend only on the
normalized index difference, independently of scale and shear direction.
-/

open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.CoordinateCubeCutoff

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The affine action is smooth on the full ambient moment space. -/
theorem contDiff_momentAffineAction (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (momentAffineAction r k δ t) :=
  contDiff_const.add
    (LinearMap.toContinuousLinearMap (Matrix.toLin' (vectorAffineMatrix r k δ t))).contDiff

/-- Every moment frame is smooth, including degenerate scales. -/
theorem contDiff_momentFrame (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (momentFrame r k ε δ t) :=
  contDiff_const.add
    (LinearMap.toContinuousLinearMap (Matrix.toLin' (scaledAffineMatrix r k ε δ t))).contDiff

/-- The explicit inverse-frame formula is smooth in its ambient argument. -/
theorem contDiff_momentFrameInverse (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (momentFrameInverse r k ε δ t) :=
  (LinearMap.toContinuousLinearMap
    (Matrix.toLin' (verticalDilationMatrix r k ε⁻¹))).contDiff.comp
      (contDiff_momentAffineAction r k (-(ε • δ)) (-t))

/-- The coordinate cutoff in normalized moment-frame coordinates. -/
def frameCutoff (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (x : AffineAxisSpace r k) : ℝ := cubeCutoff (momentFrameInverse r k ε δ t x)

/-- The open plateau of a frame cutoff. -/
def frameCore (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    Set (AffineAxisSpace r k) :=
  momentFrameInverse r k ε δ t ⁻¹' cubeCore (AffineAxisIndex r k)

theorem contDiff_frameCutoff (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (frameCutoff r k ε δ t) :=
  contDiff_cubeCutoff.comp (contDiff_momentFrameInverse r k ε δ t)

theorem frameCutoff_mem_Icc (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (x : AffineAxisSpace r k) : frameCutoff r k ε δ t x ∈ Set.Icc (0 : ℝ) 1 :=
  cubeCutoff_mem_Icc _

/-- Pullback by its own frame recovers the fixed coordinate profile exactly. -/
theorem frameCutoff_comp_frame (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (x : AffineAxisSpace r k) :
    frameCutoff r k ε δ t (momentFrame r k ε δ t x) = cubeCutoff x := by
  rw [frameCutoff, momentFrameInverse_frame r k ε hε]

/-- Covering boxes are compact even when their scale degenerates. -/
theorem isCompact_momentCoveringBox (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) : IsCompact (momentCoveringBox r k ε δ t) :=
  (isCompact_Icc : IsCompact (centeredCube (0 : AffineAxisSpace r k) 2)).image
    (contDiff_momentFrame r k ε δ t).continuous

/-- A nonzero frame cutoff can occur only inside its covering box. -/
theorem support_frameCutoff_subset (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    Function.support (frameCutoff r k ε δ t) ⊆ momentCoveringBox r k ε δ t := by
  intro x hx
  apply (mem_momentCoveringBox_iff_inverse r k ε hε δ t x).mpr
  exact tsupport_cubeCutoff_subset (subset_closure hx)

/-- The entire topological support lies inside the closed covering box. -/
theorem tsupport_frameCutoff_subset (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    tsupport (frameCutoff r k ε δ t) ⊆ momentCoveringBox r k ε δ t :=
  closure_minimal (support_frameCutoff_subset r k ε hε δ t)
    (isCompact_momentCoveringBox r k ε δ t).isClosed

theorem hasCompactSupport_frameCutoff (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) : HasCompactSupport (frameCutoff r k ε δ t) :=
  (isCompact_momentCoveringBox r k ε δ t).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_frameCutoff_subset r k ε hε δ t)

theorem isOpen_frameCore (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    IsOpen (frameCore r k ε δ t) :=
  isOpen_cubeCore.preimage (contDiff_momentFrameInverse r k ε δ t).continuous

theorem frameCutoff_eqOn_frameCore (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    Set.EqOn (frameCutoff r k ε δ t) 1 (frameCore r k ε δ t) :=
  fun _ hx => cubeCutoff_eqOn_core hx

/-- The open plateau contains every frame image of a unit-cube point. -/
theorem momentFrame_unitCube_subset_frameCore (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    momentFrame r k ε δ t '' centeredCube 0 1 ⊆ frameCore r k ε δ t := by
  rintro x ⟨y, hy, rfl⟩
  change momentFrameInverse r k ε δ t (momentFrame r k ε δ t y) ∈ cubeCore (AffineAxisIndex r k)
  rw [momentFrameInverse_frame r k ε hε]
  exact unitCube_subset_cubeCore hy

/-- Integer-grid cutoff profiles lose all dependence on scale and direction. -/
theorem frameCutoff_integer_parallelFrame (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i j : ℤ) (x : AffineAxisSpace r k) :
    frameCutoff r k ε δ (ε * (j : ℝ) / (q + 1 : ℝ))
      (momentFrame r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x) =
        cubeCutoff (momentAffineAction r k 0 (((i : ℝ) - (j : ℝ)) / (q + 1 : ℝ)) x) := by
  rw [frameCutoff, momentFrameInverse_integer_parallelFrame r k q ε hε]

/-- The actual frame cutoff bundled as a complex Schwartz function. -/
def frameCutoffSchwartz (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) : SchwartzMap (AffineAxisSpace r k) ℂ :=
  ((hasCompactSupport_frameCutoff r k ε hε δ t).comp_left
    (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (contDiff_frameCutoff r k ε δ t))

#print axioms contDiff_momentAffineAction
#print axioms contDiff_momentFrame
#print axioms contDiff_momentFrameInverse
#print axioms contDiff_frameCutoff
#print axioms frameCutoff_mem_Icc
#print axioms frameCutoff_comp_frame
#print axioms isCompact_momentCoveringBox
#print axioms support_frameCutoff_subset
#print axioms tsupport_frameCutoff_subset
#print axioms hasCompactSupport_frameCutoff
#print axioms isOpen_frameCore
#print axioms frameCutoff_eqOn_frameCore
#print axioms momentFrame_unitCube_subset_frameCore
#print axioms frameCutoff_integer_parallelFrame
#print axioms frameCutoffSchwartz

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
