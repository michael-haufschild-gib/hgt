import GaloisForLFunctions.RHTower.FokasLenellsCauchyMatrixJump
import GaloisForLFunctions.HTGeometry.FokasLenellsSingularPhase
import GaloisForLFunctions.HTGeometry.FokasLenellsOrbitEntries

/-!
# Actual phase conjugacy and conservation of the full jump norm

The paper's time and space phases act by one genuine unitary multiplier.
Applying it on the first boundary coordinate intertwines the complete
nonlinear jump with its value at time and position zero. The full jump norm,
and therefore its Cauchy-compressed norm, are independent of both parameters.
-/

open MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The exact phase appearing in the existing lower jump symbol. -/
def directPhaseSymbol (t x z : ℝ) : ℂ := FDNLS.staggerPhase 2 (z*x-t/(4*z))

/-- The singular time phase has unit modulus at every spectral point, including zero. -/
theorem norm_directPhaseSymbol (t x z : ℝ) : ‖directPhaseSymbol t x z‖ = 1 :=
  FDNLS.norm_staggerPhase _ _

/-- The actual phase is measurable without any restriction at the spectral origin. -/
theorem directPhaseSymbol_measurable (t x : ℝ) : Measurable (directPhaseSymbol t x) := by
  unfold directPhaseSymbol FDNLS.staggerPhase
  fun_prop

private def directPhaseData (t x : ℝ) :
    GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ volume where
  toFun := directPhaseSymbol t x
  aestronglyMeasurable := (directPhaseSymbol_measurable t x).aestronglyMeasurable
  norm_eq_one := .of_forall (norm_directPhaseSymbol t x)

/-- Actual time and space evolution as a unitary multiplier on the existing Sonin L2 carrier. -/
def directPhaseUnitary (t x : ℝ) : SoninL2 ≃ₗᵢ[ℂ] SoninL2 := (directPhaseData t x).mulUnitary

/-- The unitary acts by the original phase almost everywhere. -/
theorem directPhaseUnitary_ae (t x : ℝ) (u : SoninL2) :
    (directPhaseUnitary t x u : ℝ → ℂ) =ᵐ[volume] fun z => directPhaseSymbol t x z*u z :=
  (directPhaseData t x).mulUnitary_ae u

/-- Diagonal unitary acting on the first coordinate of the actual two-channel boundary. -/
def boundaryPhaseUnitary (t x : ℝ) : Boundary ≃ₗᵢ[ℂ] Boundary where
  toLinearEquiv := (directPhaseUnitary t x).toLinearEquiv.prodCongr (LinearEquiv.refl ℂ SoninL2)
  norm_map' u := by
    change max ‖directPhaseUnitary t x u.1‖ ‖u.2‖ = max ‖u.1‖ ‖u.2‖
    rw [(directPhaseUnitary t x).norm_map]

/-- The second coordinate is fixed by the diagonal phase conjugacy. -/
theorem boundaryPhaseUnitary_apply (t x : ℝ) (u : Boundary) :
    boundaryPhaseUnitary t x u = (directPhaseUnitary t x u.1, u.2) := rfl

private theorem directSymbol_false_phase_factor (q : SchwartzMap ℝ ℂ) (t x z : ℝ) :
    directSymbol q t x false z = directPhaseSymbol t x z * directSymbol q 0 0 false z := by
  simp [directSymbol, regularJumpReflection, directPhaseSymbol, FDNLS.staggerPhase]

private theorem directSymbol_true_phase_cancel (q : SchwartzMap ℝ ℂ) (t x z : ℝ) :
    directSymbol q t x true z * directPhaseSymbol t x z = directSymbol q 0 0 true z := by
  have hp : FDNLS.staggerPhase (-2) (z*x-t/(4*z)) * FDNLS.staggerPhase 2 (z*x-t/(4*z)) = 1 := by
    simpa only [neg_neg] using staggerPhase_mul_opposite (-2) (z*x-t/(4*z))
  change (FDNLS.staggerPhase (-2) (z*x-t/(4*z)) *
    regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z) *
      FDNLS.staggerPhase 2 (z*x-t/(4*z)) = _
  rw [mul_right_comm, hp, one_mul]
  simp [directSymbol, regularJumpReverseReflection, FDNLS.staggerPhase]

/-- The actual lower multiplier factors through the genuine unitary phase. -/
theorem directMultiplier_false_phase_factor (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : SoninL2) :
    directMultiplier q t x false u = directPhaseUnitary t x (directMultiplier q 0 0 false u) := by
  apply Lp.ext
  filter_upwards [directMultiplier_ae q t x false u,
    directPhaseUnitary_ae t x (directMultiplier q 0 0 false u), directMultiplier_ae q 0 0 false u]
    with z h0 h1 h2
  rw [h0, h1, h2, directSymbol_false_phase_factor, mul_assoc]

/-- The inverse phase in the upper channel cancels the same unitary exactly. -/
theorem directMultiplier_true_phase_cancel (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : SoninL2) :
    directMultiplier q t x true (directPhaseUnitary t x u) = directMultiplier q 0 0 true u := by
  apply Lp.ext
  filter_upwards [directMultiplier_ae q t x true (directPhaseUnitary t x u),
    directPhaseUnitary_ae t x u, directMultiplier_ae q 0 0 true u] with z h0 h1 h2
  rw [h0, h1, h2, ← mul_assoc, directSymbol_true_phase_cancel]

/-- Actual unitary equivalence of the complete nonlinear jump at every time and position. -/
theorem directJumpPerturbation_phase_intertwining (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    directJumpPerturbation q t x (boundaryPhaseUnitary t x u) =
      boundaryPhaseUnitary t x (directJumpPerturbation q 0 0 u) := by
  change (-directMultiplier q t x false u.2,
    directMultiplier q t x true (directPhaseUnitary t x u.1) -
      directMultiplier q t x false (directMultiplier q t x true u.2)) =
    (directPhaseUnitary t x (-directMultiplier q 0 0 false u.2),
      directMultiplier q 0 0 true u.1 - directMultiplier q 0 0 false (directMultiplier q 0 0 true u.2))
  rw [directMultiplier_false_phase_factor, directMultiplier_true_phase_cancel,
    directMultiplier_product_invariant q t x 0 0, map_neg]

/-- The full jump's actual operator norm is conserved by both physical phase parameters. -/
theorem norm_directJumpPerturbation_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directJumpPerturbation q t x‖ = ‖directJumpPerturbation q 0 0‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    obtain ⟨u, rfl⟩ := (boundaryPhaseUnitary t x).surjective v
    rw [directJumpPerturbation_phase_intertwining, (boundaryPhaseUnitary t x).norm_map,
      (boundaryPhaseUnitary t x).norm_map]
    exact (directJumpPerturbation q 0 0).le_opNorm u
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    have h := (directJumpPerturbation q t x).le_opNorm (boundaryPhaseUnitary t x u)
    rw [directJumpPerturbation_phase_intertwining, (boundaryPhaseUnitary t x).norm_map,
      (boundaryPhaseUnitary t x).norm_map] at h
    exact h

/-- The Cauchy-compressed operator has the same conserved initial jump norm. -/
theorem norm_directCauchyOperator_time_space_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyOperator q t x‖ = ‖directJumpPerturbation q 0 0‖ := by
  rw [norm_directCauchyOperator_eq_jump, norm_directJumpPerturbation_time_space_invariant]

end
end RHTower.FokasLenells
