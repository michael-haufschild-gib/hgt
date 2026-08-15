import GaloisForLFunctions.RHTower.WallTailRayEstimates
import GaloisForLFunctions.RHTower.WallFirstBoundarySquareIntegrable

/-!
# Regularity of the block resolvent in the position variable

In the one-block estimate the resolvent `C(x,L)^{-1}` is integrated over the block in the *position*
variable `L`, so the estimate needs its regularity there, not only in the frequency.  The shifted
generator depends affinely on the position, hence continuously; wherever the numerical floor is open
it is a unit, and the ring inverse is continuous at units.  So the resolvent and the two amplitudes
built from it are continuous in the position on the block, which is what makes the block integrals of
the expansion's terms well defined and lets them be separated.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

omit [CompleteSpace X] in
theorem continuous_wallGeneratorShift_position (T : X →L[ℂ] X) (σ x : ℝ) :
    Continuous fun L : ℝ => wallGeneratorShift T σ L x := by
  have h : Continuous fun L : ℝ =>
      wallGenerator T σ x + (L : ℂ) • ContinuousLinearMap.id ℂ X :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  exact h

/-- **The block resolvent is continuous in the position.**  Wherever the floor is open the shifted
generator is a unit, and the ring inverse is continuous at units. -/
theorem continuousOn_invFamily_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x : ℝ} {S : Set ℝ}
    (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ => invFamily (wallGeneratorShift T σ L) x) S := by
  intro L hL
  have hunit : IsUnit (wallGeneratorShift T σ L x) :=
    isUnit_wallGeneratorShift hσ0 hσ1 (hgap L hL)
  obtain ⟨u, hu⟩ := hunit
  have hinv : ContinuousAt Ring.inverse (wallGeneratorShift T σ L x) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hpos : ContinuousAt (fun M : ℝ => wallGeneratorShift T σ M x) L :=
    (continuous_wallGeneratorShift_position T σ x).continuousAt
  have hcomp : ContinuousAt (fun M : ℝ => invFamily (wallGeneratorShift T σ M) x) L :=
    ContinuousAt.comp (x := L) hinv hpos
  exact hcomp.continuousWithinAt

theorem continuousOn_invFamilyDeriv_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {x : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ =>
      invFamilyDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x) S := by
  have hbase := continuousOn_invFamily_position (T := T) hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      -(invFamily (wallGeneratorShift T σ L) x * wallGeneratorD1 X σ x
        * invFamily (wallGeneratorShift T σ L) x)) S :=
    ((hbase.mul continuousOn_const).mul hbase).neg
  exact h

theorem continuousOn_invFamilyProduct_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {x : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ =>
      invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x) S := by
  have h1 := continuousOn_invFamily_position (T := T) hσ0 hσ1 hgap
  have h2 := continuousOn_invFamilyDeriv_position (T := T) hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      invFamily (wallGeneratorShift T σ L) x
        * invFamilyDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x) S := h1.mul h2
  exact h

/-! ## Joint regularity in position and frequency -/

theorem continuous_wallGeneratorShift_pair (T : X →L[ℂ] X) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous fun p : ℝ × ℝ => wallGeneratorShift T σ p.1 p.2 := by
  have h : Continuous fun p : ℝ × ℝ =>
      wallGenerator T σ p.2 + (p.1 : ℂ) • ContinuousLinearMap.id ℂ X :=
    ((continuous_wallGenerator T hσ0 hσ1).comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const)
  exact h

/-- **The block resolvent is jointly continuous in position and frequency** wherever the floor is
open.  This is what makes the surviving amplitude of the expansion jointly measurable, and hence the
remaining integral measurable in the position. -/
theorem continuousOn_invFamily_pair {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {S : Set (ℝ × ℝ)}
    (hgap : ∀ p ∈ S, 0 < wallFloor T σ p.2 + p.1) :
    ContinuousOn (fun p : ℝ × ℝ => invFamily (wallGeneratorShift T σ p.1) p.2) S := by
  intro q hq
  have hunit : IsUnit (wallGeneratorShift T σ q.1 q.2) :=
    isUnit_wallGeneratorShift hσ0 hσ1 (hgap q hq)
  obtain ⟨u, hu⟩ := hunit
  have hinv : ContinuousAt Ring.inverse (wallGeneratorShift T σ q.1 q.2) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hpair : ContinuousAt (fun p : ℝ × ℝ => wallGeneratorShift T σ p.1 p.2) q :=
    (continuous_wallGeneratorShift_pair T hσ0 hσ1).continuousAt
  have hcomp : ContinuousAt
      (fun p : ℝ × ℝ => invFamily (wallGeneratorShift T σ p.1) p.2) q :=
    ContinuousAt.comp (x := q) hinv hpair
  exact hcomp.continuousWithinAt

/-! ## Integrability of the block integrands -/

/-- **A continuous bounded operator family applied to an integrable profile, against a unimodular
phase, is integrable.**  This is the shape of every term the block expansion integrates over the
position. -/
theorem integrableOn_phase_apply_of_continuousOn {A : ℝ → (X →L[ℂ] X)} {S : Set ℝ}
    (hS : MeasurableSet S) (hA : ContinuousOn A S) {C : ℝ} (hC : ∀ L ∈ S, ‖A L‖ ≤ C)
    {g : ℝ → X} (hg : IntegrableOn g S) {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hφ1 : ∀ L : ℝ, ‖φ L‖ = 1) :
    IntegrableOn (fun L => φ L • A L (g L)) S := by
  have hAm : AEStronglyMeasurable A (volume.restrict S) := hA.aestronglyMeasurable hS
  have hev : AEStronglyMeasurable (fun L => A L (g L)) (volume.restrict S) :=
    ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.apply ℂ X)
      hg.aestronglyMeasurable hAm
  have hmeas : AEStronglyMeasurable (fun L => φ L • A L (g L)) (volume.restrict S) :=
    hφ.aestronglyMeasurable.smul hev
  refine Integrable.mono' (hg.norm.const_mul C) hmeas ?_
  filter_upwards [ae_restrict_mem hS] with L hL
  rw [norm_smul, hφ1 L, one_mul]
  exact le_trans (ContinuousLinearMap.le_opNorm _ _)
    (mul_le_mul_of_nonneg_right (hC L hL) (norm_nonneg _))

end GaloisForLFunctions.RHTower
