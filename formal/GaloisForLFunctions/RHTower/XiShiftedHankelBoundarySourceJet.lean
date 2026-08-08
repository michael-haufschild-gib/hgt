import GaloisForLFunctions.RHTower.XiShiftedMomentSourceJet
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryFlux

/-!
# Source-jet realization of the shifted Xi Hankel boundary coordinate

At a singular shifted-Xi Hankel face, extension to the next positive-semidefinite block is
controlled by one scalar: the null polynomial paired with the first omitted moment column.  This
file removes the moment/divisor presentation from that scalar.  After the exact positive
normalization furnished by the reverse-Bessel identity, the boundary coordinate is a finite linear
functional of completed source jets.

On the Euler ray `w > 1/2`, the same coordinate splits exactly into an archimedean boundary jet and
a cancellation-preserving Chebyshev--Stieltjes prime discrepancy boundary jet.  Consequently the
remaining moving-degree obstruction can be stated entirely on the source side.
-/

open Complex Matrix MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive scale relating the completed source jet to the shifted reciprocal-Xi moment. -/
def completedSourceMomentScale (n : ℕ) (w : ℝ) : ℝ :=
  (2 : ℝ) ^ n * (n.factorial : ℝ) * w ^ (2 * n + 1)

/-- Completed source jet with the exact moment normalization removed. -/
def normalizedCompletedSourceMoment (n : ℕ) (w : ℝ) : ℝ :=
  completedSourceJet n w / completedSourceMomentScale n w

theorem completedSourceMomentScale_pos (n : ℕ) {w : ℝ} (hw : 0 < w) :
    0 < completedSourceMomentScale n w := by
  exact mul_pos (mul_pos (pow_pos (by norm_num) n) (by positivity))
    (pow_pos hw (2 * n + 1))

/-- The normalized completed source jet is exactly the shifted reciprocal-Xi moment. -/
theorem normalizedCompletedSourceMoment_eq (n : ℕ) {w : ℝ} (hw : 0 < w) :
    normalizedCompletedSourceMoment n w =
      (xiShiftedReciprocalMoment (w ^ 2) n).re := by
  rw [normalizedCompletedSourceMoment,
    completedSourceJet_eq_xiShiftedReciprocalMoment n hw]
  apply mul_div_cancel_left₀
  exact ne_of_gt (completedSourceMomentScale_pos n hw)

/-- Normalized archimedean contribution to one shifted moment. -/
def normalizedArchimedeanSourceMoment (n : ℕ) (w : ℝ) : ℝ :=
  radialJet n (1 / 2 + w) archimedeanRayLogDeriv /
    completedSourceMomentScale n w

/-- Normalized cancellation-preserving prime discrepancy contribution to one shifted moment. -/
def normalizedChebyshevDiscrepancyMoment (n : ℕ) (w : ℝ) : ℝ :=
  ((∫ x in Ioi (1 : ℝ), radialBesselKernel n (1 / 2 + w) x) -
      ∫ x, radialBesselKernel n (1 / 2 + w) x ∂chebyshevPsiStieltjes.measure) /
    completedSourceMomentScale n w

theorem normalizedCompletedSourceMoment_eq_archimedean_add_discrepancy
    (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    normalizedCompletedSourceMoment n w =
      normalizedArchimedeanSourceMoment n w +
        normalizedChebyshevDiscrepancyMoment n w := by
  rw [normalizedCompletedSourceMoment,
    completedSourceJet_eq_archimedean_add_discrepancy n hw]
  exact add_div _ _ _

/-- Completed-source realization of the first omitted Hankel coupling. -/
def xiShiftedHankelBoundarySourceJet
    (w : ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, c j * normalizedCompletedSourceMoment (n + (j : ℕ)) w

/-- Archimedean part of the boundary source coordinate. -/
def xiShiftedHankelBoundaryArchimedeanJet
    (w : ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, c j * normalizedArchimedeanSourceMoment (n + (j : ℕ)) w

/-- Prime-discrepancy part of the boundary source coordinate. -/
def xiShiftedHankelBoundaryDiscrepancyJet
    (w : ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, c j * normalizedChebyshevDiscrepancyMoment (n + (j : ℕ)) w

/-- The first omitted Xi coupling is exactly the normalized completed-source boundary jet. -/
theorem xiShiftedHankelBoundarySourceJet_eq
    {w : ℝ} (hw : 0 < w) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedHankelBoundarySourceJet w n c =
      xiShiftedHankelFirstOmittedCoupling (w ^ 2) n c := by
  simp only [xiShiftedHankelBoundarySourceJet,
    xiShiftedHankelFirstOmittedCoupling,
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling]
  apply Finset.sum_congr rfl
  intro j hj
  rw [normalizedCompletedSourceMoment_eq (n + (j : ℕ)) hw]

theorem xiShiftedHankelBoundarySourceJet_eq_archimedean_add_discrepancy
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedHankelBoundarySourceJet w n c =
      xiShiftedHankelBoundaryArchimedeanJet w n c +
        xiShiftedHankelBoundaryDiscrepancyJet w n c := by
  simp only [xiShiftedHankelBoundarySourceJet,
    xiShiftedHankelBoundaryArchimedeanJet,
    xiShiftedHankelBoundaryDiscrepancyJet,
    normalizedCompletedSourceMoment_eq_archimedean_add_discrepancy _ hw,
    mul_add, Finset.sum_add_distrib]

/-- **Prime--Gamma boundary reduction.** On the Euler ray the exact PSD-extension obstruction is
the sum of one normalized archimedean jet and one normalized Chebyshev--Stieltjes discrepancy jet. -/
theorem xiShiftedHankelFirstOmittedCoupling_eq_archimedean_add_discrepancy
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedHankelFirstOmittedCoupling (w ^ 2) n c =
      xiShiftedHankelBoundaryArchimedeanJet w n c +
        xiShiftedHankelBoundaryDiscrepancyJet w n c := by
  rw [← xiShiftedHankelBoundarySourceJet_eq (by linarith : 0 < w) n c,
    xiShiftedHankelBoundarySourceJet_eq_archimedean_add_discrepancy hw n c]

end


end RHTower
