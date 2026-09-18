import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapDefect
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalOrbitCurrent

/-!
# Finite modular Green bridge for literal cyclic Peierls fields

This is the exact finite-domain integration-by-parts stage needed by the
cap/contact comparison.  It pairs the actual full angular response and the
actual retained square response separately against an independent left reader.
The original vertical sides, top, and curved core all remain in the boundary
functional.  No noncompact limit, cusp cancellation, or contact equality is
asserted here.

Proof-chain role:
`physical cap action -> finite full/square reader Green identities -> admitted
noncompact boundary limit -> actual left-QNM contact -> HB B2 decision`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsAngularGreen

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMJointSource
open D4BMFullAngularCircle D4BMOriginalOrbitCurrent

noncomputable section
set_option autoImplicit false

private def angularProjection (x : Fin 4 → ℝ) : Fin 2 → ℝ := ![x 2, x 3]

private theorem angularProjection_smooth (x : Fin 4 → ℝ) :
    ContDiffAt ℝ ∞ angularProjection x := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ (2 : Fin 4)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (3 : Fin 4)).contDiffAt

private theorem angularProjection_slice (p R : ℝ) (z : ℂ) :
    angularProjection (physicalSlice p R z) = ![z.re, z.im] := by
  ext i
  fin_cases i <;> rfl

/-- Actual full angular field lifted to the physical four-coordinate modular slice. -/
def fullAngularPhysicalField (q : XiZeroCopy) (branch : Bool) : PhysicalField :=
  fun x => fullAngularField q branch (angularProjection x)

/-- Actual full-square field lifted to the same physical modular slice. -/
def fullSquarePhysicalField (q : XiZeroCopy) : PhysicalField :=
  fun x => fullSquarePotential q (angularProjection x)

/-- Independent literal left reader on the physical modular slice. -/
def leftReaderPhysicalField (reader : XiZeroCopy) : PhysicalField :=
  fun x => D4BMLiteralCusp.scalar (physicalAngularParameter reader) (angularProjection x)

private theorem fullAngularPhysicalField_smooth (q : XiZeroCopy) (branch : Bool)
    (p R : ℝ) (z : ℂ) (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fullAngularPhysicalField q branch) (physicalSlice p R z) := by
  have hp := angularProjection_slice p R z
  change ContDiffAt ℝ ∞ (fullAngularField q branch ∘ angularProjection)
    (physicalSlice p R z)
  rw [hp]
  exact (fullAngularField_smooth q branch ![z.re, z.im] hz).comp _
    (angularProjection_smooth _)

private theorem fullSquarePhysicalField_smooth (q : XiZeroCopy) (p R : ℝ)
    (z : ℂ) (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fullSquarePhysicalField q) (physicalSlice p R z) := by
  have hp := angularProjection_slice p R z
  apply contDiffAt_infty.mpr
  intro n
  change ContDiffAt ℝ n (fullSquarePotential q ∘ angularProjection)
    (physicalSlice p R z)
  rw [hp]
  exact (fullSquarePotential_smooth q ![z.re, z.im] hz n).comp _
    (angularProjection_smooth _).of_le le_top

private theorem leftReaderPhysicalField_smooth (reader : XiZeroCopy) (p R : ℝ)
    (z : ℂ) (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (leftReaderPhysicalField reader) (physicalSlice p R z) := by
  have hp := angularProjection_slice p R z
  apply contDiffAt_infty.mpr
  intro n
  change ContDiffAt ℝ n
    (D4BMLiteralCusp.scalar (physicalAngularParameter reader) ∘ angularProjection)
      (physicalSlice p R z)
  rw [hp]
  exact (D4BMLiteralCusp.scalar_contDiffAt (physicalAngularParameter reader) n
    ![z.re, z.im] hz).comp _ (angularProjection_smooth _).of_le le_top

/-- Exact finite modular Green identity for the actual full angular response
against the independent left reader. -/
theorem fullAngular_leftReader_green (q reader : XiZeroCopy) (branch : Bool)
    (p R : ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in domain Y,
      physicalScalarDensity (leftReaderPhysicalField reader)
        (fullAngularPhysicalField q branch) (physicalSlice p R (point w.1 w.2))) -
      (∫ w in domain Y,
        physicalScalarDensity (fullAngularPhysicalField q branch)
          (leftReaderPhysicalField reader) (physicalSlice p R (point w.1 w.2))) =
      physicalBoundary
        (physicalTransfer (leftReaderPhysicalField reader) (fullAngularPhysicalField q branch) 0)
        (physicalTransfer (leftReaderPhysicalField reader) (fullAngularPhysicalField q branch) 1)
        p R Y -
        physicalBoundary
          (physicalTransfer (fullAngularPhysicalField q branch) (leftReaderPhysicalField reader) 0)
          (physicalTransfer (fullAngularPhysicalField q branch) (leftReaderPhysicalField reader) 1)
          p R Y := by
  apply physical_scalar_green_integral
  · intro z hz
    exact fullAngularPhysicalField_smooth q branch p R z hz
  · intro z hz
    exact leftReaderPhysicalField_smooth reader p R z hz
  · exact hY

/-- Exact finite modular Green identity for the retained native square response
against the same independent left reader. -/
theorem fullSquare_leftReader_green (q reader : XiZeroCopy)
    (p R : ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in domain Y,
      physicalScalarDensity (leftReaderPhysicalField reader)
        (fullSquarePhysicalField q) (physicalSlice p R (point w.1 w.2))) -
      (∫ w in domain Y,
        physicalScalarDensity (fullSquarePhysicalField q)
          (leftReaderPhysicalField reader) (physicalSlice p R (point w.1 w.2))) =
      physicalBoundary
        (physicalTransfer (leftReaderPhysicalField reader) (fullSquarePhysicalField q) 0)
        (physicalTransfer (leftReaderPhysicalField reader) (fullSquarePhysicalField q) 1)
        p R Y -
        physicalBoundary
          (physicalTransfer (fullSquarePhysicalField q) (leftReaderPhysicalField reader) 0)
          (physicalTransfer (fullSquarePhysicalField q) (leftReaderPhysicalField reader) 1)
          p R Y := by
  apply physical_scalar_green_integral
  · intro z hz
    exact fullSquarePhysicalField_smooth q p R z hz
  · intro z hz
    exact leftReaderPhysicalField_smooth reader p R z hz
  · exact hY

/-- Finite modular Green transport for the exact physical cyclic Peierls
coefficient.  Both full and retained-square fields, both orientations, and
every side/top/core boundary term remain explicit.  This is the finite-domain
angular boundary identity needed before the noncompact cap/contact limit. -/
theorem cyclicPeierls_leftReader_green (q reader : XiZeroCopy) (branch : Bool)
    (p R : ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    ((∫ w in domain Y,
      physicalScalarDensity (leftReaderPhysicalField reader)
        (fullAngularPhysicalField q branch) (physicalSlice p R (point w.1 w.2))) -
      (∫ w in domain Y,
        physicalScalarDensity (fullAngularPhysicalField q branch)
          (leftReaderPhysicalField reader) (physicalSlice p R (point w.1 w.2)))) -
      (physicalRate q branch*(physicalRate q branch-1)/4)*
        ((∫ w in domain Y,
          physicalScalarDensity (leftReaderPhysicalField reader)
            (fullSquarePhysicalField q) (physicalSlice p R (point w.1 w.2))) -
          (∫ w in domain Y,
            physicalScalarDensity (fullSquarePhysicalField q)
              (leftReaderPhysicalField reader) (physicalSlice p R (point w.1 w.2)))) =
      (physicalBoundary
        (physicalTransfer (leftReaderPhysicalField reader) (fullAngularPhysicalField q branch) 0)
        (physicalTransfer (leftReaderPhysicalField reader) (fullAngularPhysicalField q branch) 1)
        p R Y -
        physicalBoundary
          (physicalTransfer (fullAngularPhysicalField q branch) (leftReaderPhysicalField reader) 0)
          (physicalTransfer (fullAngularPhysicalField q branch) (leftReaderPhysicalField reader) 1)
          p R Y) -
      (physicalRate q branch*(physicalRate q branch-1)/4)*
        (physicalBoundary
          (physicalTransfer (leftReaderPhysicalField reader) (fullSquarePhysicalField q) 0)
          (physicalTransfer (leftReaderPhysicalField reader) (fullSquarePhysicalField q) 1)
          p R Y -
          physicalBoundary
            (physicalTransfer (fullSquarePhysicalField q) (leftReaderPhysicalField reader) 0)
            (physicalTransfer (fullSquarePhysicalField q) (leftReaderPhysicalField reader) 1)
            p R Y) := by
  rw [fullAngular_leftReader_green q reader branch p R hY,
    fullSquare_leftReader_green q reader p R hY]

end

end RHTower.D4BMLiteralCyclicPeierlsAngularGreen
