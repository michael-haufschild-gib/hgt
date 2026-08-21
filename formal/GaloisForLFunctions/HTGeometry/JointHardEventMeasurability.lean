/-
# Joint measurability of the hard event

The Schrödinger propagator is the exponential of a continuous function of the generator and the
time, and matrix action on a fixed vector is a linear map of a finite-dimensional space, so the
orbit is jointly continuous in the two variables.  The easy event -- being within a prescribed
distance of some member of a finite dictionary -- is therefore a finite union of closed conditions,
and the hard event is jointly measurable, as the quenched fixed-time transfer requires.

Main results:
* `continuous_unitaryEvolution`, `continuous_mulVec_const`, `continuous_orbit_pair`.
* `isClosed_easyPairEvent`, `measurableSet_hardPairEvent` — **the joint measurability**.
-/
import GaloisForLFunctions.HTGeometry.ObserverProfileStability
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow

open Matrix MeasureTheory Metric Set
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

local instance instCStarAlgebraMatrixJoint : CStarAlgebra (Matrix d d ℂ) where

/-- **The Schrödinger propagator is jointly continuous in the generator and the time.** -/
theorem continuous_unitaryEvolution :
    Continuous (fun q : Matrix d d ℂ × ℝ => unitaryEvolution q.1 q.2) := by
  have hinner : Continuous (fun q : Matrix d d ℂ × ℝ => (q.2 : ℝ) • ((-Complex.I) • q.1)) := by
    exact continuous_snd.smul (continuous_fst.const_smul (-Complex.I))
  letI : NormedAlgebra ℚ (Matrix d d ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (Matrix d d ℂ)
  exact NormedSpace.exp_continuous.comp hinner

/-- Matrix action on a fixed vector, as a continuous linear map. -/
theorem continuous_mulVec_const (psi : d → ℂ) :
    Continuous (fun M : Matrix d d ℂ => eucVec (M *ᵥ psi)) := by
  classical
  obtain ⟨L, hLdef⟩ : ∃ L : Matrix d d ℂ →ₗ[ℂ] EuclideanSpace ℂ d,
    L = { toFun := fun M => eucVec (M *ᵥ psi)
          map_add' := by
            intro M N
            ext x
            show ((M + N) *ᵥ psi) x = (M *ᵥ psi) x + (N *ᵥ psi) x
            rw [Matrix.add_mulVec]
            rfl
          map_smul' := by
            intro c M
            ext x
            show ((c • M) *ᵥ psi) x = c * ((M *ᵥ psi) x)
            show (∑ y, (c * M x y) * psi y) = c * ∑ y, M x y * psi y
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring } := ⟨_, rfl⟩
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  rw [hLdef] at hL
  exact hL

/-- **The Schrödinger orbit is jointly continuous in the generator and the time.** -/
theorem continuous_orbit_pair (psi : d → ℂ) :
    Continuous (fun q : Matrix d d ℂ × ℝ => eucVec (unitaryEvolution q.1 q.2 *ᵥ psi)) :=
  (continuous_mulVec_const psi).comp continuous_unitaryEvolution


section Event

variable {Ω : Type} [TopologicalSpace Ω] {C : Type} [Fintype C]

set_option maxHeartbeats 1000000 in
/-- **The easy event is closed in the generator and the time jointly.** -/
theorem isClosed_easyPairEvent (Hmap : Ω → Matrix d d ℂ) (hH : Continuous Hmap)
    (psi : d → ℂ) (Z : C → (d → ℂ)) (eps : ℝ) :
    IsClosed {q : Ω × ℝ | ∃ κ : C,
      dist (eucVec (unitaryEvolution (Hmap q.1) q.2 *ᵥ psi)) (eucVec (Z κ)) ≤ eps} := by
  classical
  have hmap : Continuous (fun q : Ω × ℝ => ((Hmap q.1 : Matrix d d ℂ), q.2)) :=
    (hH.comp continuous_fst).prodMk continuous_snd
  have hcont : Continuous
      (fun q : Ω × ℝ => eucVec (unitaryEvolution (Hmap q.1) q.2 *ᵥ psi)) :=
    (continuous_orbit_pair psi).comp hmap
  have hset : {q : Ω × ℝ | ∃ κ : C,
        dist (eucVec (unitaryEvolution (Hmap q.1) q.2 *ᵥ psi)) (eucVec (Z κ)) ≤ eps}
      = ⋃ κ : C, {q : Ω × ℝ |
        dist (eucVec (unitaryEvolution (Hmap q.1) q.2 *ᵥ psi)) (eucVec (Z κ)) ≤ eps} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  refine isClosed_iUnion_of_finite fun κ => ?_
  have hd : Continuous (fun q : Ω × ℝ =>
      dist (eucVec (unitaryEvolution (Hmap q.1) q.2 *ᵥ psi)) (eucVec (Z κ))) :=
    hcont.dist continuous_const
  exact isClosed_le hd continuous_const

variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]

/-- **The hard event is jointly measurable.**  This is the measurability the quenched fixed-time
transfer consumes. -/
theorem measurableSet_hardPairEvent (Hmap : Ω → Matrix d d ℂ) (hH : Continuous Hmap)
    (psi : d → ℂ) (Z : C → (d → ℂ)) (eps : ℝ) :
    MeasurableSet {q : Ω × ℝ | ¬ ∃ κ : C,
      dist (eucVec (unitaryEvolution (Hmap q.1) q.2 *ᵥ psi)) (eucVec (Z κ)) ≤ eps} := by
  have hclosed := isClosed_easyPairEvent Hmap hH psi Z eps
  have hmeas : MeasurableSet {q : Ω × ℝ | ∃ κ : C,
      dist (eucVec (unitaryEvolution (Hmap q.1) q.2 *ᵥ psi)) (eucVec (Z κ)) ≤ eps} :=
    hclosed.measurableSet
  exact hmeas.compl

end Event

end GaloisForLFunctions.HTGeometry

end
