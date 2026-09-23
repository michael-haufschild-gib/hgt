import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointAngularTests

/-! The complete cutoff-subtracted half-square is admitted to the actual invariant angular L² space. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMModularCore
noncomputable section

/-- The full three-term squared principal part, retaining both original Weyl coefficients. -/
def principalSquare (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ := (principal (center q) z)^(2 : ℕ)/2

def squareResidual (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  fullSquarePotential q z-cutoff z*principalSquare q z

/-- A continuous cusp-bounded coordinate field belongs to the actual quotient L² space. -/
theorem cuspBound_memLp (f : (Fin 2 → ℝ) → ℂ) (hf : ContinuousOn f domain)
    (B : ℝ) (hb : ∀ z, 3 < z 1 → ‖f z‖ ≤ B) :
    MemLp (fun z : UpperHalfPlane => f (coordinates z)) 2 D4BMModularCore.measure := by
  let lo : Fin 2 → ℝ := ![-1/2,1/2]
  let hi : Fin 2 → ℝ := ![1/2,4]
  have hc : ContinuousOn f (Icc lo hi) := hf.mono (by
    intro z hz
    have hh := hz.1 1
    change (1/2:ℝ) ≤ z 1 at hh
    change 0 < z 1
    linarith)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hcoordinates : Continuous coordinates := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have hfc : Continuous (fun z : UpperHalfPlane => f (coordinates z)) :=
    hf.comp_continuous hcoordinates (fun z => z.im_pos)
  apply MemLp.of_bound hfc.aestronglyMeasurable (max C B)
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  have hre := abs_le.mp hz.2
  have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have him : (1/2:ℝ) ≤ z.im := by nlinarith [z.im_pos]
  by_cases hh : 4 ≤ z.im
  · exact (hb (coordinates z) (by change 3 < z.im; linarith)).trans (le_max_right _ _)
  · apply (hC (coordinates z) ?_).trans (le_max_left _ _)
    constructor
    · intro i
      fin_cases i
      · simpa [lo,coordinates,neg_div] using hre.1
      · exact him
    · intro i
      fin_cases i
      · exact hre.2
      · exact le_of_not_ge hh

/-- Smooth cusp cutoff in the original chart. -/
theorem sourceCutoff_smooth : ContDiff ℝ ∞ cutoff := by
  let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    (Y.contDiff.sub contDiff_const))

/-- The complete principal half-square is smooth on every positive-height chart. -/
theorem principalSquare_smooth (q : XiZeroCopy) : ContDiffOn ℝ ∞ (principalSquare q) domain :=
  ((cuspConstantPart_contDiffOn .scalar (center q)).pow 2).div_const 2

theorem squareResidual_continuousOn (q : XiZeroCopy) : ContinuousOn (squareResidual q) domain := by
  have hQ : ContinuousOn (fullSquarePotential q) domain :=
    fun z hz => (fullSquarePotential_smooth q z hz 0).continuousAt.continuousWithinAt
  exact hQ.sub (sourceCutoff_smooth.continuous.continuousOn.mul (principalSquare_smooth q).continuousOn)

/-- In the cusp this is precisely half of the complete scalar-square remainder, including every cross term. -/
theorem squareResidual_high (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    squareResidual q z = squareRemainder (center q) z/2 := by
  unfold squareResidual cutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp only [Complex.ofReal_one,one_mul]
  dsimp [fullSquarePotential,principalSquare,squareRemainder]
  ring

/-- Actual L² admission of the full cutoff-subtracted scalar-square source, at every Xi occurrence. -/
theorem squareResidual_memLp (q : XiZeroCopy) :
    MemLp (fun z : UpperHalfPlane => squareResidual q (coordinates z)) 2 D4BMModularCore.measure := by
  obtain ⟨B,hB,hb⟩ := squareRemainder_bounded (center q) 3 (by norm_num)
  apply cuspBound_memLp _ (squareResidual_continuousOn q) (B/2)
  intro z hz
  rw [squareResidual_high q z hz,norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (hb z hz.le) (by norm_num)

def squareResidualVector (q : XiZeroCopy) : D4BMModularCore.Space :=
  (squareResidual_memLp q).toLp (fun z => squareResidual q (coordinates z))

end
end RHTower.D4BMJointSource
