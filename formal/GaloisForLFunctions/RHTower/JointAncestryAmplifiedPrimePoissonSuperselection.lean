import GaloisForLFunctions.HTGeometry.L2OperatorFamilyAmplificationDisjointness
import GaloisForLFunctions.HTGeometry.PrimePoissonSourceLinearSuperselection
import GaloisForLFunctions.RHTower.JointAncestryCompletedThetaAllGradeMellinChain

/-!
# JAS amplified prime-Poisson superselection

Adding countably many diagonal valuation, compound, or prime-support channels cannot evade the
reflected prime-Poisson `C(PrimeTorus)` superselection wall. The countably amplified families have
a nonzero closed densely-defined source-linear sewing exactly at `sigma = 1/2`.

The positive critical survivor is source-marked: norms of the actual completed-theta Mellin grades
weight distinct amplification coordinates, producing a nonzero linearly independent countable
packet family. Thus diagonal/separable completion is terminal off wall, while a successful JAS
successor must introduce genuinely mixed prime--grade incidence rather than Hilbert multiplicity.
-/

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory

/-- Reflected prime-Poisson disjointness survives countable Hilbert multiplicity. -/
theorem primePoisson_reflection_operatorFamiliesDisjoint_l2Amplification_of_ne_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2) :
    OperatorFamiliesDisjoint
      (fun f => l2Amplification (Γ := ℕ)
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f))
      (fun f => l2Amplification (Γ := ℕ)
        (continuousL2Mul
          (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) f)) :=
  operatorFamiliesDisjoint_l2Amplification
    (primePoisson_reflection_continuousL2Mul_disjoint_of_ne_half
      sigma t hsigma hsigma1 hwall)

theorem primePoisson_continuousL2Mul_l2Amplification_nonzeroSewing_of_measure_eq
    (μ ν : Measure PrimeTorus) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν = μ) (u : L2Amplification ℕ (Lp ℂ 2 μ)) (hu : u ≠ 0) :
    NonzeroClosedSourceLinearSewing
      (fun f => l2Amplification (Γ := ℕ) (continuousL2Mul μ f))
      (fun f => l2Amplification (Γ := ℕ) (continuousL2Mul ν f)) := by
  subst ν
  exact nonzeroClosedSourceLinearSewing_self
    (fun f => l2Amplification (Γ := ℕ) (continuousL2Mul μ f)) u hu

set_option maxHeartbeats 1000000 in
/-- Exact countably-amplified source-linear sewing wall. Arbitrarily many diagonal completion
channels do not create an off-wall sewing. -/
theorem primePoisson_reflection_nonzeroClosedSourceLinearSewing_l2Amplification_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    NonzeroClosedSourceLinearSewing
      (fun f => l2Amplification (Γ := ℕ)
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f))
      (fun f => l2Amplification (Γ := ℕ)
        (continuousL2Mul
          (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) f)) ↔
      sigma = 1 / 2 := by
  constructor
  · intro hsew
    by_contra hwall
    rcases hsew with ⟨R, hclosed, hdense, hsingle, hinv, z, hz, hout⟩
    have hdisj :=
      primePoisson_reflection_operatorFamiliesDisjoint_l2Amplification_of_ne_half
        sigma t hsigma hsigma1 hwall
    have hinvAdj : ∀ f : C(PrimeTorus, ℂ), ∀ w, w ∈ R →
        hilbertBlockDiagonal
          (l2Amplification (Γ := ℕ)
            (continuousL2Mul (primePoissonMeasure sigma t hsigma) f)).adjoint
          (l2Amplification (Γ := ℕ)
            (continuousL2Mul
              (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) f)).adjoint w ∈ R := by
      intro f w hw
      rw [adjoint_l2Amplification, adjoint_l2Amplification,
        adjoint_continuousL2Mul, adjoint_continuousL2Mul]
      exact hinv (star f) w hw
    exact hout ((closedDenseSingleValuedRelation_mem_iff_output_eq_zero_of_disjoint
      _ _ hdisj R hclosed hdense hsingle hinv hinvAdj z).mp hz)
  · intro hhalf
    subst sigma
    let μ := primePoissonMeasure (1 / 2 : ℝ) t hsigma
    let u : Lp ℂ 2 μ :=
      ContinuousMap.toLp 2 μ ℂ (1 : C(PrimeTorus, ℂ))
    let uAmplified : L2Amplification ℕ (Lp ℂ 2 μ) := l2Single 0 u
    have hu : u ≠ 0 := by
      simpa only [u, μ] using primePoisson_half_continuousOne_toLp_ne_zero t
    have huAmplified : uAmplified ≠ 0 := by
      intro hzero
      have hcoord := congrArg (l2Coordinate (H₁ := Lp ℂ 2 μ) 0) hzero
      exact hu (by simpa [uAmplified] using hcoord)
    have htarget : primePoissonMeasure (1 - (1 / 2 : ℝ)) t
        (sub_pos.mpr hsigma1) = μ := by
      dsimp only [μ]
      congr 2
      norm_num
    simpa only [μ] using
      primePoisson_continuousL2Mul_l2Amplification_nonzeroSewing_of_measure_eq
        μ _ htarget uAmplified huAmplified

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open MeasureTheory
open GaloisForLFunctions.HTGeometry

/-- Critical prime-Poisson fibre used by the source-marked JAS amplification. -/
abbrev JASCriticalPrimePoissonL2 (t : ℝ) :=
  PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)

/-- Actual completed-theta grade norm times the critical constant prime-torus vector. -/
def jointAncestryCriticalPrimeThetaGradePayload (t : ℝ) (r : ℕ) :
    JASCriticalPrimePoissonL2 t :=
  (‖jointAncestryCompletedThetaGradeL2 r‖ : ℂ) •
    ContinuousMap.toLp 2
      (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) ℂ
      (1 : C(PrimeTorus, ℂ))

theorem jointAncestryCriticalPrimeThetaGradePayload_ne_zero
    (t : ℝ) (r : ℕ) :
    jointAncestryCriticalPrimeThetaGradePayload t r ≠ 0 := by
  apply smul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (jointAncestryCompletedThetaGradeL2_ne_zero r))
  · exact primePoisson_half_continuousOne_toLp_ne_zero t

/-- Source-marked packet: completed-theta grade `r` occupies amplification coordinate `r`. -/
def jointAncestryCriticalPrimeThetaGradePacket (t : ℝ) (r : ℕ) :
    L2Amplification ℕ (JASCriticalPrimePoissonL2 t) :=
  l2Single r (jointAncestryCriticalPrimeThetaGradePayload t r)

theorem jointAncestryCriticalPrimeThetaGradePacket_ne_zero
    (t : ℝ) (r : ℕ) :
    jointAncestryCriticalPrimeThetaGradePacket t r ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (l2Coordinate (H₁ := JASCriticalPrimePoissonL2 t) r) hzero
  exact jointAncestryCriticalPrimeThetaGradePayload_ne_zero t r
    (by simpa [jointAncestryCriticalPrimeThetaGradePacket] using hcoord)

/-- The entire actual completed-theta grade packet remains independent in the critical amplified
prime-torus carrier. -/
theorem linearIndependent_jointAncestryCriticalPrimeThetaGradePacket (t : ℝ) :
    LinearIndependent ℂ (jointAncestryCriticalPrimeThetaGradePacket t) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  have hcoord := congrArg
    (fun w : L2Amplification ℕ (JASCriticalPrimePoissonL2 t) => w i) hsum
  rw [lp.coeFn_sum, Finset.sum_apply] at hcoord
  simp only [lp.coeFn_smul, Pi.smul_apply,
    jointAncestryCriticalPrimeThetaGradePacket, l2Single_apply,
    lp.single_apply, Pi.single_apply] at hcoord
  have hci : c i • jointAncestryCriticalPrimeThetaGradePayload t i = 0 := by
    simpa [hi] using hcoord
  exact (smul_eq_zero.mp hci).resolve_right
    (jointAncestryCriticalPrimeThetaGradePayload_ne_zero t i)

/-- Positive survivor: actual completed-theta packet supplies a nonzero critical diagonal sewing. -/
theorem jointAncestryCriticalPrimeThetaGrade_sourceLinearSewing (t : ℝ) :
    NonzeroClosedSourceLinearSewing
      (fun f => l2Amplification (Γ := ℕ)
        (continuousL2Mul
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) f))
      (fun f => l2Amplification (Γ := ℕ)
        (continuousL2Mul
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) f)) :=
  nonzeroClosedSourceLinearSewing_self _
    (jointAncestryCriticalPrimeThetaGradePacket t 0)
    (jointAncestryCriticalPrimeThetaGradePacket_ne_zero t 0)

end


end RHTower
