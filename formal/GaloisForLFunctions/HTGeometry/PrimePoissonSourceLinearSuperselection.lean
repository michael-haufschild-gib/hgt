import GaloisForLFunctions.HTGeometry.ContinuousL2MultiplicationDisjointness
import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen

/-!
# Source-linear superselection for reflected prime-Poisson sectors

Closed `C(𝕋^ℙ)`-linear relations between reflected off-wall prime-Poisson multiplication
representations split coordinatewise.  Consequently every closed single-valued relation is the
zero operator on its domain, and every closed densely defined operator is the everywhere-defined
zero operator.  At the critical wall, the diagonal identity graph supplies a nonzero sewing.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Ordinary infinite prime torus. -/
abbrev PrimeTorus := Nat.Primes → UnitAddCircle

/-- `L²` space of an ordinary-prime product-Poisson measure. -/
abbrev PrimePoissonL2 (sigma t : ℝ) (hsigma : 0 < sigma) :=
  Lp ℂ 2 (primePoissonMeasure sigma t hsigma)

theorem primePoisson_reflection_continuousL2Mul_disjoint_of_ne_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2) :
    OperatorFamiliesDisjoint
      (continuousL2Mul (primePoissonMeasure sigma t hsigma))
      (continuousL2Mul (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1))) := by
  exact continuousL2Mul_operatorFamiliesDisjoint_of_mutuallySingular
    (primePoissonMeasure_reflection_mutuallySingular_of_ne_half
      sigma t hsigma hsigma1 hwall)

/-- The continuous constant one is nonzero in critical prime-Poisson `L²`. -/
theorem primePoisson_half_continuousOne_toLp_ne_zero (t : ℝ) :
    ContinuousMap.toLp 2 (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) ℂ
      (1 : C(PrimeTorus, ℂ)) ≠ 0 := by
  let mu := primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)
  let u : Lp ℂ 2 mu := ContinuousMap.toLp 2 mu ℂ (1 : C(PrimeTorus, ℂ))
  change u ≠ 0
  intro hzero
  have hnorm : ‖u‖ ^ 2 = 1 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hcoe : ((u : Lp ℂ 2 mu) : PrimeTorus → ℂ) =ᵐ[mu]
        fun _ => (1 : ℂ) := by
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) mu
        (1 : C(PrimeTorus, ℂ))] with x hx
      simpa [u] using hx
    calc
      (∫ x, ‖((u : Lp ℂ 2 mu) : PrimeTorus → ℂ) x‖ ^ 2 ∂mu) =
          ∫ _x : PrimeTorus, (1 : ℝ) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx
        rw [hx]
        norm_num
      _ = 1 := by simp [mu]
  rw [hzero, norm_zero, zero_pow (by norm_num)] at hnorm
  norm_num at hnorm

/-- Every closed source-linear relation between reflected off-wall prime-Poisson sectors splits
into its source and target coordinates. -/
theorem primePoisson_reflection_closedSourceRelation_splits
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2)
    (R : Submodule ℂ (HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1))))
    (hclosed : IsClosed (R : Set (HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1)))))
    (hinv : ∀ f : C(PrimeTorus, ℂ), ∀ z, z ∈ R →
      hilbertBlockDiagonal
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f)
        (continuousL2Mul (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) f) z ∈ R)
    (z : HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1))) :
    z ∈ R ↔ hilbertSumInl (hilbertSumFst z) ∈ R ∧
      hilbertSumInr (hilbertSumSnd z) ∈ R := by
  apply closedRelation_mem_iff_coordinate_mem_of_disjoint
    (continuousL2Mul (primePoissonMeasure sigma t hsigma))
    (continuousL2Mul (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)))
    (primePoisson_reflection_continuousL2Mul_disjoint_of_ne_half
      sigma t hsigma hsigma1 hwall) R hclosed hinv
  intro f w hw
  rw [adjoint_continuousL2Mul, adjoint_continuousL2Mul]
  exact hinv (star f) w hw

/-- Off wall, every closed densely defined single-valued source-linear relation is the full zero
graph. -/
theorem primePoisson_reflection_closedDenseSingleValuedSourceRelation_eq_zero
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2)
    (R : Submodule ℂ (HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1))))
    (hclosed : IsClosed (R : Set (HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1)))))
    (hdense : Dense (hilbertRelationDomain R : Set (PrimePoissonL2 sigma t hsigma)))
    (hsingle : HilbertRelationSingleValued R)
    (hinv : ∀ f : C(PrimeTorus, ℂ), ∀ z, z ∈ R →
      hilbertBlockDiagonal
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f)
        (continuousL2Mul (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) f) z ∈ R)
    (z : HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1))) :
    z ∈ R ↔ hilbertSumSnd z = 0 := by
  apply closedDenseSingleValuedRelation_mem_iff_output_eq_zero_of_disjoint
    (continuousL2Mul (primePoissonMeasure sigma t hsigma))
    (continuousL2Mul (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)))
    (primePoisson_reflection_continuousL2Mul_disjoint_of_ne_half
      sigma t hsigma hsigma1 hwall) R hclosed hdense hsingle hinv
  intro f w hw
  rw [adjoint_continuousL2Mul, adjoint_continuousL2Mul]
  exact hinv (star f) w hw

/-- Off wall, every closed single-valued source-linear relation is the zero operator on its actual
domain.  No ambient density assumption is needed, so this includes operators on reducing
subrepresentations. -/
theorem primePoisson_reflection_closedSingleValuedSourceRelation_eq_zero_on_domain
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2)
    (R : Submodule ℂ (HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1))))
    (hclosed : IsClosed (R : Set (HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1)))))
    (hsingle : HilbertRelationSingleValued R)
    (hinv : ∀ f : C(PrimeTorus, ℂ), ∀ z, z ∈ R →
      hilbertBlockDiagonal
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f)
        (continuousL2Mul (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) f) z ∈ R)
    (z : HilbertSum (PrimePoissonL2 sigma t hsigma)
      (PrimePoissonL2 (1 - sigma) t (sub_pos.mpr hsigma1))) :
    z ∈ R ↔ hilbertSumFst z ∈ hilbertRelationDomain R ∧ hilbertSumSnd z = 0 := by
  apply closedSingleValuedRelation_mem_iff_domain_and_output_zero_of_disjoint
    (continuousL2Mul (primePoissonMeasure sigma t hsigma))
    (continuousL2Mul (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)))
    (primePoisson_reflection_continuousL2Mul_disjoint_of_ne_half
      sigma t hsigma hsigma1 hwall) R hclosed hsingle hinv
  intro f w hw
  rw [adjoint_continuousL2Mul, adjoint_continuousL2Mul]
  exact hinv (star f) w hw

/-- Exact source-linear closed-sewing wall: a nonzero closed densely defined reflected sewing
exists exactly at `sigma = 1/2`. -/
theorem primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    NonzeroClosedSourceLinearSewing
      (continuousL2Mul (primePoissonMeasure sigma t hsigma))
      (continuousL2Mul
        (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1))) ↔
      sigma = 1 / 2 := by
  constructor
  · intro hsew
    by_contra hwall
    rcases hsew with ⟨R, hclosed, hdense, hsingle, hinv, z, hz, hout⟩
    exact hout ((primePoisson_reflection_closedDenseSingleValuedSourceRelation_eq_zero
      sigma t hsigma hsigma1 hwall R hclosed hdense hsingle hinv z).mp hz)
  · intro hhalf
    subst sigma
    let mu := primePoissonMeasure (1 / 2 : ℝ) t hsigma
    let u : Lp ℂ 2 mu := ContinuousMap.toLp 2 mu ℂ (1 : C(PrimeTorus, ℂ))
    have hu : u ≠ 0 := by
      simpa only [u, mu] using primePoisson_half_continuousOne_toLp_ne_zero t
    have htarget : primePoissonMeasure (1 - (1 / 2 : ℝ)) t
        (sub_pos.mpr hsigma1) = mu := by
      dsimp only [mu]
      congr 2
      norm_num
    exact continuousL2Mul_nonzeroClosedSourceLinearSewing_of_measure_eq
      mu _ htarget u hu

end

end GaloisForLFunctions.HTGeometry
