import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# The trace invariant of the compressed source inverse

The source inverse of the Riemann source is Hilbert–Schmidt, so its square is a product of two
Hilbert–Schmidt operators.  The corpus trace layer therefore applies verbatim: the diagonal series
converges over every Hilbert basis, its sum is basis independent, it equals the Hilbert–Schmidt
pairing `⟨B†, B⟩_HS`, and it is bounded by `‖B‖²_HS`.  This makes the trace calibration of the
compressed-inverse card a well-posed identity.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt ContinuousLinearMap

/-- The source inverse of the Riemann source as an operator on the quantile space. -/
def thetaKernelOperator : Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
    (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)

theorem isHilbertSchmidt_thetaKernelOperator' :
    IsHilbertSchmidt thetaKernelOperator :=
  isHilbertSchmidt_thetaKernelOperator

/-- **The trace invariant `tr(B²)` of the compressed source inverse.** -/
def thetaTraceSq : ℂ := opTrace (thetaKernelOperator ∘L thetaKernelOperator)

/-- **The trace series converges over every Hilbert basis.** -/
theorem summable_thetaTraceSq_diag {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 unitIntervalMeasure)) :
    Summable (fun i => (inner ℂ (b i)
      ((thetaKernelOperator ∘L thetaKernelOperator) (b i)) : ℂ)) :=
  summable_inner_diag_comp isHilbertSchmidt_thetaKernelOperator'
    isHilbertSchmidt_thetaKernelOperator' b

/-- **The trace invariant is basis independent.** -/
theorem thetaTraceSq_eq_tsum_basis {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 unitIntervalMeasure)) :
    thetaTraceSq = ∑' i, (inner ℂ (b i)
      ((thetaKernelOperator ∘L thetaKernelOperator) (b i)) : ℂ) :=
  opTrace_comp_eq_tsum_basis isHilbertSchmidt_thetaKernelOperator'
    isHilbertSchmidt_thetaKernelOperator' b

/-- **The trace invariant is the Hilbert--Schmidt pairing of `B†` with `B`.** -/
theorem thetaTraceSq_eq_hsInner :
    thetaTraceSq = hsInner (ContinuousLinearMap.adjoint thetaKernelOperator) thetaKernelOperator :=
  opTrace_comp_eq_hsInner _ _

/-- **The trace invariant is bounded by the Hilbert--Schmidt energy.** -/
theorem norm_thetaTraceSq_le :
    ‖thetaTraceSq‖ ≤ hsNorm thetaKernelOperator * hsNorm thetaKernelOperator :=
  norm_opTrace_comp_le isHilbertSchmidt_thetaKernelOperator'
    isHilbertSchmidt_thetaKernelOperator'

end HedenmalmThetaSource

end

end RHTower
