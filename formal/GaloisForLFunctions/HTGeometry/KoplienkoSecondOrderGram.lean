import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Second-order regularization of a Gram perturbation

For a Hilbert--Schmidt perturbation, Koplienko's trace formula applies to the second-order Taylor
remainder: the unperturbed value and the first variation are subtracted before taking a trace.
For a Gram observable this subtraction is completely explicit.  If `P` is the principal channel
and `c R` the perturbation, then

```text
(P+cR)†(P+cR) - P†P
  - (c P†R + conj(c) R†P)
    = |c|² R†R.
```

Thus a second-order regularization retains only the positive quadratic residual energy and cannot
retain information carried solely by the first variation.

The trace-regularization provenance is L. S. Koplienko, *The trace formula for perturbations of
nonnuclear type*, Siberian Math. J. 25 (1984), 735--743,
DOI 10.1007/BF00968686.  The theorem below is the exact bounded-operator Gram algebra that occurs
before any trace is taken; it needs no Schatten or trace hypothesis.
-/

namespace HTGeometry

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Raw change of the Gram operator under the perturbation `P ↦ P + c R`. -/
def gramPerturbation
    (P R : E →L[ℂ] F) (c : ℂ) : E →L[ℂ] E :=
  ContinuousLinearMap.adjoint (P + c • R) ∘L (P + c • R) -
    ContinuousLinearMap.adjoint P ∘L P

/-- First variation of the Gram operator in the direction `c R`. -/
def gramFirstVariation
    (P R : E →L[ℂ] F) (c : ℂ) : E →L[ℂ] E :=
  c • (ContinuousLinearMap.adjoint P ∘L R) +
    star c • (ContinuousLinearMap.adjoint R ∘L P)

/-- Koplienko's second-order subtraction at the Gram-operator level. -/
def gramSecondOrderRemainder
    (P R : E →L[ℂ] F) (c : ℂ) : E →L[ℂ] E :=
  gramPerturbation P R c - gramFirstVariation P R c

/-- **Second-order Gram collapse.**  Subtracting the first variation leaves exactly the squared
residual channel. -/
theorem gramSecondOrderRemainder_eq_residualEnergy
    (P R : E →L[ℂ] F) (c : ℂ) :
    gramSecondOrderRemainder P R c =
      (star c * c) • (ContinuousLinearMap.adjoint R ∘L R) := by
  have hadj :
      ContinuousLinearMap.adjoint (P + c • R) =
        ContinuousLinearMap.adjoint P +
          star c • ContinuousLinearMap.adjoint R := by
    rw [ContinuousLinearMap.adjoint.map_add,
      ContinuousLinearMap.adjoint.map_smulₛₗ]
    simp only [starRingEnd_apply]
  unfold gramSecondOrderRemainder gramPerturbation gramFirstVariation
  rw [hadj]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply,
    _root_.sub_apply, _root_.smul_apply, map_add, map_smul]
  module

/-- The second-order remainder vanishes at zero perturbation. -/
@[simp]
theorem gramSecondOrderRemainder_zero
    (P R : E →L[ℂ] F) :
    gramSecondOrderRemainder P R 0 = 0 := by
  rw [gramSecondOrderRemainder_eq_residualEnergy]
  simp

end

end HTGeometry
