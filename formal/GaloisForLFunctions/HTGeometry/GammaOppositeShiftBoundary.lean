import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Opposite-shift Gamma-pair differential boundary

For arbitrary complex shifts `a` and `b`, Euler reflection identifies the observable

`Gamma(z + a) * Gamma(-z + b)`

with a nonzero differentially algebraic sine gauge times the translated Gamma ratio

`Gamma(z + a) / Gamma(z + 1 - b)`.

The existing Gamma-ratio superselection theorem therefore gives the exact boundary: the pair is
differentially algebraic precisely when `a + b` is an integer, and is hypertranscendental
otherwise.  This is the asymmetric parent law behind reflected thermal, detector, and black-hole
response kernels.  The selector is the translation-orbit closure seen by the observable; it is not
a temporal-evolution hypothesis.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The general complexified-frequency pair `Gamma(z+a) * Gamma(-z+b)`. -/
def gammaOppositeShiftProductMero (a b : ℂ) : meroField Set.univ :=
  gammaShiftMero a * gammaNegativeShiftMero b

/-- Euler reflection separates the pair into a DA sine gauge and one translated Gamma ratio. -/
theorem gammaOppositeShiftProductMero_eq_gauge_mul_reducedVeneziano (a b : ℂ) :
    gammaOppositeShiftProductMero a b =
      gammaReflectionGaugeMero b *
        reducedVenezianoAmplitudeMero a (1 - a - b) := by
  rw [gammaOppositeShiftProductMero, gammaNegativeShiftMero_reflection,
    reducedVenezianoAmplitudeMero]
  have harg : a + (1 - a - b) = 1 - b := by ring
  rw [harg]
  simp only [div_eq_mul_inv]
  ring

/-- **Exact asymmetric reflection boundary, orbit-separation form.**  The opposite-shift pair is
DA exactly when the reflected denominator lies on the numerator's integer-translation orbit. -/
theorem differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSeparation
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaOppositeShiftProductMero a b) ↔
      ∃ k : ℤ, 1 - a - b = (k : ℂ) := by
  rw [gammaOppositeShiftProductMero_eq_gauge_mul_reducedVeneziano]
  have hgDA := differentialAlgebraicOver_gammaReflectionGaugeMero b
  have hg0 := gammaReflectionGaugeMero_ne_zero b
  constructor
  · intro hproduct
    have hdiv := HTGeometry.differentialAlgebraicOver_div hproduct hgDA
    have heq :
        (gammaReflectionGaugeMero b *
            reducedVenezianoAmplitudeMero a (1 - a - b)) /
              gammaReflectionGaugeMero b =
          reducedVenezianoAmplitudeMero a (1 - a - b) := by
      field_simp [hg0]
    rw [heq] at hdiv
    exact (differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
      a (1 - a - b)).1 hdiv
  · intro hinteger
    exact HTGeometry.differentialAlgebraicOver_mul hgDA
      ((differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
        a (1 - a - b)).2 hinteger)

/-- The reflected-orbit separation is integral exactly when the sum of the two physical shifts is
integral. -/
theorem exists_integer_one_sub_gammaShiftSum_iff_integer_gammaShiftSum (a b : ℂ) :
    (∃ k : ℤ, 1 - a - b = (k : ℂ)) ↔ ∃ k : ℤ, a + b = (k : ℂ) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨1 - k, ?_⟩
    calc
      a + b = 1 - (1 - a - b) := by ring
      _ = 1 - (k : ℂ) := by rw [hk]
      _ = ((1 - k : ℤ) : ℂ) := by push_cast; ring
  · rintro ⟨k, hk⟩
    refine ⟨1 - k, ?_⟩
    calc
      1 - a - b = 1 - (a + b) := by ring
      _ = 1 - (k : ℂ) := by rw [hk]
      _ = ((1 - k : ℤ) : ℂ) := by push_cast; ring

/-- **Exact asymmetric reflection boundary, physical-shift form.** -/
theorem differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSum
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaOppositeShiftProductMero a b) ↔
      ∃ k : ℤ, a + b = (k : ℂ) := by
  rw [differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSeparation,
    exists_integer_one_sub_gammaShiftSum_iff_integer_gammaShiftSum]

/-- The opposite-shift response is hypertranscendental exactly off the integral shift-sum
lattice. -/
theorem hypertranscendentalOver_gammaOppositeShiftProductMero_iff_nonintegerSum
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (gammaOppositeShiftProductMero a b) ↔
      ∀ k : ℤ, a + b ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSum]
  push Not
  rfl

end

end GaloisForLFunctions
