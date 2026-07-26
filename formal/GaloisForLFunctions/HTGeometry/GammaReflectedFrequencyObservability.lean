import GaloisForLFunctions.HTGeometry.GammaOrientationQuotientBoundary
import GaloisForLFunctions.HTGeometry.ThermalCFTGammaResponseBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Reflected-frequency observability for opposite-orientation Gamma clocks

For the amplitude

`A(z) = Gamma(z+a) / Gamma(-z+b)`,

frequency reflection gives `A(-z)`.  The two natural observation channels are

`I(z) = A(z) * A(-z)` and `P(z) = A(z) / A(-z)`.

The intensity is the quotient of the thermal reflection kernels at weights `a` and `b`.  When
`b=a+n`, the two Gamma sectors cancel by Pochhammer recurrence and leave an explicit nonzero
differentially algebraic sine--rational gauge.  In contrast, Euler reflection converts the phase
quotient into a DA gauge times four positive-charge Gamma clocks, so it is unconditionally
hypertranscendental.  This is an observation-channel theorem, not a temporal-evolution theorem.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The explicit sine--Pochhammer gauge relating reflection kernels whose weights differ by a
nonnegative integer. -/
def gammaReflectionIntegerShiftGaugeMero (h : ℂ) (n : ℕ) : meroField Set.univ :=
  gammaReflectionGaugeMero h / gammaReflectionGaugeMero (h + (n : ℂ)) *
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ (gammaOrbitNatFactor h n))⁻¹ *
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ
        (gammaOrbitNatFactor (1 - (h + (n : ℂ))) n))⁻¹

/-- **Integer-shift reflection-kernel value relation.**  A quotient of reflected Gamma products
at weights separated by `n` is exactly a sine gauge divided by two Pochhammer factors. -/
theorem gammaReflectionProductMero_div_add_nat (h : ℂ) (n : ℕ) :
    gammaReflectionProductMero h /
        gammaReflectionProductMero (h + (n : ℂ)) =
      gammaReflectionIntegerShiftGaugeMero h n := by
  rw [gammaReflectionProductMero, gammaReflectionProductMero,
    gammaNegativeShiftMero_reflection, gammaNegativeShiftMero_reflection]
  rw [gammaShiftMero_add_nat h n]
  rw [show 1 - h = (1 - (h + (n : ℂ))) + (n : ℂ) by ring,
    gammaShiftMero_add_nat]
  have hgh : gammaShiftMero h ≠ 0 := gammaShiftMero_ne_zero h
  have hgq : gammaShiftMero (1 - (h + (n : ℂ))) ≠ 0 :=
    gammaShiftMero_ne_zero _
  have hrh : gammaReflectionGaugeMero h ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero h
  have hrhn : gammaReflectionGaugeMero (h + (n : ℂ)) ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero _
  have hph : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ (gammaOrbitNatFactor h n) ≠ 0 :=
    (map_ne_zero_iff _
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).injective).mpr
        (gammaOrbitNatFactor_ne_zero h n)
  have hpq : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ
        (gammaOrbitNatFactor (1 - (h + (n : ℂ))) n) ≠ 0 :=
    (map_ne_zero_iff _
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).injective).mpr
        (gammaOrbitNatFactor_ne_zero _ n)
  unfold gammaReflectionIntegerShiftGaugeMero
  field_simp [hgh, hgq, hrh, hrhn, hph, hpq]

/-- The integer-shift reflection gauge is differentially algebraic. -/
theorem differentialAlgebraicOver_gammaReflectionIntegerShiftGaugeMero
    (h : ℂ) (n : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaReflectionIntegerShiftGaugeMero h n) := by
  unfold gammaReflectionIntegerShiftGaugeMero
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_mul
      (HTGeometry.differentialAlgebraicOver_div
        (differentialAlgebraicOver_gammaReflectionGaugeMero h)
        (differentialAlgebraicOver_gammaReflectionGaugeMero (h + (n : ℂ))))
      (HTGeometry.differentialAlgebraicOver_inv
        (HTGeometry.differentialAlgebraicOver_algebraMap
          (gammaOrbitNatFactor h n))))
    (HTGeometry.differentialAlgebraicOver_inv
      (HTGeometry.differentialAlgebraicOver_algebraMap
        (gammaOrbitNatFactor (1 - (h + (n : ℂ))) n)))

/-- The frequency-reflected carrier `A(-z)`. -/
def gammaOppositeShiftReflectedFrequencyMero (a b : ℂ) : meroField Set.univ :=
  gammaNegativeShiftMero a / gammaShiftMero b

/-- The reflected-frequency intensity channel `A(z) A(-z)`. -/
def gammaOppositeShiftIntensityMero (a b : ℂ) : meroField Set.univ :=
  gammaOppositeShiftQuotientMero a b *
    gammaOppositeShiftReflectedFrequencyMero a b

/-- The orientation-sensitive phase channel `A(z) / A(-z)`. -/
def gammaOppositeShiftPhaseMero (a b : ℂ) : meroField Set.univ :=
  gammaOppositeShiftQuotientMero a b /
    gammaOppositeShiftReflectedFrequencyMero a b

theorem gammaOppositeShiftReflectedFrequencyMero_ne_zero (a b : ℂ) :
    gammaOppositeShiftReflectedFrequencyMero a b ≠ 0 := by
  exact div_ne_zero
    (by
      rw [gammaNegativeShiftMero_reflection]
      exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero a)
        (inv_ne_zero (gammaShiftMero_ne_zero (1 - a))))
    (gammaShiftMero_ne_zero b)

theorem gammaOppositeShiftQuotientMero_ne_zero (a b : ℂ) :
    gammaOppositeShiftQuotientMero a b ≠ 0 := by
  unfold gammaOppositeShiftQuotientMero
  exact div_ne_zero (gammaShiftMero_ne_zero a)
    (by
      rw [gammaNegativeShiftMero_reflection]
      exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero b)
        (inv_ne_zero (gammaShiftMero_ne_zero (1 - b))))

/-- Multiplying the phase and intensity observations recovers the squared amplitude. -/
theorem gammaOppositeShiftPhase_mul_intensity (a b : ℂ) :
    gammaOppositeShiftPhaseMero a b *
        gammaOppositeShiftIntensityMero a b =
      (gammaOppositeShiftQuotientMero a b) ^ 2 := by
  unfold gammaOppositeShiftPhaseMero gammaOppositeShiftIntensityMero
  field_simp [gammaOppositeShiftReflectedFrequencyMero_ne_zero a b]

/-- Dividing intensity by phase recovers the squared reflected amplitude. -/
theorem gammaOppositeShiftIntensity_div_phase (a b : ℂ) :
    gammaOppositeShiftIntensityMero a b /
        gammaOppositeShiftPhaseMero a b =
      (gammaOppositeShiftReflectedFrequencyMero a b) ^ 2 := by
  unfold gammaOppositeShiftPhaseMero gammaOppositeShiftIntensityMero
  field_simp [gammaOppositeShiftReflectedFrequencyMero_ne_zero a b,
    gammaOppositeShiftQuotientMero_ne_zero a b]

/-- Reflected-frequency intensity is a quotient of two thermal reflection kernels. -/
theorem gammaOppositeShiftIntensityMero_eq_reflectionProduct_div
    (a b : ℂ) :
    gammaOppositeShiftIntensityMero a b =
      gammaReflectionProductMero a / gammaReflectionProductMero b := by
  unfold gammaOppositeShiftIntensityMero
  unfold gammaOppositeShiftQuotientMero
  unfold gammaOppositeShiftReflectedFrequencyMero
  unfold gammaReflectionProductMero
  have hpa : gammaShiftMero a ≠ 0 := gammaShiftMero_ne_zero a
  have hpb : gammaShiftMero b ≠ 0 := gammaShiftMero_ne_zero b
  have hna : gammaNegativeShiftMero a ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero a)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - a)))
  have hnb : gammaNegativeShiftMero b ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero b)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - b)))
  field_simp [hpa, hpb, hna, hnb]

/-- At an integer weight separation, intensity is exactly the DA shift gauge. -/
theorem gammaOppositeShiftIntensityMero_eq_integerShiftGauge
    (a : ℂ) (n : ℕ) :
    gammaOppositeShiftIntensityMero a (a + (n : ℂ)) =
      gammaReflectionIntegerShiftGaugeMero a n := by
  rw [gammaOppositeShiftIntensityMero_eq_reflectionProduct_div,
    gammaReflectionProductMero_div_add_nat]

/-- Integer-separated opposite-orientation clocks have DA reflected-frequency intensity. -/
theorem differentialAlgebraicOver_gammaOppositeShiftIntensityMero_add_nat
    (a : ℂ) (n : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaOppositeShiftIntensityMero a (a + (n : ℂ))) := by
  rw [gammaOppositeShiftIntensityMero_eq_integerShiftGauge]
  exact differentialAlgebraicOver_gammaReflectionIntegerShiftGaugeMero a n

/-- The phase is the symmetric product of the two opposite-orientation quotient clocks. -/
theorem gammaOppositeShiftPhaseMero_eq_symmetricProduct (a b : ℂ) :
    gammaOppositeShiftPhaseMero a b =
      gammaOppositeShiftQuotientMero a b *
        gammaOppositeShiftQuotientMero b a := by
  unfold gammaOppositeShiftPhaseMero
  unfold gammaOppositeShiftReflectedFrequencyMero
  unfold gammaOppositeShiftQuotientMero
  have hpa : gammaShiftMero a ≠ 0 := gammaShiftMero_ne_zero a
  have hpb : gammaShiftMero b ≠ 0 := gammaShiftMero_ne_zero b
  have hna : gammaNegativeShiftMero a ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero a)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - a)))
  have hnb : gammaNegativeShiftMero b ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero b)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - b)))
  field_simp [hpa, hpb, hna, hnb]

/-- The four positive-charge Gamma factors exposed by reflecting the phase quotient. -/
def gammaOppositeShiftPhasePositiveProductMero (a b : ℂ) : meroField Set.univ :=
  gammaFintypeOrbitProductMero
    ![a, 1 - b, b, 1 - a]
    (fun _ : Fin 4 => (1 : ℤ))

/-- Euler-reflection normal form of the phase observation. -/
theorem gammaOppositeShiftPhaseMero_reflectionNormalForm (a b : ℂ) :
    gammaOppositeShiftPhaseMero a b =
      ((gammaReflectionGaugeMero b)⁻¹ *
        (gammaReflectionGaugeMero a)⁻¹) *
          gammaOppositeShiftPhasePositiveProductMero a b := by
  rw [gammaOppositeShiftPhaseMero_eq_symmetricProduct,
    gammaOppositeShiftQuotientMero_reflectionNormalForm,
    gammaOppositeShiftQuotientMero_reflectionNormalForm]
  simp only [gammaPositiveShiftPairMero,
    gammaOppositeShiftPhasePositiveProductMero,
    gammaFintypeOrbitProductMero, zpow_one, Fin.prod_univ_four]
  simp
  ring

/-- The positive-charge product in the reflected phase is unconditionally HT, including every
integer collision among its four centers. -/
theorem hypertranscendentalOver_gammaOppositeShiftPhasePositiveProductMero
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftPhasePositiveProductMero a b) := by
  exact hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos
    ![a, 1 - b, b, 1 - a]
    (fun _ : Fin 4 => (1 : ℤ))
    (by intro i; norm_num)

/-- **Phase--intensity observability split.**  The phase quotient of every opposite-orientation
Gamma clock is hypertranscendental, with no shift-separation hypothesis. -/
theorem hypertranscendentalOver_gammaOppositeShiftPhaseMero (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftPhaseMero a b) := by
  rw [gammaOppositeShiftPhaseMero_reflectionNormalForm, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (HTGeometry.differentialAlgebraicOver_mul
      (HTGeometry.differentialAlgebraicOver_inv
        (differentialAlgebraicOver_gammaReflectionGaugeMero b))
      (HTGeometry.differentialAlgebraicOver_inv
        (differentialAlgebraicOver_gammaReflectionGaugeMero a)))
    (mul_ne_zero
      (inv_ne_zero (gammaReflectionGaugeMero_ne_zero b))
      (inv_ne_zero (gammaReflectionGaugeMero_ne_zero a)))).2
        (hypertranscendentalOver_gammaOppositeShiftPhasePositiveProductMero a b)

end

end GaloisForLFunctions
