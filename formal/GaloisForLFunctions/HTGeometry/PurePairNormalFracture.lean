import Mathlib

/-!
# Cartan-coordinate audit of a compatible Spin(10) pure pair

This file formalizes the ten quadratic Cartan equations in the even-form chart
`ℂ ⊕ Λ²ℂ⁵ ⊕ Λ⁴ℂ⁵`, using a skew matrix for the two-form and five dual
coordinates for the four-form.

The main result is an exact local obstruction.  At the chosen compatible pair
`(1, e⁴ ∧ e⁵)`, a variation tangent to the second Cartan pure-spinor locus has
zero weak/disagreement reporter.  Conversely, every agreement-three-vector
occurs along such a tangent variation.  The color-preserving weak doublet is
therefore represented by transverse, rather than pure-tangent, variations in
this coordinate model.

No physical interpretation of these coordinate subspaces is asserted here.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev SpinTenEvenCoordinate :=
  ℂ × Matrix (Fin 5) (Fin 5) ℂ × (Fin 5 → ℂ)

def spinTenScalar (x : SpinTenEvenCoordinate) : ℂ := x.1
def spinTenTwo (x : SpinTenEvenCoordinate) : Matrix (Fin 5) (Fin 5) ℂ := x.2.1
def spinTenFour (x : SpinTenEvenCoordinate) : Fin 5 → ℂ := x.2.2

/-- Five upper Cartan quadrics, written as scalar-times-four-form plus Pfaffian minors. -/
def spinTenCartanUpper (x : SpinTenEvenCoordinate) : Fin 5 → ℂ :=
  ![
    spinTenScalar x * spinTenFour x 0 +
      (spinTenTwo x 1 2 * spinTenTwo x 3 4 -
       spinTenTwo x 1 3 * spinTenTwo x 2 4 +
       spinTenTwo x 1 4 * spinTenTwo x 2 3),
    spinTenScalar x * spinTenFour x 1 -
      (spinTenTwo x 0 2 * spinTenTwo x 3 4 -
       spinTenTwo x 0 3 * spinTenTwo x 2 4 +
       spinTenTwo x 0 4 * spinTenTwo x 2 3),
    spinTenScalar x * spinTenFour x 2 +
      (spinTenTwo x 0 1 * spinTenTwo x 3 4 -
       spinTenTwo x 0 3 * spinTenTwo x 1 4 +
       spinTenTwo x 0 4 * spinTenTwo x 1 3),
    spinTenScalar x * spinTenFour x 3 -
      (spinTenTwo x 0 1 * spinTenTwo x 2 4 -
       spinTenTwo x 0 2 * spinTenTwo x 1 4 +
       spinTenTwo x 0 4 * spinTenTwo x 1 2),
    spinTenScalar x * spinTenFour x 4 +
      (spinTenTwo x 0 1 * spinTenTwo x 2 3 -
       spinTenTwo x 0 2 * spinTenTwo x 1 3 +
       spinTenTwo x 0 3 * spinTenTwo x 1 2)
  ]

/-- Five lower Cartan quadrics. -/
def spinTenCartanLower (x : SpinTenEvenCoordinate) : Fin 5 → ℂ :=
  fun i => ∑ j, spinTenTwo x i j * spinTenFour x j

def spinTenCartanQuadrics (x : SpinTenEvenCoordinate) :
    (Fin 5 → ℂ) × (Fin 5 → ℂ) :=
  (spinTenCartanUpper x, spinTenCartanLower x)

/-- Polar coefficient of the Cartan quadrics. -/
def spinTenCartanPolar
    (x y : SpinTenEvenCoordinate) :
    (Fin 5 → ℂ) × (Fin 5 → ℂ) :=
  spinTenCartanQuadrics (x + y) -
    spinTenCartanQuadrics x - spinTenCartanQuadrics y

/-- The first pure spinor `1`. -/
def firstPurePairSpinor : SpinTenEvenCoordinate :=
  (1, 0, 0)

/-- The second pure spinor `e⁴∧e⁵`, with its skew-matrix coordinates. -/
def secondPurePairSpinor : SpinTenEvenCoordinate :=
  (0, fun i j =>
    if i = 3 ∧ j = 4 then 1
    else if i = 4 ∧ j = 3 then -1
    else 0, 0)

theorem firstPurePairSpinor_cartan :
    spinTenCartanQuadrics firstPurePairSpinor = 0 := by
  ext i <;> fin_cases i <;>
    simp [spinTenCartanQuadrics, spinTenCartanUpper, spinTenCartanLower,
      firstPurePairSpinor, spinTenScalar, spinTenTwo, spinTenFour]

theorem secondPurePairSpinor_cartan :
    spinTenCartanQuadrics secondPurePairSpinor = 0 := by
  ext i <;> fin_cases i <;>
    simp [spinTenCartanQuadrics, spinTenCartanUpper, spinTenCartanLower,
      secondPurePairSpinor, spinTenScalar, spinTenTwo, spinTenFour]

/-- The cross-purity vector reporter against the first spinor is the four-form coordinate. -/
def firstPairVectorReporter (v : SpinTenEvenCoordinate) : Fin 5 → ℂ :=
  spinTenFour v

theorem firstPairVectorReporter_eq_cartanPolar_upper
    (v : SpinTenEvenCoordinate) :
    (spinTenCartanPolar firstPurePairSpinor v).1 =
      firstPairVectorReporter v := by
  funext i
  fin_cases i <;>
    simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanUpper,
      firstPurePairSpinor, firstPairVectorReporter, spinTenScalar, spinTenTwo, spinTenFour]
  all_goals ring

theorem firstPair_cartanPolar_lower_eq_zero
    (v : SpinTenEvenCoordinate) :
    (spinTenCartanPolar firstPurePairSpinor v).2 = 0 := by
  funext i
  fin_cases i <;>
    simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanLower,
      firstPurePairSpinor, spinTenTwo, spinTenFour]

/-- Exact linearized Cartan system at the second member of the pair. -/
def tangentCartanAtSecond (v : SpinTenEvenCoordinate) : Prop :=
  spinTenCartanPolar secondPurePairSpinor v = 0

theorem tangentCartanAtSecond_iff (v : SpinTenEvenCoordinate) :
    tangentCartanAtSecond v ↔
      spinTenTwo v 0 1 = 0 ∧
      spinTenTwo v 0 2 = 0 ∧
      spinTenTwo v 1 2 = 0 ∧
      spinTenFour v 3 = 0 ∧
      spinTenFour v 4 = 0 := by
  constructor
  · intro h
    change spinTenCartanPolar secondPurePairSpinor v = 0 at h
    have hu := congrArg Prod.fst h
    have hl := congrArg Prod.snd h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change v.2.1 0 1 = 0
      have hu2 := congrFun hu 2
      simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanUpper,
        secondPurePairSpinor, spinTenScalar, spinTenTwo, spinTenFour] at hu2
      linear_combination hu2
    · change v.2.1 0 2 = 0
      have hu1 := congrFun hu 1
      simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanUpper,
        secondPurePairSpinor, spinTenScalar, spinTenTwo, spinTenFour] at hu1
      linear_combination -hu1
    · change v.2.1 1 2 = 0
      have hu0 := congrFun hu 0
      simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanUpper,
        secondPurePairSpinor, spinTenScalar, spinTenTwo, spinTenFour] at hu0
      linear_combination hu0
    · change v.2.2 3 = 0
      have hl4 := congrFun hl 4
      simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanLower,
        secondPurePairSpinor, spinTenTwo, spinTenFour,
        Fin.sum_univ_succ] at hl4
      linear_combination -hl4
    · change v.2.2 4 = 0
      have hl3 := congrFun hl 3
      simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanLower,
        secondPurePairSpinor, spinTenTwo, spinTenFour,
        Fin.sum_univ_succ] at hl3
      linear_combination hl3
  · rintro ⟨h01, h02, h12, h3, h4⟩
    change v.2.1 0 1 = 0 at h01
    change v.2.1 0 2 = 0 at h02
    change v.2.1 1 2 = 0 at h12
    change v.2.2 3 = 0 at h3
    change v.2.2 4 = 0 at h4
    change spinTenCartanPolar secondPurePairSpinor v = 0
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanUpper,
          secondPurePairSpinor, spinTenScalar, spinTenTwo, spinTenFour,
          h01, h02, h12]
    · funext i
      fin_cases i <;>
        simp [spinTenCartanPolar, spinTenCartanQuadrics, spinTenCartanLower,
          secondPurePairSpinor, spinTenTwo, spinTenFour, Fin.sum_univ_succ, h3, h4]

def purePairAgreementReporter (v : SpinTenEvenCoordinate) : Fin 3 → ℂ :=
  ![firstPairVectorReporter v 0,
    firstPairVectorReporter v 1,
    firstPairVectorReporter v 2]

def purePairDisagreementReporter (v : SpinTenEvenCoordinate) : Fin 2 → ℂ :=
  ![firstPairVectorReporter v 3,
    firstPairVectorReporter v 4]

/-- Pure tangent motion has identically zero first-order disagreement defect. -/
theorem purePairDisagreementReporter_eq_zero_of_tangent
    (v : SpinTenEvenCoordinate)
    (hv : tangentCartanAtSecond v) :
    purePairDisagreementReporter v = 0 := by
  rw [tangentCartanAtSecond_iff] at hv
  rcases hv with ⟨_, _, _, h3, h4⟩
  funext i
  fin_cases i <;>
    simp [purePairDisagreementReporter, firstPairVectorReporter, h3, h4]

/-- Every complex agreement-three-vector occurs as a pure tangent cross defect. -/
def pureTangentVariationOfAgreement
    (c : Fin 3 → ℂ) : SpinTenEvenCoordinate :=
  (0, 0, ![c 0, c 1, c 2, 0, 0])

theorem pureTangentVariationOfAgreement_is_tangent
    (c : Fin 3 → ℂ) :
    tangentCartanAtSecond (pureTangentVariationOfAgreement c) := by
  rw [tangentCartanAtSecond_iff]
  simp [pureTangentVariationOfAgreement, spinTenTwo, spinTenFour]

theorem purePairAgreementReporter_variationOfAgreement
    (c : Fin 3 → ℂ) :
    purePairAgreementReporter (pureTangentVariationOfAgreement c) = c := by
  funext i
  fin_cases i <;>
    simp [purePairAgreementReporter, pureTangentVariationOfAgreement,
      firstPairVectorReporter, spinTenFour]

abbrev ColorPreservingNormal := Fin 2 → ℂ

def colorPreservingNormalVariation
    (w : ColorPreservingNormal) : SpinTenEvenCoordinate :=
  (0, 0, ![0, 0, 0, w 0, w 1])

theorem colorPreservingNormal_agreement_eq_zero
    (w : ColorPreservingNormal) :
    purePairAgreementReporter (colorPreservingNormalVariation w) = 0 := by
  funext i
  fin_cases i <;>
    simp [purePairAgreementReporter, colorPreservingNormalVariation,
      firstPairVectorReporter, spinTenFour]

theorem colorPreservingNormal_disagreement_eq
    (w : ColorPreservingNormal) :
    purePairDisagreementReporter (colorPreservingNormalVariation w) = w := by
  funext i
  fin_cases i <;>
    simp [purePairDisagreementReporter, colorPreservingNormalVariation,
      firstPairVectorReporter, spinTenFour]

theorem colorPreservingNormal_not_tangent_of_ne_zero
    (w : ColorPreservingNormal) (hw : w ≠ 0) :
    ¬ tangentCartanAtSecond (colorPreservingNormalVariation w) := by
  intro ht
  have hz := purePairDisagreementReporter_eq_zero_of_tangent _ ht
  rw [colorPreservingNormal_disagreement_eq] at hz
  exact hw hz

theorem finrank_colorPreservingNormal_complex :
    Module.finrank ℂ ColorPreservingNormal = 2 := by
  simp [ColorPreservingNormal]

theorem finrank_colorPreservingNormal_real :
    Module.finrank ℝ ColorPreservingNormal = 4 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ ColorPreservingNormal,
    Complex.finrank_real_complex, finrank_colorPreservingNormal_complex]

end GaloisForLFunctions.HTGeometry
