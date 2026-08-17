import GaloisForLFunctions.RHTower.CCMRestrictedWeilSourceAlignedFiniteBlock

/-!
# Arbitrarily accurate source-aligned finite reduction

The fixed source head gives a universal quarter-norm loss.  Compactness of the literal
Gamma--Slepian embedding gives more: for every positive accuracy `delta`, a finite peripheral
Gamma--Slepian head captures the full restricted-Weil form up to `delta` times head mass.

Consequently every hypothetical nonpositive direction produces, at every requested accuracy, a
nonzero finite-source vector on which the literal prime compression overcompensates scalar Gamma
plus rank-two polar by `(1 - delta)` times its norm.  No fixed loss or source-conditioning constant
remains in the obstruction.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Gamma--Slepian cutoff giving source-reduction error below `delta`. -/
def ccmRestrictedWeilSourceAccuracyThreshold
    (a : SuzukiPositiveAperture) (delta : ℝ) : ℝ :=
  delta /
    (8 * (ccmRestrictedWeilRemainderEnvelope a + 1) ^ 2 * (delta + 1))

theorem ccmRestrictedWeilSourceAccuracyThreshold_pos
    (a : SuzukiPositiveAperture) {delta : ℝ} (hdelta : 0 < delta) :
    0 < ccmRestrictedWeilSourceAccuracyThreshold a delta := by
  unfold ccmRestrictedWeilSourceAccuracyThreshold
  have hE := ccmRestrictedWeilRemainderEnvelope_nonneg a
  positivity

theorem remainderEnvelope_mul_sourceAccuracyThreshold_lt_eighth
    (a : SuzukiPositiveAperture) {delta : ℝ} (hdelta : 0 < delta) :
    ccmRestrictedWeilRemainderEnvelope a *
        ccmRestrictedWeilSourceAccuracyThreshold a delta < (1 : ℝ) / 8 := by
  let E := ccmRestrictedWeilRemainderEnvelope a
  have hE : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hden : 0 < 8 * (E + 1) ^ 2 * (delta + 1) := by positivity
  change E * (delta / (8 * (E + 1) ^ 2 * (delta + 1))) < (1 : ℝ) / 8
  rw [show E * (delta / (8 * (E + 1) ^ 2 * (delta + 1))) =
      E * delta / (8 * (E + 1) ^ 2 * (delta + 1)) by ring,
    div_lt_iff₀ hden]
  nlinarith [mul_nonneg (sq_nonneg E) hdelta.le]

theorem two_mul_remainderEnvelope_sq_mul_sourceAccuracyThreshold_lt
    (a : SuzukiPositiveAperture) {delta : ℝ} (hdelta : 0 < delta) :
    2 * ccmRestrictedWeilRemainderEnvelope a ^ 2 *
        ccmRestrictedWeilSourceAccuracyThreshold a delta < delta := by
  let E := ccmRestrictedWeilRemainderEnvelope a
  have hE : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hden : 0 < 4 * (E + 1) ^ 2 * (delta + 1) := by positivity
  change 2 * E ^ 2 * (delta / (8 * (E + 1) ^ 2 * (delta + 1))) < delta
  rw [show 2 * E ^ 2 * (delta / (8 * (E + 1) ^ 2 * (delta + 1))) =
      E ^ 2 * delta / (4 * (E + 1) ^ 2 * (delta + 1)) by
        field_simp
        ring,
    div_lt_iff₀ hden]
  nlinarith [mul_nonneg (sq_nonneg E) hdelta.le,
    mul_pos (sq_pos_of_pos (by linarith : 0 < E + 1)) hdelta]

/-- Finite Gamma--Slepian head selected at a requested form-approximation accuracy. -/
structure CCMRestrictedWeilSourceApproximationCertificate
    (a : SuzukiPositiveAperture) (delta : ℝ) where
  exterior : Submodule ℂ (CCMArchimedeanFormDomain a)
  exterior_isClosed : IsClosed (exterior : Set (CCMArchimedeanFormDomain a))
  sourceHead_finiteDimensional : FiniteDimensional ℂ exterior.orthogonal
  sourceHead_eq_gammaSlepianPeripheral : exterior.orthogonal =
    compactPeripheralSpectralSubspace (ccmArchimedeanGammaSlepianGram a)
      (ccmRestrictedWeilSourceAccuracyThreshold a delta)
  exterior_gammaSlepian_invariant : ∀ u ∈ exterior,
    ccmArchimedeanGammaSlepianGram a u ∈ exterior
  sourceHead_gammaSlepian_invariant : ∀ u ∈ exterior.orthogonal,
    ccmArchimedeanGammaSlepianGram a u ∈ exterior.orthogonal
  exterior_physicalMass_lt : ∀ u ∈ exterior, u ≠ 0 →
    ‖ccmArchimedeanFormToAperture a u‖ ^ 2 <
      ccmRestrictedWeilSourceAccuracyThreshold a delta * ‖u‖ ^ 2

set_option maxHeartbeats 1000000 in
/-- Every positive accuracy has an actual finite peripheral Gamma--Slepian source head. -/
theorem exists_ccmRestrictedWeil_sourceApproximationCertificate
    (a : SuzukiPositiveAperture) {delta : ℝ} (hdelta : 0 < delta) :
    Nonempty (CCMRestrictedWeilSourceApproximationCertificate a delta) := by
  let G := ccmArchimedeanGammaSlepianGram a
  let eps := ccmRestrictedWeilSourceAccuracyThreshold a delta
  obtain ⟨M, hMclosed, hMfinite, hMperipheral, hMinv, hMperpinv, hcontract⟩ :=
    exists_finiteCodimensional_reducing_strictContraction G
      (isCompactOperator_ccmArchimedeanGammaSlepianGram a)
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp
        (ccmArchimedeanGammaSlepianGram_isSelfAdjoint a))
      eps (ccmRestrictedWeilSourceAccuracyThreshold_pos a hdelta)
  have hmass : ∀ u ∈ M, u ≠ 0 →
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 < eps * ‖u‖ ^ 2 := by
    intro u hu hune
    have hGnorm : ‖G u‖ < eps * ‖u‖ := hcontract u hu hune
    have henergy := ccmArchimedeanGammaSlepianGram_reApplyInnerSelf a u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at henergy
    have hcauchy : (inner ℂ (G u) u).re ≤ ‖G u‖ * ‖u‖ := by
      refine le_trans (Complex.re_le_norm _) ?_
      exact norm_inner_le_norm (𝕜 := ℂ) (G u) u
    have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hune
    change ‖ccmArchimedeanFormToAperture a u‖ ^ 2 < eps * ‖u‖ ^ 2
    rw [← henergy]
    calc
      _ ≤ ‖G u‖ * ‖u‖ := hcauchy
      _ < (eps * ‖u‖) * ‖u‖ := mul_lt_mul_of_pos_right hGnorm hupos
      _ = eps * ‖u‖ ^ 2 := by ring
  exact ⟨⟨M, hMclosed, hMfinite, hMperipheral, hMinv, hMperpinv, hmass⟩⟩

/-- Orthogonal projection onto the accuracy-dependent finite Gamma--Slepian source head. -/
noncomputable def CCMRestrictedWeilSourceApproximationCertificate.sourceHeadProjection
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta) :
    CCMArchimedeanFormDomain a →L[ℂ] C.exterior.orthogonal := by
  let M := C.exterior
  letI : FiniteDimensional ℂ M.orthogonal := C.sourceHead_finiteDimensional
  letI : CompleteSpace M.orthogonal := inferInstance
  letI : M.orthogonal.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
  exact M.orthogonal.orthogonalProjectionOnto

/-- The accuracy-dependent exterior is strictly coercive for the full prime--polar form. -/
theorem CCMRestrictedWeilSourceApproximationCertificate.exterior_coercive
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta)
    (hdelta : 0 < delta) (u : CCMArchimedeanFormDomain a)
    (hu : u ∈ C.exterior) (hune : u ≠ 0) :
    (7 / 8 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re := by
  let E := ccmRestrictedWeilRemainderEnvelope a
  let eps := ccmRestrictedWeilSourceAccuracyThreshold a delta
  have hE0 : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hmass := C.exterior_physicalMass_lt u hu hune
  have hcost : E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 <
      (1 / 8 : ℝ) * ‖u‖ ^ 2 := by
    have hcoef : E * eps < (1 : ℝ) / 8 :=
      remainderEnvelope_mul_sourceAccuracyThreshold_lt_eighth a hdelta
    have hnormsq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hune)
    calc
      E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2
          ≤ E * (eps * ‖u‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (le_of_lt hmass) hE0
      _ = (E * eps) * ‖u‖ ^ 2 := by ring
      _ < (1 / 8 : ℝ) * ‖u‖ ^ 2 := mul_lt_mul_of_pos_right hcoef hnormsq
  have hlower := ccmRestrictedWeilForm_sourceRelative_lowerBound a u
  dsimp only [E] at hcost
  linarith

theorem CCMRestrictedWeilSourceApproximationCertificate.nonzero_nonpositive_not_mem_exterior
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta)
    (hdelta : 0 < delta) (u : CCMArchimedeanFormDomain a)
    (hune : u ≠ 0) (hQ : (ccmRestrictedWeilForm a u u).re ≤ 0) :
    u ∉ C.exterior := by
  intro hu
  have hnormsq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hune)
  have hpos := C.exterior_coercive hdelta u hu hune
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Arbitrarily accurate source-relative finite-block lower bound.**  Full restricted-Weil form
is bounded below by its finite Gamma--Slepian head compression with any prescribed positive
norm-tax.  Exterior and head--tail prime--polar couplings remain intact. -/
theorem CCMRestrictedWeilSourceApproximationCertificate.form_ge_sourceHead_sub_accuracy
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta)
    (hdelta : 0 < delta) (u : CCMArchimedeanFormDomain a) :
    (ccmRestrictedWeilForm a
        (C.sourceHeadProjection u : CCMArchimedeanFormDomain a)
        (C.sourceHeadProjection u : CCMArchimedeanFormDomain a)).re -
        delta * ‖C.sourceHeadProjection u‖ ^ 2 ≤
      (ccmRestrictedWeilForm a u u).re := by
  let M := C.exterior
  let A := ccmArchimedeanFormToAperture a
  let B := ccmRestrictedWeilBoundedRemainder a
  let eps := ccmRestrictedWeilSourceAccuracyThreshold a delta
  let E := ccmRestrictedWeilRemainderEnvelope a
  letI : CompleteSpace M := C.exterior_isClosed.completeSpace_coe
  letI : M.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M
  letI : FiniteDimensional ℂ M.orthogonal := C.sourceHead_finiteDimensional
  letI : CompleteSpace M.orthogonal := inferInstance
  letI : M.orthogonal.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
  let m : M := M.orthogonalProjectionOnto u
  let f : M.orthogonal := M.orthogonal.orthogonalProjectionOnto u
  have hsourceHeadProjection : C.sourceHeadProjection u = f := rfl
  have hdecomp : (m : CCMArchimedeanFormDomain a) +
      (f : CCMArchimedeanFormDomain a) = u := by
    change M.starProjection u + M.orthogonal.starProjection u = u
    exact M.starProjection_add_starProjection_orthogonal u
  have hnormadd :
      ‖(m : CCMArchimedeanFormDomain a) + (f : CCMArchimedeanFormDomain a)‖ ^ 2 =
        ‖m‖ ^ 2 + ‖f‖ ^ 2 := by
    rw [hdecomp]
    exact Submodule.norm_sq_eq_add_norm_sq_projection u M
  have hsplit :
      (ccmRestrictedWeilForm a u u).re =
        (ccmRestrictedWeilForm a
          (m : CCMArchimedeanFormDomain a)
          (m : CCMArchimedeanFormDomain a)).re +
        (ccmRestrictedWeilForm a
          (f : CCMArchimedeanFormDomain a)
          (f : CCMArchimedeanFormDomain a)).re +
        (inner ℂ (B (A (m : CCMArchimedeanFormDomain a)))
          (A (f : CCMArchimedeanFormDomain a))).re +
        (inner ℂ (B (A (f : CCMArchimedeanFormDomain a)))
          (A (m : CCMArchimedeanFormDomain a))).re := by
    rw [← hdecomp]
    rw [ccmRestrictedWeilForm_self_re_eq_norm_add_physicalRemainder]
    rw [ccmRestrictedWeilForm_self_re_eq_norm_add_physicalRemainder]
    rw [ccmRestrictedWeilForm_self_re_eq_norm_add_physicalRemainder]
    dsimp only [A, B]
    simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
    rw [hnormadd]
    rw [show ‖(m : CCMArchimedeanFormDomain a)‖ = ‖m‖ from rfl,
      show ‖(f : CCMArchimedeanFormDomain a)‖ = ‖f‖ from rfl]
    ring
  have hmassM : ‖A (m : CCMArchimedeanFormDomain a)‖ ^ 2 ≤
      eps * ‖m‖ ^ 2 := by
    by_cases hm : m = 0
    · simp [hm]
    exact le_of_lt (C.exterior_physicalMass_lt
      (m : CCMArchimedeanFormDomain a) m.property
      (fun hz => hm (Subtype.ext hz)))
  have hmassF : ‖A (f : CCMArchimedeanFormDomain a)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have h := norm_ccmArchimedeanFormToAperture_le a
      (f : CCMArchimedeanFormDomain a)
    change ‖A (f : CCMArchimedeanFormDomain a)‖ ≤ ‖f‖ at h
    nlinarith [norm_nonneg (A (f : CCMArchimedeanFormDomain a)), norm_nonneg f]
  have hE0 : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have heps0 : 0 ≤ eps :=
    (ccmRestrictedWeilSourceAccuracyThreshold_pos a hdelta).le
  have htailLower := ccmRestrictedWeilForm_sourceRelative_lowerBound a
    (m : CCMArchimedeanFormDomain a)
  have hEeps : E * eps ≤ (1 : ℝ) / 8 :=
    le_of_lt (remainderEnvelope_mul_sourceAccuracyThreshold_lt_eighth a hdelta)
  have htailCost : E * ‖A (m : CCMArchimedeanFormDomain a)‖ ^ 2 ≤
      (1 / 8 : ℝ) * ‖m‖ ^ 2 := by
    calc
      E * ‖A (m : CCMArchimedeanFormDomain a)‖ ^ 2
          ≤ E * (eps * ‖m‖ ^ 2) := mul_le_mul_of_nonneg_left hmassM hE0
      _ = (E * eps) * ‖m‖ ^ 2 := by ring
      _ ≤ (1 / 8 : ℝ) * ‖m‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hEeps (sq_nonneg ‖m‖)
  have htailForm : (7 / 8 : ℝ) * ‖m‖ ^ 2 ≤
      (ccmRestrictedWeilForm a
        (m : CCMArchimedeanFormDomain a)
        (m : CCMArchimedeanFormDomain a)).re := by
    change ‖m‖ ^ 2 - E * ‖A (m : CCMArchimedeanFormDomain a)‖ ^ 2 ≤
      (ccmRestrictedWeilForm a
        (m : CCMArchimedeanFormDomain a)
        (m : CCMArchimedeanFormDomain a)).re at htailLower
    linarith
  have hBnorm : ‖B‖ ≤ E := norm_ccmRestrictedWeilBoundedRemainder_le_envelope a
  have hcrossLower (x y : suzukiApertureHilbert a) :
      -(E * ‖x‖ * ‖y‖) ≤ (inner ℂ (B x) y).re := by
    have hBapply : ‖B x‖ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
    have hnegCauchy : -(inner ℂ (B x) y).re ≤ ‖B x‖ * ‖y‖ := by
      calc
        -(inner ℂ (B x) y).re = (inner ℂ (-(B x)) y).re := by simp
        _ ≤ ‖-(B x)‖ * ‖y‖ := by
          refine le_trans (Complex.re_le_norm _) ?_
          exact norm_inner_le_norm (𝕜 := ℂ) (-(B x)) y
        _ = ‖B x‖ * ‖y‖ := by rw [norm_neg]
    have hupper : ‖B x‖ * ‖y‖ ≤ E * ‖x‖ * ‖y‖ := by
      calc
        _ ≤ (‖B‖ * ‖x‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right hBapply (norm_nonneg y)
        _ ≤ (E * ‖x‖) * ‖y‖ := by gcongr
    linarith
  let X : ℝ := E * ‖A (m : CCMArchimedeanFormDomain a)‖ *
    ‖A (f : CCMArchimedeanFormDomain a)‖
  have hX0 : 0 ≤ X := by positivity
  have hmassProduct :
      ‖A (m : CCMArchimedeanFormDomain a)‖ ^ 2 *
          ‖A (f : CCMArchimedeanFormDomain a)‖ ^ 2 ≤
        (eps * ‖m‖ ^ 2) * ‖f‖ ^ 2 := by
    exact mul_le_mul hmassM hmassF (sq_nonneg _)
      (mul_nonneg heps0 (sq_nonneg ‖m‖))
  have hXsq : X ^ 2 ≤
      (E ^ 2 * eps * ‖f‖ ^ 2) * ‖m‖ ^ 2 := by
    calc
      X ^ 2 = E ^ 2 *
          (‖A (m : CCMArchimedeanFormDomain a)‖ ^ 2 *
            ‖A (f : CCMArchimedeanFormDomain a)‖ ^ 2) := by
        dsimp only [X]
        ring
      _ ≤ E ^ 2 * ((eps * ‖m‖ ^ 2) * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmassProduct (sq_nonneg E)
      _ = (E ^ 2 * eps * ‖f‖ ^ 2) * ‖m‖ ^ 2 := by ring
  have hYoung : 2 * X ≤
      (1 / 2 : ℝ) * ‖m‖ ^ 2 +
        2 * (E ^ 2 * eps * ‖f‖ ^ 2) := by
    have hright0 : 0 ≤ (1 / 2 : ℝ) * ‖m‖ ^ 2 +
        2 * (E ^ 2 * eps * ‖f‖ ^ 2) := by positivity
    have hsquare := sq_nonneg
      ((1 / 2 : ℝ) * ‖m‖ ^ 2 - 2 * (E ^ 2 * eps * ‖f‖ ^ 2))
    nlinarith
  have hcrossSum :
      -(2 * X) ≤
        (inner ℂ (B (A (m : CCMArchimedeanFormDomain a)))
          (A (f : CCMArchimedeanFormDomain a))).re +
        (inner ℂ (B (A (f : CCMArchimedeanFormDomain a)))
          (A (m : CCMArchimedeanFormDomain a))).re := by
    have h1 := hcrossLower (A (m : CCMArchimedeanFormDomain a))
      (A (f : CCMArchimedeanFormDomain a))
    have h2 := hcrossLower (A (f : CCMArchimedeanFormDomain a))
      (A (m : CCMArchimedeanFormDomain a))
    dsimp only [X]
    nlinarith
  have haccuracy : 2 * E ^ 2 * eps < delta :=
    two_mul_remainderEnvelope_sq_mul_sourceAccuracyThreshold_lt a hdelta
  rw [hsourceHeadProjection]
  change (ccmRestrictedWeilForm a
      (f : CCMArchimedeanFormDomain a)
      (f : CCMArchimedeanFormDomain a)).re -
      delta * ‖f‖ ^ 2 ≤ (ccmRestrictedWeilForm a u u).re
  rw [hsplit]
  nlinarith [sq_nonneg ‖m‖, sq_nonneg ‖f‖]

/-- A nonzero nonpositive direction has a nonzero projection into every positive-accuracy source
head. -/
theorem CCMRestrictedWeilSourceApproximationCertificate.sourceHeadProjection_ne_zero_of_nonpositive
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta)
    (hdelta : 0 < delta) (u : CCMArchimedeanFormDomain a)
    (hune : u ≠ 0) (hQ : (ccmRestrictedWeilForm a u u).re ≤ 0) :
    C.sourceHeadProjection u ≠ 0 := by
  let M := C.exterior
  letI : CompleteSpace M := C.exterior_isClosed.completeSpace_coe
  letI : M.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M
  letI : FiniteDimensional ℂ M.orthogonal := C.sourceHead_finiteDimensional
  letI : CompleteSpace M.orthogonal := inferInstance
  letI : M.orthogonal.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
  let m : M := M.orthogonalProjectionOnto u
  let f : M.orthogonal := M.orthogonal.orthogonalProjectionOnto u
  have hprojection : C.sourceHeadProjection u = f := rfl
  have hdecomp : (m : CCMArchimedeanFormDomain a) +
      (f : CCMArchimedeanFormDomain a) = u := by
    change M.starProjection u + M.orthogonal.starProjection u = u
    exact M.starProjection_add_starProjection_orthogonal u
  intro hp
  have hf : f = 0 := by rw [← hprojection]; exact hp
  have huM : u ∈ M := by
    have hu : u = (m : CCMArchimedeanFormDomain a) := by
      rw [← hdecomp, hf]
      simp
    rw [hu]
    exact m.property
  exact C.nonzero_nonpositive_not_mem_exterior hdelta u hune hQ huM

/-- **Accuracy-sharp finite-source obstruction.**  A nonpositive direction yields a nonzero finite
Gamma--Slepian head vector where prime compression exceeds scalar Gamma plus polar by the margin
`1 - delta`.  Since `delta` is arbitrary, the earlier fixed `3/4` margin is not intrinsic. -/
theorem CCMRestrictedWeilSourceApproximationCertificate.sourceHead_prime_overcompensation_of_nonpositive
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta)
    (hdelta : 0 < delta) (u : CCMArchimedeanFormDomain a)
    (hune : u ≠ 0) (hQ : (ccmRestrictedWeilForm a u u).re ≤ 0) :
    let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection u
    h ≠ 0 ∧
      (1 - delta) * ‖h‖ ^ 2 +
          (inner ℂ
            ((ccmArchimedeanRemainderScalar •
              ccmArchimedeanGammaSlepianGram a) h) h).re +
          (inner ℂ (ccmRestrictedWeilFormPolarCompression a h) h).re ≤
        (inner ℂ (ccmRestrictedWeilFormPrimeCompression a h) h).re := by
  dsimp only
  let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection u
  have hhneSub := C.sourceHeadProjection_ne_zero_of_nonpositive hdelta u hune hQ
  have hhne : h ≠ 0 := by
    intro hh
    apply hhneSub
    apply Subtype.ext
    exact hh
  have hheadLower := C.form_ge_sourceHead_sub_accuracy hdelta u
  have hheadQ : (ccmRestrictedWeilForm a h h).re ≤ delta * ‖h‖ ^ 2 := by
    have hnorm : ‖h‖ = ‖C.sourceHeadProjection u‖ := rfl
    dsimp only [h]
    rw [hnorm]
    linarith
  have hform := ccmRestrictedWeilForm_self_re_eq_norm_add_formRemainder a h
  rw [ccmRestrictedWeilFormRemainder_eq_scalarGamma_add_polar_sub_prime] at hform
  simp only [add_apply, sub_apply, inner_add_left, inner_sub_left,
    Complex.add_re, Complex.sub_re] at hform
  refine ⟨hhne, ?_⟩
  linarith

end RHTower
