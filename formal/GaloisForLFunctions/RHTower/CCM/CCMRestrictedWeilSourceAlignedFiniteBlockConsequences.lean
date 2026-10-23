import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilSourceAlignedFiniteBlock

/-!
# Quantitative consequences of source-aligned restricted-Weil finite reduction

Quarter-loss head compression, literal von Mangoldt overcompensation, and the sharper
linear-envelope rank reduction.  Kept separate from the foundational finite-block construction so
consumers needing only its source-selected exterior do not elaborate these expensive consequences.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Source-relative finite-block lower bound.**  The full literal restricted-Weil form is bounded
below by its value on the finite Gamma--Slepian source head, with a universal quarter-norm loss.
All exterior and head--tail prime--polar couplings are included in the estimate. -/
theorem CCMRestrictedWeilSourceAlignedBlockCertificate.form_ge_sourceHead_sub_quarter
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilSourceAlignedBlockCertificate a)
    (u : CCMArchimedeanFormDomain a) :
    (ccmRestrictedWeilForm a
        (C.sourceHeadProjection u : CCMArchimedeanFormDomain a)
        (C.sourceHeadProjection u : CCMArchimedeanFormDomain a)).re -
        (1 / 4 : ℝ) * ‖C.sourceHeadProjection u‖ ^ 2 ≤
      (ccmRestrictedWeilForm a u u).re := by
  let M := C.exterior
  let A := ccmArchimedeanFormToAperture a
  let B := ccmRestrictedWeilBoundedRemainder a
  let eps := ccmRestrictedWeilSourceHeadThreshold a
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
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hE0 : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have heps0 : 0 ≤ eps := (ccmRestrictedWeilSourceHeadThreshold_pos a).le
  have htailLower := ccmRestrictedWeilForm_sourceRelative_lowerBound a
    (m : CCMArchimedeanFormDomain a)
  have hEeps : E * eps ≤ (1 : ℝ) / 8 :=
    le_of_lt (ccmRestrictedWeilRemainderEnvelope_mul_sourceHeadThreshold_lt_eighth a)
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
    change E * ‖A (m : CCMArchimedeanFormDomain a)‖ ^ 2 ≤
      (1 / 8 : ℝ) * ‖m‖ ^ 2 at htailCost
    linarith only [htailLower, htailCost]
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
        _ ≤ (E * ‖x‖) * ‖y‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBnorm (norm_nonneg x)) (norm_nonneg y)
    linarith only [hnegCauchy, hupper]
  let X : ℝ := E * ‖A (m : CCMArchimedeanFormDomain a)‖ *
    ‖A (f : CCMArchimedeanFormDomain a)‖
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
    apply two_mul_le_add_of_sq_le_mul (by positivity) (by positivity)
    calc
      X ^ 2 ≤ (E ^ 2 * eps * ‖f‖ ^ 2) * ‖m‖ ^ 2 := hXsq
      _ = ((1 / 2 : ℝ) * ‖m‖ ^ 2) *
          (2 * (E ^ 2 * eps * ‖f‖ ^ 2)) := by ring
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
    linarith only [h1, h2]
  have hquarter : 2 * E ^ 2 * eps < (1 : ℝ) / 4 :=
    two_mul_remainderEnvelope_sq_mul_sourceHeadThreshold_lt_quarter a
  have hquarterCost : 2 * (E ^ 2 * eps * ‖f‖ ^ 2) ≤
      (1 / 4 : ℝ) * ‖f‖ ^ 2 := by
    calc
      2 * (E ^ 2 * eps * ‖f‖ ^ 2) = (2 * E ^ 2 * eps) * ‖f‖ ^ 2 := by ring
      _ ≤ (1 / 4 : ℝ) * ‖f‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hquarter.le (sq_nonneg ‖f‖)
  rw [hsourceHeadProjection]
  change (ccmRestrictedWeilForm a
      (f : CCMArchimedeanFormDomain a)
      (f : CCMArchimedeanFormDomain a)).re -
      (1 / 4 : ℝ) * ‖f‖ ^ 2 ≤ (ccmRestrictedWeilForm a u u).re
  rw [hsplit]
  linarith only [htailForm, hYoung, hcrossSum, hquarterCost, sq_nonneg ‖m‖]

/-- Exact form-domain presentation of the restricted-Weil quadratic as identity plus the
compressed scalar--polar--prime source remainder. -/
theorem ccmRestrictedWeilForm_self_re_eq_norm_add_formRemainder
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (ccmRestrictedWeilForm a u u).re =
      ‖u‖ ^ 2 + (inner ℂ (ccmRestrictedWeilFormRemainder a u) u).re := by
  have hid := congrArg Complex.re
    (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a u u)
  rw [ccmRestrictedWeilFormBirmanSchwinger_zero_eq_neg_remainder] at hid
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  simpa only [neg_apply, inner_neg_left, sub_neg_eq_add, Complex.add_re, hself] using hid

/-- **Literal finite-source obstruction.**  Any nonzero nonpositive direction forces a nonzero
vector in the finite peripheral Gamma--Slepian source head on which finite von Mangoldt compression
overcompensates the scalar Gamma block and rank-two polar block by at least three quarters of the
head norm.  Thus a negative direction cannot hide in an ill-conditioned source projection. -/
theorem CCMRestrictedWeilSourceAlignedBlockCertificate.sourceHead_prime_overcompensation_of_nonpositive
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilSourceAlignedBlockCertificate a)
    (u : CCMArchimedeanFormDomain a) (hune : u ≠ 0)
    (hQ : (ccmRestrictedWeilForm a u u).re ≤ 0) :
    let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection u
    h ≠ 0 ∧
      (ccmRestrictedWeilForm a h h).re ≤ (1 / 4 : ℝ) * ‖h‖ ^ 2 ∧
      (3 / 4 : ℝ) * ‖h‖ ^ 2 +
          (inner ℂ
            ((ccmArchimedeanRemainderScalar •
              ccmArchimedeanGammaSlepianGram a) h) h).re +
          (inner ℂ (ccmRestrictedWeilFormPolarCompression a h) h).re ≤
        (inner ℂ (ccmRestrictedWeilFormPrimeCompression a h) h).re := by
  dsimp only
  let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection u
  have hheadLower := C.form_ge_sourceHead_sub_quarter u
  have hheadQ : (ccmRestrictedWeilForm a h h).re ≤
      (1 / 4 : ℝ) * ‖h‖ ^ 2 := by
    have hnorm : ‖h‖ = ‖C.sourceHeadProjection u‖ := rfl
    dsimp only [h]
    rw [hnorm]
    linarith only [hheadLower, hQ]
  have hhne : h ≠ 0 := by
    intro hh
    have hprojection := C.sourceHeadProjection_lower_of_nonpositive u hune hQ
    have hpzero : C.sourceHeadProjection u = 0 := by
      apply Subtype.ext
      exact hh
    rw [hpzero] at hprojection
    have hunorm : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hune)
    have hfalse : (1 / 2 : ℝ) * ‖u‖ ^ 2 < 0 := by
      simpa using hprojection
    linarith only [hunorm, hfalse]
  have hform := ccmRestrictedWeilForm_self_re_eq_norm_add_formRemainder a h
  rw [ccmRestrictedWeilFormRemainder_eq_scalarGamma_add_polar_sub_prime] at hform
  simp only [add_apply, sub_apply, inner_add_left, inner_sub_left,
    Complex.add_re, Complex.sub_re] at hform
  refine ⟨hhne, hheadQ, ?_⟩
  linarith

/-- Expanded arithmetic form of the finite-source obstruction.  The right side is the literal
finite von Mangoldt-weighted sum of the two logarithmic translations; the left retains both polar
boundary evaluations and the scalar Gamma--Slepian energy. -/
theorem CCMRestrictedWeilSourceAlignedBlockCertificate.sourceHead_literal_vonMangoldt_overcompensation_of_nonpositive
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilSourceAlignedBlockCertificate a)
    (u : CCMArchimedeanFormDomain a) (hune : u ≠ 0)
    (hQ : (ccmRestrictedWeilForm a u u).re ≤ 0) :
    let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection u
    h ≠ 0 ∧
      (3 / 4 : ℝ) * ‖h‖ ^ 2 +
          (inner ℂ
            ((ccmArchimedeanRemainderScalar •
              ccmArchimedeanGammaSlepianGram a) h) h).re +
          (star (inner ℂ (ccmPolarApertureVector a (-1 / 2))
                (ccmArchimedeanFormToAperture a h)) *
              inner ℂ (ccmPolarApertureVector a (1 / 2))
                (ccmArchimedeanFormToAperture a h) +
            star (inner ℂ (ccmPolarApertureVector a (1 / 2))
                (ccmArchimedeanFormToAperture a h)) *
              inner ℂ (ccmPolarApertureVector a (-1 / 2))
                (ccmArchimedeanFormToAperture a h)).re ≤
        (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (((1 / Real.sqrt n : ℝ) : ℂ) *
              (inner ℂ (logTranslationCLM (Real.log n)
                    (ccmArchimedeanFormToAperture a h).1)
                  (ccmArchimedeanFormToAperture a h).1 +
                inner ℂ (logTranslationCLM (-Real.log n)
                    (ccmArchimedeanFormToAperture a h).1)
                  (ccmArchimedeanFormToAperture a h).1))).re := by
  dsimp only
  have hw := C.sourceHead_prime_overcompensation_of_nonpositive u hune hQ
  dsimp only at hw
  refine ⟨hw.1, ?_⟩
  have hineq := hw.2.2
  rw [inner_ccmRestrictedWeilFormPolarCompression,
    inner_ccmRestrictedWeilFormPrimeCompression] at hineq
  exact hineq

/-! ## Linear-envelope source head

The fixed certificate above uses a quadratic-envelope cutoff because its later head-compression
estimates pay two source-conditioning factors.  Excluding nonpositive directions from the exterior
uses only one factor.  The following cutoff is therefore the sharp scale for the rank problem. -/

/-- Source-head threshold at the linear, rather than quadratic, remainder-envelope scale. -/
def ccmRestrictedWeilLinearSourceHeadThreshold (a : SuzukiPositiveAperture) : ℝ :=
  1 / (2 * (ccmRestrictedWeilRemainderEnvelope a + 1))

theorem ccmRestrictedWeilLinearSourceHeadThreshold_pos (a : SuzukiPositiveAperture) :
    0 < ccmRestrictedWeilLinearSourceHeadThreshold a := by
  unfold ccmRestrictedWeilLinearSourceHeadThreshold
  have hE := ccmRestrictedWeilRemainderEnvelope_nonneg a
  positivity

theorem remainderEnvelope_mul_linearSourceHeadThreshold_lt_half
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilRemainderEnvelope a *
        ccmRestrictedWeilLinearSourceHeadThreshold a < (1 : ℝ) / 2 := by
  let E := ccmRestrictedWeilRemainderEnvelope a
  have hE : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  change E * (1 / (2 * (E + 1))) < (1 : ℝ) / 2
  rw [show E * (1 / (2 * (E + 1))) = E / (2 * (E + 1)) by ring,
    div_lt_iff₀ (show 0 < 2 * (E + 1) by positivity)]
  linarith

/-- **Sharpness of scalar-envelope coercivity.**  Suppose a coefficient `c` is claimed uniformly
from only the scalar facts `normSq - E * mass ≤ q` and `mass ≤ eps * normSq`.  Then necessarily
`c ≤ 1 - E * eps`.  Thus the linear envelope scale cannot be improved by retuning constants;
any stronger restricted-Weil reduction must use signed structure of the prime--polar remainder. -/
theorem coercivityCoefficient_le_of_scalarEnvelope_only
    {E eps c : ℝ} (heps : 0 ≤ eps)
    (hguarantee : ∀ normSq mass q : ℝ,
      0 ≤ normSq → 0 ≤ mass →
      normSq - E * mass ≤ q → mass ≤ eps * normSq →
      c * normSq ≤ q) :
    c ≤ 1 - E * eps := by
  have hsharp := hguarantee 1 eps (1 - E * eps)
    (by norm_num) heps (by rfl) (by simp)
  simpa only [mul_one] using hsharp

/-- The linear cutoff is strictly larger than the previous quadratic cutoff, hence selects a
smaller peripheral source head. -/
theorem sourceHeadThreshold_lt_linearSourceHeadThreshold
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceHeadThreshold a <
      ccmRestrictedWeilLinearSourceHeadThreshold a := by
  let E := ccmRestrictedWeilRemainderEnvelope a
  have hE : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  change 1 / (8 * (E + 1) ^ 2) < 1 / (2 * (E + 1))
  have hE1 : 0 < E + 1 := by positivity
  rw [one_div_lt_one_div (by positivity) (by positivity)]
  linarith only [hE, sq_nonneg E]

/-- Raising the spectral cutoff can only shrink the Gamma--Slepian peripheral space. -/
theorem linearSourceHead_le_sourceHead (a : SuzukiPositiveAperture) :
    compactPeripheralSpectralSubspace (ccmArchimedeanGammaSlepianGram a)
        (ccmRestrictedWeilLinearSourceHeadThreshold a) ≤
      compactPeripheralSpectralSubspace (ccmArchimedeanGammaSlepianGram a)
        (ccmRestrictedWeilSourceHeadThreshold a) := by
  rw [compactPeripheralSpectralSubspace, compactPeripheralSpectralSubspace]
  refine iSup_le fun mu => ?_
  let nu : {z : ℂ //
      z ∈ spectrum ℂ (ccmArchimedeanGammaSlepianGram a) ∧
        ccmRestrictedWeilSourceHeadThreshold a ≤ ‖z‖} :=
    ⟨mu.1, mu.2.1,
      (sourceHeadThreshold_lt_linearSourceHeadThreshold a).le.trans mu.2.2⟩
  simpa only [nu] using
    (le_iSup (fun z : {z : ℂ //
      z ∈ spectrum ℂ (ccmArchimedeanGammaSlepianGram a) ∧
        ccmRestrictedWeilSourceHeadThreshold a ≤ ‖z‖} =>
        Module.End.eigenspace
          (ccmArchimedeanGammaSlepianGram a).toLinearMap z) nu)

/-- A closed coercive exterior injects every nonpositive restricted-Weil block into its
finite-dimensional orthogonal head. -/
theorem nonpositiveBlock_finrank_le_orthogonal_of_exterior_pos
    (a : SuzukiPositiveAperture)
    (M : Submodule ℂ (CCMArchimedeanFormDomain a))
    (hMclosed : IsClosed (M : Set (CCMArchimedeanFormDomain a)))
    (hMfinite : FiniteDimensional ℂ M.orthogonal)
    (hMpos : ∀ u ∈ M, u ≠ 0 → 0 < (ccmRestrictedWeilForm a u u).re)
    (N : CCMRestrictedWeilNonpositiveBlock a) :
    Module.finrank ℂ N.carrier ≤ Module.finrank ℂ M.orthogonal := by
  letI : FiniteDimensional ℂ N.carrier := N.finiteDimensional a
  letI : CompleteSpace M := hMclosed.completeSpace_coe
  letI : M.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M
  letI : FiniteDimensional ℂ M.orthogonal := hMfinite
  letI : CompleteSpace M.orthogonal := inferInstance
  letI : M.orthogonal.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
  let P : N.carrier →ₗ[ℂ] M.orthogonal :=
    (M.orthogonal.orthogonalProjectionOnto ∘L N.carrier.subtypeL).toLinearMap
  apply LinearMap.finrank_le_finrank_of_injective
  intro x y hxy
  let z : N.carrier := x - y
  have hPz : P z = 0 := by
    dsimp only [z]
    rw [map_sub, hxy, sub_self]
  have hfzero : M.orthogonal.orthogonalProjectionOnto
      (z : CCMArchimedeanFormDomain a) = 0 := by
    change M.orthogonal.orthogonalProjectionOnto
      (z : CCMArchimedeanFormDomain a) = 0 at hPz
    exact hPz
  let m : M := M.orthogonalProjectionOnto (z : CCMArchimedeanFormDomain a)
  let f : M.orthogonal :=
    M.orthogonal.orthogonalProjectionOnto (z : CCMArchimedeanFormDomain a)
  have hf : f = 0 := hfzero
  have hdecomp : (m : CCMArchimedeanFormDomain a) +
      (f : CCMArchimedeanFormDomain a) = z := by
    change M.starProjection (z : CCMArchimedeanFormDomain a) +
      M.orthogonal.starProjection (z : CCMArchimedeanFormDomain a) = z
    exact M.starProjection_add_starProjection_orthogonal z
  have hzM : (z : CCMArchimedeanFormDomain a) ∈ M := by
    have hz : (z : CCMArchimedeanFormDomain a) = m := by
      rw [← hdecomp, hf]
      simp
    rw [hz]
    exact m.property
  have hznonpos :
      (ccmRestrictedWeilForm a
        (z : CCMArchimedeanFormDomain a) (z : CCMArchimedeanFormDomain a)).re ≤ 0 :=
    N.nonpositive z z.property
  have hzzero : (z : CCMArchimedeanFormDomain a) = 0 := by
    by_contra hz
    exact (not_lt_of_ge hznonpos) (hMpos z hzM hz)
  apply Subtype.ext
  exact sub_eq_zero.mp hzzero

/-- **Linear-envelope source-head rank bound.** Every nonpositive restricted-Weil block injects
into the Gamma--Slepian peripheral space at cutoff `1 / (2(E+1))`.  This removes one full power of
the explicit prime--polar remainder envelope from the previous source-aligned rank reduction. -/
theorem exists_ccmRestrictedWeil_linearSourceHead_rankBound
    (a : SuzukiPositiveAperture) :
    ∃ M : Submodule ℂ (CCMArchimedeanFormDomain a),
      IsClosed (M : Set (CCMArchimedeanFormDomain a)) ∧
      FiniteDimensional ℂ M.orthogonal ∧
      M.orthogonal =
        compactPeripheralSpectralSubspace (ccmArchimedeanGammaSlepianGram a)
          (ccmRestrictedWeilLinearSourceHeadThreshold a) ∧
      (∀ u ∈ M, u ≠ 0 →
        (1 / 2 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re) ∧
      ∀ N : CCMRestrictedWeilNonpositiveBlock a,
        Module.finrank ℂ N.carrier ≤ Module.finrank ℂ M.orthogonal := by
  let G := ccmArchimedeanGammaSlepianGram a
  let eps := ccmRestrictedWeilLinearSourceHeadThreshold a
  obtain ⟨M, hMclosed, hMfinite, hMperipheral, _hMinv, _hMperpinv, hcontract⟩ :=
    exists_finiteCodimensional_reducing_strictContraction G
      (isCompactOperator_ccmArchimedeanGammaSlepianGram a)
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp
        (ccmArchimedeanGammaSlepianGram_isSelfAdjoint a))
      eps (ccmRestrictedWeilLinearSourceHeadThreshold_pos a)
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
  have hcoercive : ∀ u ∈ M, u ≠ 0 →
      (1 / 2 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re := by
    intro u hu hune
    let E := ccmRestrictedWeilRemainderEnvelope a
    have hE0 : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
    have hmassle := le_of_lt (hmass u hu hune)
    have hcostle : E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
        E * (eps * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hmassle hE0
    have hcoef : E * eps < (1 : ℝ) / 2 :=
      remainderEnvelope_mul_linearSourceHeadThreshold_lt_half a
    have hnormsq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hune)
    have hcostlt : E * (eps * ‖u‖ ^ 2) < (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
      rw [← mul_assoc]
      exact mul_lt_mul_of_pos_right hcoef hnormsq
    have hlower := ccmRestrictedWeilForm_sourceRelative_lowerBound a u
    dsimp only [E] at hcostle hcostlt
    linarith only [hcostle, hcostlt, hlower]
  letI : FiniteDimensional ℂ M.orthogonal := hMfinite
  refine ⟨M, hMclosed, hMfinite, hMperipheral, hcoercive, ?_⟩
  intro N
  exact nonpositiveBlock_finrank_le_orthogonal_of_exterior_pos
    a M hMclosed hMfinite (fun u hu hune => by
      have hnormsq : 0 ≤ ‖u‖ ^ 2 := sq_nonneg ‖u‖
      linarith only [hnormsq, hcoercive u hu hune]) N

end RHTower
