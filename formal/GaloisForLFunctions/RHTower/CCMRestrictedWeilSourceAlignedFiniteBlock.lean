import GaloisForLFunctions.HTGeometry.CompactSelfAdjointReducingTail
import GaloisForLFunctions.RHTower.CCMRestrictedWeilOneSidedFiniteBlock
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundFrequencyLocalization

/-!
# Source-aligned finite reduction of the restricted-Weil form

The compact Birman--Schwinger reduction detects the finite negative sector, but its head is selected
from the full prime--polar operator.  Here the head is selected before that operator acts: it is the
peripheral spectral space of the literal Gamma--Slepian Gram `J_a† J_a`.

The exact factorization `R_a = J_a† B_a J_a` gives a source-relative lower bound.  Any vector on
which the restricted-Weil form is nonpositive must carry physical aperture mass at least
`‖u‖² / M(a)`, where `M(a)` is the explicit norm envelope of the bounded prime--polar source.
Compactness of `J_a† J_a` then gives a finite source head; on its orthogonal complement the full
restricted-Weil form, with every prime and polar term intact, is strictly bounded below by
`(1/2)‖u‖²`.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Exact physical-source presentation of the restricted-Weil quadratic form. -/
theorem ccmRestrictedWeilForm_self_re_eq_norm_add_physicalRemainder
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (ccmRestrictedWeilForm a u u).re =
      ‖u‖ ^ 2 +
        (inner ℂ
          (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
  let A := ccmArchimedeanFormToAperture a
  let B := ccmRestrictedWeilBoundedRemainder a
  have hid := congrArg Complex.re
    (ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner a u u)
  rw [ccmRestrictedWeilFormBirmanSchwinger_zero_eq_neg_remainder] at hid
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hrem : inner ℂ (ccmRestrictedWeilFormRemainder a u) u =
      inner ℂ (B (A u)) (A u) := by
    change inner ℂ (A.adjoint (B (A u))) u = _
    rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [neg_apply, inner_neg_left, sub_neg_eq_add, Complex.add_re, hself] at hid
  rw [hrem] at hid
  exact hid

/-- The explicit source envelope controls the full restricted-Weil form relative to physical
Gamma--Slepian mass, rather than merely by the form-domain norm. -/
theorem ccmRestrictedWeilForm_sourceRelative_lowerBound
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ‖u‖ ^ 2 - ccmRestrictedWeilRemainderEnvelope a *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      (ccmRestrictedWeilForm a u u).re := by
  let A := ccmArchimedeanFormToAperture a
  let B := ccmRestrictedWeilBoundedRemainder a
  let M := ccmRestrictedWeilRemainderEnvelope a
  have hBnorm : ‖B‖ ≤ M := norm_ccmRestrictedWeilBoundedRemainder_le_envelope a
  have hBapply : ‖B (A u)‖ ≤ ‖B‖ * ‖A u‖ := B.le_opNorm (A u)
  have hnegCauchy : -(inner ℂ (B (A u)) (A u)).re ≤
      ‖B (A u)‖ * ‖A u‖ := by
    calc
      -(inner ℂ (B (A u)) (A u)).re =
          (inner ℂ (-(B (A u))) (A u)).re := by simp
      _ ≤ ‖-(B (A u))‖ * ‖A u‖ := by
        refine le_trans (Complex.re_le_norm _) ?_
        exact norm_inner_le_norm (𝕜 := ℂ) (-(B (A u))) (A u)
      _ = ‖B (A u)‖ * ‖A u‖ := by rw [norm_neg]
  have hinnerLower :
      -(M * ‖A u‖ ^ 2) ≤ (inner ℂ (B (A u)) (A u)).re := by
    calc
      -(M * ‖A u‖ ^ 2) ≤ -(‖B‖ * ‖A u‖ ^ 2) := by gcongr
      _ = -((‖B‖ * ‖A u‖) * ‖A u‖) := by ring
      _ ≤ -(‖B (A u)‖ * ‖A u‖) := by gcongr
      _ ≤ (inner ℂ (B (A u)) (A u)).re := by linarith
  rw [ccmRestrictedWeilForm_self_re_eq_norm_add_physicalRemainder]
  dsimp only [M, A] at hinnerLower ⊢
  linarith

/-- Every nonpositive direction pays a literal physical-source mass floor. -/
theorem ccmRestrictedWeil_sourceMass_lower_of_nonpositive
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hQ : (ccmRestrictedWeilForm a u u).re ≤ 0) :
    ‖u‖ ^ 2 ≤ ccmRestrictedWeilRemainderEnvelope a *
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  linarith [ccmRestrictedWeilForm_sourceRelative_lowerBound a u]

/-- Spectral threshold at which the explicit source envelope costs strictly less than one half of
the ambient form norm. -/
def ccmRestrictedWeilSourceHeadThreshold (a : SuzukiPositiveAperture) : ℝ :=
  1 / (8 * (ccmRestrictedWeilRemainderEnvelope a + 1) ^ 2)

theorem ccmRestrictedWeilSourceHeadThreshold_pos (a : SuzukiPositiveAperture) :
    0 < ccmRestrictedWeilSourceHeadThreshold a := by
  unfold ccmRestrictedWeilSourceHeadThreshold
  have hM := ccmRestrictedWeilRemainderEnvelope_nonneg a
  positivity

theorem ccmRestrictedWeilRemainderEnvelope_mul_sourceHeadThreshold_lt_half
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilRemainderEnvelope a *
        ccmRestrictedWeilSourceHeadThreshold a < (1 : ℝ) / 2 := by
  let M := ccmRestrictedWeilRemainderEnvelope a
  have hM : 0 ≤ M := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hden : 0 < 8 * (M + 1) ^ 2 := by positivity
  change M * (1 / (8 * (M + 1) ^ 2)) < (1 : ℝ) / 2
  rw [show M * (1 / (8 * (M + 1) ^ 2)) = M / (8 * (M + 1) ^ 2) by ring,
    div_lt_iff₀ hden]
  nlinarith [sq_nonneg M]

theorem ccmRestrictedWeilRemainderEnvelope_mul_sourceHeadThreshold_lt_eighth
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilRemainderEnvelope a *
        ccmRestrictedWeilSourceHeadThreshold a < (1 : ℝ) / 8 := by
  let M := ccmRestrictedWeilRemainderEnvelope a
  have hM : 0 ≤ M := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hden : 0 < 8 * (M + 1) ^ 2 := by positivity
  change M * (1 / (8 * (M + 1) ^ 2)) < (1 : ℝ) / 8
  rw [show M * (1 / (8 * (M + 1) ^ 2)) = M / (8 * (M + 1) ^ 2) by ring,
    div_lt_iff₀ hden]
  nlinarith [sq_nonneg M]

theorem two_mul_remainderEnvelope_sq_mul_sourceHeadThreshold_lt_quarter
    (a : SuzukiPositiveAperture) :
    2 * ccmRestrictedWeilRemainderEnvelope a ^ 2 *
        ccmRestrictedWeilSourceHeadThreshold a < (1 : ℝ) / 4 := by
  let M := ccmRestrictedWeilRemainderEnvelope a
  have hM : 0 ≤ M := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hden : 0 < 8 * (M + 1) ^ 2 := by positivity
  change 2 * M ^ 2 * (1 / (8 * (M + 1) ^ 2)) < (1 : ℝ) / 4
  rw [show 2 * M ^ 2 * (1 / (8 * (M + 1) ^ 2)) =
      M ^ 2 / (4 * (M + 1) ^ 2) by ring,
    div_lt_iff₀ (show 0 < 4 * (M + 1) ^ 2 by positivity)]
  nlinarith [sq_nonneg M]

/-- Finite Gamma--Slepian head and coercive exterior selected solely from the literal source
embedding and its explicit bounded-remainder envelope. -/
structure CCMRestrictedWeilSourceAlignedBlockCertificate (a : SuzukiPositiveAperture) where
  exterior : Submodule ℂ (CCMArchimedeanFormDomain a)
  exterior_isClosed : IsClosed (exterior : Set (CCMArchimedeanFormDomain a))
  sourceHead_finiteDimensional : FiniteDimensional ℂ exterior.orthogonal
  sourceHead_eq_gammaSlepianPeripheral : exterior.orthogonal =
    compactPeripheralSpectralSubspace (ccmArchimedeanGammaSlepianGram a)
      (ccmRestrictedWeilSourceHeadThreshold a)
  exterior_gammaSlepian_invariant : ∀ u ∈ exterior,
    ccmArchimedeanGammaSlepianGram a u ∈ exterior
  sourceHead_gammaSlepian_invariant : ∀ u ∈ exterior.orthogonal,
    ccmArchimedeanGammaSlepianGram a u ∈ exterior.orthogonal
  exterior_physicalMass_lt : ∀ u ∈ exterior, u ≠ 0 →
    ‖ccmArchimedeanFormToAperture a u‖ ^ 2 <
      ccmRestrictedWeilSourceHeadThreshold a * ‖u‖ ^ 2
  exterior_coercive : ∀ u ∈ exterior, u ≠ 0 →
    (1 / 2 : ℝ) * ‖u‖ ^ 2 < (ccmRestrictedWeilForm a u u).re
  nonpositive_sourceMass_lower : ∀ u : CCMArchimedeanFormDomain a,
    (ccmRestrictedWeilForm a u u).re ≤ 0 →
      ‖u‖ ^ 2 ≤ ccmRestrictedWeilRemainderEnvelope a *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2
  nonzero_nonpositive_not_mem_exterior : ∀ u : CCMArchimedeanFormDomain a,
    u ≠ 0 → (ccmRestrictedWeilForm a u u).re ≤ 0 → u ∉ exterior

set_option maxHeartbeats 1000000 in
/-- The actual restricted-Weil form admits a source-aligned finite block.  Its complement has a
strict half-norm floor for the full intact prime--polar form. -/
theorem exists_ccmRestrictedWeil_sourceAlignedFiniteBlock
    (a : SuzukiPositiveAperture) :
    Nonempty (CCMRestrictedWeilSourceAlignedBlockCertificate a) := by
  let G := ccmArchimedeanGammaSlepianGram a
  let eps := ccmRestrictedWeilSourceHeadThreshold a
  obtain ⟨M, hMclosed, hMfinite, hMperipheral, hMinv, hMperpinv, hcontract⟩ :=
    exists_finiteCodimensional_reducing_strictContraction G
      (isCompactOperator_ccmArchimedeanGammaSlepianGram a)
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp
        (ccmArchimedeanGammaSlepianGram_isSelfAdjoint a))
      eps (ccmRestrictedWeilSourceHeadThreshold_pos a)
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
      ccmRestrictedWeilRemainderEnvelope_mul_sourceHeadThreshold_lt_half a
    have hnormsq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hune)
    have hcostlt : E * (eps * ‖u‖ ^ 2) < (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
      rw [← mul_assoc]
      exact mul_lt_mul_of_pos_right hcoef hnormsq
    have hlower := ccmRestrictedWeilForm_sourceRelative_lowerBound a u
    dsimp only [E] at hcostle hcostlt
    linarith
  refine ⟨⟨M, hMclosed, hMfinite, hMperipheral, hMinv, hMperpinv, hmass,
    hcoercive, ccmRestrictedWeil_sourceMass_lower_of_nonpositive a, ?_⟩⟩
  intro u hune hnonpos huM
  have hnormsq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hune)
  have hQpos : 0 < (ccmRestrictedWeilForm a u u).re := by
    linarith [hcoercive u huM hune]
  exact (not_lt_of_ge hnonpos) hQpos

/-- Every closed nonpositive block injects into the finite Gamma--Slepian source head.  This gives
an aperture-by-aperture dimension bound selected by the source embedding, not by diagonalizing the
prime--polar Birman--Schwinger operator. -/
theorem CCMRestrictedWeilSourceAlignedBlockCertificate.nonpositiveBlock_finrank_le_sourceHead
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilSourceAlignedBlockCertificate a)
    (N : CCMRestrictedWeilNonpositiveBlock a) :
    Module.finrank ℂ N.carrier ≤ Module.finrank ℂ C.exterior.orthogonal := by
  let M := C.exterior
  letI : FiniteDimensional ℂ N.carrier := N.finiteDimensional a
  letI : CompleteSpace M := C.exterior_isClosed.completeSpace_coe
  letI : M.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M
  letI : FiniteDimensional ℂ M.orthogonal := C.sourceHead_finiteDimensional
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
    exact C.nonzero_nonpositive_not_mem_exterior z hz hznonpos hzM
  apply Subtype.ext
  exact sub_eq_zero.mp hzzero

/-- Orthogonal projection onto the finite Gamma--Slepian source head carried by a source-aligned
certificate. -/
noncomputable def CCMRestrictedWeilSourceAlignedBlockCertificate.sourceHeadProjection
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilSourceAlignedBlockCertificate a) :
    CCMArchimedeanFormDomain a →L[ℂ] C.exterior.orthogonal := by
  let M := C.exterior
  letI : FiniteDimensional ℂ M.orthogonal := C.sourceHead_finiteDimensional
  letI : CompleteSpace M.orthogonal := inferInstance
  letI : M.orthogonal.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
  exact M.orthogonal.orthogonalProjectionOnto

/-- Quantitative source alignment of every nonzero nonpositive vector.  Orthogonal projection onto
the finite Gamma--Slepian head retains, after multiplication by the explicit source envelope, more
than one half of the full form-domain mass.  In particular the finite-head injection above has an
explicit lower singular-value bound. -/
theorem CCMRestrictedWeilSourceAlignedBlockCertificate.sourceHeadProjection_lower_of_nonpositive
    {a : SuzukiPositiveAperture}
    (C : CCMRestrictedWeilSourceAlignedBlockCertificate a)
    (u : CCMArchimedeanFormDomain a) (hune : u ≠ 0)
    (hQ : (ccmRestrictedWeilForm a u u).re ≤ 0) :
    (1 / 2 : ℝ) * ‖u‖ ^ 2 <
      ccmRestrictedWeilRemainderEnvelope a *
        ‖C.sourceHeadProjection u‖ ^ 2 := by
  let M := C.exterior
  let G := ccmArchimedeanGammaSlepianGram a
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
  have hnorm : ‖u‖ ^ 2 = ‖m‖ ^ 2 + ‖f‖ ^ 2 := by
    simpa only [m, f] using Submodule.norm_sq_eq_add_norm_sq_projection u M
  have hGm : G (m : CCMArchimedeanFormDomain a) ∈ M :=
    C.exterior_gammaSlepian_invariant m m.property
  have hGf : G (f : CCMArchimedeanFormDomain a) ∈ M.orthogonal :=
    C.sourceHead_gammaSlepian_invariant f f.property
  have hGm_f : inner ℂ (G (m : CCMArchimedeanFormDomain a))
      (f : CCMArchimedeanFormDomain a) = 0 :=
    (Submodule.mem_orthogonal M (f : CCMArchimedeanFormDomain a)).mp
      f.property (G (m : CCMArchimedeanFormDomain a)) hGm
  have hGf_m : inner ℂ (G (f : CCMArchimedeanFormDomain a))
      (m : CCMArchimedeanFormDomain a) = 0 :=
    (inner_eq_zero_symm
      (x := (m : CCMArchimedeanFormDomain a))
      (y := G (f : CCMArchimedeanFormDomain a))).mp
      ((Submodule.mem_orthogonal M
        (G (f : CCMArchimedeanFormDomain a))).mp hGf m m.property)
  have hmassDecomp : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 =
      (inner ℂ (G (m : CCMArchimedeanFormDomain a))
        (m : CCMArchimedeanFormDomain a)).re +
      (inner ℂ (G (f : CCMArchimedeanFormDomain a))
        (f : CCMArchimedeanFormDomain a)).re := by
    have henergy := ccmArchimedeanGammaSlepianGram_reApplyInnerSelf a u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at henergy
    change (inner ℂ (ccmArchimedeanGammaSlepianGram a u) u).re =
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 at henergy
    rw [← henergy, ← hdecomp]
    dsimp only [G] at hGm_f hGf_m ⊢
    simp only [map_add, inner_add_left, inner_add_right, hGm_f, hGf_m,
      add_zero, zero_add, Complex.add_re]
  have htail :
      (inner ℂ (G (m : CCMArchimedeanFormDomain a))
        (m : CCMArchimedeanFormDomain a)).re ≤ eps * ‖m‖ ^ 2 := by
    by_cases hm : m = 0
    · simp [hm]
    have hmass := C.exterior_physicalMass_lt
      (m : CCMArchimedeanFormDomain a) m.property
      (fun hz => hm (Subtype.ext hz))
    have henergy := ccmArchimedeanGammaSlepianGram_reApplyInnerSelf a
      (m : CCMArchimedeanFormDomain a)
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at henergy
    change RCLike.re (inner ℂ
      (ccmArchimedeanGammaSlepianGram a (m : CCMArchimedeanFormDomain a))
      (m : CCMArchimedeanFormDomain a)) ≤
        ccmRestrictedWeilSourceHeadThreshold a * ‖m‖ ^ 2
    calc
      _ = ‖ccmArchimedeanFormToAperture a
          (m : CCMArchimedeanFormDomain a)‖ ^ 2 := henergy
      _ ≤ ccmRestrictedWeilSourceHeadThreshold a * ‖m‖ ^ 2 := le_of_lt hmass
  have hhead :
      (inner ℂ (G (f : CCMArchimedeanFormDomain a))
        (f : CCMArchimedeanFormDomain a)).re ≤ ‖f‖ ^ 2 := by
    have hGnorm := norm_ccmArchimedeanGammaSlepianGram_le_one a
    calc
      _ ≤ ‖G (f : CCMArchimedeanFormDomain a)‖ * ‖f‖ := by
        refine le_trans (Complex.re_le_norm _) ?_
        exact norm_inner_le_norm (𝕜 := ℂ)
          (G (f : CCMArchimedeanFormDomain a))
          (f : CCMArchimedeanFormDomain a)
      _ ≤ (‖G‖ * ‖f‖) * ‖f‖ := by
        gcongr
        exact G.le_opNorm (f : CCMArchimedeanFormDomain a)
      _ ≤ (1 : ℝ) * ‖f‖ * ‖f‖ := by gcongr
      _ = ‖f‖ ^ 2 := by ring
  have hmassUpper : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      eps * ‖m‖ ^ 2 + ‖f‖ ^ 2 := by
    rw [hmassDecomp]
    exact add_le_add htail hhead
  have hE0 : 0 ≤ E := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hsourceFloor : ‖u‖ ^ 2 ≤
      E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
    ccmRestrictedWeil_sourceMass_lower_of_nonpositive a u hQ
  have htotal : ‖u‖ ^ 2 ≤ E * (eps * ‖m‖ ^ 2 + ‖f‖ ^ 2) :=
    hsourceFloor.trans (mul_le_mul_of_nonneg_left hmassUpper hE0)
  have hcoef : E * eps ≤ (1 : ℝ) / 2 :=
    le_of_lt (ccmRestrictedWeilRemainderEnvelope_mul_sourceHeadThreshold_lt_half a)
  have hmcoef : E * (eps * ‖m‖ ^ 2) ≤ (1 / 2 : ℝ) * ‖m‖ ^ 2 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖m‖)
  have hfne : f ≠ 0 := by
    intro hf
    have huM : u ∈ M := by
      have hu : u = (m : CCMArchimedeanFormDomain a) := by
        rw [← hdecomp, hf]
        simp
      rw [hu]
      exact m.property
    exact C.nonzero_nonpositive_not_mem_exterior u hune hQ huM
  have hfsq : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hfne)
  rw [hsourceHeadProjection]
  change (1 / 2 : ℝ) * ‖u‖ ^ 2 < E * ‖f‖ ^ 2
  nlinarith

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
    nlinarith [norm_nonneg (A (f : CCMArchimedeanFormDomain a)), norm_nonneg f]
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
    dsimp only [A, E] at htailLower htailCost
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
  have hquarter : 2 * E ^ 2 * eps < (1 : ℝ) / 4 :=
    two_mul_remainderEnvelope_sq_mul_sourceHeadThreshold_lt_quarter a
  rw [hsourceHeadProjection]
  change (ccmRestrictedWeilForm a
      (f : CCMArchimedeanFormDomain a)
      (f : CCMArchimedeanFormDomain a)).re -
      (1 / 4 : ℝ) * ‖f‖ ^ 2 ≤ (ccmRestrictedWeilForm a u u).re
  rw [hsplit]
  nlinarith [sq_nonneg ‖m‖, sq_nonneg ‖f‖]

end RHTower
