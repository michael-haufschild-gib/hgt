import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaRegularRationalResidueNoGo

/-!
# Bounded symmetric-support singular pivots cannot escape the CCM--FU trace ideal

The actual causal-depth Gamma feature changes every regular finite circuit only by `S¹`.  This
module closes the bounded singular-pivot escape: for symmetric supported generalized inverses,
an `S¹` change of the pivot forces both the support and the generalized inverse to change by
`S¹`.  Hence finite circuits with generalized Schur complements remain invisible to ordinary
logarithmic singular residues.  No support-motion hypothesis is assumed.

The exact survivor is a genuinely unbounded generalized inverse, equivalently in the symmetric
self-adjoint setting a nonclosed-range pivot, or a reporter outside the principal weak-`S¹` class.
-/

namespace RHTower

open _root_.ContinuousLinearMap Filter
open scoped Topology

noncomputable section

private abbrev GammaH := SuzukiCausalDepthGammaTraceL2
private abbrev GammaOp := GammaH →L[ℂ] GammaH

/-- Bounded symmetric-support generalized inverse data.  These are the algebraic equations obeyed
by the Moore--Penrose inverse and orthogonal range support of a self-adjoint closed-range pivot. -/
structure SuzukiCausalDepthGammaSupportedGeneralizedInverse (A : GammaOp) where
  inverse : GammaOp
  support : GammaOp
  metric_mul_inverse : A ∘L inverse = support
  inverse_mul_metric : inverse ∘L A = support
  metric_mul_support : A ∘L support = A
  support_mul_metric : support ∘L A = A
  support_mul_inverse : support ∘L inverse = inverse
  inverse_mul_support : inverse ∘L support = inverse

/-- Support projections cannot move outside `S¹` under an `S¹` pivot perturbation.  The support
difference is factored into two bounded multiples of the pivot difference. -/
theorem suzukiCausalDepthGammaSupportedGeneralizedInverse_support_sub_memSchattenClass_one
    {A₀ A₁ : GammaOp}
    (d₀ : SuzukiCausalDepthGammaSupportedGeneralizedInverse A₀)
    (d₁ : SuzukiCausalDepthGammaSupportedGeneralizedInverse A₁)
    (hA : MemSchattenClass 1 (A₁ - A₀)) :
    MemSchattenClass 1 (d₁.support - d₀.support) := by
  have honeP₀ : A₀ ∘L (1 - d₀.support) = 0 := by
    have hmetric0 := d₀.metric_mul_support
    simp only [← ContinuousLinearMap.mul_def] at hmetric0 ⊢
    noncomm_ring [hmetric0]
  have honeP₁ : (1 - d₁.support) ∘L A₁ = 0 := by
    have hmetric1 := d₁.support_mul_metric
    simp only [← ContinuousLinearMap.mul_def] at hmetric1 ⊢
    noncomm_ring [hmetric1]
  have hleft : MemSchattenClass 1
      ((d₁.inverse ∘L (A₁ - A₀)) ∘L (1 - d₀.support)) :=
    memSchattenClass_one_comp_right
      (memSchattenClass_one_comp_left hA d₁.inverse) (1 - d₀.support)
  have hright : MemSchattenClass 1
      (((1 - d₁.support) ∘L (A₁ - A₀)) ∘L d₀.inverse) :=
    memSchattenClass_one_comp_right
      (memSchattenClass_one_comp_left hA (1 - d₁.support)) d₀.inverse
  have hzleft : (d₁.inverse ∘L A₀) ∘L (1 - d₀.support) = 0 := by
    rw [ContinuousLinearMap.comp_assoc, honeP₀, ContinuousLinearMap.comp_zero]
  have hzright : ((1 - d₁.support) ∘L A₁) ∘L d₀.inverse = 0 := by
    rw [honeP₁, ContinuousLinearMap.zero_comp]
  have hid : d₁.support - d₀.support =
      (d₁.inverse ∘L (A₁ - A₀)) ∘L (1 - d₀.support) +
        ((1 - d₁.support) ∘L (A₁ - A₀)) ∘L d₀.inverse := by
    symm
    calc
      (d₁.inverse ∘L (A₁ - A₀)) ∘L (1 - d₀.support) +
          ((1 - d₁.support) ∘L (A₁ - A₀)) ∘L d₀.inverse =
          ((d₁.inverse ∘L A₁) ∘L (1 - d₀.support) -
            (d₁.inverse ∘L A₀) ∘L (1 - d₀.support)) +
          (((1 - d₁.support) ∘L A₁) ∘L d₀.inverse -
            ((1 - d₁.support) ∘L A₀) ∘L d₀.inverse) := by
            simp only [← ContinuousLinearMap.mul_def]
            noncomm_ring
      _ = d₁.support ∘L (1 - d₀.support) -
          (1 - d₁.support) ∘L d₀.support := by
            rw [hzleft, hzright]
            simp only [sub_zero, zero_sub]
            rw [d₁.inverse_mul_metric, ContinuousLinearMap.comp_assoc,
              d₀.metric_mul_inverse]
            simp only [sub_eq_add_neg]
      _ = d₁.support - d₀.support := by
            simp only [← ContinuousLinearMap.mul_def]
            noncomm_ring
  rw [hid]
  exact hleft.one_add hright

/-- Bounded symmetric-support generalized inversion preserves congruence modulo `S¹`. -/
theorem suzukiCausalDepthGammaSupportedGeneralizedInverse_inverse_sub_memSchattenClass_one
    {A₀ A₁ : GammaOp}
    (d₀ : SuzukiCausalDepthGammaSupportedGeneralizedInverse A₀)
    (d₁ : SuzukiCausalDepthGammaSupportedGeneralizedInverse A₁)
    (hA : MemSchattenClass 1 (A₁ - A₀)) :
    MemSchattenClass 1 (d₁.inverse - d₀.inverse) := by
  have hP :=
    suzukiCausalDepthGammaSupportedGeneralizedInverse_support_sub_memSchattenClass_one
      d₀ d₁ hA
  have hnegA : MemSchattenClass 1 (A₀ - A₁) := by
    simpa using hA.one_neg
  have hleft : MemSchattenClass 1
      (d₁.inverse ∘L (d₁.support - d₀.support)) :=
    memSchattenClass_one_comp_left hP d₁.inverse
  have hmiddle : MemSchattenClass 1
      ((d₁.inverse ∘L (A₀ - A₁)) ∘L d₀.inverse) :=
    memSchattenClass_one_comp_right
      (memSchattenClass_one_comp_left hnegA d₁.inverse) d₀.inverse
  have hright : MemSchattenClass 1
      ((d₁.support - d₀.support) ∘L d₀.inverse) :=
    memSchattenClass_one_comp_right hP d₀.inverse
  have hid : d₁.inverse - d₀.inverse =
      d₁.inverse ∘L (d₁.support - d₀.support) +
        (d₁.inverse ∘L (A₀ - A₁)) ∘L d₀.inverse +
          (d₁.support - d₀.support) ∘L d₀.inverse := by
    have hmetric0 := d₀.metric_mul_inverse
    have hmetric1 := d₁.inverse_mul_metric
    have hsupport0 := d₀.support_mul_inverse
    have hsupport1 := d₁.inverse_mul_support
    simp only [← ContinuousLinearMap.mul_def] at hmetric0 hmetric1 hsupport0 hsupport1 ⊢
    noncomm_ring [hmetric0, hmetric1, hsupport0, hsupport1]
  rw [hid]
  exact (hleft.one_add hmiddle).one_add hright

/-- Finite bounded circuits generated by the C34 regular grammar and arbitrary bounded
symmetric-support generalized inverses. -/
inductive SuzukiCausalDepthGammaBoundedSupportRationalAssembly : GammaOp → GammaOp → Prop
  | regular {A₀ A₁ : GammaOp}
      (h : SuzukiCausalDepthGammaRegularRationalAssembly A₀ A₁) :
      SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁
  | add {A₀ A₁ B₀ B₁ : GammaOp}
      (hA : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁)
      (hB : SuzukiCausalDepthGammaBoundedSupportRationalAssembly B₀ B₁) :
      SuzukiCausalDepthGammaBoundedSupportRationalAssembly (A₀ + B₀) (A₁ + B₁)
  | sub {A₀ A₁ B₀ B₁ : GammaOp}
      (hA : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁)
      (hB : SuzukiCausalDepthGammaBoundedSupportRationalAssembly B₀ B₁) :
      SuzukiCausalDepthGammaBoundedSupportRationalAssembly (A₀ - B₀) (A₁ - B₁)
  | comp {A₀ A₁ B₀ B₁ : GammaOp}
      (hA : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁)
      (hB : SuzukiCausalDepthGammaBoundedSupportRationalAssembly B₀ B₁) :
      SuzukiCausalDepthGammaBoundedSupportRationalAssembly (A₀ ∘L B₀) (A₁ ∘L B₁)
  | adjoint {A₀ A₁ : GammaOp}
      (hA : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁) :
      SuzukiCausalDepthGammaBoundedSupportRationalAssembly
        (ContinuousLinearMap.adjoint A₀) (ContinuousLinearMap.adjoint A₁)
  | supportedInverse {A₀ A₁ : GammaOp}
      (hA : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁)
      (d₀ : SuzukiCausalDepthGammaSupportedGeneralizedInverse A₀)
      (d₁ : SuzukiCausalDepthGammaSupportedGeneralizedInverse A₁) :
      SuzukiCausalDepthGammaBoundedSupportRationalAssembly d₀.inverse d₁.inverse

/-- Positive classification: every bounded supported-singular circuit remains congruent to its
source-free value modulo trace class. -/
theorem suzukiCausalDepthGammaBoundedSupportRationalAssembly_sub_memSchattenClass_one
    {A₀ A₁ : GammaOp}
    (h : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁) :
    MemSchattenClass 1 (A₁ - A₀) := by
  have hcomp : ∀ {A₀ A₁ B₀ B₁ : GammaOp},
      MemSchattenClass 1 (A₁ - A₀) → MemSchattenClass 1 (B₁ - B₀) →
        MemSchattenClass 1 (A₁ ∘L B₁ - A₀ ∘L B₀) := by
    intro A₀ A₁ B₀ B₁ hA hB
    have hid : A₁ ∘L B₁ - A₀ ∘L B₀ =
        (A₁ - A₀) ∘L B₁ + A₀ ∘L (B₁ - B₀) := by
      simp only [← ContinuousLinearMap.mul_def]
      noncomm_ring
    rw [hid]
    exact (memSchattenClass_one_comp_right hA B₁).one_add
      (memSchattenClass_one_comp_left hB A₀)
  have hadjoint : ∀ {A₀ A₁ : GammaOp},
      MemSchattenClass 1 (A₁ - A₀) →
        MemSchattenClass 1
          (ContinuousLinearMap.adjoint A₁ - ContinuousLinearMap.adjoint A₀) := by
    intro A₀ A₁ hA
    have htrace : IsTraceClass (A₁ - A₀) := hA.one_isTraceClass
    have htraceAdj := IsTraceClass.adjoint htrace
    have hmem := IsTraceClass.memSchattenClass_one htraceAdj
    rw [map_sub] at hmem
    exact hmem
  induction h with
  | regular h =>
      exact suzukiCausalDepthGammaRegularRationalAssembly_sub_memSchattenClass_one h
  | add hA hB ihA ihB =>
      convert ihA.one_add ihB using 1
      abel
  | sub hA hB ihA ihB =>
      convert ihA.one_sub ihB using 1
      abel
  | comp hA hB ihA ihB =>
      exact hcomp ihA ihB
  | adjoint hA ihA =>
      exact hadjoint ihA
  | supportedInverse hA d₀ d₁ ihA =>
      exact suzukiCausalDepthGammaSupportedGeneralizedInverse_inverse_sub_memSchattenClass_one
        d₀ d₁ ihA

/-- Generalized Schur complementation by a bounded symmetric-support inverse is admitted. -/
theorem SuzukiCausalDepthGammaBoundedSupportRationalAssembly.schur
    {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : GammaOp}
    (hA : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁)
    (hB : SuzukiCausalDepthGammaBoundedSupportRationalAssembly B₀ B₁)
    (hC : SuzukiCausalDepthGammaBoundedSupportRationalAssembly C₀ C₁)
    (hD : SuzukiCausalDepthGammaBoundedSupportRationalAssembly D₀ D₁)
    (d₀ : SuzukiCausalDepthGammaSupportedGeneralizedInverse D₀)
    (d₁ : SuzukiCausalDepthGammaSupportedGeneralizedInverse D₁) :
    SuzukiCausalDepthGammaBoundedSupportRationalAssembly
      (A₀ - (B₀ ∘L d₀.inverse) ∘L C₀)
      (A₁ - (B₁ ∘L d₁.inverse) ∘L C₁) :=
  hA.sub ((hB.comp (hD.supportedInverse d₀ d₁)).comp hC)

/-- Ordinary logarithmic singular residue is invariant under every bounded supported-singular
assembly of the actual causal-depth Gamma source. -/
theorem hasSchattenLogResidue_one_suzukiCausalDepthGammaBoundedSupportRationalAssembly_iff
    {A₀ A₁ : GammaOp}
    (h : SuzukiCausalDepthGammaBoundedSupportRationalAssembly A₀ A₁)
    (hA₀cpt : IsCompactOperator A₀) (R : ℝ) :
    HasSchattenLogResidue 1 A₁ R ↔ HasSchattenLogResidue 1 A₀ R := by
  have hdiff :=
    suzukiCausalDepthGammaBoundedSupportRationalAssembly_sub_memSchattenClass_one h
  have hdiffcpt : IsCompactOperator (A₁ - A₀) := hdiff.isCompactOperator one_pos
  have hA₁cpt : IsCompactOperator A₁ := by
    have hid : A₁ = A₀ + (A₁ - A₀) := by abel
    rw [hid]
    exact hA₀cpt.add hdiffcpt
  exact hasSchattenLogResidue_one_iff_of_traceClass_sub
    hA₁cpt hA₀cpt hdiff R

/-- A coefficient-faithful reporter would have to distinguish the two residues after a bounded
supported-singular circuit. -/
structure SuzukiCausalDepthGammaBoundedSupportRationalResidueCoefficientFaithful where
  background : GammaOp
  source : GammaOp
  assembly : SuzukiCausalDepthGammaBoundedSupportRationalAssembly background source
  background_compact : IsCompactOperator background
  backgroundResidue : ℝ
  sourceResidue : ℝ
  background_residue : HasSchattenLogResidue 1 background backgroundResidue
  source_residue : HasSchattenLogResidue 1 source sourceResidue
  detects_actual_source : sourceResidue ≠ backgroundResidue

/-- **Bounded singular-pivot CCM--FU no-go.** Neither closed-range symmetric Moore--Penrose
inversion nor generalized Schur complementation can recover a nonzero source coefficient in an
ordinary logarithmic singular residue. -/
theorem no_suzukiCausalDepthGammaBoundedSupportRationalResidueCoefficientFaithful :
    ¬ Nonempty SuzukiCausalDepthGammaBoundedSupportRationalResidueCoefficientFaithful := by
  rintro ⟨P⟩
  have hsourceOnBackground : HasSchattenLogResidue 1 P.background P.sourceResidue :=
    (hasSchattenLogResidue_one_suzukiCausalDepthGammaBoundedSupportRationalAssembly_iff
      P.assembly P.background_compact P.sourceResidue).1 P.source_residue
  have heq : P.sourceResidue = P.backgroundResidue :=
    tendsto_nhds_unique hsourceOnBackground P.background_residue
  exact P.detects_actual_source heq

end

end RHTower
