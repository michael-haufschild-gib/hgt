import GaloisForLFunctions.HTGeometry.BivariateRootCovering

/-!
# Root loci over open parameter sets

Let `f(t, w)` be monic of positive degree in `w` with polynomial coefficients.  Over an open set `V`
of parameters on which every fibre `f(t, ·)` is separable, the root locus
`{(t, w) : f(t, w) = 0, t ∈ V}` is a covering of `V` with finite fibres: the projection is a local
homeomorphism by the implicit function theorem and proper by the monic Cauchy bound.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology Set

noncomputable section

variable {f : ℂ[X][X]} {V : Set ℂ}

/-- The root locus of `f` over the parameter set `V`. -/
def RootLocusOver (f : ℂ[X][X]) (V : Set ℂ) : Set (ℂ × ℂ) := {q | biEval f q = 0 ∧ q.1 ∈ V}

/-- The parameter projection of the root locus over `V`. -/
def rootProjOver (q : RootLocusOver f V) : V := ⟨q.1.1, q.2.2⟩

theorem continuous_rootProjOver : Continuous (rootProjOver (f := f) (V := V)) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

/-- The inclusion of the root locus over `V` into the whole root locus. -/
def rootLocusOverIncl (q : RootLocusOver f V) : BiRootLocus f := ⟨q.1, q.2.1⟩

theorem isOpenEmbedding_rootLocusOverIncl (hV : IsOpen V) :
    IsOpenEmbedding (rootLocusOverIncl (f := f) (V := V)) := by
  have hopen : IsOpen {q : BiRootLocus f | (q : ℂ × ℂ).1 ∈ V} :=
    hV.preimage (continuous_fst.comp continuous_subtype_val)
  have he : IsEmbedding (rootLocusOverIncl (f := f) (V := V)) := by
    refine IsEmbedding.of_comp ((continuous_subtype_val).subtype_mk _) continuous_subtype_val ?_
    exact IsEmbedding.subtypeVal
  refine ⟨he, ?_⟩
  convert hopen using 1
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2.2
  · intro hq
    exact ⟨⟨q.1, q.2, hq⟩, rfl⟩

theorem isLocalHomeomorphOn_biRootProj :
    IsLocalHomeomorphOn (biRootProj (f := f)) {q | (biFibre f (q : ℂ × ℂ).1).Separable} := by
  apply IsLocalHomeomorphOn.mk
  intro q hq
  obtain ⟨φ, hφ, hφeq⟩ := exists_chart_biRootProj q hq
  exact ⟨φ, hφ, fun x _ => by rw [hφeq]⟩

/-- **The projection is a local homeomorphism** over a separable open parameter set. -/
theorem isLocalHomeomorph_rootProjOver (hV : IsOpen V)
    (hsep : ∀ t ∈ V, (biFibre f t).Separable) :
    IsLocalHomeomorph (rootProjOver (f := f) (V := V)) := by
  have hcomp : IsLocalHomeomorph (biRootProj (f := f) ∘ rootLocusOverIncl (V := V)) := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    refine isLocalHomeomorphOn_biRootProj.comp
      (isOpenEmbedding_rootLocusOverIncl hV).isLocalHomeomorph.isLocalHomeomorphOn ?_
    intro q _
    exact hsep _ q.2.2
  refine IsLocalHomeomorph.of_comp (g := Subtype.val) ?_
    hV.isOpenEmbedding_subtypeVal.isLocalHomeomorph continuous_rootProjOver
  exact hcomp

/-- **The projection is proper** for a monic family of positive degree. -/
theorem isProperMap_rootProjOver (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    IsProperMap (rootProjOver (f := f) (V := V)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_rootProjOver, fun K hK => ?_⟩
  have hK' : IsCompact ((Subtype.val : V → ℂ) '' K) := hK.image continuous_subtype_val
  have hpre := (isProperMap_biRootProj hf hdeg).isCompact_preimage hK'
  have hsub : (fun q : RootLocusOver f V => (q : ℂ × ℂ)) '' (rootProjOver ⁻¹' K) =
      (fun q : BiRootLocus f => (q : ℂ × ℂ)) '' (biRootProj ⁻¹' ((Subtype.val : V → ℂ) '' K)) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q.1, q.2.1⟩, ⟨rootProjOver q, hq, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨t, htK, ht⟩, rfl⟩
      have hV : (q : ℂ × ℂ).1 ∈ V := by
        have hq : biRootProj q = (q : ℂ × ℂ).1 := rfl
        rw [← hq, ← ht]; exact t.2
      refine ⟨⟨q.1, q.2, hV⟩, ?_, rfl⟩
      have : rootProjOver ⟨q.1, q.2, hV⟩ = t := Subtype.ext ht.symm
      change rootProjOver ⟨q.1, q.2, hV⟩ ∈ K
      rw [this]; exact htK
  refine (IsEmbedding.subtypeVal.isInducing.isCompact_iff).mpr ?_
  rw [hsub]
  exact hpre.image continuous_subtype_val

/-- **Covering.** -/
theorem isCoveringMap_rootProjOver (hf : f.Monic) (hdeg : 0 < f.natDegree) (hV : IsOpen V)
    (hsep : ∀ t ∈ V, (biFibre f t).Separable) :
    IsCoveringMap (rootProjOver (f := f) (V := V)) :=
  isCoveringMap_of_isProperMap_of_isLocalHomeomorph (isLocalHomeomorph_rootProjOver hV hsep)
    (isProperMap_rootProjOver hf hdeg)

/-- Every fibre is finite. -/
theorem finite_fibre_rootProjOver (hf : f.Monic) (t : V) :
    Finite ((rootProjOver (f := f) (V := V)) ⁻¹' {t}) := by
  have hne : biFibre f t ≠ 0 := (biFibre_monic hf t).ne_zero
  have hfin : ((biFibre f t).roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
  refine Finite.of_injective (β := ((biFibre f t).roots.toFinset : Set ℂ))
    (fun q => ⟨(q.1 : ℂ × ℂ).2, ?_⟩) ?_
  · have hq : biEval f (q.1 : ℂ × ℂ) = 0 := q.1.2.1
    have ht : (q.1 : ℂ × ℂ).1 = t := congrArg Subtype.val (q.2 : rootProjOver q.1 = t)
    rw [biEval_eq_eval_biFibre, ht] at hq
    simpa [Polynomial.mem_roots hne] using hq
  · intro q₁ q₂ h
    have e1 : (q₁.1 : ℂ × ℂ).1 = (t : ℂ) :=
      congrArg Subtype.val (q₁.2 : rootProjOver q₁.1 = t)
    have e2 : (q₂.1 : ℂ × ℂ).1 = (t : ℂ) :=
      congrArg Subtype.val (q₂.2 : rootProjOver q₂.1 = t)
    have h1 : (q₁.1 : ℂ × ℂ).1 = (q₂.1 : ℂ × ℂ).1 := e1.trans e2.symm
    have h2 : (q₁.1 : ℂ × ℂ).2 = (q₂.1 : ℂ × ℂ).2 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))

end

end GaloisForLFunctions.HTGeometry
