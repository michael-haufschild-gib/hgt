import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineZeroSets
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveJetCuts
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveJetSpans
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveShiftedFibres
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalCotangentBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothSchemeDimension

/-! A smooth integral projective scheme admits a linear-system projection
with a transverse origin fibre through any prescribed finite set of rational points. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} {N : ℕ}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- Forms giving a projection whose origin fibre contains the specified
points and whose defining ratios generate the cotangent space at its points. -/
structure TransversalProjectionForms (i : X ⟶ PSpace K N) (d : ℕ)
    (S : Finset (X.BaseFieldPointOver K s)) where
  degree : ℕ
  positive : 0 < degree
  forms : Fin (d + 1) → Grade (K := K) (N := N) degree
  cover : (⨆ j, formBasicOpen i (forms j).1) = ⊤
  generic : ∀ j, genericPoint X ∈ formBasicOpen i (forms j).1
  pinned : ∀ y ∈ S, y.hom default ∈ formBasicOpen i (forms 0).1 ∧
    ∀ j : Fin d, y.hom default ∉ formBasicOpen i (forms j.succ).1
  tangent : ∀ (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ formBasicOpen i (forms 0).1),
    (∀ j : Fin d, y.hom default ∉ formBasicOpen i (forms j.succ).1) →
    SpansCotangentAt y hy (fun j : Fin d => projectiveRatio i (forms 0).2 (forms j.succ).2)

private theorem spanning_at_singleton (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    [Subsingleton X] [SmoothOfRelativeDimension 0 s]
    (S : Finset (X.BaseFieldPointOver K s))
    (l : MvPolynomial (Fin (N + 1)) K) (hl : l.IsHomogeneous 1)
    (hg : genericPoint X ∈ formBasicOpen i l) : Nonempty (TransversalProjectionForms i 0 S) := by
  let U := formBasicOpen i l
  have hu (x : X) : x ∈ U := (Subsingleton.elim x (genericPoint X)).symm ▸ hg
  have hU : IsAffineOpen U := (Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N)) _ hl one_pos).preimage i
  refine ⟨⟨1, one_pos, fun _ => ⟨l, hl⟩, ?_, fun _ => hg, ?_, ?_⟩⟩
  · exact top_le_iff.mp (fun x _ => Opens.mem_iSup.mpr ⟨0, hu x⟩)
  · exact fun y _ => ⟨hu _, fun j => Fin.elim0 j⟩
  · intro y hy _
    obtain ⟨t, _, ht⟩ := exists_rational_cotangent_basis s 0 hU y hy
    exact spansCotangentAt_of_firstJets y hy t _ ht (fun j => Fin.elim0 j)

variable (i : X ⟶ PSpace K N) [IsClosedImmersion i] (hi : i ≫ PSpace.str K N = s)
  (d : ℕ) [SmoothOfRelativeDimension d s] (S : Finset (X.BaseFieldPointOver K s))

include hi

omit [IsIntegral X] [IsClosedImmersion i] [SmoothOfRelativeDimension d s] in
private theorem spans_of_shifted_firstJets {l : MvPolynomial (Fin (N + 1)) K}
    (hl : l.IsHomogeneous 1) (hS : ∀ y ∈ S, y.hom default ∈ formBasicOpen i l)
    {n : ℕ} (hn : 0 < n) (h : Grade (K := K) (N := N) n)
    (g : Fin d → Grade (K := K) (N := N) n) (c : Fin d → K)
    (t : S → Fin d → SectionRing s (formBasicOpen i l))
    (hh : ∀ y : S, projectivePowerRatio i hl n h.1 h.2 ∈
      RingHom.ker (affinePointEval y.1 (hS y.1 y.2)).toRingHom ^ 2)
    (hg : ∀ j (y : S), let r : SectionRing s (formBasicOpen i l) :=
        projectivePowerRatio i hl n (g j).1 (g j).2
      r - t y j ∈ RingHom.ker (affinePointEval y.1 (hS y.1 y.2)).toRingHom ^ 2) :
    ∀ j (y : S), let F := g j - c j • h
      let r : SectionRing s (formBasicOpen i l) := projectivePowerRatio i hl n F.1 F.2
      r - t y j ∈ RingHom.ker (affinePointEval y.1 (hS y.1 y.2)).toRingHom ^ 2 := by
  intro j y
  let R := projectivePowerRatioLinear i hi hl hn
  let I := RingHom.ker (affinePointEval y.1 (hS y.1 y.2)).toRingHom ^ 2
  have h₁ : R h ∈ I := by rw [projectivePowerRatioLinear_apply]; exact hh y
  have h₂ : R (g j) - t y j ∈ I := by rw [projectivePowerRatioLinear_apply]; exact hg j y
  suffices hshift : R (g j - c j • h) - t y j ∈ I by
    have e := projectivePowerRatioLinear_apply i hi hl hn (g j - c j • h)
    exact (congrArg (fun a : SectionRing s (formBasicOpen i l) => a - t y j ∈ I) e).mp hshift
  rw [map_sub, map_smul]
  have hmul : c j • R h ∈ I := by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ h₁
  have he : R (g j) - c j • R h - t y j = R (g j) - t y j - c j • R h := by abel
  rw [he]
  exact I.sub_mem h₂ hmul

variable [IsAlgClosed K] [CharZero K]

/-- The origin of a projective projection can be chosen to contain a
prescribed finite set of rational points and to have transverse equations. -/
theorem exists_transversalProjectionForms : Nonempty (TransversalProjectionForms i d S) := by
  classical
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  letI : CompactSpace X := IsProjOver.compactSpace (f := s) ⟨N, i, inferInstance, hi⟩
  letI : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian s }
  obtain ⟨l, hl, hlg, hlS⟩ := exists_form_chart_of_points i 1 S
  let U := formBasicOpen i l
  have hU : IsAffineOpen U := (Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N)) _ hl one_pos).preimage i
  by_cases hgen : ∀ y ∈ S, genericPoint X ≠ y.hom default
  swap
  · push Not at hgen
    obtain ⟨y, _, he⟩ := hgen
    have hx (x : X) : x = y.hom default := by
      have hspec : y.hom default ⤳ x := he ▸ genericPoint_specializes x
      exact hspec.mem_closed (baseFieldPoint_isClosed y) (Set.mem_singleton _)
    letI : Subsingleton X := ⟨fun a b => (hx a).trans (hx b).symm⟩
    have hd := topologicalKrullDim_smooth_affineOpen s d hU ⟨_, hlg⟩
    have hle : topologicalKrullDim (↥U) ≤ 0 := topologicalKrullDim_zero_of_discreteTopology (↥U)
    have heq : d = 0 := by
      rw [hd] at hle
      exact Nat.eq_zero_of_le_zero (by exact_mod_cast hle)
    subst d
    exact spanning_at_singleton i S l hl hlg
  choose t ht hspan using fun y : S =>
    exists_rational_cotangent_basis s d hU y.1 (hlS y.1 y.2)
  obtain ⟨n, h, g, hn, hh, hhjet, hgjet, hcut⟩ :=
    exists_forms_cutting_outside_chart i hi hl S hlS hgen
      (topologicalKrullDim_smooth_lt_succ s d) (fun j y => t y j)
  obtain ⟨c, hc, hÉt⟩ := exists_shift_formallyEtale_projective_fibre i hi d hn h hh g
  let G (j : Fin d) := g j - c j • h
  let Z : Set X := {x | ∀ j, x ∉ formBasicOpen i (G j).1}
  let V := formBasicOpen i h.1
  have hV : IsAffineOpen V := (Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N)) _ h.2 hn).preimage i
  let A := SectionRing s V
  let r (j : Fin d) : A := projectiveRatio i h.2 (G j).2
  let I : Ideal A := Ideal.span (Set.range r)
  letI : Algebra.FiniteType K A := sectionRing_finiteType s hV
  letI : Algebra.FormallyEtale K (A ⧸ I) := hÉt
  letI : Algebra.FiniteType K (A ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  letI : Module.Finite K (A ⧸ I) := Algebra.FormallyUnramified.finite_of_free K _
  letI : IsArtinianRing (A ⧸ I) := IsArtinianRing.of_finite K _
  have hout (x : X) (hx : x ∈ Z) (hxV : x ∉ V) : ∃ y ∈ S, x = y.hom default := by
    apply hcut x hxV
    intro j hj
    have hp := (i x).asHomogeneousIdeal.toIdeal.add_mem (not_not.mp (hx j))
      ((i x).asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C (c j)) (not_not.mp hxV))
    change (g j).1 - c j • h.1 + MvPolynomial.C (c j) * h.1 ∈ (i x).asHomogeneousIdeal at hp
    rw [MvPolynomial.smul_eq_C_mul, sub_add_cancel] at hp
    exact hj hp
  have hfin : Z.Finite := by
    let q (y : X.BaseFieldPointOver K s) := y.hom default
    have hr₀ := @finite_commonZeros_of_isArtinianQuotient X V hV (Fin d) r
      (inferInstanceAs (IsArtinianRing (A ⧸ I)))
    refine (hr₀.union (S.finite_toSet.image q)).subset ?_
    intro x hx
    by_cases hxV : x ∈ V
    · refine Set.mem_union_left _ ⟨hxV, fun j hj => ?_⟩
      exact hx j ((basicOpen_projectiveRatio i h.2 (G j).2).le hj).2
    · obtain ⟨y, hy, he⟩ := hout x hx hxV
      exact Set.mem_union_right _ ⟨y, hy, he.symm⟩
  let T := insert (i (genericPoint X)) (hfin.toFinset.image i)
  obtain ⟨f, hf, hT⟩ := PSpace.exists_form_nonvanishing N n T
  let F₀ : Grade (K := K) (N := N) n := ⟨f, hf⟩
  let W := formBasicOpen i F₀.1
  have hW : IsAffineOpen W := (Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N)) _ hf hn).preimage i
  have h₀ (x : X) (hx : x ∈ Z) : x ∈ W :=
    hT (i x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem i (hfin.mem_toFinset.mpr hx)))
  have hjets (j : Fin d) (y : S) := spans_of_shifted_firstJets i hi d S hl hlS hn h g c t hhjet hgjet j y
  have hSz (y : S) : y.1.hom default ∈ Z := by
    intro j
    let ε := affinePointEval y.1 (hlS y.1 y.2)
    let M := RingHom.ker ε.toRingHom
    let u : SectionRing s U := projectivePowerRatio i hl n (G j).1 (G j).2
    have hm : u - t y j ∈ M :=
      Ideal.pow_le_self two_ne_zero (hjets j y)
    have hz : ε u = 0 := by
      have h' := Ideal.add_mem M hm (RingHom.mem_ker.mpr (ht y j))
      rw [sub_add_cancel] at h'
      exact h'
    exact (affinePointEval_powerRatio_eq_zero_iff i hl hn (G j).2 y.1 _).mp hz
  refine ⟨⟨n, hn, Fin.cons F₀ G, ?_, ?_, ?_, ?_⟩⟩
  · apply top_le_iff.mp
    intro x _
    by_cases hx : x ∈ Z
    · exact Opens.mem_iSup.mpr ⟨0, h₀ x hx⟩
    · change ¬ (∀ j : Fin d, x ∉ formBasicOpen i (G j).1) at hx
      push Not at hx
      obtain ⟨j, hj⟩ := hx
      exact Opens.mem_iSup.mpr ⟨j.succ, hj⟩
  · exact Fin.cases (hT (i (genericPoint X)) (Finset.mem_insert_self _ _)) hc
  · exact fun y hy => ⟨h₀ _ (hSz ⟨y, hy⟩), hSz ⟨y, hy⟩⟩
  · intro y hy hzero
    have hyZ : y.hom default ∈ Z := hzero
    by_cases hyV : y.hom default ∈ V
    · apply (cotangentSpan_projectiveRatio_iff y i hf h.2 (fun j : Fin d => (G j).1)
        (fun j => (G j).2) hW hV hy hyV).mpr
      apply cotangentSpan_of_formallyEtale_quotient I
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact (affinePointEval_projectiveRatio_eq_zero_iff i h.2 (G j).2 y hyV).mpr (hyZ j)
    · obtain ⟨z, hz, he⟩ := hout (y.hom default) hyZ hyV
      let z₀ : S := ⟨z, hz⟩
      have hzW := h₀ (z.hom default) (hSz z₀)
      apply (spansCotangentAt_congr_point hW hy hzW he
        (fun j : Fin d => projectiveRatio i hf (G j).2)).mpr
      have hpow : (l ^ n).IsHomogeneous n := by simpa only [one_mul] using hl.pow n
      have hU' : IsAffineOpen (formBasicOpen i (l ^ n)) :=
        (Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N)) _ hpow hn).preimage i
      have hz' : z.hom default ∈ formBasicOpen i (l ^ n) :=
        i.preimage_mono (Proj.basicOpen_pow (Grade (K := K) (N := N)) l n hn).ge (hlS z hz)
      apply (cotangentSpan_projectiveRatio_iff z i hf hpow (fun j : Fin d => (G j).1)
        (fun j => (G j).2) hW hU' hzW hz').mpr
      apply (spansCotangentAt_powerRatio_iff i hl hn hpow G z (hlS z hz) hz').mp
      exact spansCotangentAt_of_firstJets z (hlS z hz) (t z₀) _ (hspan z₀) (fun j => hjets j z₀)

end GlobalTheory.SchemeCohomology
