import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CotangentAtStalk
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFirstJets

/-! First-order residues on the linear chart determine the cotangent
generation of the actual projective ratios. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open GaloisForLFunctions.HTGeometry UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)}
  {N n : ℕ} {l : MvPolynomial (Fin (N + 1)) K} {U : X.Opens}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- The section values in the maximal ideal generate the cotangent space
when their ideal and the square of the maximal ideal contain the maximal ideal. -/
abbrev SpansCotangentAt {J : Type*} (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ U)
    (r : J → SectionRing s U) : Prop :=
  let m := RingHom.ker (affinePointEval y hy).toRingHom
  m ≤ Ideal.span (Set.range r) ⊔ m ^ 2

/-- Lifts of generators modulo the square of the point ideal generate the
cotangent space. -/
theorem spansCotangentAt_of_firstJets {d : ℕ} (y : X.BaseFieldPointOver K s)
    (hy : y.hom default ∈ U) (t r : Fin d → SectionRing s U)
    (ht : ∀ a, affinePointEval y hy a = 0 →
      ∃ c : Fin d → K, a - ∑ j, c j • t j ∈ RingHom.ker (affinePointEval y hy).toRingHom ^ 2)
    (hr : ∀ j, r j - t j ∈ RingHom.ker (affinePointEval y hy).toRingHom ^ 2) :
    SpansCotangentAt y hy r := by
  let A := SectionRing s U
  let m := RingHom.ker (affinePointEval y hy).toRingHom
  let I := Ideal.span (Set.range r)
  intro a ha
  obtain ⟨c, hc⟩ := ht a ha
  have hsum : ∑ j, c j • (r j - t j) ∈ m ^ 2 :=
    Ideal.sum_mem _ fun j _ => by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (hr j)
  have ha' : a - ∑ j, c j • r j ∈ m ^ 2 := by
    have e : a - ∑ j, c j • r j = (a - ∑ j, c j • t j) - ∑ j, c j • (r j - t j) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    exact Ideal.sub_mem _ hc hsum
  have hr' : ∑ j, c j • r j ∈ I := Ideal.sum_mem _ fun j _ => by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
  have h := Ideal.add_mem (I ⊔ m ^ 2)
    ((le_sup_right : m ^ 2 ≤ I ⊔ m ^ 2) ha') ((le_sup_left : I ≤ I ⊔ m ^ 2) hr')
  rwa [sub_add_cancel] at h

theorem affinePointEval_powerRatio_eq_zero_iff (i : X ⟶ PSpace K N)
    (hl : l.IsHomogeneous 1) (hn : 0 < n) {f : MvPolynomial (Fin (N + 1)) K}
    (hf : f.IsHomogeneous n) (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ formBasicOpen i l) :
    affinePointEval y hy (projectivePowerRatio i hl n f hf) = 0 ↔
      y.hom default ∉ formBasicOpen i f := by
  have e := pointEval_ne_zero_iff y.hom _ hy (projectivePowerRatio i hl n f hf)
  rw [basicOpen_projectivePowerRatio i hl hn hf] at e
  exact ⟨fun h hx => (e.mpr ⟨hy, hx⟩) h, fun h => by
    by_contra hz
    exact h (e.mp hz).2⟩

/-- The cotangent span computed on the linear chart and the chart of any
positive power of the linear form are the same. -/
theorem spansCotangentAt_powerRatio_iff (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    (hl : l.IsHomogeneous 1) (hn : 0 < n) (hp : (l ^ n).IsHomogeneous n)
    {J : Type*} (f : J → Grade (K := K) (N := N) n)
    (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ formBasicOpen i l)
    (hy' : y.hom default ∈ formBasicOpen i (l ^ n)) :
    SpansCotangentAt y hy (fun j => projectivePowerRatio i hl n (f j).1 (f j).2) ↔
      SpansCotangentAt y hy' (fun j => projectiveRatio i hp (f j).2) := by
  let A := Grade (K := K) (N := N)
  let V := formBasicOpen i l
  let W := formBasicOpen i (l ^ n)
  have hV : IsAffineOpen V := (Proj.isAffineOpen_basicOpen A _ hl one_pos).preimage i
  have hW : IsAffineOpen W := (Proj.isAffineOpen_basicOpen A _ hp hn).preimage i
  have e : V ≤ W := i.preimage_mono (Proj.basicOpen_pow A l n hn).ge
  let x := y.hom default
  let g (j : J) : SectionRing s V := projectivePowerRatio i hl n (f j).1 (f j).2
  let g' (j : J) : SectionRing s W := projectiveRatio i hp (f j).2
  have he (j : J) : (X.presheaf.germ V x hy).hom (g j) =
      (X.presheaf.germ W x hy').hom (g' j) := by
    have hg := projectivePowerRatio_eq_appLE i hl hn (f j).2 hp
    change (i.appLE _ V e).hom (homogeneousRatio hp (f j).2) = g j at hg
    rw [← hg]
    exact X.presheaf.germ_res_apply (homOfLE e) x hy (g' j)
  let I : Ideal (SectionRing s V) := Ideal.span (Set.range g)
  let I' : Ideal (SectionRing s W) := Ideal.span (Set.range g')
  let a : SectionRing s V →+* X.presheaf.stalk x := (X.presheaf.germ V x hy).hom
  let b : SectionRing s W →+* X.presheaf.stalk x := (X.presheaf.germ W x hy').hom
  have hspan : I.map a = I'.map b := calc
    _ = Ideal.span (a '' Set.range g) := Ideal.map_span _ _
    _ = Ideal.span (Set.range (a ∘ g)) := congrArg Ideal.span (Set.range_comp a g).symm
    _ = Ideal.span (Set.range (b ∘ g')) :=
      congrArg (fun v : J → X.presheaf.stalk x => Ideal.span (Set.range v)) (funext he)
    _ = Ideal.span (b '' Set.range g') := congrArg Ideal.span (Set.range_comp b g')
    _ = _ := (Ideal.map_span _ _).symm
  refine (cotangentSpan_iff_stalk y hV hy I).trans (Iff.trans ?_ (cotangentSpan_iff_stalk y hW hy' I').symm)
  let M := IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  change (M ≤ I.map a ⊔ M ^ 2) ↔ (M ≤ I'.map b ⊔ M ^ 2)
  rw [hspan]

/-- The cotangent-span condition depends only on the image point of a rational
point in an affine chart. -/
theorem spansCotangentAt_congr_point {J : Type*} (hU : IsAffineOpen U)
    {y z : X.BaseFieldPointOver K s} (hy : y.hom default ∈ U) (hz : z.hom default ∈ U)
    (e : y.hom default = z.hom default) (r : J → SectionRing s U) :
    SpansCotangentAt y hy r ↔ SpansCotangentAt z hz r := by
  let I : Ideal (SectionRing s U) := Ideal.span (Set.range r)
  refine (cotangentSpan_iff_stalk y hU hy I).trans (Iff.trans ?_ (cotangentSpan_iff_stalk z hU hz I).symm)
  let P (x : U) :=
    let m := IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)
    m ≤ (Ideal.span (Set.range r)).map (X.presheaf.germ U x.1 x.2).hom ⊔ m ^ 2
  exact Iff.of_eq (congrArg P (Subtype.ext e : (⟨y.hom default, hy⟩ : U) = ⟨z.hom default, hz⟩))

end GlobalTheory.SchemeCohomology
