import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffinePointJets
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectivePointSeparation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveSectionLifts
import GaloisForLFunctions.HTGeometry.LinearNonzerodivisor

/-! Homogeneous forms realize simultaneous first-order residues on a linear
chart. At sufficiently large degree they can also avoid a finite set of
points outside the prescribed jets. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)}
  {N : ℕ} {l : MvPolynomial (Fin (N + 1)) K}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- The open where a form is nonzero on a scheme mapping to projective space. -/
abbrev formBasicOpen (i : X ⟶ PSpace K N) (f : MvPolynomial (Fin (N + 1)) K) : X.Opens :=
  i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) f

variable (i : X ⟶ PSpace K N) [IsClosedImmersion i] (hi : i ≫ PSpace.str K N = s)
  (hl : l.IsHomogeneous 1) (S : Finset (X.BaseFieldPointOver K s))
  (hS : ∀ y ∈ S, y.hom default ∈ formBasicOpen i l)

private abbrev pointIdeal {U : X.Opens} (y : X.BaseFieldPointOver K s)
    (hy : y.hom default ∈ U) : Ideal (SectionRing s U) :=
  RingHom.ker (affinePointEval y hy).toRingHom

/-- Each finite family of simultaneous residues admits homogeneous
numerators in every sufficiently large degree. -/
theorem exists_homogeneous_firstJets {J : Type} [Fintype J]
    (t : J → S → SectionRing s (formBasicOpen i l)) :
    ∃ b : ℕ, ∀ m ≥ b, ∀ j, ∃ f : Grade (K := K) (N := N) m,
      ∀ y : S, let r : SectionRing s (formBasicOpen i l) := projectivePowerRatio i hl m f.1 f.2
        r - t j y ∈ pointIdeal y.1 (hS y.1 y.2) ^ 2 := by
  let U := formBasicOpen i l
  have hU : IsAffineOpen U := (Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N)) _ hl one_pos).preimage i
  let z (y : S) : {y : X.BaseFieldPointOver K s // y.hom default ∈ U} :=
    ⟨y.1, hS y.1 y.2⟩
  have hz : Function.Injective z := by
    intro a b e
    apply Subtype.ext
    exact congrArg (fun q : {y : X.BaseFieldPointOver K s // y.hom default ∈ U} => q.1) e
  choose a ha using fun j => exists_affine_section_firstJets hU z hz (t j)
  obtain ⟨b, hb⟩ := exists_common_powerRatio i hl a
  refine ⟨b, fun m hm j => ?_⟩
  obtain ⟨f, hf, he⟩ := hb m hm j
  exact ⟨⟨f, hf⟩, fun y => he.symm ▸ ha j y⟩

include hi

/-- At every point outside the prescribed set, some form of each sufficiently
large degree is nonzero while its first-order residues at the set vanish. -/
theorem exists_form_zero_firstJets_avoiding (m : ℕ) (hm : 2 * S.card ≤ m) (x : X)
    (hx : ∀ y ∈ S, x ≠ y.hom default) :
    ∃ f : Grade (K := K) (N := N) m,
      x ∈ formBasicOpen i f.1 ∧
      ∀ y : S, projectivePowerRatio i hl m f.1 f.2 ∈ pointIdeal y.1 (hS y.1 y.2) ^ 2 := by
  obtain ⟨f, hf, hfS, hfx⟩ := exists_form_separating_finite_points i hi S S.card le_rfl x hx
  obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), i x ∈ PSpace.coordinateOpen K N j := by
    apply Opens.mem_iSup.mp
    rw [PSpace.iSup_coordinateOpen]
    trivial
  let n := m - 2 * S.card
  let u : MvPolynomial (Fin (N + 1)) K := MvPolynomial.X j ^ n
  have hu : u.IsHomogeneous n := by
    simpa only [one_mul] using (MvPolynomial.isHomogeneous_X K j).pow n
  have hs : S.card + S.card + n = m := by omega
  let g := f * f * u
  have hg : g.IsHomogeneous m := (congrArg (fun d => g.IsHomogeneous d) hs).mp ((hf.mul hf).mul hu)
  refine ⟨⟨g, hg⟩, ?_, fun y => ?_⟩
  · intro h
    change g ∈ (i x).asHomogeneousIdeal at h
    rcases (i x).isPrime.mem_or_mem h with h | h
    · exact hfx (((i x).isPrime.mem_or_mem h).elim id id)
    · exact hj ((i x).isPrime.mem_of_pow_mem n h)
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨y.1, y.2⟩
  let p := projectivePowerRatio i hl S.card f hf
  have hp : p ∈ pointIdeal y.1 (hS y.1 y.2) := by
    have hunit : y.1.hom default ∉ X.basicOpen p := by
      change y.1.hom default ∉ X.basicOpen (projectivePowerRatio i hl S.card f hf)
      rw [basicOpen_projectivePowerRatio i hl hpos hf]
      exact fun h => hfS y.1 y.2 h.2
    apply RingHom.mem_ker.mpr
    by_contra hne
    exact hunit ((pointEval_ne_zero_iff y.1.hom _ (hS y.1 y.2) p).mp hne)
  have hmul := projectivePowerRatio_mul i hl (hf.mul hf) hu
  have hf2 := projectivePowerRatio_mul i hl hf hf
  have hprod (b : ℕ) (hb : g.IsHomogeneous b) (hb' : S.card + S.card + n = b) :
      projectivePowerRatio i hl b g hb = p * p * projectivePowerRatio i hl n u hu := by
    subst b
    exact hmul.trans (congrArg (fun a => a * projectivePowerRatio i hl n u hu) hf2)
  rw [hprod m hg hs, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hp hp)

/-- A homogeneous numerator with prescribed first-order residues can be
perturbed through the same residues to miss any finite set of other points. -/
theorem exists_form_firstJets_avoiding [Infinite K] {m : ℕ} (hm : 2 * S.card ≤ m)
    (hpos : 0 < m) (g : Grade (K := K) (N := N) m)
    (T : Finset X) (hT : ∀ x ∈ T, ∀ y ∈ S, x ≠ y.hom default) :
    ∃ f : Grade (K := K) (N := N) m,
      (∀ x ∈ T, x ∈ formBasicOpen i f.1) ∧
      ∀ y : S, projectivePowerRatio i hl m f.1 f.2 - projectivePowerRatio i hl m g.1 g.2 ∈
        pointIdeal y.1 (hS y.1 y.2) ^ 2 := by
  classical
  let G := Grade (K := K) (N := N) m
  let R := projectivePowerRatioLinear i hi hl hpos
  let W : Submodule K G :=
    ⨅ y : S, ((pointIdeal y.1 (hS y.1 y.2) ^ 2).restrictScalars K).comap R
  have hW (f : G) : f ∈ W ↔ ∀ y : S, R f ∈ pointIdeal y.1 (hS y.1 y.2) ^ 2 :=
    Submodule.mem_iInf _
  let L (x : X) : Submodule K G :=
    ((i x).asHomogeneousIdeal.toIdeal.restrictScalars K).comap G.subtype
  let L' (x : X) := (L x).comap W.subtype
  have hproper (x : X) (hx : x ∈ T) : L' x ≠ ⊤ := by
    obtain ⟨f, hfx, hf⟩ := exists_form_zero_firstJets_avoiding i hi hl S hS m hm x (hT x hx)
    have hfW : f ∈ W := (hW f).mpr fun y => by
      rw [projectivePowerRatioLinear_apply]
      exact hf y
    intro ht
    exact hfx (show (⟨f, hfW⟩ : W) ∈ L' x from ht.symm ▸ Submodule.mem_top)
  let P : Set (Submodule K W) := L' '' (T : Set X)
  have hP : P.Finite := T.finite_toSet.image L'
  have hproper' (L₀ : Submodule K W) (hL₀ : L₀ ∈ P) : L₀ ≠ ⊤ := by
    obtain ⟨x, hx, rfl⟩ := hL₀
    exact hproper x hx
  obtain ⟨v, hv⟩ := exists_notMem_of_finite_proper (K := K) (V := ↥W) (s := P) hP hproper'
  have hv' (x : X) (hx : x ∈ T) : (v : G) ∉ L x := hv _ ⟨x, hx, rfl⟩
  let B := ⋃ x ∈ (T : Set X), {c : K | (v : G) + c • g ∈ L x}
  have hB : B.Finite := T.finite_toSet.biUnion fun x hx =>
    (subsingleton_line_meet (hv' x hx)).finite
  obtain ⟨c, hc⟩ := (hB.union (Set.finite_singleton (0 : K))).infinite_compl.nonempty
  have hc0 : c ≠ 0 := fun h => hc (Set.mem_union_right _ h)
  let f : G := g + c⁻¹ • (v : G)
  refine ⟨f, ?_, ?_⟩
  · intro x hx h
    have hf : f ∈ L x := h
    have hb : (v : G) + c • g ∈ L x := by
      have hcf : c • f = (v : G) + c • g := by
        dsimp [f]
        rw [smul_add, smul_smul, mul_inv_cancel₀ hc0, one_smul]
        exact add_comm (c • g) (v : G)
      exact hcf ▸ Submodule.smul_mem _ _ hf
    exact hc (Set.mem_union_left _ (Set.mem_iUnion₂.mpr ⟨x, hx, hb⟩))
  · intro y
    change projectivePowerRatio i hl m f.1 f.2 - projectivePowerRatio i hl m g.1 g.2 ∈ _
    rw [← projectivePowerRatioLinear_apply i hi hl hpos f,
      ← projectivePowerRatioLinear_apply i hi hl hpos g]
    change R (g + c⁻¹ • (v : G)) - R g ∈ _
    rw [map_add, add_sub_cancel_left, map_smul]
    exact Submodule.smul_mem ((pointIdeal y.1 (hS y.1 y.2) ^ 2).restrictScalars K) _
      ((hW _).mp v.2 y)

end GlobalTheory.SchemeCohomology
