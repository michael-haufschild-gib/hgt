import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordBundleOriginCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordBundleAwayCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordProductCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveAffineCoverDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechOpenSlice
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechSingletonShift

/-! The universal translation difference of a principal polarization has
one-dimensional cohomology in the dimension of the abelian variety. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace HTGeometry GlobalTheory.WH
open HTGeometry.FinsetCechDatum GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

private theorem preimage_finsetInf {X Y : Scheme.{0}} (f : X ⟶ Y) {T : Type}
    (U : T → Y.Opens) (s : Finset T) : s.inf (fun j => f ⁻¹ᵁ U j) = f ⁻¹ᵁ s.inf U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp only [Finset.inf_insert, ih, Scheme.Hom.preimage_inf]

private theorem exists_origin_algHom {K : Type} [Field K] {A : Over (Spec (.of K))}
    [GrpObj A] {W : A.left.Opens} (hW : IsAffineOpen W)
    (h : η[A].left (IsLocalRing.closedPoint K) ∈ W) :
    let R := Γ(A.left, W)
    letI : Algebra K R := (Spec.preimage (hW.fromSpec ≫ A.hom)).hom.toAlgebra
    ∃ χ : R →ₐ[K] K, Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hW.fromSpec = η[A].left := by
  let R := Γ(A.left, W)
  let t : Spec R ⟶ A.left := hW.fromSpec
  let e : Spec (.of K) ⟶ A.left := η[A].left
  let φ : CommRingCat.of K ⟶ R := Spec.preimage (t ≫ A.hom)
  letI : Algebra K R := φ.hom.toAlgebra
  have hs : Set.range e ⊆ Set.range t := by
    rintro _ ⟨z, rfl⟩
    apply hW.range_fromSpec.ge
    change η[A].left z ∈ W
    rwa [Subsingleton.elim (α := PrimeSpectrum K) z (IsLocalRing.closedPoint K)]
  let q : Spec (.of K) ⟶ Spec R := IsOpenImmersion.lift t e hs
  let χ : R ⟶ CommRingCat.of K := Spec.preimage q
  have hq : q ≫ t = e := IsOpenImmersion.lift_fac t e hs
  have hχ : Spec.map χ ≫ t = e :=
    (congrArg (fun u : Spec (.of K) ⟶ Spec R => u ≫ t) (Spec.map_preimage q)).trans hq
  have hφ : φ ≫ χ = 𝟙 _ := Spec.map_injective (calc
    Spec.map (φ ≫ χ) = Spec.map χ ≫ Spec.map φ := Spec.map_comp φ χ
    _ = Spec.map χ ≫ (t ≫ A.hom) :=
      congrArg (fun u : Spec R ⟶ Spec (.of K) => Spec.map χ ≫ u) (Spec.map_preimage _)
    _ = (Spec.map χ ≫ t) ≫ A.hom := (Category.assoc _ _ _).symm
    _ = e ≫ A.hom := congrArg (fun u : Spec (.of K) ⟶ A.left => u ≫ A.hom) hχ
    _ = 𝟙 (Spec (.of K)) := Over.w η[A]
    _ = Spec.map (𝟙 (CommRingCat.of K)) := (Spec.map_id _).symm)
  exact ⟨⟨χ.hom, fun r => congrArg (fun u : CommRingCat.of K ⟶ CommRingCat.of K => u r) hφ⟩, hχ⟩

/-- The affine charts away from the identity give acyclic columns. The
remaining singleton column is the regular local calculation at the identity. -/
theorem finrank_cech_universal_translation {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    {κ : Type} [LinearOrder κ] [Fintype κ] (W : κ → (A ⊗ A).left.Opens)
    (hW : ∀ j, IsAffineOpen (W j)) (cW : ⨆ j, W j = ⊤) (n : ℕ) :
    Module.finrank K ((cech (A ⊗ A).hom (toMod (translDiff A L (𝟙 A))) W).homology n) =
      if n = d then 1 else 0 := by
  let Z := A ⊗ A
  let p := (fst A A).left
  let q := (snd A A).left
  let M := translDiff A L (𝟙 A)
  let F := toMod M
  have hM : M.IsLB := hL.linComb _ _
  letI : F.IsQuasicoherent := isQuasicoherent_toMod hM
  letI : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} Z.left) := hasExt_of_enoughInjectives _
  have H : IsPullback p q A.hom A.hom := IsPullback.of_hasPullback _ _
  have hp := ProjectiveSections.isProjOver_of_relAmple hL hAmp
  have hZ := ProjectiveSections.isProjOver_product H hp hp
  letI : CompactSpace A.left := hp.compactSpace
  letI : A.left.IsSeparated := hp.isSeparated
  letI : Z.left.IsSeparated := hZ.isSeparated
  obtain ⟨U, hU, cU⟩ := exists_affine_cover_of_smooth_projective d hp
  let o := η[A].left (IsLocalRing.closedPoint K)
  letI : IsSeparated A.hom := hA.proper.toIsSeparated
  letI : IsClosedImmersion η[A].left :=
    isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) A.hom η[A].left (Over.w η[A])
  have ho : IsClosed {o} := by
    change IsClosed {η[A].left (IsLocalRing.closedPoint K)}
    rw [← Set.image_singleton]
    apply η[A].left.isClosedEmbedding.isClosedMap
    rw [show ({IsLocalRing.closedPoint K} : Set (PrimeSpectrum K)) = Set.univ from
      Set.eq_univ_of_forall fun x => Subsingleton.elim _ _]
    exact isClosed_univ
  obtain ⟨r, V, hV, cV, hV₀, hVaway⟩ := exists_affine_cover_separating_point A.left o ho
  let U' (i : Fin (d + 1)) := q ⁻¹ᵁ U i
  let V' (j : Fin (r + 1)) := p ⁻¹ᵁ V j
  let E := joinedCover U' V'
  let D := sectionDatum F E
  letI (s : Finset (Fin (d + 1) ⊕ₗ Fin (r + 1))) := sectionDatumModule Z.hom F E s
  let hD {s t : Finset (Fin (d + 1) ⊕ₗ Fin (r + 1))} (h : s ⊆ t) (x : K)
      (a : D.obj s) := res_base_smul Z.hom F E h x a
  let k : Fin (r + 1) := 0
  let P := offSingletonMixedSupport (Fin (d + 1)) k
  let Q := mixedSupport (Fin (d + 1)) (Fin (r + 1))
  let hP := (offSingletonMixedSupport_upper (I := Fin (d + 1)) k).ordConnected
  let hQ := joinedSupport_ordConnected (nonemptyIntersections_ordConnected (Fin (d + 1)))
    (nonemptyIntersections_ordConnected (Fin (r + 1)))
  let hS := supportDiff_ordConnected hQ (offSingletonMixedSupport_upper_in_mixed k)
  have hU' (i : Fin (d + 1)) (B : Z.left.Opens) (hB : IsAffineOpen B) :=
    isAffineOpen_preimage_inf q (hU i) hB
  have hV' (j : Fin (r + 1)) (B : Z.left.Opens) (hB : IsAffineOpen B) :=
    isAffineOpen_preimage_inf p (hV j) hB
  have hUV (i : Fin (d + 1)) (j : Fin (r + 1)) : IsAffineOpen (U' i ⊓ V' j) := by
    rw [inf_comm]
    exact isAffineOpen_product H (hV j) (hU i)
  obtain ⟨e₁⟩ := nonempty_homology_equiv_affine_mixed Z.hom F U' V' W hU' hV'
    (fun j B hB => (hW j).inf hB) hW hUV (q.iSup_preimage_eq_top cU)
    (p.iSup_preimage_eq_top cV) cW n
  have hAway (S : Finset (Fin (r + 1))) (h : S ∈ offSingletonSupport k) :
      let T := (D.truncate (R := K) P hP).leftSlice S
      ∀ x : T.Cochain, T.d x = 0 → ∃ y, T.d y = x := by
    let T := (D.truncate (R := K) P hP).leftSlice S
    let hT {a b : Finset (Fin (d + 1))} (hab : a ⊆ b) (c : K) (z : T.obj a) :=
      (D.truncate (R := K) P hP).leftSlice_linear (D.truncate_linear P hP hD) S hab c z
    have hSn : S.Nonempty := offSingletonSupport_le k h
    have hSaff : IsAffineOpen (S.inf V) := by
      simpa only [coverInter, top_inf_eq] using affine_coverInter_of_affine V hV S hSn
    obtain ⟨j, hj, hj₀⟩ := h
    have hno : o ∉ S.inf V := by
      intro ho
      have hle : S.inf V ≤ V j := Finset.inf_le hj
      exact hVaway j hj₀ (hle ho)
    obtain ⟨Y, π, f, V₀, Hp, hV₀, cV₀, ⟨I⟩⟩ := exists_affine_chart_cech hSaff U hU cU hM
    let a := (Spec.preimage (hSaff.fromSpec ≫ A.hom)).hom
    letI := a.toAlgebra
    have ht : hSaff.fromSpec ≫ A.hom = Spec.map (CommRingCat.ofHom a) := (Spec.map_preimage _).symm
    have haway (z : Spec Γ(A.left, S.inf V)) : hSaff.fromSpec z ≠ o := fun e =>
      hno (hSaff.range_fromSpec.le ⟨z, e⟩)
    have he := cech_acyclic_away_chart hA hL hAmp hK hSaff.fromSpec ht haway Hp V₀ hV₀ cV₀
    obtain ⟨J⟩ := nonempty_openCechIsoLeftSlice Z.hom F U' V' S P hP
      (fun s hs => by
        refine ⟨?_, ?_⟩
        · change (lft (uni s S)).Nonempty
          rwa [lft_uni]
        · change rgt (uni s S) ∈ offSingletonSupport k
          rw [rgt_uni]
          exact ⟨j, hj, hj₀⟩)
    let e : T.linearComplex hT ≅ cech (f ≫ Spec.map (CommRingCat.ofHom a)) (toMod (M.pull π)) V₀ := by
      rw [← ht]
      exact J ≪≫ eqToIso (congrArg (fun O => cechOverOpen Z.hom F O U') (preimage_finsetInf p V S)) ≪≫ I
    have h₀ : Subsingleton (T.obj ∅) :=
      D.subsingleton_truncate_obj P hP (uni ∅ S) (fun h => by
        have hf := h.1
        rw [lft_uni] at hf
        exact Finset.not_nonempty_empty hf)
    exact T.exists_primitive_of_acyclic_linearComplex hT h₀ fun m => (he m).of_iso e.symm
  obtain ⟨e₂⟩ := D.nonempty_homology_equiv_singleton_column hD k hAway (n + 1)
  let T := D.truncate (R := K) (Q \ P) hS
  have hzero (s : Finset (Fin (d + 1) ⊕ₗ Fin (r + 1))) (hs : rgt s ≠ {k}) :
      Subsingleton (T.obj s) := D.subsingleton_truncate_obj (Q \ P) hS s (fun hu => by
    have hold : ∀ j ∈ rgt s, j = k := fun j hj => by
      by_contra hn
      exact hu.2 ⟨hu.1.1, j, hj, hn⟩
    have hle : rgt s ⊆ {k} := fun j hj => Finset.mem_singleton.mpr (hold j hj)
    obtain ⟨j, hj⟩ := hu.1.2
    exact hs (Finset.Subset.antisymm hle (Finset.singleton_subset_iff.mpr (hold j hj ▸ hj))))
  have h₀ : Subsingleton ((T.leftSlice {k}).obj ∅) :=
    D.subsingleton_truncate_obj (Q \ P) hS (uni ∅ {k}) (fun hs => by
      have hf := hs.1.1
      rw [lft_uni] at hf
      exact Finset.not_nonempty_empty hf)
  let e₃ := T.homologyIsoSingletonColumn (D.truncate_linear (Q \ P) hS hD) k hzero h₀ n
  obtain ⟨e₄⟩ := nonempty_openCechIsoLeftSlice Z.hom F U' V' {k} (Q \ P) hS
    (fun s hs => by
      refine ⟨⟨?_, by simp [rgt_uni, nonemptyIntersections]⟩, ?_⟩
      · change (lft (uni s ({k} : Finset (Fin (r + 1))))).Nonempty
        rwa [lft_uni]
      · rintro ⟨_, j, hj, hj₀⟩
        exact hj₀ (Finset.mem_singleton.mp (by simpa only [rgt_uni] using hj)))
  obtain ⟨Y, π, f, V₀, Hp, hV₀', cV₀, ⟨I⟩⟩ := exists_affine_chart_cech (hV 0) U hU cU hM
  let a := (Spec.preimage ((hV 0).fromSpec ≫ A.hom)).hom
  letI := a.toAlgebra
  have ht : (hV 0).fromSpec ≫ A.hom = Spec.map (CommRingCat.ofHom a) := (Spec.map_preimage _).symm
  obtain ⟨χ, hχ⟩ := exists_origin_algHom (hV 0) hV₀
  have e₅ : cechOverOpen Z.hom F (({k} : Finset (Fin (r + 1))).inf V') U' ≅
      cech (f ≫ Spec.map (CommRingCat.ofHom a)) (toMod (M.pull π)) V₀ := by
    rw [Finset.inf_singleton, ← ht]
    exact I
  have h := finrank_cech_on_origin_chart hA hL hAmp hK d (hV 0).fromSpec ht χ hχ Hp V₀ hV₀' cV₀ n
  exact (e₁.trans (e₂.trans ((e₃ ≪≫ HomologicalComplex.homologyMapIso (e₄ ≪≫ e₅) n).toLinearEquiv))).finrank_eq.trans h.2

end GlobalTheory.MumfordFibre
