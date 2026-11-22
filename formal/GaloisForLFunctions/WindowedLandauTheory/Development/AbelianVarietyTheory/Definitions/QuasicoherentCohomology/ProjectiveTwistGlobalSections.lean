import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectivePolynomialCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ModuleCechComparison

/-! A global section of a negative projective twist is determined by one Laurent
coefficient on a coordinate chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

open UpperTheory.Cb

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (K : Type) [Field K] (N m : ℕ)

private abbrev D := polyTwCech K (Fin (N + 1)) PEmpty m
private abbrev X := PSpace K N
private abbrev F := pspaceTwist K N (-(m : ℤ))
private abbrev U := PSpace.coordinateOpen K N
private abbrev W₀ := coverInter ⊤ (U K N) ∅
private abbrev W₁ := coverInter ⊤ (U K N) {0}
private abbrev comparison := pspaceTwistCechMap K N m
private abbrev hsub : (∅ : Finset (Fin (N + 1))) ⊆ {0} := Finset.empty_subset _
private abbrev exp₀ : LaurentExp (Fin (N + 1)) PEmpty := Finsupp.single (Sum.inl 0) (-(m : ℤ))

private abbrev e₁ : (D K N m).obj {0} ≃+ Γ(F K N m, W₁ K N) :=
  AddEquiv.ofBijective ((comparison K N m).app {0})
    (pspaceTwistCechMap_bijective K N m (Finset.singleton_nonempty _))

private def res₁ : Γ(F K N m, W₀ K N) →+ Γ(F K N m, W₁ K N) :=
  ((F K N m).presheaf.map
    (homOfLE (coverInter_anti (V := ⊤) (U := U K N) (hsub N))).op).hom

private theorem res₁_comparison (z : (D K N m).obj ∅) :
    res₁ K N m ((comparison K N m).app ∅ z) =
      (e₁ K N m) ((D K N m).res (hsub N) z) :=
  (comparison K N m).comm (hsub N) z

private def laurentHom (a : Finset (Fin (N + 1))) :
    (D K N m).obj a →+ LaurentRing K (Fin (N + 1)) PEmpty :=
  (laurentLoc K (Fin (N + 1)) PEmpty a).toAddMonoidHom.comp (twValHom a)

private theorem laurentHom_injective (a : Finset (Fin (N + 1))) :
    Function.Injective (laurentHom K N m a) :=
  (laurentLoc_injective a).comp (twVal_injective projCoord_mem)

private theorem laurentHom_res (z : (D K N m).obj ∅) :
    laurentHom K N m {0} ((D K N m).res (hsub N) z) = laurentHom K N m ∅ z :=
  laurentLoc_resLoc (hsub N) (twVal projCoord_mem z)

private theorem exp_eq_of_degree {a : LaurentExp (Fin (N + 1)) PEmpty}
    (ha : DegAdm m a) (hs : N = 0 ∨ negSupp a ⊆ ∅) : a = exp₀ N m := by
  rcases hs with rfl | hs
  · ext j
    rcases j with j | j
    · have h := ha.2
      rw [Fin.sum_univ_one] at h
      have hj : j = 0 := Fin.eq_zero j
      rw [hj]
      exact h.trans Finsupp.single_eq_same.symm
    · exact isEmptyElim j
  · have hnonneg (j : Fin (N + 1)) : 0 ≤ a (Sum.inl j) := by
      by_contra! h
      exact Finset.notMem_empty j (hs (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩))
    have hsum : 0 ≤ ∑ j, a (Sum.inl j) :=
      Finset.sum_nonneg fun j _ => hnonneg j
    rw [ha.2] at hsum
    have hm : m = 0 := by omega
    subst m
    ext j
    rcases j with j | j
    · have hle := Finset.single_le_sum (f := fun i => a (Sum.inl i))
        (fun i _ => hnonneg i) (Finset.mem_univ j)
      rw [ha.2] at hle
      simpa [exp₀] using le_antisymm hle (hnonneg j)
    · exact isEmptyElim j

private theorem glob_exp_eq (x : Γ(F K N m, W₀ K N))
    {a : LaurentExp (Fin (N + 1)) PEmpty}
    (ha : a ∈ (laurentHom K N m {0} ((e₁ K N m).symm (res₁ K N m x))).coeff.support) :
    a = exp₀ N m := by
  by_cases hN : N = 0
  · have h := laurentLoc_mem_admSubgroup ((e₁ K N m).symm (res₁ K N m x)).2 a ha
    exact exp_eq_of_degree N m h.2 (Or.inl hN)
  · obtain ⟨z, rfl⟩ := pspaceTwistCechMap_surjective_global K N m (Or.inr (by omega)) x
    rw [res₁_comparison, AddEquiv.symm_apply_apply, laurentHom_res] at ha
    have hadm := laurentLoc_mem_admSubgroup z.2 a ha
    exact exp_eq_of_degree N m hadm.2 (Or.inr hadm.1)

private theorem res₁_injective : Function.Injective (res₁ K N m) := by
  by_cases hN : N = 0
  · subst N
    have hW : W₁ K 0 = W₀ K 0 := by
      change coverInter ⊤ (U K 0) {0} = coverInter ⊤ (U K 0) ∅
      rw [coverInter_empty, coverInter_singleton, top_inf_eq]
      apply le_antisymm le_top
      rw [← PSpace.iSup_coordinateOpen K 0]
      refine iSup_le (fun i => ?_)
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
    have hi : IsIso (homOfLE (coverInter_anti (V := ⊤) (U := U K 0) (hsub 0))) := by
      rw [show homOfLE (coverInter_anti (V := ⊤) (U := U K 0) (hsub 0)) =
        eqToHom hW from Subsingleton.elim _ _]
      infer_instance
    letI := hi
    exact (ConcreteCategory.bijective_of_isIso
      ((F K 0 m).presheaf.map (homOfLE (coverInter_anti (V := ⊤) (U := U K 0) (hsub 0))).op)).1
  · intro x y hxy
    have hsurj := pspaceTwistCechMap_surjective_global K N m (Or.inr (by omega))
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [res₁_comparison, res₁_comparison] at hxy
    apply congrArg ((comparison K N m).app ∅)
    apply laurentHom_injective K N m ∅
    rw [← laurentHom_res K N m a, ← laurentHom_res K N m b, (e₁ K N m).injective hxy]

private def globLaurent : Γ(F K N m, W₀ K N) →+ LaurentRing K (Fin (N + 1)) PEmpty :=
  (laurentHom K N m {0}).comp ((e₁ K N m).symm.toAddMonoidHom.comp (res₁ K N m))

private def globalCoefficient : Γ(F K N m, W₀ K N) →+ K :=
  { toFun := fun x => (globLaurent K N m x).coeff (exp₀ N m)
    map_zero' := by rw [map_zero, AddMonoidAlgebra.coeff_zero]; rfl
    map_add' := fun x y => by rw [map_add, AddMonoidAlgebra.coeff_add]; rfl }

private theorem globalCoefficient_injective : Function.Injective (globalCoefficient K N m) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hzero : globLaurent K N m x = 0 := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro a
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra h
    have ha := glob_exp_eq K N m x (Finsupp.mem_support_iff.mpr h)
    subst a
    exact h hx
  have hinj := (laurentHom_injective K N m {0}).comp
    ((e₁ K N m).symm.injective.comp (res₁_injective K N m))
  exact hinj (hzero.trans (map_zero (globLaurent K N m)).symm)

private theorem globalCoefficient_smul (r : K) (x : Γ(F K N m, W₀ K N)) :
    letI := sectionAlgebra (PSpace.str K N) ⊤
    globalCoefficient K N m ((globalSectionEnd (F K N m)
      (algebraMap K Γ(X K N, ⊤) r)).app (W₀ K N) x) = r • globalCoefficient K N m x := by
  letI := sectionAlgebra (PSpace.str K N) ⊤
  let t := globalSectionEnd (F K N m) (algebraMap K Γ(X K N, ⊤) r)
  let z := (e₁ K N m).symm (res₁ K N m x)
  have hn : res₁ K N m (t.app (W₀ K N) x) = t.app (W₁ K N) (res₁ K N m x) :=
    ConcreteCategory.congr_hom
      (t.mapPresheaf.naturality (homOfLE (coverInter_anti (V := ⊤) (U := U K N) (hsub N))).op).symm x
  have hz : (e₁ K N m).symm (res₁ K N m (t.app (W₀ K N) x)) =
      (polynomialTwistScale m r).app {0} z := by
    apply (e₁ K N m).injective
    rw [AddEquiv.apply_symm_apply, hn, globalSectionEnd_app]
    have he : (comparison K N m).app {0} z = res₁ K N m x :=
      (e₁ K N m).apply_symm_apply _
    rw [← he]
    exact (pspaceTwistCechMap_scale K N m r (Finset.singleton_nonempty _) z).symm
  let c : (D K N m).Cochain := fun a => if h : a = {0} then h.symm ▸ z else 0
  have hc : c {0} = z := dif_pos rfl
  have h := congrArg (fun f : LaurentExp (Fin (N + 1)) PEmpty →₀ K => f (exp₀ N m))
    (laurentCoeffs_scale r c {0})
  change (laurentHom K N m {0} ((polynomialTwistScale m r).app {0} (c {0}))).coeff
    (exp₀ N m) = r • (laurentHom K N m {0} (c {0})).coeff (exp₀ N m) at h
  rw [hc] at h
  change (laurentHom K N m {0} ((e₁ K N m).symm (res₁ K N m (t.app (W₀ K N) x)))).coeff
    (exp₀ N m) = _
  rw [hz]
  exact h

/-- The degree-zero Čech cohomology of a negative twist is finite over the base field. -/
theorem pspaceTwist_zeroCech_finite :
    letI := sectionAlgebra (PSpace.str K N) ⊤
    let H := ModuleCechCohomology ⊤ (U K N) (F K N m) 0
    letI := Module.compHom H (algebraMap K Γ(X K N, ⊤))
    Module.Finite K H := by
  letI := sectionAlgebra (PSpace.str K N) ⊤
  let H := ModuleCechCohomology ⊤ (U K N) (F K N m) 0
  letI := Module.compHom H (algebraMap K Γ(X K N, ⊤))
  let A := SheafOfModules.toSheaf (X K N).ringCatSheaf
  let e : Γ(F K N m, W₀ K N) ≃+ H :=
    sectionsToCechH0 (A.obj (F K N m)) (PSpace.iSup_coordinateOpen K N).ge
  let f : H →ₗ[K] K :=
    { (globalCoefficient K N m).comp e.symm.toAddMonoidHom with
      map_smul' := fun r x => by
        obtain ⟨y, rfl⟩ := e.surjective x
        have h := sectionsToCechH0_natural (A.obj (F K N m))
          (A.map (globalSectionEnd (F K N m) (algebraMap K Γ(X K N, ⊤) r)))
          (PSpace.iSup_coordinateOpen K N).ge y
        change r • e y = e ((globalSectionEnd (F K N m)
          (algebraMap K Γ(X K N, ⊤) r)).app (W₀ K N) y) at h
        change globalCoefficient K N m (e.symm (r • e y)) =
          r • globalCoefficient K N m (e.symm (e y))
        rw [h, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
        exact globalCoefficient_smul K N m r y }
  exact Module.Finite.of_injective f ((globalCoefficient_injective K N m).comp e.symm.injective)

end GlobalTheory.SchemeCohomology
