import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MixedCechSingleColumn
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechFaces

/-! On support restricted to one right singleton, the total differential
is the left differential with degrees shifted by one. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits GlobalTheory.WH

namespace HTGeometry.FinsetCechDatum

private def homologyShiftIso {R : Type} [CommRing R]
    (C B : CochainComplex (ModuleCat.{0} R) ℕ) (h₀ : IsZero (C.X 0))
    (e : ∀ n, C.X (n + 1) ≅ B.X n)
    (he : ∀ n, C.d (n + 1) (n + 2) ≫ (e (n + 1)).hom = (e n).hom ≫ B.d n (n + 1))
    (n : ℕ) : C.homology (n + 1) ≅ B.homology n := by
  cases n with
  | zero =>
    let iC : C.cycles 1 ≅ kernel (C.d 1 2) :=
      (C.cyclesIsKernel 1 2 (by simp)).conePointUniqueUpToIso (limit.isLimit _)
    let iB : B.cycles 0 ≅ kernel (B.d 0 1) :=
      (B.cyclesIsKernel 0 1 (by simp)).conePointUniqueUpToIso (limit.isLimit _)
    let j : kernel (C.d 1 2) ≅ kernel (B.d 0 1) :=
      HasLimit.isoOfNatIso (parallelPair.ext (e 0) (e 1) (he 0) (by simp))
    exact (C.isoHomologyπ 0 1 (by simp) (h₀.eq_zero_of_src _)).symm ≪≫ iC ≪≫ j ≪≫
      iB.symm ≪≫ B.isoHomologyπ₀
  | succ n =>
    let i : C.sc' (n + 1) (n + 2) (n + 3) ≅ B.sc' n (n + 1) (n + 2) :=
      ShortComplex.isoMk (e n) (e (n + 1)) (e (n + 2)) (he n).symm (he (n + 1)).symm
    exact C.homologyIsoSc' (n + 1) (n + 2) (n + 3) (by simp) (by simp) ≪≫
      ShortComplex.homologyMapIso i ≪≫ (B.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).symm

variable {R I J : Type} [CommRing R] [LinearOrder I] [LinearOrder J]
  (D : FinsetCechDatum.{0} (I ⊕ₗ J)) [∀ s, Module R (D.obj s)]
  (hD : ∀ {s t : Finset (I ⊕ₗ J)} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
  (k : J)

private def singletonTerm (n : ℕ) :
    D.degreeSubmodule (R := R) (n + 1) →ₗ[R]
      (D.leftSlice {k}).degreeSubmodule (R := R) n where
  toFun x := ⟨fun I₀ => x.1 (uni I₀ {k}), fun I₀ hI => x.2 _ (by
    rw [card_uni, Finset.card_singleton]
    exact fun e => hI (Nat.add_right_cancel e))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem singletonTerm_bijective
    (hz : ∀ s : Finset (I ⊕ₗ J), rgt s ≠ {k} → Subsingleton (D.obj s)) (n : ℕ) :
    Function.Bijective (D.singletonTerm (R := R) k n) := by
  classical
  refine ⟨fun x y e => Subtype.ext (funext fun s => ?_), fun x => ?_⟩
  · obtain ⟨I₀, J₀, rfl⟩ : ∃ I₀ J₀, s = uni I₀ J₀ := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    by_cases hJ : J₀ = {k}
    · subst J₀
      exact congrArg (fun z : (D.leftSlice {k}).degreeSubmodule (R := R) n => z.1 I₀) e
    · exact (hz (uni I₀ J₀) (by simpa only [rgt_uni] using hJ)).elim _ _
  · let a (I₀ : Finset I) (J₀ : Finset J) : D.obj (uni I₀ J₀) :=
      if h : J₀ = {k} then h.symm ▸ x.1 I₀ else 0
    let y := (D.cochainSlices R).symm a
    have hy (I₀ : Finset I) (J₀ : Finset J) : y (uni I₀ J₀) = a I₀ J₀ :=
      congrFun (congrFun ((D.cochainSlices R).apply_symm_apply a) I₀) J₀
    have hdeg : D.IsDeg y (n + 1) := by
      intro s
      obtain ⟨I₀, J₀, rfl⟩ : ∃ I₀ J₀, s = uni I₀ J₀ := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
      intro hs
      rw [hy]
      by_cases hJ : J₀ = {k}
      · subst J₀
        exact (dif_pos rfl).trans (x.2 I₀ (fun h => hs (by rw [card_uni, Finset.card_singleton, h])))
      · exact dif_neg hJ
    exact ⟨⟨y, hdeg⟩, Subtype.ext (funext fun I₀ => (hy I₀ {k}).trans (dif_pos rfl))⟩

/-- The right singleton contributes one total degree and has no internal differential. -/
def homologyIsoSingletonColumn
    (hz : ∀ s : Finset (I ⊕ₗ J), rgt s ≠ {k} → Subsingleton (D.obj s))
    (h₀ : Subsingleton ((D.leftSlice {k}).obj ∅)) (n : ℕ) :
    (D.linearComplex hD).homology (n + 1) ≅
      ((D.leftSlice {k}).linearComplex (D.leftSlice_linear hD {k})).homology n := by
  let C := D.linearComplex hD
  let B := (D.leftSlice {k}).linearComplex (D.leftSlice_linear hD {k})
  let e (m : ℕ) : C.X (m + 1) ≅ B.X m :=
    (LinearEquiv.ofBijective (D.singletonTerm k m) (D.singletonTerm_bijective k hz m)).toModuleIso
  have hzero : IsZero (C.X 0) := ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => by
    apply Subtype.ext
    funext s
    by_cases hj : rgt s = {k}
    · obtain ⟨I₀, rfl⟩ : ∃ I₀ : Finset I, s = uni I₀ {k} := ⟨lft s, by rw [← hj, uni_lft_rgt]⟩
      by_cases hi : I₀ = ∅
      · subst I₀
        exact h₀.elim _ _
      · have hcard : (uni I₀ ({k} : Finset J)).card ≠ 0 + 1 := by
          rw [card_uni, Finset.card_singleton]
          exact fun h => hi (Finset.card_eq_zero.mp (Nat.add_right_cancel h))
        exact (x.2 _ hcard).trans (y.2 _ hcard).symm
    · exact (hz s hj).elim _ _⟩
  refine homologyShiftIso C B hzero e (fun m => ?_) n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hC : ((C.d (m + 1) (m + 2)) x).1 = D.d x.1 := by
    change (CochainComplex.of.d (fun n : ℕ => ModuleCat.of R (D.degreeSubmodule (R := R) n))
      _ (m + 1) ((m + 1) + 1) x).1 = _
    rw [CochainComplex.of_d]
    rfl
  let v := (e m).hom x
  have hB : ((B.d m (m + 1)) v).1 = (D.leftSlice {k}).d v.1 := by
    change (CochainComplex.of.d
      (fun n : ℕ => ModuleCat.of R ((D.leftSlice {k}).degreeSubmodule (R := R) n))
      _ m (m + 1) v).1 = _
    rw [CochainComplex.of_d]
    rfl
  refine Subtype.ext (funext fun I₀ => ?_)
  change ((C.d (m + 1) (m + 2)) x).1 (uni I₀ {k}) = ((B.d m (m + 1)) v).1 I₀
  rw [hC, hB]
  change D.d x.1 (uni I₀ {k}) = (D.leftSlice {k}).d (fun s => x.1 (uni s {k})) I₀
  rw [D.d_uni]
  have h : (D.rightSlice I₀).d (fun s => x.1 (uni I₀ s)) {k} = 0 := by
    rw [FinsetCechDatum.d, Finset.sum_singleton]
    have h₁ : x.1 (uni I₀ (({k} : Finset J).erase k)) = 0 :=
      (hz _ (by simp [rgt_uni])).elim _ _
    simp only [h₁, map_zero, smul_zero]
  rw [h, smul_zero, add_zero]

end HTGeometry.FinsetCechDatum
