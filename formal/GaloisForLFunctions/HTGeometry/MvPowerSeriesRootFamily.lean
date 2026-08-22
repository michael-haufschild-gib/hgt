import GaloisForLFunctions.HTGeometry.MvPowerSeriesOptionSplit
import GaloisForLFunctions.HTGeometry.ResidueRootFamilyTransfer
import GaloisForLFunctions.HTGeometry.ResidueRootUniqueness
import GaloisForLFunctions.HTGeometry.MonicDistinctRootFactorization

/-!
# The canonical labelled root family in a multivariate power series ring

A polynomial over `A⟦u_σ⟧` whose constant term splits with distinct roots has, for each residue
root, exactly one root congruent to it.  Splitting off one variable at a time reduces existence to
the one-variable case, and the residue determines the root, so the family does not depend on the
order in which the variables were split off.  This is the canonical labelling that different
deformation routes must agree with.

## Main results

* `mvRenameEquiv` — reindexing the variables.
* `mvPowerSeriesEmptyEquiv` — no variables at all.
* `exists_mvPowerSeriesRootFamily` — the labelled family of roots.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reindexing the variables of a multivariate power series ring. -/
def mvRenameEquiv {σ τ A : Type} [CommSemiring A] (e : σ ≃ τ) :
    MvPowerSeries σ A ≃+* MvPowerSeries τ A where
  toFun := MvPowerSeries.rename (e : σ → τ)
  invFun := MvPowerSeries.rename (e.symm : τ → σ)
  left_inv f := by
    have hid : (e.symm : τ → σ) ∘ (e : σ → τ) = id := by
      funext x
      simp
    rw [MvPowerSeries.rename_rename]
    simp only [hid, MvPowerSeries.rename_id]
    rfl
  right_inv f := by
    have hid : (e : σ → τ) ∘ (e.symm : τ → σ) = id := by
      funext x
      simp
    rw [MvPowerSeries.rename_rename]
    simp only [hid, MvPowerSeries.rename_id]
    rfl
  map_add' f g := map_add _ f g
  map_mul' f g := map_mul _ f g

@[simp] theorem constantCoeff_mvRenameEquiv {σ τ A : Type} [CommSemiring A] (e : σ ≃ τ)
    (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (mvRenameEquiv e f) = MvPowerSeries.constantCoeff f :=
  MvPowerSeries.constantCoeff_rename _ f

/-- With no variables the constant coefficient is an isomorphism. -/
def mvPowerSeriesEmptyEquiv (A : Type) [CommSemiring A] :
    MvPowerSeries PEmpty.{1} A ≃+* A where
  toFun := MvPowerSeries.constantCoeff
  invFun := (MvPowerSeries.C : A →+* MvPowerSeries PEmpty.{1} A)
  left_inv f := by
    ext e
    have he : e = 0 := Subsingleton.elim e 0
    subst he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
    simp
  right_inv a := by simp
  map_add' f g := map_add _ f g
  map_mul' f g := map_mul _ f g

/-- A monic polynomial with a full family of distinct roots splits into the linear factors, for an
arbitrary finite index type. -/
theorem eq_prod_X_sub_C_of_monic_of_injective_family {R : Type} [CommRing R] [IsDomain R]
    {ι : Type} [Fintype ι] {p : R[X]} (hp : p.Monic) (hd : p.natDegree = Fintype.card ι)
    {f : ι → R} (hf : Function.Injective f) (hroot : ∀ i, p.IsRoot (f i)) :
    p = ∏ i, (X - C (f i)) := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hfe : Function.Injective (f ∘ e.symm) := hf.comp e.symm.injective
  have := eq_prod_X_sub_C_of_monic_of_injective_roots hp hd hfe (fun i => hroot _)
  rw [this]
  exact Fintype.prod_equiv e.symm _ _ fun i => rfl

/-- A multivariate power series ring in finitely many variables over a field is a domain. -/
theorem isDomain_mvPowerSeries (A : Type) [Field A] :
    ∀ (σ : Type) [Fintype σ], IsDomain (MvPowerSeries σ A) := by
  refine Fintype.induction_empty_option (P := fun σ _ => IsDomain (MvPowerSeries σ A)) ?_ ?_ ?_
  · intro α β _ e h
    exact Function.Injective.isDomain
      ((mvRenameEquiv (A := A) e.symm : MvPowerSeries β A →+* MvPowerSeries α A))
      (mvRenameEquiv (A := A) e.symm).injective
  · exact Function.Injective.isDomain
      ((mvPowerSeriesEmptyEquiv A : MvPowerSeries PEmpty.{1} A →+* A))
      (mvPowerSeriesEmptyEquiv A).injective
  · intro α _ h
    haveI := h
    exact Function.Injective.isDomain
      ((MvPowerSeries.optionEquivLeft α A :
        MvPowerSeries (Option α) A →+* PowerSeries (MvPowerSeries α A)))
      (MvPowerSeries.optionEquivLeft α A).injective

/-- **The canonical labelled root family in a multivariate power series ring.** -/
theorem exists_mvPowerSeriesRootFamily (A : Type) [Field A]
    {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → A) (hinj : Function.Injective d) :
    ∀ (σ : Type) [Fintype σ] (F : Polynomial (MvPowerSeries σ A)), F.Monic →
      F.map (MvPowerSeries.constantCoeff (σ := σ) (R := A)) = ∏ x, (X - C (d x)) →
      ∃ Θ : ι → MvPowerSeries σ A,
        F = ∏ x, (X - C (Θ x)) ∧
          ∀ x, MvPowerSeries.constantCoeff (Θ x) = d x := by
  classical
  have hdeg : ∀ {R : Type} [CommRing R] (F : Polynomial R) (φ : R →+* A), F.Monic →
      F.map φ = ∏ x, (X - C (d x)) → F.natDegree = Fintype.card ι := by
    intro R _ F φ hm hmap
    have h1 : (F.map φ).natDegree = F.natDegree := hm.natDegree_map φ
    rw [hmap] at h1
    rw [← h1, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (d i)]
    simp
  refine Fintype.induction_empty_option (P := fun σ _ =>
    ∀ (F : Polynomial (MvPowerSeries σ A)), F.Monic →
      F.map (MvPowerSeries.constantCoeff (σ := σ) (R := A)) = ∏ x, (X - C (d x)) →
      ∃ Θ : ι → MvPowerSeries σ A,
        F = ∏ x, (X - C (Θ x)) ∧
          ∀ x, MvPowerSeries.constantCoeff (Θ x) = d x) ?_ ?_ ?_
  · -- transport along an equivalence of variable types
    intro α β _ e IH F hm hres
    set ψ : MvPowerSeries β A ≃+* MvPowerSeries α A := mvRenameEquiv e.symm with hψ
    set F' : Polynomial (MvPowerSeries α A) := F.map (ψ : MvPowerSeries β A →+* MvPowerSeries α A)
      with hF'
    have hm' : F'.Monic := hm.map _
    have hres' : F'.map (MvPowerSeries.constantCoeff (σ := α) (R := A))
        = ∏ x, (X - C (d x)) := by
      rw [hF', Polynomial.map_map]
      rw [show (MvPowerSeries.constantCoeff (σ := α) (R := A)).comp
          (ψ : MvPowerSeries β A →+* MvPowerSeries α A)
          = MvPowerSeries.constantCoeff (σ := β) (R := A) from
        RingHom.ext fun f => constantCoeff_mvRenameEquiv e.symm f]
      exact hres
    obtain ⟨Θ', hprod', hconst'⟩ := IH F' hm' hres'
    refine ⟨fun x => ψ.symm (Θ' x), ?_, ?_⟩
    · have hback : F = F'.map (ψ.symm : MvPowerSeries α A →+* MvPowerSeries β A) := by
        rw [hF', Polynomial.map_map]
        rw [show (ψ.symm : MvPowerSeries α A →+* MvPowerSeries β A).comp
            (ψ : MvPowerSeries β A →+* MvPowerSeries α A) = RingHom.id _ from
          RingHom.ext fun f => ψ.symm_apply_apply f]
        exact (Polynomial.map_id).symm
      rw [hback, hprod', Polynomial.map_prod]
      exact Finset.prod_congr rfl fun x _ => by
        simp
    · intro x
      have h := constantCoeff_mvRenameEquiv (A := A) e.symm (ψ.symm (Θ' x))
      rw [show (mvRenameEquiv (A := A) e.symm) (ψ.symm (Θ' x)) = Θ' x from
        ψ.apply_symm_apply (Θ' x)] at h
      rw [← h, hconst' x]
  · -- no variables
    intro F hm hres
    haveI : IsDomain (MvPowerSeries PEmpty.{1} A) := isDomain_mvPowerSeries A PEmpty.{1}
    refine ⟨fun x => (mvPowerSeriesEmptyEquiv A).symm (d x), ?_, ?_⟩
    · refine eq_prod_X_sub_C_of_monic_of_injective_family hm
        (hdeg F (MvPowerSeries.constantCoeff (σ := PEmpty.{1}) (R := A)) hm hres)
        (fun a b hab => hinj (by simpa using congrArg (mvPowerSeriesEmptyEquiv A) hab)) ?_
      intro x
      show Polynomial.eval ((mvPowerSeriesEmptyEquiv A).symm (d x)) F = 0
      apply (mvPowerSeriesEmptyEquiv A).injective
      rw [map_zero]
      show MvPowerSeries.constantCoeff
        (Polynomial.eval ((mvPowerSeriesEmptyEquiv A).symm (d x)) F) = 0
      have := Polynomial.eval_map_apply (MvPowerSeries.constantCoeff (σ := PEmpty.{1}) (R := A))
        ((mvPowerSeriesEmptyEquiv A).symm (d x)) (p := F)
      rw [show MvPowerSeries.constantCoeff ((mvPowerSeriesEmptyEquiv A).symm (d x)) = d x from
        (mvPowerSeriesEmptyEquiv A).apply_symm_apply (d x)] at this
      rw [← this, hres, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp)
    · intro x
      exact (mvPowerSeriesEmptyEquiv A).apply_symm_apply (d x)
  · -- one more variable
    intro α _ IH F hm hres
    haveI : IsDomain (MvPowerSeries α A) := isDomain_mvPowerSeries A α
    haveI : IsDomain (MvPowerSeries (Option α) A) := isDomain_mvPowerSeries A (Option α)
    set G : Polynomial (PowerSeries (MvPowerSeries α A)) :=
      F.map (MvPowerSeries.optionEquivLeft α A : MvPowerSeries (Option α) A →+*
        PowerSeries (MvPowerSeries α A)) with hG
    have hmG : G.Monic := hm.map _
    set F'' : Polynomial (MvPowerSeries α A) :=
      G.map (PowerSeries.constantCoeff (R := MvPowerSeries α A)) with hF''
    have hmF'' : F''.Monic := hmG.map _
    have hres'' : F''.map (MvPowerSeries.constantCoeff (σ := α) (R := A))
        = ∏ x, (X - C (d x)) := by
      rw [hF'', hG, Polynomial.map_map, Polynomial.map_map]
      rw [show ((MvPowerSeries.constantCoeff (σ := α) (R := A)).comp
            (PowerSeries.constantCoeff (R := MvPowerSeries α A))).comp
            (MvPowerSeries.optionEquivLeft α A :
              MvPowerSeries (Option α) A →+* PowerSeries (MvPowerSeries α A))
          = MvPowerSeries.constantCoeff (σ := Option α) (R := A) from
        RingHom.ext fun f => constantCoeff_optionSplit f]
      exact hres
    obtain ⟨Θ'', hprod'', hconst''⟩ := IH F'' hmF'' hres''
    have hinjΘ'' : Function.Injective fun x => MvPowerSeries.constantCoeff (Θ'' x) := by
      intro a b hab
      have hab' : MvPowerSeries.constantCoeff (Θ'' a) = MvPowerSeries.constantCoeff (Θ'' b) := hab
      rw [hconst'' a, hconst'' b] at hab'
      exact hinj hab'
    obtain ⟨y, hyroot, hycong, -⟩ :=
      exists_powerSeriesRootFamily_of_residue
        (MvPowerSeries.constantCoeff (σ := α) (R := A))
        (fun r hr => by
          rw [MvPowerSeries.isUnit_iff_constantCoeff]
          exact hr.isUnit)
        G Θ'' hinjΘ'' (by rw [← hF'']; exact hprod'')
    refine ⟨fun x => (MvPowerSeries.optionEquivLeft α A).symm (y x), ?_, ?_⟩
    · have hback : F = G.map
          ((MvPowerSeries.optionEquivLeft α A).symm :
            PowerSeries (MvPowerSeries α A) →+* MvPowerSeries (Option α) A) := by
        rw [hG, Polynomial.map_map]
        rw [show ((MvPowerSeries.optionEquivLeft α A).symm :
              PowerSeries (MvPowerSeries α A) →+* MvPowerSeries (Option α) A).comp
            (MvPowerSeries.optionEquivLeft α A : MvPowerSeries (Option α) A →+*
              PowerSeries (MvPowerSeries α A)) = RingHom.id _ from
          RingHom.ext fun f => (MvPowerSeries.optionEquivLeft α A).symm_apply_apply f]
        exact (Polynomial.map_id).symm
      have hGprod : G = ∏ x, (X - C (y x)) := by
        refine eq_prod_X_sub_C_of_monic_of_injective_family hmG
          (hdeg G ((MvPowerSeries.constantCoeff (σ := α) (R := A)).comp
            (PowerSeries.constantCoeff (R := MvPowerSeries α A))) hmG ?_) ?_ hyroot
        · rw [← Polynomial.map_map, ← hF'']
          exact hres''
        · intro a b hab
          refine hinjΘ'' ?_
          show MvPowerSeries.constantCoeff (Θ'' a) = MvPowerSeries.constantCoeff (Θ'' b)
          have ha : PowerSeries.constantCoeff (R := MvPowerSeries α A) (y a) = Θ'' a := by
            have := (PowerSeries.X_dvd_iff (R := MvPowerSeries α A)).mp (hycong a)
            rw [map_sub, PowerSeries.constantCoeff_C] at this
            exact sub_eq_zero.mp this
          have hb : PowerSeries.constantCoeff (R := MvPowerSeries α A) (y b) = Θ'' b := by
            have := (PowerSeries.X_dvd_iff (R := MvPowerSeries α A)).mp (hycong b)
            rw [map_sub, PowerSeries.constantCoeff_C] at this
            exact sub_eq_zero.mp this
          rw [← ha, ← hb, hab]
      rw [hback, hGprod, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun x _ => by
        simp
    · intro x
      have hy : PowerSeries.constantCoeff (R := MvPowerSeries α A) (y x) = Θ'' x := by
        have := (PowerSeries.X_dvd_iff (R := MvPowerSeries α A)).mp (hycong x)
        rw [map_sub, PowerSeries.constantCoeff_C] at this
        exact sub_eq_zero.mp this
      have hjoin := constantCoeff_optionJoin (y x)
      show MvPowerSeries.constantCoeff (optionJoin (y x)) = d x
      rw [hjoin, hy, hconst'' x]

/-- **The canonical labelled root family is equivariant.**  A coefficientwise automorphism fixing the
polynomial permutes the roots exactly as it permutes their constant coefficients. -/
theorem map_mvRootFamily_of_perm {A : Type} [Field A] {σ : Type} [Fintype σ]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Polynomial (MvPowerSeries σ A)} {Θ : ι → MvPowerSeries σ A} {d : ι → A}
    (hprod : F = ∏ x, (X - C (Θ x)))
    (hconst : ∀ x, MvPowerSeries.constantCoeff (Θ x) = d x)
    (hdinj : Function.Injective d)
    (φ : A ≃+* A) (hF : F.map (MvPowerSeries.map (φ : A →+* A)) = F)
    (π : Equiv.Perm ι) (hπ : ∀ x, φ (d x) = d (π x)) (x : ι) :
    MvPowerSeries.map (φ : A →+* A) (Θ x) = Θ (π x) := by
  classical
  have hroot : ∀ y, F.IsRoot (Θ y) := by
    intro y
    rw [hprod]
    show Polynomial.eval (Θ y) (∏ z, (X - C (Θ z))) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp)
  have hderiv : ∀ y, MvPowerSeries.constantCoeff
      ((Polynomial.derivative F).eval (Θ y)) ≠ 0 := by
    intro y
    rw [hprod, eval_derivative_prod_X_sub_C]
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun z hz => ?_
    rw [map_sub, hconst, hconst]
    intro h0
    exact (Finset.mem_erase.mp hz).1 (hdinj (sub_eq_zero.mp h0)).symm
  have hrootmap : F.IsRoot (MvPowerSeries.map (φ : A →+* A) (Θ x)) := by
    show Polynomial.eval (MvPowerSeries.map (φ : A →+* A) (Θ x)) F = 0
    rw [← hF, Polynomial.eval_map_apply]
    rw [show Polynomial.eval (Θ x) F = 0 from hroot x, map_zero]
  have hcc : MvPowerSeries.constantCoeff (MvPowerSeries.map (φ : A →+* A) (Θ x))
      = d (π x) := by
    rw [MvPowerSeries.constantCoeff_map, hconst x]
    exact hπ x
  exact (isRoot_unique_mvPowerSeries (hroot (π x)) hrootmap (hderiv (π x))
    (by rw [hconst (π x), hcc])).symm

end

end GaloisForLFunctions.HTGeometry
