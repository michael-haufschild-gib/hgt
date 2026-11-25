import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPieceBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ModuleFractionBaseChange

/-! A graded polynomial-module base change induces base change of the Čech complex in every degree. -/

open CategoryTheory DirectSum HTGeometry MvPolynomial TensorProduct

namespace GlobalTheory

private theorem map_xProd_pow_smul {ι B R M N : Type} [CommRing B] [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    [Module (MvPolynomial ι B) M] [Module (MvPolynomial ι R) N]
    (f : M →ₗ[B] N) (hX : ∀ (i : ι) x, f ((X i : MvPolynomial ι B) • x) = (X i : MvPolynomial ι R) • f x)
    (s : Finset ι) (k : ℕ) (x : M) :
    f (xProd B s ^ k • x) = xProd R s ^ k • f x := by
  classical
  have h (y : M) : f (xProd B s • y) = xProd R s • f y := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp only [xProd, Finset.prod_insert hi, mul_smul, hX, ih]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h, ih]

theorem nonempty_gradedCech_baseChangeIso {ι B R M N : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing B] [CommRing R] [Algebra B R] [AddCommGroup M] [Module B M]
    [Module (MvPolynomial ι B) M] [IsScalarTower B (MvPolynomial ι B) M]
    [AddCommGroup N] [Module B N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower B R N] [IsScalarTower R (MvPolynomial ι R) N] [IsScalarTower B (MvPolynomial ι R) N]
    (D : ℤ → Submodule B M) [PolyGradedSMul ι D] [Decomposition D]
    (E : ℤ → Submodule R N) [PolyGradedSMul ι E] [Decomposition E]
    (f : M →ₗ[B] N) (hf : IsBaseChange R f)
    (hX : ∀ (i : ι) x, f ((X i : MvPolynomial ι B) • x) = (X i : MvPolynomial ι R) • f x)
    (hdeg : ∀ n, ∀ x ∈ D n, f x ∈ E n) (n : ℤ) :
    Nonempty ((((ModuleCat.extendScalars (algebraMap B R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (gradedCech (ι := ι) D n)) ≅ gradedCech (ι := ι) E n) := by
  classical
  have exists_fraction_map (s : Finset ι) :
      ∃ θ : LocalizedModule.Away (xProd B s) M →ₗ[B] LocalizedModule.Away (xProd R s) N,
        IsBaseChange R θ ∧ ∀ (k : ℕ) x, θ (ModuleFraction.frac (xProd B s) k x) =
          ModuleFraction.frac (xProd R s) k (f x) := by
    obtain ⟨θ, hθ⟩ := ModuleFraction.exists_map_of_intertwine f _ _ (map_xProd_pow_smul f hX s)
    exact ⟨θ, ModuleFraction.isBaseChange_of_intertwine f hf _ _ (map_xProd_pow_smul f hX s) θ hθ, hθ⟩
  choose θ hθ hvals using exists_fraction_map
  have hθgr (s : Finset ι) (j : ℤ) : ∀ z ∈ homLoc D s j, θ s z ∈ homLoc E s j := by
    rintro _ ⟨k, x, hx, rfl⟩
    rw [hvals]
    exact frac_mem_homLoc E (hdeg _ _ hx) rfl
  let ψ (s : Finset ι) : homLoc D s n →ₗ[B] homLoc E s n :=
    { toFun := fun x => ⟨θ s x, hθgr s n x x.2⟩
      map_add' := fun x y => Subtype.ext (map_add (θ s) x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul (θ s) r x.1) }
  have hψ (s : Finset ι) : IsBaseChange R (ψ s) :=
    isBaseChange_gradedPiece (homLoc D s) (homLoc E s) (θ s) n (ψ s) (hθ s) (hθgr s) fun _ => rfl
  let φ : (homLocDatum (ι := ι) D n).Hom (homLocDatum (ι := ι) E n) :=
    { app := fun s => (ψ s).toAddMonoidHom
      comm := by
        intro s t h x
        obtain ⟨k, v, rfl⟩ := exists_homLocMk D x
        apply Subtype.ext
        change ModuleFraction.restrict (xProd_dvd R h) (θ s (ModuleFraction.frac (xProd B s) k v)) =
          θ t (ModuleFraction.restrict (xProd_dvd B h) (ModuleFraction.frac (xProd B s) k v))
        rw [hvals, ModuleFraction.restrict_frac _ (Finset.prod_sdiff h).symm,
          ModuleFraction.restrict_frac _ (Finset.prod_sdiff h).symm, hvals]
        exact congrArg _ (map_xProd_pow_smul f hX (t \ s) k v).symm }
  have hφ (s : Finset ι) (r : B) (x : (homLocDatum (ι := ι) D n).obj s) :
      φ.app s (r • x) = (algebraMap B R r) • φ.app s x := by
    let y : homLoc D s n := x
    exact ((ψ s).map_smul r y).trans (algebraMap_smul R r (ψ s y)).symm
  let F := (ModuleCat.extendScalars (algebraMap B R)).mapHomologicalComplex (ComplexShape.up ℕ)
  let g : F.obj (gradedCech (ι := ι) D n) ⟶ gradedCech (ι := ι) E n :=
    FinsetCechDatum.linearBaseChange (algebraMap B R) φ hφ
      (fun h => homLocDatum_res_smul D h n) (fun h => homLocDatum_res_smul E h n)
  have hg : IsIso g := FinsetCechDatum.isIso_linearBaseChange _ _ _ _ _ (fun s _ => by
    let α : B →+* R := algebraMap B R
    let T (A : Algebra B R) : Prop :=
      letI := A
      ∃ e : R ⊗[B] homLoc D s n ≃ₗ[R] homLoc E s n, ∀ x, e (1 ⊗ₜ[B] x) = ψ s x
    have h : T inferInstance := ⟨(hψ s).equiv, fun x =>
      ((hψ s).equiv_tmul 1 x).trans (one_smul R (ψ s x))⟩
    obtain ⟨e, he⟩ := (congrArg T (toAlgebra_algebraMap (R := B) (S := R))).mpr h
    letI : Algebra B R := α.toAlgebra
    letI : Module B ((homLocDatum (ι := ι) E n).obj s) := Module.compHom _ α
    letI : IsScalarTower B R ((homLocDatum (ι := ι) E n).obj s) :=
      .of_algebraMap_smul fun _ _ => rfl
    let e' : R ⊗[B] (homLocDatum (ι := ι) D n).obj s ≃ₗ[R] (homLocDatum (ι := ι) E n).obj s := e
    exact IsBaseChange.of_equiv e' he)
  exact ⟨@asIso _ _ _ _ g hg⟩

end GlobalTheory
