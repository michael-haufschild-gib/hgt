import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GradedCechHomology

/-! The categorical comparison with the cycle quotient is natural in maps of complexes. -/

noncomputable section

open CategoryTheory

namespace GlobalTheory.CechDR.Cx

variable {k M N : Type} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]
  {K : Cx k M} {L : Cx k N} {n : ℤ} {S T : ShortComplex AddCommGrpCat.{0}}

theorem homologyAddEquiv_natural
    (eS : S.X₂ ≃+ K.C n) (eT : T.X₂ ≃+ L.C n)
    (hgS : ∀ x, S.g x = 0 ↔ K.D (eS x) = 0)
    (hgT : ∀ x, T.g x = 0 ↔ L.D (eT x) = 0)
    (hfS : ∀ x : K.C n, (x : M) ∈ K.B n ↔ ∃ y, eS (S.f y) = x)
    (hfT : ∀ x : L.C n, (x : N) ∈ L.B n ↔ ∃ y, eT (T.f y) = x)
    (φ : S ⟶ T) (f : M →ₗ[k] N) (hf : IsMap K L f)
    (h : ∀ x : S.X₂, (eT (φ.τ₂ x) : N) = f (eS x)) (x : S.homology) :
    homologyAddEquiv eT hgT hfT (ShortComplex.homologyMap φ x) =
      K.hmap L f hf n (homologyAddEquiv eS hgS hfS x) := by
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  let z' := ShortComplex.cyclesMap φ z
  have hn : ShortComplex.homologyMap φ (S.homologyπ z) = T.homologyπ z' :=
    ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) z
  have hcomm : T.iCycles z' = φ.τ₂ (S.iCycles z) :=
    ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) z
  let a : K.Z n :=
    ⟨(eS (S.iCycles z)).val, (eS (S.iCycles z)).2,
     LinearMap.mem_ker.mpr ((hgS _).mp (ConcreteCategory.congr_hom S.iCycles_g z))⟩
  let b : L.Z n :=
    ⟨(eT (T.iCycles z')).val, (eT (T.iCycles z')).2,
     LinearMap.mem_ker.mpr ((hgT _).mp (ConcreteCategory.congr_hom T.iCycles_g z'))⟩
  have hab : b.val = f a.val := by
    change (eT (T.iCycles z') : N) = f (eS (S.iCycles z))
    rw [hcomm]
    exact h _
  rw [hn, homologyAddEquiv_π_val eT hgT hfT z' b rfl, homologyAddEquiv_π_val eS hgS hfS z a rfl]
  apply congrArg (fun v : L.Z n => (Submodule.Quotient.mk v : L.H n))
  apply Subtype.ext
  exact hab

end GlobalTheory.CechDR.Cx
