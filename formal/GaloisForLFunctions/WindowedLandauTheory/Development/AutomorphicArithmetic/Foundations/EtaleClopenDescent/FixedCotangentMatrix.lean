import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalPointCotangent

/-! A matrix specified by the values of affine differentials
represents the cotangent action on the fixed-point stalk. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open scoped TensorProduct
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.W1

variable {k : Type} [Field k] {Y Z : Scheme.{0}}
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {c₁ c₂ : Y ⟶ Z}

/-- At the evaluated cotangent fibre, the first family gives coordinate
vectors and the second family gives the rows of the matrix. -/
abbrev HasCotangentRows {A : Type} [CommRing A] [Algebra k A] {d : ℕ} (ε : A →ₐ[k] k)
    (u v : Fin d → A) (M : Matrix (Fin d) (Fin d) k) : Prop :=
  ∃ φ : Ω[A⁄k] →ₗ[k] (Fin d → k),
    (∀ (b : A) ω, φ (b • ω) = ε b • φ ω) ∧
    (∀ l, φ (D k A (u l)) = Pi.single l 1) ∧
    (∀ m, φ (D k A (v m)) = fun l => M m l) ∧
    ∀ ω, φ ω = 0 → ∃ (m : ℕ) (b : Fin m → A) (w : Fin m → Ω[A⁄k]),
      (∀ j, ε (b j) = 0) ∧ ω = ∑ j, b j • w j

/-- Affine parameters for the first pullback identify the cotangent
fibre with coordinates, and the second pullback has the given rows. -/
def IsTan (d : ℕ) (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t)
    (y : Y.BaseFieldPointOver k t) (M : Matrix (Fin d) (Fin d) k) : Prop :=
  ∃ (U : Z.Opens) (V : Y.Opens) (hV₁ : V ≤ c₁ ⁻¹ᵁ U) (hV₂ : V ≤ c₂ ⁻¹ᵁ U)
    (a : Fin d → SectionRing s U) (hy : y.hom default ∈ V), IsAffineOpen U ∧ IsAffineOpen V ∧
      HasCotangentRows (affinePointEval y hy)
        (fun l => sectionRes t (homOfLE hV₁) (sectionPullback h₁ U (a l)))
        (fun l => sectionRes t (homOfLE hV₂) (sectionPullback h₂ U (a l))) M

private theorem exists_cotangentFibreEquiv_of_eval {A : Type} [CommRing A] [Algebra k A]
    (ε : A →ₐ[k] k) {d : ℕ} (φ : Ω[A⁄k] →ₗ[k] (Fin d → k))
    (hφ : ∀ b : A, ∀ ω, φ (b • ω) = ε b • φ ω)
    (hsurj : Function.Surjective φ)
    (hker : ∀ ω, φ ω = 0 → ∃ (m : ℕ) (b : Fin m → A) (v : Fin m → Ω[A⁄k]),
      (∀ j, ε (b j) = 0) ∧ ω = ∑ j, b j • v j) :
    ∃ e : CotangentFibre ε ≃ₗ[k] (Fin d → k), ∀ a, e (cotangentFibreD ε a) = φ (D k A a) := by
  letI : Algebra A k := ε.toRingHom.toAlgebra
  letI : IsScalarTower k A k := .of_algebraMap_eq fun c => (ε.commutes c).symm
  let φ₀ : Ω[A⁄k] →ₗ[A] (Fin d → k) :=
    ⟨⟨φ, φ.map_add⟩, hφ⟩
  let f : k →ₗ[k] (Ω[A⁄k] →ₗ[A] (Fin d → k)) := LinearMap.id.smulRight φ₀
  let ψ : CotangentFibre ε →ₗ[k] (Fin d → k) := TensorProduct.AlgebraTensorModule.lift f
  have hψ (ω : Ω[A⁄k]) : ψ ((1 : k) ⊗ₜ[A] ω) = φ ω := by
    change TensorProduct.AlgebraTensorModule.lift f ((1 : k) ⊗ₜ[A] ω) = _
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    exact one_smul k (φ ω)
  have hrep (u : CotangentFibre ε) : ∃ ω : Ω[A⁄k], (1 : k) ⊗ₜ[A] ω = u := by
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
    | tmul c ω =>
      refine ⟨algebraMap k A c • ω, ?_⟩
      rw [← TensorProduct.smul_tmul]
      change (ε (algebraMap k A c) * 1) ⊗ₜ[A] ω = _
      simp
    | add _ _ h₁ h₂ =>
      obtain ⟨a, rfl⟩ := h₁
      obtain ⟨b, rfl⟩ := h₂
      exact ⟨a + b, TensorProduct.tmul_add (1 : k) a b⟩
  have hinj : Function.Injective ψ := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro u hu
    obtain ⟨ω, rfl⟩ := hrep u
    have hω := LinearMap.mem_ker.mp hu
    rw [hψ] at hω
    obtain ⟨m, b, v, hb, rfl⟩ := hker _ hω
    apply (Submodule.mem_bot k).mpr
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← TensorProduct.smul_tmul]
    change (ε (b j) * 1) ⊗ₜ[A] v j = _
    rw [hb j, zero_mul, TensorProduct.zero_tmul]
  have hsurj' : Function.Surjective ψ := by
    intro v
    obtain ⟨ω, rfl⟩ := hsurj v
    exact ⟨(1 : k) ⊗ₜ[A] ω, hψ ω⟩
  exact ⟨LinearEquiv.ofBijective ψ ⟨hinj, hsurj'⟩, fun a => hψ (D k A a)⟩

variable [IsFinite c₁] [IsFinite c₂] [Etale c₁] [Etale c₂]

/-- The matrix from the affine differential data describes the fixed
cotangent action in a basis of the stalk cotangent fibre. -/
theorem IsTan.exists_cotangentBasis
    {d : ℕ} {h₁ : c₁ ≫ s = t} {h₂ : c₂ ≫ s = t}
    {y : Y.BaseFieldPointOver k t} {M : Matrix (Fin d) (Fin d) k} (hM : IsTan d h₁ h₂ y M)
    (hfix : mapBaseFieldPoint h₁ y = mapBaseFieldPoint h₂ y)
    {W : Z.Opens} (hW : IsAffineOpen W) (hy₁ : y.hom default ∈ c₁ ⁻¹ᵁ W)
    (hy₂ : y.hom default ∈ c₂ ⁻¹ᵁ W) :
    ∃ b : Module.Basis (Fin d) k (CotangentAt y), ∀ m,
      fixedCotangentEquiv h₁ h₂ y hfix hW hy₁ hy₂ (b m) = ∑ l, M m l • b l := by
  classical
  obtain ⟨U, V, hV₁, hV₂, a, hy, hU, hV, φ, hφ, h₁a, h₂a, hker⟩ := hM
  let A := SectionRing t V
  let l (j : Fin d) : A := sectionRes t (homOfLE hV₁) (sectionPullback h₁ U (a j))
  let r (j : Fin d) : A := sectionRes t (homOfLE hV₂) (sectionPullback h₂ U (a j))
  let β := Pi.basisFun k (Fin d)
  have hsurj : Function.Surjective φ := by
    apply LinearMap.range_eq_top.mp
    refine le_antisymm le_top ?_
    rw [← β.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨D k A (l j), (h₁a j).trans (Pi.basisFun_apply k (Fin d) j).symm⟩
  let ε := affinePointEval y hy
  obtain ⟨E, hE⟩ := exists_cotangentFibreEquiv_of_eval ε φ hφ hsurj hker
  let C := chartCotangentEquiv y hV hy
  let F := C.symm.trans E
  let b := β.map F.symm
  have hb (j : Fin d) : F (b j) = Pi.single j 1 := by
    rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Pi.basisFun_apply k (Fin d) j
  have hleft (j : Fin d) :
      b j = cotangentAtD y (sectionGermAlg t (hV₁ hy) (sectionPullback h₁ U (a j))) := by
    have hg := Y.presheaf.germ_res_apply (homOfLE hV₁) (y.hom default) hy (sectionPullback h₁ U (a j))
    change sectionGermAlg t hy (l j) =
      sectionGermAlg t (hV₁ hy) (sectionPullback h₁ U (a j)) at hg
    rw [← hg, ← chartCotangentEquiv_D y hV hy]
    apply F.injective
    rw [hb]
    change Pi.single j 1 = E (C.symm (C (cotangentFibreD ε (l j))))
    rw [LinearEquiv.symm_apply_apply, hE]
    exact (h₁a j).symm
  refine ⟨b, fun m => ?_⟩
  have hf : fixedCotangentEquiv h₁ h₂ y hfix hW hy₁ hy₂ =
      fixedCotangentEquiv h₁ h₂ y hfix hU (hV₁ hy) (hV₂ hy) := rfl
  rw [hf, hleft, fixedCotangentEquiv_D]
  have hg := Y.presheaf.germ_res_apply (homOfLE hV₂) (y.hom default) hy (sectionPullback h₂ U (a m))
  change sectionGermAlg t hy (r m) =
    sectionGermAlg t (hV₂ hy) (sectionPullback h₂ U (a m)) at hg
  rw [← hg, ← chartCotangentEquiv_D y hV hy]
  apply F.injective
  have hright : F (C (cotangentFibreD ε (r m))) = fun j => M m j := by
    change E (C.symm (C (cotangentFibreD ε (r m)))) = _
    rw [LinearEquiv.symm_apply_apply, hE]
    exact h₂a m
  change F (C (cotangentFibreD ε (r m))) = _
  simp only [hright, map_sum, map_smul, hb]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hne
    simp [Pi.single_eq_of_ne hne.symm]
  · simp

end GlobalTheory.W1
