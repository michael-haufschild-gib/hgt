import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! At a rational point of a smooth affine chart, sections lifting a
cotangent basis generate its maximal ideal modulo its square. -/

noncomputable section

open AlgebraicGeometry CategoryTheory KaehlerDifferential TensorProduct

namespace GlobalTheory.SchemeCohomology

private theorem fibre_basis_of_standardSmooth {K A : Type} [Field K] [CommRing A] [Algebra K A]
    (ε : A →ₐ[K] K) (d : ℕ) (t : A) (ht : ε t ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away t)] :
    letI := ε.toRingHom.toAlgebra
    Nonempty (Module.Basis (Fin d) K (K ⊗[A] Ω[A⁄K])) := by
  letI : Algebra A K := ε.toRingHom.toAlgebra
  letI : IsScalarTower K A K := IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  let T := Localization.Away t
  let ε' : T →+* K := IsLocalization.Away.lift t (isUnit_iff_ne_zero.mpr ht)
  letI : Algebra T K := ε'.toAlgebra
  letI : IsScalarTower A T K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq t (isUnit_iff_ne_zero.mpr ht) a).symm
  letI : Nontrivial T := ε'.domain_nontrivial
  letI : Algebra.FormallyEtale A T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  letI : Algebra.IsStandardSmooth K T := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := T) d
  letI : Module.Finite T Ω[T⁄K] := Module.finite_of_rank_eq_nat hr
  let b := Module.finBasisOfFinrankEq T Ω[T⁄K] (Module.finrank_eq_of_rank_eq hr)
  let c : Module.Basis (Fin d) K (K ⊗[T] Ω[T⁄K]) := b.baseChange K
  let E : K ⊗[T] (T ⊗[A] Ω[A⁄K]) ≃ₗ[K] K ⊗[T] Ω[T⁄K] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (tensorKaehlerEquivOfFormallyEtale K A T)
  exact ⟨(c.map E.symm).map (TensorProduct.AlgebraTensorModule.cancelBaseChange A T K K Ω[A⁄K])⟩

private theorem lift_fibre_basis {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.FormallySmooth K A] (ε : A →ₐ[K] K) (d : ℕ)
    (hb : letI := ε.toRingHom.toAlgebra
      Nonempty (Module.Basis (Fin d) K (K ⊗[A] Ω[A⁄K]))) :
    ∃ g : Fin d → A, (∀ j, ε (g j) = 0) ∧
      (∀ a : A, ε a = 0 → ∃ c : Fin d → K, a - ∑ j, c j • g j ∈ RingHom.ker ε.toRingHom ^ 2) := by
  letI : Algebra A K := ε.toRingHom.toAlgebra
  letI : IsScalarTower K A K := IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  obtain ⟨b⟩ := hb
  have hs : Function.Surjective (algebraMap A K) := fun c => ⟨algebraMap K A c, ε.commutes c⟩
  have ht (c : K) (w : Ω[A⁄K]) : (1 : K) ⊗ₜ[A] (c • w) = c • ((1 : K) ⊗ₜ[A] w) := by
    rw [← algebraMap_smul A c w, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    exact ε.commutes c
  let δ : A →ₗ[K] K ⊗[A] Ω[A⁄K] :=
    { toFun := fun a => (1 : K) ⊗ₜ[A] D K A a
      map_add' := fun a b => by rw [map_add, TensorProduct.tmul_add]
      map_smul' := fun c a => by rw [(D K A).map_smul c a, ht]; rfl }
  let m := RingHom.ker (algebraMap A K)
  let θ := kerCotangentToTensor K A K
  have hδ (x : m) : δ x = θ (m.toCotangent x) := (kerCotangentToTensor_toCotangent K A K x).symm
  obtain ⟨L, hL⟩ := (Algebra.FormallySmooth.iff_split_injection (R := K) (P := A) (A := K) hs).mp
    (inferInstance : Algebra.FormallySmooth K K)
  have hinj : Function.Injective θ :=
    Function.LeftInverse.injective (g := L) fun x => LinearMap.congr_fun hL x
  have hsurj : ∀ v, ∃ x : m, δ x = v := by
    intro v
    obtain ⟨z, hz⟩ := (exact_kerCotangentToTensor_mapBaseChange K A K hs v).mp (Subsingleton.elim _ _)
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ z
    exact ⟨x, (hδ x).trans hz⟩
  have hker (x : m) (hx : δ x = 0) : (x : A) ∈ m ^ 2 := by
    have hx' : θ (m.toCotangent x) = θ 0 := (hδ x).symm.trans (hx.trans (map_zero θ).symm)
    exact (Ideal.toCotangent_eq_zero _ _).mp (hinj hx')
  choose g hg using fun j => hsurj (b j)
  have hsum (c : Fin d → K) : ∑ j, c j • (g j : A) ∈ m :=
    Ideal.sum_mem _ fun j _ => by rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (g j).2
  have hδg (c : Fin d → K) : δ (∑ j, c j • (g j : A)) = ∑ j, c j • b j := by
    rw [map_sum]; simp only [map_smul, hg]
  refine ⟨fun j => g j, fun j => (g j).2, ?_⟩
  intro a ha
  let c (j : Fin d) := b.repr (δ a) j
  have h : a - ∑ j, c j • (g j : A) ∈ m := Ideal.sub_mem _ ha (hsum c)
  refine ⟨c, hker ⟨_, h⟩ ?_⟩
  change δ (a - _) = 0
  rw [map_sub, hδg, b.sum_repr, sub_self]

/-- The cotangent fibre of a smooth affine chart at a rational point has
dimension equal to the relative dimension. -/
theorem nonempty_affineCotangentFibreBasis {K : Type} [Field K] {X : Scheme.{0}}
    (s : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d s]
    {U : X.Opens} (hU : IsAffineOpen U) (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ U) :
    let A := SectionRing s U
    let ε := affinePointEval y hy
    letI : Algebra A K := ε.toRingHom.toAlgebra
    Nonempty (Module.Basis (Fin d) K (K ⊗[A] Ω[A⁄K])) := by
  intro A ε
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have ht : U ≤ s ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := le_top
  obtain ⟨S, hS, hstd⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) s inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ht
  obtain ⟨a, ha, hna⟩ : ∃ a ∈ S, ε a ≠ 0 := by
    by_contra! h
    have hi : Ideal.span S ≤ RingHom.ker ε.toRingHom := Ideal.span_le.mpr h
    have h1 : ε (1 : A) = 0 := hi (hS.symm ▸ Submodule.mem_top)
    exact one_ne_zero ((map_one ε).symm.trans h1)
  have he := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _ e (hstd a ha)
  let a' : A := a
  let T := Localization.Away a'
  have hT : (algebraMap K T).IsStandardSmoothOfRelativeDimension d := he
  letI : Algebra.IsStandardSmoothOfRelativeDimension d K T :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mp hT
  exact fibre_basis_of_standardSmooth ε d a' hna

/-- The maximal ideal at a rational point of a smooth affine open of
relative dimension d has d generators modulo its square. -/
theorem exists_rational_cotangent_basis {K : Type} [Field K] {X : Scheme.{0}}
    (s : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d s]
    {U : X.Opens} (hU : IsAffineOpen U) (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ U) :
    let A := SectionRing s U
    let ε := affinePointEval y hy
    ∃ g : Fin d → A, (∀ j, ε (g j) = 0) ∧
      (∀ a : A, ε a = 0 → ∃ c : Fin d → K, a - ∑ j, c j • g j ∈ RingHom.ker ε.toRingHom ^ 2) := by
  intro A ε
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have ht : U ≤ s ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := le_top
  have hsmooth : (algebraMap K A).Smooth :=
    RingHom.Smooth.respectsIso.right _ e (s.smooth_appLE (isAffineOpen_top _) hU ht)
  letI : Algebra.Smooth K A := RingHom.smooth_algebraMap.mp hsmooth
  exact lift_fibre_basis ε d (nonempty_affineCotangentFibreBasis s d hU y hy)

end GlobalTheory.SchemeCohomology
