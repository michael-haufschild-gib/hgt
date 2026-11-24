import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedCoverGraphTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedOriginGeometry
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveNormalizationReducedFibre
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCompactness

/-! Holomorphic Lefschetz for finite étale correspondences between
integral schemes follows from a projection through the fixed points. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace UpperTheory.Cb
open GlobalTheory.PD GlobalTheory.WH

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {c₁ c₂ : Y ⟶ Z} [IsFinite c₁] [IsFinite c₂] [Etale c₁] [Etale c₂]
  {d : ℕ} [SmoothOfRelativeDimension d s]

private theorem alternatingHodgeTrace_eq_of_projection
    [Smooth s] [SmoothOfRelativeDimension d t] [IsSeparated s]
    [IsDominant c₁] [IsDominant c₂]
    (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t) (hp : IsProjOver s)
    (S : Finset (Y.BaseFieldPointOver k t))
    (hS : ∀ y, y ∈ S ↔ y.hom ≫ c₁ = y.hom ≫ c₂)
    (M : Y.BaseFieldPointOver k t → Matrix (Fin d) (Fin d) k)
    (hM : ∀ y ∈ S, W1.IsTan d h₁ h₂ y (M y) ∧ (1 - M y).det ≠ 0)
    (p : ℕ) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := c₁.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower h₁
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField]
      [IsScalarTower k F Z.functionField] (aFY : Algebra F Y.functionField),
      letI := aFY
      ∀ (_ : IsScalarTower k F Y.functionField) (_ : IsScalarTower F Z.functionField Y.functionField)
        (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens)
        (_ : IsFinCover k Z.functionField x) (_ : IsAffCover s U (rB k Z.functionField x)),
      IsReduced ((rB k Z.functionField x {0}) ⧸ originIdeal k Z.functionField x) →
      (∀ y ∈ S, ∃ hy : (mapBaseFieldPoint h₁ y).hom default ∈ U 0,
        ∀ (j : Fin d) (hη : genericPoint Z ∈ U 0) (a : SectionRing s (U 0)),
          (Z.presheaf.germ (U 0) _ hη).hom a = algebraMap F Z.functionField (x j.succ / x 0) →
            affinePointEval (mapBaseFieldPoint h₁ y) hy a = 0) →
      ∑ q ∈ Finset.range (d + 1), (-1 : k) ^ q *
        LinearMap.trace k _ (hodgeTrace h₁ p q ∘ₗ hodgePullback h₂ p q) =
        ∑ y ∈ S, (1 + (Polynomial.X : Polynomial k) • (M y).map Polynomial.C).det.coeff p /
          (1 - M y).det := by
  classical
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := c₁.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower h₁
  intro F _ _ _ _ algFY
  letI := algFY
  intro towerFY towerFZY
  letI := towerFY
  letI := towerFZY
  intro x U hE hZ hredE hpinZ
  have hff : algebraMap Z.functionField Y.functionField = c₁.functionFieldPullback.hom := rfl
  obtain ⟨hL, hY⟩ := isFinCover_pullback h₁ hff x U hE hZ
  let B := rB k Y.functionField x {0}
  letI : IsReduced ((rB k Z.functionField x {0}) ⧸ originIdeal k Z.functionField x) := hredE
  letI : IsReduced (B ⧸ originIdeal k Y.functionField x) :=
    isReduced_originFibre_of_finiteEtalePullback h₁ hff x U hE hZ hredE
  have hpin (y : Y.BaseFieldPointOver k t) (hy : y.hom ≫ c₁ = y.hom ≫ c₂) :=
    let h := hpinZ y ((hS y).mpr hy)
    originValues_pullback_of_pinning h₁ hff x U hZ hY y h.choose h.choose_spec
  let e := hY.chartPointEquiv {0} (Finset.singleton_nonempty 0)
  let Y₀ (f : OriginFibrePoint k Y.functionField x) : Y.BaseFieldPointOver k t := (e.symm f.1).1
  let j₂ := functionFieldPullbackAlg c₂ h₂
  let Fixed (f : OriginFibrePoint k Y.functionField x) : Prop := IsFix B f.1 j₂ (rB k Z.functionField x {0})
  have hfix (f : OriginFibrePoint k Y.functionField x) :
      Fixed f ↔ (Y₀ f).hom ≫ c₁ = (Y₀ f).hom ≫ c₂ := by
    have h := isFix_normalized_iff h₁ h₂ hff x U hZ hY (Finset.singleton_nonempty 0)
      (Y₀ f) (e.symm f.1).2
    change IsFix B (e (e.symm f.1)) j₂ (rB k Z.functionField x {0}) ↔ _ at h
    rwa [e.apply_symm_apply] at h
  have hM' (f : OriginFibrePoint k Y.functionField x) :
      ∃ A : Matrix (Fin d) (Fin d) k, Fixed f →
        (∀ m, ∃ (c : B) (g : Fin d → B), f.1 c ≠ 0 ∧
          (c : Y.functionField) * j₂ (algebraMap F Z.functionField (x m.succ / x 0)) =
            ∑ l, (g l : Y.functionField) * algebraMap F Y.functionField (x l.succ / x 0) ∧
          ∀ l, f.1 (g l) = f.1 c * A m l) ∧
        (1 - A).det = (1 - M (Y₀ f)).det ∧
        (1 + (Polynomial.X : Polynomial k) • A.map Polynomial.C).det =
          (1 + (Polynomial.X : Polynomial k) • (M (Y₀ f)).map Polynomial.C).det := by
    by_cases hf : Fixed f
    · have hTan := (hM (Y₀ f) ((hS _).mpr ((hfix f).mp hf))).1
      obtain ⟨A, hA⟩ := exists_normalizedOriginRows_matching_tangent h₁ h₂ hff x U hZ hY hL
        f hf (M (Y₀ f)) hTan
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun h => (hf h).elim⟩
  choose A hA using hM'
  have hdet (f : OriginFibrePoint k Y.functionField x) (hf : Fixed f) : (1 - A f).det ≠ 0 :=
    fun h => (hM (Y₀ f) ((hS _).mpr ((hfix f).mp hf))).2 ((hA f hf).2.1.symm.trans h)
  have traceEq := alternatingHodgeTrace_eq_fixedOrigin h₁ h₂ hp x U hE hL hZ hY hpin A
    (fun f hf => (hA f hf).1) hdet p
  let v (y : {y // y ∈ S}) : OriginFibrePoint k Y.functionField x :=
    let h := hpin y.1 ((hS y.1).mp y.2)
    ⟨e ⟨y.1, h.choose⟩, h.choose_spec⟩
  have hv (y : {y // y ∈ S}) : Y₀ (v y) = y.1 :=
    congrArg Subtype.val (e.symm_apply_apply ⟨y.1, (hpin y.1 ((hS y.1).mp y.2)).choose⟩)
  have hYinj : Function.Injective Y₀ := by
    intro a b h
    exact Subtype.ext (e.symm.injective (Subtype.ext h))
  have hvinj : Function.Injective v := by
    intro y z h
    exact Subtype.ext ((hv y).symm.trans ((congrArg Y₀ h).trans (hv z)))
  have hvFixed (y : {y // y ∈ S}) : Fixed (v y) :=
    (hfix _).mpr ((hv y).symm ▸ (hS y.1).mp y.2)
  letI : Finite (OriginFibrePoint k Y.functionField x) := (trace_originFibre hL).1
  letI : Fintype (OriginFibrePoint k Y.functionField x) := Fintype.ofFinite _
  have hset : Finset.univ.filter Fixed = Finset.univ.image v := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hf
      let y : {y // y ∈ S} := ⟨Y₀ f, (hS _).mpr ((hfix f).mp hf)⟩
      exact ⟨y, hYinj (hv y)⟩
    · rintro ⟨y, rfl⟩
      exact hvFixed y
  rw [traceEq, finsum_eq_sum_of_fintype, ← Finset.sum_filter, hset,
    Finset.sum_image (fun _ _ _ _ h => hvinj h), ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y _ => ?_
  have he := (hA (v y) (hvFixed y)).2
  rw [he.1, he.2, hv]

/-- For a transverse finite étale correspondence on an integral
smooth projective scheme, the alternating Hodge trace is the sum
of the local cotangent ratios. -/
theorem holomorphic_lefschetz_finiteEtale_integral
    (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t) (hp : IsProjOver s)
    (S : Finset (Y.BaseFieldPointOver k t))
    (hS : ∀ y, y ∈ S ↔ y.hom ≫ c₁ = y.hom ≫ c₂)
    (M : Y.BaseFieldPointOver k t → Matrix (Fin d) (Fin d) k)
    (hM : ∀ y ∈ S, W1.IsTan d h₁ h₂ y (M y) ∧ (1 - M y).det ≠ 0)
    (p : ℕ) :
    (∀ q, FiniteDimensional k (HodgeCohomology s p q)) ∧
      ∑ q ∈ Finset.range (d + 1), (-1 : k) ^ q *
        LinearMap.trace k _ (hodgeTrace h₁ p q ∘ₗ hodgePullback h₂ p q) =
      ∑ y ∈ S, (1 + (Polynomial.X : Polynomial k) • (M y).map Polynomial.C).det.coeff p /
        (1 - M y).det := by
  classical
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  letI : SmoothOfRelativeDimension d t := h₁ ▸ (by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d c₁ s)
  letI : Z.IsSeparated := hp.isSeparated
  letI : IsSeparated s := inferInstance
  letI : IsDominant c₁ := isDominant_of_etale c₁
  letI : IsDominant c₂ := isDominant_of_etale c₂
  refine ⟨fun q => hodgeCohomology_finite_of_projective s hp p q, ?_⟩
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := c₁.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower h₁
  obtain ⟨F, x, U, hE, hZ, hredE, hpinZ⟩ :=
    exists_finiteCover_projSpace_reduced_fibre_origin d hp (S.image (mapBaseFieldPoint h₁))
  letI algFY : Algebra F Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap F Z.functionField)).toAlgebra
  have towerFZY : IsScalarTower F Z.functionField Y.functionField := .of_algebraMap_eq fun _ => rfl
  have towerFY : IsScalarTower k F Y.functionField := .of_algebraMap_eq fun a =>
    (IsScalarTower.algebraMap_apply k Z.functionField Y.functionField a).trans
      (congrArg (algebraMap Z.functionField Y.functionField) (IsScalarTower.algebraMap_apply k F Z.functionField a))
  exact alternatingHodgeTrace_eq_of_projection h₁ h₂ hp S hS M hM p
    (F := F) algFY towerFY towerFZY x U hE hZ hredE
    (fun y hy => hpinZ _ (Finset.mem_image_of_mem _ hy))

end GlobalTheory.SchemeCohomology
