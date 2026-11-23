import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Cotangent fibres at rational points, with their étale pullback
equivalences and bases from regular parameters. -/

noncomputable section

open KaehlerDifferential TensorProduct

namespace GlobalTheory.SchemeCohomology

variable {k A B : Type} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The fibre of the module of differentials at a rational point. -/
abbrev CotangentFibre (e : A →ₐ[k] k) : Type :=
  letI := e.toRingHom.toAlgebra
  k ⊗[A] Ω[A⁄k]

/-- The differential of a function evaluated at the rational point. -/
def cotangentFibreD (e : A →ₐ[k] k) (a : A) : CotangentFibre e :=
  letI := e.toRingHom.toAlgebra
  (1 : k) ⊗ₜ[A] D k A a

theorem cotangentFibreD_mul (e : A →ₐ[k] k) (a b : A) :
    cotangentFibreD e (a * b) = e a • cotangentFibreD e b + e b • cotangentFibreD e a := by
  letI : Algebra A k := e.toRingHom.toAlgebra
  have h (a : A) (ω : Ω[A⁄k]) :
      (1 : k) ⊗ₜ[A] (a • ω) = e a • ((1 : k) ⊗ₜ[A] ω) := by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
  simp only [cotangentFibreD, Derivation.leibniz, TensorProduct.tmul_add, h]

theorem cotangentFibreD_sum (e : A →ₐ[k] k) {ι : Type} (s : Finset ι) (a : ι → A) :
    cotangentFibreD e (∑ i ∈ s, a i) = ∑ i ∈ s, cotangentFibreD e (a i) := by
  letI : Algebra A k := e.toRingHom.toAlgebra
  simp only [cotangentFibreD, map_sum, TensorProduct.tmul_sum]

theorem exists_cotangentFibreD_eq (e : A →ₐ[k] k) (v : CotangentFibre e) :
    ∃ a : A, e a = 0 ∧ cotangentFibreD e a = v := by
  letI : Algebra A k := e.toRingHom.toAlgebra
  letI : IsScalarTower k A k := .of_algebraMap_eq fun c => (e.commutes c).symm
  have he : Function.Surjective (algebraMap A k) := fun c => ⟨algebraMap k A c, e.commutes c⟩
  obtain ⟨z, hz⟩ := (exact_kerCotangentToTensor_mapBaseChange k A k he v).mp (Subsingleton.elim _ _)
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ z
  exact ⟨a, a.2, (kerCotangentToTensor_toCotangent k A k a).symm.trans hz⟩

/-- A cleared equation between functions vanishing at the point becomes a
linear relation after passing to the cotangent fibre. -/
theorem smul_cotangentFibreD_eq_sum (e : A →ₐ[k] k) {d : ℕ} (t g : Fin d → A)
    (a c : A) (ha : e a = 0) (ht : ∀ j, e (t j) = 0)
    (h : c * a = ∑ j, g j * t j) :
    e c • cotangentFibreD e a = ∑ j, e (g j) • cotangentFibreD e (t j) := by
  simpa only [cotangentFibreD_mul, cotangentFibreD_sum, ha, ht, zero_smul, add_zero]
    using congrArg (cotangentFibreD e) h

/-- Parameters generating the maximal ideal in the local ring give a
basis of the cotangent fibre when their number equals its dimension. -/
theorem exists_basis_of_cotangentFibre_parameters (e : A →ₐ[k] k) {d : ℕ} (t : Fin d → A)
    (ht : ∀ j, e (t j) = 0)
    (hd : Module.finrank k (CotangentFibre e) = d)
    (h : ∀ a, e a = 0 → ∃ (c : A) (g : Fin d → A),
      e c ≠ 0 ∧ c * a = ∑ j, g j * t j) :
    ∃ b : Module.Basis (Fin d) k (CotangentFibre e), ∀ j, b j = cotangentFibreD e (t j) := by
  let v (j : Fin d) := cotangentFibreD e (t j)
  have hspan : ⊤ ≤ Submodule.span k (Set.range v) := by
    intro ω _
    obtain ⟨a, ha, rfl⟩ := exists_cotangentFibreD_eq e ω
    obtain ⟨c, g, hc, hg⟩ := h a ha
    have hdg := smul_cotangentFibreD_eq_sum e t g a c ha ht hg
    have hm : e c • cotangentFibreD e a ∈ Submodule.span k (Set.range v) := by
      rw [hdg]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
    have hm' := Submodule.smul_mem _ (e c)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hm'
  have hl := linearIndependent_of_top_le_span_of_card_eq_finrank hspan
    ((Fintype.card_fin d).trans hd.symm)
  exact ⟨Module.Basis.mk hl hspan, Module.Basis.mk_apply hl hspan⟩

/-- Étale pullback is invertible on the cotangent fibres at compatible
rational points. -/
def cotangentFibreEtaleEquiv (e : A →ₐ[k] k) (ε : B →ₐ[k] k) (g : A →ₐ[k] B)
    (he : ε.comp g = e) (hg : g.toRingHom.FormallyEtale) :
    CotangentFibre e ≃ₗ[k] CotangentFibre ε := by
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : Algebra A k := e.toRingHom.toAlgebra
  letI : Algebra B k := ε.toRingHom.toAlgebra
  letI : IsScalarTower k A B := .of_algebraMap_eq fun c => (g.commutes c).symm
  letI : IsScalarTower A B k := .of_algebraMap_eq fun a =>
    (AlgHom.congr_fun he a).symm
  letI : Algebra.FormallyEtale A B := hg
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k Ω[A⁄k]).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl k k)
      (tensorKaehlerEquivOfFormallyEtale k A B))

theorem cotangentFibreEtaleEquiv_D (e : A →ₐ[k] k) (ε : B →ₐ[k] k) (g : A →ₐ[k] B)
    (he : ε.comp g = e) (hg : g.toRingHom.FormallyEtale) (a : A) :
    cotangentFibreEtaleEquiv e ε g he hg (cotangentFibreD e a) = cotangentFibreD ε (g a) := by
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : Algebra.FormallyEtale A B := hg
  have h : tensorKaehlerEquivOfFormallyEtale k A B ((1 : B) ⊗ₜ[A] D k A a) =
      D k B (g a) :=
    (LinearEquiv.eq_symm_apply _).mp
      (tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap k A B a).symm
  simp only [cotangentFibreEtaleEquiv, cotangentFibreD, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h]

end GlobalTheory.SchemeCohomology
