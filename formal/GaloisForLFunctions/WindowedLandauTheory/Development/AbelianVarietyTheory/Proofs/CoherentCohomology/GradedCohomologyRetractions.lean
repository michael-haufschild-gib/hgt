import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! Split representatives identify homology with a complement to boundaries.
The tensor homotopy and orthogonal projection ranges give corresponding splits
in the tensor total complex. -/

open CategoryTheory Limits TensorProduct

universe v u

namespace GlobalTheory

section Homology

variable {R : Type u} [Ring R]

/-- A retraction of the cycles with kernel equal to the boundaries computes homology. -/
theorem nonempty_homology_equiv_of_retract (S : ShortComplex (ModuleCat.{v} R))
    {W : Type*} [AddCommGroup W] [Module R W] (I : W →ₗ[R] S.X₂) (Q : S.X₂ →ₗ[R] W)
    (hI : ∀ w, S.g.hom (I w) = 0) (hQ : ∀ y, Q (S.f.hom y) = 0) (hQI : ∀ w, Q (I w) = w)
    (hex : ∀ x, S.g.hom x = 0 → Q x = 0 → ∃ y, S.f.hom y = x) :
    Nonempty (S.homology ≃ₗ[R] W) := by
  let q : LinearMap.ker S.g.hom →ₗ[R] W := Q ∘ₗ (LinearMap.ker S.g.hom).subtype
  have hs : Function.Surjective q := fun w => ⟨⟨I w, hI w⟩, hQI w⟩
  have hk : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hQ y
    · intro hx
      obtain ⟨y, hy⟩ := hex x.1 x.2 hx
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨S.moduleCatHomologyIso.toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    q.quotKerEquivOfSurjective hs⟩

end Homology

section Tensor

variable {K : Type u} [CommRing K] {V V' : Type v}
  [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

/-- The two contractions combine with the degree sign to contract the tensor differential. -/
theorem tensor_homotopy {D e h ε : Module.End K V} {D' e' h' : Module.End K V'}
    (hh : 1 - e = D * h + h * D) (hDe : D * e = 0) (heD : e * D = 0) (hDε : D * ε = -(ε * D))
    (hεe : ε * e = e * ε) (hεh : ε * h = -(h * ε)) (hεε : ε * ε = 1)
    (hh' : 1 - e' = D' * h' + h' * D') :
    (1 : Module.End K (V ⊗[K] V')) - TensorProduct.map e e' =
      (TensorProduct.map D 1 + TensorProduct.map ε D') *
          (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') +
        (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') *
          (TensorProduct.map D 1 + TensorProduct.map ε D') := by
  have a1 : D * (ε * e) = 0 := by rw [← mul_assoc, hDε, neg_mul, mul_assoc, hDe]; simp
  have a2 : ε * (ε * e) = e := by rw [← mul_assoc, hεε, one_mul]
  have a3 : ε * e * D = 0 := by rw [mul_assoc, heD, mul_zero]
  have a4 : ε * e * ε = e := by rw [mul_assoc, ← hεe, a2]
  have a5 : D * h = 1 - e - h * D := by rw [hh]; abel
  have a6 : D' * h' = 1 - e' - h' * D' := by rw [hh']; abel
  simp only [mul_add, add_mul, ← TensorProduct.map_mul, a1, a2, a3, a4, a5, a6, hεh]
  refine TensorProduct.ext' fun x y => ?_
  simp only [LinearMap.sub_apply, LinearMap.add_apply, TensorProduct.map_tmul, Module.End.one_apply,
    LinearMap.zero_apply, LinearMap.neg_apply, mul_one, one_mul, sub_tmul, tmul_sub, neg_tmul,
    zero_tmul]
  abel

private theorem rangeRestrict_comp_subtype_of_orthogonal {f : ℕ → Module.End K V}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0) (p : ℕ) :
    (f p).rangeRestrict ∘ₗ (LinearMap.range (f p)).subtype = LinearMap.id := by
  refine LinearMap.ext ?_
  rintro ⟨_, x, rfl⟩
  have := hf p p
  rw [if_pos rfl] at this
  exact Subtype.ext congr($this x)

private theorem rangeRestrict_comp_subtype_of_orthogonal_of_ne {f : ℕ → Module.End K V}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0) {p q : ℕ} (h : p ≠ q) :
    (f p).rangeRestrict ∘ₗ (LinearMap.range (f q)).subtype = 0 := by
  refine LinearMap.ext ?_
  rintro ⟨_, x, rfl⟩
  have := hf p q
  rw [if_neg h] at this
  exact Subtype.ext congr($this x)

/-- Orthogonal projection ranges give a split product of tensor summands. -/
theorem exists_retraction_tensor_ranges {f : ℕ → Module.End K V} {g : ℕ → Module.End K V'}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0)
    (hg : ∀ p q, g p * g q = if p = q then g p else 0) (S : Finset (ℕ × ℕ)) :
    ∃ (I : (∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)) →ₗ[K] V ⊗[K] V')
      (Q : V ⊗[K] V' →ₗ[K] ∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)),
      (∀ z, I (Q z) = ∑ x ∈ S, TensorProduct.map (f x.1) (g x.2) z) ∧ ∀ w, Q (I w) = w := by
  refine ⟨∑ x : S, TensorProduct.map (LinearMap.range (f x.1.1)).subtype
      (LinearMap.range (g x.1.2)).subtype ∘ₗ LinearMap.proj x,
    LinearMap.pi fun x => TensorProduct.map (f x.1.1).rangeRestrict (g x.1.2).rangeRestrict,
    fun z => ?_, fun w => funext fun x => ?_⟩
  · rw [LinearMap.sum_apply, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply]
    rw [TensorProduct.map_map]
    rfl
  · rw [LinearMap.sum_apply, LinearMap.pi_apply, map_sum, Finset.sum_eq_single x]
    · simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [TensorProduct.map_map, rangeRestrict_comp_subtype_of_orthogonal hf,
        rangeRestrict_comp_subtype_of_orthogonal hg, TensorProduct.map_id, LinearMap.id_apply]
    · intro y _ hy
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [TensorProduct.map_map]
      by_cases h : x.1.1 = y.1.1
      · have h' : x.1.2 ≠ y.1.2 := fun h' => hy (Subtype.ext (Prod.ext h h')).symm
        rw [rangeRestrict_comp_subtype_of_orthogonal_of_ne hg h', TensorProduct.map_zero_right,
          LinearMap.zero_apply]
      · rw [rangeRestrict_comp_subtype_of_orthogonal_of_ne hf h, TensorProduct.map_zero_left,
          LinearMap.zero_apply]
    · simp

end Tensor

end GlobalTheory
