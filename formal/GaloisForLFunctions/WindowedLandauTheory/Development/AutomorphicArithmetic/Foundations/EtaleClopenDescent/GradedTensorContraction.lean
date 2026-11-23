import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-! The tensor product of split graded complexes retracts onto
tensors of their cocycles. -/

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CechDR

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A cochain complex with finitely many orthogonal degree projections. -/
structure FiniteGradedComplex (k V : Type) [Field k] [AddCommGroup V] [Module k V] where
  d : V →ₗ[k] V
  π : ℕ → V →ₗ[k] V
  σ : V →ₗ[k] V
  N : ℕ
  dd : ∀ a, d (d a) = 0
  idem : ∀ c a, π c (π c a) = π c a
  orth : ∀ c c' a, c ≠ c' → π c (π c' a) = 0
  sum : ∀ a, ∑ c ∈ Finset.range N, π c a = a
  zero : ∀ a, π 0 a = 0
  dπ : ∀ c a, d (π c a) = π (c + 1) (d a)
  σπ : ∀ c a, σ (π c a) = ((-1 : ℤ) ^ c) • π c a

private theorem exists_partialInverse (f : V →ₗ[k] V) : ∃ g : V →ₗ[k] V, ∀ a, f (g (f a)) = f a := by
  obtain ⟨g', hg'⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g'
  refine ⟨g, fun a => ?_⟩
  have h1 : g (f a) = g' (f.rangeRestrict a) := by
    have := LinearMap.congr_fun hg (f.rangeRestrict a)
    simpa using this
  rw [h1]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hg' (f.rangeRestrict a))
  simpa using h2

namespace FiniteGradedComplex

variable (G : FiniteGradedComplex k V)

theorem big {c : ℕ} (hc : G.N ≤ c) (a : V) : G.π c a = 0 := by
  rw [← G.sum a, map_sum]
  refine Finset.sum_eq_zero fun c' hc' => G.orth _ _ _ ?_
  have := Finset.mem_range.1 hc'
  omega

theorem ext' {U : Type} [AddCommGroup U] [Module k U] {X Y : V →ₗ[k] U}
    (h : ∀ c a, X (G.π c a) = Y (G.π c a)) (a : V) : X a = Y a := by
  rw [← G.sum a, map_sum, map_sum]
  exact Finset.sum_congr rfl fun c _ => h c a

theorem σσ (a : V) : G.σ (G.σ a) = a := by
  refine G.ext' (X := G.σ ∘ₗ G.σ) (Y := LinearMap.id) (fun c a => ?_) a
  simp only [LinearMap.comp_apply, LinearMap.id_apply, G.σπ, map_zsmul, smul_smul]
  rw [← mul_pow]
  simp

theorem σd (a : V) : G.σ (G.d a) = - G.d (G.σ a) := by
  refine G.ext' (X := G.σ ∘ₗ G.d) (Y := -(G.d ∘ₗ G.σ)) (fun c a => ?_) a
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, G.σπ, map_zsmul, G.dπ, pow_succ]
  simp

/-- Split the differential degree by degree to obtain a projection to cocycles
and its chain homotopy to the identity. -/
theorem exists_contraction : ∃ e h : V →ₗ[k] V,
    (∀ a, G.d (e a) = 0) ∧ (∀ a, e (G.d a) = 0) ∧ (∀ a, G.d (h a) + h (G.d a) + e a = a) ∧
    (∀ c a, h (G.π (c + 1) a) = G.π c (h a)) ∧ (∀ c a, e (G.π c a) = G.π c (e a)) := by
  obtain ⟨g, hg⟩ := exists_partialInverse G.d
  let h : V →ₗ[k] V := ∑ c ∈ Finset.range G.N, G.π c ∘ₗ g ∘ₗ G.π (c + 1)
  have happ : ∀ a, h a = ∑ c ∈ Finset.range G.N, G.π c (g (G.π (c + 1) a)) := fun a => by
    simp [h, LinearMap.sum_apply]
  have hπ : ∀ c a, h (G.π (c + 1) a) = G.π c (h a) := by
    intro c a
    rw [happ, happ, map_sum]
    by_cases hc : c < G.N
    · rw [Finset.sum_eq_single c, Finset.sum_eq_single c]
      · rw [G.idem, G.idem]
      · intro b _ hb
        rw [G.orth _ _ _ hb.symm]
      · intro h'; exact absurd (Finset.mem_range.2 hc) h'
      · intro b _ hb
        rw [G.orth (b + 1) (c + 1) _ (by omega)]
        simp
      · intro h'; exact absurd (Finset.mem_range.2 hc) h'
    · have : G.N ≤ c := by omega
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro b _
        rw [G.big this]
      · intro b hb
        have := Finset.mem_range.1 hb
        rw [G.orth (b + 1) (c + 1) _ (by omega)]
        simp
  have hdhd : ∀ a, G.d (h (G.d a)) = G.d a := by
    intro a
    rw [happ, map_sum]
    conv_rhs => rw [← G.sum a, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← G.dπ, G.dπ c (g _), hg]
    rw [G.dπ c a, G.idem]
  let e : V →ₗ[k] V := LinearMap.id - G.d ∘ₗ h - h ∘ₗ G.d
  have eapp : ∀ a, e a = a - G.d (h a) - h (G.d a) := fun a => rfl
  refine ⟨e, h, ?_, ?_, ?_, hπ, ?_⟩
  · intro a
    rw [eapp]
    simp [G.dd, hdhd]
  · intro a
    rw [eapp]
    simp [G.dd, hdhd]
  · intro a
    rw [eapp]
    abel
  · intro c a
    rcases c with _ | c
    · rw [G.zero, G.zero]
      simp
    · rw [eapp, eapp, map_sub, map_sub, hπ c a, G.dπ c, G.dπ (c + 1) a, hπ (c + 1)]

end FiniteGradedComplex

/-- Tensor differential with the parity sign from the left factor. -/
def tensorDifferential (G : FiniteGradedComplex k V) (G' : FiniteGradedComplex k W) : V ⊗[k] W →ₗ[k] V ⊗[k] W :=
  TensorProduct.map G.d LinearMap.id + TensorProduct.map G.σ G'.d

/-- Homogeneous tensors with the specified total degree. -/
def tensorDegree (G : FiniteGradedComplex k V) (G' : FiniteGradedComplex k W) (n : ℤ) : Submodule k (V ⊗[k] W) :=
  Submodule.span k {x | ∃ (a : V) (b : W) (p q : ℕ), G.π p a = a ∧ G'.π q b = b ∧ ((p + q : ℕ) : ℤ) = n ∧ x = a ⊗ₜ[k] b}

/-- The span of pure tensors of homogeneous cocycles. -/
def tensorCycleSpan (G : FiniteGradedComplex k V) (G' : FiniteGradedComplex k W) (n : ℤ) : Submodule k (V ⊗[k] W) :=
  Submodule.span k {x | ∃ (a : V) (b : W) (p q : ℕ), G.π p a = a ∧ G'.π q b = b ∧ ((p + q : ℕ) : ℤ) = n ∧
    G.d a = 0 ∧ G'.d b = 0 ∧ x = a ⊗ₜ[k] b}

/-- Every homogeneous tensor cocycle is cohomologous to a sum of
tensors of homogeneous cocycles. -/
theorem tensor_kunneth (G : FiniteGradedComplex k V) (G' : FiniteGradedComplex k W) (n : ℤ) (t : V ⊗[k] W) (ht : t ∈ tensorDegree G G' n) (hD : tensorDifferential G G' t = 0) :
    ∃ s ∈ tensorDegree G G' (n - 1), t - tensorDifferential G G' s ∈ tensorCycleSpan G G' n := by
  obtain ⟨e, h, de, ed, deh, hπ, eπ⟩ := G.exists_contraction
  obtain ⟨e', h', de', ed', deh', hπ', eπ'⟩ := G'.exists_contraction
  have hσ : ∀ a, h (G.σ a) = - G.σ (h a) := by
    intro a
    refine G.ext' (X := h ∘ₗ G.σ) (Y := -(G.σ ∘ₗ h)) (fun c a => ?_) a
    rcases c with _ | c
    · simp [G.zero]
    · simp only [LinearMap.comp_apply, LinearMap.neg_apply, G.σπ, map_zsmul, hπ, pow_succ]
      simp
  have eσ : ∀ a, e (G.σ a) = G.σ (e a) := by
    intro a
    refine G.ext' (X := e ∘ₗ G.σ) (Y := G.σ ∘ₗ e) (fun c a => ?_) a
    simp only [LinearMap.comp_apply, G.σπ, map_zsmul, eπ]
  let H : V ⊗[k] W →ₗ[k] V ⊗[k] W := TensorProduct.map h LinearMap.id + TensorProduct.map (G.σ ∘ₗ e) h'
  have key : (tensorDifferential G G') ∘ₗ H + H ∘ₗ (tensorDifferential G G') + TensorProduct.map e e' = LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    have e1 : a ⊗ₜ[k] b = (G.d (h a) + h (G.d a) + e a) ⊗ₜ[k] b := by rw [deh]
    have e2 : e a ⊗ₜ[k] b = e a ⊗ₜ[k] (G'.d (h' b) + h' (G'.d b) + e' b) := by rw [deh']
    have e3 : G.d (G.σ (e a)) = 0 := by
      have := G.σd (e a)
      rw [de, map_zero] at this
      exact neg_eq_zero.1 this.symm
    simp only [H, tensorDifferential, LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, map_add,
      e3, ed, eσ, hσ, G.σσ, map_zero, TensorProduct.zero_tmul, TensorProduct.neg_tmul]
    rw [e1, TensorProduct.add_tmul, TensorProduct.add_tmul, e2, TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel
  have hH : ∀ x ∈ tensorDegree G G' n, H x ∈ tensorDegree G G' (n - 1) := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => H x ∈ tensorDegree G G' (n - 1)) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, b, p, q, hp, hq, hn, rfl⟩
      simp only [H, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply]
      refine add_mem ?_ ?_
      · rcases p with _ | p
        · have : a = 0 := by rw [← hp, G.zero]
          simp [this]
        · have h1 : h a = G.π p (h a) := by rw [← hπ, hp]
          refine Submodule.subset_span ⟨h a, b, p, q, ?_, hq, ?_, rfl⟩
          · exact h1.symm
          · push_cast at hn ⊢
            omega
      · rcases q with _ | q
        · have : b = 0 := by rw [← hq, G'.zero]
          simp [this]
        · have h1 : h' b = G'.π q (h' b) := by rw [← hπ', hq]
          have h2 : e a = G.π p (e a) := by rw [← eπ, hp]
          refine Submodule.subset_span ⟨G.σ (e a), h' b, p, q, ?_, h1.symm, ?_, rfl⟩
          · rw [h2, G.σπ, map_zsmul, G.idem]
          · push_cast at hn ⊢
            omega
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  refine ⟨H t, hH t ht, ?_⟩
  have h3 : t - tensorDifferential G G' (H t) = TensorProduct.map e e' t := by
    have := LinearMap.congr_fun key t
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hD, map_zero, add_zero] at this
    rw [sub_eq_iff_eq_add]
    rw [add_comm]
    exact this.symm
  rw [h3]
  refine Submodule.span_induction (p := fun x _ => TensorProduct.map e e' x ∈ tensorCycleSpan G G' n) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨a, b, p, q, hp, hq, hn, rfl⟩
    refine Submodule.subset_span ⟨e a, e' b, p, q, ?_, ?_, hn, de a, de' b, by simp⟩
    · rw [← eπ, hp]
    · rw [← eπ', hq]
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory.CechDR
