/-
# The Lagrange spectral projector and gauge-invariant spectral cross-weights

An eigenbasis of a Hermitian matrix is not a continuous function of the matrix, and its individual
vectors are only defined up to a phase.  The *rank-one spectral projector* of a simple eigenvalue
is neither: it is the Lagrange interpolation polynomial of the spectrum evaluated at the matrix,

`P_j = ∏_{k ≠ j} (H - E_k)/(E_j - E_k)`,

which is a continuous function of `(H, E)` wherever the eigenvalues are distinct.  Consequently the
*cross-weights* `w_j = ⟨u, P_j v⟩` are continuous, and they carry exactly the eigenbasis data
`conj⟨e_j,u⟩ ⟨e_j,v⟩` that a phase-orbit fidelity uses -- with the eigenvector gauge cancelled
between the two factors.

Main results:
* `lagrangeSpectralProjector` — the interpolation projector, a list product of affine factors.
* `lagrangeSpectralProjector_mulVec_eigen` — it acts as the Kronecker delta on an eigenbasis.
* `spectralCrossWeight_eq` — **the cross-weight is the gauge-invariant product**
  `conj⟨e_j,u⟩·⟨e_j,v⟩`.
* `continuous_spectralCrossWeight` — **continuity on the simple-spectrum locus**.
* `IsOrthoEigenBasis.reindex` — reindexing an orthonormal eigenbasis by an equivalence.
-/
import GaloisForLFunctions.HTGeometry.SpectralCollisionFunctional

open Matrix Filter Topology ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Reindexing an orthonormal eigenbasis -/

/-- Reindexing an orthonormal eigenbasis by an equivalence gives an orthonormal eigenbasis. -/
theorem IsOrthoEigenBasis.reindex {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (h : IsOrthoEigenBasis H e lam) (σ : α ≃ α) :
    IsOrthoEigenBasis H (fun j => e (σ j)) (fun j => lam (σ j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    rw [h.orth (σ j) (σ k)]
    by_cases hjk : j = k
    · simp [hjk]
    · simp [hjk, σ.injective.ne hjk]
  · intro j
    exact h.eigen (σ j)
  · intro ψ
    calc (∑ j, finiteComplexInner (e (σ j)) ψ • e (σ j))
        = ∑ i, finiteComplexInner (e i) ψ • e i :=
          Equiv.sum_comp σ (fun i => finiteComplexInner (e i) ψ • e i)
      _ = ψ := h.complete ψ

/-! ## The Lagrange spectral projector -/

/-- One Lagrange factor `(H - E_k)/(E_j - E_k)`. -/
def lagrangeFactor (E : α → ℝ) (j : α) (H : Matrix α α ℂ) (k : α) : Matrix α α ℂ :=
  (((E j - E k : ℝ) : ℂ))⁻¹ • (H - (((E k : ℝ) : ℂ)) • (1 : Matrix α α ℂ))

/-- The Lagrange spectral projector `∏_{k ≠ j}(H - E_k)/(E_j - E_k)`, written as a list product
over the labels other than `j`. -/
def lagrangeSpectralProjector (E : α → ℝ) (j : α) (H : Matrix α α ℂ) : Matrix α α ℂ :=
  (((Finset.univ.erase j).toList).map (lagrangeFactor E j H)).prod

theorem lagrangeFactor_mulVec_eigen {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (j k i : α) :
    lagrangeFactor lam j H k *ᵥ e i =
      ((((lam i - lam k : ℝ) : ℂ)) * (((lam j - lam k : ℝ) : ℂ))⁻¹) • e i := by
  rw [lagrangeFactor, Matrix.smul_mulVec, Matrix.sub_mulVec, heb.eigen i,
    Matrix.smul_mulVec, Matrix.one_mulVec, ← sub_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- The list product acts diagonally on an eigenvector, with the product of the scalar factors. -/
theorem listProd_lagrangeFactor_mulVec_eigen {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (j i : α) (l : List α) :
    (l.map (lagrangeFactor lam j H)).prod *ᵥ e i =
      ((l.map fun k => (((lam i - lam k : ℝ) : ℂ)) * (((lam j - lam k : ℝ) : ℂ))⁻¹).prod) • e i := by
  induction l with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        lagrangeFactor_mulVec_eigen heb j k i, smul_smul, List.map_cons, List.prod_cons]
      congr 1
      ring

theorem mem_erase_toList {j k : α} : k ∈ (Finset.univ.erase j).toList ↔ k ≠ j := by
  rw [Finset.mem_toList, Finset.mem_erase]
  simp

/-- **The Lagrange projector is the Kronecker delta on an eigenbasis with distinct eigenvalues.** -/
theorem lagrangeSpectralProjector_mulVec_eigen {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam) (j i : α) :
    lagrangeSpectralProjector lam j H *ᵥ e i = if i = j then e j else 0 := by
  rw [lagrangeSpectralProjector, listProd_lagrangeFactor_mulVec_eigen heb j i]
  by_cases hij : i = j
  · subst hij
    have hone : ((((Finset.univ.erase i).toList).map fun k =>
        (((lam i - lam k : ℝ) : ℂ)) * (((lam i - lam k : ℝ) : ℂ))⁻¹).prod) = 1 := by
      refine List.prod_eq_one ?_
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hne : lam i - lam k ≠ 0 := by
        have : k ≠ i := mem_erase_toList.mp hk
        exact sub_ne_zero_of_ne fun hcon => this (hinj hcon.symm)
      have hne' : (((lam i - lam k : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast hne
      field_simp
    rw [hone, one_smul]
    simp
  · have hzero : ((((Finset.univ.erase j).toList).map fun k =>
        (((lam i - lam k : ℝ) : ℂ)) * (((lam j - lam k : ℝ) : ℂ))⁻¹).prod) = 0 := by
      refine List.prod_eq_zero ?_
      rw [List.mem_map]
      exact ⟨i, mem_erase_toList.mpr hij, by simp⟩
    rw [hzero, zero_smul, if_neg hij]

/-- The gauge-invariant spectral cross-weight of two states at the `j`-th spectral label. -/
def spectralCrossWeight (E : α → ℝ) (H : Matrix α α ℂ) (u v : α → ℂ) (j : α) : ℂ :=
  finiteComplexInner u (lagrangeSpectralProjector E j H *ᵥ v)

/-- **The cross-weight is the gauge-invariant eigenbasis product.**  Every eigenvector phase
cancels between the two factors, so the left-hand side does not depend on the eigenbasis. -/
theorem spectralCrossWeight_eq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam) (u v : α → ℂ) (j : α) :
    spectralCrossWeight lam H u v j =
      conj (finiteComplexInner (e j) u) * finiteComplexInner (e j) v := by
  classical
  have hexp : lagrangeSpectralProjector lam j H *ᵥ v
      = finiteComplexInner (e j) v • e j := by
    conv_lhs => rw [← heb.complete v]
    rw [Matrix.mulVec_sum]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [Matrix.mulVec_smul, lagrangeSpectralProjector_mulVec_eigen heb hinj j i])]
    rw [Finset.sum_congr rfl (fun i _ => by
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi] : ∀ i ∈ Finset.univ,
        finiteComplexInner (e i) v • (if i = j then e j else 0)
          = if i = j then finiteComplexInner (e j) v • e j else 0)]
    simp
  rw [spectralCrossWeight, hexp, finiteComplexInner_smul_right,
    finiteComplexInner_conj_symm u (e j)]
  ring

/-! ## Continuity on the simple-spectrum locus -/

theorem continuousAt_lagrangeFactor {X : Type*} [TopologicalSpace X]
    {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ} (hE : Continuous Ef) (hH : Continuous Hf)
    (j k : α) {x₀ : X} (hgap : Ef x₀ j ≠ Ef x₀ k) :
    ContinuousAt (fun x => lagrangeFactor (Ef x) j (Hf x) k) x₀ := by
  have hne : (((Ef x₀ j - Ef x₀ k : ℝ) : ℂ)) ≠ 0 := by
    have : Ef x₀ j - Ef x₀ k ≠ 0 := sub_ne_zero_of_ne hgap
    exact_mod_cast this
  have h1 : ContinuousAt (fun x : X => (((Ef x j - Ef x k : ℝ) : ℂ))⁻¹) x₀ := by
    refine ContinuousAt.inv₀ ?_ hne
    exact (Complex.continuous_ofReal.comp
      (((continuous_apply j).comp hE).sub ((continuous_apply k).comp hE))).continuousAt
  have h2 : ContinuousAt (fun x : X =>
      (Hf x - (((Ef x k : ℝ) : ℂ)) • (1 : Matrix α α ℂ))) x₀ :=
    (hH.sub ((Complex.continuous_ofReal.comp ((continuous_apply k).comp hE)).smul
      continuous_const)).continuousAt
  exact h1.smul h2

theorem continuousAt_listProd_lagrangeFactor {X : Type*} [TopologicalSpace X]
    {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ} (hE : Continuous Ef) (hH : Continuous Hf)
    (j : α) {x₀ : X} (hgap : ∀ k, k ≠ j → Ef x₀ j ≠ Ef x₀ k) (l : List α)
    (hl : ∀ k ∈ l, k ≠ j) :
    ContinuousAt (fun x => (l.map (lagrangeFactor (Ef x) j (Hf x))).prod) x₀ := by
  induction l with
  | nil => simpa using continuousAt_const
  | cons k t ih =>
      simp only [List.map_cons, List.prod_cons]
      refine ContinuousAt.mul ?_ (ih fun m hm => hl m (List.mem_cons_of_mem k hm))
      exact continuousAt_lagrangeFactor hE hH j k (hgap k (hl k List.mem_cons_self))

theorem continuousAt_lagrangeSpectralProjector {X : Type*} [TopologicalSpace X]
    {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ} (hE : Continuous Ef) (hH : Continuous Hf)
    (j : α) {x₀ : X} (hinj : Function.Injective (Ef x₀)) :
    ContinuousAt (fun x => lagrangeSpectralProjector (Ef x) j (Hf x)) x₀ := by
  refine continuousAt_listProd_lagrangeFactor hE hH j (fun k hk hcon => hk (hinj hcon).symm) _ ?_
  intro k hk
  exact mem_erase_toList.mp hk

theorem continuous_inner_mulVec (u v : α → ℂ) :
    Continuous (fun M : Matrix α α ℂ => finiteComplexInner u (M *ᵥ v)) := by
  classical
  have hrw : ∀ M : Matrix α α ℂ, finiteComplexInner u (M *ᵥ v)
      = ∑ x, (starRingEnd ℂ) (u x) * ∑ y, M x y * v y := by
    intro M
    rw [finiteComplexInner]
    exact Finset.sum_congr rfl fun x _ => rfl
  simp only [hrw]
  refine continuous_finsetSum _ fun x _ => continuous_const.mul ?_
  refine continuous_finsetSum _ fun y _ => ?_
  refine Continuous.mul ?_ continuous_const
  exact (continuous_apply y).comp (continuous_apply x)

/-- **The spectral cross-weight is continuous wherever the spectrum stays simple.** -/
theorem continuousAt_spectralCrossWeight {X : Type*} [TopologicalSpace X]
    {Ef : X → α → ℝ} {Hf : X → Matrix α α ℂ} (hE : Continuous Ef) (hH : Continuous Hf)
    (u v : α → ℂ) (j : α) {x₀ : X} (hinj : Function.Injective (Ef x₀)) :
    ContinuousAt (fun x => spectralCrossWeight (Ef x) (Hf x) u v j) x₀ :=
  (continuous_inner_mulVec u v).continuousAt.comp
    (continuousAt_lagrangeSpectralProjector hE hH j hinj)

end GaloisForLFunctions.HTGeometry

end
