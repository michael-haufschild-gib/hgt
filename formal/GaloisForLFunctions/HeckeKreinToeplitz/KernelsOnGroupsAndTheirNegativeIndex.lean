import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.ArithmeticPositiveDuality.AMautnerPhenomenonForTheAffineGroupOfQ

/-!
# Kernels on groups and their negative index

A **kernel** on a group `G` is a function `k : G → ℂ`; it is **Hermitian** when
`k(u⁻¹) = conj k(u)`. A family `x : ι → G` gives the Gram matrix `(k(x_a⁻¹ x_b))_{a,b}`, and the
**negative index** `κ(k) ∈ ℕ∞` is the supremum of the negative squares of these Gram matrices over
all finite families. A Hermitian kernel is positive definite iff `κ(k) = 0`
(`isPosDefOnGroup_iff_negIndex_eq_zero`).

Basic laws of the index:

* *Hecke covariance*: translating a family leaves its Gram matrix unchanged (`gram_mul_left`).
* *Restriction*: pulling a kernel back along a homomorphism does not raise the index
  (`negIndex_comp_le`); in particular restriction to a subgroup.
* *Subadditivity*: `κ(k₁ + k₂) ≤ κ(k₁) + κ(k₂)` for Hermitian kernels (`negIndex_add_le`).
* *Positive parts are free*: adding a positive-definite kernel never raises the index
  (`negIndex_add_posDef_le`).

The matrix tool behind restriction is `hermNegIndex_le_of_hermQuad_eq`: a linear map preserving the
Hermitian forms maps a negative-definite subspace injectively onto a negative-definite subspace.
-/

open Complex Matrix Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality (IsPosDefOnGroup)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### Two inertia comparisons for Hermitian forms -/

section Inertia

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- A form-preserving linear map does not lower the negative index. -/
theorem hermNegIndex_le_of_hermQuad_eq (H : Matrix ι ι ℂ) (H' : Matrix ι' ι' ℂ)
    (L : (ι → ℂ) →ₗ[ℂ] (ι' → ℂ)) (hL : ∀ c, hermQuad H' (L c) = hermQuad H c) :
    hermNegIndex H ≤ hermNegIndex H' := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    by_contra hw0
    have hne : (w : ι → ℂ) ≠ 0 := fun h => hw0 (Subtype.ext h)
    have h1 := hW w w.2 hne
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hw
    rw [hermQuad_neg, ← hL, hw] at h1
    simp [hermQuad] at h1
  have hpos : IsPosDefOn (-H') (LinearMap.range (L.domRestrict W)) := by
    rintro y ⟨w, rfl⟩ hy
    have hne : (w : ι → ℂ) ≠ 0 := by
      rintro h
      apply hy
      rw [show w = 0 from Subtype.ext h, map_zero]
    have h1 := hW w w.2 hne
    rw [hermQuad_neg] at h1 ⊢
    rw [LinearMap.domRestrict_apply, hL]
    exact h1
  have h := finrank_le_posIndex hpos
  rw [LinearMap.finrank_range_of_inj hinj, hrank] at h
  exact h

/-- A pointwise smaller form has at least as many negative squares. -/
theorem hermNegIndex_le_of_hermQuad_le (H H' : Matrix ι ι ℂ)
    (h : ∀ c, hermQuad H' c ≤ hermQuad H c) : hermNegIndex H ≤ hermNegIndex H' := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  have hpos : IsPosDefOn (-H') W := fun c hc hc0 => by
    have := hW c hc hc0
    rw [hermQuad_neg] at this ⊢
    linarith [h c]
  have := finrank_le_posIndex hpos
  rw [hrank] at this
  exact this

end Inertia

/-! ### Kernels, Gram matrices and the negative index -/

section Kernels

variable {G : Type*} [Group G]

/-- A Hermitian kernel: `k(u⁻¹) = conj k(u)`. -/
def IsHermKernel (k : G → ℂ) : Prop := ∀ u, k u⁻¹ = conj (k u)

/-- The Gram matrix `(k(x_a⁻¹ x_b))_{a,b}` of a family. -/
def gram (k : G → ℂ) {ι : Type*} (x : ι → G) : Matrix ι ι ℂ := fun a b => k ((x a)⁻¹ * x b)

/-- The negative index: the supremum of the negative squares of all finite Gram matrices. -/
def negIndex (k : G → ℂ) : ℕ∞ := ⨆ (n : ℕ) (x : Fin n → G), (hermNegIndex (gram k x) : ℕ∞)

variable {ι : Type*} [Fintype ι]

/-- The Toeplitz form of a kernel on a family. -/
theorem hermQuad_gram (k : G → ℂ) (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram k x) c = (∑ a, ∑ b, conj (c a) * k ((x a)⁻¹ * x b) * c b).re := by
  simp only [hermQuad, gram, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]
  ring

omit [Fintype ι] in
theorem gram_add (k₁ k₂ : G → ℂ) (x : ι → G) :
    gram (fun u => k₁ u + k₂ u) x = gram k₁ x + gram k₂ x := rfl

theorem hermQuad_gram_add (k₁ k₂ : G → ℂ) (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (fun u => k₁ u + k₂ u) x) c = hermQuad (gram k₁ x) c + hermQuad (gram k₂ x) c := by
  simp only [hermQuad, gram_add, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

omit [Fintype ι] in
/-- **Hecke covariance**: translating a family does not change its Gram matrix. -/
theorem gram_mul_left (k : G → ℂ) (x : ι → G) (u : G) : gram k (fun a => u * x a) = gram k x := by
  ext a b
  simp only [gram, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

omit [Fintype ι] in
/-- The Gram matrix of a Hermitian kernel is Hermitian. -/
theorem gram_isHermitian {k : G → ℂ} (hk : IsHermKernel k) (x : ι → G) :
    (gram k x).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, gram, Complex.star_def]
  rw [← hk, _root_.mul_inv_rev, inv_inv]

/-- Every finite Gram matrix has at most `κ(k)` negative squares. -/
theorem hermNegIndex_gram_le_negIndex (k : G → ℂ) (x : ι → G) :
    (hermNegIndex (gram k x) : ℕ∞) ≤ negIndex k := by
  set e := Fintype.equivFin ι
  have hle : hermNegIndex (gram k x) ≤ hermNegIndex (gram k (x ∘ e.symm)) := by
    refine hermNegIndex_le_of_hermQuad_eq _ _ (LinearMap.funLeft ℂ ℂ e.symm) fun c => ?_
    rw [hermQuad_gram, hermQuad_gram]
    congr 1
    rw [← e.symm.sum_comp]
    refine sum_congr rfl fun a _ => ?_
    rw [← e.symm.sum_comp]
    rfl
  exact (Nat.cast_le.mpr hle).trans (le_iSup₂ (f := fun n (y : Fin n → G) =>
    (hermNegIndex (gram k y) : ℕ∞)) (Fintype.card ι) (x ∘ e.symm))

theorem negIndex_le_iff {k : G → ℂ} {m : ℕ∞} :
    negIndex k ≤ m ↔ ∀ (n : ℕ) (x : Fin n → G), (hermNegIndex (gram k x) : ℕ∞) ≤ m :=
  iSup₂_le_iff

/-- `κ(k) = 0` iff every Toeplitz form of `k` is nonnegative. -/
theorem negIndex_eq_zero_iff {k : G → ℂ} :
    negIndex k = 0 ↔ ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ), 0 ≤ hermQuad (gram k x) c := by
  rw [← nonpos_iff_eq_zero, negIndex_le_iff]
  refine forall_congr' fun n => forall_congr' fun x => ?_
  rw [nonpos_iff_eq_zero, Nat.cast_eq_zero]
  exact ⟨fun h => ArithmeticCastelnuovoSeveri.hermQuad_nonneg_of_negIndex_eq_zero h,
    ArithmeticCastelnuovoSeveri.negIndex_eq_zero_of_hermQuad_nonneg⟩

/-- The Toeplitz sum of a Hermitian kernel is real. -/
theorem im_toeplitzSum_eq_zero {k : G → ℂ} (hk : IsHermKernel k) (x : ι → G) (c : ι → ℂ) :
    (∑ a, ∑ b, conj (c a) * k ((x a)⁻¹ * x b) * c b).im = 0 := by
  rw [← Complex.conj_eq_iff_im, map_sum]
  simp_rw [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  rw [← hk, _root_.mul_inv_rev, inv_inv]
  ring

theorem isHermKernel_of_isPosDefOnGroup {k : G → ℂ} (hk : IsPosDefOnGroup k) : IsHermKernel k :=
  fun u => hk.map_inv u

/-- **A Hermitian kernel is positive definite iff it has no negative square.** -/
theorem isPosDefOnGroup_iff_negIndex_eq_zero {k : G → ℂ} (hk : IsHermKernel k) :
    IsPosDefOnGroup k ↔ negIndex k = 0 := by
  rw [negIndex_eq_zero_iff]
  constructor
  · intro h n x c
    obtain ⟨r, hr, hs⟩ := h n x c
    rw [hermQuad_gram]
    simp only [Complex.star_def] at hs
    rw [hs, Complex.ofReal_re]
    exact hr
  · intro h n x c
    have hq := h n x c
    rw [hermQuad_gram] at hq
    refine ⟨_, hq, ?_⟩
    simp only [Complex.star_def]
    exact Complex.ext (by rw [Complex.ofReal_re])
      (by rw [Complex.ofReal_im]; exact im_toeplitzSum_eq_zero hk x c)

/-- **Restriction.** Pulling a kernel back along a homomorphism does not raise the index. -/
theorem negIndex_comp_le {H : Type*} [Group H] (k : G → ℂ) (f : H →* G) :
    negIndex (k ∘ f) ≤ negIndex k := by
  rw [negIndex_le_iff]
  intro n x
  have : gram (k ∘ f) x = gram k (f ∘ x) := by
    ext a b
    simp [gram, map_mul, map_inv]
  rw [this]
  exact hermNegIndex_gram_le_negIndex k _

/-- **Positive parts are free.** Adding a positive-definite kernel never raises the index. -/
theorem negIndex_add_posDef_le {p k : G → ℂ} (hp : IsPosDefOnGroup p) :
    negIndex (fun u => p u + k u) ≤ negIndex k := by
  have hp0 := (negIndex_eq_zero_iff.mp ((isPosDefOnGroup_iff_negIndex_eq_zero (isHermKernel_of_isPosDefOnGroup hp)).mp hp))
  rw [negIndex_le_iff]
  intro n x
  refine (Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_le _ _ fun c => ?_)).trans
    (hermNegIndex_gram_le_negIndex k x)
  rw [hermQuad_gram_add]
  linarith [hp0 n x c]

/-- **Subadditivity** of the negative index for Hermitian kernels. -/
theorem negIndex_add_le {k₁ k₂ : G → ℂ} (h₁ : IsHermKernel k₁) (h₂ : IsHermKernel k₂) :
    negIndex (fun u => k₁ u + k₂ u) ≤ negIndex k₁ + negIndex k₂ := by
  rw [negIndex_le_iff]
  intro n x
  rw [gram_add]
  refine (Nat.cast_le.mpr (ArithmeticCastelnuovoSeveri.negIndex_add_le (gram_isHermitian h₁ x)
    (gram_isHermitian h₂ x))).trans ?_
  push_cast
  exact add_le_add (hermNegIndex_gram_le_negIndex k₁ x) (hermNegIndex_gram_le_negIndex k₂ x)

theorem IsHermKernel.add {k₁ k₂ : G → ℂ} (h₁ : IsHermKernel k₁) (h₂ : IsHermKernel k₂) :
    IsHermKernel fun u => k₁ u + k₂ u := fun u => by
  show k₁ u⁻¹ + k₂ u⁻¹ = conj (k₁ u + k₂ u)
  rw [h₁, h₂, map_add]

theorem isHermKernel_finset_sum {J : Type*} (s : Finset J) {k : J → G → ℂ}
    (hk : ∀ j ∈ s, IsHermKernel (k j)) : IsHermKernel fun u => ∑ j ∈ s, k j u := fun u => by
  show ∑ j ∈ s, k j u⁻¹ = conj (∑ j ∈ s, k j u)
  rw [map_sum]
  exact sum_congr rfl fun j hj => hk j hj u

end Kernels

end GaloisForLFunctions.HeckeKreinToeplitz
