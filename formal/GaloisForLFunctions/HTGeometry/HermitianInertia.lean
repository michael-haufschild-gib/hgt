import Mathlib

/-!
# Inertia of a complex Hermitian matrix

For a Hermitian matrix `H` over `ℂ` the real quadratic form `x ↦ Re (x* H x)` has a positive
index (the largest complex dimension of a subspace on which the form is positive definite), a
negative index, and a null index (the dimension of the kernel).  This file builds that inertia
triple and proves:

* invariance under invertible congruence `H ↦ Sᴴ H S` (**Sylvester's law of inertia**);
* the exact values for a real diagonal matrix, as counts of positive, negative and zero entries;
* the same values for a Hermitian matrix in terms of its eigenvalues;
* the completeness relation `hermPosIndex + hermNegIndex + hermNullIndex = card`.

The variational definition makes congruence invariance immediate; the spectral theorem then
transports every computation to the diagonal case.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex

noncomputable section

variable {n : Type*} [Fintype n]

/-- The real Hermitian quadratic form attached to a matrix. -/
def hermQuad (H : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ H *ᵥ x).re

/-- A subspace on which the Hermitian form is positive definite. -/
def IsPosDefOn (H : Matrix n n ℂ) (W : Submodule ℂ (n → ℂ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermQuad H x

@[simp] theorem hermQuad_neg (H : Matrix n n ℂ) (x : n → ℂ) :
    hermQuad (-H) x = -hermQuad H x := by
  simp [hermQuad, Matrix.neg_mulVec]

/-- The Hermitian form of a real diagonal matrix is the weighted sum of squared moduli. -/
theorem hermQuad_diagonal [DecidableEq n] (μ : n → ℝ) (x : n → ℂ) :
    hermQuad (diagonal (fun i => (μ i : ℂ))) x = ∑ i, μ i * normSq (x i) := by
  simp only [hermQuad, dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : star (x i) * ((μ i : ℂ) * x i) = ((μ i * normSq (x i) : ℝ) : ℂ) := by
    rw [Complex.star_def]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [h, Complex.ofReal_re]

/-- The set of dimensions realized by positive-definite subspaces. -/
def hermPosIndexSet (H : Matrix n n ℂ) : Set ℕ :=
  {r | ∃ W : Submodule ℂ (n → ℂ), Module.finrank ℂ W = r ∧ IsPosDefOn H W}

theorem posIndexSet_nonempty (H : Matrix n n ℂ) : (hermPosIndexSet H).Nonempty :=
  ⟨0, ⊥, by simp, fun x hx hx0 => absurd (by simpa using hx) hx0⟩

theorem posIndexSet_bddAbove (H : Matrix n n ℂ) : BddAbove (hermPosIndexSet H) := by
  refine ⟨Fintype.card n, ?_⟩
  rintro r ⟨W, rfl, -⟩
  have h := Submodule.finrank_le W
  rwa [Module.finrank_fintype_fun_eq_card] at h

/-- The positive index: the largest dimension of a positive-definite subspace. -/
def hermPosIndex (H : Matrix n n ℂ) : ℕ := sSup (hermPosIndexSet H)

/-- The negative index. -/
def hermNegIndex (H : Matrix n n ℂ) : ℕ := hermPosIndex (-H)

/-- The null index: the dimension of the kernel. -/
def hermNullIndex (H : Matrix n n ℂ) : ℕ := Module.finrank ℂ (LinearMap.ker H.mulVecLin)

theorem exists_isPosDefOn_finrank_eq_posIndex (H : Matrix n n ℂ) :
    ∃ W : Submodule ℂ (n → ℂ), Module.finrank ℂ W = hermPosIndex H ∧ IsPosDefOn H W :=
  Nat.sSup_mem (posIndexSet_nonempty H) (posIndexSet_bddAbove H)

theorem finrank_le_posIndex {H : Matrix n n ℂ} {W : Submodule ℂ (n → ℂ)} (hW : IsPosDefOn H W) :
    Module.finrank ℂ W ≤ hermPosIndex H :=
  le_csSup (posIndexSet_bddAbove H) ⟨W, rfl, hW⟩

/-! ### Congruence -/

theorem hermQuad_conjugate (H S : Matrix n n ℂ) (x : n → ℂ) :
    hermQuad (Sᴴ * H * S) x = hermQuad H (S *ᵥ x) := by
  simp only [hermQuad]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem mulVecLin_injective [DecidableEq n] {S : Matrix n n ℂ} (hS : IsUnit S) :
    Function.Injective S.mulVecLin := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  have hdet : S.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hx⟩
  exact ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero hdet

theorem isUnit_conjTranspose [DecidableEq n] {S : Matrix n n ℂ} (hS : IsUnit S) : IsUnit (Sᴴ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
  exact ((Matrix.isUnit_iff_isUnit_det S).mp hS).map (starRingEnd ℂ)

theorem posIndex_conjugate_le [DecidableEq n] (H : Matrix n n ℂ) {S : Matrix n n ℂ}
    (hS : IsUnit S) : hermPosIndex (Sᴴ * H * S) ≤ hermPosIndex H := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (Sᴴ * H * S)
  have hinj := mulVecLin_injective hS
  have hmap : IsPosDefOn H (W.map S.mulVecLin) := by
    rintro y ⟨x, hx, rfl⟩ hy0
    have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
    have := hW x hx hx0
    rwa [hermQuad_conjugate] at this
  have heq : Module.finrank ℂ (W.map S.mulVecLin) = Module.finrank ℂ W :=
    ((Submodule.equivMapOfInjective S.mulVecLin hinj W).symm).finrank_eq
  rw [← hrank, ← heq]
  exact finrank_le_posIndex hmap

/-- Congruence by the inverse undoes a congruence. -/
theorem conjugate_nonsing_inv [DecidableEq n] (H : Matrix n n ℂ) {S : Matrix n n ℂ}
    (hS : IsUnit S) : (S⁻¹)ᴴ * (Sᴴ * H * S) * S⁻¹ = H := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hdetH : IsUnit (Sᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.map (starRingEnd ℂ)
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv S hdet, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]

/-- **Sylvester's law of inertia, positive index.**  Invertible congruence preserves the positive
index. -/
theorem posIndex_conjugate [DecidableEq n] (H : Matrix n n ℂ) {S : Matrix n n ℂ} (hS : IsUnit S) :
    hermPosIndex (Sᴴ * H * S) = hermPosIndex H := by
  refine le_antisymm (posIndex_conjugate_le H hS) ?_
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hdetH : IsUnit (Sᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.map (starRingEnd ℂ)
  have hinvU : IsUnit S⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hS
  have hback := conjugate_nonsing_inv H hS
  calc hermPosIndex H = hermPosIndex ((S⁻¹)ᴴ * (Sᴴ * H * S) * S⁻¹) := by rw [hback]
    _ ≤ hermPosIndex (Sᴴ * H * S) := posIndex_conjugate_le _ hinvU

/-- **Sylvester's law of inertia, negative index.** -/
theorem negIndex_conjugate [DecidableEq n] (H : Matrix n n ℂ) {S : Matrix n n ℂ} (hS : IsUnit S) :
    hermNegIndex (Sᴴ * H * S) = hermNegIndex H := by
  have h : -(Sᴴ * H * S) = Sᴴ * (-H) * S := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [hermNegIndex, h, posIndex_conjugate _ hS, hermNegIndex]

/-- **Sylvester's law of inertia, null index.** -/
theorem nullIndex_conjugate [DecidableEq n] (H : Matrix n n ℂ) {S : Matrix n n ℂ} (hS : IsUnit S) :
    hermNullIndex (Sᴴ * H * S) = hermNullIndex H := by
  have hinj := mulVecLin_injective hS
  have hbij : Function.Bijective S.mulVecLin :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  set e : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) := LinearEquiv.ofBijective S.mulVecLin hbij with he
  have hinjH := mulVecLin_injective (isUnit_conjTranspose hS)
  have hker : LinearMap.ker (Sᴴ * H * S).mulVecLin =
      (LinearMap.ker H.mulVecLin).comap (e : (n → ℂ) →ₗ[ℂ] (n → ℂ)) := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.mulVecLin_apply,
      he, LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply]
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have h0 : Sᴴ *ᵥ (H *ᵥ (S *ᵥ x)) = Sᴴ *ᵥ (0 : n → ℂ) := by
        rw [Matrix.mulVec_zero]
        exact h
      simpa using hinjH h0
    · intro h
      rw [h, Matrix.mulVec_zero]
  rw [hermNullIndex, hker, Submodule.comap_equiv_eq_map_symm, hermNullIndex]
  exact ((Submodule.equivMapOfInjective (e.symm : (n → ℂ) →ₗ[ℂ] (n → ℂ))
    e.symm.injective _).symm).finrank_eq

open scoped ComplexOrder in
/-- Invertible congruence preserves and reflects positive semidefiniteness. -/
theorem posSemidef_conjugate_iff [DecidableEq n] (H : Matrix n n ℂ) {S : Matrix n n ℂ}
    (hS : IsUnit S) : (Sᴴ * H * S).PosSemidef ↔ H.PosSemidef := by
  refine ⟨fun h => ?_, fun h => h.conjTranspose_mul_mul_same _⟩
  have := h.conjTranspose_mul_mul_same (S⁻¹)
  rwa [conjugate_nonsing_inv H hS] at this

/-! ### Coordinate subspaces -/

/-- The subspace of vectors supported inside a finite set of coordinates. -/
def coordSupport (s : Finset n) : Submodule ℂ (n → ℂ) where
  carrier := {x | ∀ i, i ∉ s → x i = 0}
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

omit [Fintype n] in
@[simp] theorem mem_coordSupport {s : Finset n} {x : n → ℂ} :
    x ∈ coordSupport s ↔ ∀ i, i ∉ s → x i = 0 := Iff.rfl

omit [Fintype n] in
theorem coordSupport_eq_span [DecidableEq n] (s : Finset n) :
    coordSupport s =
      Submodule.span ℂ (Set.range fun i : {i // i ∈ s} => (Pi.single (i : n) (1 : ℂ))) := by
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.mpr ?_)
  · have hx' : x = ∑ i ∈ s, x i • (Pi.single i (1 : ℂ)) := by
      funext j
      by_cases hj : j ∈ s
      · rw [Finset.sum_apply, Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · intro h
          exact absurd hj h
      · rw [Finset.sum_apply, Finset.sum_eq_zero, hx j hj]
        intro b hb
        have hbj : b ≠ j := fun h => hj (h ▸ hb)
        simp [hbj]
    rw [hx']
    refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  · rintro _ ⟨i, rfl⟩ j hj
    have hij : (i : n) ≠ j := fun h => hj (h ▸ i.2)
    simp [hij]

theorem finrank_coordSupport [DecidableEq n] (s : Finset n) :
    Module.finrank ℂ (coordSupport s) = s.card := by
  have hli : LinearIndependent ℂ
      (fun i : {i // i ∈ s} => (Pi.single (i : n) (1 : ℂ) : n → ℂ)) := by
    have h := (Pi.basisFun ℂ n).linearIndependent.comp
      (fun i : {i // i ∈ s} => (i : n)) Subtype.val_injective
    simpa [Function.comp_def] using h
  rw [coordSupport_eq_span, finrank_span_eq_card hli]
  simp

/-! ### The diagonal case -/

theorem isPosDefOn_coordSupport_diagonal [DecidableEq n] {μ : n → ℝ} {s : Finset n}
    (hs : ∀ i ∈ s, 0 < μ i) : IsPosDefOn (diagonal (fun i => (μ i : ℂ))) (coordSupport s) := by
  intro x hx hx0
  rw [hermQuad_diagonal]
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hx0 (funext hc)
  have hjs : j ∈ s := by
    by_contra hjs
    exact hj (hx j hjs)
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · by_cases hi : i ∈ s
    · exact mul_nonneg (hs i hi).le (normSq_nonneg _)
    · rw [hx i hi]
      simp
  · exact mul_pos (hs j hjs) (normSq_pos.mpr hj)

/-- **Positive index of a real diagonal matrix.** -/
theorem posIndex_diagonal [DecidableEq n] (μ : n → ℝ) :
    hermPosIndex (diagonal (fun i => (μ i : ℂ))) = ({i | 0 < μ i} : Finset n).card := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex
      (diagonal (fun i => (μ i : ℂ)))
    set F : (n → ℂ) →ₗ[ℂ] ({i // i ∈ ({i | 0 < μ i} : Finset n)} → ℂ) :=
      LinearMap.pi (fun i : {i // i ∈ ({i | 0 < μ i} : Finset n)} => LinearMap.proj (i : n)) with hF
    have hinj : Function.Injective (F.domRestrict W) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker] at hy
      by_contra hy0
      have hyv : (y : n → ℂ) ≠ 0 := fun h => hy0 (Subtype.ext h)
      have hpos := hW _ y.2 hyv
      rw [hermQuad_diagonal] at hpos
      have hcoord : ∀ i ∈ ({i | 0 < μ i} : Finset n), (y : n → ℂ) i = 0 := by
        intro i hi
        have hyi := congrFun hy ⟨i, hi⟩
        simpa [hF, LinearMap.domRestrict_apply, LinearMap.pi_apply, LinearMap.proj_apply]
          using hyi
      have hle : ∑ i, μ i * normSq ((y : n → ℂ) i) ≤ 0 := by
        refine Finset.sum_nonpos (fun i _ => ?_)
        by_cases hi : i ∈ ({i | 0 < μ i} : Finset n)
        · rw [hcoord i hi]
          simp
        · have hni : ¬ (0 < μ i) := by simpa using hi
          exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hni) (normSq_nonneg _)
      linarith
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
    exact hle
  · have hpd : IsPosDefOn (diagonal (fun i => (μ i : ℂ))) (coordSupport ({i | 0 < μ i} : Finset n)) :=
      isPosDefOn_coordSupport_diagonal (fun i hi => by simpa using hi)
    have h := finrank_le_posIndex hpd
    rwa [finrank_coordSupport] at h

/-- **Negative index of a real diagonal matrix.** -/
theorem negIndex_diagonal [DecidableEq n] (μ : n → ℝ) :
    hermNegIndex (diagonal (fun i => (μ i : ℂ))) = ({i | μ i < 0} : Finset n).card := by
  classical
  have h : -(diagonal (fun i => (μ i : ℂ))) = diagonal (fun i => ((-μ i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hermNegIndex, h, posIndex_diagonal]
  congr 1
  ext i
  simp

/-- **Null index of a real diagonal matrix.** -/
theorem nullIndex_diagonal [DecidableEq n] (μ : n → ℝ) :
    hermNullIndex (diagonal (fun i => (μ i : ℂ))) = ({i | μ i = 0} : Finset n).card := by
  classical
  have hker : LinearMap.ker (diagonal (fun i => (μ i : ℂ))).mulVecLin =
      coordSupport ({i | μ i = 0} : Finset n) := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, mem_coordSupport, funext_iff,
      Matrix.mulVec_diagonal, Pi.zero_apply, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h i hi
      have hne : μ i ≠ 0 := by simpa using hi
      rcases mul_eq_zero.mp (h i) with h1 | h2
      · exact absurd (Complex.ofReal_eq_zero.mp h1) hne
      · exact h2
    · intro h i
      by_cases hz : μ i = 0
      · simp [hz]
      · rw [h i (by simpa using hz)]
        ring
  rw [hermNullIndex, hker, finrank_coordSupport]

/-! ### The inertia of a Hermitian matrix -/

theorem isUnit_eigenvectorUnitary [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    IsUnit ((hH.eigenvectorUnitary : Matrix n n ℂ)) :=
  ⟨⟨(hH.eigenvectorUnitary : Matrix n n ℂ), star (hH.eigenvectorUnitary : Matrix n n ℂ),
    Unitary.coe_mul_star_self _, Unitary.coe_star_mul_self _⟩, rfl⟩

/-- Unitary congruence puts a Hermitian matrix in real diagonal form. -/
theorem conjTranspose_mul_mul_eigenvectorUnitary [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * H * (hH.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
  have h := Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary hH
  rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at h
  rw [h]
  rfl

/-- **Positive index from the spectrum.** -/
theorem posIndex_eq_card_pos_eigenvalues [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    hermPosIndex H = ({i | 0 < hH.eigenvalues i} : Finset n).card := by
  rw [← posIndex_conjugate H (isUnit_eigenvectorUnitary hH),
    conjTranspose_mul_mul_eigenvectorUnitary hH, posIndex_diagonal]

/-- **Negative index from the spectrum.** -/
theorem negIndex_eq_card_neg_eigenvalues [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    hermNegIndex H = ({i | hH.eigenvalues i < 0} : Finset n).card := by
  rw [← negIndex_conjugate H (isUnit_eigenvectorUnitary hH),
    conjTranspose_mul_mul_eigenvectorUnitary hH, negIndex_diagonal]

/-- **Null index from the spectrum.** -/
theorem nullIndex_eq_card_zero_eigenvalues [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    hermNullIndex H = ({i | hH.eigenvalues i = 0} : Finset n).card := by
  rw [← nullIndex_conjugate H (isUnit_eigenvectorUnitary hH),
    conjTranspose_mul_mul_eigenvectorUnitary hH, nullIndex_diagonal]

theorem card_filter_trichotomy (μ : n → ℝ) :
    ({i | 0 < μ i} : Finset n).card + ({i | μ i < 0} : Finset n).card
      + ({i | μ i = 0} : Finset n).card = Fintype.card n := by
  classical
  have h1 : Disjoint ({i | 0 < μ i} : Finset n) ({i | μ i < 0} : Finset n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    linarith
  have h2 : Disjoint (({i | 0 < μ i} : Finset n) ∪ ({i | μ i < 0} : Finset n))
      ({i | μ i = 0} : Finset n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ha | ha <;> linarith
  rw [← Finset.card_union_of_disjoint h1, ← Finset.card_union_of_disjoint h2, ← Finset.card_univ]
  congr 1
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  rcases lt_trichotomy (μ i) 0 with h | h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · exact Or.inl (Or.inl h)

/-- **Completeness of the inertia triple.** -/
theorem posIndex_add_negIndex_add_nullIndex [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) : hermPosIndex H + hermNegIndex H + hermNullIndex H = Fintype.card n := by
  rw [posIndex_eq_card_pos_eigenvalues hH, negIndex_eq_card_neg_eigenvalues hH,
    nullIndex_eq_card_zero_eigenvalues hH]
  exact card_filter_trichotomy _

end

end GaloisForLFunctions.HTGeometry
