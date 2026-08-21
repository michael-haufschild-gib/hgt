import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# The dual lattice and its covolume

For a full `ℤ`-lattice `Λ ⊆ ℝⁿ` the *dual lattice* is

`Λ* = {y | ⟪x, y⟫ ∈ ℤ for every x ∈ Λ}`,

where `⟪x, y⟫ = ∑ k, x k * y k` is the standard pairing.  This file proves

* `DualZLattice.dual_span_eq`: if `b` and `c` are `ℝ`-bases of `ℝⁿ` in perfect duality
  (`⟪b i, c j⟫ = δᵢⱼ`) then the `ℤ`-span of `c` is the dual lattice of the `ℤ`-span of `b`;
* `DualZLattice.covolume_span_eq_abs_det`: the covolume of the `ℤ`-span of an `ℝ`-basis is the
  absolute value of the determinant of its matrix;
* `DualZLattice.covolume_mul_covolume_dual`: **`covol Λ · covol Λ* = 1`.**

mathlib knows `ZLattice.covolume` and computes it as a determinant, but has no dual-lattice theory.

This is the quantitative content of Proposition 4.1 of Suzuki, *Duality invariance of Faltings
heights, Hodge line bundles and global periods* (arXiv:2504.04993): for a complex torus
`A = ℂ^g / M ℤ^{2g}` the Faltings norm of the generator `dz₁ ∧ … ∧ dz_g` of `ω_A` is
`C(g) · 2^g · |det M|`, whereas the dual torus `B = ℂ^g / (Mᵀ)⁻¹ ℤ^{2g}` gives
`C(g) · 2^g · |det M|⁻¹` — the product being `(C(g) 2^g)²` precisely because the two period
lattices are dual to each other.
-/

namespace GaloisForLFunctions.HTGeometry.DualZLattice

open Submodule Matrix Module

variable {ι : Type*} [Fintype ι]

/-- The standard `ℝ`-bilinear pairing of `ι → ℝ` with itself. -/
def pair (x y : ι → ℝ) : ℝ := ∑ k, x k * y k

theorem pair_comm (x y : ι → ℝ) : pair x y = pair y x := by
  simp only [pair]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem pair_add_left (x y z : ι → ℝ) : pair (x + y) z = pair x z + pair y z := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pair_smul_left (m : ℤ) (x y : ι → ℝ) : pair (m • x) y = m * pair x y := by
  simp only [pair, Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The **dual lattice** of a `ℤ`-submodule of `ℝⁿ` for the standard pairing. -/
def dual (L : Submodule ℤ (ι → ℝ)) : Submodule ℤ (ι → ℝ) where
  carrier := {y | ∀ x ∈ L, ∃ m : ℤ, pair x y = m}
  add_mem' := by
    rintro y z hy hz x hx
    obtain ⟨m, hm⟩ := hy x hx
    obtain ⟨p, hp⟩ := hz x hx
    refine ⟨m + p, ?_⟩
    simp only [pair, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    rw [← hm, ← hp]
    rfl
  zero_mem' := by
    intro x _
    exact ⟨0, by simp [pair]⟩
  smul_mem' := by
    rintro c y hy x hx
    obtain ⟨m, hm⟩ := hy x hx
    refine ⟨c * m, ?_⟩
    have : pair x (c • y) = c * pair x y := by
      simp only [pair, Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hm]; push_cast; ring

theorem mem_dual {L : Submodule ℤ (ι → ℝ)} {y : ι → ℝ} :
    y ∈ dual L ↔ ∀ x ∈ L, ∃ m : ℤ, pair x y = m := Iff.rfl


theorem pair_sum_smul_right {κ : Type*} (x : ι → ℝ) (s : Finset κ) (f : κ → ℝ)
    (v : κ → (ι → ℝ)) :
    pair x (∑ j ∈ s, f j • v j) = ∑ j ∈ s, f j * pair x (v j) := by
  simp only [pair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-! ### Dual bases give dual lattices -/

variable [DecidableEq ι] {b c : Basis ι ℝ (ι → ℝ)}

/-- Two `ℝ`-bases of `ℝⁿ` are *in duality* when their pairing matrix is the identity. -/
def InDuality (b c : Basis ι ℝ (ι → ℝ)) : Prop :=
  ∀ i j, pair (b i) (c j) = if i = j then 1 else 0

theorem span_le_dual (hbc : InDuality b c) :
    span ℤ (Set.range c) ≤ dual (span ℤ (Set.range b)) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩ x hx
  refine Submodule.span_induction (p := fun x _ => ∃ m : ℤ, pair x (c j) = m) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    refine ⟨if i = j then 1 else 0, ?_⟩
    rw [hbc i j]
    by_cases h : i = j <;> simp [h]
  · exact ⟨0, by simp [pair]⟩
  · rintro y z - - ⟨m, hm⟩ ⟨p, hp⟩
    exact ⟨m + p, by rw [pair_add_left, hm, hp]; push_cast; ring⟩
  · rintro t y - ⟨m, hm⟩
    exact ⟨t * m, by rw [pair_smul_left, hm]; push_cast; ring⟩

theorem dual_le_span (hbc : InDuality b c) :
    dual (span ℤ (Set.range b)) ≤ span ℤ (Set.range c) := by
  intro y hy
  -- every coordinate of `y` in the basis `c` is an integer
  have hcoord : ∀ i, ∃ m : ℤ, c.repr y i = m := by
    intro i
    obtain ⟨m, hm⟩ := hy (b i) (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨m, ?_⟩
    have hyrepr : y = ∑ j, c.repr y j • c j := (c.sum_repr y).symm
    have : pair (b i) y = c.repr y i := by
      conv_lhs => rw [hyrepr]
      rw [pair_sum_smul_right]
      rw [Finset.sum_eq_single i]
      · rw [hbc i i, if_pos rfl, mul_one]
      · intro j _ hj
        rw [hbc i j, if_neg (Ne.symm hj), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← this, hm]
  choose m hm using hcoord
  have : y = ∑ i, (m i : ℤ) • c i := by
    conv_lhs => rw [← c.sum_repr y]
    exact Finset.sum_congr rfl fun i _ => by rw [hm i, Int.cast_smul_eq_zsmul]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Dual bases span dual lattices.** -/
theorem dual_span_eq (hbc : InDuality b c) :
    dual (span ℤ (Set.range b)) = span ℤ (Set.range c) :=
  le_antisymm (dual_le_span hbc) (span_le_dual hbc)

/-! ### Covolumes -/

/-- The covolume of the `ℤ`-span of an `ℝ`-basis of `ℝⁿ` is `|det|` of its matrix. -/
theorem covolume_span_eq_abs_det (b : Basis ι ℝ (ι → ℝ)) :
    ZLattice.covolume (span ℤ (Set.range b)) = |(Matrix.of ⇑b).det| := by
  rw [ZLattice.covolume_eq_det _ (b.restrictScalars ℤ)]
  congr 2
  funext i
  exact congrArg (Matrix.of) (funext fun i => Basis.restrictScalars_apply ℤ b i) ▸ rfl

theorem matrix_mul_transpose_of_inDuality (hbc : InDuality b c) :
    (Matrix.of ⇑b) * (Matrix.of ⇑c)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [pair] using hbc i j

theorem det_mul_det_of_inDuality (hbc : InDuality b c) :
    (Matrix.of ⇑b).det * (Matrix.of ⇑c).det = 1 := by
  have h := congrArg Matrix.det (matrix_mul_transpose_of_inDuality hbc)
  rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h

/-- **The covolume of a lattice times that of its dual is `1`.** -/
theorem covolume_mul_covolume_of_inDuality (hbc : InDuality b c) :
    ZLattice.covolume (span ℤ (Set.range b)) * ZLattice.covolume (span ℤ (Set.range c)) = 1 := by
  rw [covolume_span_eq_abs_det, covolume_span_eq_abs_det, ← abs_mul,
    det_mul_det_of_inDuality hbc, abs_one]

/-- **The covolume of a lattice times that of its dual lattice is `1`**, stated with the intrinsic
dual lattice. -/
theorem covolume_mul_covolume_dual (hbc : InDuality b c) :
    ZLattice.covolume (span ℤ (Set.range b)) * ZLattice.covolume (dual (span ℤ (Set.range b)))
      = 1 := by
  rw [dual_span_eq hbc]
  exact covolume_mul_covolume_of_inDuality hbc

/-! ### The matrix form used for period lattices

For an invertible real matrix `M`, the lattice spanned by the rows of `M` and the lattice spanned
by the rows of `(Mᵀ)⁻¹` are dual to each other; this is exactly the pair of period lattices
`M ℤ^{2g}` and `(Mᵀ)⁻¹ ℤ^{2g}` of a complex torus and its dual, written with rows instead of
columns. -/

theorem inDuality_of_mul_transpose {M N : Matrix ι ι ℝ} (h : M * Nᵀ = 1)
    (bM bN : Basis ι ℝ (ι → ℝ)) (hbM : ⇑bM = M) (hbN : ⇑bN = N) : InDuality bM bN := by
  intro i j
  have := congrFun (congrFun h i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [pair, hbM, hbN] using this

/-- The `ℝ`-basis of `ℝⁿ` given by the rows of an invertible matrix. -/
noncomputable def rowBasis (M : Matrix ι ι ℝ) (hM : IsUnit M.det) : Basis ι ℝ (ι → ℝ) :=
  (Pi.basisFun ℝ ι).map
    (Matrix.toLinearEquiv' Mᵀ
      ((Matrix.isUnit_iff_isUnit_det Mᵀ).2 (by rwa [Matrix.det_transpose])).invertible)

@[simp] theorem coe_rowBasis (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    ⇑(rowBasis M hM) = M := by
  funext i j
  rw [rowBasis, Basis.map_apply, Pi.basisFun_apply]
  show (Mᵀ *ᵥ (Pi.single i 1)) j = M i j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-- The lattice spanned over `ℤ` by the rows of a real matrix. -/
def rowLattice (M : Matrix ι ι ℝ) : Submodule ℤ (ι → ℝ) := span ℤ (Set.range (fun i => M i))

theorem rowLattice_eq_span_rowBasis (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    rowLattice M = span ℤ (Set.range ⇑(rowBasis M hM)) := by
  rw [rowLattice, coe_rowBasis]

theorem inDuality_rowBasis (M : Matrix ι ι ℝ) (hM : IsUnit M.det)
    (hMi : IsUnit ((M⁻¹)ᵀ).det) : InDuality (rowBasis M hM) (rowBasis (M⁻¹)ᵀ hMi) := by
  refine inDuality_of_mul_transpose ?_ _ _ (coe_rowBasis M hM) (coe_rowBasis (M⁻¹)ᵀ hMi)
  rw [Matrix.transpose_transpose]
  exact Matrix.mul_nonsing_inv M hM

/-- The covolume of the row lattice of an invertible matrix is `|det|`. -/
theorem covolume_rowLattice (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    ZLattice.covolume (rowLattice M) = |M.det| := by
  rw [rowLattice_eq_span_rowBasis M hM, covolume_span_eq_abs_det, coe_rowBasis]
  rfl

theorem isUnit_det_inv_transpose {M : Matrix ι ι ℝ} (hM : IsUnit M.det) :
    IsUnit ((M⁻¹)ᵀ).det := by
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
  rw [Ring.inverse_eq_inv']
  exact hM.inv

/-- **The row lattice of `(Mᵀ)⁻¹ = (M⁻¹)ᵀ` is the dual lattice of the row lattice of `M`.** -/
theorem dual_rowLattice (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    dual (rowLattice M) = rowLattice ((M⁻¹)ᵀ) := by
  rw [rowLattice_eq_span_rowBasis M hM,
    rowLattice_eq_span_rowBasis ((M⁻¹)ᵀ) (isUnit_det_inv_transpose hM),
    dual_span_eq (inDuality_rowBasis M hM (isUnit_det_inv_transpose hM))]

/-- **Suzuki's period–covolume relation.**  For an invertible period matrix `M`, the row lattice of
`M` and its dual lattice have covolumes `|det M|` and `|det M|⁻¹`, whose product is `1`. -/
theorem covolume_rowLattice_mul_covolume_dual (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    ZLattice.covolume (rowLattice M) * ZLattice.covolume (dual (rowLattice M)) = 1 := by
  have hd := inDuality_rowBasis M hM (isUnit_det_inv_transpose hM)
  rw [rowLattice_eq_span_rowBasis M hM, dual_span_eq hd]
  exact covolume_mul_covolume_of_inDuality hd

end GaloisForLFunctions.HTGeometry.DualZLattice
