import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGreenMatrixOfTheMiddleIsNegativeOnlyAlongItsPotentialAndPositiveOnChargeFreePackets

/-!
# The pole plane absorbs the bound state, and the Green matrix of Weil's form on the middle is positive

Weil's form on the step packets of a window is its neutral part plus the pole plane,

  `𝔚 = N + d ⊗ 𝟙 + 𝟙 ⊗ d`,

with `d` the degrees of the blocks and `𝟙` the flat packet. The neutral part of the dyadic
middle has one bound state; Weil's form on it is positive definite with the certified margin.
This module computes how the pole plane removes the bound state, in terms of the Green matrix.

* **The pole normal form and the pole criterion** (`OneBoundState.withPoles_form_eq`,
  `OneBoundState.withPoles_pos_iff`). For a form `M` with one bound state and Green matrix `G`,
  put `α = ⟨p, Gp⟩`, `β = ⟨p, Gq⟩`, `γ = ⟨q, Gq⟩`. Then

    `⟨x, (M + p ⊗ q + q ⊗ p) x⟩ = ⟨z, Mz⟩ + ⟨p, x⟩² ((1 + β)² − αγ)/α`,  `z ⊥ p`,

  and `M + p ⊗ q + q ⊗ p` is positive definite iff `α < 0` and `(1 + β)² < αγ`: the pole matrix
  `[[α, 1 + β], [1 + β, γ]]` is negative definite.
* **The inverse through the pole matrix** (`OneBoundState.withPoles_inv_mulVec`,
  `OneBoundState.dotProduct_poleSolution`): the inverse of `M + p ⊗ q + q ⊗ p` is `G` minus the
  rank two term of the pole matrix, and it is at least `G`
  (`OneBoundState.inv_form_le_dotProduct_poleSolution`).
* **The pole pairings of the middle** (`degreeEnergy_neg`, `poleDet_pos`, `degreeCharge_lt`): for
  the Green matrix `G_D` of the dyadic middle, unconditionally at every block size,
  `⟨d, G_D d⟩ < 0`, `(1 + ⟨d, G_D 𝟙⟩)² < ⟨d, G_D d⟩⟨𝟙, G_D 𝟙⟩`, and `⟨d, G_D 𝟙⟩ < −1/2`.
* **The Green matrix of Weil's form on the middle** (`weilGreen`) is positive definite with
  two-sided bounds on the whole space, `‖w‖²/(2 log 2D + 5) ≤ ⟨w, 𝒢_D w⟩ ≤ 5000 ‖w‖²`
  (`weilGreen_form_ge`, `weilGreen_form_le`), it is `G_D` plus the rank two term of the pole
  matrix (`weilGreen_form_eq`), and `G_D ⪯ 𝒢_D` (`greenMatrix_form_le_weilGreen`).
* **The overlap law for Weil's form** (`forall_blockWindow_form_nonneg_iff_weilSchur`,
  `riemannHypothesis_iff_forall_weilSchur_nonneg`): Weil's form is nonnegative on the step
  packets of `(R, 2(R + a) + b]` iff on the two ends it dominates the form of the couplings in
  the positive matrix `𝒢_{R+a}`; the Riemann hypothesis is this inequality on every window. The
  coupling is the neutral coupling plus the pole plane (`weilCoupling_mulVec`,
  `weilEndForm_eq`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Positive definite symmetric matrices -/

section Positive

variable {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} {ε : ℝ}

theorem le_div_of_floor_of_sq_le {δ t U W : ℝ} (hδ : 0 < δ) (hW : 0 ≤ W) (h1 : δ * U ≤ t)
    (h2 : t ^ 2 ≤ U * W) : t ≤ 1 / δ * W := by
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
  rcases le_or_gt t 0 with ht | ht
  · have := mul_nonpos_of_nonpos_of_nonneg ht hδ.le
    linarith
  · have h5 : t * (t * δ) ≤ t * W := by
      calc t * (t * δ) = δ * t ^ 2 := by ring
        _ ≤ δ * (U * W) := mul_le_mul_of_nonneg_left h2 hδ.le
        _ = δ * U * W := by ring
        _ ≤ t * W := mul_le_mul_of_nonneg_right h1 hW
    exact le_of_mul_le_mul_left h5 ht

/-- The Cauchy–Schwarz inequality of a nonnegative symmetric form. -/
theorem sq_form_le_of_form_nonneg (hsymm : ∀ i j, A i j = A j i)
    (hA0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) (x y : ι → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have hq : ∀ t : ℝ,
      0 ≤ y ⬝ᵥ (A *ᵥ y) * (t * t) + 2 * (x ⬝ᵥ (A *ᵥ y)) * t + x ⬝ᵥ (A *ᵥ x) := by
    intro t
    have h3 : (x + t • y) ⬝ᵥ (A *ᵥ (x + t • y)) =
        y ⬝ᵥ (A *ᵥ y) * (t * t) + 2 * (x ⬝ᵥ (A *ᵥ y)) * t + x ⬝ᵥ (A *ᵥ x) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_mulVec_symm hsymm y x]
      ring
    rw [← h3]
    exact hA0 _
  have hd := discrim_le_zero hq
  have h4 : discrim (y ⬝ᵥ (A *ᵥ y)) (2 * (x ⬝ᵥ (A *ᵥ y))) (x ⬝ᵥ (A *ᵥ x)) =
      4 * ((x ⬝ᵥ (A *ᵥ y)) ^ 2 - (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y))) := by
    rw [discrim]
    ring
  rw [h4] at hd
  linarith

/-- A nonnegative symmetric form of norm at most `Λ` satisfies `‖Ay‖² ≤ Λ ⟨y, Ay⟩`. -/
theorem mulVec_sq_le_of_form_nonneg {Λ : ℝ} (hsymm : ∀ i j, A i j = A j i)
    (hA0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ Λ * (x ⬝ᵥ x)) (y : ι → ℝ) :
    (A *ᵥ y) ⬝ᵥ (A *ᵥ y) ≤ Λ * (y ⬝ᵥ (A *ᵥ y)) := by
  have hcs := sq_form_le_of_form_nonneg hsymm hA0 (A *ᵥ y) y
  have he : 0 ≤ y ⬝ᵥ (A *ᵥ y) := hA0 y
  have hs : 0 ≤ (A *ᵥ y) ⬝ᵥ (A *ᵥ y) := dotProduct_self_star_nonneg (v := A *ᵥ y)
  rcases hs.eq_or_lt with hs0 | hspos
  · rw [← hs0]
    exact mul_nonneg hΛ0 he
  · have h3 : (A *ᵥ y) ⬝ᵥ (A *ᵥ y) * ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ≤
        (A *ᵥ y) ⬝ᵥ (A *ᵥ y) * (Λ * (y ⬝ᵥ (A *ᵥ y))) := by
      calc (A *ᵥ y) ⬝ᵥ (A *ᵥ y) * ((A *ᵥ y) ⬝ᵥ (A *ᵥ y))
          = ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ^ 2 := (sq _).symm
        _ ≤ (A *ᵥ y) ⬝ᵥ (A *ᵥ (A *ᵥ y)) * (y ⬝ᵥ (A *ᵥ y)) := hcs
        _ ≤ Λ * ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) * (y ⬝ᵥ (A *ᵥ y)) :=
            mul_le_mul_of_nonneg_right (hΛ _) he
        _ = (A *ᵥ y) ⬝ᵥ (A *ᵥ y) * (Λ * (y ⬝ᵥ (A *ᵥ y))) := by ring
    exact le_of_mul_le_mul_left h3 hspos

/-- The two linear equations of the pole matrix. -/
theorem pole_solve {α β γ a b Δ : ℝ} (hΔ : Δ ≠ 0) (hdef : Δ = α * γ - (1 + β) ^ 2) :
    b - (γ * a - (1 + β) * b) / Δ * β - (α * b - (1 + β) * a) / Δ * γ =
        (γ * a - (1 + β) * b) / Δ ∧
      a - (γ * a - (1 + β) * b) / Δ * α - (α * b - (1 + β) * a) / Δ * β =
        (α * b - (1 + β) * a) / Δ := by
  constructor
  · rw [eq_div_iff hΔ]
    have h1 : (b - (γ * a - (1 + β) * b) / Δ * β - (α * b - (1 + β) * a) / Δ * γ) * Δ =
        b * Δ - (γ * a - (1 + β) * b) * β - (α * b - (1 + β) * a) * γ := by
      field_simp
    rw [h1, hdef]
    ring
  · rw [eq_div_iff hΔ]
    have h1 : (a - (γ * a - (1 + β) * b) / Δ * α - (α * b - (1 + β) * a) / Δ * β) * Δ =
        a * Δ - (γ * a - (1 + β) * b) * α - (α * b - (1 + β) * a) * β := by
      field_simp
    rw [h1, hdef]
    ring

/-- The form of a matrix reindexed by an equivalence. -/
theorem dotProduct_submatrix_equiv_mulVec {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix β β ℝ) (e : α ≃ β) (x : β → ℝ) :
    (x ∘ e) ⬝ᵥ (B.submatrix e e *ᵥ (x ∘ e)) = x ⬝ᵥ (B *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Function.comp_apply]
  refine Fintype.sum_equiv e _ _ fun i => ?_
  show x (e i) * ∑ j, B (e i) (e j) * x (e j) = x (e i) * ∑ j, B (e i) j * x j
  congr 1
  exact Fintype.sum_equiv e _ _ fun j => rfl

variable [DecidableEq ι]

/-- A form with a positive floor is invertible. -/
theorem isUnit_of_form_floor (hε : 0 < ε)
    (hA : ∀ x : ι → ℝ, ε * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) : IsUnit A := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hw0 : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  suffices hwz : x - y = 0 from sub_eq_zero.mp hwz
  generalize x - y = w at hw0 ⊢
  have hf := hA w
  rw [hw0, dotProduct_zero] at hf
  have hww : w ⬝ᵥ w = 0 :=
    le_antisymm (by nlinarith) (dotProduct_self_star_nonneg (v := w))
  exact dotProduct_self_eq_zero.mp hww

theorem mulVec_inv_mulVec_of_isUnit (hA : IsUnit A) (w : ι → ℝ) : A *ᵥ (A⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA),
    Matrix.one_mulVec]

theorem inv_mulVec_mulVec_of_isUnit (hA : IsUnit A) (w : ι → ℝ) : A⁻¹ *ᵥ (A *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).mp hA),
    Matrix.one_mulVec]

/-- The inverse of a form with floor `ε` is at most `1/ε`. -/
theorem inv_form_le_of_form_floor (hε : 0 < ε)
    (hA : ∀ x : ι → ℝ, ε * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (w : ι → ℝ) :
    w ⬝ᵥ (A⁻¹ *ᵥ w) ≤ 1 / ε * (w ⬝ᵥ w) := by
  have hu : A *ᵥ (A⁻¹ *ᵥ w) = w := mulVec_inv_mulVec_of_isUnit (isUnit_of_form_floor hε hA) w
  have h1 := hA (A⁻¹ *ᵥ w)
  rw [hu] at h1
  rw [dotProduct_comm w (A⁻¹ *ᵥ w)]
  exact le_div_of_floor_of_sq_le hε (dotProduct_self_star_nonneg (v := w)) h1
    (sq_dotProduct_le_mul (A⁻¹ *ᵥ w) w)

/-- The inverse of a form with a positive floor is positive definite. -/
theorem inv_form_pos_of_form_floor (hε : 0 < ε)
    (hA : ∀ x : ι → ℝ, ε * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) {w : ι → ℝ} (hw : w ≠ 0) :
    0 < w ⬝ᵥ (A⁻¹ *ᵥ w) := by
  have hu : A *ᵥ (A⁻¹ *ᵥ w) = w := mulVec_inv_mulVec_of_isUnit (isUnit_of_form_floor hε hA) w
  have hu0 : A⁻¹ *ᵥ w ≠ 0 := fun h0 => hw (by rw [← hu, h0, Matrix.mulVec_zero])
  have h1 := hA (A⁻¹ *ᵥ w)
  rw [hu, dotProduct_comm (A⁻¹ *ᵥ w) w] at h1
  have h2 : 0 < (A⁻¹ *ᵥ w) ⬝ᵥ (A⁻¹ *ᵥ w) := by
    refine lt_of_le_of_ne (dotProduct_self_star_nonneg (v := A⁻¹ *ᵥ w)) fun h0 => hu0 ?_
    exact dotProduct_self_eq_zero.mp h0.symm
  linarith [mul_pos hε h2]

/-- The inverse of a symmetric form with a positive floor and norm at most `Λ` is at least
`1/Λ`. -/
theorem inv_form_ge_of_form_le {Λ : ℝ} (hε : 0 < ε)
    (hA : ∀ x : ι → ℝ, ε * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (hsymm : ∀ i j, A i j = A j i)
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ Λ * (x ⬝ᵥ x)) (w : ι → ℝ) :
    w ⬝ᵥ w ≤ Λ * (w ⬝ᵥ (A⁻¹ *ᵥ w)) := by
  have hu : A *ᵥ (A⁻¹ *ᵥ w) = w := mulVec_inv_mulVec_of_isUnit (isUnit_of_form_floor hε hA) w
  have hA0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := fun x =>
    le_trans (mul_nonneg hε.le (dotProduct_self_star_nonneg (v := x))) (hA x)
  have h := mulVec_sq_le_of_form_nonneg hsymm hA0 hΛ0 hΛ (A⁻¹ *ᵥ w)
  rwa [hu, dotProduct_comm (A⁻¹ *ᵥ w) w] at h

/-- **A block form over a positive definite block is nonnegative iff the Schur complement
is.** -/
theorem fromBlocks_form_nonneg_iff_schur {κ : Type*} [Fintype κ]
    (hsymm : ∀ i j, A i j = A j i) (hAu : IsUnit A)
    (hA0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) (P : Matrix ι κ ℝ) (N : Matrix κ κ ℝ) :
    (∀ v : ι ⊕ κ → ℝ, 0 ≤ v ⬝ᵥ (fromBlocks A P Pᵀ N *ᵥ v)) ↔
      ∀ e : κ → ℝ, 0 ≤ e ⬝ᵥ ((N - Pᵀ * A⁻¹ * P) *ᵥ e) := by
  constructor
  · intro hv e
    have h1 := hv (Sum.elim (-(A⁻¹ *ᵥ (P *ᵥ e))) e)
    rw [dotProduct_fromBlocks_mulVec_eq_schur hsymm hAu, neg_add_cancel, Matrix.mulVec_zero,
      dotProduct_zero, zero_add] at h1
    exact h1
  · intro hS v
    rw [← Sum.elim_comp_inl_inr v, dotProduct_fromBlocks_mulVec_eq_schur hsymm hAu]
    exact add_nonneg (hA0 _) (hS _)

end Positive

/-! ### A form with one bound state and a pole plane -/

section Poles

variable {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

/-- A matrix with a pole plane added: `M + p ⊗ q + q ⊗ p`. -/
def withPoles (M : Matrix ι ι ℝ) (p q : ι → ℝ) : Matrix ι ι ℝ :=
  M + Matrix.of fun i j => p i * q j + q i * p j

theorem withPoles_mulVec (M : Matrix ι ι ℝ) (p q x : ι → ℝ) :
    withPoles M p q *ᵥ x = M *ᵥ x + (q ⬝ᵥ x) • p + (p ⬝ᵥ x) • q := by
  rw [withPoles, Matrix.add_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  have h : ∑ j, (p i * q j + q i * p j) * x j =
      (∑ j, q j * x j) * p i + (∑ j, p j * x j) * q i := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  ring

/-- The form of a matrix with a pole plane. -/
theorem withPoles_form (M : Matrix ι ι ℝ) (p q x : ι → ℝ) :
    x ⬝ᵥ (withPoles M p q *ᵥ x) = x ⬝ᵥ (M *ᵥ x) + 2 * (p ⬝ᵥ x) * (q ⬝ᵥ x) := by
  rw [withPoles_mulVec, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, dotProduct_comm x p, dotProduct_comm x q]
  ring

omit [Fintype ι] in
theorem withPoles_symm (hM : ∀ i j, M i j = M j i) (p q : ι → ℝ) (i j : ι) :
    withPoles M p q i j = withPoles M p q j i := by
  simp only [withPoles, Matrix.add_apply, Matrix.of_apply]
  rw [hM i j]
  ring

variable [DecidableEq ι]

/-- A form with one bound state is positive on the hyperplane `p^⊥` if its Green form is
negative at `p`. -/
theorem OneBoundState.form_pos_of_inv_form_neg (h : OneBoundState M φ μ c) {p : ι → ℝ}
    (hp : p ⬝ᵥ (M⁻¹ *ᵥ p) < 0) {y : ι → ℝ} (hy : p ⬝ᵥ y = 0) (hy0 : y ≠ 0) :
    0 < y ⬝ᵥ (M *ᵥ y) := by
  have hMu : M *ᵥ (M⁻¹ *ᵥ p) = p := h.mulVec_inv_mulVec p
  refine h.form_pos_of_orthogonal_neg (ψ := M⁻¹ *ᵥ p) ?_ ?_ hy0
  · rwa [hMu, dotProduct_comm]
  · rw [hMu, dotProduct_comm, hy]

/-- A form with one bound state is nonnegative on the hyperplane `p^⊥` if its Green form is
nonpositive at `p ≠ 0`. -/
theorem OneBoundState.form_nonneg_of_inv_form_nonpos (h : OneBoundState M φ μ c) {p : ι → ℝ}
    (hp0 : p ≠ 0) (hp : p ⬝ᵥ (M⁻¹ *ᵥ p) ≤ 0) {y : ι → ℝ} (hy : p ⬝ᵥ y = 0) :
    0 ≤ y ⬝ᵥ (M *ᵥ y) := by
  by_contra hneg
  rw [not_le] at hneg
  -- otherwise `M⁻¹p` is orthogonal for the form to the negative vector `y`
  have hMu : M *ᵥ (M⁻¹ *ᵥ p) = p := h.mulVec_inv_mulVec p
  have hu : (M⁻¹ *ᵥ p) ⬝ᵥ (M *ᵥ y) = 0 := by
    rw [dotProduct_mulVec_symm h.symm, hMu, dotProduct_comm, hy]
  have hu0 : M⁻¹ *ᵥ p ≠ 0 := fun h0 => hp0 (by rw [← hMu, h0, Matrix.mulVec_zero])
  have hpos := h.form_pos_of_orthogonal_neg hneg hu hu0
  rw [hMu, dotProduct_comm] at hpos
  linarith

/-- **The reversed Cauchy–Schwarz inequality of the Green form** at a vector where it is
negative. -/
theorem OneBoundState.inv_reverse_cauchy_schwarz (h : OneBoundState M φ μ c) {p : ι → ℝ}
    (hp : p ⬝ᵥ (M⁻¹ *ᵥ p) < 0) (q : ι → ℝ) :
    p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) ≤ (p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 := by
  have hMp : M *ᵥ (M⁻¹ *ᵥ p) = p := h.mulVec_inv_mulVec p
  have hMq : M *ᵥ (M⁻¹ *ᵥ q) = q := h.mulVec_inv_mulVec q
  have h1 := h.reverse_cauchy_schwarz (ψ := M⁻¹ *ᵥ p) (by rwa [hMp, dotProduct_comm])
    (M⁻¹ *ᵥ q)
  rw [hMp, hMq, dotProduct_comm (M⁻¹ *ᵥ p) p, dotProduct_comm (M⁻¹ *ᵥ q) q,
    dotProduct_comm (M⁻¹ *ᵥ q) p] at h1
  exact h1

/-- The component of `x` in the hyperplane `p^⊥` in the pole normal form. -/
def poleResidual (M : Matrix ι ι ℝ) (p q x : ι → ℝ) : ι → ℝ :=
  x + (p ⬝ᵥ x) •
    (M⁻¹ *ᵥ q - ((1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) / (p ⬝ᵥ (M⁻¹ *ᵥ p))) • (M⁻¹ *ᵥ p))

theorem poleResidual_def (M : Matrix ι ι ℝ) (p q x : ι → ℝ) :
    poleResidual M p q x = x + (p ⬝ᵥ x) •
      (M⁻¹ *ᵥ q - ((1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) / (p ⬝ᵥ (M⁻¹ *ᵥ p))) • (M⁻¹ *ᵥ p)) := rfl

theorem dotProduct_poleResidual {p : ι → ℝ} (q : ι → ℝ) (hα : p ⬝ᵥ (M⁻¹ *ᵥ p) ≠ 0)
    (x : ι → ℝ) : p ⬝ᵥ poleResidual M p q x = 0 := by
  rw [poleResidual, dotProduct_add, dotProduct_smul, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, div_mul_cancel₀ _ hα]
  ring

/-- **The pole normal form.** The form with a pole plane is the form of the residual in `p^⊥`
plus the square of the charge `⟨p, x⟩` times the determinant of the pole matrix over `α`. -/
theorem OneBoundState.withPoles_form_eq (h : OneBoundState M φ μ c) {p : ι → ℝ} (q : ι → ℝ)
    (hα : p ⬝ᵥ (M⁻¹ *ᵥ p) ≠ 0) (x : ι → ℝ) :
    x ⬝ᵥ (withPoles M p q *ᵥ x) =
      poleResidual M p q x ⬝ᵥ (M *ᵥ poleResidual M p q x) +
        (p ⬝ᵥ x) ^ 2 *
          (((1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 - p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q))) /
            (p ⬝ᵥ (M⁻¹ *ᵥ p))) := by
  have hMq : M *ᵥ (M⁻¹ *ᵥ q) = q := h.mulVec_inv_mulVec q
  have hMp : M *ᵥ (M⁻¹ *ᵥ p) = p := h.mulVec_inv_mulVec p
  have hqp : q ⬝ᵥ (M⁻¹ *ᵥ p) = p ⬝ᵥ (M⁻¹ *ᵥ q) := h.inv_form_symm q p
  have h1 : (M⁻¹ *ᵥ q) ⬝ᵥ (M *ᵥ x) = q ⬝ᵥ x := by
    rw [dotProduct_mulVec_symm h.symm, hMq, dotProduct_comm]
  have h2 : (M⁻¹ *ᵥ p) ⬝ᵥ (M *ᵥ x) = p ⬝ᵥ x := by
    rw [dotProduct_mulVec_symm h.symm, hMp, dotProduct_comm]
  have h3 : (M⁻¹ *ᵥ q) ⬝ᵥ q = q ⬝ᵥ (M⁻¹ *ᵥ q) := dotProduct_comm _ _
  have h4 : (M⁻¹ *ᵥ q) ⬝ᵥ p = p ⬝ᵥ (M⁻¹ *ᵥ q) := dotProduct_comm _ _
  have h5 : (M⁻¹ *ᵥ p) ⬝ᵥ q = p ⬝ᵥ (M⁻¹ *ᵥ q) := (dotProduct_comm _ _).trans hqp
  have h6 : (M⁻¹ *ᵥ p) ⬝ᵥ p = p ⬝ᵥ (M⁻¹ *ᵥ p) := dotProduct_comm _ _
  have h7 : x ⬝ᵥ q = q ⬝ᵥ x := dotProduct_comm _ _
  have h8 : x ⬝ᵥ p = p ⬝ᵥ x := dotProduct_comm _ _
  rw [withPoles_form, poleResidual_def]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, add_dotProduct,
    dotProduct_add, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hMq, hMp, h1, h2, h3, h4, h5, h6, h7, h8]
  field_simp
  ring

/-- **The pole criterion, sufficiency.** If the pole matrix is negative semidefinite with
`α < 0`, the form with the pole plane is nonnegative. -/
theorem OneBoundState.withPoles_form_nonneg (h : OneBoundState M φ μ c) {p q : ι → ℝ}
    (hα : p ⬝ᵥ (M⁻¹ *ᵥ p) < 0)
    (hdet : (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 ≤ p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q))) (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ (withPoles M p q *ᵥ x) := by
  have hp0 : p ≠ 0 := fun h0 => by
    rw [h0, zero_dotProduct] at hα
    exact lt_irrefl _ hα
  rw [h.withPoles_form_eq q hα.ne]
  have h1 : 0 ≤ poleResidual M p q x ⬝ᵥ (M *ᵥ poleResidual M p q x) :=
    h.form_nonneg_of_inv_form_nonpos hp0 hα.le (dotProduct_poleResidual q hα.ne x)
  have h2 : 0 ≤ ((1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 - p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q))) /
      (p ⬝ᵥ (M⁻¹ *ᵥ p)) := div_nonneg_of_nonpos (by linarith) hα.le
  exact add_nonneg h1 (mul_nonneg (sq_nonneg _) h2)

/-- **The pole criterion.** A form with one bound state becomes positive definite by the pole
plane `p ⊗ q + q ⊗ p` iff the pole matrix `[[α, 1 + β], [1 + β, γ]]` of its Green pairings
`α = ⟨p, Gp⟩`, `β = ⟨p, Gq⟩`, `γ = ⟨q, Gq⟩` is negative definite. -/
theorem OneBoundState.withPoles_pos_iff (h : OneBoundState M φ μ c) (p q : ι → ℝ) :
    (∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (withPoles M p q *ᵥ x)) ↔
      p ⬝ᵥ (M⁻¹ *ᵥ p) < 0 ∧
        (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 < p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) := by
  constructor
  · intro hpos
    have hα : p ⬝ᵥ (M⁻¹ *ᵥ p) < 0 := by
      refine h.inv_form_neg_of_pos_on_hyperplane fun y hy0 hyp => ?_
      have h1 := hpos y hy0
      rwa [withPoles_form, dotProduct_comm p y, hyp, mul_zero, zero_mul, add_zero] at h1
    refine ⟨hα, ?_⟩
    -- the vector of charge one with residual zero
    obtain ⟨x, hx⟩ : ∃ x : ι → ℝ, x =
        -(M⁻¹ *ᵥ q - ((1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) / (p ⬝ᵥ (M⁻¹ *ᵥ p))) • (M⁻¹ *ᵥ p)) := ⟨_, rfl⟩
    have hpx : p ⬝ᵥ x = 1 := by
      rw [hx, dotProduct_neg, dotProduct_sub, dotProduct_smul, smul_eq_mul,
        div_mul_cancel₀ _ hα.ne]
      ring
    have hz : poleResidual M p q x = 0 := by
      rw [poleResidual_def, hpx, one_smul, hx, neg_add_cancel]
    have hx0 : x ≠ 0 := fun h0 => by
      rw [h0, dotProduct_zero] at hpx
      exact zero_ne_one hpx
    have h1 := hpos x hx0
    rw [h.withPoles_form_eq q hα.ne, hz, zero_dotProduct, hpx, one_pow, one_mul, zero_add]
      at h1
    rcases div_pos_iff.mp h1 with ⟨-, hb⟩ | ⟨ha, -⟩
    · exact absurd hb (not_lt.mpr hα.le)
    · linarith
  · rintro ⟨hα, hdet⟩ x hx0
    rw [h.withPoles_form_eq q hα.ne]
    have hδ : 0 < ((1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 - p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q))) /
        (p ⬝ᵥ (M⁻¹ *ᵥ p)) := div_pos_of_neg_of_neg (by linarith) hα
    by_cases hs : p ⬝ᵥ x = 0
    · have hzx : poleResidual M p q x = x := by
        rw [poleResidual_def, hs, zero_smul, add_zero]
      rw [hzx, hs]
      have h1 := h.form_pos_of_inv_form_neg hα hs hx0
      have h2 : (0 : ℝ) ^ 2 * (((1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 -
          p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q))) / (p ⬝ᵥ (M⁻¹ *ᵥ p))) = 0 := by ring
      rw [h2, add_zero]
      exact h1
    · have hp0 : p ≠ 0 := fun h0 => hs (by rw [h0, zero_dotProduct])
      have h1 : 0 ≤ poleResidual M p q x ⬝ᵥ (M *ᵥ poleResidual M p q x) :=
        h.form_nonneg_of_inv_form_nonpos hp0 hα.le (dotProduct_poleResidual q hα.ne x)
      have h2 : 0 < (p ⬝ᵥ x) ^ 2 := lt_of_le_of_ne (sq_nonneg _) fun h0 =>
        hs ((pow_eq_zero_iff two_ne_zero).mp h0.symm)
      linarith [mul_pos h2 hδ]

/-- The solution of `(M + p ⊗ q + q ⊗ p) u = w` through the Green matrix of `M` and the pole
matrix. -/
def poleSolution (M : Matrix ι ι ℝ) (p q w : ι → ℝ) : ι → ℝ :=
  M⁻¹ *ᵥ w -
    ((q ⬝ᵥ (M⁻¹ *ᵥ q) * (p ⬝ᵥ (M⁻¹ *ᵥ w)) -
        (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) * (q ⬝ᵥ (M⁻¹ *ᵥ w))) /
      (p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2)) • (M⁻¹ *ᵥ p) -
    ((p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ w)) -
        (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) * (p ⬝ᵥ (M⁻¹ *ᵥ w))) /
      (p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2)) • (M⁻¹ *ᵥ q)

theorem OneBoundState.withPoles_mulVec_poleSolution (h : OneBoundState M φ μ c)
    (p q w : ι → ℝ)
    (hΔ : p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 ≠ 0) :
    withPoles M p q *ᵥ poleSolution M p q w = w := by
  have hqp : q ⬝ᵥ (M⁻¹ *ᵥ p) = p ⬝ᵥ (M⁻¹ *ᵥ q) := h.inv_form_symm q p
  have hq : q ⬝ᵥ poleSolution M p q w =
      (q ⬝ᵥ (M⁻¹ *ᵥ q) * (p ⬝ᵥ (M⁻¹ *ᵥ w)) -
          (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) * (q ⬝ᵥ (M⁻¹ *ᵥ w))) /
        (p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2) := by
    simp only [poleSolution, dotProduct_sub, dotProduct_smul, smul_eq_mul, hqp]
    exact (pole_solve hΔ rfl).1
  have hp : p ⬝ᵥ poleSolution M p q w =
      (p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ w)) -
          (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) * (p ⬝ᵥ (M⁻¹ *ᵥ w))) /
        (p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2) := by
    simp only [poleSolution, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    exact (pole_solve hΔ rfl).2
  rw [withPoles_mulVec, hq, hp]
  simp only [poleSolution, Matrix.mulVec_sub, Matrix.mulVec_smul, h.mulVec_inv_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The inverse of a form with a pole plane** is the Green matrix corrected through the pole
matrix. -/
theorem OneBoundState.withPoles_inv_mulVec (h : OneBoundState M φ μ c) (p q w : ι → ℝ)
    (hΔ : p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2 ≠ 0)
    (hU : IsUnit (withPoles M p q)) :
    (withPoles M p q)⁻¹ *ᵥ w = poleSolution M p q w := by
  have hs := h.withPoles_mulVec_poleSolution p q w hΔ
  calc (withPoles M p q)⁻¹ *ᵥ w
      = (withPoles M p q)⁻¹ *ᵥ (withPoles M p q *ᵥ poleSolution M p q w) := by rw [hs]
    _ = poleSolution M p q w := inv_mulVec_mulVec_of_isUnit hU _

/-- **The Green form with a pole plane** is the Green form minus the form of the inverse pole
matrix on the two pole pairings `⟨p, Gw⟩`, `⟨q, Gw⟩`. -/
theorem OneBoundState.dotProduct_poleSolution (h : OneBoundState M φ μ c) (p q w : ι → ℝ) :
    w ⬝ᵥ poleSolution M p q w = w ⬝ᵥ (M⁻¹ *ᵥ w) -
      (q ⬝ᵥ (M⁻¹ *ᵥ q) * (p ⬝ᵥ (M⁻¹ *ᵥ w)) ^ 2 -
          2 * (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) * (p ⬝ᵥ (M⁻¹ *ᵥ w)) * (q ⬝ᵥ (M⁻¹ *ᵥ w)) +
          p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ w)) ^ 2) /
        (p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2) := by
  simp only [poleSolution, dotProduct_sub, dotProduct_smul, smul_eq_mul, h.inv_form_symm w p,
    h.inv_form_symm w q]
  ring

/-- **The pole plane raises the Green form**: for a negative definite pole matrix the inverse
of the form with the pole plane is at least the Green matrix. -/
theorem OneBoundState.inv_form_le_dotProduct_poleSolution (h : OneBoundState M φ μ c)
    {p q : ι → ℝ} (hα : p ⬝ᵥ (M⁻¹ *ᵥ p) < 0)
    (hΔ : 0 < p ⬝ᵥ (M⁻¹ *ᵥ p) * (q ⬝ᵥ (M⁻¹ *ᵥ q)) - (1 + p ⬝ᵥ (M⁻¹ *ᵥ q)) ^ 2)
    (w : ι → ℝ) : w ⬝ᵥ (M⁻¹ *ᵥ w) ≤ w ⬝ᵥ poleSolution M p q w := by
  rw [h.dotProduct_poleSolution]
  generalize p ⬝ᵥ (M⁻¹ *ᵥ p) = α at hα hΔ ⊢
  generalize q ⬝ᵥ (M⁻¹ *ᵥ q) = γ at hΔ ⊢
  generalize p ⬝ᵥ (M⁻¹ *ᵥ q) = β at hΔ ⊢
  generalize p ⬝ᵥ (M⁻¹ *ᵥ w) = a
  generalize q ⬝ᵥ (M⁻¹ *ᵥ w) = b
  have hN : γ * a ^ 2 - 2 * (1 + β) * a * b + α * b ^ 2 ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    have h1 := mul_neg_of_neg_of_pos hα hpos
    have h2 : α * (γ * a ^ 2 - 2 * (1 + β) * a * b + α * b ^ 2) =
        (α * b - (1 + β) * a) ^ 2 + (α * γ - (1 + β) ^ 2) * a ^ 2 := by ring
    linarith [sq_nonneg (α * b - (1 + β) * a), mul_nonneg hΔ.le (sq_nonneg a)]
  have := div_nonpos_of_nonpos_of_nonneg hN hΔ.le
  linarith

end Poles

/-! ### Weil's form on the dyadic middle -/

/-- The degrees of the blocks of the dyadic middle `(D, 2D]`. -/
def middleDegree (D : ℕ) (i : Fin D) : ℝ := blockDegree (D + i)

/-- **Weil's form on the step packets of the dyadic middle**: the block matrix of
`(D, 2D]`. -/
def weilMiddle (D : ℕ) : Matrix (Fin D) (Fin D) ℝ := AbsoluteGeometryOfSpecZ.blockWindow 1 D D

/-- The block matrix of a dyadic window does not depend on the contacts admitted. -/
theorem blockWindow_dyadic_eq (Q D : ℕ) : AbsoluteGeometryOfSpecZ.blockWindow Q D D = weilMiddle D := by
  ext i j
  have h : max (D + (i : ℕ)) (D + (j : ℕ)) < 2 * min (D + (i : ℕ)) (D + (j : ℕ)) := by
    have hi := i.2
    have hj := j.2
    omega
  have h1 := neutralBlock_eq_of_lt_two_mul (Q := Q) h
  have h2 := neutralBlock_eq_of_lt_two_mul (Q := 1) h
  simp only [weilMiddle, AbsoluteGeometryOfSpecZ.blockWindow, windowMatrix, Matrix.of_apply]
  rw [neutralBlock] at h1 h2
  linarith

/-- **Weil's form on the middle is the neutral part plus the pole plane** of the degrees and the
flat packet. -/
theorem weilMiddle_eq (D : ℕ) :
    weilMiddle D = withPoles (primeFreeMiddle D) (middleDegree D) (fun _ => 1) := by
  ext i j
  simp only [weilMiddle, AbsoluteGeometryOfSpecZ.blockWindow, withPoles, primeFreeMiddle, neutralWindow, windowMatrix,
    Matrix.add_apply, Matrix.of_apply, middleDegree, neutralBlock]
  ring

theorem weilMiddle_symm (D : ℕ) (i j : Fin D) : weilMiddle D i j = weilMiddle D j i := by
  simp only [weilMiddle, AbsoluteGeometryOfSpecZ.blockWindow, windowMatrix, Matrix.of_apply]
  exact blockMatrix_comm 1 _ _

/-- **The certified margin of Weil's form on the middle**, at every block size. -/
theorem weilMiddle_form_ge {D : ℕ} (hD : 1 ≤ D) (x : Fin D → ℝ) :
    1 / 5000 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (weilMiddle D *ᵥ x) := by
  rw [← blockWindow_dyadic_eq 2 D, AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    AbsoluteGeometryOfSpecZ.blockWindow, sum_fin_windowMatrix_eq,
    show x ⬝ᵥ x = ∑ j ∈ range D, extendFin (fun i => x i ^ 2) j by
      rw [← sum_fin_eq_sum_range_extendFin]
      exact Finset.sum_congr rfl fun i _ => (sq _).symm]
  have h := sum_blockMatrix_ge_of_short (R := D) (J := D) hD (by omega) (le_refl 2)
    (extendFin x)
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [extendFin, extendFin, dif_pos (Finset.mem_range.mp hj), dif_pos (Finset.mem_range.mp hj)]

theorem weilMiddle_form_nonneg {D : ℕ} (hD : 1 ≤ D) (x : Fin D → ℝ) :
    0 ≤ x ⬝ᵥ (weilMiddle D *ᵥ x) :=
  le_trans (mul_nonneg (by norm_num) (dotProduct_self_star_nonneg (v := x)))
    (weilMiddle_form_ge hD x)

theorem weilMiddle_form_pos {D : ℕ} (hD : 1 ≤ D) {x : Fin D → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (weilMiddle D *ᵥ x) := by
  have h2 : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne (dotProduct_self_star_nonneg (v := x)) fun h0 => hx ?_
    exact dotProduct_self_eq_zero.mp h0.symm
  linarith [weilMiddle_form_ge hD x, mul_pos (by norm_num : (0 : ℝ) < 1 / 5000) h2]

theorem isUnit_weilMiddle {D : ℕ} (hD : 1 ≤ D) : IsUnit (weilMiddle D) :=
  isUnit_of_form_floor (by norm_num : (0 : ℝ) < 1 / 5000) (weilMiddle_form_ge hD)

/-- The degrees of the middle have square sum at most `1/D`. -/
theorem mul_middleDegree_sq_le {D : ℕ} (hD : 1 ≤ D) :
    (D : ℝ) * (middleDegree D ⬝ᵥ middleDegree D) ≤ 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hD0 : (D : ℝ) ≠ 0 := hD'.ne'
  have h1 : ∀ i : Fin D,
      middleDegree D i * middleDegree D i ≤ 1 / (D : ℝ) * (1 / (D : ℝ)) := by
    intro i
    have hpos : 0 < middleDegree D i := blockDegree_pos (by omega)
    have hle : middleDegree D i ≤ 1 / (D : ℝ) := by
      refine (blockDegree_le_inv (n := D + i) (by omega)).trans ?_
      exact one_div_le_one_div_of_le hD' (by exact_mod_cast Nat.le_add_right D i)
    exact mul_le_mul hle hle hpos.le (by positivity)
  have h2 : middleDegree D ⬝ᵥ middleDegree D ≤ ∑ _i : Fin D, 1 / (D : ℝ) * (1 / (D : ℝ)) :=
    Finset.sum_le_sum fun i _ => h1 i
  calc (D : ℝ) * (middleDegree D ⬝ᵥ middleDegree D)
      ≤ (D : ℝ) * ∑ _i : Fin D, 1 / (D : ℝ) * (1 / (D : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 hD'.le
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **The norm of Weil's form on the middle is logarithmic**: `𝔚_D ⪯ 2 log 2D + 5`. -/
theorem weilMiddle_form_le {D : ℕ} (hD : 1 ≤ D) (x : Fin D → ℝ) :
    x ⬝ᵥ (weilMiddle D *ᵥ x) ≤ (2 * Real.log (2 * (D : ℝ)) + 5) * (x ⬝ᵥ x) := by
  rw [weilMiddle_eq, withPoles_form]
  have h1 := primeFreeMiddle_form_le hD x
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hd := sq_dotProduct_le_mul (middleDegree D) x
  have hone := sq_dotProduct_le_mul (fun _ : Fin D => (1 : ℝ)) x
  have h11 : (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (fun _ => 1) = D := by
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [h11] at hone
  have hxx : 0 ≤ x ⬝ᵥ x := dotProduct_self_star_nonneg (v := x)
  have h2 : (D : ℝ) * (middleDegree D ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
    calc (D : ℝ) * (middleDegree D ⬝ᵥ x) ^ 2
        ≤ (D : ℝ) * ((middleDegree D ⬝ᵥ middleDegree D) * (x ⬝ᵥ x)) :=
          mul_le_mul_of_nonneg_left hd hD'.le
      _ = (D : ℝ) * (middleDegree D ⬝ᵥ middleDegree D) * (x ⬝ᵥ x) := by ring
      _ ≤ 1 * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_right (mul_middleDegree_sq_le hD) hxx
      _ = x ⬝ᵥ x := one_mul _
  -- `2uv ≤ D u² + v²/D`
  have h3 : (D : ℝ) * (2 * (middleDegree D ⬝ᵥ x) * ((fun _ : Fin D => (1 : ℝ)) ⬝ᵥ x)) ≤
      (D : ℝ) * (2 * (x ⬝ᵥ x)) := by
    nlinarith [sq_nonneg ((D : ℝ) * (middleDegree D ⬝ᵥ x) - (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ x),
      mul_le_mul_of_nonneg_left h2 hD'.le]
  have h4 := le_of_mul_le_mul_left h3 hD'
  linarith

/-! ### The pole pairings of the middle -/

/-- The Green form of the degrees of the middle. -/
def degreeEnergy (D : ℕ) : ℝ := middleDegree D ⬝ᵥ (greenMatrix D *ᵥ middleDegree D)

/-- The charge of the Green potential of the degrees: the Green pairing of the degrees with the
flat packet. -/
def degreeCharge (D : ℕ) : ℝ := middleDegree D ⬝ᵥ (greenMatrix D *ᵥ fun _ => 1)

/-- The Green form of the flat packet of the middle. -/
def middleCapacity (D : ℕ) : ℝ := (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (greenMatrix D *ᵥ fun _ => 1)

/-- **The pole matrix of the middle is negative definite**, at every block size. -/
theorem middle_pole_pairings {D : ℕ} (hD : 1 ≤ D) :
    degreeEnergy D < 0 ∧ (1 + degreeCharge D) ^ 2 < degreeEnergy D * middleCapacity D :=
  ((oneBoundState_primeFreeMiddle hD).withPoles_pos_iff (middleDegree D) fun _ => 1).mp
    fun x hx => by
    rw [← weilMiddle_eq]
    exact weilMiddle_form_pos hD hx

/-- **The degrees are a negative vector of the Green matrix of the middle.** -/
theorem degreeEnergy_neg {D : ℕ} (hD : 1 ≤ D) : degreeEnergy D < 0 :=
  (middle_pole_pairings hD).1

theorem middleCapacity_neg {D : ℕ} (hD : 1 ≤ D) : middleCapacity D < 0 :=
  greenMatrix_flat_neg hD

/-- **The determinant of the pole matrix of the middle is positive.** -/
theorem poleDet_pos {D : ℕ} (hD : 1 ≤ D) :
    0 < degreeEnergy D * middleCapacity D - (1 + degreeCharge D) ^ 2 :=
  sub_pos.mpr (middle_pole_pairings hD).2

/-- **The Green potential of the degrees has charge below `−1/2`**: the pole criterion against
the reversed Cauchy–Schwarz inequality of the Green form. -/
theorem degreeCharge_lt {D : ℕ} (hD : 1 ≤ D) : degreeCharge D < -(1 / 2) := by
  have h1 := (middle_pole_pairings hD).2
  have h2 : degreeEnergy D * middleCapacity D ≤ degreeCharge D ^ 2 :=
    (oneBoundState_primeFreeMiddle hD).inv_reverse_cauchy_schwarz (degreeEnergy_neg hD) _
  nlinarith

/-! ### The Green matrix of Weil's form on the middle -/

/-- **The Green matrix of Weil's form on the dyadic middle.** -/
def weilGreen (D : ℕ) : Matrix (Fin D) (Fin D) ℝ := (weilMiddle D)⁻¹

/-- **The Green matrix of Weil's form on the middle is positive definite.** -/
theorem weilGreen_form_pos {D : ℕ} (hD : 1 ≤ D) {w : Fin D → ℝ} (hw : w ≠ 0) :
    0 < w ⬝ᵥ (weilGreen D *ᵥ w) :=
  inv_form_pos_of_form_floor (by norm_num : (0 : ℝ) < 1 / 5000) (weilMiddle_form_ge hD) hw

/-- The Green matrix of Weil's form on the middle is at most `5000`. -/
theorem weilGreen_form_le {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ (weilGreen D *ᵥ w) ≤ 5000 * (w ⬝ᵥ w) := by
  have h := inv_form_le_of_form_floor (by norm_num : (0 : ℝ) < 1 / 5000)
    (weilMiddle_form_ge hD) w
  rw [one_div_one_div] at h
  exact h

/-- **The Green matrix of Weil's form on the middle from below, on the whole space**:
`‖w‖² ≤ (2 log 2D + 5) ⟨w, 𝒢_D w⟩`. -/
theorem weilGreen_form_ge {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ w ≤ (2 * Real.log (2 * (D : ℝ)) + 5) * (w ⬝ᵥ (weilGreen D *ᵥ w)) :=
  inv_form_ge_of_form_le (by norm_num : (0 : ℝ) < 1 / 5000) (weilMiddle_form_ge hD)
    (weilMiddle_symm D) (by linarith [two_mul_log_add_three_pos hD]) (weilMiddle_form_le hD) w

/-- **The Green matrix of Weil's form is the neutral Green matrix corrected through the pole
matrix.** -/
theorem weilGreen_mulVec {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    weilGreen D *ᵥ w = poleSolution (primeFreeMiddle D) (middleDegree D) (fun _ => 1) w := by
  rw [weilGreen, weilMiddle_eq]
  refine (oneBoundState_primeFreeMiddle hD).withPoles_inv_mulVec _ _ w (poleDet_pos hD).ne' ?_
  rw [← weilMiddle_eq]
  exact isUnit_weilMiddle hD

/-- **The Green form of Weil's form on the middle** is the neutral Green form minus the form of
the inverse pole matrix on the pairings of `G_D w` with the degrees and the flat packet. -/
theorem weilGreen_form_eq {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ (weilGreen D *ᵥ w) = w ⬝ᵥ (greenMatrix D *ᵥ w) -
      (middleCapacity D * (middleDegree D ⬝ᵥ (greenMatrix D *ᵥ w)) ^ 2 -
          2 * (1 + degreeCharge D) * (middleDegree D ⬝ᵥ (greenMatrix D *ᵥ w)) *
            ((fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (greenMatrix D *ᵥ w)) +
          degreeEnergy D * ((fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (greenMatrix D *ᵥ w)) ^ 2) /
        (degreeEnergy D * middleCapacity D - (1 + degreeCharge D) ^ 2) := by
  rw [weilGreen_mulVec hD]
  exact (oneBoundState_primeFreeMiddle hD).dotProduct_poleSolution _ _ w

/-- **The neutral Green matrix of the middle is below the Green matrix of Weil's form.** -/
theorem greenMatrix_form_le_weilGreen {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ (greenMatrix D *ᵥ w) ≤ w ⬝ᵥ (weilGreen D *ᵥ w) := by
  rw [weilGreen_mulVec hD]
  exact (oneBoundState_primeFreeMiddle hD).inv_form_le_dotProduct_poleSolution
    (degreeEnergy_neg hD) (poleDet_pos hD) w

/-! ### The overlap law for Weil's form -/

/-- The couplings of Weil's form between the middle `(R + a, 2(R + a)]` and the two ends of
`(R, 2(R + a) + b]`. -/
def weilCoupling (Q R a b : ℕ) : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ :=
  joinColumns (posMatrix (blockMatrix Q) (middlePos R a) (leftPos R a))
    (posMatrix (blockMatrix Q) (middlePos R a) (rightPos R a b))

/-- Weil's form on the two ends of `(R, 2(R + a) + b]`. -/
def weilEndForm (Q R a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  fromBlocks (posMatrix (blockMatrix Q) (leftPos R a) (leftPos R a))
    (posMatrix (blockMatrix Q) (leftPos R a) (rightPos R a b))
    (posMatrix (blockMatrix Q) (leftPos R a) (rightPos R a b))ᵀ
    (posMatrix (blockMatrix Q) (rightPos R a b) (rightPos R a b))

/-- The Schur complement of the middle in Weil's form on `(R, 2(R + a) + b]`. -/
def weilSchur (Q R a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  weilEndForm Q R a b - (weilCoupling Q R a b)ᵀ * weilGreen (R + a) * weilCoupling Q R a b

/-- The degrees of the blocks of the two ends. -/
def endDegree (R a b : ℕ) (p : Fin a ⊕ Fin b) : ℝ :=
  blockDegree (Sum.elim (leftPos R a) (rightPos R a b) p)

theorem weilCoupling_apply (Q R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    weilCoupling Q R a b m p =
      blockMatrix Q (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) := by
  rcases p with i | j <;> rfl

theorem weilEndForm_apply (Q R a b : ℕ) (x y : Fin a ⊕ Fin b) :
    weilEndForm Q R a b x y =
      blockMatrix Q (Sum.elim (leftPos R a) (rightPos R a b) x)
        (Sum.elim (leftPos R a) (rightPos R a b) y) := by
  rcases x with i | j <;> rcases y with i' | j'
  · rfl
  · rfl
  · exact blockMatrix_comm Q _ _
  · rfl

theorem endForm_apply_pos (Q R a b : ℕ) (x y : Fin a ⊕ Fin b) :
    endForm Q R a b x y =
      neutralBlock Q (Sum.elim (leftPos R a) (rightPos R a b) x)
        (Sum.elim (leftPos R a) (rightPos R a b) y) := by
  rcases x with i | j <;> rcases y with i' | j'
  · rfl
  · rfl
  · exact neutralBlock_comm Q _ _
  · rfl

/-- **The coupling of Weil's form is the neutral coupling plus the pole plane.** -/
theorem weilCoupling_mulVec (Q R a b : ℕ) (e : Fin a ⊕ Fin b → ℝ) :
    weilCoupling Q R a b *ᵥ e = endCoupling Q R a b *ᵥ e + (∑ p, e p) • middleDegree (R + a) +
      (endDegree R a b ⬝ᵥ e) • fun _ => 1 := by
  ext m
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [weilCoupling_apply, endCoupling_apply, neutralBlock, endDegree, middleDegree, middlePos]
  ring

/-- **Weil's form on the ends is the neutral form plus the pole plane.** -/
theorem weilEndForm_eq (Q R a b : ℕ) :
    weilEndForm Q R a b = withPoles (endForm Q R a b) (endDegree R a b) (fun _ => 1) := by
  ext x y
  simp only [withPoles, Matrix.add_apply, Matrix.of_apply, mul_one, one_mul]
  rw [weilEndForm_apply, endForm_apply_pos, neutralBlock, endDegree, endDegree]
  ring

/-- The block matrix of the window in the blocks of the overlap: middle and the two ends. -/
theorem blockWindow_submatrix_overlapEquiv (Q R a b : ℕ) :
    (AbsoluteGeometryOfSpecZ.blockWindow Q R (a + (R + a) + b)).submatrix (overlapEquiv a (R + a) b)
        (overlapEquiv a (R + a) b) =
      fromBlocks (weilMiddle (R + a)) (weilCoupling Q R a b) (weilCoupling Q R a b)ᵀ
        (weilEndForm Q R a b) := by
  have hmid : windowMatrix (blockMatrix Q) (R + a) (R + a) = weilMiddle (R + a) :=
    blockWindow_dyadic_eq Q (R + a)
  rw [AbsoluteGeometryOfSpecZ.blockWindow, windowMatrix_submatrix_overlapEquiv (blockMatrix_comm Q) R a b, hmid]
  rfl

/-- **The overlap law for Weil's form.** Weil's form is nonnegative on the step packets of the
window `(R, 2(R + a) + b]` iff on the two ends it dominates the form of the couplings in the
positive Green matrix of Weil's form on the dyadic middle. -/
theorem forall_blockWindow_form_nonneg_iff_weilSchur (Q R a b : ℕ) (hD : 1 ≤ R + a) :
    (∀ x : Fin (a + (R + a) + b) → ℝ,
        0 ≤ x ⬝ᵥ (AbsoluteGeometryOfSpecZ.blockWindow Q R (a + (R + a) + b) *ᵥ x)) ↔
      ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (weilSchur Q R a b *ᵥ e) := by
  have key := fromBlocks_form_nonneg_iff_schur (weilMiddle_symm (R + a)) (isUnit_weilMiddle hD)
    (weilMiddle_form_nonneg hD) (weilCoupling Q R a b) (weilEndForm Q R a b)
  refine Iff.trans ?_ key
  rw [← blockWindow_submatrix_overlapEquiv Q R a b]
  constructor
  · intro hx v
    have h1 := dotProduct_submatrix_equiv_mulVec (AbsoluteGeometryOfSpecZ.blockWindow Q R (a + (R + a) + b))
      (overlapEquiv a (R + a) b) (v ∘ (overlapEquiv a (R + a) b).symm)
    have h2 : (v ∘ (overlapEquiv a (R + a) b).symm) ∘ overlapEquiv a (R + a) b = v := by
      ext y
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [h2] at h1
    rw [h1]
    exact hx _
  · intro hv x
    rw [← dotProduct_submatrix_equiv_mulVec _ (overlapEquiv a (R + a) b) x]
    exact hv _

/-- Weil's form of a step packet is the form of the block matrix of its window. -/
theorem packetForm_stepPacket_eq_blockWindow_form {R : ℕ} (hR : 1 ≤ R) (Q J : ℕ)
    (σ : ℕ → ℝ) :
    packetForm Q (stepPacket R J σ) =
      (fun i : Fin J => σ i) ⬝ᵥ (AbsoluteGeometryOfSpecZ.blockWindow Q R J *ᵥ fun i : Fin J => σ i) := by
  rw [packetForm_stepPacket_eq_sum_blockMatrix hR,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, AbsoluteGeometryOfSpecZ.blockWindow, sum_fin_windowMatrix_coe]

/-- **The Riemann hypothesis as the overlap law of Weil's form.** It holds iff on the two ends
of every window `(R, 2(R + a) + b]` Weil's form dominates the form of the couplings in the
Green matrix of Weil's form on the dyadic middle, a positive definite matrix between
`1/(2 log 2D + 5)` and `5000`. -/
theorem riemannHypothesis_iff_forall_weilSchur_nonneg :
    RiemannHypothesis ↔ ∀ Q R a b : ℕ, 1 ≤ R → R + (a + (R + a) + b) ≤ Q * R →
      ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (weilSchur Q R a b *ᵥ e) := by
  constructor
  · intro hRH Q R a b hR hQ
    refine (forall_blockWindow_form_nonneg_iff_weilSchur Q R a b (by omega)).mp fun x => ?_
    have h := packetForm_stepPacket_nonneg_of_riemannHypothesis hRH hR hQ (extendFin x)
    rw [packetForm_stepPacket_eq_blockWindow_form hR] at h
    have hx : (fun i : Fin (a + (R + a) + b) => extendFin x i) = x :=
      funext fun i => extendFin_coe x i
    rwa [hx] at h
  · intro h
    rw [riemannHypothesis_iff_forall_packetForm_stepPacket_nonneg]
    intro K hK R hR σ
    have hle : R ≤ 3 * K * R := Nat.le_mul_of_pos_left R (by omega)
    have hQ : (3 * K + 1) * R = 3 * K * R + R := by ring
    obtain ⟨N, hN⟩ : ∃ N, N = 3 * K * R := ⟨_, rfl⟩
    rw [← hN] at hle hQ ⊢
    have hJ : N = 0 + (R + 0) + (N - R) := by omega
    rw [hJ, packetForm_stepPacket_eq_blockWindow_form hR]
    exact (forall_blockWindow_form_nonneg_iff_weilSchur (3 * K + 1) R 0 (N - R) (by omega)).mpr
      (h (3 * K + 1) R 0 (N - R) hR (by omega)) _

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
