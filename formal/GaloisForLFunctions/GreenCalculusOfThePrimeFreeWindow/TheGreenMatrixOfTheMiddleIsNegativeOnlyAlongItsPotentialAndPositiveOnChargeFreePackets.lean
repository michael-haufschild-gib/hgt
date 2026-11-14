import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheContactPencilOfTheOnePrimeRangeIsConcaveInTheWeightOfThePrimeTwo

/-!
# The Green matrix of the middle is negative only along its potential and positive on charge-free packets

The bound state of the dyadic middle `M_D` is not explicit, but one negative vector is: the flat
packet `𝟙`, with `⟨𝟙, M_D 𝟙⟩ = D · N(1, 1) < −D`. Its image `V_D = M_D 𝟙` is the potential of
the middle (the row sums), and `G_D V_D = 𝟙`. This gives the Green matrix a normal form in which
the negative part is explicit.

* **The charge formula** (`OneBoundState.inv_form_eq_charge`, `greenMatrix_form_eq_charge`):

    `⟨w, G_D w⟩ = (Σ w)² / (D · N(1, 1)) + ⟨w₀, G_D w₀⟩`,  `w₀ = w − (Σ w / (D · N(1, 1))) V_D`,

  and `w₀` is charge-free. The first term is the only negative one
  (`greenMatrix_form_ge_charge`): **`G_D` is positive definite on charge-free packets**
  (`greenMatrix_pos_of_sum_eq_zero`), while the flat packet is negative for `G_D` as well
  (`greenMatrix_flat_neg`).
* **The class is closed under inversion** (`OneBoundState.inv`): the inverse of a form with one
  bound state, depth `μ`, floor `c` and norm at most `Λ` is a form with one bound state, depth
  `1/μ` and floor `1/Λ`. The norm of the middle is logarithmic
  (`primeFreeMiddle_form_le`, Gershgorin: `M_D ⪯ 2 log 2D + 3`).
* **Quantitative positivity off a negative vector** (`OneBoundState.inv_form_ge_of_binding`): if
  `⟨ψ, Mψ⟩ ≤ −ν‖ψ‖²` then `‖w‖² ≤ (Λ + μ(μ + Λ)/ν) ⟨w, M⁻¹w⟩` for `w ⊥ ψ`. The mechanism is
  the Cauchy–Schwarz inequality of `M` on the `M`-orthogonal complement of `ψ`
  (`OneBoundState.sq_form_le_of_orthogonal_neg`), applied to `M⁻¹w` and to `w` corrected
  along `ψ`.
* **Two-sided bounds** at every block size, with the upper bound `G_D ⪯ 5000`:
  on the orthogonal complement of the ground vector `‖y‖² ≤ (2 log 2D + 3)⟨y, G_D y⟩`
  (`greenMatrix_form_ge_of_perp`), on charge-free packets
  `‖w‖² ≤ (8 log 2D + 21)⟨w, G_D w⟩` (`greenMatrix_form_ge_of_sum_eq_zero`), on the slivers
  `‖w‖² ≤ (152 log 2D + 453)⟨w, G_D w⟩` (`greenMatrix_form_ge_of_sliver`). Hence the diagonal
  of the Green matrix is positive at every block size `D ≥ 2` (`greenMatrix_diag_ge`) and the
  contact form of the one-prime range is at least `‖𝒞e‖²/(152 log 2D + 453)`
  (`contactGreen_ge`).
* **The overlap law in charge form** (`overlapSchur_form_eq_charge`,
  `riemannHypothesis_iff_forall_chargeForm`): the Schur complement of the middle is the form of
  the ends, plus the explicit repulsion `(Σ Pe)²/(D · |N(1, 1)|)` through the charge of the
  middle, minus the Green form of the neutralized coupling.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

section General

variable {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

/-- The Cauchy–Schwarz inequality of the dot product. -/
theorem sq_dotProduct_le_mul (x y : ι → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simp only [sq] at h
  rw [sq]
  exact h

/-- **Gershgorin's bound for the form of a symmetric matrix**: the absolute row sums on the
squares of the coordinates. -/
theorem dotProduct_mulVec_le_sum_abs (hM : ∀ i j, M i j = M j i) (y : ι → ℝ) :
    y ⬝ᵥ (M *ᵥ y) ≤ ∑ i, (∑ j, |M i j|) * y i ^ 2 := by
  have h1 : y ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, y i * M i j * y j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : ∀ i j, y i * M i j * y j ≤ |M i j| * y i ^ 2 / 2 + |M i j| * y j ^ 2 / 2 := by
    intro i j
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self (M i j))) (sq_nonneg (y i + y j)),
      mul_nonneg (sub_nonneg.mpr (neg_abs_le (M i j))) (sq_nonneg (y i - y j))]
  have hswap : ∑ i, ∑ j, |M i j| * y j ^ 2 / 2 = ∑ i, ∑ j, |M i j| * y i ^ 2 / 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hM j i]
  calc y ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, y i * M i j * y j := h1
    _ ≤ ∑ i, ∑ j, (|M i j| * y i ^ 2 / 2 + |M i j| * y j ^ 2 / 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
    _ = ∑ i, ∑ j, |M i j| * y i ^ 2 / 2 + ∑ i, ∑ j, |M i j| * y j ^ 2 / 2 := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i, (∑ j, |M i j|) * y i ^ 2 := by
        rw [hswap, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- A form with one bound state is nonnegative on the orthogonal complement of a negative
vector, the complement taken for the form itself. -/
theorem OneBoundState.form_nonneg_of_orthogonal_neg (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) < 0) {y : ι → ℝ} (hy : y ⬝ᵥ (M *ᵥ ψ) = 0) :
    0 ≤ y ⬝ᵥ (M *ᵥ y) := by
  by_cases hy0 : y = 0
  · rw [hy0, zero_dotProduct]
  · exact (h.form_pos_of_orthogonal_neg hψ hy hy0).le

/-- **The Cauchy–Schwarz inequality of a form with one bound state** on the orthogonal
complement of a negative vector, the complement taken for the form itself. -/
theorem OneBoundState.sq_form_le_of_orthogonal_neg (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) < 0) {x y : ι → ℝ} (hx : x ⬝ᵥ (M *ᵥ ψ) = 0)
    (hy : y ⬝ᵥ (M *ᵥ ψ) = 0) :
    (x ⬝ᵥ (M *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (M *ᵥ x)) * (y ⬝ᵥ (M *ᵥ y)) := by
  have hq : ∀ t : ℝ,
      0 ≤ y ⬝ᵥ (M *ᵥ y) * (t * t) + 2 * (x ⬝ᵥ (M *ᵥ y)) * t + x ⬝ᵥ (M *ᵥ x) := by
    intro t
    have hz : (x + t • y) ⬝ᵥ (M *ᵥ ψ) = 0 := by
      rw [add_dotProduct, smul_dotProduct, hx, hy, smul_zero, add_zero]
    have h1 := h.form_nonneg_of_orthogonal_neg hψ hz
    have h3 : (x + t • y) ⬝ᵥ (M *ᵥ (x + t • y)) =
        y ⬝ᵥ (M *ᵥ y) * (t * t) + 2 * (x ⬝ᵥ (M *ᵥ y)) * t + x ⬝ᵥ (M *ᵥ x) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_mulVec_symm h.symm y x]
      ring
    rw [← h3]
    exact h1
  have hd := discrim_le_zero hq
  have h4 : discrim (y ⬝ᵥ (M *ᵥ y)) (2 * (x ⬝ᵥ (M *ᵥ y))) (x ⬝ᵥ (M *ᵥ x)) =
      4 * ((x ⬝ᵥ (M *ᵥ y)) ^ 2 - (x ⬝ᵥ (M *ᵥ x)) * (y ⬝ᵥ (M *ᵥ y))) := by
    rw [discrim]
    ring
  rw [h4] at hd
  linarith

/-- The Cauchy–Schwarz inequality of the form on the orthogonal complement of the ground
vector. -/
theorem OneBoundState.sq_form_le (h : OneBoundState M φ μ c) {x y : ι → ℝ} (hx : φ ⬝ᵥ x = 0)
    (hy : φ ⬝ᵥ y = 0) :
    (x ⬝ᵥ (M *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (M *ᵥ x)) * (y ⬝ᵥ (M *ᵥ y)) := by
  have hφ : φ ⬝ᵥ (M *ᵥ φ) < 0 := by
    rw [h.eig, dotProduct_smul, h.unit, smul_eq_mul, mul_one]
    linarith [h.depth_pos]
  have hz : ∀ z : ι → ℝ, φ ⬝ᵥ z = 0 → z ⬝ᵥ (M *ᵥ φ) = 0 := fun z hz => by
    rw [h.eig, dotProduct_smul, dotProduct_comm, hz, smul_zero]
  exact h.sq_form_le_of_orthogonal_neg hφ (hz x hx) (hz y hy)

/-- On the orthogonal complement of the ground vector a form of norm at most `Λ` satisfies
`‖My‖² ≤ Λ ⟨y, My⟩`. -/
theorem OneBoundState.mulVec_sq_le_of_perp (h : OneBoundState M φ μ c) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y : ι → ℝ, y ⬝ᵥ (M *ᵥ y) ≤ Λ * (y ⬝ᵥ y)) {y : ι → ℝ} (hy : φ ⬝ᵥ y = 0) :
    (M *ᵥ y) ⬝ᵥ (M *ᵥ y) ≤ Λ * (y ⬝ᵥ (M *ᵥ y)) := by
  have hz : φ ⬝ᵥ (M *ᵥ y) = 0 := by rw [h.dot_mulVec, hy, mul_zero]
  have hcs := h.sq_form_le hz hy
  have he : 0 ≤ y ⬝ᵥ (M *ᵥ y) := by
    have h1 := h.floor y hy
    have h2 : 0 ≤ y ⬝ᵥ y := dotProduct_self_star_nonneg (v := y)
    linarith [mul_nonneg h.floor_pos.le h2]
  have hs : 0 ≤ (M *ᵥ y) ⬝ᵥ (M *ᵥ y) := dotProduct_self_star_nonneg (v := M *ᵥ y)
  rcases hs.eq_or_lt with hs0 | hspos
  · rw [← hs0]
    exact mul_nonneg hΛ0 he
  · have h3 : (M *ᵥ y) ⬝ᵥ (M *ᵥ y) * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) ≤
        (M *ᵥ y) ⬝ᵥ (M *ᵥ y) * (Λ * (y ⬝ᵥ (M *ᵥ y))) := by
      calc (M *ᵥ y) ⬝ᵥ (M *ᵥ y) * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y))
          = ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) ^ 2 := (sq _).symm
        _ ≤ (M *ᵥ y) ⬝ᵥ (M *ᵥ (M *ᵥ y)) * (y ⬝ᵥ (M *ᵥ y)) := hcs
        _ ≤ Λ * ((M *ᵥ y) ⬝ᵥ (M *ᵥ y)) * (y ⬝ᵥ (M *ᵥ y)) :=
            mul_le_mul_of_nonneg_right (hΛ _) he
        _ = (M *ᵥ y) ⬝ᵥ (M *ᵥ y) * (Λ * (y ⬝ᵥ (M *ᵥ y))) := by ring
    exact le_of_mul_le_mul_left h3 hspos

/-- **The size of the image of a vector** under a form with one bound state and norm at most
`Λ`. -/
theorem OneBoundState.mulVec_sq_le (h : OneBoundState M φ μ c) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ y : ι → ℝ, y ⬝ᵥ (M *ᵥ y) ≤ Λ * (y ⬝ᵥ y)) (x : ι → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) ≤ μ * (μ + Λ) * (φ ⬝ᵥ x) ^ 2 + Λ * (x ⬝ᵥ (M *ᵥ x)) := by
  have hφz : φ ⬝ᵥ (M *ᵥ OneBoundState.perp φ x) = 0 := by
    rw [h.dot_mulVec, h.dot_perp, mul_zero]
  have hM : M *ᵥ x = M *ᵥ OneBoundState.perp φ x + (-(μ * (φ ⬝ᵥ x))) • φ := by
    have h1 : M *ᵥ OneBoundState.perp φ x = M *ᵥ x - (φ ⬝ᵥ x) • ((-μ) • φ) := by
      rw [OneBoundState.perp, Matrix.mulVec_sub, Matrix.mulVec_smul, h.eig]
    rw [h1, smul_smul, show (φ ⬝ᵥ x) * -μ = -(μ * (φ ⬝ᵥ x)) by ring, sub_add_cancel]
  have hsq : (M *ᵥ x) ⬝ᵥ (M *ᵥ x) =
      (M *ᵥ OneBoundState.perp φ x) ⬝ᵥ (M *ᵥ OneBoundState.perp φ x) +
        μ ^ 2 * (φ ⬝ᵥ x) ^ 2 := by
    rw [hM]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hφz, dotProduct_comm (M *ᵥ OneBoundState.perp φ x) φ, h.unit]
    ring
  have h2 := h.mulVec_sq_le_of_perp hΛ0 hΛ (h.dot_perp x)
  have h3 := h.form_eq x
  have h4 : OneBoundState.perp φ x ⬝ᵥ (M *ᵥ OneBoundState.perp φ x) =
      x ⬝ᵥ (M *ᵥ x) + μ * (φ ⬝ᵥ x) ^ 2 := by linarith
  rw [h4] at h2
  rw [hsq]
  nlinarith

/-- The neutralized vector of the charge formula has no charge. -/
theorem dotProduct_sub_charge_smul {ψ : ι → ℝ} (hψ : ψ ⬝ᵥ (M *ᵥ ψ) ≠ 0) (w : ι → ℝ) :
    ψ ⬝ᵥ (w - ((ψ ⬝ᵥ w) / (ψ ⬝ᵥ (M *ᵥ ψ))) • (M *ᵥ ψ)) = 0 := by
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hψ, sub_self]

variable [DecidableEq ι]

/-- **The class of forms with one bound state is closed under inversion**: the inverse of a
form with depth `μ` and norm at most `Λ` has the same ground vector, depth `1/μ` and floor
`1/Λ`. -/
theorem OneBoundState.inv (h : OneBoundState M φ μ c) {Λ : ℝ} (hΛpos : 0 < Λ)
    (hΛ : ∀ y : ι → ℝ, y ⬝ᵥ (M *ᵥ y) ≤ Λ * (y ⬝ᵥ y)) :
    OneBoundState M⁻¹ φ (1 / μ) (1 / Λ) where
  symm := fun i j => by
    have hT : Mᵀ = M := Matrix.ext fun i j => h.symm j i
    have h1 : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
    calc M⁻¹ i j = (M⁻¹)ᵀ j i := rfl
      _ = M⁻¹ j i := by rw [h1]
  unit := h.unit
  eig := h.inv_mulVec_ground
  depth_pos := one_div_pos.mpr h.depth_pos
  floor_pos := one_div_pos.mpr hΛpos
  floor := fun z hz => by
    have hMx : M *ᵥ (M⁻¹ *ᵥ z) = z := h.mulVec_inv_mulVec z
    have hφx : φ ⬝ᵥ (M⁻¹ *ᵥ z) = 0 := by
      have h1 := h.dot_mulVec (M⁻¹ *ᵥ z)
      rw [hMx, hz] at h1
      have h2 : μ * (φ ⬝ᵥ (M⁻¹ *ᵥ z)) = 0 := by linarith
      exact (mul_eq_zero.mp h2).resolve_left h.depth_pos.ne'
    have h3 := h.mulVec_sq_le_of_perp hΛpos.le hΛ hφx
    rw [hMx] at h3
    calc 1 / Λ * (z ⬝ᵥ z) ≤ 1 / Λ * (Λ * ((M⁻¹ *ᵥ z) ⬝ᵥ z)) :=
          mul_le_mul_of_nonneg_left h3 (one_div_pos.mpr hΛpos).le
      _ = (M⁻¹ *ᵥ z) ⬝ᵥ z := by rw [← mul_assoc, one_div_mul_cancel hΛpos.ne', one_mul]
      _ = z ⬝ᵥ (M⁻¹ *ᵥ z) := dotProduct_comm _ _

/-- **The charge formula.** Along a vector `ψ` with `⟨ψ, Mψ⟩ ≠ 0` the Green form splits into
the square of the charge `⟨ψ, w⟩` and the Green form of the vector neutralized along `Mψ`. -/
theorem OneBoundState.inv_form_eq_charge (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) ≠ 0) (w : ι → ℝ) :
    w ⬝ᵥ (M⁻¹ *ᵥ w) = (ψ ⬝ᵥ w) ^ 2 / (ψ ⬝ᵥ (M *ᵥ ψ)) +
      (w - ((ψ ⬝ᵥ w) / (ψ ⬝ᵥ (M *ᵥ ψ))) • (M *ᵥ ψ)) ⬝ᵥ
        (M⁻¹ *ᵥ (w - ((ψ ⬝ᵥ w) / (ψ ⬝ᵥ (M *ᵥ ψ))) • (M *ᵥ ψ))) := by
  have hG : M⁻¹ *ᵥ (M *ᵥ ψ) = ψ := h.inv_mulVec_mulVec ψ
  have h1 : (M *ᵥ ψ) ⬝ᵥ (M⁻¹ *ᵥ w) = ψ ⬝ᵥ w := by
    rw [h.inv_form_symm (M *ᵥ ψ) w, hG]
    exact dotProduct_comm _ _
  have h2 : (M *ᵥ ψ) ⬝ᵥ ψ = ψ ⬝ᵥ (M *ᵥ ψ) := dotProduct_comm _ _
  have h3 : w ⬝ᵥ ψ = ψ ⬝ᵥ w := dotProduct_comm _ _
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hG, h1, h2, h3]
  field_simp
  ring

/-- **The Green form is negative only along the image of a negative vector**: it is at least
the square of the charge over the energy of the negative vector. -/
theorem OneBoundState.inv_form_ge_charge (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) < 0) (w : ι → ℝ) :
    (ψ ⬝ᵥ w) ^ 2 / (ψ ⬝ᵥ (M *ᵥ ψ)) ≤ w ⬝ᵥ (M⁻¹ *ᵥ w) := by
  have hψ0 : ψ ≠ 0 := fun h0 => by
    rw [h0, zero_dotProduct] at hψ
    exact lt_irrefl _ hψ
  have h1 := h.inv_form_eq_charge hψ.ne w
  have h2 := h.inv_form_nonneg_of_dot_eq_zero hψ0 hψ.le (dotProduct_sub_charge_smul hψ.ne w)
  linarith

/-- **The Dirichlet principle off a negative vector**: for `w` orthogonal to a negative vector
`ψ`, every `v` orthogonal to `ψ` for the form gives a lower bound of the Green form. -/
theorem OneBoundState.inv_form_ge_of_orthogonal_neg (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) < 0) {w : ι → ℝ} (hw : ψ ⬝ᵥ w = 0) {v : ι → ℝ}
    (hv : v ⬝ᵥ (M *ᵥ ψ) = 0) :
    2 * (v ⬝ᵥ w) - v ⬝ᵥ (M *ᵥ v) ≤ w ⬝ᵥ (M⁻¹ *ᵥ w) := by
  have hMu : M *ᵥ (M⁻¹ *ᵥ w) = w := h.mulVec_inv_mulVec w
  have hu : (M⁻¹ *ᵥ w) ⬝ᵥ (M *ᵥ ψ) = 0 := by rw [dotProduct_mulVec_symm h.symm, hMu, hw]
  have hd : (M⁻¹ *ᵥ w - v) ⬝ᵥ (M *ᵥ ψ) = 0 := by rw [sub_dotProduct, hu, hv, sub_zero]
  have h1 := h.form_nonneg_of_orthogonal_neg hψ hd
  have h2 : (M⁻¹ *ᵥ w - v) ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ w - v)) =
      w ⬝ᵥ (M⁻¹ *ᵥ w) - 2 * (v ⬝ᵥ w) + v ⬝ᵥ (M *ᵥ v) := by
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, hMu]
    rw [dotProduct_mulVec_symm h.symm (M⁻¹ *ᵥ w) v, hMu, dotProduct_comm (M⁻¹ *ᵥ w) w]
    ring
  linarith

/-- **Quantitative positivity of the Green form off a negative vector.** If `ψ` has binding
`ν` for a form with depth `μ` and norm at most `Λ`, the Green form is at least
`‖w‖² / (Λ + μ(μ + Λ)/ν)` on the orthogonal complement of `ψ`. -/
theorem OneBoundState.inv_form_ge_of_binding (h : OneBoundState M φ μ c) {Λ ν : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ y : ι → ℝ, y ⬝ᵥ (M *ᵥ y) ≤ Λ * (y ⬝ᵥ y)) (hν : 0 < ν)
    {ψ : ι → ℝ} (hψ0 : ψ ≠ 0) (hψ : ψ ⬝ᵥ (M *ᵥ ψ) ≤ -ν * (ψ ⬝ᵥ ψ)) {w : ι → ℝ}
    (hw : ψ ⬝ᵥ w = 0) :
    w ⬝ᵥ w ≤ (Λ + μ * (μ + Λ) / ν) * (w ⬝ᵥ (M⁻¹ *ᵥ w)) := by
  have hψψ : 0 < ψ ⬝ᵥ ψ := by
    refine lt_of_le_of_ne (dotProduct_self_star_nonneg (v := ψ)) fun h0 => hψ0 ?_
    exact dotProduct_self_eq_zero.mp h0.symm
  have hneg : ψ ⬝ᵥ (M *ᵥ ψ) < 0 := by
    have := mul_pos hν hψψ
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℝ, ψ ⬝ᵥ (M *ᵥ ψ) = -n := ⟨-(ψ ⬝ᵥ (M *ᵥ ψ)), (neg_neg _).symm⟩
  have hnpos : 0 < n := by linarith
  have hnν : ν * (ψ ⬝ᵥ ψ) ≤ n := by linarith
  have hg0 : 0 ≤ w ⬝ᵥ (M⁻¹ *ᵥ w) := h.inv_form_nonneg_of_dot_eq_zero hψ0 hneg.le hw
  have hMu : M *ᵥ (M⁻¹ *ᵥ w) = w := h.mulVec_inv_mulVec w
  have hu : (M⁻¹ *ᵥ w) ⬝ᵥ (M *ᵥ ψ) = 0 := by rw [dotProduct_mulVec_symm h.symm, hMu, hw]
  -- `v = n w + ⟨w, Mψ⟩ ψ` is orthogonal to `ψ` for the form
  have hv : (n • w + (w ⬝ᵥ (M *ᵥ ψ)) • ψ) ⬝ᵥ (M *ᵥ ψ) = 0 := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hn]
    simp only [smul_eq_mul]
    ring
  have hcs := h.sq_form_le_of_orthogonal_neg hneg hv hu
  have h1 : (n • w + (w ⬝ᵥ (M *ᵥ ψ)) • ψ) ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ w)) = n * (w ⬝ᵥ w) := by
    rw [hMu, add_dotProduct, smul_dotProduct, smul_dotProduct, hw]
    simp only [smul_eq_mul, mul_zero, add_zero]
  have h2 : (M⁻¹ *ᵥ w) ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ w)) = w ⬝ᵥ (M⁻¹ *ᵥ w) := by
    rw [hMu]
    exact dotProduct_comm _ _
  have h3 : (n • w + (w ⬝ᵥ (M *ᵥ ψ)) • ψ) ⬝ᵥ (M *ᵥ (n • w + (w ⬝ᵥ (M *ᵥ ψ)) • ψ)) =
      n * (n * (w ⬝ᵥ (M *ᵥ w)) + (w ⬝ᵥ (M *ᵥ ψ)) ^ 2) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hn]
    rw [dotProduct_mulVec_symm h.symm ψ w]
    ring
  rw [h1, h2, h3] at hcs
  -- the energy of `v` is at most `n ‖w‖² (Λ + μ(μ + Λ)/ν)`
  have hbb : (w ⬝ᵥ (M *ᵥ ψ)) ^ 2 ≤ (w ⬝ᵥ w) * ((M *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ)) :=
    sq_dotProduct_le_mul w _
  have hμΛ : 0 ≤ μ * (μ + Λ) := mul_nonneg h.depth_pos.le (by linarith [h.depth_pos])
  have hMψ : (M *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ) ≤ μ * (μ + Λ) * (ψ ⬝ᵥ ψ) := by
    have h4 := h.mulVec_sq_le hΛ0 hΛ ψ
    have h5 := mul_le_mul_of_nonneg_left (h.sq_dot_le ψ) hμΛ
    have h6 : Λ * (ψ ⬝ᵥ (M *ᵥ ψ)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hΛ0 hneg.le
    linarith
  have hψn : ψ ⬝ᵥ ψ ≤ n / ν := by
    rw [le_div_iff₀ hν]
    linarith
  have ha0 : 0 ≤ w ⬝ᵥ w := dotProduct_self_star_nonneg (v := w)
  have hE : n * (w ⬝ᵥ (M *ᵥ w)) + (w ⬝ᵥ (M *ᵥ ψ)) ^ 2 ≤
      n * (w ⬝ᵥ w) * (Λ + μ * (μ + Λ) / ν) := by
    have h6 : (w ⬝ᵥ w) * ((M *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ)) ≤ (w ⬝ᵥ w) * (μ * (μ + Λ) * (n / ν)) :=
      mul_le_mul_of_nonneg_left (hMψ.trans (mul_le_mul_of_nonneg_left hψn hμΛ)) ha0
    have h7 : n * (w ⬝ᵥ (M *ᵥ w)) ≤ n * (Λ * (w ⬝ᵥ w)) :=
      mul_le_mul_of_nonneg_left (hΛ w) hnpos.le
    calc n * (w ⬝ᵥ (M *ᵥ w)) + (w ⬝ᵥ (M *ᵥ ψ)) ^ 2
        ≤ n * (Λ * (w ⬝ᵥ w)) + (w ⬝ᵥ w) * (μ * (μ + Λ) * (n / ν)) := by linarith
      _ = n * (w ⬝ᵥ w) * (Λ + μ * (μ + Λ) / ν) := by ring
  have hfin : n * (w ⬝ᵥ w) ^ 2 ≤
      n * (w ⬝ᵥ w) * (Λ + μ * (μ + Λ) / ν) * (w ⬝ᵥ (M⁻¹ *ᵥ w)) := by
    have h8 : n * (n * (w ⬝ᵥ w) ^ 2) ≤
        n * ((n * (w ⬝ᵥ (M *ᵥ w)) + (w ⬝ᵥ (M *ᵥ ψ)) ^ 2) * (w ⬝ᵥ (M⁻¹ *ᵥ w))) := by
      calc n * (n * (w ⬝ᵥ w) ^ 2) = (n * (w ⬝ᵥ w)) ^ 2 := by ring
        _ ≤ n * (n * (w ⬝ᵥ (M *ᵥ w)) + (w ⬝ᵥ (M *ᵥ ψ)) ^ 2) * (w ⬝ᵥ (M⁻¹ *ᵥ w)) := hcs
        _ = n * ((n * (w ⬝ᵥ (M *ᵥ w)) + (w ⬝ᵥ (M *ᵥ ψ)) ^ 2) * (w ⬝ᵥ (M⁻¹ *ᵥ w))) := by
            ring
    exact (le_of_mul_le_mul_left h8 hnpos).trans (mul_le_mul_of_nonneg_right hE hg0)
  rcases ha0.eq_or_lt with ha | ha
  · rw [← ha]
    exact mul_nonneg (add_nonneg hΛ0 (div_nonneg hμΛ hν.le)) hg0
  · have h10 : n * (w ⬝ᵥ w) * (w ⬝ᵥ w) ≤
        n * (w ⬝ᵥ w) * ((Λ + μ * (μ + Λ) / ν) * (w ⬝ᵥ (M⁻¹ *ᵥ w))) := by
      calc n * (w ⬝ᵥ w) * (w ⬝ᵥ w) = n * (w ⬝ᵥ w) ^ 2 := by ring
        _ ≤ n * (w ⬝ᵥ w) * (Λ + μ * (μ + Λ) / ν) * (w ⬝ᵥ (M⁻¹ *ᵥ w)) := hfin
        _ = n * (w ⬝ᵥ w) * ((Λ + μ * (μ + Λ) / ν) * (w ⬝ᵥ (M⁻¹ *ᵥ w))) := by ring
    exact le_of_mul_le_mul_left h10 (mul_pos hnpos ha)

/-- **Quantitative positivity of the inverse off a bound principal submatrix**: on the vectors
that vanish on the coordinates of a principal submatrix with binding `μ`. -/
theorem inv_form_ge_of_comp_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M' : Matrix κ κ ℝ} {φ' : κ → ℝ} {μ' c' : ℝ} (h' : OneBoundState M' φ' μ' c') {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ y : κ → ℝ, y ⬝ᵥ (M' *ᵥ y) ≤ Λ * (y ⬝ᵥ y)) {f : ι → κ}
    (hf : Function.Injective f) (h : OneBoundState (M'.submatrix f f) φ μ c) {w : κ → ℝ}
    (hw : w ∘ f = 0) :
    w ⬝ᵥ w ≤ (Λ + μ' * (μ' + Λ) / μ) * (w ⬝ᵥ (M'⁻¹ *ᵥ w)) := by
  have hψψ : (inclusionMatrix f *ᵥ φ) ⬝ᵥ (inclusionMatrix f *ᵥ φ) = 1 := by
    have h1 := dotProduct_transpose_mul_mul_mulVec (inclusionMatrix f) (1 : Matrix κ κ ℝ) φ
    rw [inclusionMatrix_transpose_mul_mul, Matrix.submatrix_one f hf, Matrix.one_mulVec,
      Matrix.one_mulVec, h.unit] at h1
    exact h1.symm
  have hψM : (inclusionMatrix f *ᵥ φ) ⬝ᵥ (M' *ᵥ (inclusionMatrix f *ᵥ φ)) = -μ := by
    rw [← dotProduct_transpose_mul_mul_mulVec, inclusionMatrix_transpose_mul_mul, h.eig,
      dotProduct_smul, h.unit, smul_eq_mul, mul_one]
  have hψ0 : inclusionMatrix f *ᵥ φ ≠ 0 := fun h0 => by
    rw [h0, zero_dotProduct] at hψψ
    exact zero_ne_one hψψ
  refine h'.inv_form_ge_of_binding hΛ0 hΛ h.depth_pos hψ0 ?_ ?_
  · rw [hψM, hψψ, mul_one]
  · rw [dotProduct_comm, dotProduct_mulVec_eq_transpose, inclusionMatrix_transpose_mulVec, hw,
      zero_dotProduct]

/-- The form of a matrix on a coordinate vector is its diagonal entry. -/
theorem single_dotProduct_mulVec_single (A : Matrix ι ι ℝ) (i : ι) :
    (Pi.single i 1 : ι → ℝ) ⬝ᵥ (A *ᵥ Pi.single i 1) = A i i := by
  simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end General

/-! ### The potential of the dyadic middle -/

/-- **The potential of the dyadic middle**: its row sums, the image of the flat packet. -/
def middlePotential (D : ℕ) : Fin D → ℝ := primeFreeMiddle D *ᵥ fun _ => 1

theorem sum_primeFreeMiddle_row (D : ℕ) (i : Fin D) :
    ∑ j, primeFreeMiddle D i j = middlePotential D i := by
  simp only [middlePotential, Matrix.mulVec, dotProduct, mul_one]

theorem middlePotential_apply (D : ℕ) (i : Fin D) :
    middlePotential D i = blockPotential 1 D D i := by
  rw [← sum_primeFreeMiddle_row, blockPotential,
    ← Fin.sum_univ_eq_sum_range (fun l => neutralBlock 1 (D + i) (D + l)) D]
  rfl

theorem one_dotProduct_eq_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (fun _ => (1 : ℝ)) ⬝ᵥ w = ∑ i, w i := by
  simp only [dotProduct, one_mul]

/-- **The flat packet of the middle** has energy `D · N(1, 1)`. -/
theorem flat_form_primeFreeMiddle {D : ℕ} (hD : 1 ≤ D) :
    (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (primeFreeMiddle D *ᵥ fun _ => 1) =
      D * neutralBlock 1 1 1 := by
  rw [dotProduct_mulVec_eq_bilin, ← sum_neutralBlock_dyadic 1 hD]
  have hc := sum_fin_windowMatrix_coe (neutralBlock 1) D D (fun _ => 1)
  simp only [one_mul] at hc
  rw [← hc]
  simp only [bilin, one_mul, primeFreeMiddle, neutralWindow]

theorem mul_neutralBlock_one_one_neg {D : ℕ} (hD : 1 ≤ D) :
    (D : ℝ) * neutralBlock 1 1 1 < 0 :=
  mul_neg_of_pos_of_neg (by exact_mod_cast hD) (by linarith [neutralBlock_one_one_lt 1])

theorem flat_form_primeFreeMiddle_neg {D : ℕ} (hD : 1 ≤ D) :
    (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (primeFreeMiddle D *ᵥ fun _ => 1) < 0 := by
  rw [flat_form_primeFreeMiddle hD]
  exact mul_neutralBlock_one_one_neg hD

/-- The flat packet binds at least one unit per block. -/
theorem flat_form_primeFreeMiddle_le {D : ℕ} (hD : 1 ≤ D) :
    (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (primeFreeMiddle D *ᵥ fun _ => 1) ≤
      -1 * ((fun _ : Fin D => (1 : ℝ)) ⬝ᵥ fun _ => 1) := by
  rw [flat_form_primeFreeMiddle hD]
  have h1 : (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (fun _ => 1) = D := by
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [h1]
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [neutralBlock_one_one_lt 1]

theorem flat_ne_zero {D : ℕ} (hD : 1 ≤ D) : (fun _ : Fin D => (1 : ℝ)) ≠ 0 := fun h0 =>
  one_ne_zero (congrFun h0 ⟨0, hD⟩)

/-- **The Green matrix sends the potential to the flat packet.** -/
theorem greenMatrix_mulVec_middlePotential {D : ℕ} (hD : 1 ≤ D) :
    greenMatrix D *ᵥ middlePotential D = fun _ => 1 :=
  (oneBoundState_primeFreeMiddle hD).inv_mulVec_mulVec _

/-! ### The charge formula of the middle -/

/-- The neutralization of a vector on the middle: its charge is removed along the potential. -/
def neutralize (D : ℕ) (w : Fin D → ℝ) : Fin D → ℝ :=
  w - ((∑ i, w i) / (D * neutralBlock 1 1 1)) • middlePotential D

/-- The neutralized vector is charge-free. -/
theorem sum_neutralize {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) : ∑ i, neutralize D w i = 0 := by
  have h := dotProduct_sub_charge_smul (M := primeFreeMiddle D) (ψ := fun _ => (1 : ℝ))
    (flat_form_primeFreeMiddle_neg hD).ne w
  rw [flat_form_primeFreeMiddle hD, one_dotProduct_eq_sum, one_dotProduct_eq_sum] at h
  exact h

/-- **The charge formula of the middle.** The Green form is the square of the charge over the
energy `D · N(1, 1) < 0` of the flat packet, plus the Green form of the neutralized vector. -/
theorem greenMatrix_form_eq_charge {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ (greenMatrix D *ᵥ w) = (∑ i, w i) ^ 2 / (D * neutralBlock 1 1 1) +
      neutralize D w ⬝ᵥ (greenMatrix D *ᵥ neutralize D w) := by
  have h := (oneBoundState_primeFreeMiddle hD).inv_form_eq_charge (ψ := fun _ => (1 : ℝ))
    (flat_form_primeFreeMiddle_neg hD).ne w
  rw [flat_form_primeFreeMiddle hD, one_dotProduct_eq_sum] at h
  exact h

/-- **The Green matrix of the middle is negative only along its potential**: its form is at
least `−(Σ w)² / (D · |N(1, 1)|)`. -/
theorem greenMatrix_form_ge_charge {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    (∑ i, w i) ^ 2 / (D * neutralBlock 1 1 1) ≤ w ⬝ᵥ (greenMatrix D *ᵥ w) := by
  have h := (oneBoundState_primeFreeMiddle hD).inv_form_ge_charge (ψ := fun _ => (1 : ℝ))
    (flat_form_primeFreeMiddle_neg hD) w
  rw [flat_form_primeFreeMiddle hD, one_dotProduct_eq_sum] at h
  exact h

/-- **The Green matrix of the middle is positive definite on charge-free packets.** -/
theorem greenMatrix_pos_of_sum_eq_zero {D : ℕ} (hD : 1 ≤ D) {w : Fin D → ℝ}
    (hw : ∑ i, w i = 0) (hw0 : w ≠ 0) : 0 < w ⬝ᵥ (greenMatrix D *ᵥ w) :=
  (oneBoundState_primeFreeMiddle hD).inv_form_pos_of_dot_eq_zero
    (flat_form_primeFreeMiddle_neg hD) ((one_dotProduct_eq_sum w).trans hw) hw0

/-- **The flat packet is negative for the Green matrix of the middle**: the middle is positive
on charge-free packets. -/
theorem greenMatrix_flat_neg {D : ℕ} (hD : 1 ≤ D) :
    (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ (greenMatrix D *ᵥ fun _ => 1) < 0 := by
  refine (oneBoundState_primeFreeMiddle hD).inv_form_neg_of_pos_on_hyperplane
    fun y hy0 hy => ?_
  have hsum : ∑ i, y i = 0 :=
    (one_dotProduct_eq_sum y).symm.trans ((dotProduct_comm _ _).trans hy)
  have h1 := primeFreeMiddle_floor_of_sum_eq_zero hD y hsum
  have h2 : 0 < y ⬝ᵥ y := by
    refine lt_of_le_of_ne (dotProduct_self_star_nonneg (v := y)) fun h0 => hy0 ?_
    exact dotProduct_self_eq_zero.mp h0.symm
  linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 5000) h2]

/-! ### The norm of the middle and two-sided bounds for its Green matrix -/

/-- **The norm of the dyadic middle is logarithmic**: `M_D ⪯ 2 log 2D + 3`. -/
theorem primeFreeMiddle_form_le {D : ℕ} (hD : 1 ≤ D) (y : Fin D → ℝ) :
    y ⬝ᵥ (primeFreeMiddle D *ᵥ y) ≤ (2 * Real.log (2 * (D : ℝ)) + 3) * (y ⬝ᵥ y) := by
  have hL : 0 ≤ Real.log (2 * (D : ℝ)) := by
    have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
    exact Real.log_nonneg (by linarith)
  have hrow : ∀ i : Fin D, ∑ j, |primeFreeMiddle D i j| ≤ 2 * Real.log (2 * (D : ℝ)) + 3 := by
    intro i
    have h1 : ∑ j, (|primeFreeMiddle D i j| + primeFreeMiddle D i j) =
        |primeFreeMiddle D i i| + primeFreeMiddle D i i := by
      refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
      have hneg : primeFreeMiddle D i j < 0 := neutralWindow_neg_of_ne 1 D (Ne.symm hji)
      rw [abs_of_neg hneg, neg_add_cancel]
    have h3 : -3 < middlePotential D i := by
      rw [middlePotential_apply]
      exact neg_three_lt_blockPotential_dyadic hD i.2
    have h4 := (primeFreeMiddle_diag_bounds hD i).2
    have h5 : |primeFreeMiddle D i i| + primeFreeMiddle D i i ≤
        2 * Real.log (2 * (D : ℝ)) := by
      rcases le_or_gt 0 (primeFreeMiddle D i i) with h | h
      · rw [abs_of_nonneg h]
        linarith
      · rw [abs_of_neg h]
        linarith
    rw [Finset.sum_add_distrib, sum_primeFreeMiddle_row] at h1
    linarith
  calc y ⬝ᵥ (primeFreeMiddle D *ᵥ y) ≤ ∑ i, (∑ j, |primeFreeMiddle D i j|) * y i ^ 2 :=
        dotProduct_mulVec_le_sum_abs (primeFreeMiddle_symm D) y
    _ ≤ ∑ i, (2 * Real.log (2 * (D : ℝ)) + 3) * y i ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
    _ = (2 * Real.log (2 * (D : ℝ)) + 3) * (y ⬝ᵥ y) := by
        rw [← Finset.mul_sum]
        simp only [dotProduct, sq]

theorem two_mul_log_add_three_pos {D : ℕ} (hD : 1 ≤ D) :
    0 < 2 * Real.log (2 * (D : ℝ)) + 3 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (D : ℝ))]

/-- **The Green matrix of the middle is a form with one bound state**, with depth `1/μ_D` and
floor `1/(2 log 2D + 3)`. -/
theorem oneBoundState_greenMatrix {D : ℕ} (hD : 1 ≤ D) :
    OneBoundState (greenMatrix D) (groundVector D) (1 / bindingEnergy D)
      (1 / (2 * Real.log (2 * (D : ℝ)) + 3)) :=
  (oneBoundState_primeFreeMiddle hD).inv (two_mul_log_add_three_pos hD)
    (primeFreeMiddle_form_le hD)

/-- **The floor of the positive part of the Green matrix**: on the orthogonal complement of the
ground vector `‖y‖² ≤ (2 log 2D + 3) ⟨y, G_D y⟩`. -/
theorem greenMatrix_form_ge_of_perp {D : ℕ} (hD : 1 ≤ D) {y : Fin D → ℝ}
    (hy : groundVector D ⬝ᵥ y = 0) :
    y ⬝ᵥ y ≤ (2 * Real.log (2 * (D : ℝ)) + 3) * (y ⬝ᵥ (greenMatrix D *ᵥ y)) := by
  have hΛ := two_mul_log_add_three_pos hD
  have h := (oneBoundState_greenMatrix hD).floor y hy
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hΛ] at h
  linarith

/-- **The Green matrix on charge-free packets**: `‖w‖² ≤ (8 log 2D + 21) ⟨w, G_D w⟩`. -/
theorem greenMatrix_form_ge_of_sum_eq_zero {D : ℕ} (hD : 1 ≤ D) {w : Fin D → ℝ}
    (hw : ∑ i, w i = 0) :
    w ⬝ᵥ w ≤ (8 * Real.log (2 * (D : ℝ)) + 21) * (w ⬝ᵥ (greenMatrix D *ᵥ w)) := by
  have hM := oneBoundState_primeFreeMiddle hD
  have hΛ := two_mul_log_add_three_pos hD
  have hw' : (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ w = 0 := (one_dotProduct_eq_sum w).trans hw
  have h := hM.inv_form_ge_of_binding hΛ.le (primeFreeMiddle_form_le hD) one_pos
    (flat_ne_zero hD) (flat_form_primeFreeMiddle_le hD) hw'
  have hg : 0 ≤ w ⬝ᵥ (greenMatrix D *ᵥ w) :=
    hM.inv_form_nonneg_of_dot_eq_zero (flat_ne_zero hD) (flat_form_primeFreeMiddle_neg hD).le hw'
  have hμ := (bindingEnergy_lt_three hD).2
  have hμ0 := hM.depth_pos
  have hK : 2 * Real.log (2 * (D : ℝ)) + 3 +
      bindingEnergy D * (bindingEnergy D + (2 * Real.log (2 * (D : ℝ)) + 3)) / 1 ≤
        8 * Real.log (2 * (D : ℝ)) + 21 := by
    rw [div_one]
    nlinarith [mul_nonneg (sub_nonneg.mpr hμ.le) hΛ.le,
      mul_nonneg hμ0.le (sub_nonneg.mpr hμ.le)]
  exact h.trans (mul_le_mul_of_nonneg_right hK hg)

/-- **The sliver blocks of the Green matrix from below**: on the vectors that vanish on a
sub-window `(D + s, D + s + J']` of ratio at least `4/3`,
`‖w‖² ≤ (152 log 2D + 453) ⟨w, G_D w⟩`. -/
theorem greenMatrix_form_ge_of_sliver {D s J' : ℕ} (hJ' : 1 ≤ J') (hs : s + J' ≤ D)
    (hbind : D + s ≤ 3 * J') {w : Fin D → ℝ} (hw : ∀ i : Fin J', w (shiftFin s hs i) = 0) :
    w ⬝ᵥ w ≤ (152 * Real.log (2 * (D : ℝ)) + 453) * (w ⬝ᵥ (greenMatrix D *ᵥ w)) := by
  have hD : 1 ≤ D := by omega
  obtain ⟨ψ, ν, -, hT, hν⟩ := exists_oneBoundState_neutralWindow_of_ratio (Q := 2)
    (R := D + s) hJ' (by omega) hbind le_rfl
  have hsub : OneBoundState ((primeFreeMiddle D).submatrix (shiftFin s hs) (shiftFin s hs))
      ψ ν (1 / 5000) := by
    rw [← neutralWindow_dyadic_eq 2 D, neutralWindow_submatrix_shiftFin]
    exact hT
  have hM := oneBoundState_primeFreeMiddle hD
  have hΛ := two_mul_log_add_three_pos hD
  have hinj : Function.Injective (shiftFin s hs) := fun i j hij => by
    have h1 := congrArg Fin.val hij
    simp only [shiftFin] at h1
    exact Fin.ext (by omega)
  have h := inv_form_ge_of_comp_eq_zero hM hΛ.le (primeFreeMiddle_form_le hD) hinj hsub
    (funext hw)
  have hg : 0 ≤ w ⬝ᵥ (greenMatrix D *ᵥ w) := greenMatrix_nonneg_of_sliver hJ' hs hbind hw
  have hμ := (bindingEnergy_lt_three hD).2
  have hμ0 := hM.depth_pos
  have hνpos : 0 < ν := by linarith
  have hprod : bindingEnergy D * (bindingEnergy D + (2 * Real.log (2 * (D : ℝ)) + 3)) ≤
      3 * (3 + (2 * Real.log (2 * (D : ℝ)) + 3)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hμ.le) hΛ.le,
      mul_nonneg hμ0.le (sub_nonneg.mpr hμ.le)]
  have hprod0 : 0 ≤ bindingEnergy D * (bindingEnergy D + (2 * Real.log (2 * (D : ℝ)) + 3)) :=
    mul_nonneg hμ0.le (by linarith)
  have hdiv : bindingEnergy D * (bindingEnergy D + (2 * Real.log (2 * (D : ℝ)) + 3)) / ν ≤
      25 * (bindingEnergy D * (bindingEnergy D + (2 * Real.log (2 * (D : ℝ)) + 3))) := by
    rw [div_le_iff₀ hνpos]
    nlinarith [mul_nonneg hprod0 (by linarith : (0 : ℝ) ≤ 25 * ν - 1)]
  have hK : 2 * Real.log (2 * (D : ℝ)) + 3 +
      bindingEnergy D * (bindingEnergy D + (2 * Real.log (2 * (D : ℝ)) + 3)) / ν ≤
        152 * Real.log (2 * (D : ℝ)) + 453 := by linarith
  exact h.trans (mul_le_mul_of_nonneg_right hK hg)

/-- **The diagonal of the Green matrix of the middle is positive at every block size
`D ≥ 2`**, and at least `1/(152 log 2D + 453)`. -/
theorem greenMatrix_diag_ge {D : ℕ} (hD : 2 ≤ D) (i : Fin D) :
    1 ≤ (152 * Real.log (2 * (D : ℝ)) + 453) * greenMatrix D i i := by
  have h1 : (Pi.single i 1 : Fin D → ℝ) ⬝ᵥ Pi.single i 1 = 1 := by
    have h := single_dotProduct_mulVec_single (1 : Matrix (Fin D) (Fin D) ℝ) i
    rwa [Matrix.one_mulVec, Matrix.one_apply_eq] at h
  suffices key : (Pi.single i 1 : Fin D → ℝ) ⬝ᵥ Pi.single i 1 ≤
      (152 * Real.log (2 * (D : ℝ)) + 453) *
        ((Pi.single i 1 : Fin D → ℝ) ⬝ᵥ (greenMatrix D *ᵥ Pi.single i 1)) by
    rwa [h1, single_dotProduct_mulVec_single] at key
  by_cases hi : 2 * (i : ℕ) + 2 ≤ D
  · -- the bulk above the block
    have hs : (i : ℕ) + 1 + (D - ((i : ℕ) + 1)) ≤ D := by omega
    refine greenMatrix_form_ge_of_sliver (s := (i : ℕ) + 1) (J' := D - ((i : ℕ) + 1))
      (by omega) hs (by omega) fun k => Pi.single_eq_of_ne (fun h => ?_) _
    have h2 := congrArg Fin.val h
    simp only [shiftFin] at h2
    omega
  · -- the bulk below the block
    have hs : 0 + (i : ℕ) ≤ D := by have := i.2; omega
    refine greenMatrix_form_ge_of_sliver (s := 0) (J' := (i : ℕ)) (by omega) hs
      (by have := i.2; omega) fun k => Pi.single_eq_of_ne (fun h => ?_) _
    have h2 := congrArg Fin.val h
    simp only [shiftFin] at h2
    have := k.2
    omega

/-- **The contact form of the one-prime range from below**: at every block size it is at least
`‖𝒞e‖² / (152 log 2D + 453)`, `D = R + a`. -/
theorem contactGreen_ge {Q R a b : ℕ} (hR : 1 ≤ R) (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R)
    (e : Fin a ⊕ Fin b → ℝ) :
    (endContact Q R a b *ᵥ e) ⬝ᵥ (endContact Q R a b *ᵥ e) ≤
      (152 * Real.log (2 * ((R + a : ℕ) : ℝ)) + 453) * contactGreen Q R a b e := by
  have hs : (b + 1) / 2 + (R - a - (b + 1) / 2) ≤ R + a := by omega
  exact greenMatrix_form_ge_of_sliver (D := R + a) (s := (b + 1) / 2)
    (J' := R - a - (b + 1) / 2) (by omega) hs (by omega) (endContact_mulVec_bulk Q R a b hs e)

/-! ### The overlap law in charge form -/

/-- **The Schur complement of the middle in charge form**: the form of the ends, plus the
repulsion `(Σ Pe)² / (D · |N(1, 1)|)` through the charge of the middle, minus the Green form of
the neutralized coupling. -/
theorem overlapSchur_form_eq_charge (Q R a b : ℕ) (hD : 1 ≤ R + a) (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) =
      e ⬝ᵥ (endForm Q R a b *ᵥ e) -
        (∑ m, (endCoupling Q R a b *ᵥ e) m) ^ 2 / (((R + a : ℕ) : ℝ) * neutralBlock 1 1 1) -
        neutralize (R + a) (endCoupling Q R a b *ᵥ e) ⬝ᵥ
          (greenMatrix (R + a) *ᵥ neutralize (R + a) (endCoupling Q R a b *ᵥ e)) := by
  rw [overlapSchur, Matrix.sub_mulVec, dotProduct_sub, dotProduct_transpose_mul_mul_mulVec,
    greenMatrix_form_eq_charge hD]
  ring

/-- **The Riemann hypothesis in charge form.** It holds iff on the two ends of every window
`(R, 2(R + a) + b]` with `R ≥ 34` the Green form of the neutralized coupling to the dyadic
middle is at most the form of the ends plus the repulsion through the charge of the middle.
The Green matrix enters only through charge-free packets, where it is positive definite. -/
theorem riemannHypothesis_iff_forall_chargeForm :
    RiemannHypothesis ↔ ∀ Q R a b : ℕ, 34 ≤ R → 1 ≤ a → 1 ≤ b →
      R + (a + (R + a) + b) ≤ Q * R → ∀ e : Fin a ⊕ Fin b → ℝ,
        neutralize (R + a) (endCoupling Q R a b *ᵥ e) ⬝ᵥ
            (greenMatrix (R + a) *ᵥ neutralize (R + a) (endCoupling Q R a b *ᵥ e)) ≤
          e ⬝ᵥ (endForm Q R a b *ᵥ e) -
            (∑ m, (endCoupling Q R a b *ᵥ e) m) ^ 2 /
              (((R + a : ℕ) : ℝ) * neutralBlock 1 1 1) := by
  rw [riemannHypothesis_iff_forall_overlapSchur_nonneg]
  refine forall_congr' fun Q => forall_congr' fun R => forall_congr' fun a =>
    forall_congr' fun b => forall_congr' fun hR => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => forall_congr' fun e => ?_
  rw [overlapSchur_form_eq_charge Q R a b (by omega) e, sub_nonneg]

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
