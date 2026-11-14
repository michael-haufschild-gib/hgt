import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.AWindowGluesItsTwoOverlappingPartsThroughItsDyadicMiddle
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnANarrowWindowThePotentialIsShallowAndTheCountOfBoundStatesIsOne
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFirstBlockMatricesOfRatioFourAndSevenHaveAMargin

/-!
# The Green matrix of the dyadic middle has a bound-state channel and a positive channel

The overlap law glues a window `(R, 2D + b]`, `D = R + a`, from its two parts through its dyadic
middle `(D, 2D]`. The mediator of the gluing is the inverse of the neutral part of the middle.

* **The middle is prime-free** (`neutralWindow_dyadic_eq`): between two blocks of `(D, 2D]` no
  floor map acts, so the neutral part of the middle is one matrix `primeFreeMiddle D` for every
  `Q` and every window.
* **One bound state.** A symmetric matrix `M` with a unit eigenvector `φ` of eigenvalue `−μ < 0`
  and a floor `c > 0` on the orthogonal complement of `φ` (`OneBoundState`) is invertible, and
  its inverse splits as `M⁻¹ = −φφᵀ/μ + G₊` with `0 ≤ G₊ ≤ 1/c` and `G₊ φ = 0`
  (`positiveChannel_nonneg`, `positiveChannel_le`, `positiveChannel_mulVec_ground`): the
  **bound-state channel** and the **positive channel**.
* **The middle.** `primeFreeMiddle D` has one bound state with a positive ground vector, floor
  `1/5000` and binding energy `μ_D ≥ −N(1, 1) > 1` at every block size (`groundPair_spec`,
  `one_lt_bindingEnergy`). The floor is the certified floor of the charge-free packets, carried
  to the orthogonal complement of the ground vector (`floor_orthogonal_of_floor_hyperplane`).
* **Schur complements in two channels** (`schur_form_eq_channels`): eliminating the middle from
  boundary data `P` gives `N + (Pᵀφ)(Pᵀφ)ᵀ/μ − PᵀG₊P`. Through the bound state the boundary is
  repelled, through the positive channel it is attracted.
* **The Riemann hypothesis in Green form** (`riemannHypothesis_iff_forall_greenForm`): it holds
  iff on the two ends of every window `(R, 2(R + a) + b]`, `R ≥ 34`, the attraction through the
  positive channel of the middle is at most the neutral form of the ends plus the repulsion
  through its bound state.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Symmetric matrices with one bound state -/

section Channels

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_symm {M : Matrix ι ι ℝ} (hM : ∀ i j, M i j = M j i) (x y : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have hMt : Mᵀ = M := Matrix.ext fun i j => hM j i
  rw [Matrix.dotProduct_mulVec, ← hMt, Matrix.vecMul_transpose, hMt, dotProduct_comm]

/-- A symmetric matrix **with one bound state**: a unit eigenvector `φ` of eigenvalue `−μ < 0`
and a floor `c > 0` of the form on the orthogonal complement of `φ`. -/
structure OneBoundState (M : Matrix ι ι ℝ) (φ : ι → ℝ) (μ c : ℝ) : Prop where
  symm : ∀ i j, M i j = M j i
  unit : φ ⬝ᵥ φ = 1
  eig : M *ᵥ φ = (-μ) • φ
  depth_pos : 0 < μ
  floor_pos : 0 < c
  floor : ∀ z : ι → ℝ, φ ⬝ᵥ z = 0 → c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (M *ᵥ z)

namespace OneBoundState

variable {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

theorem dot_mulVec (h : OneBoundState M φ μ c) (x : ι → ℝ) :
    φ ⬝ᵥ (M *ᵥ x) = -μ * (φ ⬝ᵥ x) := by
  rw [dotProduct_mulVec_symm h.symm, h.eig, dotProduct_smul, smul_eq_mul, dotProduct_comm]

/-- The component of `x` orthogonal to the ground vector. -/
def perp (φ x : ι → ℝ) : ι → ℝ := x - (φ ⬝ᵥ x) • φ

theorem dot_perp (h : OneBoundState M φ μ c) (x : ι → ℝ) : φ ⬝ᵥ perp φ x = 0 := by
  rw [perp, dotProduct_sub, dotProduct_smul, h.unit, smul_eq_mul, mul_one, sub_self]

theorem perp_dot_perp (h : OneBoundState M φ μ c) (x : ι → ℝ) :
    perp φ x ⬝ᵥ perp φ x = x ⬝ᵥ x - (φ ⬝ᵥ x) ^ 2 := by
  have h1 : perp φ x ⬝ᵥ perp φ x = x ⬝ᵥ perp φ x - (φ ⬝ᵥ x) * (φ ⬝ᵥ perp φ x) := by
    change (x - (φ ⬝ᵥ x) • φ) ⬝ᵥ perp φ x = _
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [h1, h.dot_perp, mul_zero, sub_zero, perp, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_comm x φ]
  ring

/-- **The form splits along the ground vector**: minus the depth on the ground vector, plus the
form on the orthogonal component. -/
theorem form_eq (h : OneBoundState M φ μ c) (x : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = -μ * (φ ⬝ᵥ x) ^ 2 + perp φ x ⬝ᵥ (M *ᵥ perp φ x) := by
  have hM : M *ᵥ perp φ x = M *ᵥ x - (φ ⬝ᵥ x) • ((-μ) • φ) := by
    rw [perp, Matrix.mulVec_sub, Matrix.mulVec_smul, h.eig]
  have hx : x ⬝ᵥ φ = φ ⬝ᵥ x := dotProduct_comm _ _
  rw [hM, perp]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    h.dot_mulVec, h.unit, hx]
  ring

/-- The form is at least minus the depth on the ground vector plus the floor elsewhere. -/
theorem form_ge (h : OneBoundState M φ μ c) (x : ι → ℝ) :
    -μ * (φ ⬝ᵥ x) ^ 2 + c * (x ⬝ᵥ x - (φ ⬝ᵥ x) ^ 2) ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [h.form_eq x, ← h.perp_dot_perp x]
  linarith [h.floor _ (h.dot_perp x)]

variable [DecidableEq ι]

/-- A matrix with one bound state is invertible. -/
theorem isUnit (h : OneBoundState M φ μ c) : IsUnit M := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hw0 : M *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  suffices hwz : x - y = 0 from sub_eq_zero.mp hwz
  generalize x - y = w at hw0 ⊢
  have ht : φ ⬝ᵥ w = 0 := by
    have h1 := h.dot_mulVec w
    rw [hw0, dotProduct_zero] at h1
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · linarith [h.depth_pos]
    · exact h2
  have hf := h.floor w ht
  rw [hw0, dotProduct_zero] at hf
  have hww : w ⬝ᵥ w = 0 :=
    le_antisymm (by nlinarith [h.floor_pos]) (dotProduct_self_star_nonneg (v := w))
  exact dotProduct_self_eq_zero.mp hww

theorem mulVec_inv_mulVec (h : OneBoundState M φ μ c) (w : ι → ℝ) : M *ᵥ (M⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).mp h.isUnit),
    Matrix.one_mulVec]

theorem inv_mulVec_mulVec (h : OneBoundState M φ μ c) (w : ι → ℝ) : M⁻¹ *ᵥ (M *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).mp h.isUnit),
    Matrix.one_mulVec]

/-- **The bound-state channel**: the inverse acts on the ground vector by `−1/μ`. -/
theorem inv_mulVec_ground (h : OneBoundState M φ μ c) : M⁻¹ *ᵥ φ = (-(1 / μ)) • φ := by
  have h1 : M *ᵥ ((-(1 / μ)) • φ) = φ := by
    rw [Matrix.mulVec_smul, h.eig, smul_smul]
    have : -(1 / μ) * -μ = 1 := by
      field_simp [h.depth_pos.ne']
    rw [this, one_smul]
  conv_lhs => rw [← h1]
  exact h.inv_mulVec_mulVec _

end OneBoundState

variable [DecidableEq ι]

/-- **The positive channel** of a matrix with one bound state: its inverse with the bound-state
channel `−φφᵀ/μ` removed. -/
def positiveChannel (M : Matrix ι ι ℝ) (φ : ι → ℝ) (μ : ℝ) : Matrix ι ι ℝ :=
  M⁻¹ + (1 / μ) • vecMulVec φ φ

theorem positiveChannel_mulVec (M : Matrix ι ι ℝ) (φ : ι → ℝ) (μ : ℝ) (w : ι → ℝ) :
    positiveChannel M φ μ *ᵥ w = M⁻¹ *ᵥ w + ((1 / μ) * (φ ⬝ᵥ w)) • φ := by
  rw [positiveChannel, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  congr 1
  ext i
  simp only [Pi.smul_apply, op_smul_eq_mul, smul_eq_mul]
  ring

variable {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

/-- The positive channel does not see the ground vector. -/
theorem positiveChannel_mulVec_ground (h : OneBoundState M φ μ c) :
    positiveChannel M φ μ *ᵥ φ = 0 := by
  rw [positiveChannel_mulVec, h.inv_mulVec_ground, h.unit, mul_one, ← add_smul, neg_add_cancel,
    zero_smul]

/-- **The form of the positive channel** at `w` is the form of the matrix on the component of
`M⁻¹ w` orthogonal to the ground vector. -/
theorem positiveChannel_form (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    w ⬝ᵥ (positiveChannel M φ μ *ᵥ w) =
      OneBoundState.perp φ (M⁻¹ *ᵥ w) ⬝ᵥ (M *ᵥ OneBoundState.perp φ (M⁻¹ *ᵥ w)) := by
  set g := M⁻¹ *ᵥ w with hg
  have hMg : M *ᵥ g = w := h.mulVec_inv_mulVec w
  have hφw : φ ⬝ᵥ w = -μ * (φ ⬝ᵥ g) := by rw [← hMg, h.dot_mulVec]
  have hwg : w ⬝ᵥ g = g ⬝ᵥ (M *ᵥ g) := by rw [hMg, dotProduct_comm]
  have hsplit := h.form_eq g
  rw [positiveChannel_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm w φ,
    hwg, hφw]
  have hμ := h.depth_pos.ne'
  have e : 1 / μ * (-μ * (φ ⬝ᵥ g)) * (-μ * (φ ⬝ᵥ g)) = μ * (φ ⬝ᵥ g) ^ 2 := by
    field_simp
  rw [e]
  linarith

/-- **The positive channel is nonnegative.** -/
theorem positiveChannel_nonneg (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    0 ≤ w ⬝ᵥ (positiveChannel M φ μ *ᵥ w) := by
  rw [positiveChannel_form h]
  have h1 := h.floor _ (h.dot_perp (M⁻¹ *ᵥ w))
  have h2 : 0 ≤ OneBoundState.perp φ (M⁻¹ *ᵥ w) ⬝ᵥ OneBoundState.perp φ (M⁻¹ *ᵥ w) :=
    dotProduct_self_star_nonneg (v := OneBoundState.perp φ (M⁻¹ *ᵥ w))
  nlinarith [h.floor_pos]

/-- **The positive channel is at most the inverse of the floor**, on the component of `w`
orthogonal to the ground vector. -/
theorem positiveChannel_le (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    w ⬝ᵥ (positiveChannel M φ μ *ᵥ w) ≤ (1 / c) * (w ⬝ᵥ w - (φ ⬝ᵥ w) ^ 2) := by
  rw [positiveChannel_form h]
  set g := M⁻¹ *ᵥ w with hg
  set z := OneBoundState.perp φ g with hz
  have hMg : M *ᵥ g = w := h.mulVec_inv_mulVec w
  have hφz : φ ⬝ᵥ z = 0 := h.dot_perp g
  -- the form on `z` is its pairing with the component of `w` orthogonal to the ground vector
  have hMz : M *ᵥ z = w + (μ * (φ ⬝ᵥ g)) • φ := by
    rw [hz, OneBoundState.perp, Matrix.mulVec_sub, Matrix.mulVec_smul, h.eig, hMg, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have hQ : z ⬝ᵥ (M *ᵥ z) = z ⬝ᵥ OneBoundState.perp φ w := by
    rw [hMz, dotProduct_add, dotProduct_smul, dotProduct_comm z φ, hφz, smul_zero, add_zero,
      OneBoundState.perp, dotProduct_sub, dotProduct_smul, dotProduct_comm z φ, hφz, smul_zero,
      sub_zero]
  have hfloor := h.floor z hφz
  have hcs : (z ⬝ᵥ OneBoundState.perp φ w) ^ 2 ≤
      (z ⬝ᵥ z) * (OneBoundState.perp φ w ⬝ᵥ OneBoundState.perp φ w) := by
    simp only [dotProduct]
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z (OneBoundState.perp φ w)
    simpa only [sq] using this
  have hn : 0 ≤ OneBoundState.perp φ w ⬝ᵥ OneBoundState.perp φ w :=
    dotProduct_self_star_nonneg (v := OneBoundState.perp φ w)
  rw [h.perp_dot_perp w] at hcs hn
  rw [hQ] at hfloor ⊢
  set q := z ⬝ᵥ OneBoundState.perp φ w
  set n := w ⬝ᵥ w - (φ ⬝ᵥ w) ^ 2
  have hc := h.floor_pos
  have hzz : 0 ≤ z ⬝ᵥ z := dotProduct_self_star_nonneg (v := z)
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
  by_contra hlt
  rw [not_le] at hlt
  -- `q c > n ≥ 0` and `c z·z ≤ q` contradict Cauchy–Schwarz
  have hq : 0 < q := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hfloor hn, mul_pos hq hc]

/-- **The Schur complement over a matrix with one bound state, in two channels**: the boundary
data `P` are repelled through the bound state and attracted through the positive channel. -/
theorem schur_form_eq_channels (h : OneBoundState M φ μ c) (P : Matrix ι κ ℝ)
    (N : Matrix κ κ ℝ) (e : κ → ℝ) :
    e ⬝ᵥ ((N - Pᵀ * M⁻¹ * P) *ᵥ e) =
      e ⬝ᵥ (N *ᵥ e) + (φ ⬝ᵥ (P *ᵥ e)) ^ 2 / μ -
        (P *ᵥ e) ⬝ᵥ (positiveChannel M φ μ *ᵥ (P *ᵥ e)) := by
  have h1 : e ⬝ᵥ ((Pᵀ * M⁻¹ * P) *ᵥ e) = (P *ᵥ e) ⬝ᵥ (M⁻¹ *ᵥ (P *ᵥ e)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, positiveChannel_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, dotProduct_comm (P *ᵥ e) φ]
  have hμ := h.depth_pos.ne'
  field_simp
  ring

omit [DecidableEq ι] in
/-- **A floor on a hyperplane is a floor on the orthogonal complement of the ground vector.**
If `φ` is an eigenvector of eigenvalue `−μ ≤ 0` and the form is at least `c ≥ 0` on the kernel
of a functional that does not vanish at `φ`, it is at least `c` on the orthogonal complement of
`φ`. -/
theorem floor_orthogonal_of_floor_hyperplane (hM : ∀ i j, M i j = M j i) (hμ : 0 ≤ μ)
    (hc : 0 ≤ c) (heig : M *ᵥ φ = (-μ) • φ) {ℓ : ι → ℝ} (hℓ : ℓ ⬝ᵥ φ ≠ 0)
    (hfloor : ∀ y : ι → ℝ, ℓ ⬝ᵥ y = 0 → c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (M *ᵥ y)) (z : ι → ℝ)
    (hz : φ ⬝ᵥ z = 0) : c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (M *ᵥ z) := by
  set α := -(ℓ ⬝ᵥ z) with hα
  set β := ℓ ⬝ᵥ φ with hβ
  have hy0 : ℓ ⬝ᵥ (α • φ + β • z) = 0 := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hβ, hα]
    ring
  have hf := hfloor _ hy0
  have hzφ : z ⬝ᵥ φ = 0 := (dotProduct_comm _ _).trans hz
  have hφMz : φ ⬝ᵥ (M *ᵥ z) = 0 := by
    rw [dotProduct_mulVec_symm hM, heig, dotProduct_smul, hzφ, smul_zero]
  have hnorm : (α • φ + β • z) ⬝ᵥ (α • φ + β • z) = α ^ 2 * (φ ⬝ᵥ φ) + β ^ 2 * (z ⬝ᵥ z) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hz, hzφ]
    ring
  have hform : (α • φ + β • z) ⬝ᵥ (M *ᵥ (α • φ + β • z)) =
      -μ * α ^ 2 * (φ ⬝ᵥ φ) + β ^ 2 * (z ⬝ᵥ (M *ᵥ z)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, heig, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hzφ, hφMz]
    ring
  rw [hnorm, hform] at hf
  have hφφ : 0 ≤ φ ⬝ᵥ φ := dotProduct_self_star_nonneg (v := φ)
  have hβ2 : 0 < β ^ 2 := by positivity
  have hα2 : 0 ≤ α ^ 2 * (φ ⬝ᵥ φ) := mul_nonneg (sq_nonneg _) hφφ
  have key : β ^ 2 * (c * (z ⬝ᵥ z)) ≤ β ^ 2 * (z ⬝ᵥ (M *ᵥ z)) := by
    nlinarith [mul_nonneg hμ hα2, mul_nonneg hc hα2]
  exact le_of_mul_le_mul_left key hβ2

end Channels

/-! ### The dyadic middle -/

/-- **The neutral part of the dyadic window `(D, 2D]`**: density on the diagonal minus the jets.
No floor map acts between two of its blocks. -/
def primeFreeMiddle (D : ℕ) : Matrix (Fin D) (Fin D) ℝ := neutralWindow 1 D D

/-- **The middle is prime-free**: the neutral part of a dyadic window does not depend on the
contacts admitted. -/
theorem neutralWindow_dyadic_eq (Q D : ℕ) : neutralWindow Q D D = primeFreeMiddle D := by
  ext i j
  have h : max (D + (i : ℕ)) (D + (j : ℕ)) < 2 * min (D + (i : ℕ)) (D + (j : ℕ)) := by
    have hi := i.2
    have hj := j.2
    omega
  simp only [primeFreeMiddle, neutralWindow, windowMatrix, Matrix.of_apply]
  rw [neutralBlock_eq_of_lt_two_mul h, neutralBlock_eq_of_lt_two_mul h]

theorem primeFreeMiddle_symm (D : ℕ) (i j : Fin D) :
    primeFreeMiddle D i j = primeFreeMiddle D j i := neutralWindow_symm 1 D D i j

/-- **The certified floor of the middle**: on charge-free packets the neutral part of a dyadic
window is at least `1/5000`. -/
theorem primeFreeMiddle_floor_of_sum_eq_zero {D : ℕ} (hD : 1 ≤ D) (z : Fin D → ℝ)
    (hz : ∑ i, z i = 0) : 1 / 5000 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (primeFreeMiddle D *ᵥ z) := by
  rw [← neutralWindow_dyadic_eq 2 D, AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    neutralWindow, sum_fin_windowMatrix_eq,
    show z ⬝ᵥ z = ∑ j ∈ range D, extendFin (fun i => z i ^ 2) j by
      rw [← sum_fin_eq_sum_range_extendFin]
      exact Finset.sum_congr rfl fun i _ => (sq _).symm]
  have h := sum_neutralBlock_ge_of_short (R := D) (J := D) hD (by omega) (le_refl 2)
    (σ := extendFin z) (Or.inl ((sum_fin_eq_sum_range_extendFin z).symm.trans hz))
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [extendFin, extendFin, dif_pos (Finset.mem_range.mp hj), dif_pos (Finset.mem_range.mp hj)]

/-- The value of the neutral part on the first block: `3 log 3 − 4 log 2 − γ − log π`. -/
theorem neutralBlock_one_one_eq (Q : ℕ) :
    neutralBlock Q 1 1 = 3 * Real.log 3 - 4 * Real.log 2 - Real.eulerMascheroniConstant -
      Real.log Real.pi := by
  have h2 : xLogX (1 + 1) = 2 * Real.log 2 := by
    unfold xLogX
    norm_num
  have h1 : xLogX 1 = 0 := by
    unfold xLogX
    simp
  have h3 : xLogX 3 = 3 * Real.log 3 := by
    unfold xLogX
    norm_num
  have h4 : xLogX 4 = 8 * Real.log 2 := by
    unfold xLogX
    rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, log_four]
    ring
  rw [neutralBlock, blockMatrix_self le_rfl, blockJet, Nat.sub_self, xLogXDiff_zero, blockDensity,
    xLogXDiff, show 1 + 1 + 1 + 1 = 4 by norm_num, show 1 + 1 + 1 - 1 = 2 by norm_num,
    show 1 + 1 + 1 = 3 by norm_num, h1, h3, h4, show xLogX 2 = 2 * Real.log 2 from h2,
    log_two_pi]
  ring

/-- **The flat packet of a dyadic window binds more than one unit.** -/
theorem neutralBlock_one_one_lt (Q : ℕ) : neutralBlock Q 1 1 < -1 := by
  rw [neutralBlock_one_one_eq]
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hπ : Real.log 3 < Real.log Real.pi := Real.log_lt_log (by norm_num) Real.pi_gt_three
  have h3 := log_three_mem.2
  have h2 := Real.log_two_gt_d9
  linarith

/-- **The ground pair of the dyadic middle.** At every block size the neutral part of the dyadic
window has a positive unit ground vector, floor `1/5000` on its orthogonal complement, and a
binding energy at least that of the flat packet. -/
theorem exists_groundPair {D : ℕ} (hD : 1 ≤ D) :
    ∃ φ : Fin D → ℝ, ∃ μ : ℝ, (∀ i, 0 < φ i) ∧
      OneBoundState (primeFreeMiddle D) φ μ (1 / 5000) ∧ -neutralBlock 1 1 1 ≤ μ := by
  obtain ⟨φ₀, hφ₀, lam, heig⟩ := exists_groundVector_neutralWindow 1 D hD
  have hsymm := neutralWindow_symm 1 D D
  have hoff : ∀ i j : Fin D, i ≠ j → neutralWindow 1 D D i j ≤ 0 := fun _ _ hij =>
    (neutralWindow_neg_of_ne 1 D hij).le
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  -- the flat packet bounds the eigenvalue
  have hlam : lam ≤ neutralBlock 1 1 1 := by
    have h1 := lam_mul_sum_sq_le_bilin hsymm hoff hφ₀ heig (fun _ => (1 : ℝ))
    have h2 : bilin (neutralWindow 1 D D) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) =
        D * neutralBlock 1 1 1 := by
      rw [← sum_neutralBlock_dyadic 1 hD]
      have hc := sum_fin_windowMatrix_coe (neutralBlock 1) D D (fun _ => 1)
      simp only [one_mul] at hc
      rw [← hc]
      simp only [bilin, one_mul, neutralWindow]
    rw [h2] at h1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at h1
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    nlinarith
  have hμ : 0 < -lam := by linarith [neutralBlock_one_one_neg 1]
  -- normalization
  have hs2 : 0 < φ₀ ⬝ᵥ φ₀ :=
    Finset.sum_pos (fun i _ => mul_pos (hφ₀ i) (hφ₀ i)) Finset.univ_nonempty
  set s := Real.sqrt (φ₀ ⬝ᵥ φ₀) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hs2
  have hss : s * s = φ₀ ⬝ᵥ φ₀ := Real.mul_self_sqrt hs2.le
  set φ : Fin D → ℝ := s⁻¹ • φ₀ with hφdef
  have hφpos : ∀ i, 0 < φ i := fun i => by
    simp only [hφdef, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hspos) (hφ₀ i)
  have hunit : φ ⬝ᵥ φ = 1 := by
    rw [hφdef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  have heig' : primeFreeMiddle D *ᵥ φ = (-(-lam)) • φ := by
    rw [neg_neg, hφdef, primeFreeMiddle, Matrix.mulVec_smul, heig, smul_comm]
  -- the floor on the orthogonal complement, from the floor on charge-free packets
  have hones : (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ φ ≠ 0 := by
    have : 0 < (fun _ : Fin D => (1 : ℝ)) ⬝ᵥ φ := by
      simp only [dotProduct, one_mul]
      exact Finset.sum_pos (fun i _ => hφpos i) Finset.univ_nonempty
    exact this.ne'
  have hfloor := floor_orthogonal_of_floor_hyperplane (primeFreeMiddle_symm D) hμ.le
    (by norm_num : (0 : ℝ) ≤ 1 / 5000) heig' hones fun y hy =>
      primeFreeMiddle_floor_of_sum_eq_zero hD y (by simpa [dotProduct] using hy)
  exact ⟨φ, -lam, hφpos,
    ⟨primeFreeMiddle_symm D, hunit, heig', hμ, by norm_num, hfloor⟩, by linarith⟩

/-- The ground vector `φ_D` of the dyadic middle. -/
def groundVector (D : ℕ) : Fin D → ℝ :=
  if h : 1 ≤ D then (exists_groundPair h).choose else 0

/-- The binding energy `μ_D` of the dyadic middle. -/
def bindingEnergy (D : ℕ) : ℝ :=
  if h : 1 ≤ D then (exists_groundPair h).choose_spec.choose else 1

theorem groundPair_spec {D : ℕ} (hD : 1 ≤ D) :
    (∀ i, 0 < groundVector D i) ∧
      OneBoundState (primeFreeMiddle D) (groundVector D) (bindingEnergy D) (1 / 5000) ∧
      -neutralBlock 1 1 1 ≤ bindingEnergy D := by
  have h := (exists_groundPair hD).choose_spec.choose_spec
  simpa only [groundVector, bindingEnergy, dif_pos hD] using h

theorem oneBoundState_primeFreeMiddle {D : ℕ} (hD : 1 ≤ D) :
    OneBoundState (primeFreeMiddle D) (groundVector D) (bindingEnergy D) (1 / 5000) :=
  (groundPair_spec hD).2.1

/-- **The binding energy of the dyadic middle exceeds one at every block size.** -/
theorem one_lt_bindingEnergy {D : ℕ} (hD : 1 ≤ D) : 1 < bindingEnergy D := by
  linarith [(groundPair_spec hD).2.2, neutralBlock_one_one_lt 1]

/-- **The Green matrix of the dyadic middle.** -/
def greenMatrix (D : ℕ) : Matrix (Fin D) (Fin D) ℝ := (primeFreeMiddle D)⁻¹

/-- **The positive part of the Green matrix**: the Green matrix on the orthogonal complement of
the bound state of the middle. -/
def greenPositive (D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  positiveChannel (primeFreeMiddle D) (groundVector D) (bindingEnergy D)

/-- The Green matrix is the bound-state channel plus the positive part. -/
theorem greenMatrix_eq (D : ℕ) :
    greenMatrix D = greenPositive D -
      (1 / bindingEnergy D) • vecMulVec (groundVector D) (groundVector D) := by
  rw [greenPositive, positiveChannel, greenMatrix, add_sub_cancel_right]

theorem greenMatrix_mulVec_groundVector {D : ℕ} (hD : 1 ≤ D) :
    greenMatrix D *ᵥ groundVector D = (-(1 / bindingEnergy D)) • groundVector D :=
  (oneBoundState_primeFreeMiddle hD).inv_mulVec_ground

theorem greenPositive_mulVec_groundVector {D : ℕ} (hD : 1 ≤ D) :
    greenPositive D *ᵥ groundVector D = 0 :=
  positiveChannel_mulVec_ground (oneBoundState_primeFreeMiddle hD)

theorem greenPositive_nonneg {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    0 ≤ w ⬝ᵥ (greenPositive D *ᵥ w) :=
  positiveChannel_nonneg (oneBoundState_primeFreeMiddle hD) w

/-- **The a priori bound of the positive part**: the certified floor of the middle bounds it by
`5000`. -/
theorem greenPositive_le {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ (greenPositive D *ᵥ w) ≤ 5000 * (w ⬝ᵥ w - (groundVector D ⬝ᵥ w) ^ 2) := by
  have h := positiveChannel_le (oneBoundState_primeFreeMiddle hD) w
  rwa [one_div_one_div] at h

/-! ### The overlap law in Green form -/

/-- The couplings of the middle `(R + a, 2(R + a)]` to the two ends of `(R, 2(R + a) + b]`. -/
def endCoupling (Q R a b : ℕ) : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ :=
  joinColumns (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))
    (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))

/-- The neutral form on the two ends of `(R, 2(R + a) + b]`. -/
def endForm (Q R a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  fromBlocks (posMatrix (neutralBlock Q) (leftPos R a) (leftPos R a))
    (posMatrix (neutralBlock Q) (leftPos R a) (rightPos R a b))
    (posMatrix (neutralBlock Q) (leftPos R a) (rightPos R a b))ᵀ
    (posMatrix (neutralBlock Q) (rightPos R a b) (rightPos R a b))

/-- The Schur complement of the dyadic middle in the window `(R, 2(R + a) + b]`: the form the two
ends see after the middle is eliminated. -/
def overlapSchur (Q R a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  endForm Q R a b - (endCoupling Q R a b)ᵀ * greenMatrix (R + a) * endCoupling Q R a b

/-- The Schur complement of the middle consists of the two conditional energies and the
conditional coupling of the overlap law. -/
theorem overlapSchur_eq_fromBlocks (Q R a b : ℕ) :
    overlapSchur Q R a b =
      fromBlocks (overlapLeftEnergy Q R a) (overlapCoupling Q R a b) (overlapCoupling Q R a b)ᵀ
        (overlapRightEnergy Q R a b) := by
  rw [overlapSchur, endForm, endCoupling, greenMatrix, ← neutralWindow_dyadic_eq Q (R + a),
    fromBlocks_sub_joinColumns (neutralWindow_symm Q (R + a) (R + a))]
  rfl

/-- **One bound state of a window is the nonnegativity of the Schur complement of its dyadic
middle.** -/
theorem hermNegIndex_neutralWindow_eq_one_iff_overlapSchur {Q R : ℕ} (a b : ℕ) (hR : 1 ≤ R)
    (hQ : 2 ≤ Q) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 ↔
      ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) := by
  have hD : 1 ≤ R + a := by omega
  have hM := hermNegIndex_neutralWindow_dyadic (Q := Q) hD hQ
  have hsymm : ∀ x y, endForm Q R a b x y = endForm Q R a b y x :=
    fromBlocks_symm (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) _
      (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b))
  have hH := hermNegIndex_fromBlocks_transpose (neutralWindow_symm Q (R + a) (R + a))
    (isUnit_neutralWindow_dyadic hD hQ) (endCoupling Q R a b) hsymm
  rw [← hermNegIndex_map_submatrix _ (overlapEquiv a (R + a) b),
    neutralWindow_submatrix_overlapEquiv, overlapWhole]
  change hermNegIndex ((fromBlocks (neutralWindow Q (R + a) (R + a)) (endCoupling Q R a b)
    (endCoupling Q R a b)ᵀ (endForm Q R a b)).map (↑) : Matrix _ _ ℂ) = 1 ↔ _
  rw [hH, hM, Nat.add_eq_left, hermNegIndex_eq_zero_iff_forall, overlapSchur, greenMatrix,
    neutralWindow_dyadic_eq]

/-- **The Schur complement of the middle in two channels.** -/
theorem overlapSchur_form_eq_channels (Q R a b : ℕ) (hD : 1 ≤ R + a) (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) =
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) -
        (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) :=
  schur_form_eq_channels (oneBoundState_primeFreeMiddle hD) _ _ e

/-- **The Riemann hypothesis in Green form.** It holds iff on the two ends of every window
`(R, 2(R + a) + b]` with `R ≥ 34` the attraction through the positive part of the Green matrix
of the dyadic middle is at most the neutral form of the ends plus the repulsion through the
bound state of the middle. -/
theorem riemannHypothesis_iff_forall_greenForm :
    RiemannHypothesis ↔ ∀ Q R a b : ℕ, 34 ≤ R → 1 ≤ a → 1 ≤ b →
      R + (a + (R + a) + b) ≤ Q * R → ∀ e : Fin a ⊕ Fin b → ℝ,
        (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) ≤
          e ⬝ᵥ (endForm Q R a b *ᵥ e) +
            (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) := by
  have hQ2 : ∀ {Q R a b : ℕ}, 34 ≤ R → R + (a + (R + a) + b) ≤ Q * R → 2 ≤ Q := by
    intro Q R a b hR hQ
    by_contra hlt
    have : Q * R ≤ 1 * R := Nat.mul_le_mul_right R (by omega)
    omega
  constructor
  · intro hRH Q R a b hR ha hb hQ e
    have h1 := (riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one.mp hRH) Q R
      (a + (R + a) + b) (by omega) (by omega) hQ
    have h2 := (hermNegIndex_neutralWindow_eq_one_iff_overlapSchur a b (by omega)
      (hQ2 hR hQ)).mp h1 e
    rw [overlapSchur_form_eq_channels Q R a b (by omega)] at h2
    linarith
  · intro h
    rw [riemannHypothesis_iff_forall_overlap_contraction]
    intro Q R a b hR ha hb hQ
    have hS : ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) := fun e => by
      rw [overlapSchur_form_eq_channels Q R a b (by omega)]
      linarith [h Q R a b hR ha hb hQ e]
    rw [overlapSchur_eq_fromBlocks] at hS
    have h₁ : ∀ u, 0 ≤ u ⬝ᵥ (overlapLeftEnergy Q R a *ᵥ u) := fun u => by
      have := hS (Sum.elim u 0)
      rw [dotProduct_fromBlocks_mulVec] at this
      simpa using this
    have h₃ : ∀ v, 0 ≤ v ⬝ᵥ (overlapRightEnergy Q R a b *ᵥ v) := fun v => by
      have := hS (Sum.elim 0 v)
      rw [dotProduct_fromBlocks_mulVec] at this
      simpa using this
    exact (forall_fromBlocks_nonneg_iff h₁ h₃).mp hS

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
