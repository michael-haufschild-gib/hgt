import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheCertifiedFloorsAreAPrioriBoundsForTheGreenMatrixAndTheConditionalEnergies
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTwoHalvesOfAWindowOfRatioFourDoNotGlueThroughAProductOfCharges

/-!
# The Green form of a bound window grows with the window and along the refinement tower

For a positive definite form the Green function grows with the domain. The neutral part of a
window is not positive: it has one bound state. The monotonicity survives as long as the bound
state is held on both sides.

* **Reversed Cauchy–Schwarz** (`OneBoundState.reverse_cauchy_schwarz`): for a form `M` with one
  bound state and a negative vector `ψ`, `⟨ψ, Mψ⟩⟨y, My⟩ ≤ ⟨y, Mψ⟩²`. In particular `M ⪰ 0` on
  the `M`-orthogonal complement of a negative vector.
* **Compression monotonicity** (`inv_form_compression_le`): if `M'` and its compression
  `M = Tᵀ M' T` both have one bound state, then `T M⁻¹ Tᵀ ⪯ M'⁻¹`. The defect of the two
  solutions is `M'`-orthogonal to the range of `T`, which contains a negative vector.
* **Domain monotonicity** (`inv_form_submatrix_le`, `inv_form_neutralWindow_shift_le`): the Green
  matrix of a bound sub-window, extended by zero, is below the Green matrix of the window. The
  Green matrix of the dyadic middle is below the compression of the inverse of every certified
  window that contains it (`greenMatrix_form_le_neutralWindow_inv`).
* **Windows of ratio between `3/2` and `2` bind** (`sum_neutralBlock_window_le`,
  `exists_oneBoundState_neutralWindow_of_ratio`): the flat packet of `(R, R + J]`, `J ≤ R ≤ 2J`,
  has energy at most `−J/6`; the window has one bound state with floor `1/5000`.
* **The Green matrix is nonnegative on the slivers** (`greenMatrix_nonneg_of_sliver`): on the
  vectors supported on a left sliver of `s` blocks and a right sliver of `s'` blocks of the
  dyadic middle, `3s + 2s' ≤ D`, the Green matrix `G_D` is nonnegative at every block size:
  there the positive channel dominates the bound-state channel
  (`groundVector_sq_le_greenPositive_of_sliver`).
* **The tower law** (`greenMatrix_form_le_refined`, `bindingEnergy_le_refined`): refinement by
  `m` is an isometry that compresses the middle at block size `mD` to the middle at block size
  `D`. Along the refinement tower the Green form and the binding energy increase; the Green
  form stays below `5000` (`greenMatrix_form_refined_le`) and the binding energy below `3`
  (`bindingEnergy_lt_three`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Compressions of a form with one bound state -/

section Compression

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The adjoint of a matrix in the dot product. -/
theorem dotProduct_mulVec_eq_transpose (T : Matrix κ ι ℝ) (x : κ → ℝ) (y : ι → ℝ) :
    x ⬝ᵥ (T *ᵥ y) = (Tᵀ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- A compression of a symmetric matrix is symmetric. -/
theorem transpose_mul_mul_symm {N : Matrix κ κ ℝ} (hN : ∀ i j, N i j = N j i)
    (T : Matrix κ ι ℝ) (i j : ι) : (Tᵀ * N * T) i j = (Tᵀ * N * T) j i := by
  have hNt : Nᵀ = N := Matrix.ext fun i j => hN j i
  have h : (Tᵀ * N * T)ᵀ = Tᵀ * N * T := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hNt,
      Matrix.mul_assoc]
  have h2 := congrFun (congrFun h j) i
  rwa [Matrix.transpose_apply] at h2

variable {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

/-- **The reversed Cauchy–Schwarz inequality of a form with one bound state.** The line through
`y` in the direction of a negative vector `ψ` meets the orthogonal complement of the ground
vector, where the form is nonnegative. -/
theorem OneBoundState.reverse_cauchy_schwarz (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) < 0) (y : ι → ℝ) :
    (ψ ⬝ᵥ (M *ᵥ ψ)) * (y ⬝ᵥ (M *ᵥ y)) ≤ (y ⬝ᵥ (M *ᵥ ψ)) ^ 2 := by
  have ha : φ ⬝ᵥ ψ ≠ 0 := fun h0 => by
    have h1 := h.floor ψ h0
    have h2 : 0 ≤ ψ ⬝ᵥ ψ := dotProduct_self_star_nonneg (v := ψ)
    linarith [mul_nonneg h.floor_pos.le h2]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * (φ ⬝ᵥ ψ) = φ ⬝ᵥ y :=
    ⟨φ ⬝ᵥ y / (φ ⬝ᵥ ψ), div_mul_cancel₀ _ ha⟩
  have hz : φ ⬝ᵥ (y - s • ψ) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hs, sub_self]
  have hnn : 0 ≤ (y - s • ψ) ⬝ᵥ (M *ᵥ (y - s • ψ)) :=
    le_trans (mul_nonneg h.floor_pos.le (dotProduct_self_star_nonneg (v := y - s • ψ)))
      (h.floor _ hz)
  have hexp : (y - s • ψ) ⬝ᵥ (M *ᵥ (y - s • ψ)) =
      y ⬝ᵥ (M *ᵥ y) - 2 * s * (y ⬝ᵥ (M *ᵥ ψ)) + s ^ 2 * (ψ ⬝ᵥ (M *ᵥ ψ)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_mulVec_symm h.symm ψ y]
    ring
  rw [hexp] at hnn
  nlinarith [mul_nonneg (neg_nonneg.mpr hψ.le) hnn,
    sq_nonneg ((ψ ⬝ᵥ (M *ᵥ ψ)) * s - y ⬝ᵥ (M *ᵥ ψ))]

variable [DecidableEq ι] [DecidableEq κ]

/-- Two symmetric matrices with the same quadratic form are equal. -/
theorem matrix_eq_of_forall_form_eq {A B : Matrix ι ι ℝ} (hA : ∀ i j, A i j = A j i)
    (hB : ∀ i j, B i j = B j i) (h : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (B *ᵥ v)) : A = B := by
  have hbil : ∀ u v : ι → ℝ, u ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ (B *ᵥ v) := fun u v => by
    have h1 := h (u + v)
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add] at h1
    rw [dotProduct_mulVec_symm hA v u, dotProduct_mulVec_symm hB v u, h u, h v] at h1
    linarith
  have hvec : ∀ v : ι → ℝ, A *ᵥ v = B *ᵥ v := fun v => by
    have h0 : (A *ᵥ v - B *ᵥ v) ⬝ᵥ (A *ᵥ v - B *ᵥ v) = 0 := by
      rw [dotProduct_sub, hbil, sub_self]
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h0)
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hvec v)

/-- **Compression monotonicity of the Green form.** If a matrix `M'` and its compression
`M = Tᵀ M' T` both have one bound state, then `T M⁻¹ Tᵀ ⪯ M'⁻¹`. -/
theorem inv_form_compression_le {M' : Matrix κ κ ℝ} {φ' : κ → ℝ} {μ' c' : ℝ}
    (h' : OneBoundState M' φ' μ' c') (h : OneBoundState M φ μ c) (T : Matrix κ ι ℝ)
    (hT : Tᵀ * M' * T = M) (w : κ → ℝ) :
    (Tᵀ *ᵥ w) ⬝ᵥ (M⁻¹ *ᵥ (Tᵀ *ᵥ w)) ≤ w ⬝ᵥ (M'⁻¹ *ᵥ w) := by
  have hTM : ∀ v : ι → ℝ, Tᵀ *ᵥ (M' *ᵥ (T *ᵥ v)) = M *ᵥ v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT]
  obtain ⟨u, hu⟩ : ∃ u, u = M'⁻¹ *ᵥ w := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = M⁻¹ *ᵥ (Tᵀ *ᵥ w) := ⟨_, rfl⟩
  have hMu : M' *ᵥ u = w := by rw [hu, h'.mulVec_inv_mulVec]
  have hMv : M *ᵥ v = Tᵀ *ᵥ w := by rw [hv, h.mulVec_inv_mulVec]
  rw [← hu, ← hv]
  -- the defect `u − T v` is `M'`-orthogonal to the range of `T`
  have hTd : Tᵀ *ᵥ (M' *ᵥ (u - T *ᵥ v)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub, hTM, hMu, hMv, sub_self]
  -- the image of the ground vector of `M` is a negative vector of `M'`
  have hψ : (T *ᵥ φ) ⬝ᵥ (M' *ᵥ (T *ᵥ φ)) = -μ := by
    rw [dotProduct_comm, dotProduct_mulVec_eq_transpose, hTM, h.eig, smul_dotProduct, h.unit,
      smul_eq_mul, mul_one]
  have hdψ : (u - T *ᵥ v) ⬝ᵥ (M' *ᵥ (T *ᵥ φ)) = 0 := by
    rw [dotProduct_mulVec_symm h'.symm, dotProduct_comm, dotProduct_mulVec_eq_transpose, hTd,
      zero_dotProduct]
  have hrc := h'.reverse_cauchy_schwarz (ψ := T *ᵥ φ) (by rw [hψ]; linarith [h.depth_pos])
    (u - T *ᵥ v)
  rw [hψ, hdψ] at hrc
  have hd : 0 ≤ (u - T *ᵥ v) ⬝ᵥ (M' *ᵥ (u - T *ᵥ v)) := by
    by_contra hneg
    rw [not_le] at hneg
    linarith [mul_pos h.depth_pos (neg_pos.mpr hneg)]
  -- the difference of the two Green forms is the form of the defect
  have h1 : (T *ᵥ v) ⬝ᵥ (M' *ᵥ (u - T *ᵥ v)) = 0 := by
    rw [dotProduct_comm, dotProduct_mulVec_eq_transpose, hTd, zero_dotProduct]
  have h2 : u ⬝ᵥ (M' *ᵥ (u - T *ᵥ v)) = w ⬝ᵥ (u - T *ᵥ v) := by
    rw [dotProduct_mulVec_symm h'.symm, hMu, dotProduct_comm]
  have hid : (u - T *ᵥ v) ⬝ᵥ (M' *ᵥ (u - T *ᵥ v)) = w ⬝ᵥ u - (Tᵀ *ᵥ w) ⬝ᵥ v := by
    rw [sub_dotProduct, h1, sub_zero, h2, dotProduct_sub, dotProduct_mulVec_eq_transpose]
  linarith

/-- Compression by an isometry: `M⁻¹ ⪯ Tᵀ M'⁻¹ T`. -/
theorem inv_form_le_of_isometry {M' : Matrix κ κ ℝ} {φ' : κ → ℝ} {μ' c' : ℝ}
    (h' : OneBoundState M' φ' μ' c') (h : OneBoundState M φ μ c) (T : Matrix κ ι ℝ)
    (hT : Tᵀ * M' * T = M) (hTT : Tᵀ * T = 1) (w : ι → ℝ) :
    w ⬝ᵥ (M⁻¹ *ᵥ w) ≤ (T *ᵥ w) ⬝ᵥ (M'⁻¹ *ᵥ (T *ᵥ w)) := by
  have h1 := inv_form_compression_le h' h T hT (T *ᵥ w)
  rwa [Matrix.mulVec_mulVec, hTT, Matrix.one_mulVec] at h1

/-- **The binding energy does not decrease under an isometric extension.** -/
theorem OneBoundState.depth_le_of_isometry {M' : Matrix κ κ ℝ} {φ' : κ → ℝ} {μ' c' : ℝ}
    (h' : OneBoundState M' φ' μ' c') (h : OneBoundState M φ μ c) (T : Matrix κ ι ℝ)
    (hT : Tᵀ * M' * T = M) (hTT : Tᵀ * T = 1) : μ ≤ μ' := by
  have hψψ : (T *ᵥ φ) ⬝ᵥ (T *ᵥ φ) = 1 := by
    rw [dotProduct_mulVec_eq_transpose, Matrix.mulVec_mulVec, hTT, Matrix.one_mulVec, h.unit]
  have hψ : (T *ᵥ φ) ⬝ᵥ (M' *ᵥ (T *ᵥ φ)) = -μ := by
    rw [← dotProduct_transpose_mul_mul_mulVec, hT, h.eig, dotProduct_smul, h.unit, smul_eq_mul,
      mul_one]
  have hge := h'.form_ge (T *ᵥ φ)
  have ht := h'.sq_dot_le (T *ᵥ φ)
  rw [hψψ] at hge ht
  rw [hψ] at hge
  nlinarith [mul_nonneg h'.depth_pos.le (sub_nonneg.mpr ht),
    mul_nonneg h'.floor_pos.le (sub_nonneg.mpr ht)]

/-- The matrix of the inclusion of the coordinates `f`. -/
def inclusionMatrix (f : ι → κ) : Matrix κ ι ℝ :=
  Matrix.of fun k i => if k = f i then 1 else 0

omit [Fintype ι] [DecidableEq ι] in
theorem inclusionMatrix_transpose_mulVec (f : ι → κ) (w : κ → ℝ) :
    (inclusionMatrix f)ᵀ *ᵥ w = w ∘ f := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, inclusionMatrix,
    Matrix.of_apply, Function.comp_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

omit [Fintype ι] [DecidableEq ι] in
theorem inclusionMatrix_transpose_mul_mul (f : ι → κ) (M' : Matrix κ κ ℝ) :
    (inclusionMatrix f)ᵀ * M' * inclusionMatrix f = M'.submatrix f f := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, inclusionMatrix, Matrix.of_apply,
    Matrix.submatrix_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Domain monotonicity of the Green form.** If a matrix and a principal submatrix both have
one bound state, the inverse of the submatrix, extended by zero, is below the inverse. -/
theorem inv_form_submatrix_le {M' : Matrix κ κ ℝ} {φ' : κ → ℝ} {μ' c' : ℝ}
    (h' : OneBoundState M' φ' μ' c') (f : ι → κ) (h : OneBoundState (M'.submatrix f f) φ μ c)
    (w : κ → ℝ) :
    (w ∘ f) ⬝ᵥ ((M'.submatrix f f)⁻¹ *ᵥ (w ∘ f)) ≤ w ⬝ᵥ (M'⁻¹ *ᵥ w) := by
  have h1 := inv_form_compression_le h' h (inclusionMatrix f)
    (inclusionMatrix_transpose_mul_mul f M') w
  rwa [inclusionMatrix_transpose_mulVec] at h1

/-- **The inverse is nonnegative off a bound principal submatrix**: on the vectors that vanish
on the coordinates of a principal submatrix which still has a bound state. -/
theorem inv_form_nonneg_of_comp_eq_zero {M' : Matrix κ κ ℝ} {φ' : κ → ℝ} {μ' c' : ℝ}
    (h' : OneBoundState M' φ' μ' c') (f : ι → κ) (h : OneBoundState (M'.submatrix f f) φ μ c)
    {w : κ → ℝ} (hw : w ∘ f = 0) : 0 ≤ w ⬝ᵥ (M'⁻¹ *ᵥ w) := by
  have h1 := inv_form_submatrix_le h' f h w
  rwa [hw, zero_dotProduct] at h1

end Compression

/-! ### Sub-windows -/

/-- The blocks `s, …, s + J' − 1` of a window of `J` blocks. -/
def shiftFin (s : ℕ) {J' J : ℕ} (h : s + J' ≤ J) (i : Fin J') : Fin J :=
  ⟨s + i, by have := i.2; omega⟩

/-- The neutral part of a sub-window is a principal submatrix. -/
theorem neutralWindow_submatrix_shiftFin (Q R s : ℕ) {J' J : ℕ} (h : s + J' ≤ J) :
    (neutralWindow Q R J).submatrix (shiftFin s h) (shiftFin s h) =
      neutralWindow Q (R + s) J' := by
  ext i j
  simp only [Matrix.submatrix_apply, neutralWindow, windowMatrix, Matrix.of_apply, shiftFin,
    Fin.val_mk, Nat.add_assoc]

/-- **The Green matrix of a bound sub-window is below the Green matrix of the window.** -/
theorem inv_form_neutralWindow_shift_le {Q R J s J' : ℕ} (hs : s + J' ≤ J)
    {ψ' : Fin J → ℝ} {ν' c' : ℝ} (h' : OneBoundState (neutralWindow Q R J) ψ' ν' c')
    {ψ : Fin J' → ℝ} {ν c : ℝ} (h : OneBoundState (neutralWindow Q (R + s) J') ψ ν c)
    (w : Fin J → ℝ) :
    (w ∘ shiftFin s hs) ⬝ᵥ ((neutralWindow Q (R + s) J')⁻¹ *ᵥ (w ∘ shiftFin s hs)) ≤
      w ⬝ᵥ ((neutralWindow Q R J)⁻¹ *ᵥ w) := by
  have hsub : OneBoundState ((neutralWindow Q R J).submatrix (shiftFin s hs) (shiftFin s hs))
      ψ ν c := by
    rw [neutralWindow_submatrix_shiftFin]
    exact h
  have h1 := inv_form_submatrix_le h' (shiftFin s hs) hsub w
  rw [neutralWindow_submatrix_shiftFin] at h1
  exact h1

/-- **The Green matrix of the dyadic middle is below the inverse of every certified window that
contains it.** -/
theorem greenMatrix_form_le_neutralWindow_inv {Q R J s : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hJ : 50 * J ≤ 53 * R) (hQ : 2 ≤ Q) (hs : s + (R + s) ≤ J) (w : Fin J → ℝ) :
    (w ∘ shiftFin s hs) ⬝ᵥ (greenMatrix (R + s) *ᵥ (w ∘ shiftFin s hs)) ≤
      w ⬝ᵥ ((neutralWindow Q R J)⁻¹ *ᵥ w) := by
  obtain ⟨ψ', ν', -, h'⟩ := exists_oneBoundState_neutralWindow hR hRJ hJ hQ
  have hmid : OneBoundState (neutralWindow Q (R + s) (R + s)) (groundVector (R + s))
      (bindingEnergy (R + s)) (1 / 5000) := by
    rw [neutralWindow_dyadic_eq]
    exact oneBoundState_primeFreeMiddle (by omega)
  have h1 := inv_form_neutralWindow_shift_le hs h' hmid w
  rw [neutralWindow_dyadic_eq] at h1
  exact h1

/-! ### Windows of ratio between `3/2` and `2` -/

/-- **The flat packet of a window of ratio between `3/2` and `2` binds**: on `(R, R + J]` with
`J ≤ R ≤ 2J` the constant packet has energy at most `−J/6`. The two entropy terms are at most
`J` and `J log 3`, the jet term is a second difference of the convex `x log x`, and
`1 + log 3 < γ + log 2π`. -/
theorem sum_neutralBlock_window_le {Q R J : ℕ} (hJ : 1 ≤ J) (hJR : J ≤ R) (hRJ : R ≤ 2 * J) :
    ∑ j ∈ range J, ∑ l ∈ range J, neutralBlock Q (R + j) (R + l) ≤ -(1 / 6) * J := by
  rw [sum_neutralBlock_window hJR]
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hrj : (R : ℝ) ≤ 2 * J := by exact_mod_cast hRJ
  have hA : Real.log ((R : ℝ) + J) - Real.log R ≤ J / R := by
    rw [← Real.log_div (by positivity) hr.ne']
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((R : ℝ) + J) / R by positivity)
    have e : ((R : ℝ) + J) / R - 1 = J / R := by
      rw [add_div, div_self hr.ne']
      ring
    linarith
  have hA' : (R : ℝ) * (Real.log ((R : ℝ) + J) - Real.log R) ≤ J := by
    have h := mul_le_mul_of_nonneg_left hA hr.le
    have e : (R : ℝ) * (J / R) = J := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hr.ne'
    linarith
  have hB : Real.log ((R : ℝ) + J) - Real.log J ≤ Real.log 3 := by
    rw [← Real.log_div (by positivity) hj.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hj]
    linarith
  have hB' : (J : ℝ) * (Real.log ((R : ℝ) + J) - Real.log J) ≤ J * Real.log 3 :=
    mul_le_mul_of_nonneg_left hB hj.le
  have h1 : xLogX (R + J) - xLogX R - xLogX J =
      R * (Real.log ((R : ℝ) + J) - Real.log R) +
        J * (Real.log ((R : ℝ) + J) - Real.log J) := by
    unfold xLogX
    push_cast
    ring
  -- the jet term: a second difference of `x log x`
  have h4 : 0 ≤ xLogX (R + R + J + J) - 2 * xLogX (R + R + J) + xLogX (R + R) := by
    have hconv := Real.strictConvexOn_mul_log.convexOn.2
      (Set.mem_Ici.mpr (Nat.cast_nonneg (R + R)))
      (Set.mem_Ici.mpr (Nat.cast_nonneg (R + R + J + J)))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    have hmid : (1 / 2 : ℝ) • ((R + R : ℕ) : ℝ) + (1 / 2 : ℝ) • ((R + R + J + J : ℕ) : ℝ) =
        ((R + R + J : ℕ) : ℝ) := by
      rw [smul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [hmid] at hconv
    simp only [smul_eq_mul] at hconv
    unfold xLogX
    linarith
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hπ : Real.log 3 < Real.log Real.pi := Real.log_lt_log (by norm_num) Real.pi_gt_three
  have hl2 := Real.log_two_gt_d9
  have hconst : (J : ℝ) + J * Real.log 3 -
      J * (Real.eulerMascheroniConstant + (Real.log 2 + Real.log Real.pi)) ≤ -(1 / 6) * J := by
    nlinarith [mul_pos hj (sub_pos.mpr hπ), mul_pos hj (sub_pos.mpr hγ),
      mul_pos hj (sub_pos.mpr hl2)]
  rw [log_two_pi]
  linarith

/-- **Every window of ratio between `3/2` and `2` has one bound state with floor `1/5000`**,
of binding energy at least `1/6`. -/
theorem exists_oneBoundState_neutralWindow_of_ratio {Q R J : ℕ} (hJ : 1 ≤ J) (hJR : J ≤ R)
    (hRJ : R ≤ 2 * J) (hQ : 2 ≤ Q) :
    ∃ ψ : Fin J → ℝ, ∃ ν : ℝ, (∀ i, 0 < ψ i) ∧
      OneBoundState (neutralWindow Q R J) ψ ν (1 / 5000) ∧ 1 / 6 ≤ ν := by
  obtain ⟨φ₀, hφ₀, lam, heig⟩ := exists_groundVector_neutralWindow Q R hJ
  have hsymm := neutralWindow_symm Q R J
  have hoff : ∀ i j : Fin J, i ≠ j → neutralWindow Q R J i j ≤ 0 := fun _ _ hij =>
    (neutralWindow_neg_of_ne Q R hij).le
  haveI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  -- the flat packet bounds the eigenvalue
  have hlam : lam ≤ -(1 / 6) := by
    have h1 := lam_mul_sum_sq_le_bilin hsymm hoff hφ₀ heig (fun _ => (1 : ℝ))
    have h2 : bilin (neutralWindow Q R J) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) =
        ∑ j ∈ range J, ∑ l ∈ range J, neutralBlock Q (R + j) (R + l) := by
      have hc := sum_fin_windowMatrix_coe (neutralBlock Q) R J (fun _ => 1)
      simp only [one_mul] at hc
      rw [← hc]
      simp only [bilin, one_mul, neutralWindow]
    rw [h2] at h1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at h1
    have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
    have h3 := sum_neutralBlock_window_le (Q := Q) hJ hJR hRJ
    nlinarith
  obtain ⟨ψ, hψ, h⟩ := exists_oneBoundState_of_pos_eigenvector hsymm hφ₀
    (by linarith : lam < 0) heig (by norm_num : (0 : ℝ) < 1 / 5000)
    (neutralWindow_floor_of_sum_eq_zero (by omega) (by omega) hQ)
  exact ⟨ψ, -lam, hψ, h, by linarith⟩

/-! ### The slivers of the dyadic middle -/

/-- **The Green matrix of the dyadic middle is nonnegative on its slivers.** Let a vector on
the blocks of `(D, 2D]` vanish on the sub-window `(D + s, D + s + J']` with `D + s ≤ 2J'`: it is
supported on a left sliver of `s` blocks and a right sliver of `s' = D − s − J'` blocks with
`3s + 2s' ≤ D`. The sub-window still binds, so the Green form of the vector is nonnegative, at
every block size. -/
theorem greenMatrix_nonneg_of_sliver {D s J' : ℕ} (hJ' : 1 ≤ J') (hs : s + J' ≤ D)
    (hbind : D + s ≤ 2 * J') {w : Fin D → ℝ} (hw : ∀ i : Fin J', w (shiftFin s hs i) = 0) :
    0 ≤ w ⬝ᵥ (greenMatrix D *ᵥ w) := by
  obtain ⟨ψ, ν, -, hT, -⟩ := exists_oneBoundState_neutralWindow_of_ratio (Q := 2)
    (R := D + s) hJ' (by omega) hbind le_rfl
  have hsub : OneBoundState ((primeFreeMiddle D).submatrix (shiftFin s hs) (shiftFin s hs))
      ψ ν (1 / 5000) := by
    rw [← neutralWindow_dyadic_eq 2 D, neutralWindow_submatrix_shiftFin]
    exact hT
  exact inv_form_nonneg_of_comp_eq_zero (oneBoundState_primeFreeMiddle (by omega))
    (shiftFin s hs) hsub (funext hw)

/-- **On the slivers the positive channel dominates the bound-state channel**: for a vector
supported on the two slivers, `⟨φ_D, w⟩² / μ_D ≤ ⟨w, G₊ w⟩`. -/
theorem groundVector_sq_le_greenPositive_of_sliver {D s J' : ℕ} (hJ' : 1 ≤ J')
    (hs : s + J' ≤ D) (hbind : D + s ≤ 2 * J') {w : Fin D → ℝ}
    (hw : ∀ i : Fin J', w (shiftFin s hs i) = 0) :
    1 / bindingEnergy D * (groundVector D ⬝ᵥ w) ^ 2 ≤ w ⬝ᵥ (greenPositive D *ᵥ w) := by
  have h := greenMatrix_nonneg_of_sliver hJ' hs hbind hw
  rw [greenMatrix, inv_form_eq_channels (primeFreeMiddle D) (groundVector D) (bindingEnergy D) w]
    at h
  rw [greenPositive]
  linarith

/-! ### The refinement tower -/

/-- The refinement of block values as a matrix: each block is split into `m` blocks and the
value is divided by `√m`. -/
def refineMatrix (m J : ℕ) : Matrix (Fin (m * J)) (Fin J) ℝ :=
  Matrix.of fun i j => if (i : ℕ) / m = (j : ℕ) then 1 / Real.sqrt m else 0

theorem extendFin_refineMatrix_mulVec {m J : ℕ} (v : Fin J → ℝ) {n : ℕ} (hn : n < m * J) :
    extendFin (refineMatrix m J *ᵥ v) n = refineStep m (extendFin v) n := by
  have hdiv : n / m < J := Nat.div_lt_of_lt_mul hn
  rw [extendFin, dif_pos hn, refineStep, extendFin, dif_pos hdiv]
  simp only [Matrix.mulVec, dotProduct, refineMatrix, Matrix.of_apply, Fin.val_mk]
  rw [Finset.sum_eq_single (⟨n / m, hdiv⟩ : Fin J)]
  · rw [if_pos rfl]
    ring
  · intro j _ hj
    rw [if_neg fun h => hj (Fin.ext h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Refinement keeps the mass. -/
theorem refineMatrix_mulVec_dot_self {m : ℕ} (hm : 1 ≤ m) {J : ℕ} (v : Fin J → ℝ) :
    (refineMatrix m J *ᵥ v) ⬝ᵥ (refineMatrix m J *ᵥ v) = v ⬝ᵥ v := by
  rw [dotProduct_self_eq_sum_range_extendFin, dotProduct_self_eq_sum_range_extendFin,
    ← sum_refineStep_sq hm J (extendFin v)]
  exact Finset.sum_congr rfl fun n hn => by
    rw [extendFin_refineMatrix_mulVec v (Finset.mem_range.mp hn)]

/-- Refinement keeps the neutral form. -/
theorem refineMatrix_mulVec_form {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (Q : ℕ) {J : ℕ}
    (v : Fin J → ℝ) :
    (refineMatrix m J *ᵥ v) ⬝ᵥ (neutralWindow Q (m * R) (m * J) *ᵥ (refineMatrix m J *ᵥ v)) =
      v ⬝ᵥ (neutralWindow Q R J *ᵥ v) := by
  rw [AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, neutralWindow, neutralWindow,
    sum_fin_windowMatrix_eq, sum_fin_windowMatrix_eq,
    ← sum_neutralBlock_refine hR hm Q J (extendFin v)]
  exact Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun l hl => by
    rw [extendFin_refineMatrix_mulVec v (Finset.mem_range.mp hn),
      extendFin_refineMatrix_mulVec v (Finset.mem_range.mp hl)]

/-- **Refinement compresses the neutral part at block size `mR` to the neutral part at block
size `R`.** -/
theorem refineMatrix_transpose_mul_mul {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (Q J : ℕ) :
    (refineMatrix m J)ᵀ * neutralWindow Q (m * R) (m * J) * refineMatrix m J =
      neutralWindow Q R J :=
  matrix_eq_of_forall_form_eq
    (transpose_mul_mul_symm (neutralWindow_symm Q (m * R) (m * J)) _)
    (neutralWindow_symm Q R J) fun v => by
      rw [dotProduct_transpose_mul_mul_mulVec, refineMatrix_mulVec_form hR hm]

/-- Refinement is an isometry. -/
theorem refineMatrix_transpose_mul {m : ℕ} (hm : 1 ≤ m) (J : ℕ) :
    (refineMatrix m J)ᵀ * refineMatrix m J = 1 := by
  refine matrix_eq_of_forall_form_eq (fun i j => ?_) (fun i j => ?_) fun v => ?_
  · have h : ((refineMatrix m J)ᵀ * refineMatrix m J)ᵀ =
        (refineMatrix m J)ᵀ * refineMatrix m J := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have h2 := congrFun (congrFun h j) i
    rwa [Matrix.transpose_apply] at h2
  · rcases eq_or_ne i j with h | h
    · rw [h]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm]
  · rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      Matrix.one_mulVec]
    exact refineMatrix_mulVec_dot_self hm v

/-- **The tower law of the Green form.** The Green form of the dyadic middle at block size `D`
is at most the Green form at block size `mD` of the refined vector. -/
theorem greenMatrix_form_le_refined {D : ℕ} (hD : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m)
    (w : Fin D → ℝ) :
    w ⬝ᵥ (greenMatrix D *ᵥ w) ≤
      (refineMatrix m D *ᵥ w) ⬝ᵥ (greenMatrix (m * D) *ᵥ (refineMatrix m D *ᵥ w)) := by
  have hT : (refineMatrix m D)ᵀ * primeFreeMiddle (m * D) * refineMatrix m D =
      primeFreeMiddle D := refineMatrix_transpose_mul_mul hD hm 1 D
  exact inv_form_le_of_isometry (oneBoundState_primeFreeMiddle (Nat.mul_pos hm hD))
    (oneBoundState_primeFreeMiddle hD) _ hT (refineMatrix_transpose_mul hm D) w

/-- **The Green forms of the refinement tower are bounded**: the refined vector has the same
mass, and the Green matrix is at most `5000` at every block size. -/
theorem greenMatrix_form_refined_le {D : ℕ} (hD : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m)
    (w : Fin D → ℝ) :
    (refineMatrix m D *ᵥ w) ⬝ᵥ (greenMatrix (m * D) *ᵥ (refineMatrix m D *ᵥ w)) ≤
      5000 * (w ⬝ᵥ w) := by
  have h := greenMatrix_form_le (Nat.mul_pos hm hD) (refineMatrix m D *ᵥ w)
  rwa [refineMatrix_mulVec_dot_self hm] at h

/-- **The binding energy of the dyadic middle increases along the refinement tower.** -/
theorem bindingEnergy_le_refined {D : ℕ} (hD : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m) :
    bindingEnergy D ≤ bindingEnergy (m * D) := by
  have hT : (refineMatrix m D)ᵀ * primeFreeMiddle (m * D) * refineMatrix m D =
      primeFreeMiddle D := refineMatrix_transpose_mul_mul hD hm 1 D
  exact (oneBoundState_primeFreeMiddle (Nat.mul_pos hm hD)).depth_le_of_isometry
    (oneBoundState_primeFreeMiddle hD) _ hT (refineMatrix_transpose_mul hm D)

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
