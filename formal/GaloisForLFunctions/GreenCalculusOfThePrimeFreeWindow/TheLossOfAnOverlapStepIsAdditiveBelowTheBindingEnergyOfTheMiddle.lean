import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGreenMatrixOfTheDyadicMiddleHasABoundStateChannelAndAPositiveChannel
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis

/-!
# The loss of an overlap step is additive below the binding energy of the middle

The level `C` of a window is its neutral part shifted by `C` on the diagonal; the margin of the
window is the least level at which it holds at most one bound state. The Riemann hypothesis is a
uniform bound for the margins (MAFT). This file is the calculus of levels over the dyadic middle.

* **Levels of the middle** (`OneBoundState.add_diagonal`). Below its binding energy `μ` a matrix
  `M` with one bound state keeps it at every level: `M + C` has depth `μ − C` and floor `c + C`.
* **Dirichlet principle** (`positiveChannel_ge`): `⟨w, G₊ w⟩ ≥ 2⟨w, z⟩ − ⟨z, M z⟩` for every `z`
  orthogonal to the ground vector. Hence `⟨w, (M + C)⁻¹ w⟩` decreases in `C` below the binding
  energy (`inv_form_add_diagonal_antitone`), and the Schur complement
  `S_C = N + C − Pᵀ (M + C)⁻¹ P` grows at least at unit speed (`schur_add_diagonal_mono`).
* **The margin from a Schur complement** (`hermNegIndex_fromBlocks_add_diagonal_le_one`): if
  `S_C ⪰ −x`, the whole holds at most one bound state at level `C + x`. Completing the square over
  the middle, the form at level `C + x` is nonnegative on the hyperplane where the component of
  `m + (M + C)⁻¹ P e` along the ground vector vanishes. No bound on `C + x` is needed.
* **The additive loss law** (`hermNegIndex_overlapWhole_add_diagonal_le_one`,
  `hermNegIndex_neutralWindow_add_le_one_of_parts`): if both parts hold at most one bound state
  at a level `C` below the binding energy of the middle, and the conditional coupling at level `C`
  has norm at most `x`, the whole holds at most one at level `C + x`. On the first overlap step
  the parts are certified at level `0`: the margin is at most the norm of the conditional
  coupling (`hermNegIndex_neutralWindow_add_le_one_of_firstStep`).
* **The Riemann hypothesis with a loss.** It holds iff the Schur complement of the dyadic middle
  is bounded below uniformly over all windows (`riemannHypothesis_iff_overlapSchur_bddBelow`),
  iff it is nonnegative (`riemannHypothesis_iff_forall_overlapSchur_nonneg`), iff the neutral
  form is nonnegative on the vectors that are harmonic on the middle
  (`riemannHypothesis_iff_forall_harmonic_nonneg`). It follows from a level function with
  values in `[0, 1]` whose increments along the recursion dominate the conditional couplings
  (`riemannHypothesis_of_level_function`): a loss that sums below the binding energy.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Shifts on the diagonal -/

section Diagonal

variable {ι ι' α β : Type*} [DecidableEq ι] [DecidableEq ι'] [DecidableEq α] [DecidableEq β]

theorem symm_add_diagonal {N : Matrix ι ι ℝ} (hN : ∀ i j, N i j = N j i) (C : ℝ) (i j : ι) :
    (N + Matrix.diagonal fun _ => C : Matrix ι ι ℝ) i j =
      (N + Matrix.diagonal fun _ => C : Matrix ι ι ℝ) j i := by
  rw [Matrix.add_apply, Matrix.add_apply, hN i j]
  by_cases hij : i = j
  · rw [hij]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

theorem submatrix_add_diagonal_equiv (A : Matrix ι ι ℝ) (e : ι' ≃ ι) (C : ℝ) :
    (A + Matrix.diagonal fun _ => C).submatrix e e =
      A.submatrix e e + Matrix.diagonal fun _ => C := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.add_apply, Matrix.add_apply, Matrix.submatrix_apply]
  by_cases hij : i = j
  · rw [hij, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hne]

theorem diagonal_const_add (C x : ℝ) :
    (Matrix.diagonal fun _ : ι => C + x) =
      Matrix.diagonal (fun _ => C) + Matrix.diagonal fun _ => x := by
  ext i j
  rw [Matrix.add_apply]
  by_cases hij : i = j
  · rw [hij, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ hij, add_zero]

/-- A shift of a block matrix is the shift of its diagonal blocks. -/
theorem fromBlocks_add_diagonal_const (A : Matrix α α ℝ) (B : Matrix α β ℝ) (B' : Matrix β α ℝ)
    (D : Matrix β β ℝ) (c : ℝ) :
    fromBlocks A B B' D + Matrix.diagonal (fun _ => c) =
      fromBlocks (A + Matrix.diagonal fun _ => c) B B' (D + Matrix.diagonal fun _ => c) := by
  have hd : (Matrix.diagonal fun _ : α ⊕ β => c) =
      fromBlocks (Matrix.diagonal fun _ => c) 0 0 (Matrix.diagonal fun _ => c) := by
    rw [Matrix.fromBlocks_diagonal]
    congr 1
    ext (i | i) <;> rfl
  rw [hd, Matrix.fromBlocks_add, add_zero, add_zero]

end Diagonal

/-! ### Levels of a matrix with one bound state -/

section Levels

variable {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]

/-- A real form that is nonnegative on a hyperplane has at most one negative square. -/
theorem hermNegIndex_le_one_of_nonneg_on_hyperplane (G : Matrix ι ι ℝ) (ℓ : ι → ℝ)
    (h : ∀ y : ι → ℝ, ℓ ⬝ᵥ y = 0 → 0 ≤ y ⬝ᵥ (G *ᵥ y)) :
    hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ≤ 1 := by
  refine (ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
    (G.map (↑) : Matrix ι ι ℂ) (fun _ : Unit => realChargeForm ℓ) fun z hz => ?_).trans
    (le_of_eq Fintype.card_unit)
  have key : ∀ y : ι → ℝ, ∑ i, ℓ i * y i = 0 → 0 ≤ y ⬝ᵥ (G *ᵥ y) := fun y hy => h y hy
  have hc : ∑ m, ((ℓ m : ℝ) : ℂ) * z m = 0 := hz ()
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal]
  refine add_nonneg (key _ ?_) (key _ ?_)
  · have h1 := congrArg Complex.re hc
    rw [Complex.re_sum, Complex.zero_re] at h1
    exact (Finset.sum_congr rfl fun m _ => (Complex.re_ofReal_mul _ _).symm).trans h1
  · have h1 := congrArg Complex.im hc
    rw [Complex.im_sum, Complex.zero_im] at h1
    exact (Finset.sum_congr rfl fun m _ => (Complex.im_ofReal_mul _ _).symm).trans h1

/-- **A matrix with one bound state has exactly one negative square.** -/
theorem OneBoundState.hermNegIndex_eq_one {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}
    (h : OneBoundState M φ μ c) : hermNegIndex (M.map (↑) : Matrix ι ι ℂ) = 1 := by
  refine le_antisymm (hermNegIndex_le_one_of_nonneg_on_hyperplane M φ fun y hy => ?_) ?_
  · exact le_trans (mul_nonneg h.floor_pos.le (dotProduct_self_star_nonneg (v := y)))
      (h.floor y hy)
  · by_contra hlt
    have h0 : hermNegIndex (M.map (↑) : Matrix ι ι ℂ) = 0 := by omega
    have hnn := (hermNegIndex_eq_zero_iff_forall.mp h0) φ
    rw [h.eig, dotProduct_smul, h.unit, smul_eq_mul, mul_one] at hnn
    linarith [h.depth_pos]

/-- The form of `Pᵀ A P` is the form of `A` on the image of `P`. -/
theorem dotProduct_transpose_mul_mul_mulVec (P : Matrix ι κ ℝ) (A : Matrix ι ι ℝ) (e : κ → ℝ) :
    e ⬝ᵥ ((Pᵀ * A * P) *ᵥ e) = (P *ᵥ e) ⬝ᵥ (A *ᵥ (P *ᵥ e)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- **A two-block form with nonnegative diagonal blocks is bounded below by the norm of its
off-diagonal block.** -/
theorem fromBlocks_form_ge_of_coupling_le {E₁ : Matrix α α ℝ} {X : Matrix α β ℝ}
    {E₂ : Matrix β β ℝ} (h₁ : ∀ u, 0 ≤ u ⬝ᵥ (E₁ *ᵥ u)) (h₂ : ∀ v, 0 ≤ v ⬝ᵥ (E₂ *ᵥ v)) {x : ℝ}
    (hx : 0 ≤ x)
    (hX : ∀ u v, (u ⬝ᵥ (X *ᵥ v)) ^ 2 ≤ x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v))) (z : α ⊕ β → ℝ) :
    -x * (z ⬝ᵥ z) ≤ z ⬝ᵥ (fromBlocks E₁ X Xᵀ E₂ *ᵥ z) := by
  rw [← Sum.elim_comp_inl_inr z, dotProduct_fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  have huu : 0 ≤ (z ∘ Sum.inl) ⬝ᵥ (z ∘ Sum.inl) := dotProduct_self_star_nonneg (v := z ∘ Sum.inl)
  have hvv : 0 ≤ (z ∘ Sum.inr) ⬝ᵥ (z ∘ Sum.inr) := dotProduct_self_star_nonneg (v := z ∘ Sum.inr)
  have hq := hX (z ∘ Sum.inl) (z ∘ Sum.inr)
  have ha := h₁ (z ∘ Sum.inl)
  have hc := h₂ (z ∘ Sum.inr)
  generalize (z ∘ Sum.inl) ⬝ᵥ (z ∘ Sum.inl) = p at huu hq ⊢
  generalize (z ∘ Sum.inr) ⬝ᵥ (z ∘ Sum.inr) = r at hvv hq ⊢
  generalize (z ∘ Sum.inl) ⬝ᵥ (X *ᵥ (z ∘ Sum.inr)) = q at hq ⊢
  -- `(2q)² ≤ x² (p + r)²`, so `2q ≥ −x (p + r)`
  have hsq : (2 * q) ^ 2 ≤ (x * (p + r)) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg (p - r))]
  have hb : 0 ≤ x * (p + r) := mul_nonneg hx (add_nonneg huu hvv)
  have habs : -(x * (p + r)) ≤ 2 * q := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 0 < -(x * (p + r)) - 2 * q := by linarith
    have h2 : 0 < x * (p + r) - 2 * q := by linarith
    nlinarith [mul_pos h1 h2]
  linarith

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α] [DecidableEq β]

theorem diagonal_const_mulVec (C : ℝ) (v : ι → ℝ) :
    (Matrix.diagonal fun _ : ι => C) *ᵥ v = C • v := by
  ext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

/-- The form at level `C`. -/
theorem dotProduct_add_diagonal_mulVec (A : Matrix ι ι ℝ) (C : ℝ) (z : ι → ℝ) :
    z ⬝ᵥ ((A + Matrix.diagonal fun _ => C) *ᵥ z) = z ⬝ᵥ (A *ᵥ z) + C * (z ⬝ᵥ z) := by
  rw [Matrix.add_mulVec, dotProduct_add, diagonal_const_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Raising the level does not raise the index.** -/
theorem hermNegIndex_add_diagonal_mono (G : Matrix ι ι ℝ) {C C' : ℝ} (h : C ≤ C') :
    hermNegIndex ((G + Matrix.diagonal fun _ => C').map (↑) : Matrix ι ι ℂ) ≤
      hermNegIndex ((G + Matrix.diagonal fun _ => C).map (↑) : Matrix ι ι ℂ) := by
  refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun c => ?_
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, HeckeKreinToeplitz.hermQuad_map_ofReal]
  simp only [dotProduct_add_diagonal_mulVec]
  have h1 : 0 ≤ (fun i => (c i).re) ⬝ᵥ fun i => (c i).re :=
    dotProduct_self_star_nonneg (v := fun i => (c i).re)
  have h2 : 0 ≤ (fun i => (c i).im) ⬝ᵥ fun i => (c i).im :=
    dotProduct_self_star_nonneg (v := fun i => (c i).im)
  nlinarith [mul_nonneg (sub_nonneg.mpr h) h1, mul_nonneg (sub_nonneg.mpr h) h2]

theorem hermNegIndex_add_diagonal_le (G : Matrix ι ι ℝ) {x : ℝ} (hx : 0 ≤ x) :
    hermNegIndex ((G + Matrix.diagonal fun _ => x).map (↑) : Matrix ι ι ℂ) ≤
      hermNegIndex (G.map (↑) : Matrix ι ι ℂ) := by
  have h := hermNegIndex_add_diagonal_mono G hx
  rwa [Matrix.diagonal_zero, add_zero] at h

variable {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

/-- **Below the binding energy the bound state survives at every level**: `M + C` has depth
`μ − C` and floor `c + C`. -/
theorem OneBoundState.add_diagonal (h : OneBoundState M φ μ c) {C : ℝ} (hC : C < μ)
    (hc : 0 < c + C) : OneBoundState (M + Matrix.diagonal fun _ => C) φ (μ - C) (c + C) where
  symm := symm_add_diagonal h.symm C
  unit := h.unit
  eig := by
    rw [Matrix.add_mulVec, h.eig, diagonal_const_mulVec, ← add_smul]
    congr 1
    ring
  depth_pos := sub_pos.mpr hC
  floor_pos := hc
  floor z hz := by
    rw [dotProduct_add_diagonal_mulVec]
    have h1 := h.floor z hz
    have e : (c + C) * (z ⬝ᵥ z) = c * (z ⬝ᵥ z) + C * (z ⬝ᵥ z) := by ring
    rw [e]
    linarith

/-- The matrix on the component of `M⁻¹ w` orthogonal to the ground vector. -/
theorem OneBoundState.mulVec_perp_inv (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    M *ᵥ OneBoundState.perp φ (M⁻¹ *ᵥ w) = w + (μ * (φ ⬝ᵥ (M⁻¹ *ᵥ w))) • φ := by
  rw [OneBoundState.perp, Matrix.mulVec_sub, Matrix.mulVec_smul, h.eig, h.mulVec_inv_mulVec,
    smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

/-- The form of the inverse in the two channels. -/
theorem inv_form_eq_channels (M : Matrix ι ι ℝ) (φ : ι → ℝ) (μ : ℝ) (w : ι → ℝ) :
    w ⬝ᵥ (M⁻¹ *ᵥ w) = w ⬝ᵥ (positiveChannel M φ μ *ᵥ w) - 1 / μ * (φ ⬝ᵥ w) ^ 2 := by
  rw [positiveChannel_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm w φ]
  ring

/-- **Dirichlet principle for the positive channel**: every vector orthogonal to the ground
vector bounds the positive channel from below. -/
theorem positiveChannel_ge (h : OneBoundState M φ μ c) (w : ι → ℝ) {z : ι → ℝ}
    (hz : φ ⬝ᵥ z = 0) :
    2 * (w ⬝ᵥ z) - z ⬝ᵥ (M *ᵥ z) ≤ w ⬝ᵥ (positiveChannel M φ μ *ᵥ w) := by
  rw [positiveChannel_form h]
  have hφz₀ := h.dot_perp (M⁻¹ *ᵥ w)
  have hMz₀ := h.mulVec_perp_inv w
  generalize OneBoundState.perp φ (M⁻¹ *ᵥ w) = z₀ at hφz₀ hMz₀ ⊢
  have hzMz₀ : z ⬝ᵥ (M *ᵥ z₀) = w ⬝ᵥ z := by
    rw [hMz₀, dotProduct_add, dotProduct_smul, dotProduct_comm z φ, hz, smul_zero, add_zero]
    exact dotProduct_comm z w
  have hd : φ ⬝ᵥ (z - z₀) = 0 := by rw [dotProduct_sub, hz, hφz₀, sub_zero]
  have hnn : 0 ≤ (z - z₀) ⬝ᵥ (M *ᵥ (z - z₀)) :=
    le_trans (mul_nonneg h.floor_pos.le (dotProduct_self_star_nonneg (v := z - z₀)))
      (h.floor _ hd)
  have hexp : (z - z₀) ⬝ᵥ (M *ᵥ (z - z₀)) =
      z ⬝ᵥ (M *ᵥ z) - 2 * (z ⬝ᵥ (M *ᵥ z₀)) + z₀ ⬝ᵥ (M *ᵥ z₀) := by
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_mulVec_symm h.symm z₀ z]
    ring
  rw [hexp, hzMz₀] at hnn
  linarith

/-- **The form of the inverse decreases in the level below the binding energy.** -/
theorem inv_form_add_diagonal_antitone (h : OneBoundState M φ μ c) {C C' : ℝ} (hCC : C ≤ C')
    (hC' : C' < μ) (hc : 0 < c + C) (w : ι → ℝ) :
    w ⬝ᵥ ((M + Matrix.diagonal fun _ => C')⁻¹ *ᵥ w) ≤
      w ⬝ᵥ ((M + Matrix.diagonal fun _ => C)⁻¹ *ᵥ w) := by
  have hA := h.add_diagonal (lt_of_le_of_lt hCC hC') hc
  have hA' := h.add_diagonal hC' (by linarith : 0 < c + C')
  rw [inv_form_eq_channels (M + Matrix.diagonal fun _ => C') φ (μ - C') w,
    inv_form_eq_channels (M + Matrix.diagonal fun _ => C) φ (μ - C) w]
  -- the trial vector of the lower level is the optimal vector of the higher level
  have hz' := hA'.dot_perp ((M + Matrix.diagonal fun _ => C')⁻¹ *ᵥ w)
  have hMz' := hA'.mulVec_perp_inv w
  have hform := positiveChannel_form hA' w
  have hge := positiveChannel_ge hA w hz'
  generalize OneBoundState.perp φ ((M + Matrix.diagonal fun _ => C')⁻¹ *ᵥ w) = z'
    at hz' hMz' hform hge
  have hpair : z' ⬝ᵥ ((M + Matrix.diagonal fun _ => C') *ᵥ z') = w ⬝ᵥ z' := by
    rw [hMz', dotProduct_add, dotProduct_smul, dotProduct_comm z' φ, hz', smul_zero, add_zero]
    exact dotProduct_comm z' w
  have hAA : z' ⬝ᵥ ((M + Matrix.diagonal fun _ => C) *ᵥ z') ≤ w ⬝ᵥ z' := by
    rw [← hpair, dotProduct_add_diagonal_mulVec, dotProduct_add_diagonal_mulVec]
    have h2 : 0 ≤ z' ⬝ᵥ z' := dotProduct_self_star_nonneg (v := z')
    nlinarith [mul_nonneg (sub_nonneg.mpr hCC) h2]
  have hdiv : 1 / (μ - C) * (φ ⬝ᵥ w) ^ 2 ≤ 1 / (μ - C') * (φ ⬝ᵥ w) ^ 2 :=
    mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (sub_pos.mpr hC') (by linarith)) (sq_nonneg _)
  rw [hform, hpair]
  linarith

/-- **The Schur complement over a matrix with one bound state grows at least at unit speed in
the level**, below the binding energy. -/
theorem schur_add_diagonal_mono (h : OneBoundState M φ μ c) (P : Matrix ι κ ℝ)
    (N : Matrix κ κ ℝ) {C C' : ℝ} (hCC : C ≤ C') (hC' : C' < μ) (hc : 0 < c + C)
    (e : κ → ℝ) :
    e ⬝ᵥ ((N + Matrix.diagonal (fun _ => C) -
        Pᵀ * (M + Matrix.diagonal fun _ => C)⁻¹ * P) *ᵥ e) + (C' - C) * (e ⬝ᵥ e) ≤
      e ⬝ᵥ ((N + Matrix.diagonal (fun _ => C') -
        Pᵀ * (M + Matrix.diagonal fun _ => C')⁻¹ * P) *ᵥ e) := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, dotProduct_sub, dotProduct_sub,
    dotProduct_transpose_mul_mul_mulVec, dotProduct_transpose_mul_mul_mulVec,
    dotProduct_add_diagonal_mulVec, dotProduct_add_diagonal_mulVec]
  have := inv_form_add_diagonal_antitone h hCC hC' hc (P *ᵥ e)
  linarith

omit [DecidableEq κ] in
/-- **Completing the square over the middle.** -/
theorem dotProduct_fromBlocks_mulVec_eq_schur {A : Matrix ι ι ℝ} (hA : ∀ i j, A i j = A j i)
    (hAu : IsUnit A) (P : Matrix ι κ ℝ) (N : Matrix κ κ ℝ) (m : ι → ℝ) (e : κ → ℝ) :
    Sum.elim m e ⬝ᵥ (fromBlocks A P Pᵀ N *ᵥ Sum.elim m e) =
      (m + A⁻¹ *ᵥ (P *ᵥ e)) ⬝ᵥ (A *ᵥ (m + A⁻¹ *ᵥ (P *ᵥ e))) +
        e ⬝ᵥ ((N - Pᵀ * A⁻¹ * P) *ᵥ e) := by
  have hAg : A *ᵥ (A⁻¹ *ᵥ (P *ᵥ e)) = P *ᵥ e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hAu),
      Matrix.one_mulVec]
  rw [dotProduct_fromBlocks_mulVec, Matrix.sub_mulVec, dotProduct_sub,
    dotProduct_transpose_mul_mul_mulVec, Matrix.mulVec_add, hAg]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_mulVec_symm hA (A⁻¹ *ᵥ (P *ᵥ e)) m, hAg,
    dotProduct_comm (A⁻¹ *ᵥ (P *ᵥ e)) (P *ᵥ e)]
  ring

/-- **The margin from a Schur complement.** If the Schur complement over a matrix with one bound
state is at least `−x`, the block matrix holds at most one bound state at level `x`. -/
theorem hermNegIndex_fromBlocks_add_diagonal_le_one {A : Matrix ι ι ℝ}
    (h : OneBoundState A φ μ c) (P : Matrix ι κ ℝ) (N : Matrix κ κ ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hS : ∀ e : κ → ℝ, -x * (e ⬝ᵥ e) ≤ e ⬝ᵥ ((N - Pᵀ * A⁻¹ * P) *ᵥ e)) :
    hermNegIndex ((fromBlocks A P Pᵀ N + Matrix.diagonal fun _ => x).map (↑) :
      Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) ≤ 1 := by
  -- the hyperplane: the component of `m + A⁻¹ P e` along the ground vector vanishes
  refine hermNegIndex_le_one_of_nonneg_on_hyperplane _
    (Sum.elim (μ • φ) (-(Pᵀ *ᵥ φ))) fun y hy => ?_
  obtain ⟨m, e, rfl⟩ : ∃ m e, y = Sum.elim m e :=
    ⟨y ∘ Sum.inl, y ∘ Sum.inr, (Sum.elim_comp_inl_inr y).symm⟩
  rw [sumElim_dotProduct_sumElim, smul_dotProduct, neg_dotProduct, smul_eq_mul,
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec] at hy
  have h1 : φ ⬝ᵥ (P *ᵥ e) = -μ * (φ ⬝ᵥ (A⁻¹ *ᵥ (P *ᵥ e))) := by
    rw [← h.dot_mulVec, h.mulVec_inv_mulVec]
  have hu : φ ⬝ᵥ (m + A⁻¹ *ᵥ (P *ᵥ e)) = 0 := by
    have h2 : μ * (φ ⬝ᵥ (m + A⁻¹ *ᵥ (P *ᵥ e))) = 0 := by
      rw [dotProduct_add, mul_add]
      linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 h.depth_pos.ne'
    · exact h3
  rw [dotProduct_add_diagonal_mulVec, dotProduct_fromBlocks_mulVec_eq_schur h.symm h.isUnit,
    sumElim_dotProduct_sumElim]
  have hU : 0 ≤ (m + A⁻¹ *ᵥ (P *ᵥ e)) ⬝ᵥ (A *ᵥ (m + A⁻¹ *ᵥ (P *ᵥ e))) :=
    le_trans (mul_nonneg h.floor_pos.le
      (dotProduct_self_star_nonneg (v := m + A⁻¹ *ᵥ (P *ᵥ e)))) (h.floor _ hu)
  have hm : 0 ≤ x * (m ⬝ᵥ m) := mul_nonneg hx (dotProduct_self_star_nonneg (v := m))
  have hSe := hS e
  nlinarith

/-- Over a matrix with one bound state, a block matrix with at most one negative square has a
nonnegative Schur complement. -/
theorem schur_nonneg_of_hermNegIndex_le_one {A : Matrix ι ι ℝ} (h : OneBoundState A φ μ c)
    (P : Matrix ι κ ℝ) {N : Matrix κ κ ℝ} (hN : ∀ i j, N i j = N j i)
    (hidx : hermNegIndex ((fromBlocks A P Pᵀ N).map (↑) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) ≤ 1)
    (e : κ → ℝ) : 0 ≤ e ⬝ᵥ ((N - Pᵀ * A⁻¹ * P) *ᵥ e) := by
  have hH := hermNegIndex_fromBlocks_transpose h.symm h.isUnit P hN
  rw [h.hermNegIndex_eq_one] at hH
  have h0 : hermNegIndex ((N - Pᵀ * A⁻¹ * P).map (↑) : Matrix κ κ ℂ) = 0 := by omega
  exact hermNegIndex_eq_zero_iff_forall.mp h0 e

/-- **The additive loss law.** Let the middle have one bound state of depth `μ`. If both parts
hold at most one bound state at a level `C < μ` and the conditional coupling of the ends at
level `C` has norm at most `x`, the whole holds at most one bound state at level `C + x`. -/
theorem hermNegIndex_overlapWhole_add_diagonal_le_one (h : OneBoundState M φ μ c)
    (P₁ : Matrix ι α ℝ) (P₂ : Matrix ι β ℝ) {N₁ : Matrix α α ℝ}
    (hN₁ : ∀ i j, N₁ i j = N₁ j i) (K : Matrix α β ℝ) {N₂ : Matrix β β ℝ}
    (hN₂ : ∀ i j, N₂ i j = N₂ j i) {C x : ℝ} (hC : C < μ) (hc : 0 < c + C) (hx : 0 ≤ x)
    (hleft : hermNegIndex ((fromBlocks M P₁ P₁ᵀ N₁ + Matrix.diagonal fun _ => C).map (↑) :
      Matrix (ι ⊕ α) (ι ⊕ α) ℂ) ≤ 1)
    (hright : hermNegIndex ((fromBlocks M P₂ P₂ᵀ N₂ + Matrix.diagonal fun _ => C).map (↑) :
      Matrix (ι ⊕ β) (ι ⊕ β) ℂ) ≤ 1)
    (hX : ∀ u v, (u ⬝ᵥ ((K - P₁ᵀ * (M + Matrix.diagonal fun _ => C)⁻¹ * P₂) *ᵥ v)) ^ 2 ≤
      x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v))) :
    hermNegIndex ((overlapWhole M P₁ P₂ N₁ K N₂ + Matrix.diagonal fun _ => (C + x)).map (↑) :
      Matrix (ι ⊕ (α ⊕ β)) (ι ⊕ (α ⊕ β)) ℂ) ≤ 1 := by
  have hA := h.add_diagonal hC hc
  rw [fromBlocks_add_diagonal_const] at hleft hright
  have h₁ := schur_nonneg_of_hermNegIndex_le_one hA P₁ (symm_add_diagonal hN₁ C) hleft
  have h₂ := schur_nonneg_of_hermNegIndex_le_one hA P₂ (symm_add_diagonal hN₂ C) hright
  rw [diagonal_const_add, ← add_assoc, overlapWhole, fromBlocks_add_diagonal_const M _ _ _ C,
    fromBlocks_add_diagonal_const N₁ K Kᵀ N₂ C]
  refine hermNegIndex_fromBlocks_add_diagonal_le_one hA _ _ hx fun e => ?_
  rw [fromBlocks_sub_joinColumns hA.symm]
  exact fromBlocks_form_ge_of_coupling_le h₁ h₂ hx hX e

end Levels

/-! ### Levels of a window -/

/-- The Schur complement of the dyadic middle in the window `(R, 2(R + a) + b]` at level `C`. -/
def overlapSchurLevel (Q R a b : ℕ) (C : ℝ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  endForm Q R a b + Matrix.diagonal (fun _ => C) -
    (endCoupling Q R a b)ᵀ * (primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *
      endCoupling Q R a b

/-- The conditional coupling of the two ends through the dyadic middle at level `C`. -/
def overlapCouplingLevel (Q R a b : ℕ) (C : ℝ) : Matrix (Fin a) (Fin b) ℝ :=
  posMatrix (neutralBlock Q) (leftPos R a) (rightPos R a b) -
    (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))ᵀ *
      (primeFreeMiddle (R + a) + Matrix.diagonal fun _ => C)⁻¹ *
      posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b)

theorem overlapSchurLevel_zero (Q R a b : ℕ) :
    overlapSchurLevel Q R a b 0 = overlapSchur Q R a b := by
  rw [overlapSchurLevel, overlapSchur, greenMatrix, Matrix.diagonal_zero, Matrix.diagonal_zero,
    add_zero, add_zero]

theorem overlapCouplingLevel_zero (Q R a b : ℕ) :
    overlapCouplingLevel Q R a b 0 = overlapCoupling Q R a b := by
  rw [overlapCouplingLevel, overlapCoupling, neutralWindow_dyadic_eq, Matrix.diagonal_zero,
    add_zero]

/-- **The Schur complement of the dyadic middle grows at least at unit speed in the level**,
below the binding energy of the middle. -/
theorem overlapSchurLevel_mono (Q : ℕ) {R : ℕ} (a b : ℕ) (hR : 1 ≤ R) {C C' : ℝ}
    (hC : -(1 / 5000) < C) (hCC : C ≤ C') (hC' : C' < bindingEnergy (R + a))
    (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e) + (C' - C) * (e ⬝ᵥ e) ≤
      e ⬝ᵥ (overlapSchurLevel Q R a b C' *ᵥ e) :=
  schur_add_diagonal_mono (oneBoundState_primeFreeMiddle (by omega)) _ _ hCC hC'
    (by linarith) e

/-- **The margin of a window from the Schur complement of its dyadic middle.** If the Schur
complement at a level `C` below the binding energy of the middle is at least `−x`, the window
holds at most one bound state at level `C + x`. -/
theorem hermNegIndex_neutralWindow_add_le_one_of_schurLevel {Q R : ℕ} (a b : ℕ) (hR : 1 ≤ R)
    {C x : ℝ} (hC : -(1 / 5000) < C) (hCμ : C < bindingEnergy (R + a)) (hx : 0 ≤ x)
    (hS : ∀ e : Fin a ⊕ Fin b → ℝ,
      -x * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e)) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b) +
        Matrix.diagonal fun _ => (C + x)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) ≤ 1 := by
  have hA := (oneBoundState_primeFreeMiddle (by omega : 1 ≤ R + a)).add_diagonal hCμ
    (by linarith)
  have key := hermNegIndex_fromBlocks_add_diagonal_le_one hA (endCoupling Q R a b)
    (endForm Q R a b + Matrix.diagonal fun _ => C) hx hS
  rw [← hermNegIndex_map_submatrix _ (overlapEquiv a (R + a) b), submatrix_add_diagonal_equiv,
    neutralWindow_submatrix_overlapEquiv, neutralWindow_dyadic_eq, diagonal_const_add,
    ← add_assoc, overlapWhole, fromBlocks_add_diagonal_const (primeFreeMiddle (R + a)) _ _ _ C]
  exact key

/-- **The additive loss law on windows.** If the parts `(R, 2(R + a)]` and
`(R + a, 2(R + a) + b]` hold at most one bound state at a level `C` below the binding energy of
the dyadic middle, and the conditional coupling at level `C` has norm at most `x`, the window
`(R, 2(R + a) + b]` holds at most one bound state at level `C + x`. -/
theorem hermNegIndex_neutralWindow_add_le_one_of_parts {Q R : ℕ} (a b : ℕ) (hR : 1 ≤ R)
    {C x : ℝ} (hC : -(1 / 5000) < C) (hCμ : C < bindingEnergy (R + a)) (hx : 0 ≤ x)
    (hleft : hermNegIndex ((neutralWindow Q R (a + (R + a)) +
        Matrix.diagonal fun _ => C).map (↑) :
      Matrix (Fin (a + (R + a))) (Fin (a + (R + a))) ℂ) ≤ 1)
    (hright : hermNegIndex ((neutralWindow Q (R + a) ((R + a) + b) +
        Matrix.diagonal fun _ => C).map (↑) :
      Matrix (Fin ((R + a) + b)) (Fin ((R + a) + b)) ℂ) ≤ 1)
    (hX : ∀ (u : Fin a → ℝ) (v : Fin b → ℝ),
      (u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v)) ^ 2 ≤ x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v))) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b) +
        Matrix.diagonal fun _ => (C + x)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) ≤ 1 := by
  rw [← hermNegIndex_map_submatrix _ (leftPartEquiv a (R + a)), submatrix_add_diagonal_equiv,
    neutralWindow_submatrix_leftPartEquiv, neutralWindow_dyadic_eq] at hleft
  rw [← hermNegIndex_map_submatrix _ (finSumFinEquiv : Fin (R + a) ⊕ Fin b ≃ Fin (R + a + b)),
    submatrix_add_diagonal_equiv, neutralWindow_submatrix_rightPart,
    neutralWindow_dyadic_eq] at hright
  rw [← hermNegIndex_map_submatrix _ (overlapEquiv a (R + a) b), submatrix_add_diagonal_equiv,
    neutralWindow_submatrix_overlapEquiv, neutralWindow_dyadic_eq]
  exact hermNegIndex_overlapWhole_add_diagonal_le_one
    (oneBoundState_primeFreeMiddle (by omega : 1 ≤ R + a)) _ _
    (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) _
    (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b)) hCμ (by linarith) hx hleft hright hX

/-- **The margin of a window of the first overlap step is at most the norm of its conditional
coupling**: for `a ≤ 3R/100` and `b ≤ 3(R + a)/50` both parts are certified at level `0`. -/
theorem hermNegIndex_neutralWindow_add_le_one_of_firstStep {Q R a b : ℕ} (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (hQ : 2 ≤ Q) {x : ℝ} (hx : 0 ≤ x)
    (hX : ∀ (u : Fin a → ℝ) (v : Fin b → ℝ),
      (u ⬝ᵥ (overlapCoupling Q R a b *ᵥ v)) ^ 2 ≤ x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v))) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b) + Matrix.diagonal fun _ => x).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) ≤ 1 := by
  have hD : 1 ≤ R + a := by omega
  have h₁ : hermNegIndex ((neutralWindow Q R (a + (R + a)) +
      Matrix.diagonal fun _ => (0 : ℝ)).map (↑) :
      Matrix (Fin (a + (R + a))) (Fin (a + (R + a))) ℂ) ≤ 1 := by
    rw [Matrix.diagonal_zero, add_zero]
    exact hermNegIndex_neutralWindow_le_one hR (by omega) hQ
  have h₂ : hermNegIndex ((neutralWindow Q (R + a) ((R + a) + b) +
      Matrix.diagonal fun _ => (0 : ℝ)).map (↑) :
      Matrix (Fin ((R + a) + b)) (Fin ((R + a) + b)) ℂ) ≤ 1 := by
    rw [Matrix.diagonal_zero, add_zero]
    exact hermNegIndex_neutralWindow_le_one hD (by omega) hQ
  have hX0 : ∀ (u : Fin a → ℝ) (v : Fin b → ℝ),
      (u ⬝ᵥ (overlapCouplingLevel Q R a b 0 *ᵥ v)) ^ 2 ≤ x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
    rw [overlapCouplingLevel_zero]
    exact hX
  have h := hermNegIndex_neutralWindow_add_le_one_of_parts (Q := Q) a b hR (C := 0) (x := x)
    (by norm_num) (by linarith [one_lt_bindingEnergy hD]) hx h₁ h₂ hX0
  rw [zero_add] at h
  exact h

/-! ### Refinement at a level -/

/-- The mass of a real vector on the blocks of a window. -/
theorem dotProduct_self_eq_sum_range_extendFin {J : ℕ} (z : Fin J → ℝ) :
    z ⬝ᵥ z = ∑ j ∈ range J, extendFin z j ^ 2 :=
  calc z ⬝ᵥ z = ∑ i, z i ^ 2 := Finset.sum_congr rfl fun i _ => (sq _).symm
    _ = ∑ j ∈ range J, extendFin (fun i => z i ^ 2) j := sum_fin_eq_sum_range_extendFin _
    _ = ∑ j ∈ range J, extendFin z j ^ 2 := Finset.sum_congr rfl fun j hj => by
        rw [extendFin, extendFin, dif_pos (Finset.mem_range.mp hj),
          dif_pos (Finset.mem_range.mp hj)]

/-- Refinement keeps the mass of a real-linear coordinate of a complex vector. -/
theorem dotProduct_complexRefine {m : ℕ} (hm : 1 ≤ m) (J : ℕ) (g : ℂ → ℝ) (hg0 : g 0 = 0)
    (hdiv : ∀ z : ℂ, g (z / (Real.sqrt m : ℂ)) = g z / Real.sqrt m) (c : Fin J → ℂ) :
    (fun i : Fin (m * J) => g (complexRefine m J c i)) ⬝ᵥ
        (fun i : Fin (m * J) => g (complexRefine m J c i)) =
      (fun i : Fin J => g (c i)) ⬝ᵥ fun i : Fin J => g (c i) := by
  rw [dotProduct_self_eq_sum_range_extendFin, dotProduct_self_eq_sum_range_extendFin,
    ← sum_refineStep_sq hm J (extendFin fun i : Fin J => g (c i))]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.mp hn
  congr 1
  rw [extendFin, dif_pos hn', refineStep]
  simp only [complexRefine, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hdiv]
  congr 1
  simp only [complexExtend, LinearMap.coe_mk, AddHom.coe_mk, extendFin]
  split_ifs <;> simp [hg0]

/-- **Refinement does not lower the index at a level**: the margin of a window is at most the
margin of its refinements. -/
theorem hermNegIndex_neutralWindow_add_le_refined {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m)
    (Q J : ℕ) (C : ℝ) :
    hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex ((neutralWindow Q (m * R) (m * J) + Matrix.diagonal fun _ => C).map (↑) :
        Matrix (Fin (m * J)) (Fin (m * J)) ℂ) := by
  refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_eq _ _ (complexRefine m J) fun c => ?_
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, HeckeKreinToeplitz.hermQuad_map_ofReal]
  simp only [dotProduct_add_diagonal_mulVec]
  rw [dotProduct_complexRefine hm J Complex.re (by simp) (fun z => Complex.div_ofReal_re z _) c,
    dotProduct_complexRefine hm J Complex.im (by simp) (fun z => Complex.div_ofReal_im z _) c,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum,
    neutralWindow, neutralWindow, sum_fin_windowMatrix_eq,
    sum_fin_windowMatrix_eq, sum_fin_windowMatrix_eq, sum_fin_windowMatrix_eq,
    sum_neutralBlock_complexRefine hR hm Q J Complex.re (by simp)
      (fun z => Complex.div_ofReal_re z _),
    sum_neutralBlock_complexRefine hR hm Q J Complex.im (by simp)
      (fun z => Complex.div_ofReal_im z _)]

/-! ### The Riemann hypothesis with a loss -/

theorem two_le_of_window_le {Q R J : ℕ} (hJ : 1 ≤ J) (hQ : R + J ≤ Q * R) :
    2 ≤ Q := by
  by_contra hlt
  have : Q * R ≤ 1 * R := Nat.mul_le_mul_right R (by omega)
  omega

/-- Under the Riemann hypothesis the Schur complement of the dyadic middle is nonnegative. -/
theorem overlapSchur_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {Q R a b : ℕ}
    (hR : 1 ≤ R) (hQ : R + (a + (R + a) + b) ≤ Q * R) (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) :=
  (hermNegIndex_neutralWindow_eq_one_iff_overlapSchur a b hR
    (two_le_of_window_le (by omega) hQ)).mp
    ((riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one.mp hRH) Q R
      (a + (R + a) + b) hR (by omega) hQ) e

/-- **The Riemann hypothesis is a uniform lower bound for the Schur complements of the dyadic
middles.** It holds iff for some `x` the form the two ends of every window `(R, 2(R + a) + b]`
with `R ≥ 34` see through the middle is at least `−x`. -/
theorem riemannHypothesis_iff_overlapSchur_bddBelow :
    RiemannHypothesis ↔ ∃ x : ℝ, ∀ Q R a b : ℕ, 34 ≤ R → 1 ≤ a → 1 ≤ b →
      R + (a + (R + a) + b) ≤ Q * R → ∀ e : Fin a ⊕ Fin b → ℝ,
        -x * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) := by
  constructor
  · intro hRH
    refine ⟨0, fun Q R a b hR _ _ hQ e => ?_⟩
    rw [neg_zero, zero_mul]
    exact overlapSchur_nonneg_of_riemannHypothesis hRH (by omega) hQ e
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy0, hxy⟩ : ∃ y : ℝ, 0 ≤ y ∧ x ≤ y :=
      ⟨max x 0, le_max_right _ _, le_max_left _ _⟩
    -- every window with `R ≥ 34` holds at most one bound state at level `y`
    have key : ∀ Q R J : ℕ, 34 ≤ R → R ≤ J → R + J ≤ Q * R →
        hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => y).map (↑) :
          Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
      intro Q R J hR hRJ hQ
      have hQ2 : 2 ≤ Q := two_le_of_window_le (by omega) hQ
      rcases Nat.lt_or_ge J (R + 3) with hJ | hJ
      · exact (hermNegIndex_add_diagonal_le (neutralWindow Q R J) hy0).trans
          (hermNegIndex_neutralWindow_eq_one (by omega) hRJ (by omega) hQ2).le
      · obtain ⟨c, rfl⟩ : ∃ c, J = 1 + (R + 1) + (c + 1) := ⟨J - R - 3, by omega⟩
        have hS : ∀ e : Fin 1 ⊕ Fin (c + 1) → ℝ,
            -y * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchurLevel Q R 1 (c + 1) 0 *ᵥ e) := by
          intro e
          rw [overlapSchurLevel_zero]
          have h1 := hx Q R 1 (c + 1) hR le_rfl (by omega) hQ e
          have h2 : 0 ≤ e ⬝ᵥ e := dotProduct_self_star_nonneg (v := e)
          nlinarith [mul_nonneg (sub_nonneg.mpr hxy) h2]
        have h := hermNegIndex_neutralWindow_add_le_one_of_schurLevel (Q := Q) 1 (c + 1)
          (by omega : 1 ≤ R) (C := 0) (x := y) (by norm_num)
          (by linarith [one_lt_bindingEnergy (D := R + 1) (by omega)]) hy0 hS
        rw [zero_add] at h
        exact h
    rw [riemannHypothesis_iff_neutralWindow_margin_bddBelow]
    refine ⟨y, fun Q R J hR hRJ hQ => ?_⟩
    exact (hermNegIndex_neutralWindow_add_le_refined hR (m := 34) (by norm_num) Q J y).trans
      (key Q (34 * R) (34 * J) (by omega) (by omega) (by nlinarith [hQ]))

/-- **The Riemann hypothesis is the nonnegativity of the Schur complements of the dyadic
middles.** -/
theorem riemannHypothesis_iff_forall_overlapSchur_nonneg :
    RiemannHypothesis ↔ ∀ Q R a b : ℕ, 34 ≤ R → 1 ≤ a → 1 ≤ b →
      R + (a + (R + a) + b) ≤ Q * R → ∀ e : Fin a ⊕ Fin b → ℝ,
        0 ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) := by
  constructor
  · intro hRH Q R a b hR _ _ hQ e
    exact overlapSchur_nonneg_of_riemannHypothesis hRH (by omega) hQ e
  · intro h
    refine riemannHypothesis_iff_overlapSchur_bddBelow.mpr ⟨0, fun Q R a b hR ha hb hQ e => ?_⟩
    rw [neg_zero, zero_mul]
    exact h Q R a b hR ha hb hQ e

/-- **The Schur complement of the middle is the neutral form on the vectors that are harmonic
on the middle.** -/
theorem overlapSchur_form_eq_harmonic (Q R a b : ℕ) (hD : 1 ≤ R + a) {m : Fin (R + a) → ℝ}
    {e : Fin a ⊕ Fin b → ℝ}
    (hme : primeFreeMiddle (R + a) *ᵥ m + endCoupling Q R a b *ᵥ e = 0) :
    Sum.elim m e ⬝ᵥ (fromBlocks (primeFreeMiddle (R + a)) (endCoupling Q R a b)
        (endCoupling Q R a b)ᵀ (endForm Q R a b) *ᵥ Sum.elim m e) =
      e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) := by
  have h := oneBoundState_primeFreeMiddle hD
  have hm : m + (primeFreeMiddle (R + a))⁻¹ *ᵥ (endCoupling Q R a b *ᵥ e) = 0 := by
    have h1 : (primeFreeMiddle (R + a))⁻¹ *ᵥ
        (primeFreeMiddle (R + a) *ᵥ m + endCoupling Q R a b *ᵥ e) = 0 := by
      rw [hme, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_add, h.inv_mulVec_mulVec] at h1
  rw [dotProduct_fromBlocks_mulVec_eq_schur h.symm h.isUnit, hm, Matrix.mulVec_zero,
    dotProduct_zero, zero_add]
  rfl

/-- **The Riemann hypothesis on harmonic vectors.** It holds iff on every window
`(R, 2(R + a) + b]` with `R ≥ 34`, written in the blocks of its dyadic middle and its two ends,
the neutral form is nonnegative on the vectors `(m, e)` that are harmonic on the middle. -/
theorem riemannHypothesis_iff_forall_harmonic_nonneg :
    RiemannHypothesis ↔ ∀ Q R a b : ℕ, 34 ≤ R → 1 ≤ a → 1 ≤ b →
      R + (a + (R + a) + b) ≤ Q * R → ∀ (m : Fin (R + a) → ℝ) (e : Fin a ⊕ Fin b → ℝ),
        primeFreeMiddle (R + a) *ᵥ m + endCoupling Q R a b *ᵥ e = 0 →
          0 ≤ Sum.elim m e ⬝ᵥ (fromBlocks (primeFreeMiddle (R + a)) (endCoupling Q R a b)
            (endCoupling Q R a b)ᵀ (endForm Q R a b) *ᵥ Sum.elim m e) := by
  rw [riemannHypothesis_iff_forall_overlapSchur_nonneg]
  constructor
  · intro h Q R a b hR ha hb hQ m e hme
    rw [overlapSchur_form_eq_harmonic Q R a b (by omega) hme]
    exact h Q R a b hR ha hb hQ e
  · intro h Q R a b hR ha hb hQ e
    have hD : 1 ≤ R + a := by omega
    have hme : primeFreeMiddle (R + a) *ᵥ
        (-(greenMatrix (R + a) *ᵥ (endCoupling Q R a b *ᵥ e))) +
        endCoupling Q R a b *ᵥ e = 0 := by
      rw [Matrix.mulVec_neg, greenMatrix, (oneBoundState_primeFreeMiddle hD).mulVec_inv_mulVec,
        neg_add_cancel]
    rw [← overlapSchur_form_eq_harmonic Q R a b hD hme]
    exact h Q R a b hR ha hb hQ _ _ hme

/-- **The Riemann hypothesis from a loss that sums below the binding energy.** Let `L` assign a
level in `[0, 1]` to every window, such that every window `(R, R + J]` with `R ≥ 34` and
`J ≥ R + 3` splits as `(R, 2(R + a) + b]` with a level `C` between the levels of its two parts
and its own, at which the conditional coupling has norm at most `L − C`. Then every window holds
at most one bound state at its level, and the Riemann hypothesis follows. -/
theorem riemannHypothesis_of_level_function (L : ℕ → ℕ → ℕ → ℝ)
    (hL0 : ∀ Q R J, 0 ≤ L Q R J) (hL1 : ∀ Q R J, L Q R J ≤ 1)
    (hstep : ∀ Q R J : ℕ, 34 ≤ R → R + 3 ≤ J → R + J ≤ Q * R →
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ J = a + (R + a) + b ∧ ∃ C : ℝ,
        L Q R (a + (R + a)) ≤ C ∧ L Q (R + a) ((R + a) + b) ≤ C ∧ C ≤ L Q R J ∧
          ∀ (u : Fin a → ℝ) (v : Fin b → ℝ),
            (u ⬝ᵥ (overlapCouplingLevel Q R a b C *ᵥ v)) ^ 2 ≤
              (L Q R J - C) ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v))) :
    RiemannHypothesis := by
  have key : ∀ J Q R : ℕ, 34 ≤ R → R ≤ J → R + J ≤ Q * R →
      hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => L Q R J).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
    intro J
    induction J using Nat.strong_induction_on with
    | _ J ih =>
      intro Q R hR hRJ hQ
      have hQ2 : 2 ≤ Q := two_le_of_window_le (by omega) hQ
      rcases Nat.lt_or_ge J (R + 3) with hJ | hJ
      · exact (hermNegIndex_add_diagonal_le (neutralWindow Q R J) (hL0 Q R J)).trans
          (hermNegIndex_neutralWindow_eq_one (by omega) hRJ (by omega) hQ2).le
      · obtain ⟨a, b, ha, hb, rfl, C, hC₁, hC₂, hCL, hX⟩ := hstep Q R J hR hJ hQ
        have h₁ := (hermNegIndex_add_diagonal_mono (neutralWindow Q R (a + (R + a))) hC₁).trans
          (ih (a + (R + a)) (by omega) Q R hR (by omega) (by omega))
        have h₂ := (hermNegIndex_add_diagonal_mono
          (neutralWindow Q (R + a) ((R + a) + b)) hC₂).trans
          (ih ((R + a) + b) (by omega) Q (R + a) (by omega) (by omega)
            (le_trans (by omega) (Nat.mul_le_mul_left Q (Nat.le_add_right R a))))
        have hμ := one_lt_bindingEnergy (D := R + a) (by omega)
        have h := hermNegIndex_neutralWindow_add_le_one_of_parts (Q := Q) a b (by omega : 1 ≤ R)
          (by linarith [hL0 Q R (a + (R + a))] : -(1 / 5000 : ℝ) < C)
          (by linarith [hL1 Q R (a + (R + a) + b)]) (sub_nonneg.mpr hCL) h₁ h₂ hX
        rw [show C + (L Q R (a + (R + a) + b) - C) = L Q R (a + (R + a) + b) by ring] at h
        exact h
  rw [riemannHypothesis_iff_neutralWindow_margin_bddBelow]
  refine ⟨1, fun Q R J hR hRJ hQ => ?_⟩
  exact (hermNegIndex_neutralWindow_add_le_refined hR (m := 34) (by norm_num) Q J 1).trans
    ((hermNegIndex_add_diagonal_mono _ (hL1 Q (34 * R) (34 * J))).trans
      (key (34 * J) Q (34 * R) (by omega) (by omega) (by nlinarith [hQ])))

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
