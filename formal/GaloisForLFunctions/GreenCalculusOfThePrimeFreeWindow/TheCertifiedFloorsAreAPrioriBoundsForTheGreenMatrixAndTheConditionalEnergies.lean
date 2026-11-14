import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.ChargeCancellationPreservesTheCertifiedFloor

/-!
# The certified floors are a priori bounds for the Green matrix and the conditional energies

The floor `1/5000` of the neutral part on charge-free packets, certified for the windows
`(R, R + J]` with `50 J ≤ 53 R` at every block size, is turned into bounds for the objects of
the Green calculus.

* **Two-sided bounds of the inverse** (`OneBoundState.inv_form_le`, `OneBoundState.inv_form_ge`):
  a matrix with one bound state of depth `μ` and floor `c` has `−1/μ ⪯ M⁻¹ ⪯ 1/c`. For the
  dyadic middle `−1 ⪯ G_D ⪯ 5000` at every block size (`greenMatrix_form_ge`,
  `greenMatrix_form_le`).
* **One bound state with a floor on the certified range**
  (`exists_oneBoundState_neutralWindow`): for `R ≤ J`, `50 J ≤ 53 R` the neutral part has a
  positive ground vector of negative eigenvalue and is at least `1/5000` on its orthogonal
  complement: the second eigenvalue is at least `1/5000`.
* **The first overlap step** (`overlapLeftEnergy_floor`, `overlapRightEnergy_floor`,
  `overlapSchur_ge_of_firstStep`): for `a ≤ 3R/100`, `b ≤ 3(R + a)/50` both parts lie in the
  certified range, so by charge cancellation both conditional energies are at least `1/5000`,
  and the Schur complement of the middle is at least `1/5000 − ‖X‖`. A conditional coupling of
  norm at most `1/5000` gives one bound state
  (`hermNegIndex_neutralWindow_eq_one_of_firstStep_coupling_le`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

section Bounds

variable {ι ι' α β : Type*} [Fintype ι] [Fintype ι'] [Fintype α] [Fintype β]

/-- The form of a reindexed matrix. -/
theorem dotProduct_submatrix_mulVec_equiv (A : Matrix ι ι ℝ) (e : ι' ≃ ι) (y : ι' → ℝ) :
    y ⬝ᵥ (A.submatrix e e *ᵥ y) = (y ∘ e.symm) ⬝ᵥ (A *ᵥ (y ∘ e.symm)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Function.comp_apply]
  refine Eq.trans ?_ (Equiv.sum_comp e fun i => y (e.symm i) * ∑ j, A i j * y (e.symm j))
  refine Finset.sum_congr rfl fun i _ => ?_
  show y i * ∑ j, A (e i) (e j) * y j = y (e.symm (e i)) * ∑ j, A (e i) j * y (e.symm j)
  rw [Equiv.symm_apply_apply, ← Equiv.sum_comp e fun j => A (e i) j * y (e.symm j)]
  simp only [Equiv.symm_apply_apply]

/-- A floor on the charge-free vectors is kept by a reindexing. -/
theorem floor_submatrix_equiv {A : Matrix ι ι ℝ} {c : ℝ}
    (hA : ∀ z : ι → ℝ, ∑ i, z i = 0 → c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (A *ᵥ z)) (e : ι' ≃ ι)
    (y : ι' → ℝ) (hy : (fun _ => (1 : ℝ)) ⬝ᵥ y = 0) :
    c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A.submatrix e e *ᵥ y) := by
  have h0 : ∑ i, y i = 0 := by simpa [dotProduct] using hy
  have hsum : ∑ i, (y ∘ e.symm) i = 0 := (Equiv.sum_comp e.symm y).trans h0
  have hnorm : (y ∘ e.symm) ⬝ᵥ (y ∘ e.symm) = y ⬝ᵥ y := by
    simp only [dotProduct, Function.comp_apply]
    exact Equiv.sum_comp e.symm fun i => y i * y i
  rw [dotProduct_submatrix_mulVec_equiv, ← hnorm]
  exact hA _ hsum

variable {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

/-- The component along the unit ground vector is at most the norm. -/
theorem OneBoundState.sq_dot_le (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    (φ ⬝ᵥ w) ^ 2 ≤ w ⬝ᵥ w := by
  have h1 := h.perp_dot_perp w
  have h2 : 0 ≤ OneBoundState.perp φ w ⬝ᵥ OneBoundState.perp φ w :=
    dotProduct_self_star_nonneg (v := OneBoundState.perp φ w)
  linarith

variable [DecidableEq ι] [DecidableEq α] [DecidableEq β]

/-- **The inverse of a matrix with one bound state is at most the inverse of its floor.** -/
theorem OneBoundState.inv_form_le (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    w ⬝ᵥ (M⁻¹ *ᵥ w) ≤ 1 / c * (w ⬝ᵥ w) := by
  rw [inv_form_eq_channels M φ μ w]
  have h1 := positiveChannel_le h w
  have h2 : 0 ≤ 1 / μ * (φ ⬝ᵥ w) ^ 2 :=
    mul_nonneg (one_div_nonneg.mpr h.depth_pos.le) (sq_nonneg _)
  have h3 : 1 / c * (w ⬝ᵥ w - (φ ⬝ᵥ w) ^ 2) ≤ 1 / c * (w ⬝ᵥ w) :=
    mul_le_mul_of_nonneg_left (by linarith [sq_nonneg (φ ⬝ᵥ w)])
      (one_div_nonneg.mpr h.floor_pos.le)
  linarith

/-- **The inverse of a matrix with one bound state is at least minus the inverse of its
depth.** -/
theorem OneBoundState.inv_form_ge (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    -(1 / μ) * (w ⬝ᵥ w) ≤ w ⬝ᵥ (M⁻¹ *ᵥ w) := by
  rw [inv_form_eq_channels M φ μ w]
  have h1 := positiveChannel_nonneg h w
  have h2 : 1 / μ * (φ ⬝ᵥ w) ^ 2 ≤ 1 / μ * (w ⬝ᵥ w) :=
    mul_le_mul_of_nonneg_left (h.sq_dot_le w) (one_div_nonneg.mpr h.depth_pos.le)
  linarith

/-- A two-block form with diagonal blocks at least `c` and an off-diagonal block of norm at
most `x` is at least `c − x`. -/
theorem fromBlocks_form_ge_of_floors {E₁ : Matrix α α ℝ} {X : Matrix α β ℝ}
    {E₂ : Matrix β β ℝ} {c x : ℝ} (h₁ : ∀ u, c * (u ⬝ᵥ u) ≤ u ⬝ᵥ (E₁ *ᵥ u))
    (h₂ : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (E₂ *ᵥ v)) (hx : 0 ≤ x)
    (hX : ∀ u v, (u ⬝ᵥ (X *ᵥ v)) ^ 2 ≤ x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v))) (z : α ⊕ β → ℝ) :
    (c - x) * (z ⬝ᵥ z) ≤ z ⬝ᵥ (fromBlocks E₁ X Xᵀ E₂ *ᵥ z) := by
  have h := fromBlocks_form_ge_of_coupling_le (E₁ := E₁ + Matrix.diagonal fun _ => -c)
    (X := X) (E₂ := E₂ + Matrix.diagonal fun _ => -c)
    (fun u => by rw [dotProduct_add_diagonal_mulVec]; linarith [h₁ u])
    (fun v => by rw [dotProduct_add_diagonal_mulVec]; linarith [h₂ v]) hx hX z
  rw [← fromBlocks_add_diagonal_const, dotProduct_add_diagonal_mulVec] at h
  linarith

end Bounds

/-! ### The dyadic middle -/

/-- **The Green matrix of the dyadic middle is at most `5000`** at every block size. -/
theorem greenMatrix_form_le {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ (greenMatrix D *ᵥ w) ≤ 5000 * (w ⬝ᵥ w) := by
  have h := (oneBoundState_primeFreeMiddle hD).inv_form_le w
  rw [show (1 : ℝ) / (1 / 5000) = 5000 by norm_num] at h
  exact h

/-- **The Green matrix of the dyadic middle is at least `−1`** at every block size. -/
theorem greenMatrix_form_ge {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    -(w ⬝ᵥ w) ≤ w ⬝ᵥ (greenMatrix D *ᵥ w) := by
  have h : -(1 / bindingEnergy D) * (w ⬝ᵥ w) ≤ w ⬝ᵥ (greenMatrix D *ᵥ w) :=
    (oneBoundState_primeFreeMiddle hD).inv_form_ge w
  have hμ := one_lt_bindingEnergy hD
  have h1 : 1 / bindingEnergy D ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hμ.le
  have h2 : 0 ≤ w ⬝ᵥ w := dotProduct_self_star_nonneg (v := w)
  linarith [mul_nonneg (sub_nonneg.mpr h1) h2]

/-! ### The certified range -/

/-- **The certified floor**: on charge-free packets the neutral part of a window `(R, R + J]`
with `50 J ≤ 53 R` is at least `1/5000`. -/
theorem neutralWindow_floor_of_sum_eq_zero {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 50 * J ≤ 53 * R)
    (hQ : 2 ≤ Q) (z : Fin J → ℝ) (hz : ∑ i, z i = 0) :
    1 / 5000 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) := by
  rw [AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, neutralWindow, sum_fin_windowMatrix_eq,
    dotProduct_self_eq_sum_range_extendFin]
  exact sum_neutralBlock_ge_of_short hR hJ hQ
    (Or.inl ((sum_fin_eq_sum_range_extendFin z).symm.trans hz))

/-- **Every window of the certified range has one bound state with floor `1/5000`**: for
`R ≤ J`, `50 J ≤ 53 R` the neutral part has a positive ground vector of negative eigenvalue and
its second eigenvalue is at least `1/5000`. -/
theorem exists_oneBoundState_neutralWindow {Q R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hJ : 50 * J ≤ 53 * R) (hQ : 2 ≤ Q) :
    ∃ ψ : Fin J → ℝ, ∃ ν : ℝ, (∀ i, 0 < ψ i) ∧
      OneBoundState (neutralWindow Q R J) ψ ν (1 / 5000) := by
  obtain ⟨φ₀, hφ₀, lam, heig⟩ := exists_groundVector_neutralWindow Q R (by omega : 1 ≤ J)
  haveI : Nonempty (Fin J) := ⟨⟨0, by omega⟩⟩
  obtain ⟨ψ, hψ, h⟩ := exists_oneBoundState_of_pos_eigenvector (neutralWindow_symm Q R J) hφ₀
    (eigenvalue_neg_of_pos_eigenvector Q hR hRJ hφ₀ heig) heig
    (by norm_num : (0 : ℝ) < 1 / 5000) (neutralWindow_floor_of_sum_eq_zero hR hJ hQ)
  exact ⟨ψ, -lam, hψ, h⟩

/-! ### The first overlap step -/

/-- The charge of the ground vector of the middle does not vanish. -/
theorem charge_groundVector_ne_zero {κ : Type*} {D : ℕ} (hD : 1 ≤ D) :
    ((fun _ : Fin D ⊕ κ => (1 : ℝ)) ∘ Sum.inl) ⬝ᵥ groundVector D ≠ 0 := by
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hp : 0 < ∑ i, groundVector D i :=
    Finset.sum_pos (fun i _ => (groundPair_spec hD).1 i) Finset.univ_nonempty
  simpa only [dotProduct, Function.comp_apply, one_mul] using hp.ne'

/-- **The conditional energy of the left end is at least `1/5000`** when the left part
`(R, 2(R + a)]` lies in the certified range: the charge of an end is cancelled on the ground
vector of the middle. -/
theorem overlapLeftEnergy_floor {Q R a : ℕ} (hR : 1 ≤ R) (ha : 100 * a ≤ 3 * R) (hQ : 2 ≤ Q)
    (u : Fin a → ℝ) : 1 / 5000 * (u ⬝ᵥ u) ≤ u ⬝ᵥ (overlapLeftEnergy Q R a *ᵥ u) := by
  have hD : 1 ≤ R + a := by omega
  have h := schur_floor_of_charge_cancellation (oneBoundState_primeFreeMiddle hD)
    (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))
    (posMatrix (neutralBlock Q) (leftPos R a) (leftPos R a)) (fun _ => (1 : ℝ))
    (charge_groundVector_ne_zero hD) (by norm_num : (0 : ℝ) ≤ 1 / 5000)
    (fun y hy => by
      rw [← neutralWindow_dyadic_eq Q, ← neutralWindow_submatrix_leftPartEquiv]
      exact floor_submatrix_equiv (neutralWindow_floor_of_sum_eq_zero hR (by omega) hQ) _ y hy)
    u
  rw [overlapLeftEnergy, neutralWindow_dyadic_eq]
  exact h

/-- **The conditional energy of the right end is at least `1/5000`** when the right part
`(R + a, 2(R + a) + b]` lies in the certified range. -/
theorem overlapRightEnergy_floor {Q R a b : ℕ} (hR : 1 ≤ R) (hb : 50 * b ≤ 3 * (R + a))
    (hQ : 2 ≤ Q) (v : Fin b → ℝ) :
    1 / 5000 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (overlapRightEnergy Q R a b *ᵥ v) := by
  have hD : 1 ≤ R + a := by omega
  have h := schur_floor_of_charge_cancellation (oneBoundState_primeFreeMiddle hD)
    (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))
    (posMatrix (neutralBlock Q) (rightPos R a b) (rightPos R a b)) (fun _ => (1 : ℝ))
    (charge_groundVector_ne_zero hD) (by norm_num : (0 : ℝ) ≤ 1 / 5000)
    (fun y hy => by
      rw [← neutralWindow_dyadic_eq Q, ← neutralWindow_submatrix_rightPart Q R a b]
      exact floor_submatrix_equiv (neutralWindow_floor_of_sum_eq_zero hD (by omega) hQ) _ y hy)
    v
  rw [overlapRightEnergy, neutralWindow_dyadic_eq]
  exact h

/-- **The Schur complement of the middle at the first overlap step is at least
`1/5000 − ‖X‖`**, with `X` the conditional coupling of the two ends. -/
theorem overlapSchur_ge_of_firstStep {Q R a b : ℕ} (hR : 1 ≤ R) (ha : 100 * a ≤ 3 * R)
    (hb : 50 * b ≤ 3 * (R + a)) (hQ : 2 ≤ Q) {x : ℝ} (hx : 0 ≤ x)
    (hX : ∀ (u : Fin a → ℝ) (v : Fin b → ℝ),
      (u ⬝ᵥ (overlapCoupling Q R a b *ᵥ v)) ^ 2 ≤ x ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v)))
    (e : Fin a ⊕ Fin b → ℝ) :
    (1 / 5000 - x) * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) := by
  rw [overlapSchur_eq_fromBlocks]
  exact fromBlocks_form_ge_of_floors (overlapLeftEnergy_floor hR ha hQ)
    (overlapRightEnergy_floor hR hb hQ) hx hX e

/-- **A window of the first overlap step whose conditional coupling has norm at most `1/5000`
holds exactly one bound state.** -/
theorem hermNegIndex_neutralWindow_eq_one_of_firstStep_coupling_le {Q R a b : ℕ} (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (hQ : 2 ≤ Q)
    (hX : ∀ (u : Fin a → ℝ) (v : Fin b → ℝ),
      (u ⬝ᵥ (overlapCoupling Q R a b *ᵥ v)) ^ 2 ≤
        (1 / 5000 : ℝ) ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v))) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 := by
  refine (hermNegIndex_neutralWindow_eq_one_iff_overlapSchur a b hR hQ).mpr fun e => ?_
  have h := overlapSchur_ge_of_firstStep hR ha hb hQ (by norm_num : (0 : ℝ) ≤ 1 / 5000) hX e
  rwa [sub_self, zero_mul] at h

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
