import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsCarriedByItsFloorTrees

/-!
# The certified floors are a priori bounds for the Green matrix and the conditional energies

The floor `1/5000` of the neutral part on charge-free packets, certified for the windows
`(R, R + J]` with `50 J ≤ 53 R` at every block size, is turned into bounds for the objects of
the Green calculus.

* **Two-sided bounds of the inverse** (`OneBoundState.inv_form_le`, `OneBoundState.inv_form_ge`):
  a matrix with one bound state of depth `μ` and floor `c` has `−1/μ ⪯ M⁻¹ ⪯ 1/c`. For the
  dyadic middle `−1 ⪯ G_D ⪯ 5000` at every block size (`greenMatrix_form_ge`,
  `greenMatrix_form_le`), and its binding energy lies in `(1, γ + π/2 + log 8π]`
  (`one_lt_bindingEnergy`, `bindingEnergy_le`).
* **One bound state with a floor on the certified range**
  (`exists_oneBoundState_neutralWindow`): for `R ≤ J`, `50 J ≤ 53 R` the neutral part has a
  positive ground vector of negative eigenvalue and is at least `1/5000` on its orthogonal
  complement: the second eigenvalue is at least `1/5000`.
* **The conditional energy inherits the floors** (`schur_floor_of_floor_hyperplane`): if the
  middle has one bound state with floor `c` and the part is at least `c'` on a hyperplane, the
  Schur complement of the middle is at least `min c c'`. The part still holds at most one bound
  state at every level `−t > −min c c'`, so the Schur complement at that level is nonnegative,
  and it grows at unit speed in the level.
* **The first overlap step** (`overlapLeftEnergy_floor`, `overlapRightEnergy_floor`,
  `overlapSchur_ge_of_firstStep`): for `a ≤ 3R/100`, `b ≤ 3(R + a)/50` both conditional
  energies are at least `1/5000`, and the Schur complement of the middle is at least
  `1/5000 − ‖X‖`. A conditional coupling of norm at most `1/5000` gives one bound state
  (`hermNegIndex_neutralWindow_eq_one_of_firstStep_coupling_le`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-- A bound `t q ≤ S` for every `t` below `m` is the bound at `m`. -/
theorem le_of_forall_lt_mul {m q S : ℝ} (hm : 0 < m) (hq : 0 ≤ q)
    (h : ∀ t, 0 < t → t < m → t * q ≤ S) : m * q ≤ S := by
  by_contra hlt
  rw [not_le] at hlt
  have hS0 : 0 ≤ S :=
    le_trans (mul_nonneg (half_pos hm).le hq) (h (m / 2) (half_pos hm) (half_lt_self hm))
  have hq0 : 0 < q := by
    rcases hq.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hlt
      linarith
    · exact h0
  have hSq : S / q < m := by rwa [div_lt_iff₀ hq0]
  have hSq0 : 0 ≤ S / q := div_nonneg hS0 hq0.le
  have ht := h ((m + S / q) / 2) (by linarith) (by linarith)
  have hc : S / q * q = S := div_mul_cancel₀ S hq0.ne'
  nlinarith

section Bounds

variable {ι ι' κ α β : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype α] [Fintype β]

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

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α] [DecidableEq β]

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

/-- **The conditional energy inherits the floors.** If the middle has one bound state with
floor `c` and the part is at least `c'` on a hyperplane, the Schur complement of the middle is
at least `min c c'`. -/
theorem schur_floor_of_floor_hyperplane {A : Matrix ι ι ℝ} (h : OneBoundState A φ μ c)
    (P : Matrix ι κ ℝ) {N : Matrix κ κ ℝ} (hN : ∀ i j, N i j = N j i) {ℓ : ι ⊕ κ → ℝ}
    {c' : ℝ} (hc' : 0 < c')
    (hfloor : ∀ y : ι ⊕ κ → ℝ, ℓ ⬝ᵥ y = 0 →
      c' * (y ⬝ᵥ y) ≤ y ⬝ᵥ (fromBlocks A P Pᵀ N *ᵥ y)) (e : κ → ℝ) :
    min c c' * (e ⬝ᵥ e) ≤ e ⬝ᵥ ((N - Pᵀ * A⁻¹ * P) *ᵥ e) := by
  refine le_of_forall_lt_mul (lt_min h.floor_pos hc') (dotProduct_self_star_nonneg (v := e))
    fun t ht0 htm => ?_
  have htc : t < c := lt_of_lt_of_le htm (min_le_left _ _)
  have htc' : t < c' := lt_of_lt_of_le htm (min_le_right _ _)
  -- at the level `−t` the part still holds at most one bound state
  have hA := h.add_diagonal (C := -t) (by linarith [h.depth_pos]) (by linarith)
  have hidx : hermNegIndex ((fromBlocks (A + Matrix.diagonal fun _ => -t) P Pᵀ
      (N + Matrix.diagonal fun _ => -t)).map (↑) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) ≤ 1 := by
    rw [← fromBlocks_add_diagonal_const]
    refine hermNegIndex_le_one_of_nonneg_on_hyperplane _ ℓ fun y hy => ?_
    rw [dotProduct_add_diagonal_mulVec]
    have h1 := hfloor y hy
    have h2 : 0 ≤ y ⬝ᵥ y := dotProduct_self_star_nonneg (v := y)
    linarith [mul_nonneg (sub_nonneg.mpr htc'.le) h2]
  have hS := schur_nonneg_of_hermNegIndex_le_one hA P (symm_add_diagonal hN (-t)) hidx e
  -- the Schur complement grows at unit speed from the level `−t` to the level `0`
  have hmono := schur_add_diagonal_mono h P N (C := -t) (C' := 0) (by linarith) h.depth_pos
    (by linarith) e
  simp only [Matrix.diagonal_zero, add_zero] at hmono
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

/-- **The binding energy of the dyadic middle is at most `γ + π/2 + log 8π`** at every block
size: the middle carries no floor tree. -/
theorem bindingEnergy_le {D : ℕ} (hD : 1 ≤ D) :
    bindingEnergy D ≤
      Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi) := by
  have h := le_eigenvalue_of_prime_free hD hD (groundPair_spec hD).1
    (oneBoundState_primeFreeMiddle hD).eig
  have h0 := neg_gammaBracket_zero
  linarith

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

/-- **The conditional energy of the left end is at least `1/5000`** when the left part
`(R, 2(R + a)]` lies in the certified range. -/
theorem overlapLeftEnergy_floor {Q R a : ℕ} (hR : 1 ≤ R) (ha : 100 * a ≤ 3 * R) (hQ : 2 ≤ Q)
    (u : Fin a → ℝ) : 1 / 5000 * (u ⬝ᵥ u) ≤ u ⬝ᵥ (overlapLeftEnergy Q R a *ᵥ u) := by
  have hfl : ∀ y : Fin (R + a) ⊕ Fin a → ℝ, (fun _ => (1 : ℝ)) ⬝ᵥ y = 0 →
      1 / 5000 * (y ⬝ᵥ y) ≤ y ⬝ᵥ (fromBlocks (primeFreeMiddle (R + a))
        (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))
        (posMatrix (neutralBlock Q) (middlePos R a) (leftPos R a))ᵀ
        (posMatrix (neutralBlock Q) (leftPos R a) (leftPos R a)) *ᵥ y) := by
    intro y hy
    rw [← neutralWindow_dyadic_eq Q, ← neutralWindow_submatrix_leftPartEquiv]
    exact floor_submatrix_equiv (neutralWindow_floor_of_sum_eq_zero hR (by omega) hQ) _ y hy
  have h := schur_floor_of_floor_hyperplane
    (oneBoundState_primeFreeMiddle (by omega : 1 ≤ R + a)) _
    (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) (by norm_num : (0 : ℝ) < 1 / 5000)
    hfl u
  rw [min_self] at h
  rw [overlapLeftEnergy, neutralWindow_dyadic_eq]
  exact h

/-- **The conditional energy of the right end is at least `1/5000`** when the right part
`(R + a, 2(R + a) + b]` lies in the certified range. -/
theorem overlapRightEnergy_floor {Q R a b : ℕ} (hR : 1 ≤ R) (hb : 50 * b ≤ 3 * (R + a))
    (hQ : 2 ≤ Q) (v : Fin b → ℝ) :
    1 / 5000 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (overlapRightEnergy Q R a b *ᵥ v) := by
  have hfl : ∀ y : Fin (R + a) ⊕ Fin b → ℝ, (fun _ => (1 : ℝ)) ⬝ᵥ y = 0 →
      1 / 5000 * (y ⬝ᵥ y) ≤ y ⬝ᵥ (fromBlocks (primeFreeMiddle (R + a))
        (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))
        (posMatrix (neutralBlock Q) (middlePos R a) (rightPos R a b))ᵀ
        (posMatrix (neutralBlock Q) (rightPos R a b) (rightPos R a b)) *ᵥ y) := by
    intro y hy
    rw [← neutralWindow_dyadic_eq Q, ← neutralWindow_submatrix_rightPart Q R a b]
    exact floor_submatrix_equiv
      (neutralWindow_floor_of_sum_eq_zero (by omega) (by omega) hQ) _ y hy
  have h := schur_floor_of_floor_hyperplane
    (oneBoundState_primeFreeMiddle (by omega : 1 ≤ R + a)) _
    (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b))
    (by norm_num : (0 : ℝ) < 1 / 5000) hfl v
  rw [min_self] at h
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
