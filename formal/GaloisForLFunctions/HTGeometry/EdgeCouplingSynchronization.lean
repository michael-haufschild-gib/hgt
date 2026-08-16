import GaloisForLFunctions.HTGeometry.CrossProductSynchronization

/-!
# Synchronization of consecutive edge couplings

If the rows of one invertible coupling and the columns of the next are cross-multiplied against the
corresponding rows and columns of a second pair of couplings and the two products agree, then the
second pair is a common scalar multiple of the first.  Invertibility turns the basis relation into
the cross-product synchronization identity, whose only solutions are scalar.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem mulVec_transpose_eq_sum_rows (J : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) :
    Jᵀ *ᵥ u = ∑ a : Fin 3, u a • (fun b => J a b) := by
  funext b
  rw [Matrix.mulVec, dotProduct]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem mulVec_eq_sum_cols (J : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    J *ᵥ w = ∑ e : Fin 3, w e • (fun d => J d e) := by
  funext d
  rw [Matrix.mulVec, dotProduct]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- **Consecutive edge couplings synchronize.** -/
theorem exists_scalar_of_row_col_cross (Jv Jv1 Lv Lv1 : Matrix (Fin 3) (Fin 3) ℝ)
    (hJv : IsUnit Jv.det) (hJv1 : IsUnit Jv1.det)
    (hrel : ∀ a e : Fin 3,
      crossProduct (fun b => Jv a b) (fun d => Lv1 d e) =
        crossProduct (fun b => Lv a b) (fun d => Jv1 d e)) :
    ∃ lam : ℝ, Lv = lam • Jv ∧ Lv1 = lam • Jv1 := by
  classical
  have hJvT : IsUnit (Jvᵀ).det := by
    rw [Matrix.det_transpose]
    exact hJv
  have hbil : ∀ u w : Fin 3 → ℝ,
      crossProduct (Jvᵀ *ᵥ u) (Lv1 *ᵥ w) = crossProduct (Lvᵀ *ᵥ u) (Jv1 *ᵥ w) := by
    intro u w
    have expand : ∀ M N : Matrix (Fin 3) (Fin 3) ℝ,
        crossProduct (Mᵀ *ᵥ u) (N *ᵥ w) =
          ∑ a : Fin 3, ∑ e : Fin 3, (u a * w e) •
            crossProduct (fun b => M a b) (fun d => N d e) := by
      intro M N
      have step1 : crossProduct (Mᵀ *ᵥ u) (N *ᵥ w)
          = ∑ e : Fin 3, w e • crossProduct (Mᵀ *ᵥ u) (fun d => N d e) := by
        rw [mulVec_eq_sum_cols N w, map_sum]
        exact Finset.sum_congr rfl fun e _ =>
          LinearMap.map_smul (crossProduct (Mᵀ *ᵥ u)) (w e) (fun d => N d e)
      have step2 : ∀ e : Fin 3, crossProduct (Mᵀ *ᵥ u) (fun d => N d e)
          = ∑ a : Fin 3, u a • crossProduct (fun b => M a b) (fun d => N d e) := by
        intro e
        rw [mulVec_transpose_eq_sum_rows M u, map_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun a _ => by rw [map_smul, LinearMap.smul_apply]
      rw [step1]
      simp only [step2, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
        rw [mul_comm (w e) (u a)]
    rw [expand Jv Lv1, expand Lv Jv1]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by rw [hrel a e]
  set A : Matrix (Fin 3) (Fin 3) ℝ := Lvᵀ * (Jvᵀ)⁻¹ with hA
  set B : Matrix (Fin 3) (Fin 3) ℝ := Lv1 * Jv1⁻¹ with hB
  have hAJ : A * Jvᵀ = Lvᵀ := by
    rw [hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJvT, Matrix.mul_one]
  have hBJ : B * Jv1 = Lv1 := by
    rw [hB, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJv1, Matrix.mul_one]
  have hsync : ∀ x y : Fin 3 → ℝ,
      crossProduct x (B *ᵥ y) = crossProduct (A *ᵥ x) y := by
    intro x y
    have hx : Jvᵀ *ᵥ ((Jvᵀ)⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJvT, Matrix.one_mulVec]
    have hy : Jv1 *ᵥ (Jv1⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJv1, Matrix.one_mulVec]
    have hBy : B *ᵥ y = Lv1 *ᵥ (Jv1⁻¹ *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hB]
    have hAx : A *ᵥ x = Lvᵀ *ᵥ ((Jvᵀ)⁻¹ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hA]
    have hb := hbil ((Jvᵀ)⁻¹ *ᵥ x) (Jv1⁻¹ *ᵥ y)
    rw [hx, hy] at hb
    rw [hBy, hAx]
    exact hb
  obtain ⟨lam, hAlam, hBlam⟩ := eq_smul_one_of_cross_sync A B hsync
  refine ⟨lam, ?_, ?_⟩
  · have hLT : Lvᵀ = lam • Jvᵀ := by
      rw [← hAJ, hAlam, Matrix.smul_mul, Matrix.one_mul]
    have := congrArg Matrix.transpose hLT
    rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_transpose] at this
  · rw [← hBJ, hBlam, Matrix.smul_mul, Matrix.one_mul]


section Chain

/-- Consecutive synchronization scalars agree along a chain of nonzero couplings. -/
theorem chain_scalar_eq_zero (n : ℕ) (J L : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (lam : ℕ → ℝ)
    (hJne : ∀ v, v < n → J v ≠ 0)
    (h1 : ∀ v, v + 1 < n → L v = lam v • J v)
    (h2 : ∀ v, v + 1 < n → L (v + 1) = lam v • J (v + 1)) :
    ∀ v, v + 1 < n → lam v = lam 0 := by
  intro v
  induction v with
  | zero => intro _; rfl
  | succ v ih =>
      intro hlt
      have hv : v + 1 < n := by omega
      have hprev : lam v = lam 0 := ih hv
      have ha := h2 v hv
      have hb := h1 (v + 1) hlt
      have hzero : (lam v - lam (v + 1)) • J (v + 1) = 0 := by
        rw [sub_smul, ← ha, ← hb, sub_self]
      rcases smul_eq_zero.mp hzero with hc | hc
      · have : lam v = lam (v + 1) := by linarith [sub_eq_zero.mp hc]
        rw [← this, hprev]
      · exact absurd hc (hJne (v + 1) (by omega))

/-- **One scalar synchronizes the whole chain.** -/
theorem exists_common_scalar_of_chain (n : ℕ) (hn : 2 ≤ n)
    (J L : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (lam : ℕ → ℝ)
    (hJne : ∀ v, v < n → J v ≠ 0)
    (h1 : ∀ v, v + 1 < n → L v = lam v • J v)
    (h2 : ∀ v, v + 1 < n → L (v + 1) = lam v • J (v + 1)) :
    ∃ c : ℝ, ∀ v, v < n → L v = c • J v := by
  refine ⟨lam 0, fun v hv => ?_⟩
  by_cases hlast : v + 1 < n
  · rw [h1 v hlast, chain_scalar_eq_zero n J L lam hJne h1 h2 v hlast]
  · have hveq : v = n - 1 := by omega
    have hprev : (n - 2) + 1 < n := by omega
    have hstep := h2 (n - 2) hprev
    have hidx : n - 2 + 1 = v := by omega
    rw [hidx] at hstep
    rw [hstep, chain_scalar_eq_zero n J L lam hJne h1 h2 (n - 2) hprev]

end Chain

end GaloisForLFunctions.HTGeometry
