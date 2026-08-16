import GaloisForLFunctions.HTGeometry.EdgeCouplingSynchronization

/-!
# Field-rigid edge couplings

The local-field commutator map of an edge coupling sends a pair of site fields to the matrix whose
entries pair the coupling's columns and rows against the two fields through the cross product.  A
diagonal coupling with nonzero entries of pairwise distinct squares kills only the zero pair, and an
invertible coupling already kills only the zero field when the other field vanishes.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section CrossComponents

theorem fin3_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

theorem cross_apply_zero (x y : Fin 3 → ℝ) :
    (crossProduct x y) 0 = x 1 * y 2 - x 2 * y 1 := by
  simp [crossProduct]

theorem cross_apply_one (x y : Fin 3 → ℝ) :
    (crossProduct x y) 1 = x 2 * y 0 - x 0 * y 2 := by
  simp [crossProduct]

theorem cross_apply_two (x y : Fin 3 → ℝ) :
    (crossProduct x y) 2 = x 0 * y 1 - x 1 * y 0 := by
  simp [crossProduct]

end CrossComponents

/-- The local-field commutator map of an edge coupling. -/
def fieldMap (J : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun f q => crossProduct (fun p => J p q) a f + crossProduct (fun g => J f g) b q

/-- An edge coupling is field rigid when its local-field commutator map has trivial kernel. -/
def FieldRigid (J : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ a b : Fin 3 → ℝ, fieldMap J a b = 0 → a = 0 ∧ b = 0

section Diagonal

variable {d : Fin 3 → ℝ}

/-- **A generic diagonal coupling is field rigid.** -/
theorem fieldRigid_diagonal (hne : ∀ i j : Fin 3, i ≠ j → d i ^ 2 ≠ d j ^ 2) :
    FieldRigid (Matrix.diagonal d) := by
  intro a b hab
  have hentry : ∀ f q : Fin 3, fieldMap (Matrix.diagonal d) a b f q = 0 := by
    intro f q
    rw [hab]
    rfl
  have hdiag : ∀ p q : Fin 3, (Matrix.diagonal d) p q = if p = q then d p else 0 := by
    intro p q
    exact Matrix.diagonal_apply d p q
  have hpair : ∀ (f q r : Fin 3), f ≠ q →
      d q * a r = d f * b r → d f * a r = d q * b r → a r = 0 ∧ b r = 0 := by
    intro f q r hfq h1 h2
    have hdet : d f ^ 2 - d q ^ 2 ≠ 0 := by
      intro hc
      exact hne f q hfq (by linarith)
    constructor
    · have hza : (d f ^ 2 - d q ^ 2) * a r = 0 := by
        linear_combination (-(d q)) * h1 + (d f) * h2
      exact (mul_eq_zero.mp hza).resolve_left hdet
    · have hzb : (d f ^ 2 - d q ^ 2) * b r = 0 := by
        linear_combination (-(d f)) * h1 + (d q) * h2
      exact (mul_eq_zero.mp hzb).resolve_left hdet
  have e01 := hentry 0 1
  have e10 := hentry 1 0
  have e02 := hentry 0 2
  have e20 := hentry 2 0
  have e12 := hentry 1 2
  have e21 := hentry 2 1
  simp only [fieldMap, cross_apply_zero, cross_apply_one, cross_apply_two, hdiag] at e01 e10 e02 e20 e12 e21
  simp +decide at e01 e10 e02 e20 e12 e21
  obtain ⟨ha2, hb2⟩ := hpair 0 1 2 (by decide) (by linarith) (by linarith)
  obtain ⟨ha1, hb1⟩ := hpair 0 2 1 (by decide) (by linarith) (by linarith)
  obtain ⟨ha0, hb0⟩ := hpair 1 2 0 (by decide) (by linarith) (by linarith)
  constructor
  · funext r
    rcases fin3_cases r with rfl | rfl | rfl
    · exact ha0
    · exact ha1
    · exact ha2
  · funext r
    rcases fin3_cases r with rfl | rfl | rfl
    · exact hb0
    · exact hb1
    · exact hb2

end Diagonal

section Invertible

/-- A vector whose cross product with a fixed nonzero vector vanishes is a multiple of it. -/
theorem eq_smul_of_cross_eq_zero {u a : Fin 3 → ℝ} {i : Fin 3} (hai : a i ≠ 0)
    (h : crossProduct u a = 0) : ∀ p, u p * a i = u i * a p := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rw [cross_apply_zero] at h0
  rw [cross_apply_one] at h1
  rw [cross_apply_two] at h2
  intro p
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases p with rfl | rfl | rfl <;>
    simp only [Pi.zero_apply] at h0 h1 h2 <;> linarith

/-- **An invertible coupling kills only the zero field on the first slot.** -/
theorem eq_zero_of_cross_cols {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : IsUnit J.det) {a : Fin 3 → ℝ}
    (h : ∀ q, crossProduct (fun p => J p q) a = 0) : a = 0 := by
  by_contra hane
  obtain ⟨i, hai⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    exact hane (funext fun i => not_not.mp fun hc => hcon ⟨i, hc⟩)
  have hprop : ∀ p q, J p q * a i = J i q * a p := fun p q =>
    eq_smul_of_cross_eq_zero hai (h q) p
  obtain ⟨alpha, hJp⟩ : ∃ alpha : Fin 3 → ℝ, ∀ p q, J p q = alpha q * a p := by
    refine ⟨fun q => J i q / a i, fun p q => ?_⟩
    field_simp
    linarith [hprop p q]
  have hdet : J.det = 0 := by
    rw [Matrix.det_fin_three]
    simp only [hJp]
    ring
  rw [hdet] at hJ
  exact (not_isUnit_zero) hJ

/-- **An invertible coupling kills only the zero field on the second slot.** -/
theorem eq_zero_of_cross_rows {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : IsUnit J.det) {b : Fin 3 → ℝ}
    (h : ∀ f, crossProduct (fun g => J f g) b = 0) : b = 0 := by
  refine eq_zero_of_cross_cols (J := Jᵀ) ?_ ?_
  · rw [Matrix.det_transpose]
    exact hJ
  · intro q
    exact h q

end Invertible


section Propagation

theorem cross_rows_eq_zero_of_fieldMap {J : Matrix (Fin 3) (Fin 3) ℝ} {b : Fin 3 → ℝ}
    (h : fieldMap J 0 b = 0) : ∀ f, crossProduct (fun g => J f g) b = 0 := by
  intro f
  funext q
  have hfq : fieldMap J 0 b f q = 0 := by
    rw [h]
    rfl
  rw [fieldMap, map_zero] at hfq
  simpa using hfq

theorem cross_cols_eq_zero_of_fieldMap {J : Matrix (Fin 3) (Fin 3) ℝ} {a : Fin 3 → ℝ}
    (h : fieldMap J a 0 = 0) : ∀ q, crossProduct (fun p => J p q) a = 0 := by
  intro q
  funext f
  have hfq : fieldMap J a 0 f q = 0 := by
    rw [h]
    rfl
  rw [fieldMap, map_zero] at hfq
  simpa using hfq

/-- **A single field-rigid edge kills every site field along an invertible chain.** -/
theorem all_field_zero_of_chain (n : ℕ) (J : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℕ → (Fin 3 → ℝ)) (hJ : ∀ v, v < n → IsUnit (J v).det)
    (hzero : ∀ v, v < n → fieldMap (J v) (r v) (r (v + 1)) = 0)
    (q : ℕ) (hqn : q < n) (hq : FieldRigid (J q)) :
    ∀ v, v ≤ n → r v = 0 := by
  obtain ⟨hrq, hrq1⟩ := hq (r q) (r (q + 1)) (hzero q hqn)
  have hright : ∀ k, q + 1 + k ≤ n → r (q + 1 + k) = 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using hrq1
    | succ k ih =>
        intro hle
        have hstep : r (q + 1 + k) = 0 := ih (by omega)
        have hlt : q + 1 + k < n := by omega
        have hz := hzero (q + 1 + k) hlt
        rw [hstep] at hz
        have := eq_zero_of_cross_rows (hJ (q + 1 + k) hlt) (cross_rows_eq_zero_of_fieldMap hz)
        have heq : q + 1 + (k + 1) = q + 1 + k + 1 := by omega
        rw [heq]
        exact this
  have hleft : ∀ k, k ≤ q → r (q - k) = 0 := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using hrq
    | succ k ih =>
        intro hle
        have hstep : r (q - k) = 0 := ih (by omega)
        have hlt : q - (k + 1) < n := by omega
        have hz := hzero (q - (k + 1)) hlt
        have hsucc : q - (k + 1) + 1 = q - k := by omega
        rw [hsucc, hstep] at hz
        exact eq_zero_of_cross_cols (hJ _ hlt) (cross_cols_eq_zero_of_fieldMap hz)
  intro v hv
  by_cases hvq : v ≤ q
  · have := hleft (q - v) (by omega)
    have heq : q - (q - v) = v := by omega
    rwa [heq] at this
  · have hgt : q + 1 ≤ v := by omega
    have := hright (v - (q + 1)) (by omega)
    have heq : q + 1 + (v - (q + 1)) = v := by omega
    rwa [heq] at this

end Propagation

end GaloisForLFunctions.HTGeometry
