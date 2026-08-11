import Mathlib

/-!
# Weighted port capacity and the exact capacity–cost reciprocity

For positive weights `w` and coefficients `a` on an index set, the **port capacity** of a finite
aperture `F` is

`C_F = ∑_{p ∈ F} ‖a p‖² / w p`,

and the **filling energy** of a source vector is `E_F(x) = ∑_{p ∈ F} w p ‖x p‖²`.  The port value
is `λ(x) = ∑_{p ∈ F} coef p · x p`, where `coef` has the same modulus as `a`.  Weighted
Cauchy–Schwarz gives

`‖λ(x)‖² ≤ E_F(x) · C_F`,

and the explicit vector `x_p = z · conj (coef p) / (w p · C_F)` attains equality with
`λ(x) = z`, so the minimum filling energy of the value `z` is exactly `‖z‖² / C_F`:

`C_F · E_F^min(z) = ‖z‖²`.
-/

open scoped ComplexConjugate

namespace HTGeometry.ConstraintMotiveRelativity

section WeightedCapacity

variable {P : Type*} [DecidableEq P]

/-- The port capacity of a finite aperture. -/
noncomputable def portCap (w : P → ℝ) (a : P → ℂ) (F : Finset P) : ℝ :=
  ∑ p ∈ F, ‖a p‖ ^ 2 / w p

/-- The weighted filling energy of a source vector on a finite aperture. -/
noncomputable def portEnergy (w : P → ℝ) (x : P → ℂ) (F : Finset P) : ℝ :=
  ∑ p ∈ F, w p * ‖x p‖ ^ 2

/-- The observed port value on a finite aperture. -/
noncomputable def portValue (coef : P → ℂ) (x : P → ℂ) (F : Finset P) : ℂ :=
  ∑ p ∈ F, coef p * x p

variable {w : P → ℝ} {a coef : P → ℂ}

omit [DecidableEq P] in
theorem portCap_nonneg (hw : ∀ p, 0 < w p) (F : Finset P) : 0 ≤ portCap w a F :=
  Finset.sum_nonneg fun p _ => by
    have := (hw p).le
    positivity

omit [DecidableEq P] in
theorem portEnergy_nonneg (hw : ∀ p, 0 < w p) (x : P → ℂ) (F : Finset P) :
    0 ≤ portEnergy w x F :=
  Finset.sum_nonneg fun p _ => by
    have := (hw p).le
    positivity

omit [DecidableEq P] in
theorem portCap_pos (hw : ∀ p, 0 < w p) {F : Finset P} (hF : F.Nonempty) (ha : ∀ p, a p ≠ 0) :
    0 < portCap w a F := by
  obtain ⟨q, hq⟩ := hF
  refine Finset.sum_pos' (fun p _ => by have := (hw p).le; positivity) ⟨q, hq, ?_⟩
  have h1 : 0 < ‖a q‖ ^ 2 := by
    have : ‖a q‖ ≠ 0 := norm_ne_zero_iff.2 (ha q)
    positivity
  exact div_pos h1 (hw q)

omit [DecidableEq P] in
/-- **Weighted Cauchy–Schwarz for a port.** -/
theorem portValue_normSq_le (hw : ∀ p, 0 < w p) (hcoef : ∀ p, ‖coef p‖ = ‖a p‖)
    (x : P → ℂ) (F : Finset P) :
    ‖portValue coef x F‖ ^ 2 ≤ portEnergy w x F * portCap w a F := by
  have hstep : ‖portValue coef x F‖ ≤ ∑ p ∈ F, ‖coef p‖ * ‖x p‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun p _ => le_of_eq (norm_mul _ _)
  have hsplit : ∀ p ∈ F, ‖coef p‖ * ‖x p‖
      = (Real.sqrt (w p) * ‖x p‖) * (‖a p‖ / Real.sqrt (w p)) := by
    intro p _
    have hs : Real.sqrt (w p) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw p))
    rw [hcoef p]
    field_simp
    try ring
  have hcs : (∑ p ∈ F, (Real.sqrt (w p) * ‖x p‖) * (‖a p‖ / Real.sqrt (w p))) ^ 2
      ≤ (∑ p ∈ F, (Real.sqrt (w p) * ‖x p‖) ^ 2)
        * (∑ p ∈ F, (‖a p‖ / Real.sqrt (w p)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq F _ _
  have he : ∑ p ∈ F, (Real.sqrt (w p) * ‖x p‖) ^ 2 = portEnergy w x F := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw p).le]
  have hc : ∑ p ∈ F, (‖a p‖ / Real.sqrt (w p)) ^ 2 = portCap w a F := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_pow, Real.sq_sqrt (hw p).le]
  rw [he, hc] at hcs
  have hsum : ∑ p ∈ F, ‖coef p‖ * ‖x p‖
      = ∑ p ∈ F, (Real.sqrt (w p) * ‖x p‖) * (‖a p‖ / Real.sqrt (w p)) :=
    Finset.sum_congr rfl hsplit
  have hnn : 0 ≤ ∑ p ∈ F, ‖coef p‖ * ‖x p‖ :=
    Finset.sum_nonneg fun p _ => by positivity
  have hstep2 : ‖portValue coef x F‖ ^ 2 ≤ (∑ p ∈ F, ‖coef p‖ * ‖x p‖) ^ 2 := by
    have := norm_nonneg (portValue coef x F)
    nlinarith
  rw [hsum] at hstep2
  linarith

/-- The minimizing source vector of the exact capacity–cost law. -/
noncomputable def portMinimizer (w : P → ℝ) (coef : P → ℂ) (F : Finset P) (z : ℂ) : P → ℂ :=
  fun p => if p ∈ F then z * conj (coef p) / ((w p : ℂ) * (portCap w coef F : ℂ)) else 0

omit [DecidableEq P] in
theorem portCap_congr (hcoef : ∀ p, ‖coef p‖ = ‖a p‖) (F : Finset P) :
    portCap w coef F = portCap w a F := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hcoef p]

theorem portValue_portMinimizer (hw : ∀ p, 0 < w p) {F : Finset P}
    (hC : portCap w coef F ≠ 0) (z : ℂ) :
    portValue coef (portMinimizer w coef F z) F = z := by
  have hCc : ((portCap w coef F : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hC
  have hval : ∀ p ∈ F, coef p * portMinimizer w coef F z p
      = (z / (portCap w coef F : ℂ)) * (((‖coef p‖ ^ 2 / w p : ℝ)) : ℂ) := by
    intro p hp
    have hwp : (w p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hw p)
    have hmul : coef p * conj (coef p) = ((‖coef p‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.conj_mul']
      push_cast
      ring
    rw [portMinimizer, if_pos hp]
    field_simp
    rw [show coef p * z * conj (coef p) = z * (coef p * conj (coef p)) by ring, hmul]
    push_cast
    field_simp
  rw [portValue, Finset.sum_congr rfl hval, ← Finset.mul_sum]
  have hsum : ∑ p ∈ F, (((‖coef p‖ ^ 2 / w p : ℝ)) : ℂ) = ((portCap w coef F : ℝ) : ℂ) := by
    rw [portCap]
    push_cast
    rfl
  rw [hsum]
  field_simp

theorem portEnergy_portMinimizer (hw : ∀ p, 0 < w p) {F : Finset P}
    (hC : portCap w coef F ≠ 0) (z : ℂ) :
    portEnergy w (portMinimizer w coef F z) F = ‖z‖ ^ 2 / portCap w coef F := by
  have hCpos : 0 < portCap w coef F :=
    lt_of_le_of_ne (portCap_nonneg (w := w) (a := coef) hw F) (Ne.symm hC)
  have hterm : ∀ p ∈ F, w p * ‖portMinimizer w coef F z p‖ ^ 2
      = (‖z‖ ^ 2 / (portCap w coef F) ^ 2) * (‖coef p‖ ^ 2 / w p) := by
    intro p hp
    have hwp : (0:ℝ) < w p := hw p
    rw [portMinimizer, if_pos hp, norm_div, norm_mul, norm_mul]
    simp only [RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hwp, abs_of_pos hCpos]
    field_simp
    try ring
  rw [portEnergy, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← portCap]
  field_simp
  try ring

/-- **Exact capacity-cost reciprocity.**  The minimum filling energy of the port value `z` on a
finite aperture is `‖z‖² / C_F`. -/
theorem isLeast_portEnergy (hw : ∀ p, 0 < w p) {F : Finset P}
    (hC : portCap w coef F ≠ 0) (z : ℂ) :
    IsLeast {e : ℝ | ∃ x : P → ℂ, portValue coef x F = z ∧ portEnergy w x F = e}
      (‖z‖ ^ 2 / portCap w coef F) := by
  constructor
  · exact ⟨portMinimizer w coef F z, portValue_portMinimizer hw hC z,
      portEnergy_portMinimizer hw hC z⟩
  · rintro e ⟨x, hx, rfl⟩
    have hcs := portValue_normSq_le (w := w) (a := coef) (coef := coef) hw (fun p => rfl) x F
    rw [hx] at hcs
    have hCpos : 0 < portCap w coef F :=
      lt_of_le_of_ne (portCap_nonneg (w := w) (a := coef) hw F) (Ne.symm hC)
    rw [div_le_iff₀ hCpos]
    linarith

omit [DecidableEq P] in
/-- **The capacity-cost product law.** -/
theorem portCap_mul_minEnergy {F : Finset P} (hC : portCap w coef F ≠ 0) (z : ℂ) :
    portCap w coef F * (‖z‖ ^ 2 / portCap w coef F) = ‖z‖ ^ 2 := by
  field_simp

end WeightedCapacity

end HTGeometry.ConstraintMotiveRelativity
