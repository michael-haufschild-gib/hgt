import GaloisForLFunctions.HTGeometry.JacobiLeadingMinors
import GaloisForLFunctions.HTGeometry.ArithmeticMinimum

/-!
# The Lovász bound from local minimality

The diagonal entries of a form are read off its Jacobi coordinates as `A_jj = ∑ dₘ Uₘⱼ²`, so the
`j`-th diagonal entry is at least `dⱼ`, and on a size reduced datum it exceeds `dⱼ` by at most a
quarter of the earlier diagonal.

Consequently, whenever the `k`-th diagonal entry of the Jacobi decomposition is minimal against the
next basis vector — for `k = 0` this is exactly the arithmetic minimum — the Lovász bound
`dₖ ≤ (4/3) dₖ₊₁` follows.  This is the second Siegel bound, and unlike Minkowski's it is local:
the constant `4/3` does not grow with the dimension.

* `JacobiData.form_diag` : `A_jj = ∑ dₘ Uₘⱼ²`.
* `JacobiData.d_le_form_diag` : `dⱼ ≤ A_jj`.
* `lovasz_of_le` : **the Lovász bound from local minimality.**
* `JacobiData.lovasz_zero_of_arithmeticMinimum` : **the case `k = 0`, from the arithmetic minimum.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The diagonal entries in Jacobi coordinates.** -/
theorem JacobiData.form_diag (J : JacobiData n) (j : Fin n) :
    J.form j j = ∑ m, J.d m * (J.U m j) ^ (2 : ℕ) := by
  classical
  have hmul : ∀ a b : Fin n, (J.Uᵀ * Matrix.diagonal J.d) a b = J.U b a * J.d b := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.transpose_apply, Matrix.diagonal_apply_eq]
  show (J.Uᵀ * Matrix.diagonal J.d * J.U) j j = _
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hmul]
  ring

/-- The `j`-th diagonal entry dominates the `j`-th diagonal of the Jacobi decomposition. -/
theorem JacobiData.d_le_form_diag (J : JacobiData n) (j : Fin n) : J.d j ≤ J.form j j := by
  classical
  rw [J.form_diag j]
  refine Finset.single_le_sum (f := fun m => J.d m * (J.U m j) ^ (2 : ℕ))
    (fun m _ => mul_nonneg (J.pos m).le (sq_nonneg _)) (Finset.mem_univ j) |>.trans' ?_
  rw [J.unit j, one_pow, mul_one]

/-- On a size reduced datum the `j`-th diagonal entry exceeds `dⱼ` by at most a quarter of the sum
of the earlier diagonal entries. -/
theorem JacobiData.form_diag_le (J : JacobiData n)
    (hred : ∀ i j : Fin n, i < j → |J.U i j| ≤ 1 / 2) (j : Fin n) :
    J.form j j ≤ J.d j + (1 / 4) * ∑ m ∈ Finset.univ.filter (fun m : Fin n => m < j), J.d m := by
  classical
  rw [J.form_diag j]
  have hsplit : (∑ m, J.d m * (J.U m j) ^ (2 : ℕ))
      = J.d j * (J.U j j) ^ (2 : ℕ)
        + ∑ m ∈ Finset.univ.filter (fun m : Fin n => m ≠ j), J.d m * (J.U m j) ^ (2 : ℕ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m : Fin n => m = j)]
    congr 1
    rw [Finset.filter_eq' Finset.univ j]
    simp
  rw [hsplit, J.unit j, one_pow, mul_one]
  refine add_le_add (le_refl (J.d j)) ?_
  have hbound : ∀ m ∈ Finset.univ.filter (fun m : Fin n => m ≠ j),
      J.d m * (J.U m j) ^ (2 : ℕ) ≤ (if m < j then (1 / 4 : ℝ) * J.d m else 0) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rcases lt_trichotomy m j with hmj | hmj | hmj
    · rw [if_pos hmj]
      have hb : (J.U m j) ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) := by
        have := hred m j hmj
        nlinarith [abs_nonneg (J.U m j), sq_abs (J.U m j)]
      calc J.d m * (J.U m j) ^ (2 : ℕ) ≤ J.d m * (1 / 2 : ℝ) ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hb (J.pos m).le
        _ = 1 / 4 * J.d m := by ring
    · exact absurd hmj hm.2
    · rw [if_neg (not_lt.2 (le_of_lt hmj)), J.upper m j hmj]
      simp
  have hfin : (∑ m ∈ Finset.univ.filter (fun m : Fin n => m ≠ j),
      (if m < j then (1 / 4 : ℝ) * J.d m else 0))
      = (1 / 4 : ℝ) * ∑ m ∈ Finset.univ.filter (fun m : Fin n => m < j), J.d m := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun m _ => rfl
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  exact le_trans (Finset.sum_le_sum hbound) (le_of_eq hfin)

/-- **The Lovász bound from local minimality.**  If the `k`-th Jacobi diagonal entry does not exceed
the squared distance of the next basis vector from the earlier ones, then `dₖ ≤ (4/3) dₖ₊₁`. -/
theorem lovasz_of_le {J : JacobiData n} {k l : Fin n}
    (hred : ∀ i j : Fin n, i < j → |J.U i j| ≤ 1 / 2) (hkl : k < l)
    (hmin : J.d k ≤ J.d l + (J.U k l) ^ (2 : ℕ) * J.d k) : J.d k ≤ (4 / 3) * J.d l := by
  have hb : (J.U k l) ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) := by
    have := hred k l hkl
    nlinarith [abs_nonneg (J.U k l), sq_abs (J.U k l)]
  have hdk : (0 : ℝ) < J.d k := J.pos k
  nlinarith [hmin, hb, hdk]

/-- The first diagonal entry of the form is the first Jacobi diagonal entry. -/
theorem JacobiData.form_diag_zero (J : JacobiData n) {i : Fin n} (hi : (i : ℕ) = 0) :
    J.form i i = J.d i := by
  classical
  rw [J.form_diag i]
  refine (Finset.sum_eq_single i (fun m _ hm => ?_)
    (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
  · rcases lt_trichotomy m i with hmi | hmi | hmi
    · exact absurd (Fin.lt_def.1 hmi) (by omega)
    · exact absurd hmi hm
    · rw [J.upper m i hmi]
      ring
  · rw [J.unit i, one_pow, mul_one]

/-- **The diagonal entry at the successor index**, when the earlier coordinates vanish. -/
theorem JacobiData.form_diag_succ (J : JacobiData n) {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1)
    (hpre : ∀ m : Fin n, m < i → J.U m j = 0) :
    J.form j j = J.d i * (J.U i j) ^ (2 : ℕ) + J.d j := by
  classical
  rw [J.form_diag j]
  have hji : i < j := Fin.lt_def.2 (by omega)
  have hsplit : (∑ m, J.d m * (J.U m j) ^ (2 : ℕ))
      = J.d i * (J.U i j) ^ (2 : ℕ)
        + ∑ m ∈ Finset.univ.filter (fun m : Fin n => m ≠ i), J.d m * (J.U m j) ^ (2 : ℕ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m : Fin n => m = i)]
    congr 1
    rw [Finset.filter_eq' Finset.univ i]
    simp
  rw [hsplit]
  congr 1
  refine (Finset.sum_eq_single j (fun m hm hmj => ?_) (fun hcon => ?_)).trans ?_
  · rw [Finset.mem_filter] at hm
    rcases lt_trichotomy m i with h1 | h1 | h1
    · rw [hpre m h1]
      ring
    · exact absurd h1 hm.2
    · have hmj' : j < m := by
        refine Fin.lt_def.2 ?_
        have := Fin.lt_def.1 h1
        have : (m : ℕ) ≠ (j : ℕ) := fun hc => hmj (Fin.ext hc)
        omega
      rw [J.upper m j hmj']
      ring
  · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, fun hc => by
      rw [hc] at hij; omega⟩) hcon
  · rw [J.unit j, one_pow, mul_one]

/-- **The Lovász bound at consecutive indices**, from minimality of `dᵢ` against the value of the
form at the next basis vector. -/
theorem JacobiData.lovasz_succ (J : JacobiData n) {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1)
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2)
    (hpre : ∀ m : Fin n, m < i → J.U m j = 0)
    (hmin : J.d i ≤ J.form j j) : J.d i ≤ (4 / 3) * J.d j := by
  refine lovasz_of_le hred (Fin.lt_def.2 (by omega)) ?_
  rw [J.form_diag_succ hij hpre] at hmin
  linarith [hmin]

/-- **The Lovász bound at the bottom of the flag**, where minimality is the arithmetic minimum: no
hypothesis on the earlier coordinates is needed, because there are none. -/
theorem JacobiData.lovasz_first (J : JacobiData n) {i j : Fin n} (hi : (i : ℕ) = 0)
    (hij : (j : ℕ) = 1)
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2)
    (hmin : J.form i i ≤ J.form j j) : J.d i ≤ (4 / 3) * J.d j := by
  refine J.lovasz_succ (by omega) hred (fun m hm => ?_) ?_
  · exact absurd (Fin.lt_def.1 hm) (by omega)
  · rw [← J.form_diag_zero hi]
    exact hmin

/-- The value of the form at a standard basis vector is the corresponding diagonal entry. -/
theorem quadForm_single (A : posDefCone n) (j : Fin n) :
    quadForm A (intVec (Pi.single j 1))
      = ((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ) j j := by
  classical
  have hx : intVec (Pi.single j (1 : ℤ)) = Pi.single j (1 : ℝ) := by
    funext i
    by_cases hij : i = j <;> simp [intVec, hij]
  unfold quadForm
  rw [hx]
  simp only [dotProduct, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- **The Lovász bound at the bottom of the flag, from the arithmetic minimum.**  If the first
standard basis vector realises the arithmetic minimum of the form, then the first two Jacobi
diagonal entries satisfy `d₀ ≤ (4/3) d₁`. -/
theorem lovasz_first_of_arithmeticMinimum {A : posDefCone n} {J : JacobiData n}
    (hform : J.form = ((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ))
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2)
    {i j : Fin n} (hi : (i : ℕ) = 0) (hj : (j : ℕ) = 1)
    (hmin : ∀ v : Fin n → ℤ, v ≠ 0 →
      quadForm A (intVec (Pi.single i 1)) ≤ quadForm A (intVec v)) :
    J.d i ≤ (4 / 3) * J.d j := by
  classical
  refine J.lovasz_first hi hj hred ?_
  have hjne : (Pi.single j (1 : ℤ) : Fin n → ℤ) ≠ 0 := by
    intro hcon
    have := congrFun hcon j
    simp at this
  have := hmin (Pi.single j (1 : ℤ)) hjne
  rw [quadForm_single, quadForm_single] at this
  rw [hform]
  exact this

end GaloisForLFunctions.HTGeometry
