import GaloisForLFunctions.ArithmeticScatteringHolography.TheTrivialZerosOfACusp
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The black hole of genus two

An explicit graph for every `q ≥ 2`, with one cusp and the functional equation of genus two. It is the sharp case of the law of trivial zeros: one trivial zero, and `∑ n_u b_u = q + 1` at the vertex of the cusp.

The cusp is attached to a vertex `v₀` of index one with two branches. Each branch is a chain of five vertices, listed from `v₀`, as (edges down to it, edges back up):

- first branch: `(1, 2)`, `(q - 1, 2)`, `(q - 1, 1)`, `(q, 1)`, `(q, q + 1)`;
- second branch: `(q - 1, 1)`, `(q, 1)`, `(q, 2)`, `(q - 1, 2)`, `(q - 1, q + 1)`.

The two branches are different chains with the same denominator `λ (λ⁴ - e₁ λ² + e₂)`, `e₁ = q² + 5q - 3`, `e₂ = q (q - 1)(3q + 5)`. So the five differences of the branches are compact modes, and the rest is

  `R = x² (x² - q²) L_q(x²) · (compact)` (`genusTwo_modePoly`),

  `L_q(z) = z⁴ - (q - 2) z³ - (q - 1) z² - q (q - 2) z + q²`.

`L_q` has the functional equation for every `q` (`genusTwoL_functional_equation`), and the factorization has exactly the form of the law (`genusTwo_factorization`, `genusTwo_sharp`).

**The critical circle.** `L_q = (z² - t₁ z + q)(z² - t₂ z + q)`, with `t₁ + t₂ = q - 2`, `t₁ t₂ = 1 - 3q`. All the modes are on `|z|² = q` if and only if `q ≤ 3` (`genusTwo_critical_iff`). So the functional equation at genus two does not force universal damping: for `q ≥ 4` there is a slow resonance (`universal_damping_not_forced_at_genus_two`).

Flux, unitarity and the functional equation hold on every member of the family, and for `q ≤ 3` damping does not exclude it either.
-/

open Polynomial Matrix Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-! ### Tridiagonal determinants -/

section Tridiagonal

variable {R : Type*} [CommRing R]

/-- The tridiagonal matrix of a chain, at offset `s`. -/
def triMatrix (d u l : ℕ → R) (s n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then d (s + i) else if (i : ℕ) + 1 = j then u (s + i)
    else if (j : ℕ) + 1 = i then l (s + j) else 0

theorem det_triMatrix_zero (d u l : ℕ → R) (s : ℕ) : (triMatrix d u l s 0).det = 1 :=
  Matrix.det_isEmpty

theorem det_triMatrix_one (d u l : ℕ → R) (s : ℕ) : (triMatrix d u l s 1).det = d s := by
  rw [Matrix.det_fin_one]
  simp [triMatrix]

/-- **The three-term recursion.** -/
theorem det_triMatrix_add_two (d u l : ℕ → R) (s n : ℕ) :
    (triMatrix d u l s (n + 2)).det =
      d s * (triMatrix d u l (s + 1) (n + 1)).det -
        u s * l s * (triMatrix d u l (s + 2) n).det := by
  set A := triMatrix d u l s (n + 2) with hA
  have h00 : A 0 0 = d s := by simp [hA, triMatrix]
  have h01 : A 0 (Fin.succ 0) = u s := by simp [hA, triMatrix]
  have h10 : A 1 0 = l s := by simp [hA, triMatrix]
  have h0 (j : Fin n) : A 0 j.succ.succ = 0 := by simp [hA, triMatrix, Fin.val_succ]
  have hc0 (i : Fin n) : A i.succ.succ 0 = 0 := by simp [hA, triMatrix, Fin.val_succ]
  have hm1 : A.submatrix Fin.succ (Fin.succAbove 0) = triMatrix d u l (s + 1) (n + 1) := by
    refine Matrix.ext fun i j => ?_
    have ei : s + ((i : ℕ) + 1) = s + 1 + i := by omega
    have ej : s + ((j : ℕ) + 1) = s + 1 + j := by omega
    simp only [hA, triMatrix, Matrix.submatrix_apply, Matrix.of_apply, Fin.zero_succAbove, Fin.val_succ,
      ei, ej, Nat.add_right_cancel_iff]
  have hm2 : (A.submatrix Fin.succ (Fin.succAbove (Fin.succ 0))).submatrix (Fin.succAbove 0) Fin.succ =
      triMatrix d u l (s + 2) n := by
    refine Matrix.ext fun i j => ?_
    have ei : s + ((i : ℕ) + 1 + 1) = s + 2 + i := by omega
    have ej : s + ((j : ℕ) + 1 + 1) = s + 2 + j := by omega
    simp only [hA, triMatrix, Matrix.submatrix_apply, Matrix.of_apply, Fin.zero_succAbove,
      Fin.succ_succAbove_succ, Fin.val_succ, ei, ej, Nat.add_right_cancel_iff]
  have hminor : (A.submatrix Fin.succ (Fin.succAbove (Fin.succ 0))).det =
      l s * (triMatrix d u l (s + 2) n).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero, hm2]
    · simp [h10]
    · intro i _
      simp [hc0]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero,
    hm1, hminor, h00, h01]
  · simp
    ring
  · intro j _
    rw [h0]
    ring

/-- The recursion with its indices as separate parameters, so that numerals need no unfolding. -/
theorem det_tri_step (d u l : ℕ → R) {s s₁ s₂ n₂ n₁ n₀ : ℕ} (h₁ : s₁ = s + 1) (h₂ : s₂ = s + 2)
    (hn₁ : n₁ = n₀ + 1) (hn₂ : n₂ = n₀ + 2) :
    (triMatrix d u l s n₂).det =
      d s * (triMatrix d u l s₁ n₁).det - u s * l s * (triMatrix d u l s₂ n₀).det := by
  subst h₁ h₂ hn₁ hn₂
  exact det_triMatrix_add_two d u l s n₀

end Tridiagonal

/-- The integer indices of a chain. -/
def chainIndex (up lo : ℕ → ℤ) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if (i : ℕ) + 1 = j then up i else if (j : ℕ) + 1 = i then lo j else 0

/-- The mode matrix of a chain with rays at its vertices is tridiagonal. -/
theorem modeMatrix_chainIndex (q : ℕ) (up lo c : ℕ → ℤ) (n : ℕ) :
    modeMatrix q (chainIndex up lo n) (fun i => c i) =
      triMatrix (fun i => X ^ 2 + C ((q : ℤ) * (1 - c i))) (fun i => -(C (up i) * X))
        (fun i => -(C (lo i) * X)) 0 n := by
  refine Matrix.ext fun i j => ?_
  simp only [modeMatrix, chainIndex, triMatrix, Matrix.of_apply, zero_add, Fin.ext_iff]
  by_cases h : (i : ℕ) = j
  · have h1 : ¬ ((i : ℕ) + 1 = j) := by omega
    have h2 : ¬ ((j : ℕ) + 1 = i) := by omega
    simp [h]
  · by_cases h1 : (i : ℕ) + 1 = j
    · simp [h, h1]
    · by_cases h2 : (j : ℕ) + 1 = i
      · simp [h, h1, h2]
      · simp [h, h1, h2]

/-! ### The graph -/

/-- Edge indices from a vertex to the next one along the chain. -/
def genusTwoUp (q : ℕ) : ℕ → ℤ
  | 0 => q + 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2
  | 5 => q - 1 | 6 => q | 7 => q | 8 => q - 1 | 9 => q - 1 | _ => 0

/-- Edge indices from a vertex to the previous one along the chain. -/
def genusTwoLo (q : ℕ) : ℕ → ℤ
  | 0 => q | 1 => q | 2 => q - 1 | 3 => q - 1 | 4 => 1
  | 5 => 1 | 6 => 1 | 7 => 2 | 8 => 2 | 9 => q + 1 | _ => 0

/-- The ray is at vertex five, with index one. -/
def genusTwoRay (i : ℕ) : ℤ := if i = 5 then 1 else 0

/-- **The graph of genus two.** -/
def genusTwoIndex (q : ℕ) : Matrix (Fin 11) (Fin 11) ℤ := chainIndex (genusTwoUp q) (genusTwoLo q) 11

/-- **Every vertex has `q + 1` edges.** -/
theorem genusTwo_row (q : ℕ) (v : Fin 11) :
    ∑ u, genusTwoIndex q v u + genusTwoRay v = (q : ℤ) + 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, genusTwoIndex, chainIndex, Matrix.of_apply]
  fin_cases v <;> simp [genusTwoUp, genusTwoLo, genusTwoRay] <;> ring

/-- The two indices of an edge vanish together, for `q ≥ 2`: the indices define a graph. -/
theorem genusTwo_edge {q : ℕ} (hq : 2 ≤ q) (v u : Fin 11) :
    genusTwoIndex q v u = 0 ↔ genusTwoIndex q u v = 0 := by
  have h1 : (q : ℤ) - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq
    omega
  have h2 : q ≠ 0 := by omega
  have h3 : (q : ℤ) + 1 ≠ 0 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq
    omega
  fin_cases v <;> fin_cases u <;>
    simp [genusTwoIndex, chainIndex, genusTwoUp, genusTwoLo, h1, h2, h3]

/-- The first branch law holds with equality at the vertex of the cusp. -/
theorem genusTwo_branch (q : ℕ) :
    ∑ u, genusTwoIndex q 5 u * genusTwoIndex q u 5 = (q : ℤ) + 1 := by
  simp [Fin.sum_univ_succ, genusTwoIndex, chainIndex, genusTwoUp, genusTwoLo, Fin.val_succ]
  ring

/-- `L_q(x²)` over the integers. -/
def genusTwoLInt (q : ℕ) : ℤ[X] :=
  X ^ 8 - (C (q : ℤ) - 2) * X ^ 6 - (C (q : ℤ) - 1) * X ^ 4 -
    C (q : ℤ) * (C (q : ℤ) - 2) * X ^ 2 + C (q : ℤ) ^ 2

/-- The five compact modes. -/
def genusTwoCompactInt (q : ℕ) : ℤ[X] :=
  (X ^ 2 + C (q : ℤ)) * ((X ^ 2 + C (q : ℤ)) ^ 4 -
    (C (q : ℤ) ^ 2 + 5 * C (q : ℤ) - 3) * X ^ 2 * (X ^ 2 + C (q : ℤ)) ^ 2 +
    C (q : ℤ) * (C (q : ℤ) - 1) * (3 * C (q : ℤ) + 5) * X ^ 4)

/-- **The mode polynomial of the black hole of genus two.** -/
theorem genusTwo_modePoly (q : ℕ) :
    modePoly q (genusTwoIndex q) (fun i => genusTwoRay i) =
      X ^ 2 * ((X ^ 2 - C (q : ℤ) ^ 2) * (genusTwoLInt q * genusTwoCompactInt q)) := by
  rw [modePoly, genusTwoIndex, modeMatrix_chainIndex]
  set d : ℕ → ℤ[X] := fun i => X ^ 2 + C ((q : ℤ) * (1 - genusTwoRay i)) with hd
  set u : ℕ → ℤ[X] := fun i => -(C (genusTwoUp q i) * X) with hu
  set l : ℕ → ℤ[X] := fun i => -(C (genusTwoLo q i) * X) with hl
  have t11 : (triMatrix d u l 11 0).det = 1 := det_triMatrix_zero d u l 11
  have t10 : (triMatrix d u l 10 1).det = d 10 := det_triMatrix_one d u l 10
  have t9 : (triMatrix d u l 9 2).det = d 9 * (triMatrix d u l 10 1).det -
      u 9 * l 9 * (triMatrix d u l 11 0).det := det_tri_step d u l rfl rfl rfl rfl
  have t8 : (triMatrix d u l 8 3).det = d 8 * (triMatrix d u l 9 2).det -
      u 8 * l 8 * (triMatrix d u l 10 1).det := det_tri_step d u l rfl rfl rfl rfl
  have t7 : (triMatrix d u l 7 4).det = d 7 * (triMatrix d u l 8 3).det -
      u 7 * l 7 * (triMatrix d u l 9 2).det := det_tri_step d u l rfl rfl rfl rfl
  have t6 : (triMatrix d u l 6 5).det = d 6 * (triMatrix d u l 7 4).det -
      u 6 * l 6 * (triMatrix d u l 8 3).det := det_tri_step d u l rfl rfl rfl rfl
  have t5 : (triMatrix d u l 5 6).det = d 5 * (triMatrix d u l 6 5).det -
      u 5 * l 5 * (triMatrix d u l 7 4).det := det_tri_step d u l rfl rfl rfl rfl
  have t4 : (triMatrix d u l 4 7).det = d 4 * (triMatrix d u l 5 6).det -
      u 4 * l 4 * (triMatrix d u l 6 5).det := det_tri_step d u l rfl rfl rfl rfl
  have t3 : (triMatrix d u l 3 8).det = d 3 * (triMatrix d u l 4 7).det -
      u 3 * l 3 * (triMatrix d u l 5 6).det := det_tri_step d u l rfl rfl rfl rfl
  have t2 : (triMatrix d u l 2 9).det = d 2 * (triMatrix d u l 3 8).det -
      u 2 * l 2 * (triMatrix d u l 4 7).det := det_tri_step d u l rfl rfl rfl rfl
  have t1 : (triMatrix d u l 1 10).det = d 1 * (triMatrix d u l 2 9).det -
      u 1 * l 1 * (triMatrix d u l 3 8).det := det_tri_step d u l rfl rfl rfl rfl
  have t0 : (triMatrix d u l 0 11).det = d 0 * (triMatrix d u l 1 10).det -
      u 0 * l 0 * (triMatrix d u l 2 9).det := det_tri_step d u l rfl rfl rfl rfl
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ[X], Q = C (q : ℤ) := ⟨_, rfl⟩
  have dS {i : ℕ} (hi : genusTwoRay i = 0) : d i = X ^ 2 + Q := by
    simp [hd, hi, hQ]
  have d5 : d 5 = X ^ 2 := by simp [hd, genusTwoRay]
  have ul {i : ℕ} {a b : ℤ[X]} (ha : C (genusTwoUp q i) = a) (hb : C (genusTwoLo q i) = b) :
      u i * l i = a * b * X ^ 2 := by
    simp only [hu, hl, ha, hb]
    ring
  have u0 := ul (i := 0) (a := Q + 1) (b := Q) (by simp [genusTwoUp, hQ]) (by simp [genusTwoLo, hQ])
  have u1 := ul (i := 1) (a := 1) (b := Q) (by simp [genusTwoUp]) (by simp [genusTwoLo, hQ])
  have u2 := ul (i := 2) (a := 1) (b := Q - 1) (by simp [genusTwoUp]) (by simp [genusTwoLo, hQ])
  have u3 := ul (i := 3) (a := 2) (b := Q - 1) (by simp [genusTwoUp]) (by simp [genusTwoLo, hQ])
  have u4 := ul (i := 4) (a := 2) (b := 1) (by simp [genusTwoUp]) (by simp [genusTwoLo])
  have u5 := ul (i := 5) (a := Q - 1) (b := 1) (by simp [genusTwoUp, hQ]) (by simp [genusTwoLo])
  have u6 := ul (i := 6) (a := Q) (b := 1) (by simp [genusTwoUp, hQ]) (by simp [genusTwoLo])
  have u7 := ul (i := 7) (a := Q) (b := 2) (by simp [genusTwoUp, hQ]) (by simp [genusTwoLo])
  have u8 := ul (i := 8) (a := Q - 1) (b := 2) (by simp [genusTwoUp, hQ]) (by simp [genusTwoLo])
  have u9 := ul (i := 9) (a := Q - 1) (b := Q + 1) (by simp [genusTwoUp, hQ]) (by simp [genusTwoLo, hQ])
  rw [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, d5,
    dS (i := 0) (by simp [genusTwoRay]), dS (i := 1) (by simp [genusTwoRay]),
    dS (i := 2) (by simp [genusTwoRay]), dS (i := 3) (by simp [genusTwoRay]),
    dS (i := 4) (by simp [genusTwoRay]), dS (i := 6) (by simp [genusTwoRay]),
    dS (i := 7) (by simp [genusTwoRay]), dS (i := 8) (by simp [genusTwoRay]),
    dS (i := 9) (by simp [genusTwoRay]), dS (i := 10) (by simp [genusTwoRay])]
  simp only [genusTwoLInt, genusTwoCompactInt, ← hQ]
  ring

/-! ### The functional equation -/

/-- A monic quartic. -/
def quartic (a b c d : ℂ) : ℂ[X] := X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d

theorem quartic_monic_natDegree (a b c d : ℂ) :
    (quartic a b c d).Monic ∧ (quartic a b c d).natDegree = 4 := by
  have hform : quartic a b c d = X ^ 4 + (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) := by
    simp only [quartic]
    ring
  have hlow : (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℂ[X]).degree < 4 :=
    lt_of_le_of_lt degree_cubic_le (by decide)
  rw [hform]
  refine ⟨monic_X_pow_add hlow, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt (by simpa using hlow), natDegree_X_pow]

theorem quartic_reverse (a b c d : ℂ) :
    (quartic a b c d).reverse = 1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 := by
  have hp : quartic a b c d = C 1 * X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X ^ 1 + C d * X ^ 0 := by
    simp [quartic]
  have r (i : ℕ) (h : i ≤ 4) : revAt 4 i = 4 - i := revAt_le h
  rw [reverse, (quartic_monic_natDegree a b c d).2, hp]
  simp only [reflect_add, reflect_C_mul_X_pow]
  rw [r 4 le_rfl, r 3 (by norm_num), r 2 (by norm_num), r 1 (by norm_num), r 0 (by norm_num)]
  simp

/-- **The numerator `L_q` of the black hole of genus two**, in the variable `z = x²`. -/
def genusTwoL (q : ℕ) : ℂ[X] :=
  quartic (-((q : ℂ) - 2)) (-((q : ℂ) - 1)) (-((q : ℂ) * ((q : ℂ) - 2))) ((q : ℂ) ^ 2)

theorem genusTwoL_monic (q : ℕ) : (genusTwoL q).Monic := (quartic_monic_natDegree _ _ _ _).1

theorem genusTwoL_natDegree (q : ℕ) : (genusTwoL q).natDegree = 2 * 2 :=
  (quartic_monic_natDegree _ _ _ _).2

theorem genusTwoL_eval (q : ℕ) (z : ℂ) :
    (genusTwoL q).eval z = z ^ 4 - ((q : ℂ) - 2) * z ^ 3 - ((q : ℂ) - 1) * z ^ 2 -
      (q : ℂ) * ((q : ℂ) - 2) * z + (q : ℂ) ^ 2 := by
  simp only [genusTwoL, quartic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- **`L_q` has the functional equation of genus two, for every `q`.** -/
theorem genusTwoL_functional_equation {q : ℕ} (hq : q ≠ 0) (w : ℂ) (hw : w ≠ 0) :
    (genusTwoL q).reverse.eval w =
      ((q : ℂ) * w ^ 2) ^ 2 * (genusTwoL q).reverse.eval (1 / ((q : ℂ) * w)) := by
  have hQ : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  simp only [genusTwoL, quartic_reverse, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one]
  field_simp
  ring

/-- The factors of `L_q`. -/
theorem genusTwoL_factor {q : ℕ} {t₁ t₂ : ℂ} (h₁ : t₁ + t₂ = (q : ℂ) - 2)
    (h₂ : t₁ * t₂ = 1 - 3 * (q : ℂ)) (z : ℂ) :
    (genusTwoL q).eval z = (z ^ 2 - t₁ * z + q) * (z ^ 2 - t₂ * z + q) := by
  rw [genusTwoL_eval]
  linear_combination (z ^ 3 + (q : ℂ) * z) * h₁ - z ^ 2 * h₂

theorem exists_two_squares (e₁ e₂ : ℂ) : ∃ s₁ s₂ : ℂ, s₁ ^ 2 + s₂ ^ 2 = e₁ ∧ s₁ ^ 2 * s₂ ^ 2 = e₂ := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ ^ 2 - 4 * e₂) two_pos
  obtain ⟨s₁, h₁⟩ := IsAlgClosed.exists_pow_nat_eq ((e₁ + r) / 2) two_pos
  obtain ⟨s₂, h₂⟩ := IsAlgClosed.exists_pow_nat_eq ((e₁ - r) / 2) two_pos
  refine ⟨s₁, s₂, ?_, ?_⟩
  · rw [h₁, h₂]
    ring
  · rw [h₁, h₂]
    linear_combination (-1 / 4 : ℂ) * hr

/-- **The factorization has the form of the law:** one trivial zero, the ground mode, `L_q`, five compact modes. -/
theorem genusTwo_factorization (q : ℕ) :
    ∃ ls : Multiset ℂ, (modePoly q (genusTwoIndex q) (fun i => genusTwoRay i)).map (Int.castRingHom ℂ) =
      X ^ (2 * 1) * ((X ^ 2 - C ((q : ℂ) ^ 2)) * ((genusTwoL q).comp (X ^ 2) * compactProd q ls)) := by
  obtain ⟨s₁, s₂, hs, hp⟩ := exists_two_squares ((q : ℂ) ^ 2 + 5 * q - 3)
    ((q : ℂ) * ((q : ℂ) - 1) * (3 * q + 5))
  refine ⟨0 ::ₘ s₁ ::ₘ (-s₁) ::ₘ s₂ ::ₘ {-s₂}, ?_⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ[X], Q = C (q : ℂ) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ[X], a = C s₁ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ[X], b = C s₂ := ⟨_, rfl⟩
  have c2 : (C (2 : ℂ) : ℂ[X]) = 2 := map_ofNat C 2
  have c3 : (C (3 : ℂ) : ℂ[X]) = 3 := map_ofNat C 3
  have c5 : (C (5 : ℂ) : ℂ[X]) = 5 := map_ofNat C 5
  have hsum : a ^ 2 + b ^ 2 = Q ^ 2 + 5 * Q - 3 := by
    have h := congrArg (C : ℂ → ℂ[X]) hs
    simpa only [C_add, C_sub, C_mul, C_pow, c3, c5, ← ha, ← hb, ← hQ] using h
  have hprod : a ^ 2 * b ^ 2 = Q * (Q - 1) * (3 * Q + 5) := by
    have h := congrArg (C : ℂ → ℂ[X]) hp
    simpa only [C_add, C_sub, C_mul, C_pow, C_1, c3, c5, ← ha, ← hb, ← hQ] using h
  have hmap : (modePoly q (genusTwoIndex q) (fun i => genusTwoRay i)).map (Int.castRingHom ℂ) =
      X ^ 2 * ((X ^ 2 - Q ^ 2) * ((X ^ 8 - (Q - 2) * X ^ 6 - (Q - 1) * X ^ 4 - Q * (Q - 2) * X ^ 2 + Q ^ 2) *
        ((X ^ 2 + Q) * ((X ^ 2 + Q) ^ 4 - (Q ^ 2 + 5 * Q - 3) * X ^ 2 * (X ^ 2 + Q) ^ 2 +
          Q * (Q - 1) * (3 * Q + 5) * X ^ 4)))) := by
    have hc : (C ((Int.castRingHom ℂ) (q : ℤ)) : ℂ[X]) = Q := by
      rw [hQ]
      simp
    rw [genusTwo_modePoly, genusTwoLInt, genusTwoCompactInt]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
      map_C, Polynomial.map_ofNat, Polynomial.map_one, hc]
  have hL : (genusTwoL q).comp (X ^ 2) =
      X ^ 8 - (Q - 2) * X ^ 6 - (Q - 1) * X ^ 4 - Q * (Q - 2) * X ^ 2 + Q ^ 2 := by
    simp only [genusTwoL, quartic, add_comp, mul_comp, pow_comp, X_comp, C_comp, C_neg, C_sub, C_mul,
      C_pow, c2, C_1, ← hQ]
    ring
  have hK : compactProd q (0 ::ₘ s₁ ::ₘ (-s₁) ::ₘ s₂ ::ₘ {-s₂}) =
      (X ^ 2 + Q) * ((X ^ 2 + Q) ^ 4 - (Q ^ 2 + 5 * Q - 3) * X ^ 2 * (X ^ 2 + Q) ^ 2 +
        Q * (Q - 1) * (3 * Q + 5) * X ^ 4) := by
    simp only [compactProd, compactFactor, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, C_neg, C_0, ← hQ, ← ha, ← hb]
    linear_combination (-(X ^ 2 + Q) * X ^ 2 * (X ^ 2 + Q) ^ 2) * hsum + ((X ^ 2 + Q) * X ^ 4) * hprod
  rw [hmap, hL, hK, C_pow, ← hQ]
  ring

/-- **The law is sharp.** The black hole of genus two has one trivial zero, the fewest the law allows, and its scaled coefficient has size one. -/
theorem genusTwo_sharp {q : ℕ} (hq : 2 ≤ q) :
    |(scalePoly q (genusTwoIndex q) (fun i => genusTwoRay i)).coeff (2 * 1)| = 1 := by
  obtain ⟨ls, hfac⟩ := genusTwo_factorization q
  have h := (genus_le_trivial_zeros hq _ _ (genusTwoL_monic q) (genusTwoL_natDegree q)
    (genusTwoL_functional_equation (by omega)) hfac).2
  have hq0 : ((q : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  exact mul_right_cancel₀ hq0 (by rw [h]; ring)

/-! ### The critical circle -/

/-- A quadratic with negative discriminant has its roots on the circle `|z|² = q`. -/
theorem normSq_of_quadratic {Q t : ℝ} (ht : t ^ 2 < 4 * Q) {z : ℂ}
    (hz : z ^ 2 - (t : ℂ) * z + (Q : ℂ) = 0) : Complex.normSq z = Q := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_im, zero_mul, sub_zero,
    add_zero] at hre him
  rw [Complex.normSq_apply]
  have hfac : z.im * (2 * z.re - t) = 0 := by linear_combination him
  rcases mul_eq_zero.mp hfac with h | h
  · rw [h] at hre
    nlinarith [sq_nonneg (z.re - t / 2)]
  · have hu : z.re = t / 2 := by linarith
    rw [hu] at hre ⊢
    linarith

/-- The two traces of `L_q`. -/
theorem exists_traces (q : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ r ^ 2 = (q : ℝ) ^ 2 + 8 * q := by
  refine ⟨Real.sqrt ((q : ℝ) ^ 2 + 8 * q), Real.sqrt_nonneg _, Real.sq_sqrt (by positivity)⟩

/-- **For `q ≥ 4` the functional equation has a mode off the critical circle**, with `z` real. -/
theorem genusTwoL_off_circle {q : ℕ} (hq : 4 ≤ q) :
    ∃ z : ℝ, (genusTwoL q).eval (z : ℂ) = 0 ∧ (q : ℝ) < z ^ 2 := by
  obtain ⟨r, hr0, hr⟩ := exists_traces q
  have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hr2 : (q : ℝ) + 2 < r := by
    by_contra h
    push Not at h
    nlinarith
  set t₁ : ℝ := ((q : ℝ) - 2 + r) / 2 with ht₁
  set t₂ : ℝ := ((q : ℝ) - 2 - r) / 2 with ht₂
  have ht : (q : ℝ) < t₁ := by
    rw [ht₁]
    linarith
  have hD : 0 ≤ t₁ ^ 2 - 4 * q := by nlinarith
  have hbig : 4 * (q : ℝ) < t₁ ^ 2 := by nlinarith
  obtain ⟨w, hw0, hw⟩ : ∃ w : ℝ, 0 ≤ w ∧ w ^ 2 = t₁ ^ 2 - 4 * q :=
    ⟨Real.sqrt _, Real.sqrt_nonneg _, Real.sq_sqrt hD⟩
  have hz : (((t₁ + w) / 2 : ℝ)) ^ 2 - t₁ * ((t₁ + w) / 2) + q = 0 := by
    linear_combination (1 / 4 : ℝ) * hw
  refine ⟨(t₁ + w) / 2, ?_, ?_⟩
  · have h₁ : (t₁ : ℂ) + (t₂ : ℂ) = (q : ℂ) - 2 := by
      have : t₁ + t₂ = (q : ℝ) - 2 := by
        rw [ht₁, ht₂]
        ring
      exact_mod_cast this
    have h₂ : (t₁ : ℂ) * (t₂ : ℂ) = 1 - 3 * (q : ℂ) := by
      have : t₁ * t₂ = 1 - 3 * (q : ℝ) := by
        rw [ht₁, ht₂]
        linear_combination (-1 / 4 : ℝ) * hr
      exact_mod_cast this
    rw [genusTwoL_factor h₁ h₂]
    have hzC : ((((t₁ + w) / 2 : ℝ) : ℂ)) ^ 2 - (t₁ : ℂ) * (((t₁ + w) / 2 : ℝ) : ℂ) + (q : ℂ) = 0 := by
      exact_mod_cast hz
    rw [hzC, zero_mul]
  · nlinarith

/-- **All the modes of `L_q` are on the critical circle if and only if `q ≤ 3`.** -/
theorem genusTwo_critical_iff {q : ℕ} (hq : 2 ≤ q) :
    (∀ z : ℂ, (genusTwoL q).eval z = 0 → Complex.normSq z = q) ↔ q ≤ 3 := by
  constructor
  · intro h
    by_contra hq3
    obtain ⟨z, hz, hbig⟩ := genusTwoL_off_circle (q := q) (by omega)
    have := h _ hz
    rw [Complex.normSq_ofReal] at this
    nlinarith
  · intro hq3 z hz
    obtain ⟨r, hr0, hr⟩ := exists_traces q
    set t₁ : ℝ := ((q : ℝ) - 2 + r) / 2 with ht₁
    set t₂ : ℝ := ((q : ℝ) - 2 - r) / 2 with ht₂
    have hs : t₁ + t₂ = (q : ℝ) - 2 := by
      rw [ht₁, ht₂]
      ring
    have hp : t₁ * t₂ = 1 - 3 * (q : ℝ) := by
      rw [ht₁, ht₂]
      linear_combination (-1 / 4 : ℝ) * hr
    have h₁ : (t₁ : ℂ) + (t₂ : ℂ) = (q : ℂ) - 2 := by exact_mod_cast hs
    have h₂ : (t₁ : ℂ) * (t₂ : ℂ) = 1 - 3 * (q : ℂ) := by exact_mod_cast hp
    have hb₁ : t₁ ^ 2 < 4 * (q : ℝ) ∧ t₂ ^ 2 < 4 * (q : ℝ) := by
      rw [ht₁, ht₂]
      have hcases : q = 2 ∨ q = 3 := by omega
      rcases hcases with rfl | rfl
      · push_cast at hr ⊢
        constructor <;> nlinarith
      · push_cast at hr ⊢
        constructor <;> nlinarith
    rw [genusTwoL_factor h₁ h₂] at hz
    have hcast : ((q : ℝ) : ℂ) = (q : ℂ) := by simp
    rcases mul_eq_zero.mp hz with h | h
    · exact normSq_of_quadratic hb₁.1 (by rw [hcast]; exact h)
    · exact normSq_of_quadratic hb₁.2 (by rw [hcast]; exact h)

/-- **The functional equation at genus two does not force universal damping.** For `q ≥ 4`, the graph has `q + 1` edges at every vertex, its numerator has the functional equation of genus two, and it has a resonance slower than universal. -/
theorem universal_damping_not_forced_at_genus_two {q : ℕ} (hq : 4 ≤ q) :
    (∀ v, ∑ u, genusTwoIndex q v u + genusTwoRay v = (q : ℤ) + 1) ∧
      (∀ w : ℂ, w ≠ 0 → (genusTwoL q).reverse.eval w =
        ((q : ℂ) * w ^ 2) ^ 2 * (genusTwoL q).reverse.eval (1 / ((q : ℂ) * w))) ∧
      ∃ (x : ℂ) (f : Fin 11 → ℂ), x ≠ 0 ∧ f ≠ 0 ∧
        (∀ v, ∑ u, (genusTwoIndex q v u : ℂ) * f u + (genusTwoRay v : ℂ) * ((q : ℂ) / x) * f v =
          (x + (q : ℂ) / x) * f v) ∧ (q : ℝ) < Complex.normSq (x ^ 2) := by
  refine ⟨genusTwo_row q, genusTwoL_functional_equation (by omega), ?_⟩
  obtain ⟨z, hz, hbig⟩ := genusTwoL_off_circle hq
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) two_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hz0 : z ≠ 0 := by
    rintro rfl
    nlinarith
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hz0
    have : (z : ℂ) = 0 := by
      rw [← hx]
      simp
    exact_mod_cast this
  obtain ⟨ls, hfac⟩ := genusTwo_factorization q
  have hroot : modeEval q (genusTwoIndex q) (fun i => genusTwoRay i) x = 0 := by
    rw [modeEval, hfac, eval_mul, eval_mul, eval_mul, eval_comp]
    simp only [eval_pow, eval_X, hx, hz]
    ring
  obtain ⟨f, hf0, hf⟩ := exists_field_of_root q _ _ hx0 hroot
  refine ⟨x, f, hx0, hf0, hf, ?_⟩
  rw [hx, Complex.normSq_ofReal]
  nlinarith

end GaloisForLFunctions.ArithmeticScatteringHolography

end
