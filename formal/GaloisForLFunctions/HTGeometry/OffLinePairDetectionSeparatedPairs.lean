import GaloisForLFunctions.HTGeometry.OffLinePairDetectionMaclaurinBound
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Detection order of an off-line pair among separated off-line pairs

A real polynomial `E` is a *Maclaurin environment of mass `σ`* (`IsMaclaurinEnv E σ`) if
`E(0) = 1`, its coefficients are `≥ 0`, and `(j + 1) e_{j+1} ≤ σ e_j` for every `j`, i.e. the
coefficients of `σE − E'` are `≥ 0`.

* Environments multiply, and masses add (`IsMaclaurinEnv.mul`, `isMaclaurinEnv_prod`). The defect
  `(σ₁ + σ₂)E₁E₂ − (E₁E₂)'` is `(σ₁E₁ − E₁')E₂ + E₁(σ₂E₂ − E₂')`.
* `1 + vX` (`v ≥ 0`) is an environment of mass `v`. `1 + aX + bX²` with `a, b ≥ 0` and
  `2b ≤ a²` is an environment of mass `a`. Its defect is `(a² − 2b)X + abX²`.
* For every environment, `(1 − X)^{2m} E` has a negative coefficient of some order
  `1 ≤ j ≤ σ + 1` (`IsMaclaurinEnv.exists_coeff_neg`), by the argument of
  `exists_coeff_neg_one_sub_X_pow_mul_prod`.

**Theorem** (`exists_separatedSlice_coeff_neg`). Let `f(z) = ((z − γ)² + δ²)^m ∏ (z − γ_i)
∏ ((z − ε_k)² + d_k²)` with `δ ≠ 0`, `m ≥ 1`, real `γ_i ≠ γ`, and off-line pairs `ε_k ± i d_k` that
are separated from the ordinate: `|γ − ε_k| ≥ (1 + √2)|d_k|`. The slice of `f` at `γ` in `y = x²`
is `(δ² − y)^{2m} ∏ ((γ − γ_i)² + y) ∏ (y² + 2(D_k − d_k²)y + A_k²)` with `D_k = (γ − ε_k)²` and
`A_k = D_k + d_k²` (`separatedPairSlice_eq_eval`). It has a negative coefficient of some order
`1 ≤ j ≤ δ²(Σ (γ − γ_i)^{−2} + Σ 2(D_k − d_k²)/A_k²) + 1`.

So an off-line pair is detected at its own ordinate by a bounded Laguerre order. This holds when
the background is real (`exists_offLinePairSlice_coeff_neg`) and also when the background contains
other off-line pairs, as long as they are horizontally `(1 + √2)`-separated relative to their own
depth. The separation is exactly the condition `2b ≤ a²` for the normalized slice factor
`1 + aY + bY²` of a pair.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A Maclaurin environment of mass `σ`. -/
def IsMaclaurinEnv (E : ℝ[X]) (σ : ℝ) : Prop :=
  E.coeff 0 = 1 ∧ (∀ n, 0 ≤ E.coeff n) ∧ ∀ n, 0 ≤ (C σ * E - derivative E).coeff n

theorem coeff_mul_nonneg_of_forall {p q : ℝ[X]} (hp : ∀ n, 0 ≤ p.coeff n)
    (hq : ∀ n, 0 ≤ q.coeff n) (n : ℕ) : 0 ≤ (p * q).coeff n := by
  rw [coeff_mul]
  exact sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

/-- The Maclaurin inequality of an environment. -/
theorem IsMaclaurinEnv.maclaurin {E : ℝ[X]} {σ : ℝ} (h : IsMaclaurinEnv E σ) (j : ℕ) :
    ((j : ℝ) + 1) * E.coeff (j + 1) ≤ σ * E.coeff j := by
  have := h.2.2 j
  rw [coeff_sub, coeff_C_mul, coeff_derivative] at this
  linarith

theorem isMaclaurinEnv_one : IsMaclaurinEnv 1 0 := by
  refine ⟨by simp, fun n => ?_, fun n => by simp⟩
  rw [coeff_one]
  split_ifs <;> norm_num

theorem IsMaclaurinEnv.mul {E₁ E₂ : ℝ[X]} {σ₁ σ₂ : ℝ} (h₁ : IsMaclaurinEnv E₁ σ₁)
    (h₂ : IsMaclaurinEnv E₂ σ₂) : IsMaclaurinEnv (E₁ * E₂) (σ₁ + σ₂) := by
  refine ⟨by rw [mul_coeff_zero, h₁.1, h₂.1, one_mul],
    coeff_mul_nonneg_of_forall h₁.2.1 h₂.2.1, fun n => ?_⟩
  have hid : C (σ₁ + σ₂) * (E₁ * E₂) - derivative (E₁ * E₂) =
      (C σ₁ * E₁ - derivative E₁) * E₂ + E₁ * (C σ₂ * E₂ - derivative E₂) := by
    rw [derivative_mul, C_add]
    ring
  rw [hid, coeff_add]
  exact add_nonneg (coeff_mul_nonneg_of_forall h₁.2.2 h₂.2.1 n)
    (coeff_mul_nonneg_of_forall h₁.2.1 h₂.2.2 n)

theorem isMaclaurinEnv_prod {ι : Type*} (s : Finset ι) (F : ι → ℝ[X]) (σ : ι → ℝ)
    (h : ∀ i ∈ s, IsMaclaurinEnv (F i) (σ i)) :
    IsMaclaurinEnv (∏ i ∈ s, F i) (∑ i ∈ s, σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMaclaurinEnv_one
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-- `1 + vX` is an environment of mass `v`. -/
theorem isMaclaurinEnv_linear {v : ℝ} (hv : 0 ≤ v) : IsMaclaurinEnv (1 + C v * X) v := by
  refine ⟨by simp, coeff_one_add_C_mul_X_nonneg hv, fun n => ?_⟩
  have hid : C v * (1 + C v * X) - derivative (1 + C v * X) = C (v ^ 2) * X := by
    simp only [derivative_add, derivative_one, derivative_C_mul_X, zero_add, map_pow]
    ring
  rw [hid, coeff_C_mul_X]
  split_ifs <;> positivity

/-- `1 + aX + bX²` with `a, b ≥ 0` and `2b ≤ a²` is an environment of mass `a`. -/
theorem isMaclaurinEnv_quadratic {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) :
    IsMaclaurinEnv (1 + C a * X + C b * X ^ 2) a := by
  have hc : ∀ n, (1 + C a * X + C b * X ^ 2 : ℝ[X]).coeff n =
      if n = 0 then 1 else if n = 1 then a else if n = 2 then b else 0 := by
    intro n
    rw [coeff_add, coeff_add, coeff_one, coeff_C_mul_X, coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | n <;> simp
  refine ⟨by rw [hc]; simp, fun n => ?_, fun n => ?_⟩
  · rw [hc]
    split_ifs
    · norm_num
    · exact ha
    · exact hb
    · norm_num
  · have hid : C a * (1 + C a * X + C b * X ^ 2) - derivative (1 + C a * X + C b * X ^ 2) =
        C (a ^ 2 - 2 * b) * X + C (a * b) * X ^ 2 := by
      have hder : derivative (1 + C a * X + C b * X ^ 2 : ℝ[X]) = C a + C (2 * b) * X := by
        simp only [derivative_add, derivative_one, derivative_C_mul_X, derivative_C_mul_X_pow]
        rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, show (2 - 1 : ℕ) = 1 by norm_num, pow_one, zero_add,
          mul_comm b 2]
      rw [hder]
      simp only [map_sub, map_mul, map_pow]
      ring
    rw [hid, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow]
    have h1 : 0 ≤ a ^ 2 - 2 * b := by linarith
    have h2 : 0 ≤ a * b := mul_nonneg ha hb
    split_ifs <;> linarith

/-- **Detection order for an environment.** If `E` is an environment of mass `σ ≥ 0` and `m ≥ 1`,
then `(1 − X)^{2m} E` has a negative coefficient of some order `1 ≤ j ≤ σ + 1`. -/
theorem IsMaclaurinEnv.exists_coeff_neg {E : ℝ[X]} {σ : ℝ} (hE : IsMaclaurinEnv E σ)
    (hσ : 0 ≤ σ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ σ + 1 ∧ ((1 - X) ^ (2 * m) * E).coeff j < 0 := by
  set J := max 1 ⌈σ⌉₊ with hJ
  by_contra hcon
  push Not at hcon
  have h0 : E.coeff 0 = 1 := hE.1
  have hnn : ∀ n, 0 ≤ E.coeff n := hE.2.1
  have hJσ1 : (J : ℝ) ≤ σ + 1 := by
    rcases le_total 1 ⌈σ⌉₊ with h | h
    · rw [hJ, max_eq_right h]
      exact (Nat.ceil_lt_add_one hσ).le
    · rw [hJ, max_eq_left h]
      push_cast
      linarith
  have hall : ∀ j ≤ J, 0 ≤ ((1 - X) ^ (2 * m) * E).coeff j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [coeff_one_sub_X_pow_mul_zero, h0]
      norm_num
    · refine hcon j hjpos ?_
      have : (j : ℝ) ≤ J := by exact_mod_cast hj
      linarith
  obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 2 := ⟨2 * m - 2, by omega⟩
  rw [hk] at hall
  have h2 := coeff_two_nonneg_of_pow h0 k hall
  have h1 := one_le_coeff_of_one_sub_X_mul_nonneg (P := (1 - X) * E)
    (by rw [← pow_one (1 - X : ℝ[X]), coeff_one_sub_X_pow_mul_zero, h0])
    (fun i hi => by rw [← mul_assoc, ← pow_two]; exact h2 i hi)
  have hJ1 : 1 ≤ J := le_max_left _ _
  obtain ⟨J', hJ'⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  have hdiff := h1 J le_rfl
  rw [hJ', sub_mul, one_mul, coeff_sub, coeff_X_mul] at hdiff
  have hmac := hE.maclaurin J'
  have hJσ : σ ≤ (J' : ℝ) + 1 := by
    have h := (Nat.le_ceil σ).trans (Nat.cast_le.mpr (le_max_right 1 ⌈σ⌉₊))
    rw [← hJ, hJ'] at h
    push_cast at h
    exact h
  have he1 : 1 ≤ E.coeff (J' + 1) := by linarith [hnn J']
  have hstep : ((J' : ℝ) + 1) * E.coeff (J' + 1) ≤ σ * (E.coeff (J' + 1) - 1) :=
    hmac.trans (mul_le_mul_of_nonneg_left (by linarith) hσ)
  nlinarith [mul_nonneg (sub_nonneg.mpr hJσ) (sub_nonneg.mpr he1)]

/-- Separation `|γ − ε| ≥ (1 + √2)|d|` in algebraic form: with `D = (γ − ε)²` and `q = d²`,
`q ≤ D` and `(D + q)² ≤ 2(D − q)²`. -/
theorem separation_algebraic {D q : ℝ} (hq : 0 ≤ q) (hD : (1 + Real.sqrt 2) ^ 2 * q ≤ D) :
    q ≤ D ∧ (D + q) ^ 2 ≤ 2 * (D - q) ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hqD : q ≤ D := by nlinarith
  refine ⟨hqD, ?_⟩
  -- `D + q ≤ √2 (D − q)` and both sides are `≥ 0`
  have hkey : D + q ≤ Real.sqrt 2 * (D - q) := by nlinarith
  have h0 : 0 ≤ D + q := by linarith
  calc (D + q) ^ 2 ≤ (Real.sqrt 2 * (D - q)) ^ 2 := pow_le_pow_left₀ h0 hkey 2
    _ = 2 * (D - q) ^ 2 := by rw [mul_pow, hs]

/-- The slice factor of a separated off-line pair, normalized and rescaled, is an environment. -/
theorem isMaclaurinEnv_pairFactor {D q δ : ℝ} (hqD : q ≤ D)
    (hsep : (D + q) ^ 2 ≤ 2 * (D - q) ^ 2) (hA : 0 < D + q) :
    IsMaclaurinEnv (1 + C (2 * (D - q) * δ ^ 2 / (D + q) ^ 2) * X + C (δ ^ 4 / (D + q) ^ 2) * X ^ 2)
      (2 * (D - q) * δ ^ 2 / (D + q) ^ 2) := by
  refine isMaclaurinEnv_quadratic (by positivity) (by positivity) ?_
  have hA2 : 0 < (D + q) ^ 2 := by positivity
  rw [div_pow, mul_pow, mul_pow, le_div_iff₀ (by positivity)]
  have h4 : 0 ≤ δ ^ 4 := by positivity
  have : 2 * (δ ^ 4 / (D + q) ^ 2) * ((D + q) ^ 2) ^ 2 = 2 * δ ^ 4 * (D + q) ^ 2 := by
    field_simp
  rw [this]
  have : 2 ^ 2 * (D - q) ^ 2 * (δ ^ 2) ^ 2 = 2 * δ ^ 4 * (2 * (D - q) ^ 2) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hsep (by positivity)

/-- **Detection among separated pairs.** Let `δ ≠ 0`, `m ≥ 1`, real `γ_i ≠ γ`, and off-line pairs
`ε_k ± i d_k` with `|γ − ε_k| ≥ (1 + √2)|d_k|` and `d_k ≠ 0`. With `D_k = (γ − ε_k)²`, the slice
polynomial `(δ² − y)^{2m} ∏ ((γ − γ_i)² + y) ∏ (y² + 2(D_k − d_k²)y + (D_k + d_k²)²)` has a negative
coefficient of some order `1 ≤ j ≤ δ²(Σ (γ − γ_i)^{−2} + Σ 2(D_k − d_k²)/(D_k + d_k²)²) + 1`. -/
theorem exists_separatedSlice_coeff_neg {ι κ : Type*} (s : Finset ι) (t : Finset κ) (γ δ : ℝ)
    (g : ι → ℝ) (ε d : κ → ℝ) (hδ : δ ≠ 0) (hg : ∀ i ∈ s, g i ≠ γ) (hd : ∀ k ∈ t, d k ≠ 0)
    (hsep : ∀ k ∈ t, (1 + Real.sqrt 2) * |d k| ≤ |γ - ε k|) {m : ℕ} (hm : 1 ≤ m) :
    ∃ j : ℕ, 1 ≤ j ∧
      (j : ℝ) ≤ δ ^ 2 * (∑ i ∈ s, 1 / (γ - g i) ^ 2 +
        ∑ k ∈ t, 2 * ((γ - ε k) ^ 2 - d k ^ 2) / ((γ - ε k) ^ 2 + d k ^ 2) ^ 2) + 1 ∧
      ((C (δ ^ 2) - X) ^ (2 * m) * (∏ i ∈ s, (X + C ((γ - g i) ^ 2))) *
        ∏ k ∈ t, (X ^ 2 + C (2 * ((γ - ε k) ^ 2 - d k ^ 2)) * X +
          C (((γ - ε k) ^ 2 + d k ^ 2) ^ 2))).coeff j < 0 := by
  set Dk : κ → ℝ := fun k => (γ - ε k) ^ 2 with hDk
  set qk : κ → ℝ := fun k => d k ^ 2 with hqk
  have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ
  have hδ2pos : 0 < δ ^ 2 := by positivity
  set r : ℝ := 1 / δ ^ 2 with hr
  have hgne : ∀ i ∈ s, (γ - g i) ^ 2 ≠ 0 := fun i hi =>
    pow_ne_zero 2 (sub_ne_zero.mpr (hg i hi).symm)
  -- separation in algebraic form
  have halg : ∀ k ∈ t, qk k ≤ Dk k ∧ (Dk k + qk k) ^ 2 ≤ 2 * (Dk k - qk k) ^ 2 := by
    intro k hk
    refine separation_algebraic (sq_nonneg _) ?_
    have h := hsep k hk
    have h0 : 0 ≤ (1 + Real.sqrt 2) * |d k| := by positivity
    have := pow_le_pow_left₀ h0 h 2
    simp only [hDk, hqk]
    rw [mul_pow, sq_abs, sq_abs] at this
    exact this
  have hApos : ∀ k ∈ t, 0 < Dk k + qk k := fun k hk => by
    have : 0 < qk k := by
      simp only [hqk]; exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (hd k hk)).symm
    have : 0 ≤ Dk k := sq_nonneg _
    linarith
  -- the normalized environment
  set v : ι → ℝ := fun i => δ ^ 2 / (γ - g i) ^ 2 with hvdef
  set a : κ → ℝ := fun k => 2 * (Dk k - qk k) * δ ^ 2 / (Dk k + qk k) ^ 2 with hadef
  set b : κ → ℝ := fun k => δ ^ 4 / (Dk k + qk k) ^ 2 with hbdef
  set E : ℝ[X] := (∏ i ∈ s, (1 + C (v i) * X)) * ∏ k ∈ t, (1 + C (a k) * X + C (b k) * X ^ 2)
    with hE
  have hEnv : IsMaclaurinEnv E (∑ i ∈ s, v i + ∑ k ∈ t, a k) :=
    (isMaclaurinEnv_prod s _ v fun i hi => isMaclaurinEnv_linear (by positivity)).mul
      (isMaclaurinEnv_prod t _ a fun k hk => isMaclaurinEnv_pairFactor
        (halg k hk).1 (halg k hk).2 (hApos k hk))
  have hσ : 0 ≤ ∑ i ∈ s, v i + ∑ k ∈ t, a k := by
    refine add_nonneg (sum_nonneg fun i _ => by positivity) (sum_nonneg fun k hk => ?_)
    have := (halg k hk).1
    have : 0 ≤ Dk k - qk k := by linarith
    positivity
  obtain ⟨j, hj1, hjle, hneg⟩ := hEnv.exists_coeff_neg hσ hm
  -- rescaling `X ↦ rX`
  set N : ℝ[X] := (1 - X) ^ (2 * m) * E with hN
  set κ₀ : ℝ := (δ ^ 2) ^ (2 * m) * (∏ i ∈ s, (γ - g i) ^ 2) * ∏ k ∈ t, (Dk k + qk k) ^ 2
    with hκ₀
  have hκpos : 0 < κ₀ := by
    refine mul_pos (mul_pos (by positivity) (prod_pos fun i hi => ?_))
      (prod_pos fun k hk => by have := hApos k hk; positivity)
    exact lt_of_le_of_ne (sq_nonneg _) (hgne i hi).symm
  have e1 : (C (δ ^ 2) - X : ℝ[X]) = C (δ ^ 2) * (1 - C r * X) := by
    rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, show δ ^ 2 * r = 1 by rw [hr]; field_simp, C_1,
      one_mul]
  have e2 : ∀ i ∈ s, (X + C ((γ - g i) ^ 2) : ℝ[X]) =
      C ((γ - g i) ^ 2) * (1 + C (v i) * (C r * X)) := by
    intro i hi
    have hgi : γ - g i ≠ 0 := sub_ne_zero.mpr (hg i hi).symm
    have hs : (γ - g i) ^ 2 * v i * r = 1 := by
      simp only [hvdef, hr]
      field_simp
    rw [mul_add, mul_one, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hs, C_1, one_mul, add_comm]
  have e3 : ∀ k ∈ t, (X ^ 2 + C (2 * ((γ - ε k) ^ 2 - d k ^ 2)) * X +
      C (((γ - ε k) ^ 2 + d k ^ 2) ^ 2) : ℝ[X]) =
      C ((Dk k + qk k) ^ 2) * (1 + C (a k) * (C r * X) + C (b k) * (C r * X) ^ 2) := by
    intro k hk
    have hA0 : Dk k + qk k ≠ 0 := (hApos k hk).ne'
    have hA0' : (γ - ε k) ^ 2 + d k ^ 2 ≠ 0 := hA0
    have ha : (Dk k + qk k) ^ 2 * a k * r = 2 * ((γ - ε k) ^ 2 - d k ^ 2) := by
      simp only [hadef, hr, hDk, hqk]
      field_simp
    have hb : (Dk k + qk k) ^ 2 * b k * r ^ 2 = 1 := by
      simp only [hbdef, hr]
      field_simp
    have hAk : (Dk k + qk k) ^ 2 = ((γ - ε k) ^ 2 + d k ^ 2) ^ 2 := by simp only [hDk, hqk]
    calc (X ^ 2 + C (2 * ((γ - ε k) ^ 2 - d k ^ 2)) * X +
          C (((γ - ε k) ^ 2 + d k ^ 2) ^ 2) : ℝ[X])
        = C ((Dk k + qk k) ^ 2) + C ((Dk k + qk k) ^ 2 * a k * r) * X +
            C ((Dk k + qk k) ^ 2 * b k * r ^ 2) * X ^ 2 := by
          rw [ha, hb, hAk, C_1, one_mul]
          ring
      _ = _ := by
          simp only [map_mul, map_pow]
          ring
  have hcomp : N.comp (C r * X) = (1 - C r * X) ^ (2 * m) *
      ((∏ i ∈ s, (1 + C (v i) * (C r * X))) *
        ∏ k ∈ t, (1 + C (a k) * (C r * X) + C (b k) * (C r * X) ^ 2)) := by
    simp only [hN, hE, mul_comp, pow_comp, sub_comp, one_comp, X_comp, Polynomial.prod_comp,
      add_comp, C_comp]
  have hQ : (C (δ ^ 2) - X) ^ (2 * m) * (∏ i ∈ s, (X + C ((γ - g i) ^ 2))) *
      ∏ k ∈ t, (X ^ 2 + C (2 * ((γ - ε k) ^ 2 - d k ^ 2)) * X +
        C (((γ - ε k) ^ 2 + d k ^ 2) ^ 2)) = C κ₀ * N.comp (C r * X) := by
    rw [hcomp, e1, prod_congr rfl e2, prod_congr rfl e3, mul_pow, prod_mul_distrib,
      prod_mul_distrib, hκ₀]
    simp only [map_mul, map_pow, map_prod]
    ring
  refine ⟨j, hj1, ?_, ?_⟩
  · have hv : ∑ i ∈ s, v i = δ ^ 2 * ∑ i ∈ s, 1 / (γ - g i) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [hvdef]
      ring
    have ha : ∑ k ∈ t, a k = δ ^ 2 * ∑ k ∈ t, 2 * ((γ - ε k) ^ 2 - d k ^ 2) /
        ((γ - ε k) ^ 2 + d k ^ 2) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [hadef, hDk, hqk]
      ring
    rw [mul_add, ← hv, ← ha]
    exact hjle
  · rw [hQ, coeff_C_mul, comp_C_mul_X_coeff]
    have hrpos : 0 < r ^ j := by positivity
    exact mul_neg_of_pos_of_neg hκpos (mul_neg_of_neg_of_pos hneg hrpos)

/-- The slice of a separated pair factor `(z − ε)² + d²` at the ordinate `γ`, in `y = x²`:
`((γ + ix − ε)² + d²)((γ − ix − ε)² + d²) = y² + 2(D − d²)y + (D + d²)²`, `D = (γ − ε)²`. -/
theorem separatedPairSlice_eq_eval (γ ε d x : ℝ) :
    (((γ : ℂ) + x * Complex.I - ε) ^ 2 + (d : ℂ) ^ 2) *
        (((γ : ℂ) - x * Complex.I - ε) ^ 2 + (d : ℂ) ^ 2) =
      (((X ^ 2 + C (2 * ((γ - ε) ^ 2 - d ^ 2)) * X + C (((γ - ε) ^ 2 + d ^ 2) ^ 2) : ℝ[X]).eval
        (x ^ 2) : ℝ) : ℂ) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  push_cast
  linear_combination ((x : ℂ) ^ 4 * (Complex.I ^ 2 - 1) +
    2 * (x : ℂ) ^ 2 * ((d : ℂ) ^ 2 - ((γ : ℂ) - ε) ^ 2)) * hI

end

end GaloisForLFunctions.HTGeometry
