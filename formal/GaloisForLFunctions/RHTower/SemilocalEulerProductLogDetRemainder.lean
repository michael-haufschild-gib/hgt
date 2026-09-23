import GaloisForLFunctions.RHTower.SemilocalFinitePrimeSecondOrder
import GaloisForLFunctions.RHTower.MatrixEntryNormLogDetRemainder

/-!
# The determinant-level Taylor remainder for the true finite-`S` Euler product

For rapidities `δ_a` and amplitudes `ε_a ∈ [0, 1/6]` (`a : Fin k`) the **true** Euler-product weight
`W(s) = ∏_a (1 − 2ε_a cos(δ_a s) + ε_a²)⁻¹` has Gram matrix `G_n = 1 + M₁ + M₂ + E` in the
orthonormal archimedean Jacobi basis, where `M₁ = Σ ε_a T(δ_a)`, `M₂` is the second-order ray
matrix of `SemilocalFinitePrimeSecondOrder`, and `E` is the Gram matrix of the third-order weight
discrepancy `W − (1 + A + B)`.

We prove

* the weight-level cubic bound `|W − (1 + A + B)| ≤ (3/2)^k · 60 Σ ε_a³ + 12800 (Σ ε_a)³`
  (`abs_eulerProductWeight_sub_rayWeight_le`), from the one-factor `60ε³` bound, a telescoping
  product estimate and a cubic form of the quadratic-truncation lemma;
* entrywise Gram bounds `|∫ p_i p_j f| ≤ sup |f|` from orthonormality (no Cauchy–Schwarz needed:
  `|p_i p_j| ≤ ½(p_i² + p_j²)`);
* **the main theorem** `abs_log_det_eulerProductGram_sub_jet_le`:
  `|log det G_n − (tr M₁ + tr M₂ − ½ tr M₁²)| ≤ [explicit third-order bound]`, i.e. the log-Gram
  determinant of the true Euler product equals the second-order jet
  `Σ ε_a J_{δ_a} + ½ (Σ_{a,b} ε_a ε_b B_{ab} + Σ ε_a² J_{2δ_a})` up to an explicit `O(ε³)` remainder
  (`secondOrderLogDetJet_eq`);
* the Hankel-quotient form for the squared Jacobi radius
  `log (a²_{n+1}/r²_{n+1}) = ΔΔ log det G` (`abs_log_eulerProductSquaredRadius_sub_jet_le`).

The constants are explicit but crude in `n` (they go through the `ℓ¹` entry norm, so the smallness
condition is `entrySize ε n = (n+1)² (2V + 3V² + ρ) < 1`, `V = Σ ε_a`).
-/

namespace RHTower.CosineModeResponse

open MeasureTheory Polynomial Finset RHTower.MatrixLogDet RHTower.FirstEulerCriticalJet

/-! ## Two finite-product lemmas -/

/-- **Telescoping product bound.** -/
theorem abs_finset_prod_sub_prod_le {κ : Type*} [DecidableEq κ] (s : Finset κ) (f g : κ → ℝ) {C : ℝ}
    (hC : 1 ≤ C) (hf : ∀ a ∈ s, |f a| ≤ C) (hg : ∀ a ∈ s, |g a| ≤ C) :
    |∏ a ∈ s, f a - ∏ a ∈ s, g a| ≤ C ^ s.card * ∑ a ∈ s, |f a - g a| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    have hf' : ∀ a ∈ s, |f a| ≤ C := fun a ha => hf a (Finset.mem_insert_of_mem ha)
    have hg' : ∀ a ∈ s, |g a| ≤ C := fun a ha => hg a (Finset.mem_insert_of_mem ha)
    have ih' := ih hf' hg'
    rw [Finset.prod_insert hc, Finset.prod_insert hc, Finset.sum_insert hc,
      Finset.card_insert_of_notMem hc]
    have hfc : |f c| ≤ C := hf c (Finset.mem_insert_self c s)
    have hPg : |∏ a ∈ s, g a| ≤ C ^ s.card := by
      rw [Finset.abs_prod]
      calc ∏ a ∈ s, |g a| ≤ ∏ _a ∈ s, C :=
            Finset.prod_le_prod (fun a _ => abs_nonneg _) (fun a ha => hg' a ha)
        _ = C ^ s.card := Finset.prod_const C
    have hid : f c * ∏ a ∈ s, f a - g c * ∏ a ∈ s, g a =
        f c * (∏ a ∈ s, f a - ∏ a ∈ s, g a) + (f c - g c) * ∏ a ∈ s, g a := by ring
    rw [hid]
    have hS : 0 ≤ ∑ a ∈ s, |f a - g a| := Finset.sum_nonneg fun a _ => abs_nonneg _
    have hCn : 0 ≤ C ^ s.card := by positivity
    have hC0 : 0 ≤ C := by linarith
    calc |f c * (∏ a ∈ s, f a - ∏ a ∈ s, g a) + (f c - g c) * ∏ a ∈ s, g a|
        ≤ |f c| * |∏ a ∈ s, f a - ∏ a ∈ s, g a| + |f c - g c| * |∏ a ∈ s, g a| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ C * (C ^ s.card * ∑ a ∈ s, |f a - g a|) + |f c - g c| * C ^ s.card := by
          gcongr
      _ ≤ C ^ (s.card + 1) * (|f c - g c| + ∑ a ∈ s, |f a - g a|) := by
          rw [pow_succ]
          have hd : C ^ s.card * |f c - g c| ≤ C ^ s.card * |f c - g c| * C :=
            le_mul_of_one_le_right (by positivity) hC
          nlinarith [hd, hS, hCn]

/-- **Cubic form of the quadratic-truncation bound.**  With `L = Σ (|x_a| + √|y_a|) ≤ 1`,
`|∏(1 + x_a + y_a) − (1 + Σx + Σy + ½((Σx)² − Σx²))| ≤ 200 L³`. -/
theorem abs_prod_sub_quadratic_le_cubic {κ : Type*} [DecidableEq κ] (s : Finset κ) (x y : κ → ℝ)
    (hLam : ∑ a ∈ s, (|x a| + Real.sqrt |y a|) ≤ 1) :
    |∏ a ∈ s, (1 + x a + y a) -
        (1 + ∑ a ∈ s, x a + (∑ a ∈ s, y a + (1 / 2) * ((∑ a ∈ s, x a) ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ))))| ≤
      200 * (∑ a ∈ s, (|x a| + Real.sqrt |y a|)) ^ (3 : ℕ) := by
  set L := ∑ a ∈ s, (|x a| + Real.sqrt |y a|) with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun a _ => by positivity
  rcases hL0.lt_or_eq with hpos | hzero
  · have hsx : ∑ a ∈ s, |x a| ≤ L := by
      rw [hL]
      exact Finset.sum_le_sum fun a _ => by linarith [Real.sqrt_nonneg |y a|]
    have hsy : ∑ a ∈ s, |y a| ≤ L ^ (2 : ℕ) := by
      calc ∑ a ∈ s, |y a| = ∑ a ∈ s, Real.sqrt |y a| ^ (2 : ℕ) :=
            Finset.sum_congr rfl fun a _ => by rw [Real.sq_sqrt (abs_nonneg _)]
        _ ≤ (∑ a ∈ s, Real.sqrt |y a|) ^ (2 : ℕ) :=
            Finset.sum_sq_le_sq_sum_of_nonneg fun a _ => Real.sqrt_nonneg _
        _ ≤ L ^ (2 : ℕ) := by
            have : ∑ a ∈ s, Real.sqrt |y a| ≤ L := by
              rw [hL]
              exact Finset.sum_le_sum fun a _ => by linarith [abs_nonneg (x a)]
            exact pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _) this 2
    have key := abs_prod_sub_quadratic_le s (fun a => x a / L) (fun a => y a / L ^ (2 : ℕ)) (t := L)
      (by rw [abs_of_pos hpos]; exact hLam)
    beta_reduce at key
    have e1 : ∀ a, 1 + L * (x a / L) + L ^ (2 : ℕ) * (y a / L ^ (2 : ℕ)) = 1 + x a + y a := fun a => by
      field_simp
    have e2 : 1 + L * ∑ a ∈ s, x a / L + L ^ (2 : ℕ) * (∑ a ∈ s, y a / L ^ (2 : ℕ) +
        1 / 2 * ((∑ a ∈ s, x a / L) ^ (2 : ℕ) - ∑ a ∈ s, (x a / L) ^ (2 : ℕ))) =
        1 + ∑ a ∈ s, x a + (∑ a ∈ s, y a + (1 / 2) * ((∑ a ∈ s, x a) ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ))) := by
      have e3 : ∑ a ∈ s, (x a / L) ^ (2 : ℕ) = (∑ a ∈ s, x a ^ (2 : ℕ)) / L ^ (2 : ℕ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [← Finset.sum_div, ← Finset.sum_div, e3]
      field_simp
    simp only [e1] at key
    rw [e2] at key
    refine key.trans ?_
    have hsum : ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|) ≤ 2 := by
      rw [Finset.sum_add_distrib]
      have h1 : ∑ a ∈ s, |x a / L| ≤ 1 := by
        calc ∑ a ∈ s, |x a / L| = (∑ a ∈ s, |x a|) / L := by
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl fun a _ => by rw [abs_div, abs_of_pos hpos]
          _ ≤ 1 := by rw [div_le_one hpos]; exact hsx
      have h2 : ∑ a ∈ s, |y a / L ^ (2 : ℕ)| ≤ 1 := by
        calc ∑ a ∈ s, |y a / L ^ (2 : ℕ)| = (∑ a ∈ s, |y a|) / L ^ (2 : ℕ) := by
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl fun a _ => by rw [abs_div, abs_of_pos (pow_pos hpos 2)]
          _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hsy
      linarith
    have hprod : ∏ a ∈ s, (1 + (|x a / L| + |y a / L ^ (2 : ℕ)|)) ≤ Real.exp 2 := by
      calc ∏ a ∈ s, (1 + (|x a / L| + |y a / L ^ (2 : ℕ)|)) ≤
            ∏ a ∈ s, Real.exp (|x a / L| + |y a / L ^ (2 : ℕ)|) :=
            Finset.prod_le_prod (fun a _ => by positivity)
              (fun a _ => by linarith [Real.add_one_le_exp (|x a / L| + |y a / L ^ (2 : ℕ)|)])
        _ = Real.exp (∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|)) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp 2 := Real.exp_le_exp.mpr hsum
    have hcube : (1 + ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|)) ^ (3 : ℕ) ≤ 27 := by
      have h0 : 0 ≤ 1 + ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|) := by positivity
      calc (1 + ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|)) ^ (3 : ℕ) ≤ 3 ^ (3 : ℕ) :=
            pow_le_pow_left₀ h0 (by linarith) 3
        _ = 27 := by norm_num
    have hexp : Real.exp 2 ≤ 200 / 27 := by
      have h := Real.exp_one_lt_d9
      have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [e]
      calc Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
            mul_le_mul h.le h.le h0 (by norm_num)
        _ ≤ 200 / 27 := by norm_num
    rw [abs_of_pos hpos]
    have hprod0 : 0 ≤ ∏ a ∈ s, (1 + (|x a / L| + |y a / L ^ (2 : ℕ)|)) :=
      Finset.prod_nonneg fun a _ => by positivity
    have hcube0 : 0 ≤ (1 + ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|)) ^ (3 : ℕ) := by positivity
    calc L ^ (3 : ℕ) * (∏ a ∈ s, (1 + (|x a / L| + |y a / L ^ (2 : ℕ)|))) *
          (1 + ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|)) ^ (3 : ℕ)
        ≤ L ^ (3 : ℕ) * (200 / 27) * 27 := by
          have hp := hprod.trans hexp
          have hL3 : 0 ≤ L ^ (3 : ℕ) := by positivity
          calc L ^ (3 : ℕ) * (∏ a ∈ s, (1 + (|x a / L| + |y a / L ^ (2 : ℕ)|))) *
                (1 + ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|)) ^ (3 : ℕ)
              ≤ L ^ (3 : ℕ) * (200 / 27) * (1 + ∑ a ∈ s, (|x a / L| + |y a / L ^ (2 : ℕ)|)) ^ (3 : ℕ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hL3) hcube0
            _ ≤ L ^ (3 : ℕ) * (200 / 27) * 27 :=
                mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = 200 * L ^ (3 : ℕ) := by ring
  · have hall : ∀ a ∈ s, |x a| + Real.sqrt |y a| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun a _ => by positivity).mp hzero.symm
    have hx0 : ∀ a ∈ s, x a = 0 := fun a ha => by
      have := hall a ha
      have h1 := abs_nonneg (x a)
      have h2 := Real.sqrt_nonneg |y a|
      exact abs_eq_zero.mp (by linarith)
    have hy0 : ∀ a ∈ s, y a = 0 := fun a ha => by
      have := hall a ha
      have h1 := abs_nonneg (x a)
      have h2 := Real.sqrt_nonneg |y a|
      have h3 : Real.sqrt |y a| = 0 := by linarith
      rw [Real.sqrt_eq_zero (abs_nonneg _)] at h3
      exact abs_eq_zero.mp h3
    rw [← hzero]
    rw [Finset.prod_congr rfl (fun a ha => by rw [hx0 a ha, hy0 a ha]; ring :
        ∀ a ∈ s, (1 + x a + y a) = 1),
      Finset.sum_congr rfl hx0, Finset.sum_congr rfl hy0,
      Finset.sum_congr rfl (fun a ha => by rw [hx0 a ha]; ring : ∀ a ∈ s, x a ^ (2 : ℕ) = 0)]
    simp

/-! ## Euler factors and the true product weight -/

/-- `1 / (1 − 2e cos x + e²)`. -/
noncomputable def semilocalEulerFactor (e x : ℝ) : ℝ := 1 / (1 - 2 * e * Real.cos x + e ^ (2 : ℕ))

/-- Its quadratic truncation `1 + 2e cos x + e²(1 + 2 cos 2x)`. -/
noncomputable def semilocalQuadraticFactor (e x : ℝ) : ℝ :=
  1 + 2 * e * Real.cos x + e ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * x))

theorem eulerFactor_denom_ge {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 6) (x : ℝ) :
    (25 : ℝ) / 36 ≤ 1 - 2 * e * Real.cos x + e ^ (2 : ℕ) := by
  have hc := Real.cos_le_one x
  have h56 : (5 : ℝ) / 6 ≤ 1 - e := by linarith
  have h2 : (0 : ℝ) ≤ 1 - e + 5 / 6 := by linarith
  nlinarith [mul_nonneg he0 (sub_nonneg.mpr hc), mul_nonneg (sub_nonneg.mpr h56) h2]

theorem abs_eulerFactor_le {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 6) (x : ℝ) :
    |semilocalEulerFactor e x| ≤ 3 / 2 := by
  unfold semilocalEulerFactor
  have hd := eulerFactor_denom_ge he0 he x
  rw [abs_of_pos (one_div_pos.mpr (by linarith)), div_le_iff₀ (by linarith)]
  linarith

theorem abs_quadraticFactor_le {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 6) (x : ℝ) :
    |semilocalQuadraticFactor e x| ≤ 3 / 2 := by
  unfold semilocalQuadraticFactor
  have hc := Real.abs_cos_le_one x
  have hc2 := Real.abs_cos_le_one (2 * x)
  rw [abs_le] at hc hc2 ⊢
  have h1 : -e ≤ e * Real.cos x := by nlinarith
  have h2 : e * Real.cos x ≤ e := by nlinarith
  have h3 : -(e ^ (2 : ℕ)) ≤ e ^ (2 : ℕ) * Real.cos (2 * x) := by nlinarith [sq_nonneg e]
  have h4 : e ^ (2 : ℕ) * Real.cos (2 * x) ≤ e ^ (2 : ℕ) := by nlinarith [sq_nonneg e]
  have he2 : e ^ (2 : ℕ) ≤ 1 / 36 := by nlinarith
  constructor <;> nlinarith

theorem abs_prod_eulerFactor_sub_prod_quadraticFactor_le {k : ℕ} (δ ε : Fin k → ℝ)
    (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6) (s : ℝ) :
    |∏ a, semilocalEulerFactor (ε a) (δ a * s) - ∏ a, semilocalQuadraticFactor (ε a) (δ a * s)| ≤
      (3 / 2) ^ k * ∑ a, 60 * ε a ^ (3 : ℕ) := by
  have h := abs_finset_prod_sub_prod_le Finset.univ (fun a => semilocalEulerFactor (ε a) (δ a * s))
    (fun a => semilocalQuadraticFactor (ε a) (δ a * s)) (C := 3 / 2) (by norm_num)
    (fun a _ => abs_eulerFactor_le (hε0 a) (hε a) _)
    (fun a _ => abs_quadraticFactor_le (hε0 a) (hε a) _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by positivity))
  exact abs_eulerFactor_sub_quadratic_le (hε0 a) (hε a) _

/-- The quadratic truncation of the product is the ray weight at `t = 1`. -/
theorem rayTruncation_eq {k : ℕ} (δ ε : Fin k → ℝ) (s : ℝ) :
    1 + ∑ a, 2 * ε a * Real.cos (δ a * s) +
      (∑ a, ε a ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * (δ a * s))) +
        (1 / 2) * ((∑ a, 2 * ε a * Real.cos (δ a * s)) ^ (2 : ℕ) -
          ∑ a, (2 * ε a * Real.cos (δ a * s)) ^ (2 : ℕ))) =
      1 + rayFirst δ ε s + raySecond δ ε s := by
  unfold raySecond
  unfold rayFirst
  have hterm : ∀ a, ε a ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * (δ a * s))) -
      (1 / 2) * (2 * ε a * Real.cos (δ a * s)) ^ (2 : ℕ) - ε a ^ (2 : ℕ) * Real.cos (2 * δ a * s) = 0 := by
    intro a
    have h1 := Real.cos_sq (δ a * s)
    have h2 : 2 * δ a * s = 2 * (δ a * s) := by ring
    rw [h2]
    linear_combination (-(2 * ε a ^ (2 : ℕ))) * h1
  have hsum : ∑ a, (ε a ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * (δ a * s))) -
      (1 / 2) * (2 * ε a * Real.cos (δ a * s)) ^ (2 : ℕ) - ε a ^ (2 : ℕ) * Real.cos (2 * δ a * s)) = 0 :=
    Finset.sum_eq_zero fun a _ => hterm a
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linear_combination hsum

variable {k : ℕ} (δ ε : Fin k → ℝ)

/-- The true finite-`S` Euler product weight `∏_a (1 − 2ε_a cos(δ_a s) + ε_a²)⁻¹`. -/
noncomputable def eulerProductWeight (s : ℝ) : ℝ := ∏ a, semilocalEulerFactor (ε a) (δ a * s)

/-- The explicit cubic weight remainder `(3/2)^k · 60 Σ ε_a³ + 12800 (Σ ε_a)³`. -/
noncomputable def weightRemainder : ℝ := (3 / 2) ^ k * ∑ a, 60 * ε a ^ (3 : ℕ) + 12800 * (∑ a, ε a) ^ (3 : ℕ)

theorem weightRemainder_nonneg (hε0 : ∀ a, 0 ≤ ε a) : 0 ≤ weightRemainder ε := by
  unfold weightRemainder
  have h1 : 0 ≤ ∑ a, 60 * ε a ^ (3 : ℕ) := Finset.sum_nonneg fun a _ => by have := hε0 a; positivity
  have h2 : 0 ≤ ∑ a, ε a := Finset.sum_nonneg fun a _ => hε0 a
  positivity

/-- **The weight-level cubic bound.** -/
theorem abs_eulerProductWeight_sub_rayWeight_le (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6)
    (hV : ∑ a, ε a ≤ 1 / 4) (s : ℝ) :
    |eulerProductWeight δ ε s - (1 + rayFirst δ ε s + raySecond δ ε s)| ≤ weightRemainder ε := by
  set x : Fin k → ℝ := fun a => 2 * ε a * Real.cos (δ a * s) with hx
  set y : Fin k → ℝ := fun a => ε a ^ (2 : ℕ) * (1 + 2 * Real.cos (2 * (δ a * s))) with hy
  have hxb : ∀ a, |x a| ≤ 2 * ε a := fun a => by
    simp only [hx]
    rw [abs_mul, abs_of_nonneg (by linarith [hε0 a] : (0 : ℝ) ≤ 2 * ε a)]
    exact mul_le_of_le_one_right (by linarith [hε0 a]) (Real.abs_cos_le_one _)
  have hyb : ∀ a, Real.sqrt |y a| ≤ 2 * ε a := fun a => by
    have h1 : |y a| ≤ (2 * ε a) ^ (2 : ℕ) := by
      simp only [hy]
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hc := Real.abs_cos_le_one (2 * (δ a * s))
      have h3 : |1 + 2 * Real.cos (2 * (δ a * s))| ≤ 3 := by
        rw [abs_le] at hc ⊢
        constructor <;> linarith
      nlinarith [sq_nonneg (ε a), hε0 a, abs_nonneg (1 + 2 * Real.cos (2 * (δ a * s)))]
    calc Real.sqrt |y a| ≤ Real.sqrt ((2 * ε a) ^ (2 : ℕ)) := Real.sqrt_le_sqrt h1
      _ = 2 * ε a := Real.sqrt_sq (by linarith [hε0 a])
  have hL : ∑ a, (|x a| + Real.sqrt |y a|) ≤ 4 * ∑ a, ε a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => by linarith [hxb a, hyb a]
  have hL1 : ∑ a, (|x a| + Real.sqrt |y a|) ≤ 1 := by linarith
  have hquad := abs_prod_sub_quadratic_le_cubic Finset.univ x y hL1
  have hprodQ : ∏ a, semilocalQuadraticFactor (ε a) (δ a * s) = ∏ a, (1 + x a + y a) :=
    Finset.prod_congr rfl fun a _ => by
      simp only [hx, hy]
      unfold semilocalQuadraticFactor
      ring
  have htrunc : 1 + ∑ a, x a + (∑ a, y a + (1 / 2) * ((∑ a, x a) ^ (2 : ℕ) - ∑ a, x a ^ (2 : ℕ))) =
      1 + rayFirst δ ε s + raySecond δ ε s := by
    simp only [hx, hy]
    exact rayTruncation_eq δ ε s
  have hE := abs_prod_eulerFactor_sub_prod_quadraticFactor_le δ ε hε0 hε s
  unfold eulerProductWeight weightRemainder
  have hsplit : ∏ a, semilocalEulerFactor (ε a) (δ a * s) - (1 + rayFirst δ ε s + raySecond δ ε s) =
      (∏ a, semilocalEulerFactor (ε a) (δ a * s) - ∏ a, semilocalQuadraticFactor (ε a) (δ a * s)) +
      (∏ a, (1 + x a + y a) -
        (1 + ∑ a, x a + (∑ a, y a + (1 / 2) * ((∑ a, x a) ^ (2 : ℕ) - ∑ a, x a ^ (2 : ℕ))))) := by
    rw [hprodQ, htrunc]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hL0 : 0 ≤ ∑ a, (|x a| + Real.sqrt |y a|) := Finset.sum_nonneg fun a _ => by positivity
  have hcube : (∑ a, (|x a| + Real.sqrt |y a|)) ^ (3 : ℕ) ≤ (4 * ∑ a, ε a) ^ (3 : ℕ) := pow_le_pow_left₀ hL0 hL 3
  calc _ ≤ (3 / 2) ^ k * ∑ a, 60 * ε a ^ (3 : ℕ) + 200 * (∑ a, (|x a| + Real.sqrt |y a|)) ^ (3 : ℕ) :=
        add_le_add hE hquad
    _ ≤ (3 / 2) ^ k * ∑ a, 60 * ε a ^ (3 : ℕ) + 200 * (4 * ∑ a, ε a) ^ (3 : ℕ) := by
        have := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 200)
        linarith
    _ = _ := by ring

theorem abs_eulerProductWeight_le (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6) (s : ℝ) :
    |eulerProductWeight δ ε s| ≤ (3 / 2) ^ k := by
  unfold eulerProductWeight
  rw [Finset.abs_prod]
  calc ∏ a, |semilocalEulerFactor (ε a) (δ a * s)| ≤ ∏ _a : Fin k, (3 / 2 : ℝ) :=
        Finset.prod_le_prod (fun a _ => abs_nonneg _)
          (fun a _ => abs_eulerFactor_le (hε0 a) (hε a) _)
    _ = (3 / 2) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem continuous_eulerProductWeight (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6) :
    Continuous (eulerProductWeight δ ε) := by
  unfold eulerProductWeight
  refine continuous_finset_prod _ fun a _ => ?_
  unfold semilocalEulerFactor
  refine Continuous.div continuous_const (by fun_prop) fun s => ?_
  have := eulerFactor_denom_ge (hε0 a) (hε a) (δ a * s)
  linarith

theorem continuous_rayWeight : Continuous (fun s => 1 + rayFirst δ ε s + raySecond δ ε s) := by
  unfold raySecond
  unfold rayFirst
  fun_prop

theorem abs_rayFirst_le (hε0 : ∀ a, 0 ≤ ε a) (s : ℝ) : |rayFirst δ ε s| ≤ 2 * ∑ a, ε a := by
  unfold rayFirst
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [abs_mul, abs_of_nonneg (by linarith [hε0 a] : (0 : ℝ) ≤ 2 * ε a)]
  exact mul_le_of_le_one_right (by linarith [hε0 a]) (Real.abs_cos_le_one _)

theorem abs_raySecond_le (hε0 : ∀ a, 0 ≤ ε a) (s : ℝ) :
    |raySecond δ ε s| ≤ 3 * (∑ a, ε a) ^ (2 : ℕ) := by
  unfold raySecond
  have h1 := abs_rayFirst_le δ ε hε0 s
  have h2 : |∑ a, ε a ^ (2 : ℕ) * Real.cos (2 * δ a * s)| ≤ ∑ a, ε a ^ (2 : ℕ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)
  have h3 : ∑ a, ε a ^ (2 : ℕ) ≤ (∑ a, ε a) ^ (2 : ℕ) := Finset.sum_sq_le_sq_sum_of_nonneg fun a _ => hε0 a
  have h4 : rayFirst δ ε s ^ (2 : ℕ) ≤ (2 * ∑ a, ε a) ^ (2 : ℕ) := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc |(1 / 2) * rayFirst δ ε s ^ (2 : ℕ) + ∑ a, ε a ^ (2 : ℕ) * Real.cos (2 * δ a * s)|
      ≤ (1 / 2) * rayFirst δ ε s ^ (2 : ℕ) + ∑ a, ε a ^ (2 : ℕ) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg (sq_nonneg _)]
        linarith
    _ ≤ (1 / 2) * (2 * ∑ a, ε a) ^ (2 : ℕ) + (∑ a, ε a) ^ (2 : ℕ) := by linarith
    _ = 3 * (∑ a, ε a) ^ (2 : ℕ) := by ring

theorem abs_rayWeight_le (hε0 : ∀ a, 0 ≤ ε a) (s : ℝ) :
    |1 + rayFirst δ ε s + raySecond δ ε s| ≤ 1 + 2 * ∑ a, ε a + 3 * (∑ a, ε a) ^ (2 : ℕ) := by
  have h1 := abs_rayFirst_le δ ε hε0 s
  have h2 := abs_raySecond_le δ ε hε0 s
  calc |1 + rayFirst δ ε s + raySecond δ ε s| ≤ |1 + rayFirst δ ε s| + |raySecond δ ε s| :=
        abs_add_le _ _
    _ ≤ (|(1 : ℝ)| + |rayFirst δ ε s|) + |raySecond δ ε s| := by
        have := abs_add_le (1 : ℝ) (rayFirst δ ε s)
        linarith
    _ ≤ _ := by rw [abs_one]; linarith

/-! ## Gram entries of bounded multipliers -/

theorem integrable_eval_mul_eval_mul_bounded (i j : ℕ) {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ s, |f s| ≤ C) :
    Integrable (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * f s) semilocalArchimedeanGammaMeasure := by
  have hP := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial j)
  have h := hP.bdd_mul hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hC s)
  exact h.congr (Filter.Eventually.of_forall fun s => by simp only; ring)

theorem integral_abs_eval_mul_eval_le_one (i j : ℕ) :
    ∫ s : ℝ, |(semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s| ∂semilocalArchimedeanGammaMeasure ≤ 1 := by
  have hi := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial i)
  have hj := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial j) (semilocalArchimedeanJacobiPolynomial j)
  have hij := integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial j)
  have hle : (fun s : ℝ => |(semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s|) ≤
      fun s => (1 / 2) * ((semilocalArchimedeanJacobiPolynomial i).eval s *
        (semilocalArchimedeanJacobiPolynomial i).eval s +
        (semilocalArchimedeanJacobiPolynomial j).eval s *
        (semilocalArchimedeanJacobiPolynomial j).eval s) := fun s => by
    simp only
    rw [abs_mul]
    nlinarith [sq_nonneg (|(semilocalArchimedeanJacobiPolynomial i).eval s| -
      |(semilocalArchimedeanJacobiPolynomial j).eval s|),
      sq_abs ((semilocalArchimedeanJacobiPolynomial i).eval s),
      sq_abs ((semilocalArchimedeanJacobiPolynomial j).eval s)]
  calc ∫ s : ℝ, |(semilocalArchimedeanJacobiPolynomial i).eval s *
        (semilocalArchimedeanJacobiPolynomial j).eval s| ∂semilocalArchimedeanGammaMeasure
      ≤ ∫ s : ℝ, (1 / 2) * ((semilocalArchimedeanJacobiPolynomial i).eval s *
        (semilocalArchimedeanJacobiPolynomial i).eval s +
        (semilocalArchimedeanJacobiPolynomial j).eval s *
        (semilocalArchimedeanJacobiPolynomial j).eval s) ∂semilocalArchimedeanGammaMeasure :=
        integral_mono hij.abs ((hi.add hj).const_mul _) hle
    _ = (1 / 2) * (semilocalArchimedeanJacobiGram i i + semilocalArchimedeanJacobiGram j j) := by
        rw [integral_const_mul, integral_add hi hj]
        rfl
    _ = 1 := by
        rw [semilocalArchimedeanJacobiGram_eq_ite, semilocalArchimedeanJacobiGram_eq_ite]
        norm_num

theorem abs_integral_eval_mul_eval_mul_le (i j : ℕ) {f : ℝ → ℝ} {C : ℝ} (hC : ∀ s, |f s| ≤ C) :
    |∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * f s ∂semilocalArchimedeanGammaMeasure| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hg : Integrable (fun s : ℝ => C * |(semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s|) semilocalArchimedeanGammaMeasure :=
    (integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure _ _).abs.const_mul C
  have hb : ∀ᵐ s ∂semilocalArchimedeanGammaMeasure,
      ‖(semilocalArchimedeanJacobiPolynomial i).eval s *
        (semilocalArchimedeanJacobiPolynomial j).eval s * f s‖ ≤
      C * |(semilocalArchimedeanJacobiPolynomial i).eval s *
        (semilocalArchimedeanJacobiPolynomial j).eval s| :=
    Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC s) (abs_nonneg _)
  have h := norm_integral_le_of_norm_le hg hb
  rw [Real.norm_eq_abs, integral_const_mul] at h
  calc _ ≤ _ := h
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (integral_abs_eval_mul_eval_le_one i j) hC0
    _ = C := mul_one C

theorem abs_cosineModeTangent_le_two (c : ℝ) (n : ℕ) (i j : Fin (n + 1)) :
    |cosineModeTangent c n i j| ≤ 2 := by
  show |2 * ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (c * s)
    ∂semilocalArchimedeanGammaMeasure| ≤ 2
  rw [abs_mul, abs_two]
  have := abs_integral_eval_mul_eval_mul_le (i : ℕ) j (f := fun s => Real.cos (c * s)) (C := 1)
    (fun s => Real.abs_cos_le_one _)
  linarith

theorem entryNorm_cosineModeTangent_le (c : ℝ) (n : ℕ) :
    entryNorm (cosineModeTangent c n) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) * 2 := by
  have := entryNorm_le_of_abs_apply_le (fun i j => abs_cosineModeTangent_le_two c n i j)
  rwa [Fintype.card_fin, Nat.cast_succ] at this

theorem entryNorm_rayM₁_le (n : ℕ) :
    entryNorm (rayM₁ δ ε n) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) * 2 * ∑ a, |ε a| := by
  unfold rayM₁
  refine (entryNorm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [entryNorm_smul]
  calc |ε a| * entryNorm (cosineModeTangent (δ a) n) ≤ |ε a| * (((n : ℝ) + 1) ^ (2 : ℕ) * 2) :=
        mul_le_mul_of_nonneg_left (entryNorm_cosineModeTangent_le _ _) (abs_nonneg _)
    _ = _ := by ring

theorem entryNorm_rayM₂_le (n : ℕ) :
    entryNorm (rayM₂ δ ε n) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) * (2 * (∑ a, |ε a|) ^ (2 : ℕ) + ∑ a, ε a ^ (2 : ℕ)) := by
  unfold rayM₂
  refine (entryNorm_add_le _ _).trans ?_
  rw [entryNorm_smul, entryNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 : entryNorm (∑ a, ∑ b, (ε a * ε b) •
      (cosineModeTangent (δ a + δ b) n + cosineModeTangent (δ a - δ b) n)) ≤
      ∑ a, ∑ b, |ε a * ε b| * (2 * (((n : ℝ) + 1) ^ (2 : ℕ) * 2)) := by
    refine (entryNorm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
      (entryNorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
    rw [entryNorm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (entryNorm_add_le _ _).trans ?_
    linarith [entryNorm_cosineModeTangent_le (δ a + δ b) n,
      entryNorm_cosineModeTangent_le (δ a - δ b) n]
  have h2 : entryNorm (∑ a, (ε a ^ (2 : ℕ)) • cosineModeTangent (2 * δ a) n) ≤
      ∑ a, ε a ^ (2 : ℕ) * (((n : ℝ) + 1) ^ (2 : ℕ) * 2) := by
    refine (entryNorm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [entryNorm_smul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (entryNorm_cosineModeTangent_le _ _) (sq_nonneg _)
  have e1 : ∑ a, ∑ b, |ε a * ε b| * (2 * (((n : ℝ) + 1) ^ (2 : ℕ) * 2)) =
      ((n : ℝ) + 1) ^ (2 : ℕ) * (4 * (∑ a, |ε a|) ^ (2 : ℕ)) := by
    rw [sq (∑ a, |ε a|), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [abs_mul]
    ring
  have e2 : ∑ a, ε a ^ (2 : ℕ) * (((n : ℝ) + 1) ^ (2 : ℕ) * 2) = ((n : ℝ) + 1) ^ (2 : ℕ) * (2 * ∑ a, ε a ^ (2 : ℕ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e1] at h1
  rw [e2] at h2
  nlinarith [h1, h2]

/-! ## The Gram matrix of the true Euler product -/

/-- Gram matrix of the true Euler-product weight in the orthonormal Jacobi basis. -/
noncomputable def eulerProductGram (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s * eulerProductWeight δ ε s
    ∂semilocalArchimedeanGammaMeasure

theorem rayGram_one_apply (n : ℕ) (i j : Fin (n + 1)) :
    rayGram δ ε 1 n i j = ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * (1 + rayFirst δ ε s + raySecond δ ε s)
      ∂semilocalArchimedeanGammaMeasure := by
  unfold rayGram
  simp only [one_mul, one_pow]

/-- **Entrywise third-order Gram discrepancy.** -/
theorem abs_eulerProductGram_sub_rayGram_le (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6)
    (hV : ∑ a, ε a ≤ 1 / 4) (n : ℕ) (i j : Fin (n + 1)) :
    |(eulerProductGram δ ε n - rayGram δ ε 1 n) i j| ≤ weightRemainder ε := by
  rw [Matrix.sub_apply, rayGram_one_apply]
  have hW := integrable_eval_mul_eval_mul_bounded (i : ℕ) j
    (continuous_eulerProductWeight δ ε hε0 hε) (abs_eulerProductWeight_le δ ε hε0 hε)
  have hW₂ := integrable_eval_mul_eval_mul_bounded (i : ℕ) j (continuous_rayWeight δ ε)
    (abs_rayWeight_le δ ε hε0)
  show |(∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * eulerProductWeight δ ε s
      ∂semilocalArchimedeanGammaMeasure) - _| ≤ _
  rw [← integral_sub hW hW₂]
  have hfun : (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * eulerProductWeight δ ε s -
      (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * (1 + rayFirst δ ε s + raySecond δ ε s)) =
      fun s => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s *
      (eulerProductWeight δ ε s - (1 + rayFirst δ ε s + raySecond δ ε s)) := by
    funext s
    ring
  rw [hfun]
  exact abs_integral_eval_mul_eval_mul_le (i : ℕ) j
    (fun s => abs_eulerProductWeight_sub_rayWeight_le δ ε hε0 hε hV s)

/-- The size parameter `V = Σ ε_a`. -/
noncomputable def sizeV : ℝ := ∑ a, ε a

/-- The entry-norm size `(n+1)² (2V + 3V² + ρ)`. -/
noncomputable def entrySize (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (2 : ℕ) * (2 * sizeV ε + 3 * sizeV ε ^ (2 : ℕ) + weightRemainder ε)

/-- The second-order log-determinant jet `tr M₁ + tr M₂ − ½ tr M₁²`. -/
noncomputable def secondOrderLogDetJet (n : ℕ) : ℝ :=
  Matrix.trace (rayM₁ δ ε n) + Matrix.trace (rayM₂ δ ε n) -
    (1 / 2) * Matrix.trace (rayM₁ δ ε n * rayM₁ δ ε n)

/-- The jet in terms of the corpus first-order, bilinear and harmonic jets. -/
theorem secondOrderLogDetJet_eq (n : ℕ) :
    secondOrderLogDetJet δ ε n =
      ∑ a, ε a * cosineModeDeterminantJet (δ a) n +
        (1 / 2) * (∑ a, ∑ b, (ε a * ε b) * bilinearDeterminantJet (δ a) (δ b) n +
          ∑ a, ε a ^ (2 : ℕ) * cosineModeDeterminantJet (2 * δ a) n) := by
  unfold secondOrderLogDetJet
  rw [trace_rayM₁, ← rayLogJet_eq]
  unfold quadLogJet
  ring

/-- The explicit third-order remainder bound. -/
noncomputable def logDetRemainderBound (n : ℕ) : ℝ :=
  remainderConst ((n : ℝ) + 1) (entrySize ε n) + ((n : ℝ) + 1) ^ (2 : ℕ) * weightRemainder ε +
    (1 / 2) * (2 * (((n : ℝ) + 1) ^ (2 : ℕ) * (2 * sizeV ε)) *
      (((n : ℝ) + 1) ^ (2 : ℕ) * (3 * sizeV ε ^ (2 : ℕ) + weightRemainder ε)) +
      (((n : ℝ) + 1) ^ (2 : ℕ) * (3 * sizeV ε ^ (2 : ℕ) + weightRemainder ε)) ^ (2 : ℕ))

theorem eulerProductGram_eq_one_add (n : ℕ) :
    eulerProductGram δ ε n =
      1 + (rayM₁ δ ε n + rayM₂ δ ε n + (eulerProductGram δ ε n - rayGram δ ε 1 n)) := by
  have h := rayGram_eq δ ε 1 n
  unfold quadPath at h
  rw [one_smul, one_pow, one_smul] at h
  rw [h]
  abel

theorem entryNorm_discrepancy_le (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6)
    (hV : ∑ a, ε a ≤ 1 / 4) (n : ℕ) :
    entryNorm (eulerProductGram δ ε n - rayGram δ ε 1 n) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) * weightRemainder ε := by
  have := entryNorm_le_of_abs_apply_le
    (fun i j => abs_eulerProductGram_sub_rayGram_le δ ε hε0 hε hV n i j)
  rwa [Fintype.card_fin, Nat.cast_succ] at this

theorem entryNorm_rayM₁_le' (hε0 : ∀ a, 0 ≤ ε a) (n : ℕ) :
    entryNorm (rayM₁ δ ε n) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) * (2 * sizeV ε) := by
  have h := entryNorm_rayM₁_le δ ε n
  have habs : ∑ a, |ε a| = sizeV ε := Finset.sum_congr rfl fun a _ => abs_of_nonneg (hε0 a)
  rw [habs] at h
  linarith

theorem entryNorm_rayM₂_le' (hε0 : ∀ a, 0 ≤ ε a) (n : ℕ) :
    entryNorm (rayM₂ δ ε n) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) * (3 * sizeV ε ^ (2 : ℕ)) := by
  have h := entryNorm_rayM₂_le δ ε n
  have habs : ∑ a, |ε a| = sizeV ε := Finset.sum_congr rfl fun a _ => abs_of_nonneg (hε0 a)
  have hsq : ∑ a, ε a ^ (2 : ℕ) ≤ sizeV ε ^ (2 : ℕ) := Finset.sum_sq_le_sq_sum_of_nonneg fun a _ => hε0 a
  rw [habs] at h
  have := mul_le_mul_of_nonneg_left hsq (sq_nonneg ((n : ℝ) + 1))
  nlinarith

theorem entryNorm_eulerProductGram_sub_one_le (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6)
    (hV : ∑ a, ε a ≤ 1 / 4) (n : ℕ) :
    entryNorm (rayM₁ δ ε n + rayM₂ δ ε n + (eulerProductGram δ ε n - rayGram δ ε 1 n)) ≤
      entrySize ε n := by
  have h1 := entryNorm_rayM₁_le' δ ε hε0 n
  have h2 := entryNorm_rayM₂_le' δ ε hε0 n
  have h3 := entryNorm_discrepancy_le δ ε hε0 hε hV n
  refine ((entryNorm_add_le _ _).trans (add_le_add (entryNorm_add_le _ _) le_rfl)).trans ?_
  unfold entrySize
  linarith

theorem remainderConst_mono {d η₁ η₂ : ℝ} (hd : 0 ≤ d) (h0 : 0 ≤ η₁) (h : η₁ ≤ η₂) (h2 : η₂ < 1) :
    remainderConst d η₁ ≤ remainderConst d η₂ := by
  unfold remainderConst
  have hden : 0 < (1 - η₂) ^ (2 : ℕ) := pow_pos (by linarith) 2
  have hden2 : (1 - η₂) ^ (2 : ℕ) ≤ (1 - η₁) ^ (2 : ℕ) := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hη2 : 0 ≤ η₂ := h0.trans h
  have hdd : 0 ≤ d * (d + 1) := mul_nonneg hd (by linarith)
  have hnum : d * (d + 1) * η₁ ^ (3 : ℕ) ≤ d * (d + 1) * η₂ ^ (3 : ℕ) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 3) hdd
  exact div_le_div₀ (mul_nonneg hdd (pow_nonneg hη2 3)) hnum hden hden2

/-- **Positivity of the true Gram determinant.** -/
theorem eulerProductGram_det_pos (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6)
    (hV : ∑ a, ε a ≤ 1 / 4) (n : ℕ) (hsize : entrySize ε n < 1) :
    0 < (eulerProductGram δ ε n).det := by
  rw [eulerProductGram_eq_one_add]
  exact det_one_add_pos (lt_of_le_of_lt (entryNorm_eulerProductGram_sub_one_le δ ε hε0 hε hV n) hsize)

/-- **The determinant-level Taylor remainder for the true Euler product.**
`|log det G_n − (tr M₁ + tr M₂ − ½ tr M₁²)| ≤ logDetRemainderBound ε n`, an explicit third-order
quantity in `ε`. -/
theorem abs_log_det_eulerProductGram_sub_jet_le (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6)
    (hV : ∑ a, ε a ≤ 1 / 4) (n : ℕ) (hsize : entrySize ε n < 1) :
    |Real.log (eulerProductGram δ ε n).det - secondOrderLogDetJet δ ε n| ≤
      logDetRemainderBound ε n := by
  have hN := entryNorm_eulerProductGram_sub_one_le δ ε hε0 hε hV n
  have hlt : entryNorm (rayM₁ δ ε n + rayM₂ δ ε n + (eulerProductGram δ ε n - rayGram δ ε 1 n)) < 1 :=
    lt_of_le_of_lt hN hsize
  have key := abs_log_det_sub_secondOrderJet_le (rayM₁ δ ε n) (rayM₂ δ ε n)
    (eulerProductGram δ ε n - rayGram δ ε 1 n) hlt
  rw [← eulerProductGram_eq_one_add, Fintype.card_fin, Nat.cast_succ] at key
  unfold secondOrderLogDetJet logDetRemainderBound
  refine key.trans ?_
  have hV0 : 0 ≤ sizeV ε := Finset.sum_nonneg fun a _ => hε0 a
  have hρ0 : 0 ≤ weightRemainder ε := weightRemainder_nonneg ε hε0
  have hm1 := entryNorm_rayM₁_le' δ ε hε0 n
  have hm2 := entryNorm_rayM₂_le' δ ε hε0 n
  have hE := entryNorm_discrepancy_le δ ε hε0 hε hV n
  have hK : entryNorm (rayM₂ δ ε n + (eulerProductGram δ ε n - rayGram δ ε 1 n)) ≤
      ((n : ℝ) + 1) ^ (2 : ℕ) * (3 * sizeV ε ^ (2 : ℕ) + weightRemainder ε) := by
    refine (entryNorm_add_le _ _).trans ?_
    linarith
  have hrem : remainderConst ((n : ℝ) + 1) (entryNorm (rayM₁ δ ε n + rayM₂ δ ε n +
      (eulerProductGram δ ε n - rayGram δ ε 1 n))) ≤ remainderConst ((n : ℝ) + 1) (entrySize ε n) :=
    remainderConst_mono (by positivity) (entryNorm_nonneg _) hN hsize
  have hKnn := entryNorm_nonneg (rayM₂ δ ε n + (eulerProductGram δ ε n - rayGram δ ε 1 n))
  have hm1nn := entryNorm_nonneg (rayM₁ δ ε n)
  have hprod : entryNorm (rayM₁ δ ε n) *
      entryNorm (rayM₂ δ ε n + (eulerProductGram δ ε n - rayGram δ ε 1 n)) ≤
      (((n : ℝ) + 1) ^ (2 : ℕ) * (2 * sizeV ε)) *
        (((n : ℝ) + 1) ^ (2 : ℕ) * (3 * sizeV ε ^ (2 : ℕ) + weightRemainder ε)) :=
    mul_le_mul hm1 hK hKnn (by positivity)
  have hsq : entryNorm (rayM₂ δ ε n + (eulerProductGram δ ε n - rayGram δ ε 1 n)) ^ (2 : ℕ) ≤
      (((n : ℝ) + 1) ^ (2 : ℕ) * (3 * sizeV ε ^ (2 : ℕ) + weightRemainder ε)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hKnn hK 2
  linarith

/-! ## The Hankel quotient: the squared Jacobi radius of the true Euler product -/

/-- The squared Jacobi radius `a²_{n+1}` of the Euler-product measure through the Hankel quotient
`r²_{n+1} · det G_n det G_{n+2} / det G_{n+1}²`. -/
noncomputable def eulerProductSquaredRadius (n : ℕ) : ℝ :=
  archimedeanSquaredRadius (n + 1) *
    ((eulerProductGram δ ε n).det * (eulerProductGram δ ε (n + 2)).det /
      (eulerProductGram δ ε (n + 1)).det ^ (2 : ℕ))

theorem entrySize_mono (hε0 : ∀ a, 0 ≤ ε a) {m n : ℕ} (h : m ≤ n) :
    entrySize ε m ≤ entrySize ε n := by
  unfold entrySize
  have hV0 : 0 ≤ sizeV ε := Finset.sum_nonneg fun a _ => hε0 a
  have hρ0 : 0 ≤ weightRemainder ε := weightRemainder_nonneg ε hε0
  have hmn : ((m : ℝ) + 1) ^ (2 : ℕ) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ h) 2
  exact mul_le_mul_of_nonneg_right hmn (by positivity)

theorem log_eulerProductSquaredRadius (hε0 : ∀ a, 0 ≤ ε a) (hε : ∀ a, ε a ≤ 1 / 6)
    (hV : ∑ a, ε a ≤ 1 / 4) (n : ℕ) (hsize : entrySize ε (n + 2) < 1) :
    Real.log (eulerProductSquaredRadius δ ε n / archimedeanSquaredRadius (n + 1)) =
      Real.log (eulerProductGram δ ε n).det + Real.log (eulerProductGram δ ε (n + 2)).det -
        2 * Real.log (eulerProductGram δ ε (n + 1)).det := by
  have h0 := eulerProductGram_det_pos δ ε hε0 hε hV n
    (lt_of_le_of_lt (entrySize_mono ε hε0 (by omega)) hsize)
  have h1 := eulerProductGram_det_pos δ ε hε0 hε hV (n + 1)
    (lt_of_le_of_lt (entrySize_mono ε hε0 (by omega)) hsize)
  have h2 := eulerProductGram_det_pos δ ε hε0 hε hV (n + 2) hsize
  unfold eulerProductSquaredRadius
  rw [mul_div_cancel_left₀ _ (archimedeanSquaredRadius_pos _).ne',
    Real.log_div (by positivity) (by positivity), Real.log_mul h0.ne' h2.ne', Real.log_pow]
  push_cast
  ring

/-- **The second-order theory with remainder at the radius level.**
`log(a²_{n+1}/r²_{n+1})` equals the second difference of the second-order jet up to the sum of the
three explicit remainders. -/
theorem abs_log_eulerProductSquaredRadius_sub_jet_le (hε0 : ∀ a, 0 ≤ ε a)
    (hε : ∀ a, ε a ≤ 1 / 6) (hV : ∑ a, ε a ≤ 1 / 4) (n : ℕ) (hsize : entrySize ε (n + 2) < 1) :
    |Real.log (eulerProductSquaredRadius δ ε n / archimedeanSquaredRadius (n + 1)) -
        (secondOrderLogDetJet δ ε n + secondOrderLogDetJet δ ε (n + 2) -
          2 * secondOrderLogDetJet δ ε (n + 1))| ≤
      logDetRemainderBound ε n + logDetRemainderBound ε (n + 2) +
        2 * logDetRemainderBound ε (n + 1) := by
  rw [log_eulerProductSquaredRadius δ ε hε0 hε hV n hsize]
  have b0 := abs_log_det_eulerProductGram_sub_jet_le δ ε hε0 hε hV n
    (lt_of_le_of_lt (entrySize_mono ε hε0 (by omega)) hsize)
  have b1 := abs_log_det_eulerProductGram_sub_jet_le δ ε hε0 hε hV (n + 1)
    (lt_of_le_of_lt (entrySize_mono ε hε0 (by omega)) hsize)
  have b2 := abs_log_det_eulerProductGram_sub_jet_le δ ε hε0 hε hV (n + 2) hsize
  set L0 := Real.log (eulerProductGram δ ε n).det
  set L1 := Real.log (eulerProductGram δ ε (n + 1)).det
  set L2 := Real.log (eulerProductGram δ ε (n + 2)).det
  set j0 := secondOrderLogDetJet δ ε n
  set j1 := secondOrderLogDetJet δ ε (n + 1)
  set j2 := secondOrderLogDetJet δ ε (n + 2)
  have hid : L0 + L2 - 2 * L1 - (j0 + j2 - 2 * j1) = (L0 - j0) + (L2 - j2) - 2 * (L1 - j1) := by ring
  rw [hid]
  calc |(L0 - j0) + (L2 - j2) - 2 * (L1 - j1)| ≤ |L0 - j0| + |L2 - j2| + 2 * |L1 - j1| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_two]
        linarith [abs_add_le (L0 - j0) (L2 - j2)]
    _ ≤ _ := by linarith

end RHTower.CosineModeResponse
