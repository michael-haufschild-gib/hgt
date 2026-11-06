import GaloisForLFunctions.VerifiedHeightRungs.ZeroGapsFromVerifiedZeros
import Mathlib.LinearAlgebra.Lagrange

/-!
# Separated nodes control a transform on a long interval

Let `f` be supported in `[−a, a]` and let `Φ` be its transform. Take `σ = 48⁻⁴/(9a)` and nodes
`v_j ∈ [(n+1)σ + 2jσ, (n+1)σ + (2j+1)σ]`, `0 ≤ j ≤ n`. Then for `|x| ≤ (n+1)σ`

  `|Φ(x)|² ≤ 2 (n+1) 48^{2n} Σ_j |Φ(v_j)|² + 2 ‖f‖₁² 48^{−4n}` (`norm_sq_paperFT_le_of_nodes`).

`Φ` is within `2‖f‖₁ 48^{−4(n+1)}` of its Taylor polynomial of degree `n` on `|y| ≤ 3(n+1)σ`, and that polynomial is
recovered from the nodes by Lagrange interpolation: the separation `|v_i − v_j| ≥ σ|i − j|` makes every Lagrange
factor at most `48^n`, because the node differences carry `j!(n−j)!`.
-/

open Polynomial Finset
open scoped Nat

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23

noncomputable section

/-- `Π_{i ≠ j} |i − j| = j! (n − j)!`. -/
theorem prod_abs_sub_nat {n j : ℕ} (hj : j ≤ n) :
    ∏ i ∈ (range (n + 1)).erase j, |(i : ℝ) - j| = (j ! : ℝ) * ((n - j)! : ℝ) := by
  have hsplit : (range (n + 1)).erase j = range j ∪ Ico (j + 1) (n + 1) := by
    ext i
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range j) (Ico (j + 1) (n + 1)) := by
    rw [disjoint_left]
    intro i hi hi'
    simp only [mem_range, mem_Ico] at hi hi'
    omega
  rw [hsplit, prod_union hdisj]
  congr 1
  · have h1 : ∏ i ∈ range j, |(i : ℝ) - j| = ∏ i ∈ range j, ((j - 1 - i : ℕ) + 1 : ℝ) := by
      refine prod_congr rfl fun i hi => ?_
      have hi' := mem_range.1 hi
      have e : ((j - 1 - i : ℕ) : ℝ) + 1 = (j : ℝ) - i := by
        have : j - 1 - i + 1 = j - i := by omega
        have h2 : ((j - 1 - i + 1 : ℕ) : ℝ) = ((j - i : ℕ) : ℝ) := by rw [this]
        push_cast at h2
        rw [h2, Nat.cast_sub hi'.le]
      rw [e, abs_sub_comm, abs_of_nonneg]
      have : (i : ℝ) ≤ j := by exact_mod_cast hi'.le
      linarith only [this]
    rw [h1, prod_range_reflect (fun i => ((i : ℕ) : ℝ) + 1) j]
    have := prod_range_add_one_eq_factorial j
    exact_mod_cast this
  · rw [prod_Ico_eq_prod_range]
    have hlen : n + 1 - (j + 1) = n - j := by omega
    rw [hlen]
    have h1 : ∏ i ∈ range (n - j), |((j + 1 + i : ℕ) : ℝ) - j| = ∏ i ∈ range (n - j), ((i : ℝ) + 1) := by
      refine prod_congr rfl fun i _ => ?_
      push_cast
      rw [show (j : ℝ) + 1 + i - j = i + 1 by ring, abs_of_nonneg (by positivity)]
    rw [h1]
    have := prod_range_add_one_eq_factorial (n - j)
    exact_mod_cast this

/-- `(4(n+1))^n / (j!(n−j)!) ≤ 48^n`. -/
theorem lagrange_constant_le {n j : ℕ} (hj : j ≤ n) :
    (4 * ((n : ℝ) + 1)) ^ n / ((j ! : ℝ) * ((n - j)! : ℝ)) ≤ 48 ^ n := by
  have hf : (0 : ℝ) < (j ! : ℝ) * ((n - j)! : ℝ) := by positivity
  rw [div_le_iff₀ hf]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hj0 : j = 0 := by omega
    subst hj0
    norm_num
  have hchoose : (n ! : ℝ) ≤ 2 ^ n * ((j ! : ℝ) * ((n - j)! : ℝ)) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hj
    have h2 := Nat.choose_le_two_pow n j
    have h3 : (n ! : ℝ) = (n.choose j : ℝ) * ((j ! : ℝ) * ((n - j)! : ℝ)) := by
      rw [← h1]
      push_cast
      ring
    rw [h3]
    have h4 : (n.choose j : ℝ) ≤ 2 ^ n := by exact_mod_cast h2
    exact mul_le_mul_of_nonneg_right h4 hf.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : (n : ℝ) ^ n / (n ! : ℝ) ≤ Real.exp n := Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at hexp
  have he : Real.exp (n : ℝ) ≤ 3 ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith only [Real.exp_one_lt_d9]) n
  have hbase : (4 * ((n : ℝ) + 1)) ^ n ≤ (8 * (n : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hn1]) n
  calc
    (4 * ((n : ℝ) + 1)) ^ n ≤ 8 ^ n * (n : ℝ) ^ n := by rw [← mul_pow]; exact hbase
    _ ≤ 8 ^ n * (3 ^ n * (n ! : ℝ)) :=
      mul_le_mul_of_nonneg_left (hexp.trans (mul_le_mul_of_nonneg_right he (by positivity))) (by positivity)
    _ ≤ 8 ^ n * (3 ^ n * (2 ^ n * ((j ! : ℝ) * ((n - j)! : ℝ)))) := by gcongr
    _ = (48 : ℝ) ^ n * ((j ! : ℝ) * ((n - j)! : ℝ)) := by
      rw [show (48 : ℝ) = 8 * (3 * 2) by norm_num, mul_pow, mul_pow]
      ring

/-- **Lagrange on separated nodes.** A polynomial of degree at most `n` is bounded at `x` by its values at nodes with
`|v_i − v_j| ≥ σ|i − j|`, all within `4(n+1)σ` of `x`, with constant `48^n`. -/
theorem norm_eval_le_of_nodes {n : ℕ} (P : ℂ[X]) (hP : P.natDegree ≤ n) {σ : ℝ} (hσ : 0 < σ) (v : ℕ → ℝ)
    (hsep : ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1), σ * |(i : ℝ) - j| ≤ |v i - v j|) {x : ℂ}
    (hx : ∀ i ∈ range (n + 1), ‖x - (v i : ℂ)‖ ≤ 4 * ((n : ℝ) + 1) * σ) :
    ‖P.eval x‖ ≤ 48 ^ n * ∑ j ∈ range (n + 1), ‖P.eval (v j : ℂ)‖ := by
  classical
  let w : ℕ → ℂ := fun i => (v i : ℂ)
  have hpos : ∀ {i j : ℕ}, i ≠ j → 0 < |(i : ℝ) - j| := fun {i j} h =>
    abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast h))
  have hinj : Set.InjOn w (range (n + 1) : Finset ℕ) := by
    intro i hi j hj hij
    by_contra hne
    have h1 := hsep i hi j hj
    have hvij : v i = v j := Complex.ofReal_injective hij
    rw [hvij, sub_self, abs_zero] at h1
    have := mul_pos hσ (hpos hne)
    linarith only [h1, this]
  have hdeg : P.degree < ((range (n + 1)).card : ℕ) := by
    rw [card_range]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP)
  have hinterp := Lagrange.eq_interpolate hinj hdeg
  have hbasis : ∀ j ∈ range (n + 1), ‖(Lagrange.basis (range (n + 1)) w j).eval x‖ ≤ 48 ^ n := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj)
    rw [Lagrange.basis, eval_prod, norm_prod]
    have hfac : ∀ i ∈ (range (n + 1)).erase j,
        ‖(Lagrange.basisDivisor (w j) (w i)).eval x‖ ≤ 4 * ((n : ℝ) + 1) / |(i : ℝ) - j| := by
      intro i hi
      have his : i ∈ range (n + 1) := mem_of_mem_erase hi
      have hij : i ≠ j := ne_of_mem_erase hi
      have hd := hpos hij
      rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, norm_mul, norm_inv]
      have hsub : w j - w i = ((v j - v i : ℝ) : ℂ) := by simp [w]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, inv_mul_eq_div, abs_sub_comm]
      have hlow := hsep i his j hj
      have hup := hx i his
      have hpos2 : 0 < σ * |(i : ℝ) - j| := mul_pos hσ hd
      refine (div_le_div₀ (by positivity) hup hpos2 hlow).trans (le_of_eq ?_)
      field_simp
    calc
      ∏ i ∈ (range (n + 1)).erase j, ‖(Lagrange.basisDivisor (w j) (w i)).eval x‖
          ≤ ∏ i ∈ (range (n + 1)).erase j, (4 * ((n : ℝ) + 1) / |(i : ℝ) - j|) :=
        prod_le_prod (fun _ _ => norm_nonneg _) hfac
      _ = (4 * ((n : ℝ) + 1)) ^ n / ((j ! : ℝ) * ((n - j)! : ℝ)) := by
        rw [prod_div_distrib, prod_const, card_erase_of_mem hj, card_range, prod_abs_sub_nat hjn]
        simp
      _ ≤ _ := lagrange_constant_le hjn
  conv_lhs => rw [hinterp]
  rw [Lagrange.interpolate_apply, eval_finsetSum, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
  rw [eval_mul, eval_C, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hbasis j hj) (norm_nonneg _)

/-- The Taylor polynomial of the transform at the origin. -/
def taylorPoly (f : ℝ → ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ range (n + 1), C (∫ u : ℝ, f u * ((Complex.I * u) ^ k / (k ! : ℂ))) * X ^ k

theorem natDegree_taylorPoly_le (f : ℝ → ℂ) (n : ℕ) : (taylorPoly f n).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  exact natDegree_C_mul_X_pow_le _ _ |>.trans (Nat.lt_succ_iff.1 (mem_range.1 hk))

/-- **Taylor remainder of the transform.** -/
theorem norm_paperFT_sub_taylor_le {f : ℝ → ℂ} {a r : ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) {n : ℕ} {x : ℝ} (hr : a * |x| ≤ r) (hrn : r / ((n : ℝ) + 2) ≤ 1 / 2) :
    ‖paperFT f x - (taylorPoly f n).eval (x : ℂ)‖ ≤ (∫ u, ‖f u‖) * (r ^ (n + 1) / ((n + 1)! : ℝ) * 2) := by
  have hF : MeasureTheory.Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hint (k : ℕ) : MeasureTheory.Integrable fun u : ℝ => f u * ((Complex.I * u) ^ k / (k ! : ℂ)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hfc.mul_right
  have heval : (taylorPoly f n).eval (x : ℂ) =
      ∫ u : ℝ, f u * ∑ k ∈ range (n + 1), (Complex.I * x * u) ^ k / (k ! : ℂ) := by
    have hsum : ∫ u : ℝ, f u * ∑ k ∈ range (n + 1), (Complex.I * x * u) ^ k / (k ! : ℂ) =
        ∑ k ∈ range (n + 1), ∫ u : ℝ, f u * ((Complex.I * u) ^ k / (k ! : ℂ)) * (x : ℂ) ^ k := by
      rw [← MeasureTheory.integral_finsetSum _ fun k _ => (hint k).mul_const _]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [show Complex.I * (x : ℂ) * u = (Complex.I * u) * x by ring, mul_pow]
      ring
    rw [hsum, taylorPoly, eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact sum_congr rfl fun k _ => (MeasureTheory.integral_mul_const _ _).symm
  have hi1 : MeasureTheory.Integrable fun u : ℝ => f u * Complex.exp (Complex.I * x * u) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hfc.mul_right
  have hi2 : MeasureTheory.Integrable fun u : ℝ =>
      f u * ∑ k ∈ range (n + 1), (Complex.I * x * u) ^ k / (k ! : ℂ) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hfc.mul_right
  rw [heval, paperFT_def, ← MeasureTheory.integral_sub hi1 hi2,
    ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.norm_integral_le_of_norm_le (hF.norm.mul_const _)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [← mul_sub, norm_mul]
  by_cases hfu : f u = 0
  · simp [hfu]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hu := hsupp u hfu
  have hz : ‖Complex.I * (x : ℂ) * (u : ℂ)‖ ≤ r := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have hx0 := abs_nonneg x
    nlinarith only [mul_le_mul_of_nonneg_left hu hx0, hr]
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hz
  have hcond : ‖Complex.I * (x : ℂ) * (u : ℂ)‖ / ((n + 1).succ : ℝ) ≤ 1 / 2 := by
    have e : ((n + 1).succ : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [e]
    exact (div_le_div_of_nonneg_right hz (by positivity)).trans hrn
  refine (Complex.exp_bound' hcond).trans ?_
  have hp := pow_le_pow_left₀ (norm_nonneg _) hz (n + 1)
  gcongr

/-- The spacing `σ = 48⁻⁴/(9a)`. -/
def nodeStep (a : ℝ) : ℝ := 1 / (9 * 48 ^ 4 * a)

theorem nodeStep_pos {a : ℝ} (ha : 0 < a) : 0 < nodeStep a := by
  unfold nodeStep
  positivity

/-- On `|y| ≤ 3(n+1)σ` the transform is within `2‖f‖₁ 48^{−4(n+1)}` of its Taylor polynomial. -/
theorem norm_paperFT_sub_taylor_le_of_step {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) {n : ℕ} {y : ℝ}
    (hy : |y| ≤ 3 * ((n : ℝ) + 1) * nodeStep a) :
    ‖paperFT f y - (taylorPoly f n).eval (y : ℂ)‖ ≤ (∫ u, ‖f u‖) * (2 * ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨r, hrdef⟩ : ∃ r, r = ((n : ℝ) + 1) * (1 / (3 * 48 ^ 4)) := ⟨_, rfl⟩
  have hr : a * |y| ≤ r := by
    have h1 := mul_le_mul_of_nonneg_left hy ha.le
    refine h1.trans (le_of_eq ?_)
    rw [hrdef, nodeStep]
    field_simp
    norm_num
  have hrn : r / ((n : ℝ) + 2) ≤ 1 / 2 := by
    rw [hrdef, div_le_iff₀ (by positivity)]
    norm_num
    nlinarith only [hn0]
  have hbase := norm_paperFT_sub_taylor_le hf hfc hsupp hr hrn
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (MeasureTheory.integral_nonneg fun _ => norm_nonneg _))
  have hfact : ((n : ℝ) + 1) ^ (n + 1) / ((n + 1)! : ℝ) ≤ 3 ^ (n + 1) := by
    have h1 := Real.pow_div_factorial_le_exp (x := (n : ℝ) + 1) (by positivity) (n + 1)
    refine h1.trans ?_
    have e : Real.exp ((n : ℝ) + 1) = Real.exp 1 ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [e]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith only [Real.exp_one_lt_d9]) _
  have e : r ^ (n + 1) / ((n + 1)! : ℝ) =
      (((n : ℝ) + 1) ^ (n + 1) / ((n + 1)! : ℝ)) * (1 / (3 * 48 ^ 4)) ^ (n + 1) := by
    rw [hrdef, mul_pow]
    ring
  have h2 : r ^ (n + 1) / ((n + 1)! : ℝ) ≤ ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) := by
    rw [e]
    refine (mul_le_mul_of_nonneg_right hfact (by positivity)).trans (le_of_eq ?_)
    rw [← mul_pow]
    congr 1
    norm_num
  linarith only [h2]

/-- **Nodes control the transform.** -/
theorem norm_paperFT_le_of_nodes {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) {n : ℕ} (v : ℕ → ℝ)
    (hv : ∀ j ∈ range (n + 1), ((n : ℝ) + 1 + 2 * j) * nodeStep a ≤ v j ∧
      v j ≤ ((n : ℝ) + 1 + 2 * j + 1) * nodeStep a) {x : ℝ}
    (hx : |x| ≤ ((n : ℝ) + 1) * nodeStep a) :
    ‖paperFT f x‖ ≤ 48 ^ n * ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ +
      (∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹ := by
  have hσ := nodeStep_pos ha
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = nodeStep a := ⟨_, rfl⟩
  rw [← hσdef] at hv hx hσ
  have hF0 : 0 ≤ ∫ u, ‖f u‖ := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hjle (j : ℕ) (hj : j ∈ range (n + 1)) : (j : ℝ) ≤ n := by
    exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hj)
  -- Geometry of the nodes.
  have hvpos (j : ℕ) (hj : j ∈ range (n + 1)) : 0 ≤ v j := by
    have h := (hv j hj).1
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact le_trans (by positivity) h
  have hvup (j : ℕ) (hj : j ∈ range (n + 1)) : v j ≤ 3 * ((n : ℝ) + 1) * σ := by
    refine (hv j hj).2.trans (mul_le_mul_of_nonneg_right ?_ hσ.le)
    linarith only [hjle j hj]
  have hsep : ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1), σ * |(i : ℝ) - j| ≤ |v i - v j| := by
    intro i hi j hj
    rcases lt_trichotomy i j with hij | hij | hij
    · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      have h1 := (hv i hi).2
      have h2 := (hv j hj).1
      rw [abs_sub_comm (i : ℝ), abs_of_nonneg (by linarith only [hij']), abs_sub_comm (v i)]
      refine le_trans ?_ (le_abs_self _)
      nlinarith only [h1, h2, hij', hσ]
    · simp [hij]
    · have hij' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij
      have h1 := (hv j hj).2
      have h2 := (hv i hi).1
      rw [abs_of_nonneg (by linarith only [hij'])]
      refine le_trans ?_ (le_abs_self _)
      nlinarith only [h1, h2, hij', hσ]
  have hxv : ∀ i ∈ range (n + 1), ‖(x : ℂ) - (v i : ℂ)‖ ≤ 4 * ((n : ℝ) + 1) * σ := by
    intro i hi
    have e : (x : ℂ) - (v i : ℂ) = ((x - v i : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hvup i hi
    have h2 := hvpos i hi
    have h3 := abs_sub x (v i)
    rw [abs_of_nonneg h2] at h3
    linarith only [h1, h3, hx]
  have hL := norm_eval_le_of_nodes (taylorPoly f n) (natDegree_taylorPoly_le f n) hσ v hsep hxv
  obtain ⟨d, hd⟩ : ∃ d, d = (∫ u, ‖f u‖) * (2 * ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1)) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hxT : ‖paperFT f x - (taylorPoly f n).eval (x : ℂ)‖ ≤ d := by
    rw [hd]
    refine norm_paperFT_sub_taylor_le_of_step ha hf hfc hsupp ?_
    rw [← hσdef]
    nlinarith only [hx, hσ, hn0]
  have hvT : ∀ j ∈ range (n + 1), ‖(taylorPoly f n).eval (v j : ℂ)‖ ≤ ‖paperFT f (v j)‖ + d := by
    intro j hj
    have h := norm_paperFT_sub_taylor_le_of_step ha hf hfc hsupp (n := n) (y := v j) (by
      rw [← hσdef, abs_of_nonneg (hvpos j hj)]
      exact hvup j hj)
    rw [← hd] at h
    have h2 := norm_sub_norm_le ((taylorPoly f n).eval (v j : ℂ)) (paperFT f (v j))
    rw [norm_sub_rev] at h2
    linarith only [h, h2]
  have h48 : (1 : ℝ) ≤ 48 ^ n := one_le_pow₀ (by norm_num)
  have hsum : ∑ j ∈ range (n + 1), ‖(taylorPoly f n).eval (v j : ℂ)‖ ≤
      ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ + ((n : ℝ) + 1) * d := by
    refine (sum_le_sum hvT).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring
  have hP : ‖paperFT f x‖ ≤ d + ‖(taylorPoly f n).eval (x : ℂ)‖ := by
    have := norm_sub_norm_le (paperFT f x) ((taylorPoly f n).eval (x : ℂ))
    linarith only [this, hxT]
  -- The additive term.
  have hnpow : (n : ℝ) + 1 ≤ 48 ^ n := by
    have h := one_add_mul_le_pow (a := (47 : ℝ)) (by norm_num) n
    norm_num at h
    nlinarith only [h, hn0]
  have hadd : d * (1 + 48 ^ n * ((n : ℝ) + 1)) ≤ (∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹ := by
    rw [hd, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hF0
    have h1 : 1 + (48 : ℝ) ^ n * ((n : ℝ) + 1) ≤ 2 * 48 ^ (2 * n) := by
      have e : (48 : ℝ) ^ (2 * n) = 48 ^ n * 48 ^ n := by rw [two_mul, pow_add]
      rw [e]
      nlinarith only [hnpow, h48]
    have h2 : ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (4 * 48 ^ (2 * n)) ≤ ((48 : ℝ) ^ (2 * n))⁻¹ := by
      have hpos : (0 : ℝ) < 48 ^ (2 * n) := by positivity
      rw [inv_pow, ← div_eq_inv_mul, div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ hpos]
      have e : ((48 : ℝ) ^ 4) ^ (n + 1) = 48 ^ (2 * n) * 48 ^ (2 * n) * 48 ^ 4 := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
      rw [e]
      have : (1 : ℝ) ≤ 48 ^ (2 * n) := one_le_pow₀ (by norm_num)
      nlinarith only [mul_pos hpos hpos]
    have h0 : 0 ≤ ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) := by positivity
    calc
      2 * ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (1 + 48 ^ n * ((n : ℝ) + 1))
          ≤ 2 * ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (2 * 48 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((48 ^ 4 : ℝ)⁻¹) ^ (n + 1) * (4 * 48 ^ (2 * n)) := by ring
      _ ≤ _ := h2
  calc
    ‖paperFT f x‖ ≤ d + 48 ^ n * (∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ + ((n : ℝ) + 1) * d) :=
      hP.trans (add_le_add le_rfl (hL.trans (mul_le_mul_of_nonneg_left hsum (by positivity))))
    _ = 48 ^ n * ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ + d * (1 + 48 ^ n * ((n : ℝ) + 1)) := by ring
    _ ≤ _ := add_le_add le_rfl hadd

/-- **Squared form.** -/
theorem norm_sq_paperFT_le_of_nodes {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) {n : ℕ} (v : ℕ → ℝ)
    (hv : ∀ j ∈ range (n + 1), ((n : ℝ) + 1 + 2 * j) * nodeStep a ≤ v j ∧
      v j ≤ ((n : ℝ) + 1 + 2 * j + 1) * nodeStep a) {x : ℝ}
    (hx : |x| ≤ ((n : ℝ) + 1) * nodeStep a) :
    ‖paperFT f x‖ ^ 2 ≤ 2 * ((n : ℝ) + 1) * ((48 : ℝ) ^ n) ^ 2 * ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ ^ 2 +
      2 * ((∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹) ^ 2 := by
  have h := norm_paperFT_le_of_nodes ha hf hfc hsupp v hv hx
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ := ⟨_, rfl⟩
  rw [← hA] at h
  have hCS := sq_sum_le_card_mul_sum_sq (s := range (n + 1)) (f := fun j => ‖paperFT f (v j)‖)
  rw [← hA, card_range] at hCS
  push_cast at hCS
  obtain ⟨B, hB⟩ : ∃ B, B = (∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹ := ⟨_, rfl⟩
  rw [← hB] at h ⊢
  have h0 : 0 ≤ ‖paperFT f x‖ := norm_nonneg _
  have hsq : ‖paperFT f x‖ ^ 2 ≤ (48 ^ n * A + B) ^ 2 := pow_le_pow_left₀ h0 h 2
  have h2 : (48 ^ n * A + B) ^ 2 ≤ 2 * (48 ^ n * A) ^ 2 + 2 * B ^ 2 := by
    nlinarith only [sq_nonneg ((48 : ℝ) ^ n * A - B)]
  have h3 : (48 ^ n * A) ^ 2 ≤ ((48 : ℝ) ^ n) ^ 2 * (((n : ℝ) + 1) * ∑ j ∈ range (n + 1), ‖paperFT f (v j)‖ ^ 2) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
  nlinarith only [hsq, h2, h3]

end

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.norm_eval_le_of_nodes
#print axioms GaloisForLFunctions.VerifiedHeightRungs.norm_sq_paperFT_le_of_nodes
