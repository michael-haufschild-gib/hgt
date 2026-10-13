import Mathlib

/-!
# Discrete annihilating measures with rapidly decaying complex weights

There is a discrete complex measure `μ = Σ_i c_i δ_{x_i}` with pairwise distinct nodes in the
annulus `5/4 ≤ |x| ≤ 10` and a unit mass at the isolated node `x = 5/4`, all of whose holomorphic
moments vanish: `Σ_i c_i x_i^m = 0` for every `m ≥ 0`. Moreover `Σ_i |c_i|^p < ∞` for every
`p > 0` (`exists_annihilating_discrete_measure`). Equivalently, the Cauchy transform
`Σ_i c_i/(z − x_i)` vanishes identically for `|z| > 10`, although `μ ≠ 0`.

**Construction (circle quadrature).** Start from `δ_{5/4}`, with residual moments
`E_0(m) = (5/4)^m`. Stage `k` puts `N_k = 2^{3k+8}` nodes `R_k ω_k^j` on the circle of radius
`R_k`, where `ω_k` is a primitive `N_k`-th root of unity. Their weights are the discrete Fourier
coefficients `w_{k,j} = −N_k^{−1} Σ_{i<N_k} E_k(i) (R_k ω_k^j)^{−i}`.
* By orthogonality of the roots of unity, the new residual
  `E_{k+1}(m) = E_k(m) + Σ_j w_{k,j}(R_k ω_k^j)^m` vanishes for `m < N_k`
  (`sum_weight_mul_node_pow`).
* If `|E_k(m)| ≤ L_k R_k^m`, then `|w_{k,j}| ≤ L_k` (`norm_weight_le`).
* For `m ≥ N_k`, the ratio `R_{k+1}/R_k = 1 + 2^{−k}` gains `(R_k/R_{k+1})^{N_k} ≤ 2^{−4^{k+4}}`
  by Bernoulli's inequality. Hence `|E_{k+1}(m)| ≤ L_{k+1} R_{k+1}^m` with
  `L_{k+1} = (N_k + 1) 2^{−4^{k+4}} L_k` (`norm_residual_le`).
* The radii stay below `(4/3)e² < 10`, and the weights decay super-exponentially in the stage.

No summability condition of power type on the weights forces a uniqueness theorem for Cauchy
transforms of discrete measures. The node series `S(t) = Σ_i c_i/(1 − t x_i)` vanishes on the disc
`|t| < 1/10`, yet it has a simple pole at the isolated node `t = 4/5`
(`tsum_coef_div_eq_zero`, `norm_tsum_coef_div_ge`).
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.CircleQuadratureAnnihilating

noncomputable section

/-! ## Stage data -/

/-- Number of nodes of circle stage `k`: `N_k = 2^{3k+8}`. -/
def nodeCount (k : ℕ) : ℕ := 2 ^ (3 * k + 8)

/-- Gain exponent of stage `k`: `a_k = 4^{k+4}`. -/
def gainExp (k : ℕ) : ℕ := 4 ^ (k + 4)

theorem nodeCount_eq (k : ℕ) : nodeCount k = 2 ^ k * gainExp k := by
  unfold nodeCount gainExp
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem nodeCount_pos (k : ℕ) : 0 < nodeCount k := by
  unfold nodeCount; positivity

/-- Radius ratio `θ_k = 1 + 2^{−k}`. -/
def radiusRatio (k : ℕ) : ℝ := 1 + 1 / 2 ^ k

/-- Stage radii `R_0 = 4/3`, `R_{k+1} = θ_k R_k`. -/
def radius : ℕ → ℝ
  | 0 => 4 / 3
  | k + 1 => radius k * radiusRatio k

/-- A primitive `N_k`-th root of unity. -/
def root (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (nodeCount k : ℂ))

/-- The nodes `R_k ω_k^j` of stage `k`. -/
def node (k j : ℕ) : ℂ := (radius k : ℂ) * root k ^ j

/-- Residual moments: `E_0(m) = (5/4)^m` and `E_{k+1}(m) = E_k(m) + Σ_j w_{k,j} (R_k ω_k^j)^m`. -/
def residual : ℕ → ℕ → ℂ
  | 0, m => (5 / 4 : ℂ) ^ m
  | k + 1, m => residual k m + ∑ j ∈ range (nodeCount k),
      (-(1 / (nodeCount k : ℂ)) * ∑ i ∈ range (nodeCount k), residual k i / node k j ^ i) *
        node k j ^ m

/-- The discrete Fourier weights of stage `k`. -/
def weight (k j : ℕ) : ℂ :=
  -(1 / (nodeCount k : ℂ)) * ∑ i ∈ range (nodeCount k), residual k i / node k j ^ i

theorem residual_succ (k m : ℕ) :
    residual (k + 1) m = residual k m + ∑ j ∈ range (nodeCount k), weight k j * node k j ^ m :=
  rfl

/-! ## Roots of unity and orthogonality -/

theorem isPrimitiveRoot_root (k : ℕ) : IsPrimitiveRoot (root k) (nodeCount k) :=
  Complex.isPrimitiveRoot_exp _ (nodeCount_pos k).ne'

theorem norm_root (k : ℕ) : ‖root k‖ = 1 :=
  (isPrimitiveRoot_root k).norm'_eq_one (nodeCount_pos k).ne'

theorem one_lt_radiusRatio (k : ℕ) : 1 < radiusRatio k := by
  unfold radiusRatio
  have : 0 < 1 / (2 : ℝ) ^ k := by positivity
  linarith

theorem radius_pos : ∀ k, 0 < radius k
  | 0 => by norm_num [radius]
  | k + 1 => mul_pos (radius_pos k) (by linarith [one_lt_radiusRatio k])

theorem radius_lt_succ (k : ℕ) : radius k < radius (k + 1) := by
  show radius k < radius k * radiusRatio k
  have := radius_pos k
  nlinarith [one_lt_radiusRatio k]

theorem four_thirds_le_radius : ∀ k, (4 / 3 : ℝ) ≤ radius k
  | 0 => by norm_num [radius]
  | k + 1 => (four_thirds_le_radius k).trans (radius_lt_succ k).le

theorem norm_node (k j : ℕ) : ‖node k j‖ = radius k := by
  unfold node
  rw [norm_mul, norm_pow, norm_root, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radius_pos k)]

theorem node_ne_zero (k j : ℕ) : node k j ≠ 0 := by
  intro h
  have := norm_node k j
  rw [h, norm_zero] at this
  linarith [radius_pos k]

/-- Orthogonality of the stage nodes for exponents below `N_k`. -/
theorem sum_node_pow_div (k : ℕ) {m i : ℕ} (hm : m < nodeCount k) (hi : i < nodeCount k) :
    ∑ j ∈ range (nodeCount k), node k j ^ m / node k j ^ i =
      if m = i then (nodeCount k : ℂ) else 0 := by
  have hζ := isPrimitiveRoot_root k
  have hω0 : root k ≠ 0 := by
    intro h; have := norm_root k; rw [h, norm_zero] at this; norm_num at this
  split_ifs with hmi
  · subst hmi
    rw [Finset.sum_congr rfl (fun j _ => div_self (pow_ne_zero _ (node_ne_zero k j))),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hterm : ∀ j, node k j ^ m / node k j ^ i =
        ((radius k : ℂ) ^ m / (radius k : ℂ) ^ i) * (root k ^ m / root k ^ i) ^ j := by
      intro j
      unfold node
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j m, mul_comm j i, pow_mul, pow_mul,
        mul_div_mul_comm, ← div_pow]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
    have hζ1 : root k ^ m / root k ^ i ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq (pow_ne_zero _ hω0)] at h
      exact hmi (hζ.pow_inj hm hi h)
    have hζN : (root k ^ m / root k ^ i) ^ nodeCount k = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm m, mul_comm i, pow_mul, pow_mul, hζ.pow_eq_one,
        one_pow, one_pow, div_one]
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div, mul_zero]

/-- **Exactness of the circle quadrature below `N_k`.** -/
theorem sum_weight_mul_node_pow (k : ℕ) {m : ℕ} (hm : m < nodeCount k) :
    ∑ j ∈ range (nodeCount k), weight k j * node k j ^ m = -residual k m := by
  have hN : (nodeCount k : ℂ) ≠ 0 := by exact_mod_cast (nodeCount_pos k).ne'
  have hswap : ∑ j ∈ range (nodeCount k), weight k j * node k j ^ m =
      -(1 / (nodeCount k : ℂ)) * ∑ i ∈ range (nodeCount k),
        residual k i * ∑ j ∈ range (nodeCount k), node k j ^ m / node k j ^ i := by
    calc ∑ j ∈ range (nodeCount k), weight k j * node k j ^ m
        = ∑ j ∈ range (nodeCount k), ∑ i ∈ range (nodeCount k),
            -(1 / (nodeCount k : ℂ)) * (residual k i * (node k j ^ m / node k j ^ i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          unfold weight
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i ∈ range (nodeCount k), ∑ j ∈ range (nodeCount k),
            -(1 / (nodeCount k : ℂ)) * (residual k i * (node k j ^ m / node k j ^ i)) :=
          Finset.sum_comm
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [sum_node_pow_div k hm (Finset.mem_range.mp hi)])]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hm)]
  field_simp

theorem residual_succ_eq_zero (k : ℕ) {m : ℕ} (hm : m < nodeCount k) : residual (k + 1) m = 0 := by
  rw [residual_succ, sum_weight_mul_node_pow k hm, add_neg_cancel]

/-! ## Bounds -/

/-- Bernoulli gain: `2^{a_k} ≤ θ_k^{N_k}`. -/
theorem two_pow_gainExp_le (k : ℕ) : (2 : ℝ) ^ gainExp k ≤ radiusRatio k ^ nodeCount k := by
  rw [nodeCount_eq, pow_mul]
  have hb : (2 : ℝ) ≤ radiusRatio k ^ 2 ^ k := by
    have h := one_add_mul_le_pow (a := 1 / (2 : ℝ) ^ k)
      (by have : 0 ≤ 1 / (2 : ℝ) ^ k := by positivity
          linarith) (2 ^ k)
    have e : (1 : ℝ) + ((2 ^ k : ℕ) : ℝ) * (1 / 2 ^ k) = 2 := by
      push_cast; field_simp; ring
    unfold radiusRatio
    linarith
  exact pow_le_pow_left₀ (by norm_num) hb _

/-- For `m ≥ N_k`: `2^{a_k} R_k^m ≤ R_{k+1}^m`. -/
theorem two_pow_mul_radius_pow_le {k m : ℕ} (hm : nodeCount k ≤ m) :
    (2 : ℝ) ^ gainExp k * radius k ^ m ≤ radius (k + 1) ^ m := by
  show (2 : ℝ) ^ gainExp k * radius k ^ m ≤ (radius k * radiusRatio k) ^ m
  rw [mul_pow, mul_comm]
  have h1 : radiusRatio k ^ nodeCount k ≤ radiusRatio k ^ m :=
    pow_le_pow_right₀ (one_lt_radiusRatio k).le hm
  have h2 := two_pow_gainExp_le k
  have h0 : 0 ≤ radius k ^ m := pow_nonneg (radius_pos k).le _
  exact mul_le_mul_of_nonneg_left (h2.trans h1) h0

/-- The residual bounds `L_0 = 1`, `L_{k+1} = (N_k + 1) L_k / 2^{a_k}`. -/
def bound : ℕ → ℝ
  | 0 => 1
  | k + 1 => ((nodeCount k : ℝ) + 1) * bound k / 2 ^ gainExp k

theorem bound_nonneg : ∀ k, 0 ≤ bound k
  | 0 => by norm_num [bound]
  | k + 1 => by
    show 0 ≤ ((nodeCount k : ℝ) + 1) * bound k / 2 ^ gainExp k
    have := bound_nonneg k
    positivity

theorem norm_weight_le {k : ℕ} (h : ∀ m, ‖residual k m‖ ≤ bound k * radius k ^ m) (j : ℕ) :
    ‖weight k j‖ ≤ bound k := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  unfold weight
  rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_natCast]
  have hsum : ‖∑ i ∈ range (nodeCount k), residual k i / node k j ^ i‖ ≤
      (nodeCount k : ℝ) * bound k := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ range (nodeCount k), ‖residual k i / node k j ^ i‖ ≤ bound k := by
      intro i _
      rw [norm_div, norm_pow, norm_node, div_le_iff₀ (pow_pos (radius_pos k) _)]
      exact h i
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [Finset.card_range, nsmul_eq_mul]
  calc 1 / (nodeCount k : ℝ) * ‖∑ i ∈ range (nodeCount k), residual k i / node k j ^ i‖
      ≤ 1 / (nodeCount k : ℝ) * ((nodeCount k : ℝ) * bound k) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = bound k := by field_simp

/-- **The residual moments are controlled at every stage.** `|E_k(m)| ≤ L_k R_k^m`. -/
theorem norm_residual_le : ∀ k m, ‖residual k m‖ ≤ bound k * radius k ^ m
  | 0, m => by
    show ‖(5 / 4 : ℂ) ^ m‖ ≤ 1 * (4 / 3 : ℝ) ^ m
    rw [norm_pow, one_mul]
    have : ‖(5 / 4 : ℂ)‖ = 5 / 4 := by
      rw [show (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num)]
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
  | k + 1, m => by
    have ih := norm_residual_le k
    by_cases hm : m < nodeCount k
    · rw [residual_succ_eq_zero k hm, norm_zero]
      exact mul_nonneg (bound_nonneg _) (pow_nonneg (radius_pos _).le _)
    · push Not at hm
      have hw := norm_weight_le ih
      have hR0 : 0 ≤ radius k ^ m := pow_nonneg (radius_pos k).le _
      have hsum : ‖∑ j ∈ range (nodeCount k), weight k j * node k j ^ m‖ ≤
          (nodeCount k : ℝ) * (bound k * radius k ^ m) := by
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ j ∈ range (nodeCount k), ‖weight k j * node k j ^ m‖ ≤
            bound k * radius k ^ m := by
          intro j _
          rw [norm_mul, norm_pow, norm_node]
          exact mul_le_mul_of_nonneg_right (hw j) hR0
        refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
        rw [Finset.card_range, nsmul_eq_mul]
      have hgain := two_pow_mul_radius_pow_le hm
      have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
      have hL0 := bound_nonneg k
      calc ‖residual (k + 1) m‖
          ≤ ‖residual k m‖ + ‖∑ j ∈ range (nodeCount k), weight k j * node k j ^ m‖ := by
            rw [residual_succ]; exact norm_add_le _ _
        _ ≤ bound k * radius k ^ m + (nodeCount k : ℝ) * (bound k * radius k ^ m) :=
            add_le_add (ih m) hsum
        _ = ((nodeCount k : ℝ) + 1) * bound k / 2 ^ gainExp k *
              (2 ^ gainExp k * radius k ^ m) := by field_simp; ring
        _ ≤ ((nodeCount k : ℝ) + 1) * bound k / 2 ^ gainExp k * radius (k + 1) ^ m :=
            mul_le_mul_of_nonneg_left hgain (by positivity)
        _ = bound (k + 1) * radius (k + 1) ^ m := rfl

theorem norm_weight_le_bound (k j : ℕ) : ‖weight k j‖ ≤ bound k :=
  norm_weight_le (norm_residual_le k) j

/-! ## Explicit decay of the bounds -/

theorem quadratic_le_four_pow (k : ℕ) : 3 * k ^ 2 + 19 * k + 20 ≤ 4 ^ (k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ (4 : ℕ) (k + 4)]
    nlinarith

theorem nodeCount_add_one_le (k : ℕ) : (nodeCount k : ℝ) + 1 ≤ 2 ^ (3 * k + 9) := by
  unfold nodeCount
  have h : (1 : ℝ) ≤ 2 ^ (3 * k + 8) := one_le_pow₀ (by norm_num)
  push_cast
  rw [show (2 : ℝ) ^ (3 * k + 9) = 2 ^ (3 * k + 8) * 2 by rw [← pow_succ]]
  linarith

theorem bound_le_one : ∀ k, bound k ≤ 1
  | 0 => by norm_num [bound]
  | k + 1 => by
    show ((nodeCount k : ℝ) + 1) * bound k / 2 ^ gainExp k ≤ 1
    have hb := bound_le_one k
    have hb0 := bound_nonneg k
    have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
    rw [div_le_one h2]
    have hexp : 3 * k + 9 ≤ gainExp k := by
      have := quadratic_le_four_pow k; unfold gainExp; nlinarith
    have hpow : (2 : ℝ) ^ (3 * k + 9) ≤ 2 ^ gainExp k := pow_le_pow_right₀ (by norm_num) hexp
    have := nodeCount_add_one_le k
    calc ((nodeCount k : ℝ) + 1) * bound k ≤ ((nodeCount k : ℝ) + 1) * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 ^ gainExp k := by linarith

/-- `L_{k+1} ≤ 2^{−((3k+11)(k+1) + 2k)}`. -/
theorem bound_succ_le (k : ℕ) :
    bound (k + 1) ≤ (1 / 2 : ℝ) ^ ((3 * k + 11) * (k + 1) + 2 * k) := by
  show ((nodeCount k : ℝ) + 1) * bound k / 2 ^ gainExp k ≤ _
  set E := (3 * k + 11) * (k + 1) + 2 * k with hE
  have hexp : E + (3 * k + 9) ≤ gainExp k := by
    have := quadratic_le_four_pow k; unfold gainExp; rw [hE]; nlinarith
  have hb := bound_le_one k
  have hb0 := bound_nonneg k
  have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
  rw [div_le_iff₀ h2, one_div_pow]
  have hpow : (2 : ℝ) ^ (E + (3 * k + 9)) ≤ 2 ^ gainExp k := pow_le_pow_right₀ (by norm_num) hexp
  rw [pow_add] at hpow
  have h2E : (0 : ℝ) < 2 ^ E := by positivity
  have := nodeCount_add_one_le k
  calc ((nodeCount k : ℝ) + 1) * bound k ≤ 2 ^ (3 * k + 9) := by nlinarith
    _ = 1 / 2 ^ E * (2 ^ E * 2 ^ (3 * k + 9)) := by field_simp
    _ ≤ 1 / 2 ^ E * 2 ^ gainExp k := mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## Bounded radii -/

theorem radius_le_exp : ∀ k, radius k ≤ 4 / 3 * Real.exp (∑ i ∈ range k, (1 / 2 : ℝ) ^ i)
  | 0 => by simp [radius]
  | k + 1 => by
    show radius k * radiusRatio k ≤ _
    rw [Finset.sum_range_succ, Real.exp_add]
    have ih := radius_le_exp k
    have hr : radiusRatio k ≤ Real.exp ((1 / 2 : ℝ) ^ k) := by
      unfold radiusRatio
      rw [← one_div_pow]
      linarith [Real.add_one_le_exp ((1 / 2 : ℝ) ^ k)]
    have h1 : 0 ≤ radiusRatio k := by linarith [one_lt_radiusRatio k]
    calc radius k * radiusRatio k ≤ (4 / 3 * Real.exp (∑ i ∈ range k, (1 / 2 : ℝ) ^ i)) *
          Real.exp ((1 / 2 : ℝ) ^ k) :=
        mul_le_mul ih hr h1 (by positivity)
      _ = _ := by ring

theorem radius_le_ten (k : ℕ) : radius k ≤ 10 := by
  refine (radius_le_exp k).trans ?_
  have hs := sum_geometric_two_le k
  have he : Real.exp (∑ i ∈ range k, (1 / 2 : ℝ) ^ i) ≤ Real.exp 2 := Real.exp_le_exp.mpr hs
  have he2 : Real.exp 2 < 7.39 := by
    have h := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  linarith

/-! ## The configuration -/

/-- Stage sizes: one base node, then `N_k` circle nodes. -/
def count : ℕ → ℕ
  | 0 => 1
  | k + 1 => nodeCount k

/-- The index type. -/
abbrev Idx := Σ k : ℕ, Fin (count k)

/-- The nodes. -/
def point : Idx → ℂ
  | ⟨0, _⟩ => 5 / 4
  | ⟨k + 1, j⟩ => node k j

/-- The weights. -/
def coef : Idx → ℂ
  | ⟨0, _⟩ => 1
  | ⟨k + 1, j⟩ => weight k j

/-- The base index. -/
def base : Idx := ⟨0, ⟨0, by norm_num [count]⟩⟩

theorem norm_five_fourths : ‖(5 / 4 : ℂ)‖ = 5 / 4 := by
  rw [show (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by norm_num)]

theorem norm_point_ge (i : Idx) : 5 / 4 ≤ ‖point i‖ := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show 5 / 4 ≤ ‖(5 / 4 : ℂ)‖; rw [norm_five_fourths]
  | succ k =>
    show 5 / 4 ≤ ‖node k j‖
    rw [norm_node]; linarith [four_thirds_le_radius k]

theorem norm_point_le (i : Idx) : ‖point i‖ ≤ 10 := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show ‖(5 / 4 : ℂ)‖ ≤ 10; rw [norm_five_fourths]; norm_num
  | succ k => show ‖node k j‖ ≤ 10; rw [norm_node]; exact radius_le_ten k

theorem four_thirds_le_norm_point {i : Idx} (hi : i ≠ base) : 4 / 3 ≤ ‖point i‖ := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero =>
    exfalso; apply hi
    unfold base
    congr
    exact Subsingleton.elim (α := Fin 1) _ _
  | succ k => show 4 / 3 ≤ ‖node k j‖; rw [norm_node]; exact four_thirds_le_radius k

theorem strictMono_radius : StrictMono radius := strictMono_nat_of_lt_succ radius_lt_succ

theorem point_injective : Function.Injective point := by
  rintro ⟨ka, ja⟩ ⟨kb, jb⟩ h
  cases ka with
  | zero =>
    cases kb with
    | zero =>
      congr
      exact Subsingleton.elim (α := Fin 1) _ _
    | succ kb =>
      exfalso
      have h' : (5 / 4 : ℂ) = node kb jb := h
      have := congrArg norm h'
      rw [norm_five_fourths, norm_node] at this
      linarith [four_thirds_le_radius kb]
  | succ ka =>
    cases kb with
    | zero =>
      exfalso
      have h' : node ka ja = (5 / 4 : ℂ) := h
      have := congrArg norm h'
      rw [norm_five_fourths, norm_node] at this
      linarith [four_thirds_le_radius ka]
    | succ kb =>
      have h' : node ka ja = node kb jb := h
      have hk : ka = kb := by
        have := congrArg norm h'
        rw [norm_node, norm_node] at this
        exact strictMono_radius.injective this
      subst hk
      have hr : (radius ka : ℂ) ≠ 0 := by exact_mod_cast (radius_pos ka).ne'
      have hpow : root ka ^ (ja : ℕ) = root ka ^ (jb : ℕ) := by
        unfold node at h'
        exact mul_left_cancel₀ hr h'
      have hj := (isPrimitiveRoot_root ka).pow_inj ja.isLt jb.isLt hpow
      have : ja = jb := Fin.ext hj
      subst this
      rfl

/-! ## Summability -/

theorem norm_coef_le (i : Idx) : ‖coef i‖ ≤ 1 := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show ‖(1 : ℂ)‖ ≤ 1; simp
  | succ k => exact (norm_weight_le_bound k j).trans (bound_le_one k)

theorem summable_stage_rpow {p : ℝ} (hp : 0 < p) :
    Summable fun k : ℕ => (nodeCount (k + 1) : ℝ) * bound (k + 1) ^ p := by
  have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * p) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (2 * p) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0 hq1) ?_
  filter_upwards [eventually_ge_atTop ⌈1 / p⌉₊] with k hk
  have hkp : 1 ≤ p * ((k : ℝ) + 1) := by
    have h1 : 1 / p ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have h2 : 1 / p * p = 1 := by field_simp
    nlinarith
  have hb0 := bound_nonneg (k + 1)
  set E : ℕ := (3 * k + 11) * (k + 1) + 2 * k with hE
  have hbE := bound_succ_le k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : bound (k + 1) ^ p ≤ ((1 / 2 : ℝ) ^ E) ^ p := Real.rpow_le_rpow hb0 hbE hp.le
  have h2 : ((1 / 2 : ℝ) ^ E) ^ p = (2 : ℝ) ^ (-((E : ℝ) * p)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
  have h3 : (nodeCount (k + 1) : ℝ) = (2 : ℝ) ^ ((3 * k + 11 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; unfold nodeCount; push_cast; ring_nf
  have h4 : ((1 / 2 : ℝ) ^ (2 * p)) ^ k = (2 : ℝ) ^ (-(2 * p * k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
  rw [h4]
  calc (nodeCount (k + 1) : ℝ) * bound (k + 1) ^ p
      ≤ (nodeCount (k + 1) : ℝ) * (2 : ℝ) ^ (-((E : ℝ) * p)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 : ℝ) ^ (((3 * k + 11 : ℕ) : ℝ) + -((E : ℝ) * p)) := by
        rw [h3, ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (-(2 * p * k)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hE]
        push_cast
        nlinarith

theorem summable_norm_coef_rpow {p : ℝ} (hp : 0 < p) : Summable fun i : Idx => ‖coef i‖ ^ p := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun k => Summable.of_finite, ?_⟩
  rw [← summable_nat_add_iff 1]
  have hstage : ∀ k : ℕ, ∑' j : Fin (count (k + 1)), ‖coef ⟨k + 1, j⟩‖ ^ p ≤
      (nodeCount k : ℝ) * bound k ^ p := by
    intro k
    rw [tsum_fintype]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (nodeCount k))),
        ‖weight k j‖ ^ p ≤ bound k ^ p := fun j _ =>
      Real.rpow_le_rpow (norm_nonneg _) (norm_weight_le_bound k j) hp.le
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => by positivity) hstage ?_
  rw [← summable_nat_add_iff 1]
  exact summable_stage_rpow hp

theorem summable_norm_coef : Summable fun i : Idx => ‖coef i‖ := by
  have := summable_norm_coef_rpow (p := 1) one_pos
  simpa using this

/-! ## Vanishing moments -/

/-- The moment contribution of stage `k`. -/
def stageSum (m k : ℕ) : ℂ := ∑ j : Fin (count k), coef ⟨k, j⟩ * point ⟨k, j⟩ ^ m

theorem stageSum_zero (m : ℕ) : stageSum m 0 = residual 0 m := by
  unfold stageSum
  simp [count, coef, point, residual]

theorem stageSum_succ (m k : ℕ) : stageSum m (k + 1) = residual (k + 1) m - residual k m := by
  unfold stageSum
  rw [residual_succ, add_sub_cancel_left]
  exact Fin.sum_univ_eq_sum_range (fun j => weight k j * node k j ^ m) (nodeCount k)

theorem sum_range_stageSum (m K : ℕ) : ∑ k ∈ range (K + 1), stageSum m k = residual K m := by
  induction K with
  | zero => simp [stageSum_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, stageSum_succ]; ring

theorem residual_eq_zero_of_le {m k : ℕ} (hk : m ≤ k) : residual (k + 1) m = 0 := by
  apply residual_succ_eq_zero
  unfold nodeCount
  calc m ≤ k := hk
    _ < 2 ^ k := Nat.lt_two_pow_self
    _ ≤ 2 ^ (3 * k + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem hasSum_stageSum (m : ℕ) : HasSum (stageSum m) 0 := by
  have hzero : ∀ k ∉ range (m + 2), stageSum m k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [stageSum_succ, residual_eq_zero_of_le (by omega)]
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    rw [residual_eq_zero_of_le (by omega), sub_zero]
  have h : HasSum (stageSum m) (∑ b ∈ range (m + 2), stageSum m b) :=
    hasSum_sum_of_ne_finset_zero hzero
  rwa [sum_range_stageSum, residual_eq_zero_of_le le_rfl] at h

/-- **All moments vanish.** -/
theorem hasSum_coef_mul_point_pow (m : ℕ) : HasSum (fun i : Idx => coef i * point i ^ m) 0 := by
  have hsum : Summable fun i : Idx => coef i * point i ^ m := by
    refine Summable.of_norm_bounded (summable_norm_coef.mul_right ((10 : ℝ) ^ m)) fun i => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_point_le i) m)
      (norm_nonneg _)
  have hσ := hsum.hasSum.sigma (fun k => hasSum_fintype (fun j => coef ⟨k, j⟩ * point ⟨k, j⟩ ^ m))
  have heq : (fun k => ∑ j, coef ⟨k, j⟩ * point ⟨k, j⟩ ^ m) = stageSum m := rfl
  rw [heq] at hσ
  rw [← hσ.unique (hasSum_stageSum m)]
  exact hsum.hasSum

/-- **A nonzero discrete annihilating measure with `p`-summable weights for every `p > 0`.** -/
theorem exists_annihilating_discrete_measure :
    ∃ (ι : Type) (_ : Countable ι) (x : ι → ℂ) (c : ι → ℂ) (i₀ : ι), Function.Injective x ∧
      (∀ i, 5 / 4 ≤ ‖x i‖ ∧ ‖x i‖ ≤ 10) ∧ x i₀ = 5 / 4 ∧ c i₀ = 1 ∧
      (∀ i, i ≠ i₀ → 4 / 3 ≤ ‖x i‖) ∧ (∀ i, ‖c i‖ ≤ 1) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => ‖c i‖ ^ p) ∧
      ∀ m : ℕ, HasSum (fun i => c i * x i ^ m) 0 :=
  ⟨Idx, inferInstance, point, coef, base, point_injective,
    fun i => ⟨norm_point_ge i, norm_point_le i⟩, rfl, rfl, fun _ hi => four_thirds_le_norm_point hi,
    norm_coef_le, fun _ hp => summable_norm_coef_rpow hp, hasSum_coef_mul_point_pow⟩

/-! ## The node series -/

/-- **The node series vanishes near the origin.** For `|t| < 1/10`,
`Σ_i c_i/(1 − t x_i) = Σ_m t^m Σ_i c_i x_i^m = 0`. -/
theorem tsum_coef_div_eq_zero {t : ℂ} (ht : ‖t‖ < 1 / 10) :
    ∑' i : Idx, coef i / (1 - t * point i) = 0 := by
  set r : ℝ := 10 * ‖t‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxt : ∀ i, ‖t * point i‖ ≤ r := fun i => by
    rw [norm_mul, hr]; nlinarith [norm_point_le i, norm_nonneg t]
  have hsumU : Summable (Function.uncurry fun (i : Idx) (m : ℕ) => coef i * (t * point i) ^ m) := by
    refine Summable.of_norm_bounded (summable_norm_coef.mul_of_nonneg
      (summable_geometric_of_lt_one hr0 hr1) (fun _ => norm_nonneg _) (fun _ => by positivity))
      (fun q => ?_)
    show ‖coef q.1 * (t * point q.1) ^ q.2‖ ≤ ‖coef q.1‖ * r ^ q.2
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hxt _) _) (norm_nonneg _)
  have hinner : ∀ i : Idx, ∑' m : ℕ, coef i * (t * point i) ^ m = coef i / (1 - t * point i) := by
    intro i
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one ((hxt i).trans_lt hr1), div_eq_mul_inv]
  have hcol : ∀ m : ℕ, ∑' i : Idx, coef i * (t * point i) ^ m = 0 := by
    intro m
    have e : (fun i : Idx => coef i * (t * point i) ^ m) =
        fun i => t ^ m * (coef i * point i ^ m) := by
      funext i; ring
    rw [e, tsum_mul_left, (hasSum_coef_mul_point_pow m).tsum_eq, mul_zero]
  calc ∑' i : Idx, coef i / (1 - t * point i)
      = ∑' i : Idx, ∑' m : ℕ, coef i * (t * point i) ^ m := tsum_congr fun i => (hinner i).symm
    _ = ∑' m : ℕ, ∑' i : Idx, coef i * (t * point i) ^ m := hsumU.tsum_comm.symm
    _ = 0 := by simp only [hcol, tsum_zero]

/-- **The node series has a simple pole at the isolated node `4/5`.** For
`0 < |t − 4/5| < 1/40`, `|Σ_i c_i/(1 − t x_i)| ≥ (4/5)/|t − 4/5| − 30 Σ_i |c_i|`. So the series
agrees with the analytic function `0` on the disc `|t| < 1/10` (`tsum_coef_div_eq_zero`) but on no
small circle around `4/5`. -/
theorem norm_tsum_coef_div_ge {t : ℂ} (h1 : 0 < ‖t - 4 / 5‖) (h2 : ‖t - 4 / 5‖ < 1 / 40) :
    4 / 5 / ‖t - 4 / 5‖ - 30 * ∑' i : Idx, ‖coef i‖ ≤ ‖∑' i : Idx, coef i / (1 - t * point i)‖ := by
  classical
  have ht : (31 / 40 : ℝ) ≤ ‖t‖ := by
    have h45 : ‖(4 / 5 : ℂ)‖ = 4 / 5 := by
      rw [show (4 / 5 : ℂ) = ((4 / 5 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have h := norm_sub_norm_le (4 / 5 : ℂ) (4 / 5 - t)
    rw [sub_sub_cancel, norm_sub_rev, h45] at h
    linarith
  have hfar : ∀ i : Idx, i ≠ base → ‖coef i / (1 - t * point i)‖ ≤ 30 * ‖coef i‖ := by
    intro i hi
    have hx := four_thirds_le_norm_point hi
    have hden : (1 / 30 : ℝ) ≤ ‖1 - t * point i‖ := by
      have h := norm_sub_norm_le (t * point i) 1
      rw [norm_mul, norm_one, norm_sub_rev] at h
      nlinarith [norm_nonneg t, norm_nonneg (point i)]
    rw [norm_div, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (coef i)]
  set g : Idx → ℂ := fun i => coef i / (1 - t * point i) with hg
  have hgs : Summable g := by
    refine Summable.of_norm_bounded_eventually (summable_norm_coef.mul_left 30) ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton base).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq, not_le] at hi
    by_contra hne
    exact (not_le.mpr hi) (hfar i hne)
  rw [hgs.tsum_eq_add_tsum_ite base]
  have hbase : g base = 1 / (1 - t * (5 / 4)) := rfl
  have hbase_norm : ‖g base‖ = 4 / 5 / ‖t - 4 / 5‖ := by
    rw [hbase, show (1 : ℂ) - t * (5 / 4) = -(5 / 4) * (t - 4 / 5) by ring, norm_div, norm_one,
      norm_mul, norm_neg]
    have h54 : ‖(5 / 4 : ℂ)‖ = 5 / 4 := norm_five_fourths
    rw [h54]
    field_simp
  have hrest : ‖∑' n : Idx, (if n = base then 0 else g n)‖ ≤ 30 * ∑' i : Idx, ‖coef i‖ := by
    have hb : ∀ n : Idx, ‖(if n = base then 0 else g n)‖ ≤ 30 * ‖coef n‖ := by
      intro n
      split_ifs with hn
      · rw [norm_zero]; positivity
      · exact hfar n hn
    have hs : Summable fun n : Idx => ‖(if n = base then 0 else g n)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (summable_norm_coef.mul_left 30)
    calc ‖∑' n : Idx, (if n = base then 0 else g n)‖
        ≤ ∑' n : Idx, ‖(if n = base then 0 else g n)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : Idx, 30 * ‖coef n‖ := hs.tsum_le_tsum hb (summable_norm_coef.mul_left 30)
      _ = 30 * ∑' i : Idx, ‖coef i‖ := tsum_mul_left
  have htri := norm_sub_norm_le (g base) (-(∑' n : Idx, (if n = base then 0 else g n)))
  rw [sub_neg_eq_add, norm_neg, hbase_norm] at htri
  linarith

end

end GaloisForLFunctions.HTGeometry.CircleQuadratureAnnihilating
