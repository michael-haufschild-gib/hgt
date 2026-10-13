import GaloisForLFunctions.HTGeometry.CircleQuadratureAnnihilatingMeasure

/-!
# Positive discrete measures with vanishing moments and `p`-summable weights

There is a discrete measure `Σ_i c_i δ_{x_i}` with pairwise distinct nodes in `5/4 ≤ |x| ≤ 10` and
**positive** weights `c_i > 0` with `Σ_i c_i^p < ∞` for every `p > 0`, all of whose moments
`Σ_i c_i x_i^m`, `m ≥ 1`, vanish (`exists_positive_wolff_measure_pSummable`).

**Construction (real circle quadrature).** Start from the unit mass at `5/4`, with residual moments
`E_0(m) = (5/4)^m`. Stage `k` puts `2N_k` nodes `R_k ζ_k^j` on the circle of radius `R_k`, where
`ζ_k` is a primitive `2N_k`-th root of unity, with the real weights

`w_{k,j} = 2L_k − N_k^{−1} Re Σ_{1 ≤ i < N_k} E_k(i) (R_k ζ_k^j)^{−i}`.

* For `1 ≤ m < N_k`, orthogonality of the `2N_k`-th roots of unity gives
  `Σ_j w_{k,j}(R_k ζ_k^j)^m = −E_k(m)`. The conjugate half of the real part contributes the
  exponents `m + i ∈ (1, 2N_k)`, where the root sums vanish (`sum_pweight_mul_pnode_pow`).
* If `|E_k(m)| ≤ L_k R_k^m` for `m ≥ 1`, then `L_k ≤ w_{k,j} ≤ 3L_k` (`pweight_mem_Icc`).
* For `m ≥ N_k` the radius gain `(R_k/R_{k+1})^{N_k} ≤ 2^{−4^{k+4}}` of `CircleQuadratureAnnihilating`
  gives `|E_{k+1}(m)| ≤ L_{k+1} R_{k+1}^m` with `L_{k+1} = (6N_k + 1) 2^{−4^{k+4}} L_k`.
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.CircleQuadraturePositive

open CircleQuadratureAnnihilating

/-! ## Stage data -/

/-- Number of nodes of stage `k`: `2N_k`. -/
def polySize (k : ℕ) : ℕ := 2 * nodeCount k

theorem polySize_pos (k : ℕ) : 0 < polySize k := by unfold polySize; have := nodeCount_pos k; omega

/-- A primitive `2N_k`-th root of unity. -/
def proot (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (polySize k : ℂ))

/-- The nodes `R_k ζ_k^j`. -/
def pnode (k j : ℕ) : ℂ := (radius k : ℂ) * proot k ^ j

/-- The residual bounds `L_0 = 1`, `L_{k+1} = (6N_k + 1) L_k / 2^{a_k}`. -/
def pbound : ℕ → ℝ
  | 0 => 1
  | k + 1 => (6 * (nodeCount k : ℝ) + 1) * pbound k / 2 ^ gainExp k

/-- Residual moments: `E_0(m) = (5/4)^m`, `E_{k+1}(m) = E_k(m) + Σ_j w_{k,j} (R_k ζ_k^j)^m`. -/
def presidual : ℕ → ℕ → ℂ
  | 0, m => (5 / 4 : ℂ) ^ m
  | k + 1, m => presidual k m + ∑ j ∈ range (polySize k),
      ((2 * pbound k - (1 / (nodeCount k : ℝ)) *
        (∑ i ∈ Ico 1 (nodeCount k), presidual k i / pnode k j ^ i).re : ℝ) : ℂ) * pnode k j ^ m

/-- The real weights of stage `k`. -/
def pweight (k j : ℕ) : ℝ :=
  2 * pbound k - (1 / (nodeCount k : ℝ)) * (∑ i ∈ Ico 1 (nodeCount k), presidual k i / pnode k j ^ i).re

theorem presidual_succ (k m : ℕ) :
    presidual (k + 1) m = presidual k m + ∑ j ∈ range (polySize k), (pweight k j : ℂ) * pnode k j ^ m :=
  rfl

/-! ## Roots of unity -/

theorem isPrimitiveRoot_proot (k : ℕ) : IsPrimitiveRoot (proot k) (polySize k) :=
  Complex.isPrimitiveRoot_exp _ (polySize_pos k).ne'

theorem norm_proot (k : ℕ) : ‖proot k‖ = 1 :=
  (isPrimitiveRoot_proot k).norm'_eq_one (polySize_pos k).ne'

theorem norm_pnode (k j : ℕ) : ‖pnode k j‖ = radius k := by
  unfold pnode
  rw [norm_mul, norm_pow, norm_proot, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radius_pos k)]

theorem pnode_ne_zero (k j : ℕ) : pnode k j ≠ 0 := by
  intro h
  have := norm_pnode k j
  rw [h, norm_zero] at this
  linarith [radius_pos k]

/-- `Σ_{j < 2N_k} (R_k ζ_k^j)^n = 0` for `0 < n < 2N_k`. -/
theorem sum_pnode_pow_eq_zero (k : ℕ) {n : ℕ} (h0 : 0 < n) (hn : n < polySize k) :
    ∑ j ∈ range (polySize k), pnode k j ^ n = 0 := by
  have hζ := isPrimitiveRoot_proot k
  have hpow : ∀ j, pnode k j ^ n = (radius k : ℂ) ^ n * (proot k ^ n) ^ j := by
    intro j; unfold pnode; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j n]
  simp_rw [hpow]
  rw [← Finset.mul_sum]
  have hne : proot k ^ n ≠ 1 := hζ.pow_ne_one_of_pos_of_lt h0.ne' hn
  rw [geom_sum_eq hne, ← pow_mul, mul_comm n, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div,
    mul_zero]

/-- Orthogonality: `Σ_j (R ζ^j)^m/(R ζ^j)^i = 2N_k [m = i]` for `m, i < N_k`. -/
theorem sum_pnode_pow_div (k : ℕ) {m i : ℕ} (hm : m < nodeCount k) (hi : i < nodeCount k) :
    ∑ j ∈ range (polySize k), pnode k j ^ m / pnode k j ^ i =
      if m = i then (polySize k : ℂ) else 0 := by
  split_ifs with hmi
  · subst hmi
    rw [Finset.sum_congr rfl (fun j _ => div_self (pow_ne_zero _ (pnode_ne_zero k j))),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hζ := isPrimitiveRoot_proot k
    have hR : (radius k : ℂ) ≠ 0 := by exact_mod_cast (radius_pos k).ne'
    have hPow : ∀ j, pnode k j ^ polySize k = (radius k : ℂ) ^ polySize k := by
      intro j
      unfold pnode
      rw [mul_pow, ← pow_mul, mul_comm j, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hRP : (radius k : ℂ) ^ polySize k ≠ 0 := pow_ne_zero _ hR
    rcases lt_or_gt_of_ne hmi with hlt | hgt
    · set d := i - m with hd
      have hdP : d < polySize k := by unfold polySize; omega
      have hterm : ∀ j, pnode k j ^ m / pnode k j ^ i =
          pnode k j ^ (polySize k - d) / (radius k : ℂ) ^ polySize k := by
        intro j
        rw [div_eq_div_iff (pow_ne_zero _ (pnode_ne_zero k j)) hRP, ← hPow j, ← pow_add, ← pow_add]
        congr 1
        omega
      simp_rw [hterm]
      rw [← Finset.sum_div, sum_pnode_pow_eq_zero k (by omega) (by omega), zero_div]
    · set d := m - i with hd
      have hterm : ∀ j, pnode k j ^ m / pnode k j ^ i = pnode k j ^ d := by
        intro j
        have hm' : m = i + d := by omega
        rw [hm', pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ (pnode_ne_zero k j))]
      simp_rw [hterm]
      exact sum_pnode_pow_eq_zero k (by omega) (by unfold polySize; omega)

/-- `conj (R ζ^j) = R² / (R ζ^j)`. -/
theorem conj_pnode (k j : ℕ) : (starRingEnd ℂ) (pnode k j) = (radius k : ℂ) ^ 2 / pnode k j := by
  rw [eq_div_iff (pnode_ne_zero k j), mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    norm_pnode]
  push_cast; ring

/-! ## The moment identity -/

/-- The correction sum `S_{k,j} = Σ_{1 ≤ i < N_k} E_k(i)/(R_k ζ_k^j)^i`. -/
def pS (k j : ℕ) : ℂ := ∑ i ∈ Ico 1 (nodeCount k), presidual k i / pnode k j ^ i

theorem pweight_eq (k j : ℕ) :
    (pweight k j : ℂ) = 2 * (pbound k : ℂ) - (pS k j + (starRingEnd ℂ) (pS k j)) / (2 * nodeCount k) := by
  have hre : ((pS k j).re : ℂ) = (pS k j + (starRingEnd ℂ) (pS k j)) / 2 := Complex.re_eq_add_conj _
  unfold pweight
  rw [← pS]
  push_cast
  rw [hre]
  ring

theorem sum_const_mul_pnode_pow (k : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < nodeCount k) (c : ℂ) :
    ∑ j ∈ range (polySize k), c * pnode k j ^ m = 0 := by
  rw [← Finset.mul_sum, sum_pnode_pow_eq_zero k (by omega) (by unfold polySize; omega), mul_zero]

theorem sum_pS_mul_pnode_pow (k : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ j ∈ range (polySize k), pS k j * pnode k j ^ m = (polySize k : ℂ) * presidual k m := by
  simp only [pS, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ i ∈ Ico 1 (nodeCount k), ∑ j ∈ range (polySize k),
      presidual k i / pnode k j ^ i * pnode k j ^ m =
        presidual k i * (if m = i then (polySize k : ℂ) else 0) := by
    intro i hi
    rw [← sum_pnode_pow_div k hm (Finset.mem_Ico.mp hi).2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl hterm]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (Ico 1 (nodeCount k)) m, if_pos (Finset.mem_Ico.mpr ⟨hm1, hm⟩)]
  ring

theorem conj_pS (k j : ℕ) : (starRingEnd ℂ) (pS k j) = ∑ i ∈ Ico 1 (nodeCount k),
    (starRingEnd ℂ) (presidual k i) / ((radius k : ℂ) ^ 2) ^ i * pnode k j ^ i := by
  simp only [pS, map_sum, map_div₀, map_pow, conj_pnode]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := pnode_ne_zero k j
  have hR : (radius k : ℂ) ≠ 0 := by exact_mod_cast (radius_pos k).ne'
  rw [div_pow]
  field_simp

theorem sum_conj_pS_mul_pnode_pow (k : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ j ∈ range (polySize k), (starRingEnd ℂ) (pS k j) * pnode k j ^ m = 0 := by
  simp_rw [conj_pS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := Finset.mem_Ico.mp hi
  have hfac : ∀ j, (starRingEnd ℂ) (presidual k i) / ((radius k : ℂ) ^ 2) ^ i * pnode k j ^ i *
      pnode k j ^ m = (starRingEnd ℂ) (presidual k i) / ((radius k : ℂ) ^ 2) ^ i *
        pnode k j ^ (i + m) := fun j => by rw [pow_add]; ring
  simp_rw [hfac]
  rw [← Finset.mul_sum, sum_pnode_pow_eq_zero k (by omega) (by unfold polySize; omega), mul_zero]

/-- **Stage `k` cancels the residual moments `1 ≤ m < N_k`.** -/
theorem sum_pweight_mul_pnode_pow (k : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ j ∈ range (polySize k), (pweight k j : ℂ) * pnode k j ^ m = -presidual k m := by
  have hN : (nodeCount k : ℂ) ≠ 0 := by exact_mod_cast (nodeCount_pos k).ne'
  have hP : (polySize k : ℂ) = 2 * nodeCount k := by unfold polySize; push_cast; ring
  have hpt : ∀ j ∈ range (polySize k), (pweight k j : ℂ) * pnode k j ^ m =
      2 * (pbound k : ℂ) * pnode k j ^ m - (1 / (2 * nodeCount k : ℂ)) *
        (pS k j * pnode k j ^ m + (starRingEnd ℂ) (pS k j) * pnode k j ^ m) := by
    intro j _
    rw [pweight_eq]
    ring
  have e2 : ∑ j ∈ range (polySize k), (1 / (2 * nodeCount k : ℂ)) *
      (pS k j * pnode k j ^ m + (starRingEnd ℂ) (pS k j) * pnode k j ^ m) =
      (1 / (2 * nodeCount k : ℂ)) * (∑ j ∈ range (polySize k), pS k j * pnode k j ^ m +
        ∑ j ∈ range (polySize k), (starRingEnd ℂ) (pS k j) * pnode k j ^ m) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, e2, sum_const_mul_pnode_pow k hm1 hm,
    sum_pS_mul_pnode_pow k hm1 hm, sum_conj_pS_mul_pnode_pow k hm1 hm, hP]
  field_simp
  ring

theorem presidual_succ_eq_zero (k : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < nodeCount k) :
    presidual (k + 1) m = 0 := by
  rw [presidual_succ, sum_pweight_mul_pnode_pow k hm1 hm, add_neg_cancel]

/-! ## Bounds -/

theorem pbound_pos : ∀ k, 0 < pbound k
  | 0 => by norm_num [pbound]
  | k + 1 => by
    show 0 < (6 * (nodeCount k : ℝ) + 1) * pbound k / 2 ^ gainExp k
    have := pbound_pos k
    positivity

/-- Under the residual bound, the weights lie in `[L_k, 3L_k]`. -/
theorem pweight_mem_Icc {k : ℕ} (h : ∀ m, 1 ≤ m → ‖presidual k m‖ ≤ pbound k * radius k ^ m)
    (j : ℕ) : pbound k ≤ pweight k j ∧ pweight k j ≤ 3 * pbound k := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  set S := ∑ i ∈ Ico 1 (nodeCount k), presidual k i / pnode k j ^ i with hS
  have hSb : ‖S‖ ≤ (nodeCount k : ℝ) * pbound k := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ico 1 (nodeCount k), ‖presidual k i / pnode k j ^ i‖ ≤ pbound k := by
      intro i hi
      rw [norm_div, norm_pow, norm_pnode, div_le_iff₀ (pow_pos (radius_pos k) _)]
      exact h i (Finset.mem_Ico.mp hi).1
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (pbound_pos k).le
    exact_mod_cast Nat.sub_le _ _
  have hre : |S.re| ≤ (nodeCount k : ℝ) * pbound k := (Complex.abs_re_le_norm S).trans hSb
  have hcorr : |1 / (nodeCount k : ℝ) * S.re| ≤ pbound k := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / nodeCount k)]
    calc 1 / (nodeCount k : ℝ) * |S.re| ≤ 1 / (nodeCount k : ℝ) * ((nodeCount k : ℝ) * pbound k) :=
          mul_le_mul_of_nonneg_left hre (by positivity)
      _ = pbound k := by field_simp
  unfold pweight
  rw [← hS]
  constructor <;> linarith [abs_le.mp hcorr]

/-- **The residual moments are controlled at every stage.** -/
theorem norm_presidual_le : ∀ k m, 1 ≤ m → ‖presidual k m‖ ≤ pbound k * radius k ^ m
  | 0, m, _ => by
    show ‖(5 / 4 : ℂ) ^ m‖ ≤ 1 * (4 / 3 : ℝ) ^ m
    rw [norm_pow, one_mul, norm_five_fourths]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
  | k + 1, m, hm1 => by
    have ih := norm_presidual_le k
    by_cases hm : m < nodeCount k
    · rw [presidual_succ_eq_zero k hm1 hm, norm_zero]
      exact mul_nonneg (pbound_pos _).le (pow_nonneg (radius_pos _).le _)
    · push Not at hm
      have hw := pweight_mem_Icc ih
      have hR0 : 0 ≤ radius k ^ m := pow_nonneg (radius_pos k).le _
      have hsum : ‖∑ j ∈ range (polySize k), (pweight k j : ℂ) * pnode k j ^ m‖ ≤
          (polySize k : ℝ) * (3 * pbound k * radius k ^ m) := by
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ j ∈ range (polySize k), ‖(pweight k j : ℂ) * pnode k j ^ m‖ ≤
            3 * pbound k * radius k ^ m := by
          intro j _
          rw [norm_mul, norm_pow, norm_pnode, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (lt_of_lt_of_le (pbound_pos k) (hw j).1)]
          exact mul_le_mul_of_nonneg_right (hw j).2 hR0
        refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
        rw [Finset.card_range, nsmul_eq_mul]
      have hgain := two_pow_mul_radius_pow_le hm
      have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
      have hL0 := (pbound_pos k).le
      have hPs : (polySize k : ℝ) = 2 * nodeCount k := by unfold polySize; push_cast; ring
      calc ‖presidual (k + 1) m‖
          ≤ ‖presidual k m‖ + ‖∑ j ∈ range (polySize k), (pweight k j : ℂ) * pnode k j ^ m‖ := by
            rw [presidual_succ]; exact norm_add_le _ _
        _ ≤ pbound k * radius k ^ m + (polySize k : ℝ) * (3 * pbound k * radius k ^ m) :=
            add_le_add (ih m hm1) hsum
        _ = (6 * (nodeCount k : ℝ) + 1) * pbound k / 2 ^ gainExp k *
              (2 ^ gainExp k * radius k ^ m) := by rw [hPs]; field_simp; ring
        _ ≤ (6 * (nodeCount k : ℝ) + 1) * pbound k / 2 ^ gainExp k * radius (k + 1) ^ m :=
            mul_le_mul_of_nonneg_left hgain (by positivity)
        _ = pbound (k + 1) * radius (k + 1) ^ m := rfl

theorem pweight_mem_Icc' (k j : ℕ) : pbound k ≤ pweight k j ∧ pweight k j ≤ 3 * pbound k :=
  pweight_mem_Icc (norm_presidual_le k) j

theorem pweight_pos (k j : ℕ) : 0 < pweight k j :=
  lt_of_lt_of_le (pbound_pos k) (pweight_mem_Icc' k j).1

/-! ## Explicit decay of the bounds -/

theorem quadratic_le_four_pow' (k : ℕ) : 3 * k ^ 2 + 20 * k + 23 ≤ 4 ^ (k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ (4 : ℕ) (k + 4)]
    nlinarith

theorem six_nodeCount_add_one_le (k : ℕ) : 6 * (nodeCount k : ℝ) + 1 ≤ 2 ^ (3 * k + 11) := by
  unfold nodeCount
  have h : (1 : ℝ) ≤ 2 ^ (3 * k + 8) := one_le_pow₀ (by norm_num)
  push_cast
  rw [show (2 : ℝ) ^ (3 * k + 11) = 2 ^ (3 * k + 8) * 8 by
    rw [show 3 * k + 11 = (3 * k + 8) + 3 by ring, pow_add]; norm_num]
  linarith

theorem pbound_le_one : ∀ k, pbound k ≤ 1
  | 0 => by norm_num [pbound]
  | k + 1 => by
    show (6 * (nodeCount k : ℝ) + 1) * pbound k / 2 ^ gainExp k ≤ 1
    have hb := pbound_le_one k
    have hb0 := (pbound_pos k).le
    have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
    rw [div_le_one h2]
    have hexp : 3 * k + 11 ≤ gainExp k := by
      have := quadratic_le_four_pow' k; unfold gainExp; nlinarith
    have hpow : (2 : ℝ) ^ (3 * k + 11) ≤ 2 ^ gainExp k := pow_le_pow_right₀ (by norm_num) hexp
    have := six_nodeCount_add_one_le k
    calc (6 * (nodeCount k : ℝ) + 1) * pbound k ≤ (6 * (nodeCount k : ℝ) + 1) * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 ^ gainExp k := by linarith

/-- `L_{k+1} ≤ 2^{−((3k+12)(k+1) + 2k)}`. -/
theorem pbound_succ_le (k : ℕ) :
    pbound (k + 1) ≤ (1 / 2 : ℝ) ^ ((3 * k + 12) * (k + 1) + 2 * k) := by
  show (6 * (nodeCount k : ℝ) + 1) * pbound k / 2 ^ gainExp k ≤ _
  set E := (3 * k + 12) * (k + 1) + 2 * k with hE
  have hexp : E + (3 * k + 11) ≤ gainExp k := by
    have := quadratic_le_four_pow' k; unfold gainExp; rw [hE]; nlinarith
  have hb := pbound_le_one k
  have hb0 := (pbound_pos k).le
  have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
  rw [div_le_iff₀ h2, one_div_pow]
  have hpow : (2 : ℝ) ^ (E + (3 * k + 11)) ≤ 2 ^ gainExp k := pow_le_pow_right₀ (by norm_num) hexp
  rw [pow_add] at hpow
  have h2E : (0 : ℝ) < 2 ^ E := by positivity
  have := six_nodeCount_add_one_le k
  calc (6 * (nodeCount k : ℝ) + 1) * pbound k ≤ 2 ^ (3 * k + 11) := by nlinarith
    _ = 1 / 2 ^ E * (2 ^ E * 2 ^ (3 * k + 11)) := by field_simp
    _ ≤ 1 / 2 ^ E * 2 ^ gainExp k := mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## The configuration -/

/-- Stage sizes: one base node, then `2N_k` circle nodes. -/
def pcount : ℕ → ℕ
  | 0 => 1
  | k + 1 => polySize k

/-- The index type. -/
abbrev PIdx := Σ k : ℕ, Fin (pcount k)

/-- The nodes. -/
def ppoint : PIdx → ℂ
  | ⟨0, _⟩ => 5 / 4
  | ⟨k + 1, j⟩ => pnode k j

/-- The weights. -/
def pcoef : PIdx → ℝ
  | ⟨0, _⟩ => 1
  | ⟨k + 1, j⟩ => pweight k j

theorem pcoef_pos (i : PIdx) : 0 < pcoef i := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show (0 : ℝ) < 1; norm_num
  | succ k => exact pweight_pos k j

theorem pcoef_le_one (i : PIdx) : pcoef i ≤ 3 := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show (1 : ℝ) ≤ 3; norm_num
  | succ k =>
    show pweight k j ≤ 3
    linarith [(pweight_mem_Icc' k j).2, pbound_le_one k]

theorem norm_ppoint_ge (i : PIdx) : 5 / 4 ≤ ‖ppoint i‖ := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show 5 / 4 ≤ ‖(5 / 4 : ℂ)‖; rw [norm_five_fourths]
  | succ k =>
    show 5 / 4 ≤ ‖pnode k j‖
    rw [norm_pnode]; linarith [four_thirds_le_radius k]

theorem norm_ppoint_le (i : PIdx) : ‖ppoint i‖ ≤ 10 := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show ‖(5 / 4 : ℂ)‖ ≤ 10; rw [norm_five_fourths]; norm_num
  | succ k => show ‖pnode k j‖ ≤ 10; rw [norm_pnode]; exact radius_le_ten k

theorem ppoint_injective : Function.Injective ppoint := by
  rintro ⟨ka, ja⟩ ⟨kb, jb⟩ h
  cases ka with
  | zero =>
    cases kb with
    | zero =>
      congr
      exact Subsingleton.elim (α := Fin 1) _ _
    | succ kb =>
      exfalso
      have h' : (5 / 4 : ℂ) = pnode kb jb := h
      have := congrArg norm h'
      rw [norm_five_fourths, norm_pnode] at this
      linarith [four_thirds_le_radius kb]
  | succ ka =>
    cases kb with
    | zero =>
      exfalso
      have h' : pnode ka ja = (5 / 4 : ℂ) := h
      have := congrArg norm h'
      rw [norm_five_fourths, norm_pnode] at this
      linarith [four_thirds_le_radius ka]
    | succ kb =>
      have h' : pnode ka ja = pnode kb jb := h
      have hk : ka = kb := by
        have := congrArg norm h'
        rw [norm_pnode, norm_pnode] at this
        exact strictMono_radius.injective this
      subst hk
      have hr : (radius ka : ℂ) ≠ 0 := by exact_mod_cast (radius_pos ka).ne'
      have hpow : proot ka ^ (ja : ℕ) = proot ka ^ (jb : ℕ) := by
        unfold pnode at h'
        exact mul_left_cancel₀ hr h'
      have hj := (isPrimitiveRoot_proot ka).pow_inj ja.isLt jb.isLt hpow
      have : ja = jb := Fin.ext hj
      subst this
      rfl

/-! ## Summability -/

theorem summable_pstage_base {p : ℝ} (hp : 0 < p) :
    Summable fun k : ℕ => (polySize (k + 1) : ℝ) * pbound (k + 1) ^ p := by
  have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * p) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (2 * p) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0 hq1) ?_
  filter_upwards [eventually_ge_atTop ⌈1 / p⌉₊] with k hk
  have hkp : 1 ≤ p * ((k : ℝ) + 1) := by
    have h1 : 1 / p ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have h2 : 1 / p * p = 1 := by field_simp
    nlinarith
  have hb0 := (pbound_pos (k + 1)).le
  set E : ℕ := (3 * k + 12) * (k + 1) + 2 * k with hE
  have hbE := pbound_succ_le k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : pbound (k + 1) ^ p ≤ ((1 / 2 : ℝ) ^ E) ^ p := Real.rpow_le_rpow hb0 hbE hp.le
  have h2 : ((1 / 2 : ℝ) ^ E) ^ p = (2 : ℝ) ^ (-((E : ℝ) * p)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
  have h3 : (polySize (k + 1) : ℝ) = (2 : ℝ) ^ ((3 * k + 12 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; unfold polySize nodeCount; push_cast; ring_nf
  have h4 : ((1 / 2 : ℝ) ^ (2 * p)) ^ k = (2 : ℝ) ^ (-(2 * p * k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
  rw [h4]
  calc (polySize (k + 1) : ℝ) * pbound (k + 1) ^ p
      ≤ (polySize (k + 1) : ℝ) * (2 : ℝ) ^ (-((E : ℝ) * p)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 : ℝ) ^ (((3 * k + 12 : ℕ) : ℝ) + -((E : ℝ) * p)) := by
        rw [h3, ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (-(2 * p * k)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hE]
        push_cast
        nlinarith

theorem summable_pstage_rpow {p : ℝ} (hp : 0 < p) :
    Summable fun k : ℕ => (polySize (k + 1) : ℝ) * (3 * pbound (k + 1)) ^ p := by
  refine ((summable_pstage_base hp).mul_left ((3 : ℝ) ^ p)).congr fun k => ?_
  rw [Real.mul_rpow (by norm_num) (pbound_pos _).le]
  ring

theorem summable_pcoef_rpow {p : ℝ} (hp : 0 < p) : Summable fun i : PIdx => pcoef i ^ p := by
  rw [summable_sigma_of_nonneg (fun i => Real.rpow_nonneg (pcoef_pos i).le _)]
  refine ⟨fun k => Summable.of_finite, ?_⟩
  rw [← summable_nat_add_iff 1]
  have hstage : ∀ k : ℕ, ∑' j : Fin (pcount (k + 1)), pcoef ⟨k + 1, j⟩ ^ p ≤
      (polySize k : ℝ) * (3 * pbound k) ^ p := by
    intro k
    rw [tsum_fintype]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (polySize k))),
        pweight k j ^ p ≤ (3 * pbound k) ^ p := fun j _ =>
      Real.rpow_le_rpow (pweight_pos k j).le (pweight_mem_Icc' k j).2 hp.le
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun j => Real.rpow_nonneg (pcoef_pos _).le _)
    hstage ?_
  rw [← summable_nat_add_iff 1]
  exact summable_pstage_rpow hp

theorem summable_pcoef : Summable pcoef := by
  have := summable_pcoef_rpow (p := 1) one_pos
  simpa using this

/-! ## Vanishing moments -/

/-- The moment contribution of stage `k`. -/
def pstageSum (m k : ℕ) : ℂ := ∑ j : Fin (pcount k), (pcoef ⟨k, j⟩ : ℂ) * ppoint ⟨k, j⟩ ^ m

theorem pstageSum_zero (m : ℕ) : pstageSum m 0 = presidual 0 m := by
  unfold pstageSum
  simp [pcount, pcoef, ppoint, presidual]

theorem pstageSum_succ (m k : ℕ) : pstageSum m (k + 1) = presidual (k + 1) m - presidual k m := by
  unfold pstageSum
  rw [presidual_succ, add_sub_cancel_left]
  exact Fin.sum_univ_eq_sum_range (fun j => (pweight k j : ℂ) * pnode k j ^ m) (polySize k)

theorem sum_range_pstageSum (m K : ℕ) : ∑ k ∈ range (K + 1), pstageSum m k = presidual K m := by
  induction K with
  | zero => simp [pstageSum_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, pstageSum_succ]; ring

theorem presidual_eq_zero_of_le {m k : ℕ} (hm1 : 1 ≤ m) (hk : m ≤ k) : presidual (k + 1) m = 0 := by
  apply presidual_succ_eq_zero k hm1
  unfold nodeCount
  calc m ≤ k := hk
    _ < 2 ^ k := Nat.lt_two_pow_self
    _ ≤ 2 ^ (3 * k + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem hasSum_pstageSum {m : ℕ} (hm1 : 1 ≤ m) : HasSum (pstageSum m) 0 := by
  have hzero : ∀ k ∉ range (m + 2), pstageSum m k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pstageSum_succ, presidual_eq_zero_of_le hm1 (by omega)]
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    rw [presidual_eq_zero_of_le hm1 (by omega), sub_zero]
  have h : HasSum (pstageSum m) (∑ b ∈ range (m + 2), pstageSum m b) :=
    hasSum_sum_of_ne_finset_zero hzero
  rwa [sum_range_pstageSum, presidual_eq_zero_of_le hm1 (by omega)] at h

/-- **All moments `m ≥ 1` vanish.** -/
theorem hasSum_pcoef_mul_ppoint_pow {m : ℕ} (hm1 : 1 ≤ m) :
    HasSum (fun i : PIdx => (pcoef i : ℂ) * ppoint i ^ m) 0 := by
  have hsum : Summable fun i : PIdx => (pcoef i : ℂ) * ppoint i ^ m := by
    refine Summable.of_norm_bounded (summable_pcoef.mul_right ((10 : ℝ) ^ m)) fun i => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pcoef_pos i)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_ppoint_le i) m)
      (pcoef_pos i).le
  have hσ := hsum.hasSum.sigma
    (fun k => hasSum_fintype (fun j => (pcoef ⟨k, j⟩ : ℂ) * ppoint ⟨k, j⟩ ^ m))
  have heq : (fun k => ∑ j, (pcoef ⟨k, j⟩ : ℂ) * ppoint ⟨k, j⟩ ^ m) = pstageSum m := rfl
  rw [heq] at hσ
  rw [← hσ.unique (hasSum_pstageSum hm1)]
  exact hsum.hasSum

/-- **A positive discrete measure with vanishing moments and `p`-summable weights for every
`p > 0`.** -/
theorem exists_positive_wolff_measure_pSummable :
    ∃ (ι : Type) (_ : Countable ι) (x : ι → ℂ) (c : ι → ℝ), Function.Injective x ∧
      (∀ i, 5 / 4 ≤ ‖x i‖ ∧ ‖x i‖ ≤ 10) ∧ (∀ i, 0 < c i) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => c i ^ p) ∧
      ∀ m : ℕ, 1 ≤ m → HasSum (fun i => (c i : ℂ) * x i ^ m) 0 :=
  ⟨PIdx, inferInstance, ppoint, pcoef, ppoint_injective,
    fun i => ⟨norm_ppoint_ge i, norm_ppoint_le i⟩, pcoef_pos, fun _ hp => summable_pcoef_rpow hp,
    fun _ hm => hasSum_pcoef_mul_ppoint_pow hm⟩

end GaloisForLFunctions.HTGeometry.CircleQuadraturePositive
