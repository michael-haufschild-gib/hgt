import Mathlib
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# A separation-free lower bound for power sums

For complex numbers `z_1, …, z_N` of which at least one has `|z_i| ≥ 1`, and every `M ≥ 0`, some
exponent `M + 1 ≤ ν ≤ M + N` satisfies

`|z_1^ν + ⋯ + z_N^ν| ≥ 1 / (2e N (6(N+1)(M+2N+2))^N)`

(`exists_norm_powerSum_ge`; scaled form `exists_norm_powerSum_ge_scaled`).  This is Turán's second
main theorem for unit weights, with a constant of the same shape `exp(−O(N log(N(M+N))))`.  No
separation of the points is assumed: coincident and arbitrarily close points are allowed, and no
upper bound on the moduli is needed.

Mechanism.

* **Gap radius.**  Among `N + 1` disjoint annuli of width `2g`, `g = θ/(2(N+1))`, inside
  `1 − θ ≤ |x| ≤ 1`, one contains no `|z_i|`.  Its middle radius `r` splits the points into an outer
  group (`|z| ≥ r + g`, containing the point of modulus `1`) and an inner group (`|z| ≤ r − g`).
* **Newton reduction.**  In the reciprocal variable `y = 1/x`, reduce `y^m` modulo the outer
  reciprocals `u_l` in the Newton basis `N_k(y) = Π_{l<k}(y − u_l)`.  The Newton coefficients of
  `y^m` satisfy Pascal's rule with weights `u_k`, so they are bounded by `C(m,k) R^m` with
  `R = max |u_l|`, independently of the spacing of the nodes (`norm_newtonCoeff_le`).
* **Separating polynomial.**  `Q̃ = P̃ Ṽ` with `P̃(y) = Π_inner (1 − z_j y)` and `Ṽ` the Newton
  reduction of `y^{M+N} Π_inner Σ_{t≤J} (z_j y)^t`.  Then `Q(x) = x^{M+N} Q̃(1/x)` is a combination of
  `x^{M+1}, …, x^{M+N}` vanishing at every inner point and equal to `Π_j (1 − (z_j/z_o)^{J+1})` at
  every outer point `z_o`, which is `≈ 1` for large `J`.  So `Σ_ν q_ν s_ν = Σ_i Q(z_i)` has modulus
  `≥ 1/2`, while `Σ |q_ν|` is bounded through weighted coefficient norms (`wNorm_mul_le`).
-/

open Polynomial Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Weighted coefficient norms -/

/-- The coefficientwise absolute value of a complex polynomial. -/
def absPoly (p : ℂ[X]) : ℝ[X] := ∑ k ∈ range (p.natDegree + 1), C ‖p.coeff k‖ * X ^ k

theorem coeff_absPoly (p : ℂ[X]) (k : ℕ) : (absPoly p).coeff k = ‖p.coeff k‖ := by
  classical
  unfold absPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]

/-- The weighted coefficient norm `Σ_k |p_k| x^k`. -/
def wNorm (x : ℝ) (p : ℂ[X]) : ℝ := (absPoly p).eval x

theorem wNorm_eq_sum (x : ℝ) (p : ℂ[X]) :
    wNorm x p = ∑ k ∈ range (p.natDegree + 1), ‖p.coeff k‖ * x ^ k := by
  unfold wNorm absPoly
  rw [eval_finsetSum]
  simp

theorem wNorm_eq_sum_of_lt (x : ℝ) {p : ℂ[X]} {D : ℕ} (hD : p.natDegree < D) :
    wNorm x p = ∑ k ∈ range D, ‖p.coeff k‖ * x ^ k := by
  have hdeg : (absPoly p).natDegree < D := by
    refine lt_of_le_of_lt ?_ hD
    refine natDegree_le_iff_coeff_eq_zero.2 fun k hk => ?_
    rw [coeff_absPoly, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hk), norm_zero]
  unfold wNorm
  rw [eval_eq_sum_range' hdeg]
  simp only [coeff_absPoly]

theorem wNorm_nonneg {x : ℝ} (hx : 0 ≤ x) (p : ℂ[X]) : 0 ≤ wNorm x p := by
  rw [wNorm_eq_sum]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hx k)

theorem eval_le_eval_of_coeff_le {f g : ℝ[X]} {x : ℝ} (hx : 0 ≤ x)
    (hfg : ∀ k, f.coeff k ≤ g.coeff k) : f.eval x ≤ g.eval x := by
  rw [eval_eq_sum_range' (n := max f.natDegree g.natDegree + 1) (by omega),
    eval_eq_sum_range' (n := max f.natDegree g.natDegree + 1) (by omega)]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hfg k) (pow_nonneg hx k)

theorem wNorm_mul_le {x : ℝ} (hx : 0 ≤ x) (p q : ℂ[X]) :
    wNorm x (p * q) ≤ wNorm x p * wNorm x q := by
  unfold wNorm
  rw [← eval_mul]
  refine eval_le_eval_of_coeff_le hx fun k => ?_
  rw [coeff_absPoly, coeff_mul, coeff_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ij _ => ?_)
  rw [coeff_absPoly, coeff_absPoly, norm_mul]

theorem wNorm_add_le {x : ℝ} (hx : 0 ≤ x) (p q : ℂ[X]) :
    wNorm x (p + q) ≤ wNorm x p + wNorm x q := by
  unfold wNorm
  rw [← eval_add]
  refine eval_le_eval_of_coeff_le hx fun k => ?_
  rw [coeff_absPoly, coeff_add, coeff_add, coeff_absPoly, coeff_absPoly]
  exact norm_add_le _ _

theorem wNorm_zero (x : ℝ) : wNorm x 0 = 0 := by
  simp [wNorm, absPoly]

theorem wNorm_sum_le {x : ℝ} (hx : 0 ≤ x) {α : Type*} (S : Finset α) (f : α → ℂ[X]) :
    wNorm x (∑ a ∈ S, f a) ≤ ∑ a ∈ S, wNorm x (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [wNorm_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (wNorm_add_le hx _ _).trans (by linarith)

theorem wNorm_C_mul_le {x : ℝ} (hx : 0 ≤ x) (c : ℂ) (p : ℂ[X]) :
    wNorm x (C c * p) ≤ ‖c‖ * wNorm x p := by
  have h : wNorm x (C c * p) ≤ (C ‖c‖ * absPoly p).eval x := by
    unfold wNorm
    refine eval_le_eval_of_coeff_le hx fun k => ?_
    rw [coeff_absPoly, coeff_C_mul, coeff_C_mul, coeff_absPoly, norm_mul]
  simpa [wNorm, eval_mul] using h

theorem wNorm_C (x : ℝ) (c : ℂ) : wNorm x (C c) = ‖c‖ := by
  rw [wNorm_eq_sum_of_lt x (D := 1) (by rw [natDegree_C]; norm_num)]
  simp

theorem wNorm_X_pow (x : ℝ) (m : ℕ) : wNorm x (X ^ m : ℂ[X]) = x ^ m := by
  classical
  rw [wNorm_eq_sum_of_lt x (D := m + 1) (by rw [natDegree_X_pow]; omega)]
  simp only [coeff_X_pow]
  rw [Finset.sum_eq_single m (fun k _ hk => by simp [hk]) (fun h => by simp at h)]
  simp

/-- A linear factor has weighted norm at most `|a| + |b| x`. -/
theorem wNorm_linear_le {x : ℝ} (hx : 0 ≤ x) (a b : ℂ) :
    wNorm x (C a + C b * X) ≤ ‖a‖ + ‖b‖ * x := by
  refine (wNorm_add_le hx _ _).trans ?_
  rw [wNorm_C]
  have h := wNorm_C_mul_le hx b (X : ℂ[X])
  have hX : wNorm x (X : ℂ[X]) = x := by simpa using wNorm_X_pow x 1
  rw [hX] at h
  linarith

theorem wNorm_prod_le {x : ℝ} (hx : 0 ≤ x) {α : Type*} (S : Finset α) (f : α → ℂ[X]) :
    wNorm x (∏ a ∈ S, f a) ≤ ∏ a ∈ S, wNorm x (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, ← C_1, wNorm_C, norm_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (wNorm_mul_le hx _ _).trans
      (mul_le_mul_of_nonneg_left ih (wNorm_nonneg hx _))

/-! ## Newton coefficients -/

/-- Newton coefficients of `y^m` with respect to the nodes `u 0, u 1, …`:
`y^m ≡ Σ_k c_{m,k} N_k(y)` modulo `N_n` for every `n`. -/
def newtonPowerCoeff (u : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, k => if k = 0 then 1 else 0
  | m + 1, k => u k * newtonPowerCoeff u m k + if k = 0 then 0 else newtonPowerCoeff u m (k - 1)

/-- The Newton basis polynomial `N_k = Π_{l<k} (X − u_l)`. -/
def newtonBasis (u : ℕ → ℂ) (k : ℕ) : ℂ[X] := ∏ l ∈ range k, (X - C (u l))

theorem eval_newtonBasis_succ (u : ℕ → ℂ) (k : ℕ) (y : ℂ) :
    (newtonBasis u (k + 1)).eval y = (newtonBasis u k).eval y * (y - u k) := by
  simp [newtonBasis, Finset.prod_range_succ, eval_prod]

theorem newton_step (u : ℕ → ℂ) (m : ℕ) (y : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    y ^ (m + 1) - ∑ k ∈ range n, newtonPowerCoeff u (m + 1) k * (newtonBasis u k).eval y =
      y * (y ^ m - ∑ k ∈ range n, newtonPowerCoeff u m k * (newtonBasis u k).eval y) +
        newtonPowerCoeff u m (n - 1) * (newtonBasis u n).eval y := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [Finset.sum_range_one, newtonPowerCoeff, ↓reduceIte, add_zero, Nat.sub_self]
    rw [eval_newtonBasis_succ]
    simp only [newtonBasis, Finset.range_zero, Finset.prod_empty, eval_one]
    ring
  | succ n hn ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_sub_cancel]
    have hk : n ≠ 0 := by omega
    have hc : newtonPowerCoeff u (m + 1) n = u n * newtonPowerCoeff u m n + newtonPowerCoeff u m (n - 1) := by
      simp [newtonPowerCoeff, hk]
    rw [hc, eval_newtonBasis_succ]
    linear_combination ih

/-- At each of the first `n` nodes, `u_l^m` is the Newton sum of its first `n` terms. -/
theorem pow_eq_sum_newton (u : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) {l : ℕ} (hl : l < n) (m : ℕ) :
    u l ^ m = ∑ k ∈ range n, newtonPowerCoeff u m k * (newtonBasis u k).eval (u l) := by
  have hz : (newtonBasis u n).eval (u l) = 0 := by
    rw [newtonBasis, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.2 hl) (by simp)
  induction m with
  | zero =>
    rw [pow_zero, Finset.sum_eq_single 0]
    · simp [newtonPowerCoeff, newtonBasis]
    · intro k _ hk
      simp [newtonPowerCoeff, hk]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  | succ m ih =>
    have h := newton_step u m (u l) hn
    rw [hz, mul_zero, add_zero, ← ih, sub_self, mul_zero] at h
    exact (sub_eq_zero.1 h)

theorem norm_newtonCoeff_le {u : ℕ → ℂ} {R : ℝ} (hR : 1 ≤ R) (hu : ∀ l, ‖u l‖ ≤ R) (m k : ℕ) :
    ‖newtonPowerCoeff u m k‖ ≤ (m.choose k : ℝ) * R ^ m := by
  induction m generalizing k with
  | zero =>
    cases k with
    | zero => simp [newtonPowerCoeff]
    | succ k => simp [newtonPowerCoeff]
  | succ m ih =>
    have hRm : 0 ≤ R ^ m := pow_nonneg (by linarith) m
    cases k with
    | zero =>
      have h0 := ih 0
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h0
      simp only [newtonPowerCoeff, ↓reduceIte, add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
      rw [norm_mul, pow_succ]
      calc ‖u 0‖ * ‖newtonPowerCoeff u m 0‖ ≤ R * R ^ m :=
            mul_le_mul (hu 0) h0 (norm_nonneg _) (by linarith)
        _ = R ^ m * R := by ring
    | succ k =>
      have h1 := ih (k + 1)
      have h2 := ih k
      simp only [newtonPowerCoeff, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      have hc0 : (0 : ℝ) ≤ (m.choose (k + 1) : ℝ) := Nat.cast_nonneg _
      have hc1 : (0 : ℝ) ≤ (m.choose k : ℝ) := Nat.cast_nonneg _
      have hRR : R ^ m ≤ R ^ (m + 1) := pow_le_pow_right₀ hR (Nat.le_succ m)
      calc ‖u (k + 1) * newtonPowerCoeff u m (k + 1) + newtonPowerCoeff u m k‖
          ≤ R * ((m.choose (k + 1) : ℝ) * R ^ m) + (m.choose k : ℝ) * R ^ m := by
            refine (norm_add_le _ _).trans (add_le_add ?_ h2)
            rw [norm_mul]
            exact mul_le_mul (hu _) h1 (norm_nonneg _) (by linarith)
        _ ≤ (m.choose (k + 1) : ℝ) * R ^ (m + 1) + (m.choose k : ℝ) * R ^ (m + 1) := by
            have e : R * ((m.choose (k + 1) : ℝ) * R ^ m) = (m.choose (k + 1) : ℝ) * R ^ (m + 1) := by
              ring
            linarith [mul_le_mul_of_nonneg_left hRR hc1]
        _ = ((m + 1).choose (k + 1) : ℝ) * R ^ (m + 1) := by
            rw [Nat.choose_succ_succ']; push_cast; ring

/-- `C(m, k) η^k ≤ (1 + η)^m`. -/
theorem choose_mul_pow_le_one_add_pow {η : ℝ} (hη : 0 ≤ η) (m k : ℕ) :
    (m.choose k : ℝ) * η ^ k ≤ (1 + η) ^ m := by
  by_cases hk : k ≤ m
  · rw [add_comm, add_pow]
    have hmem : k ∈ range (m + 1) := Finset.mem_range.2 (by omega)
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => η ^ j * 1 ^ (m - j) * (m.choose j : ℝ))
      (fun j _ => by positivity) hmem)
    simp only [one_pow, mul_one]
    rw [mul_comm]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    positivity

/-! ## Newton reduction -/

/-- Newton reduction of `f` modulo the first `n` nodes. -/
def newtonReduce (u : ℕ → ℂ) (n : ℕ) (f : ℂ[X]) : ℂ[X] :=
  ∑ m ∈ range (f.natDegree + 1), C (f.coeff m) *
    ∑ k ∈ range n, C (newtonPowerCoeff u m k) * newtonBasis u k

theorem eval_newtonReduce (u : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) {l : ℕ} (hl : l < n) (f : ℂ[X]) :
    (newtonReduce u n f).eval (u l) = f.eval (u l) := by
  rw [newtonReduce, eval_finsetSum, eval_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_mul, eval_C, eval_finsetSum, pow_eq_sum_newton u hn hl m]
  simp only [eval_mul, eval_C]

theorem natDegree_newtonBasis_le (u : ℕ → ℂ) (k : ℕ) : (newtonBasis u k).natDegree ≤ k := by
  unfold newtonBasis
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun l _ => natDegree_X_sub_C (u l)]
  simp

theorem natDegree_newtonReduce_le (u : ℕ → ℂ) (n : ℕ) (f : ℂ[X]) :
    (newtonReduce u n f).natDegree ≤ n - 1 := by
  unfold newtonReduce
  refine natDegree_sum_le_of_forall_le _ _ fun m _ => (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => (natDegree_C_mul_le _ _).trans ?_
  have := natDegree_newtonBasis_le u k
  have hk' := Finset.mem_range.1 hk
  omega

theorem wNorm_newtonBasis_le {u : ℕ → ℂ} {R : ℝ} (hu : ∀ l, ‖u l‖ ≤ R) (k : ℕ) :
    wNorm 1 (newtonBasis u k) ≤ (1 + R) ^ k := by
  unfold newtonBasis
  refine (wNorm_prod_le zero_le_one _ _).trans ?_
  calc ∏ l ∈ range k, wNorm 1 (X - C (u l)) ≤ ∏ _l ∈ range k, (1 + R) := by
        refine Finset.prod_le_prod (fun l _ => wNorm_nonneg zero_le_one _) fun l _ => ?_
        have h := wNorm_linear_le zero_le_one (-(u l)) 1
        have heq : (C (-(u l)) + C 1 * X : ℂ[X]) = X - C (u l) := by
          rw [C_neg, C_1, one_mul]; ring
        rw [heq, norm_neg, norm_one, mul_one] at h
        linarith [hu l]
    _ = (1 + R) ^ k := by simp

/-- **Separation-free bound for the Newton reduction.** -/
theorem wNorm_newtonReduce_le {u : ℕ → ℂ} {R η : ℝ} (hR : 1 ≤ R) (hη : 0 < η)
    (hu : ∀ l, ‖u l‖ ≤ R) (n : ℕ) (f : ℂ[X]) :
    wNorm 1 (newtonReduce u n f) ≤
      wNorm ((1 + η) * R) f * ∑ k ∈ range n, ((1 + R) / η) ^ k := by
  unfold newtonReduce
  refine (wNorm_sum_le zero_le_one _ _).trans ?_
  rw [wNorm_eq_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  refine (wNorm_C_mul_le zero_le_one _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (wNorm_sum_le zero_le_one _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  refine (wNorm_C_mul_le zero_le_one _ _).trans ?_
  have hR0 : 0 ≤ R := by linarith
  have hc := norm_newtonCoeff_le hR hu m k
  have hb := choose_mul_pow_le_one_add_pow hη.le m k
  have hN := wNorm_newtonBasis_le hu k
  have hηk : 0 < η ^ k := pow_pos hη k
  -- `C(m,k) R^m ≤ ((1+η) R)^m / η^k`
  have hc' : ‖newtonPowerCoeff u m k‖ ≤ ((1 + η) * R) ^ m / η ^ k := by
    refine hc.trans ?_
    rw [le_div_iff₀ hηk, mul_pow]
    calc (m.choose k : ℝ) * R ^ m * η ^ k = ((m.choose k : ℝ) * η ^ k) * R ^ m := by ring
      _ ≤ (1 + η) ^ m * R ^ m := mul_le_mul_of_nonneg_right hb (pow_nonneg hR0 m)
  calc ‖newtonPowerCoeff u m k‖ * wNorm 1 (newtonBasis u k)
      ≤ (((1 + η) * R) ^ m / η ^ k) * (1 + R) ^ k :=
        mul_le_mul hc' hN (wNorm_nonneg zero_le_one _) (by positivity)
    _ = ((1 + η) * R) ^ m * ((1 + R) / η) ^ k := by rw [div_pow]; ring

/-! ## The gap radius -/

/-- Among `N + 1` disjoint windows of width `2g` filling `[1 − θ, 1]`, one avoids every value. -/
theorem exists_gap_radius {ι : Type*} (s : Finset ι) (a : ι → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ r : ℝ, 1 - θ + θ / (2 * (s.card + 1)) ≤ r ∧ r ≤ 1 - θ / (2 * (s.card + 1)) ∧
      ∀ i ∈ s, a i ≤ r - θ / (2 * (s.card + 1)) ∨ r + θ / (2 * (s.card + 1)) ≤ a i := by
  classical
  set g : ℝ := θ / (2 * (s.card + 1)) with hg
  have hg0 : 0 < g := by positivity
  have hθg : θ = 2 * (s.card + 1) * g := by rw [hg]; field_simp
  by_contra hcon
  push Not at hcon
  have hpick : ∀ k ∈ range (s.card + 1), ∃ i ∈ s,
      1 - θ + (2 * k + 1) * g - g < a i ∧ a i < 1 - θ + (2 * k + 1) * g + g := by
    intro k hk
    have hk' : (k : ℝ) ≤ s.card := by
      have := Finset.mem_range.1 hk; exact_mod_cast Nat.lt_succ_iff.1 this
    obtain ⟨i, hi, h1, h2⟩ := hcon (1 - θ + (2 * k + 1) * g) (by nlinarith) (by nlinarith)
    exact ⟨i, hi, h1, h2⟩
  haveI : Nonempty ι := ⟨(hpick 0 (by simp)).choose⟩
  choose! f hfs hf using hpick
  have hinj : Set.InjOn f (range (s.card + 1) : Set ℕ) := by
    intro k hk k' hk' hkk
    have h1 := hf k hk
    have h2 := hf k' hk'
    rw [hkk] at h1
    have hlt : |((k : ℝ) - k')| < 1 := by
      rw [abs_lt]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    have : ((k : ℤ) - k' : ℤ) = 0 := by
      have h3 : |((k : ℤ) - k' : ℤ)| < 1 := by exact_mod_cast hlt
      rw [abs_lt] at h3; omega
    omega
  have hcard := Finset.card_le_card_of_injOn f (fun k hk => hfs k hk) hinj
  rw [Finset.card_range] at hcard
  omega

/-! ## The separating polynomial -/

theorem natDegree_one_add_C_mul_X_le (a : ℂ) : (C 1 + C a * X : ℂ[X]).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_C]; exact zero_le_one
  · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X])

section Separating

variable {ι : Type*} (z : ι → ℂ) (I : Finset ι)

/-- The inner factor `P̃(y) = Π_{j ∈ I} (1 − z_j y)`. -/
def sepInner : ℂ[X] := ∏ j ∈ I, (C 1 + C (-z j) * X)

/-- The truncated inverse `Π_{j ∈ I} Σ_{t ≤ J} (z_j y)^t` of the inner factor. -/
def sepGeom (J : ℕ) : ℂ[X] := ∏ j ∈ I, ∑ t ∈ range (J + 1), C (z j ^ t) * X ^ t

/-- The separating polynomial `Q̃ = P̃ · Red_n(y^m Π_j Σ_{t≤J} (z_j y)^t)`. -/
def sepPoly (u : ℕ → ℂ) (n J m : ℕ) : ℂ[X] :=
  sepInner z I * newtonReduce u n (X ^ m * sepGeom z I J)

theorem eval_sepInner (y : ℂ) : (sepInner z I).eval y = ∏ j ∈ I, (1 - z j * y) := by
  rw [sepInner, eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [eval_add, eval_C, eval_mul, eval_X]
  ring

theorem eval_sepGeom (J : ℕ) (y : ℂ) :
    (sepGeom z I J).eval y = ∏ j ∈ I, ∑ t ∈ range (J + 1), (z j * y) ^ t := by
  rw [sepGeom, eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [eval_mul, eval_C, eval_X_pow, mul_pow]

theorem eval_sepPoly_inner (u : ℕ → ℂ) (n J m : ℕ) {i : ι} (hi : i ∈ I) (h0 : z i ≠ 0) :
    (sepPoly z I u n J m).eval (z i)⁻¹ = 0 := by
  rw [sepPoly, eval_mul, eval_sepInner]
  rw [Finset.prod_eq_zero hi (by rw [mul_inv_cancel₀ h0, sub_self]), zero_mul]

theorem eval_sepPoly_node (u : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) {l : ℕ} (hl : l < n) (J m : ℕ) :
    (sepPoly z I u n J m).eval (u l) = u l ^ m * ∏ j ∈ I, (1 - (z j * u l) ^ (J + 1)) := by
  rw [sepPoly, eval_mul, eval_newtonReduce u hn hl, eval_mul, eval_X_pow, eval_sepInner,
    eval_sepGeom, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_neg_geom_sum _ _

theorem natDegree_sepPoly_le (u : ℕ → ℂ) (n J m : ℕ) :
    (sepPoly z I u n J m).natDegree ≤ I.card + (n - 1) := by
  have h1 : (∏ j ∈ I, (C 1 + C (-z j) * X)).natDegree ≤ I.card := by
    refine (natDegree_prod_le I fun j => (C 1 + C (-z j) * X)).trans ?_
    refine (Finset.sum_le_sum fun j _ => natDegree_one_add_C_mul_X_le (-z j)).trans ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  exact natDegree_mul_le.trans
    (add_le_add h1 (natDegree_newtonReduce_le u n (X ^ m * sepGeom z I J)))

theorem wNorm_sepInner_le {r : ℝ} (hr : ∀ j ∈ I, ‖z j‖ ≤ r) :
    wNorm 1 (sepInner z I) ≤ (1 + r) ^ I.card := by
  refine (wNorm_prod_le zero_le_one _ _).trans ?_
  calc ∏ j ∈ I, wNorm 1 (C 1 + C (-z j) * X) ≤ ∏ _j ∈ I, (1 + r) := by
        refine Finset.prod_le_prod (fun _ _ => wNorm_nonneg zero_le_one _) fun j hj => ?_
        refine (wNorm_linear_le zero_le_one _ _).trans ?_
        rw [norm_one, norm_neg, mul_one]
        linarith [hr j hj]
    _ = (1 + r) ^ I.card := by simp

theorem wNorm_sepGeom_le {x g : ℝ} (hx : 0 ≤ x) (hg : 0 < g) (J : ℕ)
    (hq : ∀ j ∈ I, ‖z j‖ * x ≤ 1 - g) :
    wNorm x (sepGeom z I J) ≤ (1 / g) ^ I.card := by
  refine (wNorm_prod_le hx _ _).trans ?_
  calc ∏ j ∈ I, wNorm x (∑ t ∈ range (J + 1), C (z j ^ t) * X ^ t) ≤ ∏ _j ∈ I, (1 / g) := by
        refine Finset.prod_le_prod (fun _ _ => wNorm_nonneg hx _) fun j hj => ?_
        refine (wNorm_sum_le hx _ _).trans ?_
        have hq0 : 0 ≤ ‖z j‖ * x := mul_nonneg (norm_nonneg _) hx
        have hq1 : ‖z j‖ * x < 1 := by linarith [hq j hj]
        calc ∑ t ∈ range (J + 1), wNorm x (C (z j ^ t) * X ^ t)
            ≤ ∑ t ∈ Ico 0 (J + 1), (‖z j‖ * x) ^ t := by
              rw [← Finset.range_eq_Ico]
              refine Finset.sum_le_sum fun t _ => (wNorm_C_mul_le hx _ _).trans ?_
              rw [wNorm_X_pow, norm_pow, mul_pow]
          _ ≤ (‖z j‖ * x) ^ 0 / (1 - ‖z j‖ * x) := geom_sum_Ico_le_of_lt_one hq0 hq1
          _ ≤ 1 / g := by
              rw [pow_zero]
              exact one_div_le_one_div_of_le hg (by linarith [hq j hj])
    _ = (1 / g) ^ I.card := by simp

end Separating

/-- The reversed evaluation `Σ_{k<N} p_k x^{m−k} = x^m p(1/x)`. -/
theorem sum_coeff_mul_pow_sub_eq {P : ℂ[X]} {N m : ℕ} (hdeg : P.natDegree < N) (hNm : N ≤ m)
    {x : ℂ} (hx : x ≠ 0) :
    ∑ k ∈ range N, P.coeff k * x ^ (m - k) = x ^ m * P.eval x⁻¹ := by
  rw [eval_eq_sum_range' hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := by have := Finset.mem_range.1 hk; omega
  rw [pow_sub₀ x hx hk', inv_pow]
  ring

theorem sum_coeff_mul_zero_pow_sub_eq {P : ℂ[X]} {N m : ℕ} (hNm : N ≤ m) :
    ∑ k ∈ range N, P.coeff k * (0 : ℂ) ^ (m - k) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k < N := Finset.mem_range.1 hk
  rw [zero_pow (by omega), mul_zero]

/-- `x ≤ D/(D−1)` and `K ≤ D − 1` give `x^K ≤ e`. -/
theorem pow_le_exp_one_of_le {x D : ℝ} {K : ℕ} (hx : 0 ≤ x) (hD : 1 < D)
    (hxD : x ≤ 1 + 1 / (D - 1)) (hK : (K : ℝ) ≤ D - 1) : x ^ K ≤ Real.exp 1 := by
  have hxe : x ≤ Real.exp (1 / (D - 1)) := hxD.trans (by linarith [Real.add_one_le_exp (1 / (D - 1))])
  calc x ^ K ≤ Real.exp (1 / (D - 1)) ^ K := pow_le_pow_left₀ hx hxe _
    _ = Real.exp (K * (1 / (D - 1))) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp 1 := by
        refine Real.exp_le_exp.2 ?_
        rw [← div_eq_mul_one_div, div_le_one (by linarith)]
        exact hK

/-! ## The power-sum lower bound -/

/-- A combination of the power sums `S_{M+1}, …, S_{M+N}` with coefficient mass `≤ B` and modulus
`≥ 3/4` forces one of them to have modulus `≥ 1/(2B)`. -/
theorem exists_norm_ge_of_combination {N M : ℕ} (hN : 1 ≤ N) (q S : ℕ → ℂ) {B : ℝ} (hB : 0 < B)
    (hq : ∑ k ∈ range N, ‖q k‖ ≤ B) (hlow : 3 / 4 ≤ ‖∑ k ∈ range N, q k * S (M + N - k)‖) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧ 1 / (2 * B) ≤ ‖S ν‖ := by
  obtain ⟨k₀, hk₀, hk₀max⟩ := Finset.exists_max_image (range N)
    (fun k => ‖S (M + N - k)‖) ⟨0, Finset.mem_range.2 (by omega)⟩
  refine ⟨M + N - k₀, by have := Finset.mem_range.1 hk₀; omega, by omega, ?_⟩
  have hup : 3 / 4 ≤ B * ‖S (M + N - k₀)‖ := by
    refine hlow.trans ((norm_sum_le _ _).trans ?_)
    calc ∑ k ∈ range N, ‖q k * S (M + N - k)‖ ≤ ∑ k ∈ range N, ‖q k‖ * ‖S (M + N - k₀)‖ := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hk₀max k hk) (norm_nonneg _)
      _ = (∑ k ∈ range N, ‖q k‖) * ‖S (M + N - k₀)‖ := by rw [Finset.sum_mul]
      _ ≤ B * ‖S (M + N - k₀)‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
  rw [div_le_iff₀ (by linarith)]
  have e : ‖S (M + N - k₀)‖ * (2 * B) = 2 * (B * ‖S (M + N - k₀)‖) := by ring
  linarith

/-- The values of the separating polynomial sum to `≈ #outer`. -/
theorem norm_sum_sepPoly_values_ge {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (O I : Finset ι) (hOI : Disjoint O I)
    (u : ℕ → ℂ) {n J M N : ℕ} (hn1 : 1 ≤ n) (hO1 : 1 ≤ O.card) (hIN : I.card ≤ N)
    (hnode : ∀ o ∈ O, ∃ l < n, u l = (z o)⁻¹) (hO0 : ∀ o ∈ O, z o ≠ 0)
    (hdeg : (sepPoly z I u n J (M + N)).natDegree < N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ o ∈ O, ∀ j ∈ I, ‖z j * (z o)⁻¹‖ ≤ ρ) (hJ : (1 + ρ ^ (J + 1)) ^ N - 1 ≤ 1 / 4) :
    3 / 4 ≤ ‖∑ i ∈ O ∪ I, ∑ k ∈ range N,
      (sepPoly z I u n J (M + N)).coeff k * z i ^ (M + N - k)‖ := by
  have hNm : N ≤ M + N := by omega
  have hval_inner : ∀ i ∈ I,
      ∑ k ∈ range N, (sepPoly z I u n J (M + N)).coeff k * z i ^ (M + N - k) = 0 := by
    intro i hi
    by_cases h0 : z i = 0
    · rw [h0]; exact sum_coeff_mul_zero_pow_sub_eq hNm
    · rw [sum_coeff_mul_pow_sub_eq hdeg hNm h0, eval_sepPoly_inner z I u _ _ _ hi h0, mul_zero]
  have hval_outer : ∀ o ∈ O,
      ∑ k ∈ range N, (sepPoly z I u n J (M + N)).coeff k * z o ^ (M + N - k) =
        ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) := by
    intro o ho
    obtain ⟨l, hl, hul⟩ := hnode o ho
    rw [sum_coeff_mul_pow_sub_eq hdeg hNm (hO0 o ho), ← hul, eval_sepPoly_node z I u hn1 hl, hul,
      ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (hO0 o ho), one_pow, one_mul]
  rw [Finset.sum_union hOI, Finset.sum_eq_zero hval_inner, add_zero,
    Finset.sum_congr rfl hval_outer]
  have herr : ∀ o ∈ O, ‖∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) - 1‖ ≤ 1 / 4 := by
    intro o ho
    have h1 := norm_prod_one_add_sub_one_le I (fun j => -(z j * (z o)⁻¹) ^ (J + 1))
    simp only [← sub_eq_add_neg] at h1
    refine h1.trans ?_
    have hρJ : 0 ≤ ρ ^ (J + 1) := pow_nonneg hρ0 _
    have h2 : ∏ j ∈ I, (1 + ‖-(z j * (z o)⁻¹) ^ (J + 1)‖) ≤ (1 + ρ ^ (J + 1)) ^ N := by
      calc ∏ j ∈ I, (1 + ‖-(z j * (z o)⁻¹) ^ (J + 1)‖) ≤ ∏ _j ∈ I, (1 + ρ ^ (J + 1)) := by
            refine Finset.prod_le_prod (fun _ _ => by positivity) fun j hj => ?_
            rw [norm_neg, norm_pow]
            have := pow_le_pow_left₀ (norm_nonneg _) (hρ o ho j hj) (J + 1)
            linarith
        _ = (1 + ρ ^ (J + 1)) ^ I.card := by rw [Finset.prod_const]
        _ ≤ (1 + ρ ^ (J + 1)) ^ N := pow_le_pow_right₀ (by linarith) hIN
    linarith
  set E : ℂ := ∑ o ∈ O, (∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) - 1) with hE
  have hsplitsum : ∑ o ∈ O, ∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) = (O.card : ℂ) + E := by
    rw [hE, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have hEb : ‖E‖ ≤ O.card / 4 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ o ∈ O, ‖∏ j ∈ I, (1 - (z j * (z o)⁻¹) ^ (J + 1)) - 1‖ ≤ ∑ _o ∈ O, (1 / 4 : ℝ) :=
          Finset.sum_le_sum herr
      _ = O.card / 4 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hn1r : (1 : ℝ) ≤ O.card := by exact_mod_cast hO1
  have h3 := norm_sub_norm_le (O.card : ℂ) (-E)
  rw [norm_neg, sub_neg_eq_add, Complex.norm_natCast] at h3
  rw [hsplitsum]
  linarith

/-- Arithmetic of the gap parameters `θ = 1/D`, `D = M + 2N + 2`, `g = θ/(2(N+1))`. -/
theorem gap_params {M N : ℕ} (hN : 1 ≤ N) {r g : ℝ}
    (hg : g = 1 / ((M : ℝ) + 2 * N + 2) / (2 * (N + 1)))
    (hr1 : 1 - 1 / ((M : ℝ) + 2 * N + 2) + g ≤ r) (hr2 : r ≤ 1 - g) :
    0 < g ∧ r + g ≤ 1 ∧ 0 < r - g ∧ 1 ≤ 1 / (r + g) ∧ 1 / (r + g) ≤ 4 / 3 ∧
      (r - g) * ((1 + g) * (1 / (r + g))) ≤ 1 - g ∧
      (1 + g) * (1 / (r + g)) ≤ 1 + 1 / ((M : ℝ) + 2 * N + 2 - 1) ∧
      3 / g = 6 * (N + 1) * ((M : ℝ) + 2 * N + 2) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set D : ℝ := (M : ℝ) + 2 * N + 2 with hD
  have hD4 : 4 ≤ D := by rw [hD]; linarith
  have hθ4 : 1 / D ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hD4
  have hθ0 : 0 < 1 / D := by positivity
  have hg0 : 0 < g := by rw [hg]; positivity
  have hgθ : g ≤ (1 / D) / 4 := by
    rw [hg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hrg : r + g ≤ 1 := by linarith
  have hrgpos : 0 < r + g := by linarith
  refine ⟨hg0, hrg, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hrgpos]; linarith
  · rw [div_le_iff₀ hrgpos]; nlinarith
  · rw [show (r - g) * ((1 + g) * (1 / (r + g))) = (r - g) * (1 + g) / (r + g) by ring,
      div_le_iff₀ hrgpos]
    nlinarith
  · have hD1 : 0 < D - 1 := by linarith
    have hθD : 1 / D * D = 1 := by field_simp
    rw [show (1 + g) * (1 / (r + g)) = (1 + g) / (r + g) by ring, div_le_iff₀ hrgpos,
      show 1 + 1 / (D - 1) = D / (D - 1) by field_simp; ring, div_mul_eq_mul_div,
      le_div_iff₀ hD1]
    nlinarith
  · have hD0 : D ≠ 0 := by linarith
    rw [hg, div_div_eq_mul_div, one_div, div_inv_eq_mul]
    ring

/-- The coefficient mass of the separating polynomial. -/
theorem wNorm_sepPoly_le_of_gap {ι : Type*} (z : ι → ℂ) (I : Finset ι) (u : ℕ → ℂ)
    {n J M N : ℕ} (hN : 1 ≤ N) (hcard : n + I.card = N) {r g : ℝ}
    (hg : g = 1 / ((M : ℝ) + 2 * N + 2) / (2 * (N + 1)))
    (hr1 : 1 - 1 / ((M : ℝ) + 2 * N + 2) + g ≤ r) (hr2 : r ≤ 1 - g)
    (hI : ∀ j ∈ I, ‖z j‖ ≤ r - g) (hu : ∀ l, ‖u l‖ ≤ 1 / (r + g)) :
    wNorm 1 (sepPoly z I u n J (M + N)) ≤
      Real.exp 1 * N * (6 * (N + 1) * ((M : ℝ) + 2 * N + 2)) ^ N := by
  obtain ⟨hg0, hrg, hr0, hR1, hR43, hq0, hxD, h3g⟩ := gap_params hN hg hr1 hr2
  set R : ℝ := 1 / (r + g) with hR
  set x : ℝ := (1 + g) * R with hx
  have hx0 : 0 ≤ x := by positivity
  have hq : ∀ j ∈ I, ‖z j‖ * x ≤ 1 - g := fun j hj =>
    (mul_le_mul_of_nonneg_right (hI j hj) hx0).trans hq0
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxpow : x ^ (M + N) ≤ Real.exp 1 :=
    pow_le_exp_one_of_le hx0 (by linarith) hxD (by push_cast; linarith)
  have hG := wNorm_sepGeom_le z I hx0 hg0 J hq
  have h2 : wNorm x (X ^ (M + N) * sepGeom z I J) ≤ Real.exp 1 * (1 / g) ^ I.card := by
    refine (wNorm_mul_le hx0 _ _).trans ?_
    rw [wNorm_X_pow]
    exact mul_le_mul hxpow hG (wNorm_nonneg hx0 _) (Real.exp_pos 1).le
  have h3 : ∑ k ∈ range n, ((1 + R) / g) ^ k ≤ n * (3 / g) ^ n := by
    have hb : (1 + R) / g ≤ 3 / g := div_le_div_of_nonneg_right (by linarith) hg0.le
    have hb1 : 1 ≤ (1 + R) / g := by rw [le_div_iff₀ hg0]; nlinarith
    calc ∑ k ∈ range n, ((1 + R) / g) ^ k ≤ ∑ _k ∈ range n, (3 / g) ^ n := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact (pow_le_pow_right₀ hb1 (Finset.mem_range.1 hk).le).trans
            (pow_le_pow_left₀ (by positivity) hb _)
      _ = n * (3 / g) ^ n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hV : wNorm 1 (newtonReduce u n (X ^ (M + N) * sepGeom z I J)) ≤
      Real.exp 1 * (1 / g) ^ I.card * (n * (3 / g) ^ n) := by
    refine (wNorm_newtonReduce_le hR1 hg0 hu n _).trans ?_
    exact mul_le_mul h2 h3 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  have hP := wNorm_sepInner_le z I (r := 1) fun j hj => (hI j hj).trans (by linarith)
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h23 : (2 / g) ^ I.card ≤ (3 / g) ^ I.card :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by norm_num) hg0.le) _
  calc wNorm 1 (sepPoly z I u n J (M + N))
      ≤ wNorm 1 (sepInner z I) * wNorm 1 (newtonReduce u n (X ^ (M + N) * sepGeom z I J)) :=
        wNorm_mul_le zero_le_one _ _
    _ ≤ (1 + 1) ^ I.card * (Real.exp 1 * (1 / g) ^ I.card * (n * (3 / g) ^ n)) :=
        mul_le_mul hP hV (wNorm_nonneg zero_le_one _) (by positivity)
    _ = Real.exp 1 * n * ((2 / g) ^ I.card * (3 / g) ^ n) := by ring
    _ ≤ Real.exp 1 * N * ((3 / g) ^ I.card * (3 / g) ^ n) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hnN he)
          (mul_le_mul_of_nonneg_right h23 (by positivity)) (by positivity)
          (mul_nonneg he (Nat.cast_nonneg _))
    _ = Real.exp 1 * N * (6 * (N + 1) * ((M : ℝ) + 2 * N + 2)) ^ N := by
        rw [← pow_add, add_comm I.card, hcard, h3g]

/-- **Separation-free power-sum lower bound** (Turán's second main theorem, unit weights).  If
`|z_i| ≥ 1` for some `i ∈ s`, then for every `M` some exponent `M + 1 ≤ ν ≤ M + N`, `N = #s`, has
`|Σ_i z_i^ν| ≥ 1/(2e N (6(N+1)(M+2N+2))^N)`.  Points of modulus above `1` only join the outer
group, so no upper bound on the moduli is needed. -/
theorem exists_norm_powerSum_ge {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (htop : ∃ i ∈ s, 1 ≤ ‖z i‖) (M : ℕ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + s.card ∧
      1 / (2 * (Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card)) ≤
        ‖∑ i ∈ s, z i ^ ν‖ := by
  classical
  obtain ⟨i₀, hi₀s, hi₀⟩ := htop
  have hN1 : 1 ≤ s.card := Finset.card_pos.2 ⟨i₀, hi₀s⟩
  have hθ0 : 0 < 1 / ((M : ℝ) + 2 * s.card + 2) := by positivity
  obtain ⟨r, hr1, hr2, hsplit⟩ := exists_gap_radius s (fun i => ‖z i‖) hθ0
  set g : ℝ := 1 / ((M : ℝ) + 2 * s.card + 2) / (2 * (s.card + 1)) with hg
  obtain ⟨hg0, hrg, hr0, -, -, -, -, -⟩ := gap_params hN1 hg hr1 hr2
  have hrgpos : 0 < r + g := by linarith
  set O := s.filter (fun i => r + g ≤ ‖z i‖) with hO
  set I := s.filter (fun i => ¬ (r + g ≤ ‖z i‖)) with hI
  have hIle : ∀ i ∈ I, ‖z i‖ ≤ r - g := by
    intro i hi
    obtain ⟨his, hn⟩ := Finset.mem_filter.1 hi
    rcases hsplit i his with h | h
    · exact h
    · exact absurd h hn
  have hOge : ∀ i ∈ O, r + g ≤ ‖z i‖ := fun i hi => (Finset.mem_filter.1 hi).2
  have hcardOI : O.card + I.card = s.card := Finset.card_filter_add_card_filter_not _
  have hO1 : 1 ≤ O.card := Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨hi₀s, hrg.trans hi₀⟩⟩
  have hO0 : ∀ o ∈ O, z o ≠ 0 := by
    intro o ho h; have := hOge o ho; rw [h, norm_zero] at this; linarith
  -- outer reciprocals as Newton nodes
  set u : ℕ → ℂ := fun l => if h : l < O.card then (z (O.equivFin.symm ⟨l, h⟩).1)⁻¹ else 0
    with hu
  have huR : ∀ l, ‖u l‖ ≤ 1 / (r + g) := by
    intro l
    by_cases h : l < O.card
    · simp only [hu]
      rw [dif_pos h, norm_inv, one_div]
      exact inv_anti₀ hrgpos (hOge _ (O.equivFin.symm ⟨l, h⟩).2)
    · simp only [hu]
      rw [dif_neg h, norm_zero]; positivity
  have hnode : ∀ o ∈ O, ∃ l < O.card, u l = (z o)⁻¹ := by
    intro o ho
    refine ⟨O.equivFin ⟨o, ho⟩, (O.equivFin ⟨o, ho⟩).2, ?_⟩
    simp only [hu]
    rw [dif_pos (O.equivFin ⟨o, ho⟩).2]
    simp only [Fin.eta, Equiv.symm_apply_apply]
  -- the truncation length
  set ρ : ℝ := (r - g) / (r + g) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hrgpos]; linarith
  have hρz : ∀ o ∈ O, ∀ j ∈ I, ‖z j * (z o)⁻¹‖ ≤ ρ := by
    intro o ho j hj
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact div_le_div₀ hr0.le (hIle j hj) hrgpos (hOge o ho)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, (1 + ρ ^ (J + 1)) ^ s.card - 1 ≤ 1 / 4 := by
    have h1 : Tendsto (fun J : ℕ => ρ ^ (J + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
    have ht : Tendsto (fun J : ℕ => (1 + ρ ^ (J + 1)) ^ s.card - 1) atTop
        (𝓝 ((1 + 0) ^ s.card - 1)) :=
      ((tendsto_const_nhds.add h1).pow _).sub tendsto_const_nhds
    rw [add_zero, one_pow, sub_self] at ht
    exact (ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
  -- the separating polynomial
  have hdeg : (sepPoly z I u O.card J (M + s.card)).natDegree < s.card := by
    have h := natDegree_sepPoly_le z I u O.card J (M + s.card)
    omega
  have hOI : Disjoint O I := Finset.disjoint_filter_filter_not _ _ _
  have hs : O ∪ I = s := Finset.filter_union_filter_not_eq _ _
  have hlow := norm_sum_sepPoly_values_ge z O I hOI u hO1 hO1 (by omega) hnode hO0 hdeg hρ0 hρz hJ
  rw [hs] at hlow
  have hcoef : ∑ k ∈ range s.card, ‖(sepPoly z I u O.card J (M + s.card)).coeff k‖ ≤
      Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card := by
    have hw1 : ∑ k ∈ range s.card, ‖(sepPoly z I u O.card J (M + s.card)).coeff k‖ =
        wNorm 1 (sepPoly z I u O.card J (M + s.card)) := by
      rw [wNorm_eq_sum_of_lt 1 hdeg]; simp
    rw [hw1]
    exact wNorm_sepPoly_le_of_gap z I u hN1 hcardOI hg hr1 hr2 hIle huR
  have hident : ∑ i ∈ s, ∑ k ∈ range s.card,
      (sepPoly z I u O.card J (M + s.card)).coeff k * z i ^ (M + s.card - k) =
        ∑ k ∈ range s.card, (sepPoly z I u O.card J (M + s.card)).coeff k *
          ∑ i ∈ s, z i ^ (M + s.card - k) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hident] at hlow
  exact exists_norm_ge_of_combination hN1 _ (fun ν => ∑ i ∈ s, z i ^ ν)
    (by positivity) hcoef hlow

/-- **Scaled form.**  If some `|z_i| ≥ Z > 0`, then for every `M` some exponent
`M + 1 ≤ ν ≤ M + N` has `|Σ_i z_i^ν| ≥ Z^ν / (2e N (6(N+1)(M+2N+2))^N)`. -/
theorem exists_norm_powerSum_ge_scaled {ι : Type*} (s : Finset ι) (z : ι → ℂ) {Z : ℝ}
    (hZ : 0 < Z) (htop : ∃ i ∈ s, Z ≤ ‖z i‖) (M : ℕ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + s.card ∧
      Z ^ ν / (2 * (Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^
        s.card)) ≤ ‖∑ i ∈ s, z i ^ ν‖ := by
  obtain ⟨i₀, hi₀s, hi₀⟩ := htop
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  obtain ⟨ν, h1, h2, h3⟩ := exists_norm_powerSum_ge s (fun i => z i / Z)
    ⟨i₀, hi₀s, by rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ,
      le_div_iff₀ hZ, one_mul]; exact hi₀⟩ M
  refine ⟨ν, h1, h2, ?_⟩
  have hsum : ∑ i ∈ s, (z i / Z) ^ ν = (∑ i ∈ s, z i ^ ν) / (Z : ℂ) ^ ν := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => div_pow _ _ _
  rw [hsum, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ,
    le_div_iff₀ (pow_pos hZ ν)] at h3
  have hs : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.2 ⟨i₀, hi₀s⟩
  set L : ℝ := 2 * (Real.exp 1 * s.card * (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^
    s.card) with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  rw [div_le_iff₀ hLpos]
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hLpos] at h3
  exact h3

end

end GaloisForLFunctions.HTGeometry
