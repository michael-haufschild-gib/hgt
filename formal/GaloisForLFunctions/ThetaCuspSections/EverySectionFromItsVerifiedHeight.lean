import GaloisForLFunctions.ThetaCuspSections.TheTenthSectionFromHeightSixtySeven

/-!
# Every theta section from an explicit verified height

**Theorem** (`thetaCuspCenterMixedSignedHankel_posDef_of_rhVerifiedThrough`). For `0 < a ≤ ½`, the
signed section of rank `N` is positive definite as soon as RH holds through
`sectionHeight N + 1`, `sectionHeight N = 40 + 6 (N+2) log (N+2)`.

So the height of rank `N` is `O(N log N)` with explicit constants.

* **Polynomials from their mass.** Equally spaced Lagrange weights at `N` nodes in `[1, 5]` sum to at
  most `e^N |b|^{N-1}` at `|b| ≥ 5`. Averaging over the offset of the nodes gives
  `P(b)² ≤ (N/4) e^{2N} b^{2N-2} ∫₁⁵ P²` for `deg P < N`.
* **Balance.** The current is at least `6·10⁻⁴ a` on `[1, 5]`, nonnegative up to the height, and at
  most `6.05·10⁹ a e^{-(7/5)|b|}` beyond it.
-/

open Complex MeasureTheory Set Filter Topology Matrix Polynomial

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs

/-! ## Equally spaced Lagrange weights -/

private theorem prod_below (i : ℕ) : ∏ j ∈ Finset.range i, |(i : ℝ) - j| = i.factorial := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have e : ∀ j ∈ Finset.range i, |((i + 1 : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)| = |(i : ℝ) - j| := by
      intro j _
      push_cast
      congr 1
      ring
    have e0 : |((i + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)| = (i : ℝ) + 1 := by
      push_cast
      rw [sub_zero, abs_of_nonneg (by positivity)]
    rw [Finset.prod_congr rfl e, ih, e0]
    push_cast
    ring

private theorem prod_above (i k : ℕ) :
    ∏ j ∈ Finset.range k, |(i : ℝ) - ((i + 1 + j : ℕ) : ℝ)| = k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    have e : |(i : ℝ) - ((i + 1 + k : ℕ) : ℝ)| = (k : ℝ) + 1 := by
      push_cast
      rw [show (i : ℝ) - (i + 1 + k) = -((k : ℝ) + 1) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    rw [e]
    push_cast
    ring

private theorem prod_erase_abs (i k : ℕ) :
    ∏ j ∈ (Finset.range (i + 1 + k)).erase i, |(i : ℝ) - j| =
      (i.factorial : ℝ) * k.factorial := by
  classical
  let g : ℕ → ℝ := fun j => if j = i then 1 else |(i : ℝ) - j|
  have h1 : ∏ j ∈ (Finset.range (i + 1 + k)).erase i, |(i : ℝ) - j| =
      ∏ j ∈ (Finset.range (i + 1 + k)).erase i, g j :=
    Finset.prod_congr rfl fun j hj => (if_neg (Finset.ne_of_mem_erase hj)).symm
  have h2 : ∏ j ∈ (Finset.range (i + 1 + k)).erase i, g j = ∏ j ∈ Finset.range (i + 1 + k), g j :=
    Finset.prod_erase _ (if_pos rfl)
  have h3 : ∏ j ∈ Finset.range i, g j = i.factorial := by
    rw [← prod_below i]
    exact Finset.prod_congr rfl fun j hj => if_neg (Finset.mem_range.mp hj).ne
  have h4 : ∏ j ∈ Finset.range k, g (i + 1 + j) = k.factorial := by
    rw [← prod_above i k]
    exact Finset.prod_congr rfl fun j _ => if_neg (by omega)
  rw [h1, h2, Finset.prod_range_add, Finset.prod_range_succ, h3, h4]
  simp [g]

/-- One equally spaced Lagrange weight. -/
private theorem abs_eval_basis_le {N i : ℕ} {h c b : ℝ} (hh : 0 < h) (hi : i < N)
    (hv : ∀ j < N, |c + j * h| ≤ |b|) :
    |(Lagrange.basis (Finset.range N) (fun j : ℕ => c + j * h) i).eval b| ≤
      (2 * |b| / h) ^ (N - 1) / ((i.factorial : ℝ) * (N - 1 - i).factorial) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, N = i + 1 + k := ⟨N - 1 - i, by omega⟩
  have hcard : ((Finset.range (i + 1 + k)).erase i).card = i + 1 + k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hi), Finset.card_range]
  have hk : i + 1 + k - 1 - i = k := by omega
  rw [hk]
  unfold Lagrange.basis
  rw [eval_prod, Finset.abs_prod]
  have hbound : ∀ j ∈ (Finset.range (i + 1 + k)).erase i,
      |eval b (Lagrange.basisDivisor (c + i * h) (c + j * h))| ≤ (2 * |b| / h) / |(i : ℝ) - j| := by
    intro j hj
    have hji := Finset.ne_of_mem_erase hj
    have hjN := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    have hne : (i : ℝ) - j ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hji.symm
    have hab : 0 < |(i : ℝ) - j| := abs_pos.mpr hne
    have e : eval b (Lagrange.basisDivisor (c + i * h) (c + j * h)) =
        (b - (c + j * h)) / (((i : ℝ) - j) * h) := by
      unfold Lagrange.basisDivisor
      simp only [eval_mul, eval_C, eval_sub, eval_X]
      rw [show c + (i : ℝ) * h - (c + j * h) = ((i : ℝ) - j) * h by ring]
      field_simp
    rw [e, abs_div, abs_mul, abs_of_pos hh, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hab]
    have h1 : |b - (c + j * h)| ≤ 2 * |b| := by
      have := abs_sub (b) (c + j * h)
      have h2 := hv j hjN
      linarith only [this, h2]
    have h3 : 0 ≤ h * |(i : ℝ) - j| := by positivity
    calc |b - (c + j * h)| * |(i : ℝ) - j| ≤ 2 * |b| * |(i : ℝ) - j| :=
          mul_le_mul_of_nonneg_right h1 hab.le
      _ ≤ 2 * |b| * h * |(i : ℝ) - j| / (|(i : ℝ) - j| * h) * |(i : ℝ) - j| := by
          have : 2 * |b| * h * |(i : ℝ) - j| / (|(i : ℝ) - j| * h) = 2 * |b| := by
            field_simp
          rw [this]
      _ = _ := by ring
  refine (Finset.prod_le_prod (fun _ _ => abs_nonneg _) hbound).trans_eq ?_
  rw [Finset.prod_div_distrib, Finset.prod_const, hcard, prod_erase_abs]

/-- The sum of the weights at `N` equally spaced nodes of step `4/N`. -/
private theorem sum_abs_eval_basis_le {N : ℕ} (hN : 1 ≤ N) {c b : ℝ}
    (hv : ∀ j < N, |c + j * (4 / N)| ≤ |b|) :
    ∑ i ∈ Finset.range N, |(Lagrange.basis (Finset.range N)
        (fun j : ℕ => c + j * (4 / N)) i).eval b| ≤ Real.exp N * |b| ^ (N - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < 4 / N := by positivity
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  refine (Finset.sum_le_sum fun i hi =>
    abs_eval_basis_le hh (Finset.mem_range.mp hi) hv).trans ?_
  simp only [Nat.add_sub_cancel]
  have hterm : ∀ i ∈ Finset.range (n + 1), (2 * |b| / (4 / ((n + 1 : ℕ) : ℝ))) ^ n /
      ((i.factorial : ℝ) * (n - i).factorial) =
      (2 * |b| / (4 / ((n + 1 : ℕ) : ℝ))) ^ n * ((n.choose i : ℝ) / n.factorial) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hc := Nat.choose_mul_factorial_mul_factorial hin
    have hc' : (n.choose i : ℝ) * i.factorial * (n - i).factorial = n.factorial := by
      exact_mod_cast hc
    have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((n - i).factorial : ℝ) ≠ 0 := by positivity
    have h3 : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [← hc']
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_div]
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hsum]
  have hexp := Real.pow_div_factorial_le_exp ((n + 1 : ℕ) : ℝ) (by positivity) n
  have e : (2 * |b| / (4 / ((n + 1 : ℕ) : ℝ))) ^ n * (2 ^ n / (n.factorial : ℝ)) =
      |b| ^ n * (((n + 1 : ℕ) : ℝ) ^ n / n.factorial) := by
    have : 2 * |b| / (4 / ((n + 1 : ℕ) : ℝ)) * 2 = |b| * ((n + 1 : ℕ) : ℝ) := by
      field_simp
      ring
    rw [mul_div_assoc', ← mul_pow, this, mul_pow, mul_div_assoc]
  rw [e, mul_comm]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- At a real offset of the nodes, a polynomial of degree below `N` is bounded by its node values. -/
private theorem sq_eval_le_nodes {N : ℕ} (hN : 1 ≤ N) {P : ℝ[X]} (hdeg : P.degree < N) {c b : ℝ}
    (hv : ∀ j < N, |c + j * (4 / N)| ≤ |b|) :
    P.eval b ^ 2 ≤ (Real.exp N * |b| ^ (N - 1)) ^ 2 *
      ∑ i ∈ Finset.range N, P.eval (c + i * (4 / N)) ^ 2 := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < 4 / N := by positivity
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = fun j : ℕ => c + j * (4 / N) := ⟨_, rfl⟩
  have hinj : Set.InjOn v (Finset.range N : Finset ℕ) := by
    intro i _ j _ hij
    rw [hvdef] at hij
    have h1 : (i : ℝ) * (4 / N) = j * (4 / N) := by
      simpa only [add_right_inj] using hij
    have h2 : (i : ℝ) = j := mul_right_cancel₀ hh.ne' h1
    exact_mod_cast h2
  have hdeg' : P.degree < ((Finset.range N).card : ℕ) := by rwa [Finset.card_range]
  have hint := congrArg (eval b) (Lagrange.eq_interpolate hinj hdeg')
  rw [Lagrange.interpolate_apply, eval_finset_sum] at hint
  simp only [eval_mul, eval_C] at hint
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun i => (Lagrange.basis (Finset.range N) v i).eval b) (fun i => P.eval (v i))
  have hsq : ∑ i ∈ Finset.range N, ((Lagrange.basis (Finset.range N) v i).eval b) ^ 2 ≤
      (Real.exp N * |b| ^ (N - 1)) ^ 2 := by
    have h1 : ∑ i ∈ Finset.range N, |(Lagrange.basis (Finset.range N) v i).eval b| ^ 2 ≤
        (∑ i ∈ Finset.range N, |(Lagrange.basis (Finset.range N) v i).eval b|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _
    have h2 := sum_abs_eval_basis_le hN hv
    rw [← hvdef] at h2
    have h3 := pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _) h2 2
    simp only [sq_abs] at h1
    exact h1.trans h3
  have e : P.eval b = ∑ i ∈ Finset.range N,
      (Lagrange.basis (Finset.range N) v i).eval b * P.eval (v i) := by
    rw [hint]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  have hnn : 0 ≤ ∑ i ∈ Finset.range N, P.eval (v i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have := hcs.trans (mul_le_mul_of_nonneg_right hsq hnn)
  rw [hvdef] at this ⊢
  exact this

/-- **Polynomials from their mass.** For `deg P < N` and `|b| ≥ 5`,
`P(b)² ≤ (N/4) (e^N |b|^{N-1})² ∫₁⁵ P²`. -/
theorem sq_eval_le_integral {N : ℕ} (hN : 1 ≤ N) {P : ℝ[X]} (hdeg : P.degree < N) {b : ℝ}
    (hb : 5 ≤ |b|) :
    P.eval b ^ 2 ≤ (N / 4 : ℝ) * (Real.exp N * |b| ^ (N - 1)) ^ 2 *
      ∫ x in (1 : ℝ)..5, P.eval x ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 4 / N := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hNh : (N : ℝ) * h = 4 := by rw [hh]; field_simp
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : Continuous fun x : ℝ => P.eval x ^ 2 := by fun_prop
  -- The pointwise bound at each offset.
  obtain ⟨S, hS⟩ : ∃ S, S = (Real.exp N * |b| ^ (N - 1)) ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) h, P.eval b ^ 2 ≤
      S * ∑ i ∈ Finset.range N, P.eval (1 + s + i * h) ^ 2 := by
    intro s hs
    rw [hS, hh]
    refine sq_eval_le_nodes hN hdeg fun j hj => ?_
    rw [← hh]
    have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have h1 : 0 ≤ (j : ℝ) * h := by positivity
    have h2 : ((j : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hj' hh0.le
    rw [abs_of_nonneg (by linarith only [hs.1, h1])]
    nlinarith only [hs.2, h2, hNh, hb]
  -- The integrated bound.
  have hcsum : Continuous fun s : ℝ => ∑ i ∈ Finset.range N, P.eval (1 + s + i * h) ^ 2 := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_on hh0.le
    (intervalIntegrable_const (c := P.eval b ^ 2))
    ((hcsum.const_mul S).intervalIntegrable 0 h) hpt
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finset_sum fun i _ => by
      exact (by fun_prop : Continuous fun s : ℝ => P.eval (1 + s + i * h) ^ 2).intervalIntegrable
        _ _] at hmono
  have hshift : ∀ i ∈ Finset.range N, ∫ s in (0 : ℝ)..h, P.eval (1 + s + i * h) ^ 2 =
      ∫ x in (1 + (i : ℝ) * h)..(1 + ((i + 1 : ℕ) : ℝ) * h), P.eval x ^ 2 := by
    intro i _
    have e := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := h)
      (fun x : ℝ => P.eval x ^ 2) (1 + (i : ℝ) * h)
    rw [show (fun s : ℝ => P.eval (1 + s + i * h) ^ 2) =
      fun s : ℝ => P.eval (s + (1 + (i : ℝ) * h)) ^ 2 from funext fun s => by
        congr 2
        ring, e]
    congr 1
    · ring
    · push_cast
      ring
  rw [Finset.sum_congr rfl hshift] at hmono
  have hadj := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => 1 + (k : ℝ) * h) (n := N) (f := fun x : ℝ => P.eval x ^ 2)
    (μ := volume) (fun k _ => hc.intervalIntegrable _ _)
  simp only [] at hadj
  rw [hadj, Nat.cast_zero, zero_mul, add_zero, hNh, show (1 : ℝ) + 4 = 5 by norm_num] at hmono
  have hval : (N / 4 : ℝ) * h = 1 := by
    rw [hh]
    field_simp
  rw [← hS]
  calc P.eval b ^ 2 = (N / 4 : ℝ) * (h * P.eval b ^ 2) := by
        rw [← mul_assoc, hval, one_mul]
    _ ≤ (N / 4 : ℝ) * (S * ∫ x in (1 : ℝ)..5, P.eval x ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by ring

/-! ## The tail beyond a height -/

/-- `x^m e^{-(7/5)x} ≤ T^m e^{-(2/5)T} e^{-x}` for `x ≥ T`, once `m ≤ (2/5) T`. -/
theorem pow_mul_exp_tail_of_le {T x : ℝ} {m : ℕ} (hT : 0 < T) (hm : (m : ℝ) ≤ 2 / 5 * T)
    (hx : T ≤ x) :
    x ^ m * Real.exp (-(7 / 5 * x)) ≤ T ^ m * Real.exp (-(2 / 5 * T)) * Real.exp (-x) := by
  obtain ⟨y, hy⟩ : ∃ y, y = x / T := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by rw [hy, one_le_div hT]; exact hx
  have hxy : x = T * y := by rw [hy]; field_simp
  have h1 : y ≤ Real.exp (y - 1) := by
    have := Real.add_one_le_exp (y - 1)
    linarith only [this]
  have h2 : y ^ m ≤ Real.exp (2 / 5 * x - 2 / 5 * T) := by
    have h3 := pow_le_pow_left₀ (by linarith only [hy1]) h1 m
    rw [← Real.exp_nat_mul] at h3
    refine h3.trans (Real.exp_le_exp.mpr ?_)
    rw [hxy]
    nlinarith only [mul_le_mul_of_nonneg_right hm (sub_nonneg.2 hy1)]
  have e : Real.exp (2 / 5 * x - 2 / 5 * T) * Real.exp (-(7 / 5 * x)) =
      Real.exp (-(2 / 5 * T)) * Real.exp (-x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(7 / 5 * x))).le
  rw [e] at h4
  calc x ^ m * Real.exp (-(7 / 5 * x)) = T ^ m * (y ^ m * Real.exp (-(7 / 5 * x))) := by
        rw [hxy]
        ring_nf
        rw [hxy]
        ring_nf
    _ ≤ T ^ m * (Real.exp (-(2 / 5 * T)) * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

/-- The exponential on the exterior of a symmetric window. -/
def tailAt (T b : ℝ) : ℝ := if T < |b| then Real.exp (-|b|) else 0

theorem tailAt_nonneg (T b : ℝ) : 0 ≤ tailAt T b := by
  unfold tailAt
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem integrable_tailAt (T : ℝ) : Integrable (tailAt T) := by
  have hm : Measurable (tailAt T) := by
    unfold tailAt
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    exact measurableSet_lt measurable_const (by fun_prop)
  have hmaj : Integrable fun b : ℝ => Real.exp (-(1 * |b|)) :=
    integrable_exp_neg_mul_abs' (by norm_num)
  refine hmaj.mono' hm.aestronglyMeasurable (ae_of_all _ fun b => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailAt_nonneg T b), one_mul]
  unfold tailAt
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem integral_tailAt {T : ℝ} (hT : 0 ≤ T) : ∫ b, tailAt T b = 2 * Real.exp (-T) := by
  have h := integral_comp_abs (f := fun u : ℝ => if T < u then Real.exp (-u) else 0)
  have e : (∫ u in Ioi (0 : ℝ), (if T < u then Real.exp (-u) else 0)) =
      ∫ u in Ioi T, Real.exp (-1 * u) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    by_cases hu : T < u
    · have h0 : (0 : ℝ) < u := by linarith only [hu, hT]
      simp [indicator, hu, h0]
    · simp [indicator, hu]
  unfold tailAt
  rw [h, e, integral_exp_mul_Ioi (by norm_num) T]
  norm_num

/-! ## The height -/

/-- **The verified height of the section of rank `N`.** -/
def sectionHeight (N : ℕ) : ℝ := 40 + 6 * ((N : ℝ) + 2) * Real.log ((N : ℝ) + 2)

private theorem log_facts {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ Real.log ((N : ℝ) + 2) ∧ Real.log ((N : ℝ) + 2) ≤ ((N : ℝ) + 2) / 2 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  constructor
  · rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9
    linarith only [this, hN']
  · have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 2) / 2 by positivity)
    rw [Real.log_div hy0.ne' (by norm_num)] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith only [this]
    linarith only [h1, h2]

/-- The height pays the tail. -/
theorem section_numeric {N : ℕ} (hN : 1 ≤ N) :
    5 ≤ sectionHeight N ∧ ((2 * (N - 1) : ℕ) : ℝ) ≤ 2 / 5 * sectionHeight N ∧
      6050000000 * ((N : ℝ) / 2) * Real.exp N ^ 2 * sectionHeight N ^ (2 * (N - 1)) *
        Real.exp (-(7 / 5 * sectionHeight N)) ≤ 0.0005 := by
  obtain ⟨hL1, hL2⟩ := log_facts hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (N : ℝ) + 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log y := ⟨_, rfl⟩
  rw [← hy, ← hL] at hL1 hL2
  have hy3 : 3 ≤ y := by rw [hy]; linarith only [hN']
  have hy0 : 0 < y := by linarith only [hy3]
  have hyL : 0 ≤ y * L := by positivity
  obtain ⟨T, hT⟩ : ∃ T, T = sectionHeight N := ⟨_, rfl⟩
  have hTval : T = 40 + 6 * y * L := by rw [hT, sectionHeight, ← hy, ← hL]
  have hT40 : 40 ≤ T := by rw [hTval]; nlinarith only [hyL]
  have hT0 : 0 < T := by linarith only [hT40]
  rw [← hT]
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * (N - 1) := ⟨_, rfl⟩
  have hmr : (m : ℝ) = 2 * y - 6 := by
    rw [hm, hy]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [← hm]
  refine ⟨by linarith only [hT40], ?_, ?_⟩
  · rw [hmr, hTval]
    nlinarith only [hy3, mul_le_mul_of_nonneg_left hL1 hy0.le]
  -- The logarithm of the height.
  have hlogT : Real.log T ≤ 2 * L + 3 := by
    rw [Real.log_le_iff_le_exp hT0, Real.exp_add, ← mul_comm (2 : ℝ), mul_comm L,
      show (2 : ℝ) * L = L + L by ring, Real.exp_add, hL, Real.exp_log hy0]
    have he3 : (20 : ℝ) ≤ Real.exp 3 := by
      have h1 := Real.exp_one_gt_d9
      have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h2]
      calc (20 : ℝ) ≤ (2.7182818283 : ℝ) ^ 3 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1.le 3
    have hTy : T ≤ 20 * (y * y) := by
      rw [hTval, ← hL]
      nlinarith only [hy3, mul_le_mul_of_nonneg_left hL2 hy0.le]
    calc T ≤ 20 * (y * y) := hTy
      _ ≤ y * y * Real.exp 3 := by nlinarith only [mul_le_mul_of_nonneg_left he3 (mul_pos hy0 hy0).le]
  -- Everything in the exponent.
  have h1 : (6050000000 : ℝ) ≤ Real.exp 23 := by
    have h2 : Real.exp 23 = Real.exp 1 ^ 23 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h2]
    calc (6050000000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 23 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 23
  have h2 : (N : ℝ) / 2 ≤ Real.exp L := by
    rw [hL, Real.exp_log hy0, hy]
    linarith only [hN']
  have h3 : T ^ m ≤ Real.exp ((m : ℝ) * (2 * L + 3)) := by
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast]
    refine pow_le_pow_left₀ hT0.le ?_ m
    rw [← Real.log_le_iff_le_exp hT0]
    exact hlogT
  have h4 : Real.exp (-8) ≤ 0.0005 := by
    have h5 : Real.exp (-8) = (Real.exp 1 ^ 8)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      norm_num
    rw [h5]
    calc (Real.exp 1 ^ 8)⁻¹ ≤ ((2.7182818283 : ℝ) ^ 8)⁻¹ :=
          inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8)
      _ ≤ _ := by norm_num
  have hNexp : Real.exp N ^ 2 = Real.exp (2 * N) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hbound : 23 + L + 2 * (N : ℝ) + (m : ℝ) * (2 * L + 3) + -(7 / 5 * T) ≤ -8 := by
    have hNy : (N : ℝ) = y - 2 := by rw [hy]; ring
    rw [hmr, hTval, hNy]
    by_cases hy8 : y < 8
    · nlinarith only [hL1, hy8, hyL]
    · have hL3 : 2 ≤ L := by
        rw [hL, Real.le_log_iff_exp_le hy0]
        have h5 : Real.exp 2 = Real.exp 1 ^ 2 := by
          rw [← Real.exp_nat_mul]
          norm_num
        have h6 := Real.exp_one_lt_d9
        rw [h5]
        nlinarith only [h6, not_lt.1 hy8, Real.exp_pos 1]
      nlinarith only [hL1, hL3, not_lt.1 hy8, hyL, mul_le_mul_of_nonneg_left hL3 hy0.le]
  calc 6050000000 * ((N : ℝ) / 2) * Real.exp N ^ 2 * T ^ m * Real.exp (-(7 / 5 * T))
      ≤ Real.exp 23 * Real.exp L * Real.exp (2 * N) * Real.exp ((m : ℝ) * (2 * L + 3)) *
          Real.exp (-(7 / 5 * T)) := by
        rw [hNexp]
        have hNpos : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
        gcongr
    _ = Real.exp (23 + L + 2 * (N : ℝ) + (m : ℝ) * (2 * L + 3) + -(7 / 5 * T)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-8) := Real.exp_le_exp.mpr hbound
    _ ≤ _ := h4

/-! ## The form -/

private theorem integrable_eval_mul {a : ℝ} (ha : |a| < 1) (Q : ℝ[X]) :
    Integrable fun b : ℝ => Q.eval b * current a b := by
  have e : (fun b : ℝ => Q.eval b * current a b) = fun b : ℝ =>
      ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * (b ^ i * current a b) := by
    funext b
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun i _ => (raw_integrable a ha i).const_mul _

/-- **The form is positive past the height.** -/
theorem form_pos_of_verified {N : ℕ} (hN : 1 ≤ N) (hRH : RHVerifiedThrough (sectionHeight N + 1))
    {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) {P : ℝ[X]} (hdeg : P.degree < N) (hP : P ≠ 0) :
    0 < ∫ b : ℝ, P.eval b ^ 2 * current a b := by
  classical
  have habs : |a| ≤ 1 / 2 := by rw [abs_of_pos ha0]; exact ha
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hT5, hTm, hTnum⟩ := section_numeric hN
  obtain ⟨T, hT⟩ : ∃ T, T = sectionHeight N := ⟨_, rfl⟩
  rw [← hT] at hT5 hTm hTnum hRH
  have hT0 : 0 < T := by linarith only [hT5]
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * (N - 1) := ⟨_, rfl⟩
  rw [← hm] at hTm hTnum
  have hc : Continuous fun x : ℝ => P.eval x ^ 2 := by fun_prop
  obtain ⟨E, hE⟩ : ∃ E, E = ∫ x in (1 : ℝ)..5, P.eval x ^ 2 := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  -- The kernel past five.
  have hker {b : ℝ} (hb : 5 ≤ |b|) :
      P.eval b ^ 2 ≤ (N / 4 : ℝ) * Real.exp N ^ 2 * |b| ^ m * E := by
    have h := sq_eval_le_integral hN hdeg hb
    rw [← hE] at h
    refine h.trans_eq ?_
    rw [hm, pow_mul', mul_pow]
    ring
  have hEpos : 0 < E := by
    refine lt_of_le_of_ne hE0 fun h0 => hP ?_
    refine eq_zero_of_infinite_isRoot P ((Set.Ici_infinite (5 : ℝ)).mono fun x hx => ?_)
    have hx5 : (5 : ℝ) ≤ x := hx
    have h1 := hker (b := x) (by rw [abs_of_nonneg (by linarith only [hx5])]; exact hx5)
    rw [← h0, mul_zero] at h1
    exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm h1 (sq_nonneg _))
  -- The constant of the tail.
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 6050000000 * a * ((N / 4 : ℝ) * Real.exp N ^ 2 * E) *
      (T ^ m * Real.exp (-(2 / 5 * T))) := ⟨_, rfl⟩
  -- The minorant.
  let Lo : ℝ → ℝ := fun b =>
    0.0006 * a * Set.indicator (Icc (1 : ℝ) 5) (fun x => P.eval x ^ 2) b - Z * tailAt T b
  have hind : Integrable (Set.indicator (Icc (1 : ℝ) 5) fun x => P.eval x ^ 2) :=
    (hc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hLo : Integrable Lo := (hind.const_mul _).sub ((integrable_tailAt T).const_mul _)
  have hWint : Integrable fun b : ℝ => P.eval b ^ 2 * current a b := by
    have := integrable_eval_mul ha1 (P ^ 2)
    simpa only [eval_pow] using this
  have hpoint : ∀ b, Lo b ≤ P.eval b ^ 2 * current a b := by
    intro b
    have hW : 0 ≤ P.eval b ^ 2 := sq_nonneg _
    by_cases hb1 : b ∈ Icc (1 : ℝ) 5
    · have habs5 : |b| ≤ 5 := by
        rw [abs_of_pos (by linarith only [hb1.1])]
        exact hb1.2
      have hcore := current_ge_of_abs_le ha0 ha habs5
      have hT0' : tailAt T b = 0 := by
        unfold tailAt
        rw [if_neg (by linarith only [habs5, hT5])]
      simp only [Lo]
      rw [Set.indicator_of_mem hb1, hT0', mul_zero, sub_zero]
      have := mul_le_mul_of_nonneg_left hcore hW
      nlinarith only [this]
    · simp only [Lo]
      rw [Set.indicator_of_notMem hb1, mul_zero, zero_sub]
      by_cases hbT : |b| ≤ T
      · have hcur := current_nonneg_of_rhVerifiedThrough ha0 hRH hbT
        have hT0' : tailAt T b = 0 := by
          unfold tailAt
          rw [if_neg (not_lt.2 hbT)]
        rw [hT0', mul_zero, neg_zero]
        exact mul_nonneg hW hcur
      · have hbT' : T < |b| := not_le.1 hbT
        have hcur := abs_current_le_explicit habs b
        rw [abs_of_pos ha0] at hcur
        have hW2 := hker (b := b) (by linarith only [hbT', hT5])
        have htl := pow_mul_exp_tail_of_le hT0 hTm hbT'.le
        have hTv : tailAt T b = Real.exp (-|b|) := by
          unfold tailAt
          rw [if_pos hbT']
        rw [hTv]
        have hlow : -(P.eval b ^ 2 * (6050000000 * a * Real.exp (-(7 / 5 * |b|)))) ≤
            P.eval b ^ 2 * current a b := by
          have := (abs_le.mp hcur).1
          nlinarith only [mul_le_mul_of_nonneg_left this hW]
        refine le_trans ?_ hlow
        rw [neg_le_neg_iff]
        have hPp : 0 ≤ 6050000000 * a * Real.exp (-(7 / 5 * |b|)) := by positivity
        have h1 := mul_le_mul_of_nonneg_right hW2 hPp
        refine h1.trans ?_
        have hA : 0 ≤ 6050000000 * a * ((N / 4 : ℝ) * Real.exp N ^ 2 * E) := by positivity
        have h2 := mul_le_mul_of_nonneg_left htl hA
        rw [hZ]
        calc (N / 4 : ℝ) * Real.exp N ^ 2 * |b| ^ m * E *
              (6050000000 * a * Real.exp (-(7 / 5 * |b|)))
            = 6050000000 * a * ((N / 4 : ℝ) * Real.exp N ^ 2 * E) *
                (|b| ^ m * Real.exp (-(7 / 5 * |b|))) := by ring
          _ ≤ _ := h2
          _ = _ := by ring
  have hint := integral_mono hLo hWint hpoint
  have hval : ∫ b, Lo b = 0.0006 * a * E - Z * (2 * Real.exp (-T)) := by
    simp only [Lo]
    rw [integral_sub (hind.const_mul _) ((integrable_tailAt T).const_mul _), integral_const_mul,
      integral_const_mul, integral_tailAt hT0.le, integral_indicator measurableSet_Icc,
      setIntegral_congr_set Ioc_ae_eq_Icc.symm, ← intervalIntegral.integral_of_le (by norm_num),
      ← hE]
  rw [hval] at hint
  have hZle : Z * (2 * Real.exp (-T)) ≤ a * E * 0.0005 := by
    have hA : 0 ≤ a * E := by positivity
    have h1 := mul_le_mul_of_nonneg_left hTnum hA
    refine le_trans (le_of_eq ?_) h1
    rw [hZ, show Real.exp (-(7 / 5 * T)) = Real.exp (-(2 / 5 * T)) * Real.exp (-T) by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring
  have hfinal : 0 < a * E := mul_pos ha0 hEpos
  norm_num at hZle hint hfinal ⊢
  nlinarith only [hZle, hint, hfinal]

/-- **Every section from its verified height.** For `0 < a ≤ ½` the signed section of rank `N` is
positive definite once RH holds through `40 + 6 (N+2) log (N+2) + 1`. -/
theorem thetaCuspCenterMixedSignedHankel_posDef_of_rhVerifiedThrough (N : ℕ)
    (hRH : RHVerifiedThrough (sectionHeight N + 1)) {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  classical
  have habs : |a| < 1 := by
    rw [abs_of_pos ha0]
    linarith only [ha]
  apply signed_posDef_of_raw habs N
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a N, fun v hv => ?_⟩
  rw [star_trivial]
  have hN : 1 ≤ N := by
    by_contra hc
    obtain rfl : N = 0 := by omega
    exact hv (Subsingleton.elim v 0)
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ[X], P = ∑ i : Fin N, C (v i) * X ^ (i : ℕ) := ⟨_, rfl⟩
  have hdeg : P.degree < N := by
    rw [hPdef]
    exact degree_sum_fin_lt v
  have hcoeff : ∀ j : Fin N, P.coeff j = v j := by
    intro j
    rw [hPdef, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro i _ hij
      rw [coeff_C_mul_X_pow, if_neg]
      intro h
      exact hij (Fin.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hP : P ≠ 0 := by
    intro h0
    apply hv
    funext j
    rw [← hcoeff j, h0, coeff_zero]
    rfl
  have hpos := form_pos_of_verified hN hRH ha0 ha hdeg hP
  have heval : ∀ b : ℝ, P.eval b ^ 2 * current a b =
      ∑ i : Fin N, ∑ j : Fin N, v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    intro b
    have h1 : P.eval b = ∑ i : Fin N, v i * b ^ (i : ℕ) := by
      rw [hPdef, eval_finset_sum]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [h1, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  simp_rw [heval] at hpos
  rw [integral_finset_sum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (raw_integrable a habs _).const_mul _] at hpos
  have heq : v ⬝ᵥ rawHankel a N *ᵥ v = ∑ i : Fin N, ∫ b : ℝ, ∑ j : Fin N,
      v i * v j * (b ^ ((i : ℕ) + (j : ℕ)) * current a b) := by
    simp only [dotProduct, mulVec, rawHankel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (raw_integrable a habs _).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    unfold rawMoment
    ring
  rwa [heq]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
