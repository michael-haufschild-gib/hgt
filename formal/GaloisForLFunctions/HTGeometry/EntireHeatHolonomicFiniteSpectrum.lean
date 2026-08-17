import Mathlib

/-!
# Entire-heat holonomic anchors have finite spectrum

Let `(a_n)` be complex numbers such that the one-sided periodic heat orbit

`u(t,z) = ∑_{n ≥ 0} a_n e^{-4π²n²t} e^{2πinz}`

converges at every point of `ℂ²`, and let `h(w) = ∑ a_n w^n` be the multiplicative Fourier
anchor.  If `h` is D-finite — it satisfies a linear differential equation with polynomial
coefficients, not all zero — then `a_n = 0` for all large `n`
(`entireHeat_dFinite_finite_spectrum`); equivalently `h` is a polynomial
(`entireHeat_dFinite_isPolynomial`), so the heat orbit has finite spectrum.

The proof is the card's, in three steps.

* **Super-Gaussian decay.**  Evaluating the orbit at `t = -A/(4π²)`, `z = 0` makes the series
  `∑ a_n e^{An²}` converge, so its terms are bounded: `‖a_n‖ ≤ M_A e^{-An²}` for every `A > 0`
  (`exists_superGaussian_bound`).
* **D-finite ⟹ P-recursive.**  Extracting the coefficient of `w^{M+K}` from
  `∑_i p_i h^{(i)} = 0` turns the differential equation into a recurrence
  `∑_{j ≤ K+m} q_j(M) a_{M+j} = 0` valid for *every* `M ≥ 0`, with explicit polynomial
  coefficients `q_j = recurCoeff p m K j` (`recurrence_of_dFinite`).  The coefficient attached to
  the top differential order and the top degree survives because the `i`-th contribution to `q_j`
  is a *monic* polynomial of degree exactly `i`, so distinct differential orders cannot cancel
  (`recurCoeff_ne_zero`, `exists_recurCoeff_ne_zero`).  Discarding the vanishing lowest shifts
  (`exists_lowest_shift`) normalizes the recurrence to one with nonzero lowest coefficient.
* **The two scales contradict.**  A nonzero term propagates along a finite-width path with only a
  polynomially growing loss per step, which forces the subsequence to decay no faster than
  `exp(-D n log n)`; super-Gaussian decay is faster
  (`eventually_eq_zero_of_recurrence_of_superGaussian`).

The Lean propagation argument uses a crude exponential bound `‖q_j(n)/q_0(n)‖ ≤ E e^{Dn}` in place
of the card's sharper `C n^d`; this is legitimate because the decay hypothesis is available for
*every* `A > 0`, so `A` may be chosen after `D` and the recurrence width `r`.  The resulting
contradiction is between `exp(D r k²)` and `exp(-(D r + 2) k²)`, a purely quadratic comparison.

Everything here is stated for formal power series (`PowerSeries ℂ` with
`PowerSeries.derivativeFun`), which is the standard formal-power-series meaning of D-finite and
agrees with the analytic one for the entire anchor of the card.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.EntireHeatHolonomic


/-! ## Crude exponential bounds for polynomial values -/

theorem norm_polyEval_le (p : Polynomial ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ‖p.eval (n : ℂ)‖ ≤ (∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖)
      * Real.exp ((p.natDegree : ℝ) * n) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have heval : p.eval (n : ℂ) = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (n : ℂ) ^ k := by
    rw [Polynomial.eval_eq_sum_range]
  rw [heval]
  have hstep : ‖∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (n : ℂ) ^ k‖
      ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * (n : ℝ) ^ p.natDegree := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k hk => ?_))
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    have hk' : k ≤ p.natDegree := by
      have := Finset.mem_range.mp hk
      omega
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR hk') (norm_nonneg _)
  refine le_trans hstep ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun k _ => norm_nonneg _))
  have hexp : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    have := Real.add_one_le_exp (n : ℝ)
    linarith
  calc (n : ℝ) ^ p.natDegree ≤ (Real.exp (n : ℝ)) ^ p.natDegree :=
        pow_le_pow_left₀ (by linarith) hexp _
    _ = Real.exp ((p.natDegree : ℝ) * n) := by
        rw [← Real.exp_nat_mul]

/-- A nonzero complex polynomial has a positive lower bound on its values at large naturals. -/
theorem exists_lower_bound_polyEval {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ n : ℕ, N ≤ n → c ≤ ‖p.eval (n : ℂ)‖ := by
  rcases eq_or_lt_of_le (Nat.zero_le p.natDegree) with hdeg | hdeg
  · refine ⟨‖p.coeff 0‖, 0, ?_, ?_⟩
    · rw [norm_pos_iff]
      intro hc
      apply hp
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg.symm, hc, map_zero]
    · intro n _
      have hC : p.eval (n : ℂ) = p.coeff 0 := by
        conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg.symm]
        rw [Polynomial.eval_C]
      rw [hC]
  · have hdegree : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
    have hz : Filter.Tendsto (fun n : ℕ => ‖(n : ℂ)‖) Filter.atTop Filter.atTop := by
      simpa [Complex.norm_natCast] using tendsto_natCast_atTop_atTop (R := ℝ)
    have htend : Filter.Tendsto (fun n : ℕ => ‖p.eval ((n : ℂ))‖) Filter.atTop Filter.atTop :=
      Polynomial.tendsto_norm_atTop p hdegree hz
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp htend 1).exists_forall_of_atTop
    exact ⟨1, N, one_pos, fun n hn => hN n hn⟩


/-! ## Super-Gaussian decay annihilates a P-recursive tail -/

theorem eventually_eq_zero_of_recurrence_of_superGaussian
    {b : ℕ → ℂ} {r N₀ : ℕ} {q : ℕ → Polynomial ℂ}
    (hq0 : q 0 ≠ 0)
    (hrec : ∀ N : ℕ, N₀ ≤ N →
      ∑ j ∈ Finset.range (r + 1), (q j).eval (N : ℂ) * b (N + j) = 0)
    (hdecay : ∀ A : ℝ, 0 < A → ∃ M : ℝ, ∀ n : ℕ, ‖b n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ 2)) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → b n = 0 := by
  classical
  obtain ⟨c, Nc, hc, hcle⟩ := exists_lower_bound_polyEval hq0
  -- a uniform exponential upper bound for all the coefficient polynomials
  set D : ℕ := ∑ j ∈ Finset.range (r + 1), (q j).natDegree with hD
  set Cb : ℝ := ∑ j ∈ Finset.range (r + 1),
    (∑ k ∈ Finset.range ((q j).natDegree + 1), ‖(q j).coeff k‖) with hCb
  have hCb0 : 0 ≤ Cb := by
    refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
  have hqbound : ∀ j ∈ Finset.range (r + 1), ∀ n : ℕ, 1 ≤ n →
      ‖(q j).eval (n : ℂ)‖ ≤ Cb * Real.exp ((D : ℝ) * n) := by
    intro j hj n hn
    have h1 := norm_polyEval_le (q j) n hn
    have h2 : (∑ k ∈ Finset.range ((q j).natDegree + 1), ‖(q j).coeff k‖) ≤ Cb := by
      rw [hCb]
      refine Finset.single_le_sum (f := fun j => ∑ k ∈ Finset.range ((q j).natDegree + 1),
        ‖(q j).coeff k‖) (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _)) hj
    have h3 : ((q j).natDegree : ℝ) ≤ (D : ℝ) := by
      have : (q j).natDegree ≤ D := by
        rw [hD]
        exact Finset.single_le_sum (f := fun j => (q j).natDegree) (fun i _ => Nat.zero_le _) hj
      exact_mod_cast this
    have h4 : Real.exp (((q j).natDegree : ℝ) * n) ≤ Real.exp ((D : ℝ) * n) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg n)
    calc ‖(q j).eval (n : ℂ)‖
        ≤ (∑ k ∈ Finset.range ((q j).natDegree + 1), ‖(q j).coeff k‖)
            * Real.exp (((q j).natDegree : ℝ) * n) := h1
      _ ≤ Cb * Real.exp ((D : ℝ) * n) := by
          refine mul_le_mul h2 h4 (Real.exp_pos _).le hCb0
  set N₂ : ℕ := max (max N₀ Nc) 1 with hN₂
  set E : ℝ := max 1 ((r : ℝ) * Cb / c) with hE
  have hE1 : (1 : ℝ) ≤ E := le_max_left _ _
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le one_pos hE1
  -- the one-step propagation
  have hstep : ∀ n : ℕ, N₂ ≤ n → b n ≠ 0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ ‖b n‖ ≤ (E * Real.exp ((D : ℝ) * n)) * ‖b (n + j)‖ := by
    intro n hn hbn
    have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnc : Nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hsplit := hrec n hn0
    rw [Finset.sum_range_succ'] at hsplit
    have hkey : (q 0).eval (n : ℂ) * b (n + 0)
        = -∑ i ∈ Finset.range r, (q (i + 1)).eval (n : ℂ) * b (n + (i + 1)) := by
      linear_combination hsplit
    have hnorm : ‖(q 0).eval (n : ℂ)‖ * ‖b n‖
        ≤ ∑ i ∈ Finset.range r, ‖(q (i + 1)).eval (n : ℂ)‖ * ‖b (n + (i + 1))‖ := by
      have h1 : ‖(q 0).eval (n : ℂ) * b (n + 0)‖
          = ‖(q 0).eval (n : ℂ)‖ * ‖b n‖ := by rw [norm_mul]; norm_num
      rw [← h1, hkey, norm_neg]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
      rw [norm_mul]
    have hrpos : 0 < r := by
      by_contra hr0
      have hr : r = 0 := by omega
      rw [hr] at hnorm
      simp only [Finset.range_zero, Finset.sum_empty] at hnorm
      have h1 : c * ‖b n‖ ≤ 0 := by
        refine le_trans (mul_le_mul_of_nonneg_right (hcle n hnc) (norm_nonneg _)) hnorm
      have h2 : 0 < ‖b n‖ := norm_pos_iff.mpr hbn
      nlinarith
    obtain ⟨i₀, hi₀mem, hi₀max⟩ := Finset.exists_max_image (Finset.range r)
      (fun i => ‖b (n + (i + 1))‖) ⟨0, Finset.mem_range.mpr hrpos⟩
    refine ⟨i₀ + 1, by omega, by
      have := Finset.mem_range.mp hi₀mem
      omega, ?_⟩
    have hbig : ∑ i ∈ Finset.range r, ‖(q (i + 1)).eval (n : ℂ)‖ * ‖b (n + (i + 1))‖
        ≤ (r : ℝ) * (Cb * Real.exp ((D : ℝ) * n)) * ‖b (n + (i₀ + 1))‖ := by
      have hterm : ∀ i ∈ Finset.range r, ‖(q (i + 1)).eval (n : ℂ)‖ * ‖b (n + (i + 1))‖
          ≤ (Cb * Real.exp ((D : ℝ) * n)) * ‖b (n + (i₀ + 1))‖ := by
        intro i hi
        have hi' : i + 1 ∈ Finset.range (r + 1) := by
          have := Finset.mem_range.mp hi
          exact Finset.mem_range.mpr (by omega)
        refine mul_le_mul (hqbound (i + 1) hi' n hn1) (hi₀max i hi) (norm_nonneg _) ?_
        positivity
      calc ∑ i ∈ Finset.range r, ‖(q (i + 1)).eval (n : ℂ)‖ * ‖b (n + (i + 1))‖
          ≤ ∑ _i ∈ Finset.range r, (Cb * Real.exp ((D : ℝ) * n)) * ‖b (n + (i₀ + 1))‖ :=
            Finset.sum_le_sum hterm
        _ = (r : ℝ) * (Cb * Real.exp ((D : ℝ) * n)) * ‖b (n + (i₀ + 1))‖ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    have hclow : c * ‖b n‖ ≤ (r : ℝ) * (Cb * Real.exp ((D : ℝ) * n)) * ‖b (n + (i₀ + 1))‖ :=
      le_trans (le_trans (mul_le_mul_of_nonneg_right (hcle n hnc) (norm_nonneg _)) hnorm) hbig
    have hfinal : ‖b n‖ ≤ ((r : ℝ) * Cb / c) * Real.exp ((D : ℝ) * n) * ‖b (n + (i₀ + 1))‖ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith [hclow]
    refine le_trans hfinal ?_
    have hEge : ((r : ℝ) * Cb / c) ≤ E := le_max_right _ _
    have hpos : (0 : ℝ) ≤ Real.exp ((D : ℝ) * n) * ‖b (n + (i₀ + 1))‖ := by positivity
    nlinarith [hpos, hEge, Real.exp_pos ((D : ℝ) * n), norm_nonneg (b (n + (i₀ + 1)))]
  choose! nxt hnxt1 hnxt2 hnxt3 using hstep
  refine ⟨N₂, fun n₀ hn₀ => ?_⟩
  by_contra hbn₀
  set path : ℕ → ℕ := fun k => Nat.rec n₀ (fun _ m => m + nxt m) k with hpathdef
  have hpath0 : path 0 = n₀ := rfl
  have hpathS : ∀ k, path (k + 1) = path k + nxt (path k) := fun k => rfl
  have hinv : ∀ k : ℕ, N₂ ≤ path k ∧ b (path k) ≠ 0 ∧ n₀ + k ≤ path k ∧ path k ≤ n₀ + r * k ∧
      ‖b n₀‖ ≤ (∏ i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * path i))) * ‖b (path k)‖ := by
    intro k
    induction k with
    | zero =>
        refine ⟨by rw [hpath0]; exact hn₀, by rw [hpath0]; exact hbn₀, by rw [hpath0]; omega, by
          rw [hpath0]; omega, ?_⟩
        rw [hpath0, Finset.range_zero, Finset.prod_empty, one_mul]
    | succ k ih =>
        obtain ⟨h1, h2, h3, h4, h5⟩ := ih
        have hj1 := hnxt1 (path k) h1 h2
        have hj2 := hnxt2 (path k) h1 h2
        have hj3 := hnxt3 (path k) h1 h2
        have hstep' : ‖b (path k)‖
            ≤ (E * Real.exp ((D : ℝ) * path k)) * ‖b (path (k + 1))‖ := by
          rw [hpathS k]
          exact hj3
        have hposK : (0 : ℝ) < E * Real.exp ((D : ℝ) * path k) := by positivity
        have hbne : b (path (k + 1)) ≠ 0 := by
          intro hzero
          rw [hzero, norm_zero, mul_zero] at hstep'
          exact h2 (norm_eq_zero.mp (le_antisymm hstep' (norm_nonneg _)))
        refine ⟨?_, hbne, ?_, ?_, ?_⟩
        · rw [hpathS k]; omega
        · rw [hpathS k]; omega
        · rw [hpathS k]
          have hrk : r * (k + 1) = r * k + r := by ring
          omega
        · rw [Finset.prod_range_succ]
          calc ‖b n₀‖ ≤ (∏ i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * path i)))
                * ‖b (path k)‖ := h5
            _ ≤ (∏ i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * path i)))
                * ((E * Real.exp ((D : ℝ) * path k)) * ‖b (path (k + 1))‖) := by
                refine mul_le_mul_of_nonneg_left hstep' ?_
                exact Finset.prod_nonneg (fun i _ => by positivity)
            _ = (∏ i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * path i)))
                * (E * Real.exp ((D : ℝ) * path k)) * ‖b (path (k + 1))‖ := by ring
  -- bound the accumulated product
  have hprodle : ∀ k : ℕ, (∏ i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * path i)))
      ≤ E ^ k * Real.exp ((D : ℝ) * k * ((n₀ : ℝ) + r * k)) := by
    intro k
    have hbound : ∀ i ∈ Finset.range k,
        (E * Real.exp ((D : ℝ) * path i)) ≤ E * Real.exp ((D : ℝ) * ((n₀ : ℝ) + r * k)) := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hpi : (path i : ℝ) ≤ (n₀ : ℝ) + r * k := by
        have := (hinv i).2.2.2.1
        have h2 : (path i : ℝ) ≤ ((n₀ + r * i : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h2
        have h3 : (r : ℝ) * i ≤ (r : ℝ) * k := by
          have : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik.le
          exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg r)
        linarith
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hE0.le
      exact mul_le_mul_of_nonneg_left hpi (Nat.cast_nonneg D)
    calc (∏ i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * path i)))
        ≤ ∏ _i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * ((n₀ : ℝ) + r * k))) :=
          Finset.prod_le_prod (fun i _ => by positivity) hbound
      _ = (E * Real.exp ((D : ℝ) * ((n₀ : ℝ) + r * k))) ^ k := by
          rw [Finset.prod_const, Finset.card_range]
      _ = E ^ k * Real.exp ((D : ℝ) * k * ((n₀ : ℝ) + r * k)) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          ring
  obtain ⟨M, hM⟩ := hdecay ((D : ℝ) * r + 2) (by positivity)
  have hM0 : (0 : ℝ) ≤ M := by
    have h0 := hM 0
    simp only [Nat.cast_zero] at h0
    have : Real.exp (-((D : ℝ) * r + 2) * (0 : ℝ) ^ 2) = 1 := by norm_num
    rw [this, mul_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hchain : ∀ k : ℕ, ‖b n₀‖ ≤ M * Real.exp ((k : ℝ) * (Real.log E + (D : ℝ) * n₀) - 2 * k ^ 2) := by
    intro k
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv k
    have hbk : ‖b (path k)‖ ≤ M * Real.exp (-((D : ℝ) * r + 2) * (k : ℝ) ^ 2) := by
      refine le_trans (hM (path k)) ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM0
      have hk : (k : ℝ) ≤ (path k : ℝ) := by
        have : (k : ℝ) ≤ ((n₀ + k : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n₀]
        have h2' : ((n₀ + k : ℕ) : ℝ) ≤ (path k : ℝ) := by exact_mod_cast h3
        linarith
      have hsq : (k : ℝ) ^ 2 ≤ (path k : ℝ) ^ 2 := by
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
      have hA : (0 : ℝ) < (D : ℝ) * r + 2 := by positivity
      nlinarith
    have hEk : E ^ k = Real.exp ((k : ℝ) * Real.log E) := by
      rw [← Real.exp_log hE0, ← Real.exp_nat_mul, Real.log_exp]
    calc ‖b n₀‖ ≤ (∏ i ∈ Finset.range k, (E * Real.exp ((D : ℝ) * path i))) * ‖b (path k)‖ := h5
      _ ≤ (E ^ k * Real.exp ((D : ℝ) * k * ((n₀ : ℝ) + r * k)))
            * (M * Real.exp (-((D : ℝ) * r + 2) * (k : ℝ) ^ 2)) := by
          refine mul_le_mul (hprodle k) hbk (norm_nonneg _) ?_
          positivity
      _ = M * (Real.exp ((k : ℝ) * Real.log E + (D : ℝ) * k * ((n₀ : ℝ) + (r : ℝ) * k))
            * Real.exp (-((D : ℝ) * r + 2) * (k : ℝ) ^ 2)) := by
          rw [hEk, ← Real.exp_add]
          ring
      _ = M * Real.exp ((k : ℝ) * (Real.log E + (D : ℝ) * n₀) - 2 * (k : ℝ) ^ 2) := by
          rw [← Real.exp_add]
          congr 2
          ring
  -- the two scales contradict
  have htend : Filter.Tendsto (fun k : ℕ => M * Real.exp (-(k : ℝ))) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) Filter.atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr
        (tendsto_natCast_atTop_atTop (R := ℝ)))
      exact this
    simpa using h1.const_mul M
  have hev : ∀ᶠ k : ℕ in Filter.atTop, ‖b n₀‖ ≤ M * Real.exp (-(k : ℝ)) := by
    obtain ⟨K, hK⟩ := exists_nat_ge ((Real.log E + (D : ℝ) * n₀ + 1) / 2)
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    refine le_trans (hchain k) ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM0
    have hkK : ((K : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2k : Real.log E + (D : ℝ) * n₀ + 1 ≤ 2 * (k : ℝ) := by
      have : (Real.log E + (D : ℝ) * n₀ + 1) / 2 ≤ (k : ℝ) := le_trans hK hkK
      linarith
    nlinarith
  have hle0 : ‖b n₀‖ ≤ 0 := ge_of_tendsto htend hev
  exact hbn₀ (norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _)))


/-! ## D-finite formal power series are P-recursive -/

theorem coeff_iterate_derivativeFun (i : ℕ) : ∀ (F : PowerSeries ℂ) (n : ℕ),
    PowerSeries.coeff n (PowerSeries.derivativeFun^[i] F)
      = (∏ l ∈ Finset.range i, ((n + l + 1 : ℕ) : ℂ)) * PowerSeries.coeff (n + i) F := by
  induction i with
  | zero => intro F n; simp
  | succ i ih =>
      intro F n
      rw [Function.iterate_succ_apply, ih (PowerSeries.derivativeFun F) n,
        PowerSeries.coeff_derivativeFun, Finset.prod_range_succ]
      have hidx : n + i + 1 = n + (i + 1) := by omega
      rw [hidx]
      push_cast
      ring

theorem coeff_polynomial_mul {p : Polynomial ℂ} {K : ℕ} (hK : p.natDegree ≤ K)
    (G : PowerSeries ℂ) (M : ℕ) :
    PowerSeries.coeff (M + K) ((p : PowerSeries ℂ) * G)
      = ∑ k ∈ Finset.range (K + 1), p.coeff k * PowerSeries.coeff (M + (K - k)) G := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => PowerSeries.coeff k (p : PowerSeries ℂ) * PowerSeries.coeff l G)]
  have hsub : Finset.range (K + 1) ⊆ Finset.range ((M + K).succ) := by
    intro k hk
    have := Finset.mem_range.mp hk
    exact Finset.mem_range.mpr (by omega)
  have hzero : ∀ k ∈ Finset.range ((M + K).succ), k ∉ Finset.range (K + 1) →
      PowerSeries.coeff k (p : PowerSeries ℂ) * PowerSeries.coeff (M + K - k) G = 0 := by
    intro k _ hk
    have hkK : K < k := by
      by_contra hc
      exact hk (Finset.mem_range.mpr (by omega))
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkK : k ≤ K := by
    have := Finset.mem_range.mp hk
    omega
  have hidx : M + K - k = M + (K - k) := by omega
  rw [hidx, Polynomial.coeff_coe]


/-- The monic shift factor `∏_{l<i}(X + (s+l+1))`. -/
def shiftFactor (s i : ℕ) : Polynomial ℂ :=
  ∏ l ∈ Finset.range i, (Polynomial.X + Polynomial.C ((s + l + 1 : ℕ) : ℂ))

theorem shiftFactor_monic (s i : ℕ) : (shiftFactor s i).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun l _ => Polynomial.monic_X_add_C _)

theorem shiftFactor_natDegree (s i : ℕ) : (shiftFactor s i).natDegree = i := by
  rw [shiftFactor, Polynomial.natDegree_prod _ _ (fun _ _ => (Polynomial.monic_X_add_C _).ne_zero)]
  have hdeg : ∀ l ∈ Finset.range i,
      (Polynomial.X + Polynomial.C ((s + l + 1 : ℕ) : ℂ)).natDegree = 1 :=
    fun l _ => Polynomial.natDegree_X_add_C _
  rw [Finset.sum_congr rfl hdeg]
  simp

theorem eval_shiftFactor (s i M : ℕ) :
    (shiftFactor s i).eval (M : ℂ) = ∏ l ∈ Finset.range i, ((M + s + l + 1 : ℕ) : ℂ) := by
  rw [shiftFactor, Polynomial.eval_prod]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  ring

/-- The index set of the induced recurrence. -/
def recurIndex (m K : ℕ) : Finset (ℕ × ℕ) := Finset.range (m + 1) ×ˢ Finset.range (K + 1)

/-- The shift-`j` coefficient polynomial of the recurrence induced by a linear differential
equation with polynomial coefficients. -/
def recurCoeff (p : ℕ → Polynomial ℂ) (m K j : ℕ) : Polynomial ℂ :=
  ∑ ik ∈ (recurIndex m K).filter (fun ik => (K - ik.2) + ik.1 = j),
    Polynomial.C ((p ik.1).coeff ik.2) * shiftFactor (K - ik.2) ik.1

theorem recurrence_of_dFinite {F : PowerSeries ℂ} {m : ℕ} {p : ℕ → Polynomial ℂ} {K : ℕ}
    (hK : ∀ i ∈ Finset.range (m + 1), (p i).natDegree ≤ K)
    (heq : ∑ i ∈ Finset.range (m + 1), (p i : PowerSeries ℂ)
        * PowerSeries.derivativeFun^[i] F = 0) (M : ℕ) :
    ∑ j ∈ Finset.range (K + m + 1),
      (recurCoeff p m K j).eval (M : ℂ) * PowerSeries.coeff (M + j) F = 0 := by
  classical
  set g : ℕ × ℕ → ℂ := fun ik => ((p ik.1).coeff ik.2 * (shiftFactor (K - ik.2) ik.1).eval (M : ℂ))
    * PowerSeries.coeff (M + ((K - ik.2) + ik.1)) F with hg
  have hmaps : ∀ ik ∈ recurIndex m K, (K - ik.2) + ik.1 ∈ Finset.range (K + m + 1) := by
    intro ik hik
    rw [recurIndex, Finset.mem_product] at hik
    have h1 := Finset.mem_range.mp hik.1
    have h2 := Finset.mem_range.mp hik.2
    exact Finset.mem_range.mpr (by omega)
  have hstep1 : ∀ j ∈ Finset.range (K + m + 1),
      (recurCoeff p m K j).eval (M : ℂ) * PowerSeries.coeff (M + j) F
        = ∑ ik ∈ (recurIndex m K).filter (fun ik => (K - ik.2) + ik.1 = j), g ik := by
    intro j _
    rw [recurCoeff, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun ik hik => ?_)
    have hik' : (K - ik.2) + ik.1 = j := (Finset.mem_filter.mp hik).2
    rw [hg, ← hik', Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.sum_congr rfl hstep1, Finset.sum_fiberwise_of_maps_to hmaps g, recurIndex,
    Finset.sum_product]
  have hinner : ∀ i ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (K + 1), g (i, k)
        = PowerSeries.coeff (M + K) ((p i : PowerSeries ℂ) * PowerSeries.derivativeFun^[i] F) := by
    intro i hi
    rw [coeff_polynomial_mul (hK i hi)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hg]
    rw [coeff_iterate_derivativeFun, eval_shiftFactor]
    have hidx : M + (K - k) + i = M + ((K - k) + i) := by omega
    rw [hidx]
    ring
  rw [Finset.sum_congr rfl hinner, ← map_sum, heq, map_zero]


theorem coeff_shiftFactor_self (s i : ℕ) : (shiftFactor s i).coeff i = 1 := by
  have h := (shiftFactor_monic s i).coeff_natDegree
  rwa [shiftFactor_natDegree] at h

theorem coeff_shiftFactor_of_lt {s i n : ℕ} (h : i < n) : (shiftFactor s i).coeff n = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  rwa [shiftFactor_natDegree]

theorem recurCoeff_ne_zero {p : ℕ → Polynomial ℂ} {m K i₁ : ℕ}
    (hK : ∀ i ∈ Finset.range (m + 1), (p i).natDegree ≤ K)
    (hi₁ : i₁ ∈ Finset.range (m + 1)) (hp₁ : p i₁ ≠ 0)
    (hmax : ∀ i ∈ Finset.range (m + 1), i₁ < i → p i = 0) :
    recurCoeff p m K ((K - (p i₁).natDegree) + i₁) ≠ 0 := by
  classical
  set k₁ : ℕ := (p i₁).natDegree with hk₁
  set j : ℕ := (K - k₁) + i₁ with hj
  have hk₁K : k₁ ≤ K := hK i₁ hi₁
  have hmem : ((i₁, k₁) : ℕ × ℕ)
      ∈ (recurIndex m K).filter (fun ik => (K - ik.2) + ik.1 = j) := by
    refine Finset.mem_filter.mpr ⟨?_, rfl⟩
    rw [recurIndex, Finset.mem_product]
    exact ⟨hi₁, Finset.mem_range.mpr (by omega)⟩
  have hzero : ∀ ik ∈ (recurIndex m K).filter (fun ik => (K - ik.2) + ik.1 = j),
      ik ≠ (i₁, k₁) →
      ((p ik.1).coeff ik.2) * (shiftFactor (K - ik.2) ik.1).coeff i₁ = 0 := by
    intro ik hik hne
    obtain ⟨hikS, hikf⟩ := Finset.mem_filter.mp hik
    rw [recurIndex, Finset.mem_product] at hikS
    have h1 : ik.1 ≤ m := by have := Finset.mem_range.mp hikS.1; omega
    have h2 : ik.2 ≤ K := by have := Finset.mem_range.mp hikS.2; omega
    rcases lt_trichotomy ik.1 i₁ with hlt | heq | hgt
    · rw [coeff_shiftFactor_of_lt hlt, mul_zero]
    · exfalso
      apply hne
      have hk : ik.2 = k₁ := by
        rw [heq] at hikf
        omega
      exact Prod.ext heq hk
    · have : p ik.1 = 0 := hmax ik.1 (Finset.mem_range.mpr (by omega)) hgt
      rw [this, Polynomial.coeff_zero, zero_mul]
  intro hcon
  have hcoeff : (recurCoeff p m K j).coeff i₁ = (p i₁).coeff k₁ := by
    rw [recurCoeff, Polynomial.finsetSum_coeff]
    rw [Finset.sum_congr rfl (fun ik _ => Polynomial.coeff_C_mul _)]
    rw [Finset.sum_eq_single_of_mem ((i₁, k₁) : ℕ × ℕ) hmem hzero, coeff_shiftFactor_self, mul_one]
  rw [hcon, Polynomial.coeff_zero] at hcoeff
  exact hp₁ (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

theorem exists_recurCoeff_ne_zero {p : ℕ → Polynomial ℂ} {m K : ℕ}
    (hK : ∀ i ∈ Finset.range (m + 1), (p i).natDegree ≤ K)
    (hne : ∃ i ∈ Finset.range (m + 1), p i ≠ 0) :
    ∃ j ∈ Finset.range (K + m + 1), recurCoeff p m K j ≠ 0 := by
  classical
  set S : Finset ℕ := (Finset.range (m + 1)).filter (fun i => p i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi, hpi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hpi⟩⟩
  set i₁ : ℕ := S.max' hSne with hi₁def
  have hi₁S : i₁ ∈ S := S.max'_mem hSne
  obtain ⟨hi₁, hp₁⟩ := Finset.mem_filter.mp hi₁S
  have hmax : ∀ i ∈ Finset.range (m + 1), i₁ < i → p i = 0 := by
    intro i hi hlt
    by_contra hpi
    have : i ∈ S := Finset.mem_filter.mpr ⟨hi, hpi⟩
    have := S.le_max' i this
    omega
  refine ⟨(K - (p i₁).natDegree) + i₁, ?_, recurCoeff_ne_zero hK hi₁ hp₁ hmax⟩
  have h1 : i₁ ≤ m := by have := Finset.mem_range.mp hi₁; omega
  exact Finset.mem_range.mpr (by omega)


theorem exists_lowest_shift {b : ℕ → ℂ} {r : ℕ} {q : ℕ → Polynomial ℂ}
    (hne : ∃ j ∈ Finset.range (r + 1), q j ≠ 0)
    (hrec : ∀ N : ℕ, ∑ j ∈ Finset.range (r + 1), (q j).eval (N : ℂ) * b (N + j) = 0) :
    ∃ (j₀ r' : ℕ) (q' : ℕ → Polynomial ℂ), q' 0 ≠ 0 ∧
      ∀ N : ℕ, ∑ t ∈ Finset.range (r' + 1), (q' t).eval (N : ℂ) * b (N + j₀ + t) = 0 := by
  classical
  set S : Finset ℕ := (Finset.range (r + 1)).filter (fun j => q j ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨j, hj, hqj⟩ := hne
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hqj⟩⟩
  set j₀ : ℕ := S.min' hSne with hj₀def
  have hj₀S : j₀ ∈ S := S.min'_mem hSne
  obtain ⟨hj₀mem, hq₀⟩ := Finset.mem_filter.mp hj₀S
  have hj₀r : j₀ ≤ r := by have := Finset.mem_range.mp hj₀mem; omega
  have hlow : ∀ j, j < j₀ → q j = 0 := by
    intro j hj
    by_contra hqj
    by_cases hjr : j ∈ Finset.range (r + 1)
    · have : j ∈ S := Finset.mem_filter.mpr ⟨hjr, hqj⟩
      have := S.min'_le j this
      omega
    · exact hqj (by
        exfalso
        exact hjr (Finset.mem_range.mpr (by omega)))
  refine ⟨j₀, r - j₀, fun t => q (j₀ + t), hq₀, fun N => ?_⟩
  have hsplit := Finset.sum_Ico_consecutive
    (fun j => (q j).eval (N : ℂ) * b (N + j)) (Nat.zero_le j₀) (by omega : j₀ ≤ r + 1)
  have hzeroLow : ∑ j ∈ Finset.Ico 0 j₀, (q j).eval (N : ℂ) * b (N + j) = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have : j < j₀ := (Finset.mem_Ico.mp hj).2
    rw [hlow j this, Polynomial.eval_zero, zero_mul]
  have htotal : ∑ j ∈ Finset.Ico 0 (r + 1), (q j).eval (N : ℂ) * b (N + j) = 0 := by
    rw [← Finset.range_eq_Ico]
    exact hrec N
  rw [hzeroLow, zero_add, htotal] at hsplit
  rw [Finset.sum_Ico_eq_sum_range] at hsplit
  have hlen : r + 1 - j₀ = (r - j₀) + 1 := by omega
  rw [hlen] at hsplit
  refine Eq.trans ?_ hsplit
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have : N + j₀ + t = N + (j₀ + t) := by omega
  rw [this]

/-! ## The entire-heat theorem -/

theorem exists_superGaussian_bound {a : ℕ → ℂ}
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (A : ℝ) (hA : 0 < A) :
    ∃ M : ℝ, ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ 2) := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpi : (4 * (Real.pi : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hpiC)
  set t₀ : ℂ := ((-(A / (4 * Real.pi ^ 2)) : ℝ) : ℂ) with ht₀
  have hterm : ∀ n : ℕ,
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t₀)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * 0)
      = a n * Complex.exp (((A * (n : ℝ) ^ 2 : ℝ) : ℂ)) := by
    intro n
    rw [mul_zero, Complex.exp_zero, mul_one]
    congr 1
    rw [ht₀]
    push_cast
    field_simp
  have hsum := hheat t₀ 0
  rw [funext hterm] at hsum
  have htend := hsum.tendsto_atTop_zero
  obtain ⟨M, hM⟩ := htend.norm.bddAbove_range
  refine ⟨max M 0, fun n => ?_⟩
  have hMn : ‖a n * Complex.exp (((A * (n : ℝ) ^ 2 : ℝ) : ℂ))‖ ≤ M :=
    hM (Set.mem_range_self n)
  rw [norm_mul, Complex.norm_exp_ofReal] at hMn
  have hpos : (0 : ℝ) < Real.exp (A * (n : ℝ) ^ 2) := Real.exp_pos _
  have hMn' : ‖a n‖ ≤ M / Real.exp (A * (n : ℝ) ^ 2) := (le_div_iff₀ hpos).mpr hMn
  have hexpn : Real.exp (-A * (n : ℝ) ^ 2) = (Real.exp (A * (n : ℝ) ^ 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  calc ‖a n‖ ≤ M / Real.exp (A * (n : ℝ) ^ 2) := hMn'
    _ ≤ max M 0 / Real.exp (A * (n : ℝ) ^ 2) := by gcongr; exact le_max_left _ _
    _ = max M 0 * Real.exp (-A * (n : ℝ) ^ 2) := by rw [hexpn, div_eq_mul_inv]


/-- **Entire-heat holonomic anchors have finite spectrum.**  If the one-sided periodic heat orbit
`u(t,z) = ∑ a_n e^{-4π²n²t} e^{2πinz}` converges at every point of `ℂ²` and the multiplicative
generating function `h(w) = ∑ a_n w^n` is D-finite, then `a_n = 0` for all large `n`. -/
theorem entireHeat_dFinite_finite_spectrum {a : ℕ → ℂ} {m : ℕ} {p : ℕ → Polynomial ℂ}
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (hne : ∃ i ∈ Finset.range (m + 1), p i ≠ 0)
    (hdfin : ∑ i ∈ Finset.range (m + 1), (p i : PowerSeries ℂ)
        * PowerSeries.derivativeFun^[i] (PowerSeries.mk a) = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n = 0 := by
  classical
  set K : ℕ := ∑ i ∈ Finset.range (m + 1), (p i).natDegree with hKdef
  have hKle : ∀ i ∈ Finset.range (m + 1), (p i).natDegree ≤ K := by
    intro i hi
    rw [hKdef]
    exact Finset.single_le_sum (f := fun i => (p i).natDegree) (fun _ _ => Nat.zero_le _) hi
  obtain ⟨j₁, hj₁mem, hj₁ne⟩ := exists_recurCoeff_ne_zero hKle hne
  have hrec : ∀ N : ℕ, ∑ j ∈ Finset.range (K + m + 1),
      (recurCoeff p m K j).eval (N : ℂ) * a (N + j) = 0 := by
    intro N
    have h := recurrence_of_dFinite hKle hdfin N
    simpa [PowerSeries.coeff_mk] using h
  obtain ⟨j₀, r', q', hq'0, hrec'⟩ := exists_lowest_shift ⟨j₁, hj₁mem, hj₁ne⟩ hrec
  have hrecb : ∀ N : ℕ, ∑ t ∈ Finset.range (r' + 1),
      (q' t).eval (N : ℂ) * (fun n => a (n + j₀)) (N + t) = 0 := by
    intro N
    rw [← hrec' N]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have hidx : N + t + j₀ = N + j₀ + t := by omega
    simp only [hidx]
  have hdecayb : ∀ A : ℝ, 0 < A →
      ∃ M : ℝ, ∀ n : ℕ, ‖(fun n => a (n + j₀)) n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ 2) := by
    intro A hA
    obtain ⟨M, hM⟩ := exists_superGaussian_bound hheat A hA
    refine ⟨max M 0, fun n => ?_⟩
    have h1 : ‖a (n + j₀)‖ ≤ M * Real.exp (-A * ((n + j₀ : ℕ) : ℝ) ^ 2) := hM (n + j₀)
    have hMle : M ≤ max M 0 := le_max_left _ _
    have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    have hsq : ((n : ℝ)) ^ 2 ≤ ((n + j₀ : ℕ) : ℝ) ^ 2 := by
      have hle : (n : ℝ) ≤ ((n + j₀ : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j₀]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have hexp : Real.exp (-A * ((n + j₀ : ℕ) : ℝ) ^ 2) ≤ Real.exp (-A * (n : ℝ) ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc ‖a (n + j₀)‖ ≤ M * Real.exp (-A * ((n + j₀ : ℕ) : ℝ) ^ 2) := h1
      _ ≤ max M 0 * Real.exp (-A * ((n + j₀ : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hMle (Real.exp_pos _).le
      _ ≤ max M 0 * Real.exp (-A * (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hexp hM0
  obtain ⟨N₁, hN₁⟩ := eventually_eq_zero_of_recurrence_of_superGaussian
    (b := fun n => a (n + j₀)) (N₀ := 0) hq'0 (fun N _ => hrecb N) hdecayb
  refine ⟨N₁ + j₀, fun n hn => ?_⟩
  have hz : a ((n - j₀) + j₀) = 0 := hN₁ (n - j₀) (by omega)
  rwa [Nat.sub_add_cancel (by omega : j₀ ≤ n)] at hz


theorem exists_polynomial_of_eventually_zero {a : ℕ → ℂ} {N : ℕ} (h : ∀ n, N ≤ n → a n = 0) :
    ∃ P : Polynomial ℂ, ∀ n : ℕ, a n = P.coeff n := by
  classical
  refine ⟨∑ k ∈ Finset.range N, Polynomial.C (a k) * Polynomial.X ^ k, fun n => ?_⟩
  rw [Polynomial.finsetSum_coeff]
  have hterm : ∀ k ∈ Finset.range N,
      (Polynomial.C (a k) * Polynomial.X ^ k).coeff n = if n = k then a k else 0 := by
    intro k _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hnk : n = k
    · simp [hnk]
    · simp [hnk]
  rw [Finset.sum_congr rfl hterm]
  by_cases hn : n < N
  · rw [Finset.sum_ite_eq]
    simp [Finset.mem_range.mpr hn]
  · have h1 : a n = 0 := h n (by omega)
    rw [h1, Finset.sum_ite_eq]
    simp [Finset.mem_range, hn]

/-- **The card's statement.**  An entire-complex-time one-sided periodic heat orbit whose
multiplicative Fourier anchor is D-finite has finite spectrum: the anchor is a polynomial. -/
theorem entireHeat_dFinite_isPolynomial {a : ℕ → ℂ} {m : ℕ} {p : ℕ → Polynomial ℂ}
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (hne : ∃ i ∈ Finset.range (m + 1), p i ≠ 0)
    (hdfin : ∑ i ∈ Finset.range (m + 1), (p i : PowerSeries ℂ)
        * PowerSeries.derivativeFun^[i] (PowerSeries.mk a) = 0) :
    ∃ P : Polynomial ℂ, ∀ n : ℕ, a n = P.coeff n := by
  obtain ⟨N, hN⟩ := entireHeat_dFinite_finite_spectrum hheat hne hdfin
  exact exists_polynomial_of_eventually_zero hN


end GaloisForLFunctions.EntireHeatHolonomic

end
