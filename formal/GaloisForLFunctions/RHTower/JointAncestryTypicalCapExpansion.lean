import GaloisForLFunctions.RHTower.JointAncestryPhaseOrbitMoments

/-!
# Expansion tools for products of phase factors

* `sum_normSq_sum_mul_phase`: for any unimodular `u` on `ℤ/N` with mean zero,
  `Σ_k |Σ_i c_i u(k_i)|² = N^{|ι|} Σ_i |c_i|²`.
* `exists_prod_one_add_eq_exp_second_order`: if `|u_i| ≤ ½` then
  `∏(1 + u_i) = exp(Σu_i − ½Σu_i² + E)` with `|E| ≤ (2/3)Σ|u_i|³`.
* `norm_cexp_sub_cexp_le_two_mul`: `|e^a − e^b| ≤ 2 e^{Re b} |a − b|` when `|a − b| ≤ 1`.
* `sum_normSq_prod_phaseFactor`: `Σ_k |∏_i g_i(k_i)|² = N^{|ι|} ∏_i (1 + a²(|X_i|² + |Y_i|²))`,
  and the same after any global shift.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Second moments of phase sums -/

theorem sum_mul_phase_mul_conj {N : ℕ} (u : Fin N → ℂ) (hu0 : ∑ x, u x = 0)
    (hu1 : ∀ x, ‖u x‖ = 1) (i i' : ι) :
    ∑ k : ι → Fin N, u (k i) * conj (u (k i')) =
      if i = i' then (N : ℂ) ^ Fintype.card ι else 0 := by
  have hfac : ∀ k : ι → Fin N, u (k i) * conj (u (k i')) =
      ∏ t, ((if t = i then u (k t) else 1) * (if t = i' then conj (u (k t)) else 1)) := by
    intro k
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i, Finset.prod_ite_eq' Finset.univ i']
    simp
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun t x => (if t = i then u x else 1) * (if t = i' then conj (u x) else 1))]
  have hnorm : ∀ x, u x * conj (u x) = 1 := by
    intro x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1]; simp
  split_ifs with h
  · subst h
    have : ∀ t, ∑ x : Fin N, (if t = i then u x else 1) * (if t = i then conj (u x) else 1) = N := by
      intro t
      by_cases ht : t = i
      · simp only [ht, if_true, hnorm]; simp
      · simp [ht]
    simp_rw [this]; simp
  · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [if_true, if_neg h, mul_one]
    exact hu0

/-- **Second moment of a phase sum.** -/
theorem sum_normSq_sum_mul_phase {N : ℕ} (u : Fin N → ℂ) (hu0 : ∑ x, u x = 0)
    (hu1 : ∀ x, ‖u x‖ = 1) (c : ι → ℂ) :
    ∑ k : ι → Fin N, ‖∑ i, c i * u (k i)‖ ^ 2 = (N : ℝ) ^ Fintype.card ι * ∑ i, ‖c i‖ ^ 2 := by
  have hre : ∀ z : ℂ, ‖z‖ ^ 2 = (z * conj z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hre]
  rw [← Complex.re_sum]
  have h1 : ∀ k : ι → Fin N, (∑ i, c i * u (k i)) * conj (∑ i, c i * u (k i)) =
      ∑ i, ∑ i', c i * conj (c i') * (u (k i) * conj (u (k i'))) := by
    intro k
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [map_mul]; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (univ : Finset (ι → Fin N))) (t := (univ : Finset ι))]
  simp_rw [← Finset.mul_sum, sum_mul_phase_mul_conj u hu0 hu1]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Complex.re_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq, mul_comm, Complex.ofReal_re]

/-- **Markov in `L²`.** -/
theorem card_lt_norm_le {α : Type*} [Fintype α] (Y : α → ℂ) {t : ℝ} (ht : 0 < t) :
    ((univ.filter fun x => t < ‖Y x‖).card : ℝ) ≤ (∑ x, ‖Y x‖ ^ 2) / t ^ 2 := by
  have h := card_lt_le_sum_div (fun x => ‖Y x‖ ^ 2) (fun x => sq_nonneg _) (pow_pos ht 2)
  have hsub : (univ.filter fun x => t < ‖Y x‖) ⊆ (univ.filter fun x => t ^ 2 < ‖Y x‖ ^ 2) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact pow_lt_pow_left₀ hx ht.le two_ne_zero
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub) h

/-! ## The logarithmic expansion of a product -/

theorem logTaylor_three (z : ℂ) : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
  simp [Complex.logTaylor, Finset.sum_range_succ]
  ring

omit [DecidableEq ι] in
/-- **Product expansion.** -/
theorem exists_prod_one_add_eq_exp_second_order (u : ι → ℂ) (hu : ∀ i, ‖u i‖ ≤ 1 / 2) :
    ∃ E : ℂ, ‖E‖ ≤ 2 / 3 * ∑ i, ‖u i‖ ^ 3 ∧
      ∏ i, (1 + u i) = Complex.exp (∑ i, u i - (∑ i, u i ^ 2) / 2 + E) := by
  refine ⟨∑ i, (Complex.log (1 + u i) - Complex.logTaylor 3 (u i)), ?_, ?_⟩
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖u i‖ < 1 := by linarith [hu i]
    have h := Complex.norm_log_sub_logTaylor_le 2 h1
    have h2 : (1 - ‖u i‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith [hu i]) (by norm_num)]; linarith [hu i]
    have h3 : 0 ≤ ‖u i‖ ^ 3 := by positivity
    calc ‖Complex.log (1 + u i) - Complex.logTaylor 3 (u i)‖ ≤
        ‖u i‖ ^ (2 + 1) * (1 - ‖u i‖)⁻¹ / ((2 : ℕ) + 1) := by exact_mod_cast h
      _ ≤ ‖u i‖ ^ 3 * 2 / 3 := by
          norm_num
          nlinarith
      _ = 2 / 3 * ‖u i‖ ^ 3 := by ring
  · have hne : ∀ i, 1 + u i ≠ 0 := by
      intro i h
      have : ‖u i‖ = 1 := by
        have : u i = -1 := by linear_combination h
        rw [this, norm_neg, norm_one]
      linarith [hu i]
    have hsum : ∑ i, u i - (∑ i, u i ^ 2) / 2 +
        ∑ i, (Complex.log (1 + u i) - Complex.logTaylor 3 (u i)) =
        ∑ i, Complex.log (1 + u i) := by
      simp_rw [logTaylor_three]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
      ring
    rw [hsum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Complex.exp_log (hne i)).symm

/-- `|e^a − e^b| ≤ 2 e^{Re b} |a − b|` for `|a − b| ≤ 1`. -/
theorem norm_cexp_sub_cexp_le_two_mul {a b : ℂ} (h : ‖a - b‖ ≤ 1) :
    ‖Complex.exp a - Complex.exp b‖ ≤ 2 * Real.exp b.re * ‖a - b‖ := by
  have : Complex.exp a - Complex.exp b = Complex.exp b * (Complex.exp (a - b) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; ring_nf
  rw [this, norm_mul, Complex.norm_exp]
  have := Complex.norm_exp_sub_one_le h
  nlinarith [Real.exp_pos b.re]

/-! ## Second moments of products of phase factors -/

theorem sum_normSq_prod_phaseFactor {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (X Y : ι → ℂ) :
    ∑ k : ι → Fin N, ‖∏ i, phaseFactor N a (X i) (Y i) (k i)‖ ^ 2 =
      (N : ℝ) ^ Fintype.card ι * ∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2)) := by
  simp_rw [norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i j => ‖phaseFactor N a (X i) (Y i) j‖ ^ 2)]
  simp_rw [sum_normSq_phaseFactor hN]
  rw [Finset.prod_mul_distrib]
  simp

theorem sum_normSq_prod_phaseFactor_shift {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (X Y : ι → ℂ)
    (j : Fin N) :
    ∑ k : ι → Fin N, ‖∏ i, phaseFactor N a (X i) (Y i) (phaseShift j k i)‖ ^ 2 =
      (N : ℝ) ^ Fintype.card ι * ∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2)) := by
  haveI : NeZero N := ⟨by omega⟩
  rw [← sum_normSq_prod_phaseFactor hN a X Y]
  exact Fintype.sum_bijective (phaseShift j) (phaseShift_bijective j) _ _ (fun k => rfl)

/-- `Σ_k Σ_j |∏_i g_i(k_i + j)| ≤ N · N^{|ι|} · (∏_i (1 + a²(|X_i|² + |Y_i|²)))^{1/2}`. -/
theorem sum_sum_norm_prod_phaseFactor_shift_le {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (X Y : ι → ℂ) :
    ∑ k : ι → Fin N, ∑ j : Fin N, ‖∏ i, phaseFactor N a (X i) (Y i) (phaseShift j k i)‖ ≤
      N * ((N : ℝ) ^ Fintype.card ι *
        Real.sqrt (∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2)))) := by
  rw [Finset.sum_comm]
  have hj : ∀ j : Fin N, ∑ k : ι → Fin N, ‖∏ i, phaseFactor N a (X i) (Y i) (phaseShift j k i)‖ ≤
      (N : ℝ) ^ Fintype.card ι * Real.sqrt (∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2))) := by
    intro j
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ι → Fin N)) (fun _ => (1 : ℝ))
      (fun k => ‖∏ i, phaseFactor N a (X i) (Y i) (phaseShift j k i)‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
    rw [sum_normSq_prod_phaseFactor_shift hN a X Y j] at hcs
    have hP : 0 ≤ ∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2)) :=
      Finset.prod_nonneg fun i _ => by positivity
    have hS : 0 ≤ ∑ k : ι → Fin N, ‖∏ i, phaseFactor N a (X i) (Y i) (phaseShift j k i)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hn : (0 : ℝ) ≤ (N : ℝ) ^ Fintype.card ι := by positivity
    rw [← Real.sqrt_sq hS, ← Real.sqrt_sq hn, ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    push_cast at hcs
    nlinarith
  calc ∑ j : Fin N, ∑ k : ι → Fin N, ‖∏ i, phaseFactor N a (X i) (Y i) (phaseShift j k i)‖ ≤
      ∑ _j : Fin N, (N : ℝ) ^ Fintype.card ι *
        Real.sqrt (∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2))) := Finset.sum_le_sum fun j _ => hj j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end

end RHTower
