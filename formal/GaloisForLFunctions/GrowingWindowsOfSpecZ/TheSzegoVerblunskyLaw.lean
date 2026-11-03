import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeHasNoSlackUnderRH

/-!
# The Szegő–Verblunsky law

For a positive lattice evolution the margins are `E_n = κ(0)∏_{k<n}(1 − γ_k²)` with `|γ_k| < 1`
(`levinsonErr_eq_prod`). The infinite product decides everything (`tendsto_prod_one_sub_zero_iff`,
`exists_pos_le_prod_one_sub_iff`):

* **Szegő–Verblunsky law** (`tendsto_levinsonErr_zero_iff`, `levinsonErr_bounded_below_iff`): the
  margins tend to `0` iff `Σ_k γ_k² = ∞`, and they stay above a positive constant iff `Σ_k γ_k² < ∞`.
  This is Szegő's dichotomy in the language of Schur parameters: a positive margin at infinity is the
  square-summability of the reflection coefficients.
* **The rate for Spec ℤ** (`not_summable_reflCoeff_sq_of_riemannHypothesis`,
  `riemannHypothesis_iff_not_summable`): under RH the reflection coefficients of every lattice of
  Spec ℤ are not square-summable, and RH is equivalent to every lattice evolution being positive with
  `Σ_k γ_k² = ∞`. The exact collapse of the margins is the failure of `ℓ²`-decay of the Schur
  parameters: they cannot decay faster than `k^{−1/2}` on average, on any lattice.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri

/-! ### Infinite products `∏(1 − x_k)` -/

/-- `∏_{k<n}(1 − x_k) ≤ exp(−Σ_{k<n}x_k)` for `0 ≤ x_k ≤ 1`. -/
theorem prod_one_sub_le_exp {x : ℕ → ℝ} (hx1 : ∀ k, x k ≤ 1) (n : ℕ) :
    ∏ k ∈ range n, (1 - x k) ≤ Real.exp (-∑ k ∈ range n, x k) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun k _ => by linarith [hx1 k]) fun k _ => ?_
  have := Real.add_one_le_exp (-x k)
  linarith

/-- **The product tends to zero iff the series diverges**, for `0 ≤ x_k < 1`. -/
theorem tendsto_prod_one_sub_zero_iff {x : ℕ → ℝ} (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k < 1) :
    Tendsto (fun n => ∏ k ∈ range n, (1 - x k)) atTop (𝓝 0) ↔ ¬ Summable x := by
  have hpos : ∀ n, 0 < ∏ k ∈ range n, (1 - x k) := fun n =>
    Finset.prod_pos fun k _ => by linarith [hx1 k]
  constructor
  · intro ht hs
    -- a summable series keeps the product above a positive constant
    have hy : Summable fun k => x k / (1 - x k) := by
      have hlim := hs.tendsto_atTop_zero
      have hev : ∀ᶠ k in atTop, x k ≤ 1 / 2 := hlim.eventually (ge_mem_nhds (by norm_num))
      refine Summable.of_norm_bounded_eventually_nat (g := fun k => 2 * x k) (hs.mul_left 2) ?_
      filter_upwards [hev] with k hk
      have h1 : 0 < 1 - x k := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hx0 k) h1.le), div_le_iff₀ h1]
      nlinarith [hx0 k]
    set T := ∑' k, x k / (1 - x k)
    have hlow : ∀ n, Real.exp (-T) ≤ ∏ k ∈ range n, (1 - x k) := fun n => by
      have hlog : ∀ k, -(x k / (1 - x k)) ≤ Real.log (1 - x k) := fun k => by
        have h1 : 0 < 1 - x k := by linarith [hx1 k]
        have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
        rw [Real.log_inv] at this
        have e : (1 - x k)⁻¹ - 1 = x k / (1 - x k) := by field_simp; ring
        linarith
      have hsum : -T ≤ ∑ k ∈ range n, Real.log (1 - x k) := by
        have h1 : ∑ k ∈ range n, x k / (1 - x k) ≤ T :=
          hy.sum_le_tsum _ fun k _ => div_nonneg (hx0 k) (by linarith [hx1 k])
        have h2 : -∑ k ∈ range n, x k / (1 - x k) ≤ ∑ k ∈ range n, Real.log (1 - x k) := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_le_sum fun k _ => hlog k
        linarith
      calc Real.exp (-T) ≤ Real.exp (∑ k ∈ range n, Real.log (1 - x k)) := Real.exp_le_exp.mpr hsum
        _ = ∏ k ∈ range n, (1 - x k) := by
          rw [Real.exp_sum]
          exact Finset.prod_congr rfl fun k _ => Real.exp_log (by linarith [hx1 k])
    have hc := Real.exp_pos (-T)
    have := ht.eventually (gt_mem_nhds hc)
    obtain ⟨n, hn⟩ := this.exists
    linarith [hlow n]
  · intro hns
    have hdiv : Tendsto (fun n => ∑ k ∈ range n, x k) atTop atTop :=
      (not_summable_iff_tendsto_nat_atTop_of_nonneg hx0).mp hns
    have hexp : Tendsto (fun n => Real.exp (-∑ k ∈ range n, x k)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
      (fun n => (hpos n).le) fun n => prod_one_sub_le_exp (fun k => (hx1 k).le) n

/-! ### The law for the Levinson evolution -/

variable {κ : ℤ → ℝ}

theorem reflCoeff_sq_lt_one_of_pos (hE : ∀ n, 0 < levinsonErr κ n) (k : ℕ) :
    reflCoeff κ k ^ 2 < 1 :=
  (sq_lt_one_iff_abs_lt_one _).mpr ((levinsonErr_pos_iff.mp hE).2 k)

/-- **Szegő–Verblunsky law, collapse.** For a positive evolution the margins tend to `0` iff the
reflection coefficients are not square-summable. -/
theorem tendsto_levinsonErr_zero_iff (hE : ∀ n, 0 < levinsonErr κ n) :
    Tendsto (fun n => levinsonErr κ n) atTop (𝓝 0) ↔
      ¬ Summable fun k => reflCoeff κ k ^ 2 := by
  have h0 : 0 < κ 0 := hE 0
  have hprod : (fun n => levinsonErr κ n) =
      fun n => κ 0 * ∏ k ∈ range n, (1 - reflCoeff κ k ^ 2) := funext fun n =>
    levinsonErr_eq_prod n fun k _ => (hE k).ne'
  rw [hprod, ← tendsto_prod_one_sub_zero_iff (fun k => sq_nonneg _)
    (reflCoeff_sq_lt_one_of_pos hE)]
  constructor
  · intro h
    have := h.const_mul (κ 0)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ h0.ne'] using this
  · intro h
    simpa using h.const_mul (κ 0)

/-- **Szegő–Verblunsky law, positive limit.** For a positive evolution the margins stay above a
positive constant iff the reflection coefficients are square-summable. -/
theorem levinsonErr_bounded_below_iff (hE : ∀ n, 0 < levinsonErr κ n) :
    (∃ c > 0, ∀ n, c ≤ levinsonErr κ n) ↔ Summable fun k => reflCoeff κ k ^ 2 := by
  have hanti : Antitone fun n => levinsonErr κ n :=
    antitone_nat_of_succ_le fun n => levinsonErr_succ_le (hE n)
  constructor
  · rintro ⟨c, hc, hle⟩
    by_contra hns
    have ht := (tendsto_levinsonErr_zero_iff hE).mpr hns
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hc)).exists
    linarith [hle n]
  · intro hs
    by_contra hc
    push Not at hc
    apply (tendsto_levinsonErr_zero_iff hE).mp ?_ hs
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n, hn⟩ := hc ε hε
    refine ⟨n, fun m hm => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (hE m)]
    exact lt_of_le_of_lt (hanti hm) hn

/-! ### Spec ℤ -/

/-- **The rate for Spec ℤ.** Under RH the reflection coefficients of every lattice of Spec ℤ are not
square-summable. -/
theorem not_summable_reflCoeff_sq_of_riemannHypothesis (hRH : RiemannHypothesis) {φ : ℝ → ℝ}
    (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) :
    ¬ Summable fun k => reflCoeff (weilSeq φ h) k ^ 2 := by
  obtain ⟨hpos, ht⟩ := tendsto_levinsonErr_of_riemannHypothesis hRH hφ hφ0 hh
  exact (tendsto_levinsonErr_zero_iff hpos).mp ht

/-- **RH as the failure of `ℓ²`-decay.** RH holds iff for every nonzero bump and step the lattice
evolution of Spec ℤ is positive and its reflection coefficients are not square-summable. -/
theorem riemannHypothesis_iff_not_summable :
    RiemannHypothesis ↔
      ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h →
        (∀ n, 0 < levinsonErr (weilSeq φ h) n) ∧ ¬ Summable fun k => reflCoeff (weilSeq φ h) k ^ 2 :=
  ⟨fun hRH _ hφ hφ0 _ hh => ⟨(tendsto_levinsonErr_of_riemannHypothesis hRH hφ hφ0 hh).1,
      not_summable_reflCoeff_sq_of_riemannHypothesis hRH hφ hφ0 hh⟩,
    fun H => riemannHypothesis_iff_levinsonErr_pos.mpr fun φ hφ hφ0 h hh => (H φ hφ hφ0 h hh).1⟩

end GaloisForLFunctions.GrowingWindowsOfSpecZ
