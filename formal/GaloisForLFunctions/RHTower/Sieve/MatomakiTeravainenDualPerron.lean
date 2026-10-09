import GaloisForLFunctions.RHTower.Sieve.PerronFiniteSum
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDIOverHeight

/-!
# Perron's formula for a twisted unit block with moving endpoints

For `M ≥ 1`, integers `0 ≤ m₁ ≤ m₂ ≤ 4M`, `U > 0` and real `τ`,

`|Σ_{M<k≤2M, m₁<k≤m₂} k^{iτ}| ≤ ((m₁+m₂+1)/2π) ∫_{−U}^{U} |B(u−τ)|/|1+iu| du + 100 M²/U`,

where `B(t) = Σ_{M<n≤2M} n^{−1−it}` is the unit Perron block (`norm_sum_dual_le_perron`).

Apply the finite Perron formula `norm_sum_lt_sub_perron_integral_le` on the line `σ = 1` to
`c_n = n^{iτ}` at the half-integer cutoffs `x_j = m_j + ½` and subtract. Since
`n^{iτ} n^{−1−it} = n^{−1−i(t−τ)}`, the Dirichlet polynomial is `B(t − τ)`. Since
`|x₂^{1+it} − x₁^{1+it}| ≤ x₁ + x₂ = m₁ + m₂ + 1`, the difference of the two main terms is the
displayed integral. Each Perron error term is at most `(2x²/n + 2x)/(πU) ≤ 50M/(πU)`, because
`|x − n| ≥ ½`, `M < n` and `x ≤ 4M + ½`. There are `M` terms and two cutoffs.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Filter Topology

/-- `n < m + ½ ↔ n ≤ m` for a natural `n` and an integer `m`. -/
theorem natCast_lt_intCast_add_half_iff (n : ℕ) (m : ℤ) :
    ((n : ℝ) < (m : ℝ) + 1 / 2) ↔ (n : ℤ) ≤ m := by
  constructor
  · intro h
    by_contra hc
    have h1 : m + 1 ≤ (n : ℤ) := by omega
    have h2 : ((m + 1 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  · intro h
    have h2 : ((n : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    push_cast at h2
    linarith

/-- `|n − (m + ½)| ≥ ½` for a natural `n` and an integer `m`. -/
theorem half_le_abs_natCast_sub_intCast_add_half (n : ℕ) (m : ℤ) :
    1 / 2 ≤ |((m : ℝ) + 1 / 2) - n| := by
  rcases le_or_gt (n : ℤ) m with h | h
  · have h2 : ((n : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    push_cast at h2
    rw [abs_of_pos (by linarith)]
    linarith
  · have h1 : m + 1 ≤ (n : ℤ) := by omega
    have h2 : ((m + 1 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    rw [abs_of_neg (by linarith)]
    linarith

/-- **The Perron error at distance `≥ ½`**: `(x/n)/|log(x/n)| ≤ 2x²/n + 2x`. -/
theorem div_div_abs_log_le {x n : ℝ} (hx : 0 < x) (hn : 0 < n) (hxn : 1 / 2 ≤ |x - n|) :
    (x / n) / |Real.log (x / n)| ≤ 2 * x ^ 2 / n + 2 * x := by
  have hq : 0 < x / n := div_pos hx hn
  rcases lt_or_gt_of_ne (show x ≠ n by rintro rfl; norm_num at hxn) with h | h
  · -- `x < n`: `log(n/x) ≥ 1 − x/n ≥ 1/(2n)`
    have hlog : 1 - x / n ≤ Real.log (n / x) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hn hx)
      rwa [inv_div] at this
    have hneg : Real.log (x / n) = -Real.log (n / x) := by
      rw [← Real.log_inv, inv_div]
    rw [abs_of_neg (by linarith [Real.log_neg hq (by rwa [div_lt_one hn])] : Real.log (x / n) < 0),
      hneg, neg_neg]
    rw [abs_of_neg (by linarith)] at hxn
    have h1 : 1 / (2 * n) ≤ Real.log (n / x) := by
      refine le_trans ?_ hlog
      rw [div_le_iff₀ (by positivity)]
      have : (1 - x / n) * (2 * n) = 2 * (n - x) := by field_simp
      rw [this]
      linarith
    calc x / n / Real.log (n / x) ≤ x / n / (1 / (2 * n)) :=
          div_le_div_of_nonneg_left hq.le (by positivity) h1
      _ = 2 * x := by field_simp
      _ ≤ _ := by have : 0 ≤ 2 * x ^ 2 / n := by positivity
                  linarith
  · -- `n < x`: `log(x/n) ≥ 1 − n/x ≥ 1/(2x)`
    have hlog : 1 - n / x ≤ Real.log (x / n) := by
      have := Real.one_sub_inv_le_log_of_pos hq
      rwa [inv_div] at this
    rw [abs_of_pos (by linarith)] at hxn
    have h1 : 1 / (2 * x) ≤ Real.log (x / n) := by
      refine le_trans ?_ hlog
      rw [div_le_iff₀ (by positivity)]
      have : (1 - n / x) * (2 * x) = 2 * (x - n) := by field_simp
      rw [this]
      linarith
    rw [abs_of_pos (lt_of_lt_of_le (by positivity) h1)]
    calc x / n / Real.log (x / n) ≤ x / n / (1 / (2 * x)) :=
          div_le_div_of_nonneg_left hq.le (by positivity) h1
      _ = 2 * x ^ 2 / n := by field_simp
      _ ≤ _ := by linarith

/-- The Dirichlet polynomial of `n^{iτ}` on `(M, 2M]` at `1 + it` is the unit block at `t − τ`. -/
theorem sum_cpow_mul_cpow_eq_mtWattUnitBlock (M : ℕ) (τ t : ℝ) :
    ∑ n ∈ Finset.Ioc M (2 * M), (n : ℂ) ^ ((τ : ℂ) * I) * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * I)) =
      mtWattUnitBlock M (2 * M) (t - τ) := by
  rw [mtWattUnitBlock_eq_sum_Ico, show Finset.Ico (M + 1) (2 * M + 1) = Finset.Ioc M (2 * M) by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have : 0 < n := by simp at hn; omega
    exact_mod_cast this.ne'
  rw [← Complex.cpow_add _ _ hn0]
  congr 1
  push_cast
  ring

theorem continuous_cpow_one_add_mul_I {x : ℝ} (hx : 0 < x) :
    Continuous fun t : ℝ => (x : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℝ) * I) :=
  (by fun_prop : Continuous fun t : ℝ => ((1 : ℝ) : ℂ) + (t : ℝ) * I).const_cpow
    (Or.inl (by exact_mod_cast hx.ne'))

theorem ofReal_one_add_mul_I_ne_zero (t : ℝ) : ((1 : ℝ) : ℂ) + (t : ℝ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- **Perron's formula with moving dual endpoints.** -/
theorem norm_sum_dual_le_perron {M : ℕ} (hM : 1 ≤ M) {m₁ m₂ : ℤ} (hm₁ : 0 ≤ m₁)
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ 4 * M) {U τ : ℝ} (hU : 0 < U) :
    ‖∑ k ∈ (Finset.Ioc M (2 * M)).filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂),
        (k : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤
      ((m₁ + m₂ + 1 : ℝ) / (2 * Real.pi)) * (∫ u in (-U)..U,
        ‖mtWattUnitBlock M (2 * M) (u - τ)‖ / ‖(1 : ℂ) + (u : ℂ) * Complex.I‖) +
      100 * (M : ℝ) ^ 2 / U := by
  classical
  set s : Finset ℕ := Finset.Ioc M (2 * M) with hs
  let c : ℕ → ℂ := fun n => (n : ℂ) ^ ((τ : ℂ) * I)
  have hs0 : 0 ∉ s := by simp [hs]
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hm₁r : (0 : ℝ) ≤ m₁ := by exact_mod_cast hm₁
  have hm₁₂r : (m₁ : ℝ) ≤ m₂ := by exact_mod_cast hm₁₂
  have hm₂r : (m₂ : ℝ) ≤ 4 * M := by exact_mod_cast hm₂
  have hx₁ : (0 : ℝ) < (m₁ : ℝ) + 1 / 2 := by linarith
  have hx₂ : (0 : ℝ) < (m₂ : ℝ) + 1 / 2 := by linarith
  have hne : ∀ (m : ℤ), ∀ n ∈ s, (n : ℝ) ≠ (m : ℝ) + 1 / 2 := fun m n _ h => by
    have := half_le_abs_natCast_sub_intCast_add_half n m
    rw [← h, sub_self, abs_zero] at this
    norm_num at this
  have h₂ := norm_sum_lt_sub_perron_integral_le (c := c) hs0 hx₂ (hne m₂) one_pos hU
  have h₁ := norm_sum_lt_sub_perron_integral_le (c := c) hs0 hx₁ (hne m₁) one_pos hU
  -- the per-cutoff error
  have herr : ∀ m : ℤ, 0 ≤ m → m ≤ 4 * M →
      ∑ n ∈ s, ‖c n‖ * ((((m : ℝ) + 1 / 2) / n) ^ (1 : ℝ) /
        (Real.pi * U * |Real.log (((m : ℝ) + 1 / 2) / n)|)) ≤ 50 * (M : ℝ) ^ 2 / (Real.pi * U) := by
    intro m hm0 hm4
    have hmr : (0 : ℝ) ≤ m := by exact_mod_cast hm0
    have hm4r : (m : ℝ) ≤ 4 * M := by exact_mod_cast hm4
    have hterm : ∀ n ∈ s, ‖c n‖ * ((((m : ℝ) + 1 / 2) / n) ^ (1 : ℝ) /
        (Real.pi * U * |Real.log (((m : ℝ) + 1 / 2) / n)|)) ≤ 50 * M / (Real.pi * U) := by
      intro n hn
      have hn' : M < n ∧ n ≤ 2 * M := by simpa [hs] using hn
      have hnr : (M : ℝ) < n := by exact_mod_cast hn'.1
      have hnpos : (0 : ℝ) < n := by linarith
      have hcn : ‖c n‖ = 1 := by
        show ‖(n : ℂ) ^ ((τ : ℂ) * I)‖ = 1
        rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
        simp
      have hd := div_div_abs_log_le (by linarith : (0 : ℝ) < (m : ℝ) + 1 / 2) hnpos
        (half_le_abs_natCast_sub_intCast_add_half n m)
      rw [hcn, one_mul, Real.rpow_one, show Real.pi * U * |Real.log (((m : ℝ) + 1 / 2) / n)| =
        |Real.log (((m : ℝ) + 1 / 2) / n)| * (Real.pi * U) by ring, ← div_div]
      refine div_le_div_of_nonneg_right (hd.trans ?_) (by positivity)
      have hxle : (m : ℝ) + 1 / 2 ≤ 9 / 2 * M := by linarith
      have hsq : ((m : ℝ) + 1 / 2) ^ 2 ≤ (9 / 2 * M) ^ 2 := by
        exact pow_le_pow_left₀ (by linarith) hxle 2
      have h2 : 2 * ((m : ℝ) + 1 / 2) ^ 2 / n ≤ 2 * (9 / 2 * M) ^ 2 / M := by
        rw [div_le_div_iff₀ hnpos (by linarith)]
        nlinarith
      have h3 : 2 * (9 / 2 * (M : ℝ)) ^ 2 / M = 81 / 2 * M := by field_simp; ring
      linarith
    calc ∑ n ∈ s, ‖c n‖ * ((((m : ℝ) + 1 / 2) / n) ^ (1 : ℝ) /
          (Real.pi * U * |Real.log (((m : ℝ) + 1 / 2) / n)|))
        ≤ ∑ _n ∈ s, 50 * (M : ℝ) / (Real.pi * U) := Finset.sum_le_sum hterm
      _ = 50 * (M : ℝ) ^ 2 / (Real.pi * U) := by
        rw [Finset.sum_const, hs, Nat.card_Ioc, show 2 * M - M = M by omega, nsmul_eq_mul]
        ring
  have he₁ := herr m₁ hm₁ (by omega)
  have he₂ := herr m₂ (by omega) hm₂
  -- the partial sums
  have hsplit : (∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₂ : ℝ) + 1 / 2), c n) -
      (∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₁ : ℝ) + 1 / 2), c n) =
      ∑ k ∈ s.filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂), c k := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [natCast_lt_intCast_add_half_iff]
    split_ifs <;> first | (exfalso; omega) | ring
  -- the main terms
  set D : ℝ → ℂ := fun t => ∑ n ∈ s, c n * (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * I)) with hD
  have hDc : Continuous D := by
    have : D = fun t => mtWattUnitBlock M (2 * M) (t - τ) := by
      funext t; exact sum_cpow_mul_cpow_eq_mtWattUnitBlock M τ t
    rw [this]
    exact (continuous_perronPoly _ _ _).comp (continuous_id.sub continuous_const)
  have hG : ∀ {x : ℝ}, 0 < x → Continuous fun t : ℝ =>
      D t * ((x : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℝ) * I) / (((1 : ℝ) : ℂ) + (t : ℝ) * I)) :=
    fun hx => hDc.mul ((continuous_cpow_one_add_mul_I hx).div (by fun_prop)
      ofReal_one_add_mul_I_ne_zero)
  obtain ⟨P₁, hP₁⟩ : ∃ P, P = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-U)..U,
      D t * ((((m₁ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℝ) * I) /
        (((1 : ℝ) : ℂ) + (t : ℝ) * I)) := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P, P = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-U)..U,
      D t * ((((m₂ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℝ) * I) /
        (((1 : ℝ) : ℂ) + (t : ℝ) * I)) := ⟨_, rfl⟩
  rw [← hP₁] at h₁
  rw [← hP₂] at h₂
  have hmain : ‖P₂ - P₁‖ ≤ ((m₁ + m₂ + 1 : ℝ) / (2 * Real.pi)) * ∫ u in (-U)..U,
      ‖mtWattUnitBlock M (2 * M) (u - τ)‖ / ‖(1 : ℂ) + (u : ℂ) * Complex.I‖ := by
    rw [hP₁, hP₂, ← mul_sub, ← intervalIntegral.integral_sub ((hG hx₂).intervalIntegrable _ _)
      ((hG hx₁).intervalIntegrable _ _), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have hUU : -U ≤ U := by linarith
    refine (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hUU)
      (by positivity)).trans ?_
    have hbc : Continuous fun u : ℝ =>
        ‖mtWattUnitBlock M (2 * M) (u - τ)‖ / ‖(1 : ℂ) + (u : ℂ) * Complex.I‖ :=
      ((continuous_perronPoly _ _ _).comp (continuous_id.sub continuous_const)).norm.div
        (continuous_norm.comp (by fun_prop : Continuous fun u : ℝ => (1 : ℂ) + (u : ℂ) * Complex.I))
        fun u => norm_ne_zero_iff.2 (one_add_mul_I_ne_zero u)
    suffices hint : (∫ u in (-U)..U, ‖D u * ((((m₂ : ℝ) + 1 / 2 : ℝ) : ℂ) ^
        (((1 : ℝ) : ℂ) + (u : ℝ) * I) / (((1 : ℝ) : ℂ) + (u : ℝ) * I)) -
          D u * ((((m₁ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (u : ℝ) * I) /
            (((1 : ℝ) : ℂ) + (u : ℝ) * I))‖) ≤ (m₁ + m₂ + 1 : ℝ) * ∫ u in (-U)..U,
          ‖mtWattUnitBlock M (2 * M) (u - τ)‖ / ‖(1 : ℂ) + (u : ℂ) * Complex.I‖ by
      calc 1 / (2 * Real.pi) * (∫ u in (-U)..U, ‖D u * ((((m₂ : ℝ) + 1 / 2 : ℝ) : ℂ) ^
            (((1 : ℝ) : ℂ) + (u : ℝ) * I) / (((1 : ℝ) : ℂ) + (u : ℝ) * I)) -
              D u * ((((m₁ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (u : ℝ) * I) /
                (((1 : ℝ) : ℂ) + (u : ℝ) * I))‖)
          ≤ 1 / (2 * Real.pi) * ((m₁ + m₂ + 1 : ℝ) * ∫ u in (-U)..U,
            ‖mtWattUnitBlock M (2 * M) (u - τ)‖ / ‖(1 : ℂ) + (u : ℂ) * Complex.I‖) :=
            mul_le_mul_of_nonneg_left hint (by positivity)
        _ = _ := by ring
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hUU
      (((hG hx₂).sub (hG hx₁)).norm.intervalIntegrable _ _)
      ((continuous_const.mul hbc).intervalIntegrable _ _) fun u _ => ?_
    rw [← mul_sub, norm_mul, ← sum_cpow_mul_cpow_eq_mtWattUnitBlock M τ u]
    have hden : ‖((1 : ℝ) : ℂ) + (u : ℝ) * I‖ = ‖(1 : ℂ) + (u : ℂ) * Complex.I‖ := by
      push_cast; rfl
    rw [← sub_div, norm_div, ← hden]
    have hpow : ∀ {x : ℝ}, 0 < x → ‖((x : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (u : ℝ) * I)‖ = x := by
      intro x hx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    have hnum : ‖((((m₂ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (u : ℝ) * I)) -
        ((((m₁ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (u : ℝ) * I))‖ ≤
        (m₁ + m₂ + 1 : ℝ) := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [hpow hx₂, hpow hx₁]
      ring
    have hd0 : 0 < ‖((1 : ℝ) : ℂ) + (u : ℝ) * I‖ := norm_pos_iff.2 (ofReal_one_add_mul_I_ne_zero u)
    calc ‖D u‖ * (‖((((m₂ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (u : ℝ) * I)) -
          ((((m₁ : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (u : ℝ) * I))‖ /
          ‖((1 : ℝ) : ℂ) + (u : ℝ) * I‖)
        ≤ ‖D u‖ * ((m₁ + m₂ + 1 : ℝ) / ‖((1 : ℝ) : ℂ) + (u : ℝ) * I‖) := by gcongr
      _ = (m₁ + m₂ + 1 : ℝ) * (‖D u‖ / ‖((1 : ℝ) : ℂ) + (u : ℝ) * I‖) := by ring
  -- assemble
  have htot : (∑ k ∈ s.filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂), c k) =
      ((∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₂ : ℝ) + 1 / 2), c n) - P₂) -
        ((∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₁ : ℝ) + 1 / 2), c n) - P₁) + (P₂ - P₁) := by
    rw [← hsplit]; ring
  show ‖∑ k ∈ s.filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂), c k‖ ≤ _
  rw [htot]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hfin : 50 * (M : ℝ) ^ 2 / (Real.pi * U) + 50 * (M : ℝ) ^ 2 / (Real.pi * U) ≤
      100 * (M : ℝ) ^ 2 / U := by
    rw [← add_div, show 50 * (M : ℝ) ^ 2 + 50 * (M : ℝ) ^ 2 = 100 * (M : ℝ) ^ 2 by ring,
      div_le_div_iff₀ (by positivity) hU]
    have : 0 ≤ 100 * (M : ℝ) ^ 2 * U := by positivity
    nlinarith
  calc ‖((∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₂ : ℝ) + 1 / 2), c n) - P₂) -
        ((∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₁ : ℝ) + 1 / 2), c n) - P₁) + (P₂ - P₁)‖
      ≤ ‖(∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₂ : ℝ) + 1 / 2), c n) - P₂‖ +
          ‖(∑ n ∈ s.filter (fun n : ℕ => (n : ℝ) < (m₁ : ℝ) + 1 / 2), c n) - P₁‖ + ‖P₂ - P₁‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 50 * (M : ℝ) ^ 2 / (Real.pi * U) + 50 * (M : ℝ) ^ 2 / (Real.pi * U) +
          ((m₁ + m₂ + 1 : ℝ) / (2 * Real.pi)) * (∫ u in (-U)..U,
            ‖mtWattUnitBlock M (2 * M) (u - τ)‖ / ‖(1 : ℂ) + (u : ℂ) * Complex.I‖) := by
        gcongr
        · exact h₂.trans he₂
        · exact h₁.trans he₁
    _ ≤ _ := by linarith

end RHTower.Sieve
