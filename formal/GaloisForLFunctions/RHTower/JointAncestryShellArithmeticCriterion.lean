import GaloisForLFunctions.RHTower.JointAncestryShellPowerSumCriterion
import GaloisForLFunctions.RHTower.JointAncestryChainPeaks

/-!
# A prime-side power-sum criterion for RH from dyadic shells

For the shell `P_N = primes in (N, 2N]` and an integer `k ≥ 1` put

`A_k(N) = Σ_{p₁,…,p_k ∈ P_N} (p₁⋯p_k)^{−3/2} 𝓔(p₁⋯p_k)`   (`jasShellArithmeticSum`),

where `𝓔(X) = (X − ψ(X)) + X(Σ_{n≤X} Λ(n)/n − log X + γ) − log 2π + Σ_{j≥1} X^{−2j}/(2j(2j+1))`
(`lagPrimeSide`) is the prime side of the explicit formula with the genus kernel `1/(s(1−s))`.

**Theorem** (`riemannHypothesis_iff_zerosApproachLine_and_shellArithmetic_growth`).

`RH ⟺ ZAL ∧ ∀ ε > 0, ∃ᶠ N, ∀ k ≥ 1, |A_k(N)| ≤ N^{εk}`,

and the same with "no off-line chain" in place of ZAL
(`riemannHypothesis_iff_not_jasOffLineChain_and_shellArithmetic_growth`).

**Mechanism.**
* By the explicit formula `Σ_ρ X^ρ/(ρ(1−ρ)) = 𝓔(X)` (`lag_explicit_formula`) and the multinomial
  expansion, `A_k(N) = Σ_ρ U_ρ(N)^k/(ρ(1−ρ))` with `U_ρ(N) = Σ_{N<p≤2N} p^{ρ−3/2}`
  (`jasShellUniformPowerSum_eq_arithmeticSum`).
* Under RH, `|U_ρ(N)| ≤ Σ_{N<p≤2N} 1/p ≤ 1`.
* A maximal off-line zero `ρ₀ = ½ + δ + iγ` has `|U_{ρ₀}(N)| ≍ N^δ/(γ log N)` (the shell main term),
  and Turán's weighted power-sum theorem on the right half of its tie group gives
  `|A_k(N)| ≥ c (N^δ/log N)^k` for some bounded `k` at every large `N`; left zeros have
  `|U_ρ(N)| ≤ 1`.

So, given the large-height input, RH is a growth statement about averages of the classical error
terms `X − ψ(X)` and `Σ_{n≤X} Λ(n)/n − log X + γ` over products of `k` primes from one dyadic shell.
-/

open Complex Filter
open scoped ComplexConjugate Topology
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-- The shell sum `U_s(N) = Σ_{N<p≤2N} p^{s−3/2}`. -/
def jasShellUniformSum (N : ℕ) (s : ℂ) : ℂ := jasCpowSum (jasPrimeWindow N (2 * N)) (3 / 2 - s)

/-- The zero power sum `Σ_ρ U_ρ(N)^k/(ρ(1−ρ))`. -/
def jasShellUniformPowerSum (N k : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, jasShellUniformSum N (q.1 : ℂ) ^ k * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))

/-- The prime side of the genus-kernel explicit formula. -/
def lagPrimeSide (X : ℝ) : ℂ :=
  ((X - Chebyshev.psi X : ℝ) : ℂ) +
    X * (((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n / (n : ℝ) : ℝ) : ℂ) - Real.log X +
      Real.eulerMascheroniConstant) - Real.log (2 * Real.pi) + trivialZeroSeries X

/-- The arithmetic shell power sum `Σ_{p₁,…,p_k ∈ (N, 2N]} (p₁⋯p_k)^{−3/2} 𝓔(p₁⋯p_k)`. -/
def jasShellArithmeticSum (N k : ℕ) : ℂ :=
  ∑ t ∈ Fintype.piFinset (fun _ : Fin k => jasPrimeWindow N (2 * N)),
    (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)) * lagPrimeSide (∏ i, (((t i : ℕ) : ℝ)))

/-! ## Bounds for the shell sums -/

theorem norm_jasShellUniformSum_le (N : ℕ) (s : ℂ) :
    ‖jasShellUniformSum N s‖ ≤
      ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(3 / 2 - s.re) * Real.log p) := by
  refine (norm_jasCpowSum_le _ _).trans (le_of_eq ?_)
  congr 1; ext p; congr 2; simp

/-- `Σ_{N < p ≤ 2N} p^{−β} ≤ 1` for `β ≥ 1`. -/
theorem sum_shell_exp_neg_le_one (N : ℕ) {β : ℝ} (hβ : 1 ≤ β) :
    ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-β * Real.log p) ≤ 1 := by
  have hterm : ∀ p ∈ jasPrimeWindow N (2 * N), Real.exp (-β * Real.log p) ≤ 1 / ((N : ℝ) + 1) := by
    intro p hp
    have hNp : N < (p : ℕ) := (mem_jasPrimeWindow.mp hp).1
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    refine (exp_neg_mul_log_prime_anti hβ p).trans ?_
    rw [neg_one_mul, Real.exp_neg, Real.exp_log hp0]
    have : ((N : ℝ) + 1) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hNp
    exact (inv_eq_one_div _).trans_le (one_div_le_one_div_of_le (by positivity) this)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((jasPrimeWindow N (2 * N)).card : ℝ) ≤ (N : ℝ) + 1 := by
    have h1 : (jasPrimeWindow N (2 * N)).card ≤ (Finset.Ioc N (2 * N)).card := by
      refine Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ)) (fun p hp => ?_)
        (Subtype.val_injective.injOn)
      exact Finset.mem_Ioc.mpr (mem_jasPrimeWindow.mp hp)
    rw [Nat.card_Ioc] at h1
    have : ((2 * N - N : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
      have : 2 * N - N = N := by omega
      rw [this]; linarith
    exact (Nat.cast_le.mpr h1).trans this
  rw [mul_one_div, div_le_one (by positivity)]
  exact hcard

/-- Zeros on or left of the line have `|U_ρ(N)| ≤ 1`. -/
theorem norm_jasShellUniformSum_le_one {N : ℕ} {s : ℂ} (hs : s.re ≤ 1 / 2) :
    ‖jasShellUniformSum N s‖ ≤ 1 :=
  (norm_jasShellUniformSum_le N s).trans (sum_shell_exp_neg_le_one N (by linarith))

/-- Right of the line, `U_ρ(N)` is the large prime sum of the zero. -/
theorem jasShellUniformSum_eq_jasBigSum {N : ℕ} {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    jasShellUniformSum N s = jasBigSum (jasPrimeWindow N (2 * N)) 1 s := by
  rw [jasShellUniformSum, jasBigSum, if_pos hs]
  congr 1; push_cast; ring

theorem summable_jasShellUniformPowerSum_terms (N k : ℕ) :
    Summable fun q : XiZeroCopy => jasShellUniformSum N (q.1 : ℂ) ^ k *
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(1 / 2) * Real.log p) := ⟨_, rfl⟩
  refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left (C ^ k)) fun q => ?_
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ k) (norm_nonneg _)
  rw [hC]
  refine (norm_jasShellUniformSum_le N _).trans (Finset.sum_le_sum fun p _ => ?_)
  exact exp_neg_mul_log_prime_anti (by linarith [xiZeroCopy_re_lt_one q]) p

/-! ## The arithmetic identity -/

/-- `p^{s − 3/2}` for a product of primes multiplies. -/
theorem prod_cexp_eq_cpow {k : ℕ} (t : Fin k → Nat.Primes) (s : ℂ) :
    ∏ i, cexp (-(3 / 2 - s) * (Real.log ((t i : ℕ) : ℝ) : ℂ)) =
      (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ s *
        (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)) := by
  have hpos : ∀ i, (0 : ℝ) < ((t i : ℕ) : ℝ) := fun i => by exact_mod_cast (t i).2.pos
  have hm : (0 : ℝ) < ∏ i, (((t i : ℕ) : ℝ)) := Finset.prod_pos fun i _ => hpos i
  have hmc : (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Complex.cpow_add _ _ hmc, Complex.cpow_def_of_ne_zero hmc, ← Complex.ofReal_log hm.le,
    Real.log_prod (fun i _ => (hpos i).ne'), ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The arithmetic identity** `Σ_ρ U_ρ(N)^k/(ρ(1−ρ)) = A_k(N)` for `k ≥ 1`. -/
theorem jasShellUniformPowerSum_eq_arithmeticSum (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    jasShellUniformPowerSum N k = jasShellArithmeticSum N k := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Finset Nat.Primes, P = jasPrimeWindow N (2 * N) := ⟨_, rfl⟩
  -- expand the power
  have hexp : ∀ s : ℂ, jasShellUniformSum N s ^ k =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin k => P),
        ∏ i, cexp (-(3 / 2 - s) * (Real.log ((t i : ℕ) : ℝ) : ℂ)) := by
    intro s
    rw [jasShellUniformSum, jasCpowSum, ← hP, ← Fin.prod_const, Finset.prod_univ_sum]
  have hmgt : ∀ t : Fin k → Nat.Primes, (1 : ℝ) < ∏ i, (((t i : ℕ) : ℝ)) := by
    intro t
    have h2 : ∀ i, (2 : ℝ) ≤ ((t i : ℕ) : ℝ) := fun i => by exact_mod_cast (t i).2.two_le
    obtain ⟨j⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    calc (1 : ℝ) < 2 := by norm_num
      _ ≤ ((t j : ℕ) : ℝ) := h2 j
      _ ≤ ∏ i, (((t i : ℕ) : ℝ)) := by
          rw [← Finset.mul_prod_erase Finset.univ (fun i => (((t i : ℕ) : ℝ))) (Finset.mem_univ j)]
          refine le_mul_of_one_le_right (by linarith [h2 j]) ?_
          calc (1 : ℝ) = ∏ i ∈ Finset.univ.erase j, (1 : ℝ) := by simp
            _ ≤ ∏ i ∈ Finset.univ.erase j, (((t i : ℕ) : ℝ)) :=
                Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => by linarith [h2 i])
  -- each term is summable over the zeros
  have hsumm : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => P), Summable fun q : XiZeroCopy =>
      (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (q.1 : ℂ) * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro t _
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∏ i, (((t i : ℕ) : ℝ)) := ⟨_, rfl⟩
    rw [← hm]
    have hm1 : 1 < m := hm ▸ hmgt t
    refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left m) fun q => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc m ^ (q.1 : ℂ).re ≤ m ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hm1.le (xiZeroCopy_re_lt_one q).le
      _ = m := Real.rpow_one m
  rw [jasShellUniformPowerSum, jasShellArithmeticSum, ← hP]
  simp_rw [hexp, Finset.sum_mul, prod_cexp_eq_cpow]
  rw [Summable.tsum_finsetSum (fun t ht => by
    have := (hsumm t ht).mul_right ((((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)))
    refine this.congr fun q => ?_
    ring)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hlag := lag_explicit_formula (hmgt t)
  rw [← lagPrimeSide] at hlag
  have e : (∑' q : XiZeroCopy, (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (q.1 : ℂ) *
      (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)) * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) =
      (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (-(3 / 2 : ℂ)) * ∑' q : XiZeroCopy,
        (((∏ i, (((t i : ℕ) : ℝ))) : ℝ) : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [div_eq_mul_one_div]; ring
  rw [e, hlag]

/-! ## The receiver -/

/-- **A maximal off-line zero makes the uniform shell power sums grow.** If `ρ₀` has the largest
distance `δ > 0` from the critical line and `ε < δ`, then for every large `N` some `k ≥ 1` has
`|Σ_ρ U_ρ(N)^k/(ρ(1−ρ))| > N^{εk}`. Turán's theorem runs over the zeros of the top tie group with
`Re ρ ≥ ½`; the other members of the tie group are their mirror images and have `|U_ρ(N)| ≤ 1`. -/
theorem eventually_exists_large_shellUniformPowerSum_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {ε : ℝ}
    (hε : ε < |(q₀.1 : ℂ).re - 1 / 2|) :
    ∀ᶠ N : ℕ in atTop, ∃ k : ℕ, 1 ≤ k ∧ (N : ℝ) ^ (ε * k) < ‖jasShellUniformPowerSum N k‖ := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |(q₀.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  rw [← hδ] at hmax hε
  have hδ0 : 0 < δ := by rw [hδ]; exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hδ1 : δ < 1 / 2 := hδ ▸ abs_re_sub_half_lt_half_xiZeroCopy q₀
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 - δ := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have h1α : 0 < 1 - α := by linarith
  -- the tie group
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : ℝ, φ₀ = jasShellFactor α |(q₀.1 : ℂ).im| := ⟨_, rfl⟩
  have hφ0 : 0 < φ₀ := hφ₀ ▸ jasShellFactor_pos hα1 _
  have hdecay : ∀ q ∈ {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = δ}, 6 / φ₀ < |(q.1 : ℂ).im| →
      jasShellFactor α |(q.1 : ℂ).im| ≤ φ₀ / 2 := by
    intro q _ hq
    have hpos : 0 < |(q.1 : ℂ).im| := (by positivity : (0 : ℝ) < 6 / φ₀).trans hq
    have h1 := jasShellFactor_mul_abs_le hα0 |(q.1 : ℂ).im|
    rw [abs_abs] at h1
    have h2 : jasShellFactor α |(q.1 : ℂ).im| ≤ 3 / |(q.1 : ℂ).im| := by
      rw [le_div_iff₀ hpos]; exact h1
    have h3 : 3 / |(q.1 : ℂ).im| ≤ 3 / (6 / φ₀) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hq.le
    have h4 : 3 / (6 / φ₀) = φ₀ / 2 := by field_simp; ring
    linarith
  obtain ⟨G, f₁, f₂, hGD, hGne, -, hhalf, hf₂, hGval, hrestD⟩ :=
    exists_top_group {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = δ}
      (fun q => jasShellFactor α |(q.1 : ℂ).im|) (q₀ := q₀) hδ.symm (hφ₀ ▸ hφ0)
      (H := 6 / φ₀) (by positivity) (by rw [← hφ₀]; exact hdecay)
  -- a right representative of the tie group
  obtain ⟨qs₀, hqs₀⟩ := hGne
  have hmirror : ∀ q ∈ G, ∃ q' ∈ G, 1 / 2 ≤ (q'.1 : ℂ).re := by
    intro q hq
    by_cases hr : 1 / 2 ≤ (q.1 : ℂ).re
    · exact ⟨q, hq, hr⟩
    · obtain ⟨q', hq're, hq'im⟩ := exists_xiZeroCopy_mirror q
      have hD' : q' ∈ {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = δ} := by
        have h1 := hGD q hq
        simp only [Set.mem_setOf_eq] at h1 ⊢
        rw [hq're, show 1 - (q.1 : ℂ).re - 1 / 2 = -((q.1 : ℂ).re - 1 / 2) by ring, abs_neg]
        exact h1
      have hφ' : jasShellFactor α |(q'.1 : ℂ).im| = f₁ := by rw [hq'im]; exact hGval q hq
      have hq'G : q' ∈ G := by
        by_contra hn
        have := hrestD q' hD' hn
        rw [hφ'] at this
        linarith
      refine ⟨q', hq'G, ?_⟩
      rw [hq're]; push Not at hr; linarith
  obtain ⟨qs, hqsG, hqsr⟩ := hmirror qs₀ hqs₀
  have hqs : qs ∈ G.filter (fun q => 1 / 2 ≤ (q.1 : ℂ).re) := Finset.mem_filter.mpr ⟨hqsG, hqsr⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = (f₁ - f₂) / 4 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = f₁ - ε' := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁, hε']; linarith
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = (f₂ + ε') / c₁ := ⟨_, rfl⟩
  have hρ₂0 : 0 < ρ₂ := by rw [hρ₂]; exact div_pos (by linarith) hc₁0
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂, div_lt_one hc₁0, hc₁, hε']; linarith
  have hρc : ρ₂ * c₁ = f₂ + ε' := by rw [hρ₂]; field_simp
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 4 - δ ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; nlinarith
  -- weights
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    ⟨_, rfl⟩
  obtain ⟨qw, -, hqwmin⟩ :=
    G.exists_min_image (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ⟨qs, hqsG⟩
  obtain ⟨wmin, hwmin⟩ : ∃ wmin : ℝ, wmin = ‖1 / ((qw.1 : ℂ) * (1 - (qw.1 : ℂ)))‖ := ⟨_, rfl⟩
  have hwmin0 : 0 < wmin := by
    rw [hwmin]
    refine norm_pos_iff.mpr (one_div_ne_zero (mul_ne_zero ?_ ?_))
    · intro h
      have := xiZeroCopy_re_pos qw
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
    · intro h
      have := xiZeroCopy_re_lt_one qw
      have h' : (qw.1 : ℂ) = 1 := by linear_combination -h
      rw [h', Complex.one_re] at this
      exact lt_irrefl _ this
  have hwminG : ∀ q ∈ G, wmin ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := fun q hq =>
    hwmin ▸ hqwmin q hq
  have hcw : ∀ q ∈ G, c * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := fun q _ =>
    hc ▸ quarter_sub_sq_mul_norm_le_re_one_div hδ1 (hmax q)
  -- the Turán window and the constants
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 2 * (1 / (1 - α) + 1) := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max 1 (C₂ / c₁) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hKc : C₂ / c₁ ≤ K := by rw [hK]; exact le_max_right _ _
  obtain ⟨Gr, hGr⟩ : ∃ Gr : Finset XiZeroCopy, Gr = G.filter (fun q => 1 / 2 ≤ (q.1 : ℂ).re) :=
    ⟨_, rfl⟩
  rw [← hGr] at hqs
  have hGrG : Gr ⊆ G := by rw [hGr]; exact Finset.filter_subset _ _
  obtain ⟨M, hM⟩ := exists_turan_window Gr.card hρ₂0 hρ₂1 W (show 0 < c * wmin / 4 by positivity)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (Real.exp 1 * Gr.card *
      (6 * (Gr.card + 1) * ((M : ℝ) + 2 * Gr.card + 2)) ^ Gr.card) := ⟨_, rfl⟩
  rw [← hD] at hM
  have hn1 : (1 : ℝ) ≤ Gr.card := by exact_mod_cast Finset.card_pos.mpr ⟨qs, hqs⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  -- the finite set
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = c * wmin / (4 * D) / K ^ (M + Gr.card) := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨F, hFtail, hGF⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) ≤ T ∧ G ⊆ F := by
    have h1 := (tendsto_tsum_compl_atTop_zero
      (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)).eventually (ge_mem_nhds hT0)
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, G ⊆ F := eventually_ge_atTop G
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    exact ⟨F, hF1, hF2⟩
  have hW₁ : ∑ q ∈ F, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ W :=
    hW ▸ summable_inv_mul_one_sub.norm.sum_le_tsum F fun _ _ => norm_nonneg _
  have hMT : W * ρ₂ ^ (M + 1) + T * K ^ (M + Gr.card) ≤ c * wmin / (2 * D) := by
    have h1 : W * ρ₂ ^ (M + 1) ≤ c * wmin / (4 * D) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h2 : T * K ^ (M + Gr.card) = c * wmin / (4 * D) := by
      rw [hT]; field_simp
    have h3 : c * wmin / (4 * D) + c * wmin / (4 * D) = c * wmin / (2 * D) := by field_simp; ring
    linarith
  -- tolerances
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = (f₂ + ε') / C₂ := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; exact div_pos (by linarith) hC₂0
  have hε₂C : ε₂ * C₂ ≤ f₂ + ε' := le_of_eq (by rw [hε₂]; field_simp)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = c * wmin / (2 * D) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  -- eventual conditions
  have ev1 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ →
      |‖jasWindowSum N (2 * N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ -
        jasShellFactor α |(q.1 : ℂ).im| * jasMainScale α N| ≤ ε' * jasMainScale α N := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    filter_upwards [eventually_abs_norm_shell_sub_le hα0 hα1 |(q.1 : ℂ).im| hε'0] with N hN _
      using hN
  have ev2 : ∀ᶠ N : ℕ in atTop, jasPrimeRpowSum α (2 * N) ≤ C₂ * jasMainScale α N := by
    filter_upwards [tendsto_two_mul_atTop.eventually
      (eventually_jasPrimeRpowSum_le_main hα0 hα1 one_pos), eventually_ge_atTop 2] with N hN hN2
    have h0 : 0 ≤ 1 / (1 - α) + 1 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (jasMainScale_two_mul_le hα0.le hN2) h0
    have e : C₂ * jasMainScale α N = (1 / (1 - α) + 1) * (2 * jasMainScale α N) := by
      rw [hC₂]; ring
    rw [e]
    linarith
  have ev4 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < δ →
      jasPrimeRpowSum (1 - |(q.1 : ℂ).re - 1 / 2|) (2 * N) ≤ ε₂ * jasPrimeRpowSum α (2 * N) := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    by_cases hq : |(q.1 : ℂ).re - 1 / 2| < δ
    · filter_upwards [tendsto_two_mul_atTop.eventually (eventually_jasPrimeRpowSum_le hα1.le
        (show α < 1 - |(q.1 : ℂ).re - 1 / 2| by rw [hα]; linarith) hε₂0)] with N hN _ using hN
    · exact Eventually.of_forall fun N h => absurd h hq
  have ev5 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ε / (c₁ * jasMainScale α N) ≤ min 1 (A / 2) := by
    have hγ : 0 < δ - ε := by linarith
    have hlim := (tendsto_natLog_div_rpow_atTop hγ).const_mul (1 / c₁)
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (ge_mem_nhds
      (show (0 : ℝ) < min 1 (A / 2) from lt_min one_pos (by positivity))),
      eventually_ge_atTop 2] with N hN hN2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlog := Real.log_pos hN1
    have e : (N : ℝ) ^ ε / (c₁ * jasMainScale α N) =
        1 / c₁ * (Real.log N / (N : ℝ) ^ (δ - ε)) := by
      simp only [jasMainScale]
      have h1 : (N : ℝ) ^ (1 - α) = (N : ℝ) ^ (δ - ε) * (N : ℝ) ^ ε := by
        rw [← Real.rpow_add hNpos, hα]; ring_nf
      rw [h1]
      have : 0 < (N : ℝ) ^ (δ - ε) := Real.rpow_pos_of_pos hNpos _
      have : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
      field_simp
    rw [e]; exact hN
  have ev6 : ∀ᶠ N : ℕ in atTop, 1 / ρ₂ ≤ c₁ * jasMainScale α N := by
    have hlim := (tendsto_natLog_div_rpow_atTop h1α).const_mul (1 / c₁)
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (ge_mem_nhds hρ₂0), eventually_ge_atTop 2] with N hN hN2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlog := Real.log_pos hN1
    have hpow : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hNpos _
    have e : 1 / c₁ * (Real.log N / (N : ℝ) ^ (1 - α)) = 1 / (c₁ * jasMainScale α N) := by
      simp only [jasMainScale]; field_simp
    rw [e] at hN
    have hE : 0 < c₁ * jasMainScale α N := mul_pos hc₁0 (div_pos hpow hlog)
    rw [div_le_iff₀ hρ₂0]
    rw [div_le_iff₀ hE] at hN
    linarith
  filter_upwards [ev1, ev2, ev4, ev5, ev6, eventually_ge_atTop 2] with N h1 h2 h4 h5 h6 hN2
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = jasMainScale α N := ⟨_, rfl⟩
  rw [← hE] at h1 h2 h5 h6
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN2
  obtain ⟨P, hP⟩ : ∃ P : Finset Nat.Primes, P = jasPrimeWindow N (2 * N) := ⟨_, rfl⟩
  -- the large sums at distance `δ`
  have hbigD : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ →
      ‖jasBigSum P 1 (q.1 : ℂ)‖ =
        ‖jasWindowSum N (2 * N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ := by
    intro q hq
    rw [norm_jasBigSum_eq, hq, show (1 : ℝ) - δ = α from hα.symm, jasWindowSum_eq_jasCpowSum, hP]
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ‖jasBigSum P 1 (qs.1 : ℂ)‖ := ⟨_, rfl⟩
  have hqsG' : qs ∈ G := hGrG hqs
  have hZlow : c₁ * E ≤ Z := by
    have h3 := h1 qs (hGF hqsG') (hGD qs hqsG')
    rw [hGval qs hqsG', ← hbigD qs (hGD qs hqsG'), ← hZ] at h3
    have h4 := (abs_le.mp h3).1
    have e : c₁ * E = f₁ * E - ε' * E := by rw [hc₁]; ring
    linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le (mul_pos hc₁0 hE0) hZlow
  have hZρ : 1 ≤ ρ₂ * Z := by
    have := mul_le_mul_of_nonneg_left (h6.trans hZlow) hρ₂0.le
    rwa [mul_one_div_cancel hρ₂0.ne'] at this
  have hcompB : ∀ q ∈ F, q ∉ G → ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ ρ₂ * Z := by
    intro q hqF hqG
    have hgoal : ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ (f₂ + ε') * E := by
      rcases lt_or_eq_of_le (hmax q) with hlt | hd
      · have h3 := norm_jasBigSum_le P 1 (q.1 : ℂ)
        have h6 := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) (1 - |(q.1 : ℂ).re - 1 / 2|)
        rw [← hP] at h6
        have h7 := h4 q hqF hlt
        have h8 : ε₂ * jasPrimeRpowSum α (2 * N) ≤ ε₂ * (C₂ * E) :=
          mul_le_mul_of_nonneg_left h2 hε₂0.le
        have h9 : ε₂ * (C₂ * E) ≤ (f₂ + ε') * E := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hε₂C hE0.le
        linarith
      · have h3 := h1 q hqF hd
        rw [← hbigD q hd] at h3
        have h6 := (abs_le.mp h3).2
        have h7 : jasShellFactor α |(q.1 : ℂ).im| * E ≤ f₂ * E :=
          mul_le_mul_of_nonneg_right (hrestD q hd hqG) hE0.le
        have e : (f₂ + ε') * E = f₂ * E + ε' * E := by ring
        linarith
    calc ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ (f₂ + ε') * E := hgoal
      _ = ρ₂ * (c₁ * E) := by rw [← hρc]; ring
      _ ≤ ρ₂ * Z := mul_le_mul_of_nonneg_left hZlow hρ₂0.le
  have hcomp : ∀ q ∈ F, q ∉ Gr → ‖jasShellUniformSum N (q.1 : ℂ)‖ ≤ ρ₂ * Z := by
    intro q hqF hqGr
    by_cases hr : 1 / 2 ≤ (q.1 : ℂ).re
    · have hqG : q ∉ G := fun h => hqGr (by rw [hGr]; exact Finset.mem_filter.mpr ⟨h, hr⟩)
      rw [jasShellUniformSum_eq_jasBigSum hr, ← hP]
      exact hcompB q hqF hqG
    · push Not at hr
      exact (norm_jasShellUniformSum_le_one hr.le).trans hZρ
  have htail : ∀ q : XiZeroCopy, q ∉ F → ‖jasShellUniformSum N (q.1 : ℂ)‖ ≤ K * Z := by
    intro q _
    have h3 := norm_jasShellUniformSum_le N (q.1 : ℂ)
    have h6 : ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(3 / 2 - (q.1 : ℂ).re) * Real.log p) ≤
        ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-α * Real.log p) :=
      Finset.sum_le_sum fun p _ => exp_neg_mul_log_prime_anti (by
        have := (abs_le.mp (hmax q)).2
        rw [hα]; linarith) p
    have h7 := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) α
    have h8 : C₂ * E ≤ K * Z := by
      have : C₂ * E = C₂ / c₁ * (c₁ * E) := by field_simp
      rw [this]
      exact mul_le_mul hKc hZlow (by positivity) (by linarith)
    linarith
  have hZu : Z = ‖jasShellUniformSum N (qs.1 : ℂ)‖ := by
    rw [hZ, jasShellUniformSum_eq_jasBigSum hqsr, hP]
  obtain ⟨ν, hν1, -, hν⟩ := exists_norm_tsum_pow_mul_ge
    (fun q => jasShellUniformSum N (q.1 : ℂ)) M
    (summable_jasShellUniformPowerSum_terms N) (hGrG.trans hGF) hqs hZu hZ0 hcomp hρ₂0.le
    hρ₂1.le htail hK1 hc0 (fun q hq => hcw q (hGrG hq)) (fun q hq => hwminG q (hGrG hq)) hwmin0
    hW₁ hFtail (by rw [← hD]; exact hMT)
  rw [← hD, ← hA] at hν
  refine ⟨ν, by omega, ?_⟩
  -- `N^{εν} ≤ (A/2)(c₁E)^ν < A Z^ν`
  have hν0 : 1 ≤ ν := by omega
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ ε / (c₁ * E) := ⟨_, rfl⟩
  rw [← hx] at h5
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := h5.trans (min_le_left _ _)
  have hxA : x ≤ A / 2 := h5.trans (min_le_right _ _)
  have hxν : x ^ ν ≤ A / 2 := (pow_le_of_le_one hx0 hx1 (by omega)).trans hxA
  have hNν : (N : ℝ) ^ (ε * ν) = x ^ ν * (c₁ * E) ^ ν := by
    have hcE0 : (c₁ * E) ^ ν ≠ 0 := pow_ne_zero _ (by positivity)
    rw [hx, div_pow, Real.rpow_mul (by positivity), Real.rpow_natCast]
    field_simp
  have hZν : (c₁ * E) ^ ν ≤ Z ^ ν := pow_le_pow_left₀ (by positivity) hZlow ν
  have hcE : 0 < (c₁ * E) ^ ν := pow_pos (by positivity) ν
  rw [hNν]
  calc x ^ ν * (c₁ * E) ^ ν ≤ A / 2 * (c₁ * E) ^ ν := mul_le_mul_of_nonneg_right hxν hcE.le
    _ < A * (c₁ * E) ^ ν := by have := mul_pos hA0 hcE; linarith
    _ ≤ A * Z ^ ν := mul_le_mul_of_nonneg_left hZν hA0.le
    _ ≤ ‖jasShellUniformPowerSum N ν‖ := hν


/-! ## Capstones -/

/-- Under RH every `|U_ρ(N)| ≤ 1`, so the power sums stay bounded. -/
theorem norm_jasShellUniformPowerSum_le_of_riemannHypothesis (hRH : RiemannHypothesis) (N k : ℕ) :
    ‖jasShellUniformPowerSum N k‖ ≤ ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [jasShellUniformPowerSum]
  refine (norm_tsum_le_tsum_norm (summable_jasShellUniformPowerSum_terms N k).norm).trans ?_
  refine Summable.tsum_le_tsum (fun q => ?_) (summable_jasShellUniformPowerSum_terms N k).norm
    summable_inv_mul_one_sub.norm
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
    (norm_jasShellUniformSum_le_one (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le))

/-- **RH ⟺ ZAL ∧ subexponential growth of the prime-side shell power sums.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_shellArithmetic_growth :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → ‖jasShellArithmeticSum N k‖ ≤ (N : ℝ) ^ (ε * k) := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun ε hε => ?_⟩
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
      ⟨_, rfl⟩
    have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    refine ((hlim.eventually (eventually_ge_atTop W)).and (eventually_ge_atTop 1)).frequently.mono
      fun N ⟨hN, hN1⟩ k hk => ?_
    rw [← jasShellUniformPowerSum_eq_arithmeticSum N hk]
    refine (norm_jasShellUniformPowerSum_le_of_riemannHypothesis hRH N k).trans ?_
    rw [← hW]
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    refine hN.trans (Real.rpow_le_rpow_of_exponent_le hN1' ?_)
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  · rintro ⟨hZ, hfr⟩
    by_contra hRH
    obtain ⟨Θ, hΘ, q₀, hq₀, hmaxq⟩ := attainedTopExcess_of_zerosApproachLine hZ hRH
    have habs : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| = |(q.1 : ℂ).re - 1 / 2| := fun q => by
      rw [LindelofSparse.spectral_im_eq, abs_sub_comm]
    have hq₀' : |(q₀.1 : ℂ).re - 1 / 2| = Θ := by rw [← habs]; exact hq₀
    have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := fun h => by
      rw [h, sub_self, abs_zero] at hq₀'; linarith
    have hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := fun q => by
      rw [hq₀', ← habs]; exact hmaxq q
    have hev := eventually_exists_large_shellUniformPowerSum_of_maximal_offLine q₀ hoff hmax
      (ε := Θ / 2) (by rw [hq₀']; linarith)
    obtain ⟨N, hN, k, hk, hlt⟩ := ((hfr (Θ / 2) (by linarith)).and_eventually hev).exists
    rw [jasShellUniformPowerSum_eq_arithmeticSum N hk] at hlt
    exact absurd (hN k hk) (not_le.mpr hlt)

/-- **RH ⟺ no off-line chain ∧ subexponential growth of the prime-side shell power sums.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_shellArithmetic_growth :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → ‖jasShellArithmeticSum N k‖ ≤ (N : ℝ) ^ (ε * k) := by
  constructor
  · intro hRH
    exact ⟨fun ⟨⟨q, hq⟩, _⟩ => hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q),
      (riemannHypothesis_iff_zerosApproachLine_and_shellArithmetic_growth.mp hRH).2⟩
  · rintro ⟨hno, hfr⟩
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    have hnot : ¬ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
        ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| :=
      fun h => hno ⟨⟨q₁, ne_of_gt hq₁⟩, h⟩
    push Not at hnot
    obtain ⟨q₀, hoff, hmax⟩ := hnot
    have hδ0 : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
    have hev := eventually_exists_large_shellUniformPowerSum_of_maximal_offLine q₀ hoff hmax
      (ε := |(q₀.1 : ℂ).re - 1 / 2| / 2) (by linarith)
    obtain ⟨N, hN, k, hk, hlt⟩ :=
      ((hfr (|(q₀.1 : ℂ).re - 1 / 2| / 2) (by linarith)).and_eventually hev).exists
    rw [jasShellUniformPowerSum_eq_arithmeticSum N hk] at hlt
    exact absurd (hN k hk) (not_le.mpr hlt)

end

end RHTower
