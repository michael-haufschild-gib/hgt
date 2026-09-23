import GaloisForLFunctions.RHTower.Sieve.PrimeSupportedConvolutionBound

/-!
# The coefficient sequences of the Granville–Harper–Soundararajan convolution

Two applications of the logarithmic recursion to a multiplicative `f` with `‖f‖ ≤ 1` present the partial
sum of `f` as a threefold convolution of

* the outer prime weight `a_p = f(p)·log p/log⌊N/p⌋`,
* the inner prime weight `b_q = f(q)·log q` for `q ≤ M`,
* `f` itself.

Both prime weights are supported on primes and both are bounded by a constant multiple of `log` of their
argument — `1/log 2` for the outer one, because the denominator `log⌊N/p⌋` is at least `log 2` on the
support — so the polylogarithmic coefficient bound for prime-supported triple convolutions applies and
gives

`‖(a ⍟ (b ⍟ f))(n)‖ ≤ (log n)⁴/(log 2)³`.

This is the size input consumed by the smoothing and Perron steps: no divisor function, no short-interval
arithmetic, and no hypothesis on `f` beyond `‖f‖ ≤ 1`.  Both weights have finite support — the outer one
inside `[1, N]`, because its condition forces `2p ≤ N`, and the inner one inside `[1, M]` — which is what
makes the mean-square estimates for Dirichlet polynomials applicable to them.
-/

noncomputable section
namespace RHTower.Sieve

/-- The outer coefficient of the Granville–Harper–Soundararajan triple convolution at scale `N`:
`f(p)·log p/log⌊N/p⌋` on primes whose complementary scale is at least `2`, and `0` elsewhere. -/
def ghsOuter (f : ℕ → ℂ) (N : ℕ) (p : ℕ) : ℂ :=
  if Nat.Prime p ∧ 2 ≤ N / p then
    f p * ((Real.log p / Real.log ((N / p : ℕ) : ℝ) : ℝ) : ℂ) else 0

/-- The inner prime weight `f(q)·log q`, truncated at `M`.  The second application of the recursion runs
over primes `q ≤ N/p ≤ N`, so the truncation is not a restriction of the argument. -/
def ghsInner (f : ℕ → ℂ) (M : ℕ) (q : ℕ) : ℂ :=
  if Nat.Prime q ∧ q ≤ M then f q * ((Real.log q : ℝ) : ℂ) else 0

theorem ghsOuter_support {f : ℕ → ℂ} {N p : ℕ} (h : ghsOuter f N p ≠ 0) : Nat.Prime p := by
  rw [ghsOuter] at h
  by_cases hc : Nat.Prime p ∧ 2 ≤ N / p
  · exact hc.1
  · rw [if_neg hc] at h; exact absurd rfl h

theorem ghsInner_support {f : ℕ → ℂ} {M q : ℕ} (h : ghsInner f M q ≠ 0) : Nat.Prime q := by
  rw [ghsInner] at h
  by_cases hc : Nat.Prime q ∧ q ≤ M
  · exact hc.1
  · rw [if_neg hc] at h; exact absurd rfl h

/-- The outer weight is supported in `[1, N]`: its condition forces `2p ≤ N`. -/
theorem ghsOuter_mem_Icc {f : ℕ → ℂ} {N p : ℕ} (h : ghsOuter f N p ≠ 0) :
    p ∈ Finset.Icc 1 N := by
  rw [ghsOuter] at h
  by_cases hc : Nat.Prime p ∧ 2 ≤ N / p
  · have hp2 : 2 ≤ p := hc.1.two_le
    have hpos : 0 < p := by omega
    have hmul : 2 * p ≤ N := (Nat.le_div_iff_mul_le hpos).1 hc.2
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · rw [if_neg hc] at h; exact absurd rfl h

/-- The inner weight is supported in `[1, M]`. -/
theorem ghsInner_mem_Icc {f : ℕ → ℂ} {M q : ℕ} (h : ghsInner f M q ≠ 0) :
    q ∈ Finset.Icc 1 M := by
  have hq : Nat.Prime q := ghsInner_support h
  rw [ghsInner] at h
  by_cases hc : Nat.Prime q ∧ q ≤ M
  · exact Finset.mem_Icc.2 ⟨hq.one_lt.le.trans' (by norm_num), hc.2⟩
  · rw [if_neg hc] at h; exact absurd rfl h

/-- The outer coefficient obeys `‖a_p‖ ≤ (1/log 2)·log p`: the denominator `log⌊N/p⌋` is at least
`log 2` on the support. -/
theorem norm_ghsOuter_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N p : ℕ) :
    ‖ghsOuter f N p‖ ≤ (1 / Real.log 2) * Real.log p := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [ghsOuter]
  by_cases hc : Nat.Prime p ∧ 2 ≤ N / p
  · rw [if_pos hc]
    have hp2 : 2 ≤ p := hc.1.two_le
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2.trans' (by norm_num)
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hpR
    have hden : Real.log 2 ≤ Real.log ((N / p : ℕ) : ℝ) := by
      refine Real.log_le_log (by norm_num) ?_
      exact_mod_cast hc.2
    have hratio : Real.log p / Real.log ((N / p : ℕ) : ℝ) ≤ Real.log p / Real.log 2 :=
      div_le_div_of_nonneg_left hlogp hlog2 hden
    have hrnn : (0 : ℝ) ≤ Real.log p / Real.log ((N / p : ℕ) : ℝ) :=
      div_nonneg hlogp (by linarith)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnn]
    calc ‖f p‖ * (Real.log p / Real.log ((N / p : ℕ) : ℝ))
        ≤ 1 * (Real.log p / Real.log 2) :=
          mul_le_mul (hf p) hratio hrnn zero_le_one
      _ = (1 / Real.log 2) * Real.log p := by field_simp
  · rw [if_neg hc, norm_zero]
    by_cases hp : Nat.Prime p
    · have hpR : (1 : ℝ) ≤ (p : ℝ) := by
        have := hp.two_le; exact_mod_cast this.trans' (by norm_num)
      have := Real.log_nonneg hpR
      positivity
    · have hple : p = 0 ∨ p = 1 ∨ 2 ≤ p := by omega
      rcases hple with h | h | h
      · simp [h]
      · simp [h]
      · have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.trans' (by norm_num)
        have := Real.log_nonneg hpR
        positivity

/-- The inner prime weight obeys `‖b_q‖ ≤ log q`. -/
theorem norm_ghsInner_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (M q : ℕ) :
    ‖ghsInner f M q‖ ≤ Real.log q := by
  rw [ghsInner]
  by_cases hc : Nat.Prime q ∧ q ≤ M
  · rw [if_pos hc]
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by
      have := hc.1.two_le; exact_mod_cast this.trans' (by norm_num)
    have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hqR
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogq]
    calc ‖f q‖ * Real.log q ≤ 1 * Real.log q := mul_le_mul_of_nonneg_right (hf q) hlogq
      _ = Real.log q := one_mul _
  · rw [if_neg hc, norm_zero]
    have hqle : q = 0 ∨ q = 1 ∨ 2 ≤ q := by omega
    rcases hqle with h | h | h
    · simp [h]
    · simp [h]
    · have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h.trans' (by norm_num)
      exact Real.log_nonneg hqR

/-- **The coefficients of the GHS triple convolution are polylogarithmic.**  With the outer weight
`f(p)log p/log⌊N/p⌋`, the inner weight `f(q)log q` and `f` itself as the third factor,

`‖(a ⍟ (b ⍟ f))(n)‖ ≤ (log n)⁴/(log 2)³`

for every `‖f‖ ≤ 1`.  All three factors are the ones the log recursion produces, so the smoothing and
Perron steps see no arithmetic input beyond this bound. -/
theorem norm_ghsTriple_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N M : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ‖(LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f M) f)) n‖
      ≤ (Real.log n) ^ (4 : ℕ) / (Real.log 2) ^ (3 : ℕ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := norm_convolution_triple_le_log_pow_const
    (A := 1 / Real.log 2) (B := 1) (by positivity) zero_le_one
    (fun p hp => ghsOuter_support hp) (norm_ghsOuter_le hf N)
    (fun q hq => ghsInner_support hq) (by simpa using norm_ghsInner_le hf M) hf hn
  refine h.trans (le_of_eq ?_)
  field_simp

end RHTower.Sieve
end
