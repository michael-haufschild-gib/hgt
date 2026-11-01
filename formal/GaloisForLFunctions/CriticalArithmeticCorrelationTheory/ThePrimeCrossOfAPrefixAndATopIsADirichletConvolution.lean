import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# The prime cross of a prefix and a top is a Dirichlet convolution

Split a coefficient vector into a prefix `x` on `[1, M]` and a top `y` on `(M, N]`, with a bump
supported in `[0, w]`, `w < log 2`. The prime form `P(f) = Σ_k Λ(k) k^{−1/2} (lag pairings)` of the
atomic test is quadratic, and its cross term only sees the upward lags from `m ≤ M` to `n ≈ km`
(`cross_lag_eq`). Reindexing `n' = km` turns it into the pairing of the top atomic test with the
atomic test of the prime translate `(a ∗ x)(n') = Σ_{km = n'} Λ(k) k^{−1/2} x(m)`
(`primeConv`, `sum_prime_cross_eq`):

`P(f_{x+y}) = P(f_x) + P(f_y) + 2 ∫ f_y · f_{ρ(a ∗ x)}`   (`primeSum_atomicTest_prefix_add_top`),

for any weight `ρ` equal to `1` on `[M e^{−w}, N e^w]`, the only indices whose atoms meet the top.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-- The prime translate of a prefix vector, `(a ∗ x)(n) = Σ_{km = n} Λ(k) k^{−1/2} x(m)`, over the
orders `k < K` and the prefix `1 ≤ m ≤ M`. -/
def primeConv (K M : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range K, ∑ m ∈ Icc 1 M, if k * m = n then vonMangoldtAtom k * x m else 0

/-- The number of prime orders that reach the horizon: `⌈N e^w⌉ + 1`. -/
def primeOrderCutoff (N : ℕ) (w : ℝ) : ℕ := ⌈(N : ℝ) * Real.exp w⌉₊ + 1

/-- **Two atomic tests pair through the bump autocorrelation.** -/
theorem integral_atomicTest_mul_atomicTest (hg : Continuous g) (hgc : HasCompactSupport g)
    (N N' : ℕ) (x z : ℕ → ℝ) :
    ∫ u, atomicTest N x g u * atomicTest N' z g u =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N', x m * z n * bumpCorr g (Real.log m - Real.log n) := by
  have hpt : ∀ u, atomicTest N x g u * atomicTest N' z g u =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N', x m * z n * (g (u - Real.log m) * g (u + -Real.log n)) := by
    intro u
    rw [atomicTest, atomicTest, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [← sub_eq_add_neg]; ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_comp_sub_mul_comp_add hg hgc _ _).const_mul _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => (integrable_comp_sub_mul_comp_add hg hgc _ _).const_mul _]
  refine sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, bumpCorr,
    ← integral_sub_right_eq_self (fun v => g v * g (v + (Real.log m - Real.log n))) (Real.log m)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [show u - Real.log m + (Real.log m - Real.log n) = u + -Real.log n by ring]

/-- The lag form of a sum: the two self lag forms and the symmetric cross. -/
theorem lagForm_add (N k : ℕ) (x y : ℕ → ℝ) :
    lagForm g N k (fun n => x n + y n) = lagForm g N k x + lagForm g N k y +
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (x m * y n + y m * x n) *
        (bumpCorr g (-Real.log k - (Real.log n - Real.log m)) +
          bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
  unfold lagForm
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- **Only the upward lag crosses from a prefix to a top.** If `x` lives on `[1, M]`, `y` above
`M` and the bump is narrower than `log 2`, the cross of order `k ≥ 2` is twice the pairing of `x`
at `m` with `y` near `km`. -/
theorem cross_lag_eq (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < Real.log 2)
    {k M N : ℕ} (hk : 2 ≤ k) (x y : ℕ → ℝ) (hx : ∀ n, M < n → x n = 0)
    (hy : ∀ n, n ≤ M → y n = 0) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (x m * y n + y m * x n) *
        (bumpCorr g (-Real.log k - (Real.log n - Real.log m)) +
          bumpCorr g (Real.log k - (Real.log n - Real.log m))) =
      2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        x m * y n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : ∀ a b : ℕ, 1 ≤ a → a < b → Real.log a < Real.log b := fun a b ha hab =>
    Real.log_lt_log (by exact_mod_cast ha) (by exact_mod_cast hab)
  have h1 : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      x m * y n * bumpCorr g (-Real.log k - (Real.log n - Real.log m)) = 0 := by
    intro m hm n hn
    by_cases hxm : x m = 0
    · rw [hxm]; ring
    by_cases hyn : y n = 0
    · rw [hyn]; ring
    have hmM : m ≤ M := by by_contra h; exact hxm (hx m (not_le.mp h))
    have hnM : M < n := by by_contra h; exact hyn (hy n (not_lt.mp h))
    have hmn := hlt m n (mem_Icc.mp hm).1 (by omega)
    rw [bumpCorr_eq_zero hgsupp (by rw [abs_of_neg (by linarith)]; linarith), mul_zero]
  have h2 : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      y m * x n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0 := by
    intro m hm n hn
    by_cases hym : y m = 0
    · rw [hym]; ring
    by_cases hxn : x n = 0
    · rw [hxn]; ring
    have hmM : M < m := by by_contra h; exact hym (hy m (not_lt.mp h))
    have hnM : n ≤ M := by by_contra h; exact hxn (hx n (not_le.mp h))
    have hnm := hlt n m (mem_Icc.mp hn).1 (by omega)
    rw [bumpCorr_eq_zero hgsupp (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  have hsym : ∀ m n : ℕ, bumpCorr g (-Real.log k - (Real.log m - Real.log n)) =
      bumpCorr g (Real.log k - (Real.log n - Real.log m)) := fun m n => by
    rw [← bumpCorr_neg]; congr 1; ring
  have hexp : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, (x m * y n + y m * x n) *
      (bumpCorr g (-Real.log k - (Real.log n - Real.log m)) +
        bumpCorr g (Real.log k - (Real.log n - Real.log m))) =
      x m * y n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) +
        y m * x n * bumpCorr g (-Real.log k - (Real.log n - Real.log m)) := by
    intro m hm n hn
    have e1 := h1 m hm n hn
    have e2 := h2 m hm n hn
    linear_combination e1 + e2
  rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hexp m hm n hn]
  simp only [sum_add_distrib]
  rw [sum_comm (f := fun m n => y m * x n * bumpCorr g (-Real.log k - (Real.log n - Real.log m)))]
  rw [two_mul]
  congr 1
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  rw [hsym]; ring

/-- **The cross as a Dirichlet convolution.** Reindexing `n' = km`, the upward cross of `x` and
`y` pairs `y` with the prime translate `a ∗ x`, through the same autocorrelation. A weight `ρ`
equal to `1` on `[M e^{−w}, N e^w]` may be inserted: no other `n'` meets the top. -/
theorem sum_prime_cross_eq (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {K M N : ℕ} (hMN : M ≤ N)
    (x y : ℕ → ℝ) (hx : ∀ n, M < n → x n = 0) (hy : ∀ n, n ≤ M → y n = 0) (ρ : ℕ → ℝ)
    (hρ : ∀ n' : ℕ, (M : ℝ) * Real.exp (-w) ≤ n' → (n' : ℝ) ≤ N * Real.exp w → ρ n' = 1) :
    ∑ k ∈ range K, vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        x m * y n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) =
      ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 (K * M),
        y n * (ρ n' * primeConv K M x n') * bumpCorr g (Real.log n - Real.log n') := by
  have hsubM : Icc 1 M ⊆ Icc 1 N := Icc_subset_Icc le_rfl hMN
  -- restrict the prefix sum to `m ≤ M`
  have hres : ∀ k : ℕ, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      x m * y n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) =
      ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        x m * y n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) := by
    intro k
    refine (sum_subset hsubM fun m hm hmM => ?_).symm
    have : M < m := by
      by_contra h; exact hmM (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, not_lt.mp h⟩)
    simp [hx m this]
  simp_rw [hres]
  -- expand the convolution on the right
  have hrhs : ∀ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 (K * M),
      y n * (ρ n' * primeConv K M x n') * bumpCorr g (Real.log n - Real.log n') =
      ∑ k ∈ range K, ∑ m ∈ Icc 1 M, (if k * m ∈ Icc 1 (K * M) then
        y n * (ρ (k * m) * (vonMangoldtAtom k * x m)) *
          bumpCorr g (Real.log n - Real.log (k * m : ℕ)) else 0) := by
    intro n _
    unfold primeConv
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    have hite : ∀ n' : ℕ, y n * (ρ n' * (if k * m = n' then vonMangoldtAtom k * x m else 0)) *
        bumpCorr g (Real.log n - Real.log n') = if k * m = n' then
          y n * (ρ n' * (vonMangoldtAtom k * x m)) * bumpCorr g (Real.log n - Real.log n') else 0 := by
      intro n'; split_ifs <;> ring
    rw [sum_congr rfl fun n' _ => hite n', sum_ite_eq]
  rw [sum_congr rfl hrhs, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_comm (s := Icc 1 N) (t := Icc 1 M), mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rcases lt_or_ge k 2 with hk2 | hk2
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2]; simp
  have hm1 := (mem_Icc.mp hm).1
  have hkm : k * m ∈ Icc 1 (K * M) := mem_Icc.mpr ⟨Nat.mul_pos (by omega) hm1,
    Nat.mul_le_mul (le_of_lt (mem_range.mp hk)) (mem_Icc.mp hm).2⟩
  rw [if_pos hkm]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlog : Real.log ((k * m : ℕ) : ℝ) = Real.log k + Real.log m := by
    push_cast; exact Real.log_mul hk0.ne' hm0.ne'
  have hB : bumpCorr g (Real.log k - (Real.log n - Real.log m)) =
      bumpCorr g (Real.log n - Real.log (k * m : ℕ)) := by
    rw [hlog, ← bumpCorr_neg]; congr 1; ring
  rw [hB]
  by_cases hyn : y n = 0
  · rw [hyn]; ring
  by_cases hwin : |Real.log n - Real.log (k * m : ℕ)| ≤ w
  · have hnM : M < n := by by_contra h; exact hyn (hy n (not_lt.mp h))
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hkm0 : (0 : ℝ) < ((k * m : ℕ) : ℝ) := by positivity
    obtain ⟨hw1, hw2⟩ := abs_le.mp hwin
    have hlo : (M : ℝ) * Real.exp (-w) ≤ ((k * m : ℕ) : ℝ) := by
      have h1 : Real.log n - w ≤ Real.log ((k * m : ℕ) : ℝ) := by linarith
      have h2 := Real.exp_le_exp.mpr h1
      rw [Real.exp_sub, Real.exp_log hn0, Real.exp_log hkm0] at h2
      have hMn : (M : ℝ) ≤ n := by exact_mod_cast hnM.le
      calc (M : ℝ) * Real.exp (-w) ≤ n * Real.exp (-w) :=
            mul_le_mul_of_nonneg_right hMn (Real.exp_pos _).le
        _ = n / Real.exp w := by rw [Real.exp_neg, div_eq_mul_inv]
        _ ≤ _ := h2
    have hhi : ((k * m : ℕ) : ℝ) ≤ N * Real.exp w := by
      have h1 : Real.log ((k * m : ℕ) : ℝ) ≤ Real.log n + w := by linarith
      have h2 := Real.exp_le_exp.mpr h1
      rw [Real.exp_add, Real.exp_log hn0, Real.exp_log hkm0] at h2
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      exact h2.trans (mul_le_mul_of_nonneg_right hnN (Real.exp_pos _).le)
    rw [hρ _ hlo hhi]; ring
  · rw [bumpCorr_eq_zero hgsupp (not_le.mp hwin)]; ring

/-- The prime sum of an atomic test is a finite sum over the orders below `primeOrderCutoff`. -/
theorem primeSum_atomicTest_eq_sum_range (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    primeSum (atomicTest N x g) =
      ∑ k ∈ range (primeOrderCutoff N w), vonMangoldtAtom k * lagForm g N k x := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [primeSum_atomicTest_eq_lags hg hgc]
  refine tsum_eq_sum fun k hk => ?_
  simp only [primeOrderCutoff, mem_range, not_lt] at hk
  have hbig : (N : ℝ) * Real.exp w < k := by
    have := Nat.le_ceil ((N : ℝ) * Real.exp w)
    have h2 : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  have hlog : Real.log N + w < Real.log k := by
    rw [← Real.log_exp w, ← Real.log_mul hN0.ne' (Real.exp_pos w).ne']
    exact Real.log_lt_log (by positivity) hbig
  rw [lagForm_eq_zero_of_log_lt hgsupp hw0 hlog, mul_zero]

/-- **The prime form of a prefix plus a top.** For `x` on `[1, M]`, `y` on `(M, N]`, a bump
narrower than `log 2`, and any weight `ρ` equal to `1` on `[M e^{−w}, N e^w]`,
`P(f_{x+y}) = P(f_x) + P(f_y) + 2 ∫ f_y · f_{ρ (a ∗ x)}`: the prime cross is the pairing of the top
with the prime translate of the prefix. -/
theorem primeSum_atomicTest_prefix_add_top (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) (hw : w < Real.log 2)
    {M N : ℕ} (hMN : M ≤ N) (hN : 1 ≤ N) (x y : ℕ → ℝ) (hx : ∀ n, M < n → x n = 0)
    (hy : ∀ n, n ≤ M → y n = 0) (ρ : ℕ → ℝ)
    (hρ : ∀ n' : ℕ, (M : ℝ) * Real.exp (-w) ≤ n' → (n' : ℝ) ≤ N * Real.exp w → ρ n' = 1) :
    primeSum (atomicTest N (fun n => x n + y n) g) =
      primeSum (atomicTest N x g) + primeSum (atomicTest N y g) +
        2 * ∫ u, atomicTest N y g u * atomicTest (primeOrderCutoff N w * M)
          (fun n => ρ n * primeConv (primeOrderCutoff N w) M x n) g u := by
  set K := primeOrderCutoff N w
  rw [primeSum_atomicTest_eq_sum_range hg hgc hgsupp hw0 hN,
    primeSum_atomicTest_eq_sum_range hg hgc hgsupp hw0 hN,
    primeSum_atomicTest_eq_sum_range hg hgc hgsupp hw0 hN,
    integral_atomicTest_mul_atomicTest hg hgc, ← sum_prime_cross_eq hgsupp hMN x y hx hy ρ hρ,
    mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [lagForm_add]
  rcases lt_or_ge k 2 with hk2 | hk2
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2]; ring
  rw [cross_lag_eq hgsupp hw hk2 x y hx hy]
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
