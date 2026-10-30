import GaloisForLFunctions.ArithmeticGaugeTheory.TheShellDecomposition

/-!
# The coherence principle

A gauge-charged statistic is a combination `S(x) = Σ_n c(n) χ_x(n)` (or a combination of twist
pairs). Its gauge mean is `c(1)` and its gauge mean square is `Σ |c(n)|²`. Its value at the trivial
point is `Σ c(n)`. When the coefficients are nonnegative every term adds in phase at `0`.

* **Coherence** (`norm_twistSum_le_trivial`). For `c ≥ 0`, `‖S(x)‖ ≤ S(0)` at every gauge point: the
  trivial point maximizes every nonnegative statistic.
* **Gauge mean** (`integral_twistSum`). `∫ S = c(1)` when `1 ∈ s`, and `0` otherwise.
* **Coherence ratio** (`coherence_ratio`). If `0 ≤ c ≤ L`, then `S(0) · Σ c² ≤ L · S(0)²`: the value at
  `0` exceeds the gauge root-mean-square by a factor at least `√(S(0)/L)`.
* **The pole as coherence** (`primeSource_coherence`). For the prime source on `[1, N]`,
  `ψ(N) · Σ Λ² ≤ log N · ψ(N)²`. The trivial point sits at least `√(ψ(N)/log N)` gauge standard
  deviations above the gauge mean `0`; this coherent excess is the pole.
* **Diamagnetism of the prime pair form** (`norm_primePairForm_gaugeTransform_le`,
  `norm_shellPart_gaugeTransform_le`). For nonnegative weights, vectors and kernels, the
  gauge-transformed prime pair form and its shell part are dominated in modulus by their values at the
  trivial point.

So nonnegative statistics are never typical at `0`: their excess is coherence, not arithmetic
information. In Weil's form the prime part is subtracted, so on nonnegative data the trivial point
minimizes the energy among its gauge transforms. A repayment by shells can only happen on signed,
nonpolar directions, where coherence fails and the value at `0` is genuinely arithmetic. The Möbius
source is signed, and its exponent at `0` is the zero abscissa (`gaugeExponent_moebius_trivial`).
-/

open MeasureTheory Finset ArithmeticFunction
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- At the trivial point a twisted sum is the untwisted sum. -/
theorem twistSum_trivial (s : Finset ℕ) (a : ℕ → ℂ) : twistSum s a 0 = ∑ n ∈ s, a n := by
  simp [twistSum, twist_trivialPoint]

/-- **Coherence.** A nonnegative statistic is maximal at the trivial point. -/
theorem norm_twistSum_le_trivial (s : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n ∈ s, 0 ≤ c n)
    (x : GaugeTorus) : ‖twistSum s (fun n => (c n : ℂ)) x‖ ≤ ∑ n ∈ s, c n := by
  calc ‖twistSum s (fun n => (c n : ℂ)) x‖ ≤ ∑ n ∈ s, ‖(c n : ℂ) * twist x n‖ := norm_sum_le _ _
    _ = ∑ n ∈ s, c n := sum_congr rfl fun n hn => by
        rw [norm_mul, norm_twist, mul_one, Complex.norm_real, Real.norm_of_nonneg (hc n hn)]

/-- **Gauge mean.** The Haar mean of a twisted sum is its coefficient at `1`. -/
theorem integral_twistSum {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (a : ℕ → ℂ) :
    ∫ x, twistSum s a x ∂gaugeHaar = if 1 ∈ s then a 1 else 0 := by
  classical
  have hint : ∀ n ∈ s, Integrable (fun x => a n * twist x n) gaugeHaar := fun n _ =>
    ((continuous_twist n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [show (fun x => twistSum s a x) = fun x => ∑ n ∈ s, a n * twist x n from rfl,
    integral_finsetSum _ hint]
  have hmean : ∀ n ∈ s, ∫ x, a n * twist x n ∂gaugeHaar = if n = 1 then a n else 0 := by
    intro n hn
    have h := integral_twist_mul_conj (hs n hn) one_ne_zero
    simp only [twist_one, map_one, mul_one] at h
    rw [integral_const_mul, h]
    split_ifs <;> simp
  rw [sum_congr rfl hmean, sum_ite_eq']

/-- **Coherence ratio.** For `0 ≤ c ≤ L` on `s`, `S(0) · Σ c² ≤ L · S(0)²`. -/
theorem coherence_ratio (s : Finset ℕ) (c : ℕ → ℝ) {L : ℝ} (hc : ∀ n ∈ s, 0 ≤ c n)
    (hL : ∀ n ∈ s, c n ≤ L) :
    (∑ n ∈ s, c n) * ∑ n ∈ s, c n ^ 2 ≤ L * (∑ n ∈ s, c n) ^ 2 := by
  have hS : 0 ≤ ∑ n ∈ s, c n := sum_nonneg hc
  have hsq : ∑ n ∈ s, c n ^ 2 ≤ L * ∑ n ∈ s, c n := by
    rw [mul_sum]
    exact sum_le_sum fun n hn => by rw [sq]; exact mul_le_mul_of_nonneg_right (hL n hn) (hc n hn)
  calc (∑ n ∈ s, c n) * ∑ n ∈ s, c n ^ 2 ≤ (∑ n ∈ s, c n) * (L * ∑ n ∈ s, c n) :=
        mul_le_mul_of_nonneg_left hsq hS
    _ = L * (∑ n ∈ s, c n) ^ 2 := by ring

/-- **The pole as coherence.** On `[1, N]` the prime source satisfies
`ψ(N) · Σ Λ(n)² ≤ log N · ψ(N)²`: at the trivial point it lies at least `√(ψ(N)/log N)` gauge
standard deviations above its gauge mean `0`. -/
theorem primeSource_coherence (N : ℕ) :
    (∑ n ∈ Icc 1 N, Λ n) * ∑ n ∈ Icc 1 N, Λ n ^ 2 ≤ Real.log N * (∑ n ∈ Icc 1 N, Λ n) ^ 2 := by
  refine coherence_ratio _ _ (fun _ _ => vonMangoldt_nonneg) fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  refine vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn1) ?_)
  exact_mod_cast (mem_Icc.mp hn).2

/-- The gauge mean of the prime source on `[1, N]` vanishes and its gauge mean square is
`Σ Λ(n)²`, while its value at the trivial point is `ψ(N)`. -/
theorem primeSource_gauge_moments (N : ℕ) :
    ∫ x, twistSum (Icc 1 N) (fun n => (Λ n : ℂ)) x ∂gaugeHaar = 0 ∧
      ∫ x, twistSum (Icc 1 N) (fun n => (Λ n : ℂ)) x *
        conj (twistSum (Icc 1 N) (fun n => (Λ n : ℂ)) x) ∂gaugeHaar =
          ((∑ n ∈ Icc 1 N, Λ n ^ 2 : ℝ) : ℂ) ∧
      twistSum (Icc 1 N) (fun n => (Λ n : ℂ)) 0 = ((∑ n ∈ Icc 1 N, Λ n : ℝ) : ℂ) := by
  have hs : ∀ n ∈ Icc 1 N, n ≠ 0 := fun n hn => (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_twistSum hs]
    split_ifs <;> simp [vonMangoldt_apply_one]
  · rw [integral_twistSum_mul_conj hs, Complex.ofReal_sum]
    exact sum_congr rfl fun n _ => by rw [Complex.conj_ofReal, Complex.ofReal_pow, sq]
  · rw [twistSum_trivial, Complex.ofReal_sum]

/-! ### Diamagnetism of the prime pair form -/

variable (K N : ℕ) (a x : ℕ → ℝ) (G : ℝ → ℝ)

/-- The gauge-transformed prime pair form is a combination of twist pairs. -/
theorem primePairForm_gaugeTransform_eq (y : GaugeTorus) :
    primePairForm K N (gaugeTransform y fun k => (a k : ℂ)) (gaugeTransform y fun m => (x m : ℂ))
      (fun t => (G t : ℂ)) =
      ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        ((a k * x m * x n * G (Real.log n - Real.log m - Real.log k) : ℝ) : ℂ) *
          (twist y (k * m) * conj (twist y n)) := by
  refine sum_congr rfl fun k hk => sum_congr rfl fun m hm => sum_congr rfl fun n _ => ?_
  rw [shellTerm_gaugeTransform _ _ y (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1)
    (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1)]
  push_cast
  rw [Complex.conj_ofReal]

/-- A twist pair has modulus one. -/
theorem norm_twist_mul_conj (y : GaugeTorus) (m n : ℕ) : ‖twist y m * conj (twist y n)‖ = 1 := by
  rw [norm_mul, Complex.norm_conj, norm_twist, norm_twist, mul_one]

/-- **Diamagnetism.** For nonnegative weights, vectors and kernel, the gauge-transformed prime pair
form is dominated by its value at the trivial point. -/
theorem norm_primePairForm_gaugeTransform_le (ha : ∀ k, 0 ≤ a k) (hx : ∀ m, 0 ≤ x m)
    (hG : ∀ t, 0 ≤ G t) (y : GaugeTorus) :
    ‖primePairForm K N (gaugeTransform y fun k => (a k : ℂ)) (gaugeTransform y fun m => (x m : ℂ))
      (fun t => (G t : ℂ))‖ ≤
      ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        a k * x m * x n * G (Real.log n - Real.log m - Real.log k) := by
  rw [primePairForm_gaugeTransform_eq]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => (norm_sum_le _ _).trans
    (sum_le_sum fun m _ => (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)))
  rw [norm_mul, norm_twist_mul_conj, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact mul_nonneg (mul_nonneg (mul_nonneg (ha k) (hx m)) (hx n)) (hG _)

/-- The right-hand side of the diamagnetic bound is the form at the trivial point. -/
theorem primePairForm_trivial :
    primePairForm K N (gaugeTransform 0 fun k => (a k : ℂ)) (gaugeTransform 0 fun m => (x m : ℂ))
      (fun t => (G t : ℂ)) =
      ((∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        a k * x m * x n * G (Real.log n - Real.log m - Real.log k) : ℝ) : ℂ) := by
  rw [primePairForm_gaugeTransform_eq]
  push_cast
  simp [twist_trivialPoint]

/-- **The shells are coherent at the trivial point.** For nonnegative data the shell part of the
gauge-transformed form is dominated by the shell part at the trivial point. -/
theorem norm_shellPart_gaugeTransform_le (ha : ∀ k, 0 ≤ a k) (hx : ∀ m, 0 ≤ x m)
    (hG : ∀ t, 0 ≤ G t) (y : GaugeTorus) :
    ‖shellPart K N (gaugeTransform y fun k => (a k : ℂ)) (gaugeTransform y fun m => (x m : ℂ))
      (fun t => (G t : ℂ))‖ ≤
      ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if n = k * m then 0 else a k * x m * x n * G (Real.log n - Real.log m - Real.log k) := by
  rw [shellPart_gaugeTransform_eq]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => (norm_sum_le _ _).trans
    (sum_le_sum fun m _ => (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)))
  rw [norm_mul, norm_twist_mul_conj, mul_one, shellCoeff]
  split_ifs
  · simp
  · rw [Complex.conj_ofReal]
    norm_cast
    rw [Real.norm_of_nonneg]
    exact mul_nonneg (mul_nonneg (mul_nonneg (ha k) (hx m)) (hx n)) (hG _)

end GaloisForLFunctions.ArithmeticGaugeTheory
