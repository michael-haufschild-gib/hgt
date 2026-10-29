import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheBatteryOfTheCount

/-!
# The gauge stabilizer of the count

The lower half of the count is monotone in the weight: `a ≤ b` pointwise and
`A(x) − x ≥ −C √x log² x` give the same for `b` (`lowerCount_mono`). Since the lower half for `Λ`
is RH, every weight below `Λ` that satisfies the count forces RH:

* **Weights below `Λ`** (`count_iff_of_le_vonMangoldt`). If `a ≤ Λ` pointwise, then `a` satisfies the
  count iff RH holds and `Λ − a ∈ 𝒬`. This covers every sign twist of `Λ`, every Euler-factor
  deletion, every mixture `(1 − t)Λ + tλΛ` with `t ∈ [0, 1]`, and `cΛ` with `c ≤ 1`.

A **sign gauge** flips the sign of `Λ` at the odd powers of the primes of a set `F`
(`signGauge F`, `(−1)^k log p` at `p^k` for `p ∈ F`, `log p` otherwise). The Liouville twin is the
gauge of all primes.

* **The gauge stabilizer** (`count_signGauge_iff`). The sign gauge of `F` satisfies the count iff RH
  holds and the flipped prime mass `θ_F(x) = Σ_{p ≤ x, p ∈ F} log p` is `O(√x log² x)`. So the count
  is not gauge invariant, and its stabilizer in the sign-gauge group is exactly the flip sets of
  square-root prime mass: finite sets pass (`count_signGauge_of_finite`), the set of all primes does
  not.

More generally a **torus gauge** `t : primes → ℝ/ℤ` rotates `Λ(p^k)` by `e^{2πi k t_p}`; its real part
satisfies the count iff RH holds and the gauge distance `Σ_{p ≤ x} (1 − cos 2π t_p) log p` is
`O(√x log² x)` (`count_torusGauge_iff`).

This is the count-level form of the gauge picture: the arithmetic point is distinguished from its
gauge neighbours only at square-root gauge distance.
-/

noncomputable section

open Filter Asymptotics Real Finset
open ArithmeticFunction (vonMangoldt cardFactors)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- **The lower half is monotone in the weight.** -/
theorem lowerCount_mono {a b : ℕ → ℝ} (hab : ∀ n, a n ≤ b n) (ha : LowerCount a) :
    LowerCount b := by
  obtain ⟨C, hC⟩ := ha
  refine ⟨C, hC.mono fun x hx => le_trans hx ?_⟩
  have : partialSum a x ≤ partialSum b x := sum_le_sum fun n _ => hab n
  linarith

/-- **Weights below `Λ`**: if `a ≤ Λ` pointwise, the count for `a` is RH together with
`Λ − a ∈ 𝒬`. -/
theorem count_iff_of_le_vonMangoldt {a : ℕ → ℝ} (ha : ∀ n, a n ≤ vonMangoldtWeight n) :
    Count a ↔ RiemannHypothesis ∧ vonMangoldtWeight - a ∈ sqrtClass := by
  constructor
  · intro h
    have hRH : RiemannHypothesis := lowerCount_vonMangoldt_iff.mp
      (lowerCount_mono ha (count_iff_upperCount_and_lowerCount.mp h).2)
    exact ⟨hRH, sub_mem_sqrtClass_of_count h (count_vonMangoldt_iff.mpr hRH)⟩
  · rintro ⟨hRH, hδ⟩
    have h := (count_add_iff_mem_sqrtClass (count_vonMangoldt_iff.mpr hRH) _).mpr
      (PrecisionClass.smul_mem (-1) hδ)
    convert h using 1
    ext n; simp

/-! ### Sign gauges -/

/-- The **sign gauge** of a set `F` of primes: `(−1)^{Ω(n)} Λ(n)` when the prime of the prime power
`n` lies in `F`, and `Λ(n)` otherwise. -/
def signGauge (F : Set ℕ) [DecidablePred (· ∈ F)] (n : ℕ) : ℝ :=
  (if n.minFac ∈ F then (-1) ^ cardFactors n else 1) * vonMangoldt n

/-- The **flipped prime mass** `θ_F(x) = Σ_{p ≤ x, p ∈ F} log p`. -/
def flippedMass (F : Set ℕ) [DecidablePred (· ∈ F)] (x : ℝ) : ℝ :=
  ∑ p ∈ Ioc 0 ⌊x⌋₊, if p.Prime ∧ p ∈ F then Real.log p else 0

variable (F : Set ℕ) [DecidablePred (· ∈ F)]

theorem signGauge_le (n : ℕ) : signGauge F n ≤ vonMangoldtWeight n := by
  have h0 : (0 : ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  unfold signGauge
  split_ifs
  · rcases neg_one_pow_eq_or ℝ (cardFactors n) with h | h <;> rw [h]
    · simp
    · simp only [vonMangoldtWeight]; linarith
  · simp

/-- `2 θ_F ≤ Σ (Λ − sign gauge) ≤ 2 θ_F + 2 (ψ − θ)`, pointwise in `n`. -/
theorem gauge_defect_bounds (n : ℕ) :
    2 * (if n.Prime ∧ n ∈ F then Real.log n else 0) ≤ vonMangoldtWeight n - signGauge F n ∧
      vonMangoldtWeight n - signGauge F n ≤
        2 * (if n.Prime ∧ n ∈ F then Real.log n else 0) +
          2 * (if n.Prime then 0 else vonMangoldt n) := by
  have h0 : (0 : ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hsg : vonMangoldtWeight n - signGauge F n =
      (1 - if n.minFac ∈ F then (-1) ^ cardFactors n else 1) * vonMangoldt n := by
    simp only [signGauge, vonMangoldtWeight]; ring
  rw [hsg]
  by_cases hp : n.Prime
  · have hmin : n.minFac = n := hp.minFac_eq
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, hmin]
    by_cases hF : n ∈ F
    · simp [hF, hp, ArithmeticFunction.cardFactors_apply_prime hp]; ring_nf; simp
    · simp [hF, hp]
  · have hle : (1 - if n.minFac ∈ F then (-1 : ℝ) ^ cardFactors n else 1) ≤ 2 := by
      split_ifs
      · rcases neg_one_pow_eq_or ℝ (cardFactors n) with h | h <;> rw [h] <;> norm_num
      · norm_num
    have hge : 0 ≤ (1 - if n.minFac ∈ F then (-1 : ℝ) ^ cardFactors n else 1) := by
      split_ifs
      · rcases neg_one_pow_eq_or ℝ (cardFactors n) with h | h <;> rw [h] <;> norm_num
      · norm_num
    simp only [hp, false_and, if_false, mul_zero, zero_add]
    exact ⟨mul_nonneg hge h0, by nlinarith⟩

/-- The gauge defect has partial sums between `2 θ_F` and `2 θ_F + 2 (ψ − θ)`. -/
theorem partialSum_gauge_defect_bounds (x : ℝ) :
    2 * flippedMass F x ≤ partialSum (vonMangoldtWeight - signGauge F) x ∧
      partialSum (vonMangoldtWeight - signGauge F) x ≤
        2 * flippedMass F x + 2 * (Chebyshev.psi x - Chebyshev.theta x) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter, flippedMass, mul_sum, mul_sum,
    ← sum_add_distrib]
  exact ⟨sum_le_sum fun n _ => (gauge_defect_bounds F n).1,
    sum_le_sum fun n _ => by
      have := (gauge_defect_bounds F n).2
      simpa [Pi.sub_apply] using this⟩

theorem flippedMass_nonneg (x : ℝ) : 0 ≤ flippedMass F x :=
  sum_nonneg fun n hn => by
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.1.one_lt.le)
    · exact le_rfl

/-- **The gauge stabilizer of the count.** The sign gauge of `F` satisfies the count iff RH holds
and the flipped prime mass is `O(√x log² x)`. -/
theorem count_signGauge_iff :
    Count (signGauge F) ↔ RiemannHypothesis ∧ flippedMass F =O[atTop] sqrtScale := by
  rw [count_iff_of_le_vonMangoldt (signGauge_le F)]
  have hψθ : (fun x => Chebyshev.psi x - Chebyshev.theta x) =O[atTop] sqrtScale := by
    refine Chebyshev.isBigO_psi_sub_theta_sqrt.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg x), Real.norm_of_nonneg (sqrtScale_nonneg x), one_mul]
    exact sqrt_le_sqrtScale hx
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · refine (IsBigO.of_bound (1 / 2) (Eventually.of_forall fun x => ?_)).trans
      (h : partialSum (vonMangoldtWeight - signGauge F) =O[atTop] sqrtScale)
    have h1 := (partialSum_gauge_defect_bounds F x).1
    have h0 := flippedMass_nonneg F x
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by linarith)]
    linarith
  · have hsum := (h.const_mul_left 2).add (hψθ.const_mul_left 2)
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans hsum
    obtain ⟨h1, h2⟩ := partialSum_gauge_defect_bounds F x
    have h0 := flippedMass_nonneg F x
    have hθ := Chebyshev.theta_le_psi x
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith), one_mul]
    exact h2

/-- **Finite flips pass**: a sign gauge of a finite set of primes satisfies the count iff RH. -/
theorem count_signGauge_of_finite (hF : F.Finite) : Count (signGauge F) ↔ RiemannHypothesis := by
  rw [count_signGauge_iff]
  refine and_iff_left_of_imp fun _ => ?_
  obtain ⟨N, hN⟩ := hF.bddAbove
  refine IsBigO.of_bound (flippedMass F N) ?_
  filter_upwards [eventually_ge_atTop (max (exp 1) N)] with x hx
  have hxN : (N : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hconst : flippedMass F x = flippedMass F N := by
    unfold flippedMass
    rw [Nat.floor_natCast]
    refine (sum_subset (Ioc_subset_Ioc_right (Nat.le_floor hxN)) fun n hn hnN => ?_).symm
    have hnN' : N < n := by
      by_contra hle
      exact hnN (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, by omega⟩)
    rw [if_neg fun h => absurd (hN h.2) (not_le.mpr hnN')]
  rw [hconst, Real.norm_of_nonneg (flippedMass_nonneg F N), Real.norm_of_nonneg (sqrtScale_nonneg x)]
  exact le_mul_of_one_le_right (flippedMass_nonneg F N) (one_le_sqrtScale (le_trans (le_max_left _ _) hx))


/-! ### Torus gauges -/

/-- The **torus gauge** of `t : primes → ℝ/ℤ`: `cos(2π k t_p) log p` at `p^k`, the real part of the
gauge-rotated source `e^{2πi k t_p} Λ(p^k)`. -/
def torusGauge (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.cos (2 * π * cardFactors n * t n.minFac) * vonMangoldt n

/-- The **gauge distance** `D_t(x) = Σ_{p ≤ x} (1 − cos 2π t_p) log p` from the arithmetic point. -/
def gaugeDistance (t : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ Ioc 0 ⌊x⌋₊, if p.Prime then (1 - Real.cos (2 * π * t p)) * Real.log p else 0

theorem torusGauge_le (t : ℕ → ℝ) (n : ℕ) : torusGauge t n ≤ vonMangoldtWeight n := by
  have h0 : (0 : ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  unfold torusGauge
  exact mul_le_of_le_one_left h0 (Real.cos_le_one _)

theorem torus_defect_bounds (t : ℕ → ℝ) (n : ℕ) :
    (if n.Prime then (1 - Real.cos (2 * π * t n)) * Real.log n else 0) ≤
        vonMangoldtWeight n - torusGauge t n ∧
      vonMangoldtWeight n - torusGauge t n ≤
        (if n.Prime then (1 - Real.cos (2 * π * t n)) * Real.log n else 0) +
          2 * (if n.Prime then 0 else vonMangoldt n) := by
  have h0 : (0 : ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hd : vonMangoldtWeight n - torusGauge t n =
      (1 - Real.cos (2 * π * cardFactors n * t n.minFac)) * vonMangoldt n := by
    simp only [torusGauge, vonMangoldtWeight]; ring
  rw [hd]
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, ArithmeticFunction.cardFactors_apply_prime hp, hp.minFac_eq,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp
  · rw [if_neg hp, if_neg hp]
    have h1 := Real.neg_one_le_cos (2 * π * cardFactors n * t n.minFac)
    have h2 := Real.cos_le_one (2 * π * cardFactors n * t n.minFac)
    constructor <;> nlinarith

theorem gaugeDistance_nonneg (t : ℕ → ℝ) (x : ℝ) : 0 ≤ gaugeDistance t x :=
  sum_nonneg fun n _ => by
    split_ifs with h
    · exact mul_nonneg (by linarith [Real.cos_le_one (2 * π * t n)])
        (Real.log_nonneg (by exact_mod_cast h.one_lt.le))
    · exact le_rfl

/-- **The torus stabilizer of the count.** The torus gauge of `t` satisfies the count iff RH holds
and the gauge distance `Σ_{p ≤ x} (1 − cos 2π t_p) log p` is `O(√x log² x)`. -/
theorem count_torusGauge_iff (t : ℕ → ℝ) :
    Count (torusGauge t) ↔ RiemannHypothesis ∧ gaugeDistance t =O[atTop] sqrtScale := by
  rw [count_iff_of_le_vonMangoldt (torusGauge_le t)]
  have hψθ : (fun x => Chebyshev.psi x - Chebyshev.theta x) =O[atTop] sqrtScale := by
    refine Chebyshev.isBigO_psi_sub_theta_sqrt.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg x), Real.norm_of_nonneg (sqrtScale_nonneg x), one_mul]
    exact sqrt_le_sqrtScale hx
  have hb : ∀ x, gaugeDistance t x ≤ partialSum (vonMangoldtWeight - torusGauge t) x ∧
      partialSum (vonMangoldtWeight - torusGauge t) x ≤
        gaugeDistance t x + 2 * (Chebyshev.psi x - Chebyshev.theta x) := by
    intro x
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter, gaugeDistance, mul_sum,
      ← sum_add_distrib]
    exact ⟨sum_le_sum fun n _ => (torus_defect_bounds t n).1,
      sum_le_sum fun n _ => by simpa [Pi.sub_apply] using (torus_defect_bounds t n).2⟩
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · refine (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans
      (h : partialSum (vonMangoldtWeight - torusGauge t) =O[atTop] sqrtScale)
    have h0 := gaugeDistance_nonneg t x
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by linarith [(hb x).1]), one_mul]
    exact (hb x).1
  · have hsum := h.add (hψθ.const_mul_left 2)
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans hsum
    obtain ⟨h1, h2⟩ := hb x
    have h0 := gaugeDistance_nonneg t x
    have hθ := Chebyshev.theta_le_psi x
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith), one_mul]
    exact h2

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
