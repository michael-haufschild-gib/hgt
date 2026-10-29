import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheGaugeStabilizerOfTheCount

/-!
# Complex counts and primewise conjugation

A complex torus gauge has two precision obstructions: its nonnegative cosine deficit and its
signed prime sine current. Proper prime powers contribute only `O(√x)` to the imaginary part.
Conjugating whole Euler factors preserves every real coefficient. Choosing these conjugations
against the running prime sine current bounds that current by `log x` at every horizon.
Consequently every real gauge admits a complex lift with exactly the same count criterion.
-/

noncomputable section

open Filter Asymptotics Real Finset
open ArithmeticFunction (vonMangoldt cardFactors)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The partial sum of a complex arithmetic source. -/
def complexPartialSum (a : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Ioc 0 ⌊x⌋₊, a n

/-- Square-root precision for both components of a complex count. -/
def ComplexCount (a : ℕ → ℂ) : Prop :=
  (fun x => complexPartialSum a x - (x : ℂ)) =O[atTop] sqrtScale

theorem complexPartialSum_re (a : ℕ → ℂ) (x : ℝ) :
    (complexPartialSum a x).re = partialSum (fun n => (a n).re) x := by
  simp only [complexPartialSum, Complex.re_sum, partialSum]

theorem complexPartialSum_im (a : ℕ → ℂ) (x : ℝ) :
    (complexPartialSum a x).im = partialSum (fun n => (a n).im) x := by
  simp only [complexPartialSum, Complex.im_sum, partialSum]

theorem complexCount_iff (a : ℕ → ℂ) :
    ComplexCount a ↔ Count (fun n => (a n).re) ∧
      partialSum (fun n => (a n).im) =O[atTop] sqrtScale := by
  have hre (x : ℝ) : (complexPartialSum a x - (x : ℂ)).re =
      partialSum (fun n => (a n).re) x - x := by
    rw [Complex.sub_re, Complex.ofReal_re, complexPartialSum_re]
  have him (x : ℝ) : (complexPartialSum a x - (x : ℂ)).im =
      partialSum (fun n => (a n).im) x := by
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero, complexPartialSum_im]
  constructor
  · intro h
    constructor
    · refine (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans h
      rw [one_mul, Real.norm_eq_abs, ← hre]
      exact Complex.abs_re_le_norm _
    · refine (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans h
      rw [one_mul, Real.norm_eq_abs, ← him]
      exact Complex.abs_im_le_norm _
  · rintro ⟨hr, hi⟩
    obtain ⟨C, hC⟩ := isBigO_iff.mp hr
    obtain ⟨D, hD⟩ := isBigO_iff.mp hi
    refine IsBigO.of_bound (C + D) ?_
    filter_upwards [hC, hD] with x hx hy
    calc ‖complexPartialSum a x - (x : ℂ)‖ ≤
        |partialSum (fun n => (a n).re) x - x| +
          |partialSum (fun n => (a n).im) x| := by
            simpa only [hre, him] using
              Complex.norm_le_abs_re_add_abs_im (complexPartialSum a x - (x : ℂ))
      _ ≤ (C + D) * ‖sqrtScale x‖ := by
        rw [Real.norm_eq_abs] at hx hy
        nlinarith only [hx, hy]

/-- The complex source with Euler phase `exp(2π i t_p)` at each prime. -/
def complexTorusGauge (t : ℕ → ℝ) (n : ℕ) : ℂ :=
  ⟨torusGauge t n,
    Real.sin (2 * π * cardFactors n * t n.minFac) * vonMangoldt n⟩

/-- The imaginary source on primes, before adding higher powers. -/
def primeSineWeight (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n.Prime then Real.sin (2 * π * t n) * Real.log n else 0

/-- The signed prime current of a torus gauge. -/
def gaugeCurrent (t : ℕ → ℝ) : ℝ → ℝ := partialSum (primeSineWeight t)

theorem complexTorusGauge_re (t : ℕ → ℝ) (n : ℕ) :
    (complexTorusGauge t n).re = torusGauge t n := rfl

/-- Removing proper prime powers changes the imaginary count by at most `ψ - θ`. -/
theorem imaginary_partialSum_sub_current_le (t : ℕ → ℝ) (x : ℝ) :
    |partialSum (fun n => (complexTorusGauge t n).im) x - gaugeCurrent t x| ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  rw [gaugeCurrent, partialSum, partialSum, ← sum_sub_distrib,
    Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  by_cases hp : n.Prime
  · simp only [complexTorusGauge, primeSineWeight, if_pos hp, if_neg (not_not.mpr hp),
      ArithmeticFunction.cardFactors_apply_prime hp, Nat.cast_one, mul_one, hp.minFac_eq,
      ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self, abs_zero, le_refl]
  · simp only [complexTorusGauge, primeSineWeight, if_neg hp, if_pos hp, sub_zero, abs_mul,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (Real.abs_sin_le_one _)

private theorem proper_prime_powers_isBigO_sqrtScale :
    (fun x => Chebyshev.psi x - Chebyshev.theta x) =O[atTop] sqrtScale := by
  refine Chebyshev.isBigO_psi_sub_theta_sqrt.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg x),
    Real.norm_of_nonneg (sqrtScale_nonneg x), one_mul]
  exact sqrt_le_sqrtScale hx

theorem imaginary_partialSum_sub_current_isBigO (t : ℕ → ℝ) :
    (fun x => partialSum (fun n => (complexTorusGauge t n).im) x - gaugeCurrent t x)
      =O[atTop] sqrtScale := by
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans
    proper_prime_powers_isBigO_sqrtScale
  rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
  exact imaginary_partialSum_sub_current_le t x

/-- A fixed complex gauge passes exactly when RH, its cosine deficit, and its signed prime
current all have square-root precision. -/
theorem complexCount_torusGauge_iff (t : ℕ → ℝ) :
    ComplexCount (complexTorusGauge t) ↔ RiemannHypothesis ∧
      gaugeDistance t =O[atTop] sqrtScale ∧ gaugeCurrent t =O[atTop] sqrtScale := by
  rw [complexCount_iff, show (fun n => (complexTorusGauge t n).re) = torusGauge t from rfl,
    count_torusGauge_iff, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have := h.sub (imaginary_partialSum_sub_current_isBigO t)
    simpa only [sub_sub_cancel] using this
  · have := (imaginary_partialSum_sub_current_isBigO t).add h
    simpa only [sub_add_cancel] using this

/-! ## A coherent orientation of the whole Euler source -/

private def balancedPrimeState (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if 0 ≤ balancedPrimeState t n then
      balancedPrimeState t n - |primeSineWeight t (n + 1)|
    else balancedPrimeState t n + |primeSineWeight t (n + 1)|

/-- Conjugate each prime phase against the preceding prime sine current. A choice at a prime
acts on its entire Euler factor, hence on all its powers. -/
def balancedGauge (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 0 ≤ balancedPrimeState t (n - 1) then
    if 0 ≤ primeSineWeight t n then -t n else t n
  else if 0 ≤ primeSineWeight t n then t n else -t n

theorem balancedGauge_eq_or_neg (t : ℕ → ℝ) (n : ℕ) :
    balancedGauge t n = t n ∨ balancedGauge t n = -t n := by
  unfold balancedGauge
  split_ifs <;> simp

/-- Primewise conjugation preserves the real coefficient at every prime power. -/
theorem torusGauge_eq_of_pointwise_conjugate {t u : ℕ → ℝ}
    (h : ∀ n, u n = t n ∨ u n = -t n) : torusGauge u = torusGauge t := by
  funext n
  unfold torusGauge
  rcases h n.minFac with hn | hn
  · rw [hn]
  · rw [hn, mul_neg, Real.cos_neg]

theorem torusGauge_balancedGauge (t : ℕ → ℝ) :
    torusGauge (balancedGauge t) = torusGauge t :=
  torusGauge_eq_of_pointwise_conjugate (balancedGauge_eq_or_neg t)

private theorem primeSineWeight_balancedGauge (t : ℕ → ℝ) (n : ℕ) :
    primeSineWeight (balancedGauge t) n =
      if 0 ≤ balancedPrimeState t (n - 1) then -|primeSineWeight t n|
      else |primeSineWeight t n| := by
  by_cases hp : n.Prime
  · simp only [primeSineWeight, if_pos hp, balancedGauge]
    split_ifs with hs hw hw
    · simp only [mul_neg, Real.sin_neg, neg_mul, abs_of_nonneg hw]
    · simp only [abs_of_neg (lt_of_not_ge hw), neg_neg]
    · simp only [abs_of_nonneg hw]
    · simp only [mul_neg, Real.sin_neg, neg_mul, abs_of_neg (lt_of_not_ge hw)]
  · simp only [primeSineWeight, if_neg hp, abs_zero, neg_zero, ite_self]

private theorem balancedPrimeState_eq_sum (t : ℕ → ℝ) (N : ℕ) :
    balancedPrimeState t N = ∑ n ∈ Ioc 0 N, primeSineWeight (balancedGauge t) n := by
  induction N with
  | zero => simp only [balancedPrimeState, Ioc_self, sum_empty]
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), primeSineWeight_balancedGauge,
      Nat.add_sub_cancel, ← ih]
    simp only [balancedPrimeState]
    split_ifs <;> ring

private theorem primeSineWeight_abs_le (t : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |primeSineWeight t n| ≤ Real.log n := by
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold primeSineWeight
  split_ifs
  · rw [abs_mul, abs_of_nonneg hl]
    exact mul_le_of_le_one_left hl (Real.abs_sin_le_one _)
  · simpa only [abs_zero] using hl

private theorem balancedPrimeState_bound (t : ℕ → ℝ) (N : ℕ) :
    |balancedPrimeState t N| ≤ Real.log N := by
  induction N with
  | zero => simp only [balancedPrimeState, abs_zero, Nat.cast_zero, Real.log_zero, le_refl]
  | succ N ih =>
    by_cases hN : N = 0
    · subst N
      simp [balancedPrimeState, primeSineWeight]
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hs : |balancedPrimeState t N| ≤ Real.log (N + 1 : ℕ) :=
      ih.trans (Real.log_le_log hN0 (by exact_mod_cast Nat.le_succ N))
    have hw := primeSineWeight_abs_le t (Nat.succ_le_succ (Nat.zero_le N))
    obtain ⟨hlo, hhi⟩ := abs_le.mp hs
    have hw0 := abs_nonneg (primeSineWeight t (N + 1))
    simp only [balancedPrimeState]
    split_ifs with h
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The chosen conjugations keep the signed prime current within one prime-sized increment
at every real horizon. -/
theorem gaugeCurrent_balancedGauge_le (t : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |gaugeCurrent (balancedGauge t) x| ≤ Real.log x := by
  rw [gaugeCurrent, partialSum, ← balancedPrimeState_eq_sum]
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  exact (balancedPrimeState_bound t _).trans (Real.log_le_log
    (by exact_mod_cast (show 0 < ⌊x⌋₊ from hN)) (Nat.floor_le (by linarith)))

theorem gaugeCurrent_balancedGauge_isBigO (t : ℕ → ℝ) :
    gaugeCurrent (balancedGauge t) =O[atTop] sqrtScale := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hl : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (exp_pos 1) hx
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
  rw [one_mul, Real.norm_eq_abs, Real.norm_of_nonneg (sqrtScale_nonneg x)]
  refine (gaugeCurrent_balancedGauge_le t hx1).trans ?_
  calc Real.log x ≤ Real.log x ^ 2 := by nlinarith only [hl]
    _ ≤ sqrtScale x := le_mul_of_one_le_left (sq_nonneg _) hs

/-- The complete imaginary count of the lift costs only `log x + ψ(x) - θ(x)`. -/
theorem imaginary_partialSum_balancedGauge_le (t : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |partialSum (fun n => (complexTorusGauge (balancedGauge t) n).im) x| ≤
      Real.log x + (Chebyshev.psi x - Chebyshev.theta x) := by
  have h := abs_add_le
    (partialSum (fun n => (complexTorusGauge (balancedGauge t) n).im) x -
      gaugeCurrent (balancedGauge t) x) (gaugeCurrent (balancedGauge t) x)
  rw [sub_add_cancel] at h
  linarith only [h, imaginary_partialSum_sub_current_le (balancedGauge t) x,
    gaugeCurrent_balancedGauge_le t hx]

/-- Every real torus gauge has a coherent complex lift with precisely the same count.
No conjectural estimate is used to choose the lift. -/
theorem complexCount_balancedGauge_iff (t : ℕ → ℝ) :
    ComplexCount (complexTorusGauge (balancedGauge t)) ↔ Count (torusGauge t) := by
  rw [complexCount_iff, show (fun n => (complexTorusGauge (balancedGauge t) n).re) =
    torusGauge (balancedGauge t) from rfl, torusGauge_balancedGauge]
  have hi := (imaginary_partialSum_sub_current_isBigO (balancedGauge t)).add
    (gaugeCurrent_balancedGauge_isBigO t)
  have hi' : partialSum (fun n => (complexTorusGauge (balancedGauge t) n).im)
      =O[atTop] sqrtScale := by simpa only [sub_add_cancel] using hi
  exact and_iff_left hi'

/-- The image of complex count gauges under independent Euler-factor conjugation is exactly
the real gauge stabilizer. -/
theorem exists_complexCount_lift_iff (t : ℕ → ℝ) :
    (∃ u : ℕ → ℝ, (∀ n, u n = t n ∨ u n = -t n) ∧
      ComplexCount (complexTorusGauge u)) ↔
        RiemannHypothesis ∧ gaugeDistance t =O[atTop] sqrtScale := by
  rw [← count_torusGauge_iff]
  constructor
  · rintro ⟨u, hu, hc⟩
    have hr := (complexCount_iff (complexTorusGauge u)).mp hc |>.1
    change Count (torusGauge u) at hr
    rwa [torusGauge_eq_of_pointwise_conjugate hu] at hr
  · intro hc
    exact ⟨balancedGauge t, balancedGauge_eq_or_neg t,
      (complexCount_balancedGauge_iff t).mpr hc⟩

/-- A complex count lift can retain any prescribed finite prefix of the original Euler phases.
Thus the lift can be chosen in every finite-coordinate neighborhood of that gauge. -/
theorem exists_complexCount_lift_preserving_prefix (t : ℕ → ℝ) (N : ℕ) :
    ∃ u : ℕ → ℝ, (∀ n, u n = t n ∨ u n = -t n) ∧
      (∀ n ≤ N, u n = t n) ∧ torusGauge u = torusGauge t ∧
      (ComplexCount (complexTorusGauge u) ↔ Count (torusGauge t)) := by
  let u : ℕ → ℝ := fun n => if n ≤ N then t n else balancedGauge t n
  have hu : ∀ n, u n = t n ∨ u n = -t n := by
    intro n
    dsimp only [u]
    split_ifs
    · exact Or.inl rfl
    · exact balancedGauge_eq_or_neg t n
  have hreal := torusGauge_eq_of_pointwise_conjugate hu
  have hfinite : primeSineWeight u - primeSineWeight (balancedGauge t) ∈ sqrtClass := by
    refine mem_sqrtClass_of_eventually_zero (N := N) fun n hn => ?_
    have hun : u n = balancedGauge t n := if_neg (not_le.mpr hn)
    simp only [Pi.sub_apply, primeSineWeight, hun, sub_self]
  have hcurrent : gaugeCurrent u =O[atTop] sqrtScale := by
    have h := (hfinite : partialSum
      (primeSineWeight u - primeSineWeight (balancedGauge t)) =O[atTop] sqrtScale).add
        (gaugeCurrent_balancedGauge_isBigO t)
    refine h.congr_left fun x => ?_
    rw [partialSum_sub]
    exact sub_add_cancel _ _
  refine ⟨u, hu, fun n hn => if_pos hn, hreal, ?_⟩
  rw [complexCount_torusGauge_iff, ← and_assoc, ← count_torusGauge_iff, hreal]
  exact and_iff_left hcurrent

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
