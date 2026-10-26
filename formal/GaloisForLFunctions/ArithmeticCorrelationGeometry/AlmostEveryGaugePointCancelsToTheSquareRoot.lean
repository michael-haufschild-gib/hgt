import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.HTGeometry.SquarefreeDensityLowerBound

/-!
# Almost every gauge point cancels to the square root

For a bounded source `a` the twisted partial sums `S_N(x) = Σ_{n ≤ N} a_n χ_x(n)` are gauge charged:
by gauge orthogonality every block `Σ_{M < n ≤ M'} a_n χ_x(n)` has mean square `Σ |a_n|²`. This
module turns that second-moment fact into a pointwise law on almost all of the gauge orbit.

* **Dyadic maximal inequality** (`sq_norm_gaugePartialSum_le`, `integral_dyadicEnergy`). Every
  `n < 2^{K+1}` is a telescoping sum of at most one dyadic block per level `j ≤ K`, so by
  Cauchy–Schwarz `sup_{n < 2^{K+1}} |S_n|² ≤ (K+1) W_K`, where the dyadic energy `W_K` (the squares of
  all blocks of all levels) has gauge mean `(K+1) Σ_{n ≤ 2^{K+1}} |a_n|²`. This is the
  Rademacher–Menshov inequality for the orthonormal system of twists.
* **Almost-sure square-root law** (`ae_eventually_sq_norm_gaugePartialSum_le`,
  `ae_exists_norm_gaugePartialSum_le`). By Markov and Borel–Cantelli (`Σ 1/(K+1)² < ∞`), for
  Haar-almost every gauge point `|S_N(x)| ≤ C_x √(N+1) (1 + log(N+1))²` for all `N`.
* **The Möbius orbit** (`moebius_gauge_trichotomy`). The half-power law `S_N = O(N^{1/2+δ})` for
  every `δ > 0` holds for the Möbius source at almost every gauge point; it fails at the Liouville
  twin, whose partial sums count squarefree integers; and at the gauge point `0` it is the
  Riemann hypothesis (Littlewood's criterion, `RHTower`).

Gauge status: the law is a property of a gauge point, not of the orbit; the orbit carries it with
full Haar measure. RH is therefore the statement that the actual source lies outside a Haar-null
exceptional set that contains its Liouville twin. Every argument that uses only multiplicative data
proves the same statement for the whole orbit, so it proves the law almost surely and decides
nothing about the point `0`.
-/

open MeasureTheory Finset Filter
open scoped ComplexConjugate ArithmeticFunction.Moebius ArithmeticFunction.Omega

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-! ### Dyadic decomposition -/

/-- The twisted partial sum `S_N(x) = Σ_{1 ≤ n ≤ N} a_n χ_x(n)`. -/
def gaugePartialSum (a : ℕ → ℂ) (N : ℕ) (x : GaugeTorus) : ℂ := twistSum (Ioc 0 N) a x

/-- The dyadic block `Σ_{2^j i < n ≤ 2^j (i+1)} a_n χ_x(n)`. -/
def dyadicBlock (a : ℕ → ℂ) (j i : ℕ) (x : GaugeTorus) : ℂ :=
  twistSum (Ioc (2 ^ j * i) (2 ^ j * (i + 1))) a x

/-- The dyadic energy at depth `K`: the squared blocks of all levels `j ≤ K` below `2^{K+1}`. -/
def dyadicEnergy (a : ℕ → ℂ) (K : ℕ) (x : GaugeTorus) : ℝ :=
  ∑ j ∈ range (K + 1), ∑ i ∈ range (2 ^ (K + 1 - j)), ‖dyadicBlock a j i x‖ ^ 2

/-- Consecutive intervals with increasing endpoints tile. -/
theorem sum_Ioc_tile_mono {M : Type*} [AddCommMonoid M] (f : ℕ → M) {e : ℕ → ℕ} (he : Monotone e)
    (k : ℕ) : ∑ i ∈ range k, ∑ n ∈ Ioc (e i) (e (i + 1)), f n = ∑ n ∈ Ioc (e 0) (e k), f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, sum_Ioc_consecutive f (he (Nat.zero_le k)) (he (Nat.le_succ k))]

/-- Consecutive intervals with decreasing endpoints tile. -/
theorem sum_Ioc_tile_anti {M : Type*} [AddCommMonoid M] (f : ℕ → M) {e : ℕ → ℕ} (he : Antitone e)
    (k : ℕ) : ∑ j ∈ range k, ∑ n ∈ Ioc (e (j + 1)) (e j), f n = ∑ n ∈ Ioc (e k) (e 0), f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, add_comm,
      sum_Ioc_consecutive f (he (Nat.le_succ k)) (he (Nat.zero_le k))]

/-- The dyadic truncation `2^j ⌊n / 2^j⌋`. -/
def dyadicFloor (n j : ℕ) : ℕ := 2 ^ j * (n / 2 ^ j)

theorem dyadicFloor_succ (n j : ℕ) : dyadicFloor n (j + 1) = 2 ^ j * (2 * (n / 2 ^ j / 2)) := by
  rw [dyadicFloor, Nat.div_div_eq_div_mul, pow_succ]
  ring

theorem antitone_dyadicFloor (n : ℕ) : Antitone (dyadicFloor n) := by
  refine antitone_nat_of_succ_le fun j => ?_
  rw [dyadicFloor_succ, dyadicFloor]
  exact Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)

theorem dyadicFloor_zero (n : ℕ) : dyadicFloor n 0 = n := by simp [dyadicFloor]

theorem dyadicFloor_eq_zero {n K : ℕ} (hn : n < 2 ^ K) : dyadicFloor n K = 0 := by
  simp [dyadicFloor, Nat.div_eq_of_lt hn]

/-- The partial sum is the telescoping sum of its dyadic pieces. -/
theorem gaugePartialSum_eq_sum_pieces (a : ℕ → ℂ) {K n : ℕ} (hn : n < 2 ^ (K + 1))
    (x : GaugeTorus) :
    gaugePartialSum a n x =
      ∑ j ∈ range (K + 1), twistSum (Ioc (dyadicFloor n (j + 1)) (dyadicFloor n j)) a x := by
  simp only [twistSum, gaugePartialSum]
  rw [sum_Ioc_tile_anti (fun m => a m * twist x m) (antitone_dyadicFloor n),
    dyadicFloor_eq_zero hn, dyadicFloor_zero]

/-- Each dyadic piece is empty or a single block of its level. -/
theorem sq_norm_piece_le (a : ℕ → ℂ) {K n j : ℕ} (hn : n < 2 ^ (K + 1)) (hj : j ≤ K)
    (x : GaugeTorus) :
    ‖twistSum (Ioc (dyadicFloor n (j + 1)) (dyadicFloor n j)) a x‖ ^ 2 ≤
      ∑ i ∈ range (2 ^ (K + 1 - j)), ‖dyadicBlock a j i x‖ ^ 2 := by
  set m := n / 2 ^ j with hm
  have hmlt : m < 2 ^ (K + 1 - j) := by
    rw [hm, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact hn
  rw [dyadicFloor_succ, dyadicFloor, ← hm]
  rcases Nat.even_or_odd m with hev | hodd
  · rw [Nat.two_mul_div_two_of_even hev, Ioc_self, twistSum, sum_empty, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sum_nonneg fun _ _ => by positivity
  · have hm1 : 1 ≤ m := hodd.pos
    have h2 : 2 * (m / 2) = (m - 1) := by
      have := Nat.two_mul_odd_div_two hodd
      omega
    have hblock : twistSum (Ioc (2 ^ j * (2 * (m / 2))) (2 ^ j * m)) a x =
        dyadicBlock a j (m - 1) x := by
      rw [dyadicBlock, h2, Nat.sub_add_cancel hm1]
    rw [hblock]
    exact single_le_sum (f := fun i => ‖dyadicBlock a j i x‖ ^ 2) (fun _ _ => by positivity)
      (mem_range.mpr (by omega))

/-- **Dyadic maximal inequality.** Every partial sum below `2^{K+1}` is controlled by the dyadic
energy: `|S_n|² ≤ (K+1) W_K`. -/
theorem sq_norm_gaugePartialSum_le (a : ℕ → ℂ) {K n : ℕ} (hn : n < 2 ^ (K + 1)) (x : GaugeTorus) :
    ‖gaugePartialSum a n x‖ ^ 2 ≤ ((K : ℝ) + 1) * dyadicEnergy a K x := by
  rw [gaugePartialSum_eq_sum_pieces a hn]
  calc ‖∑ j ∈ range (K + 1), twistSum (Ioc (dyadicFloor n (j + 1)) (dyadicFloor n j)) a x‖ ^ 2
      ≤ (∑ j ∈ range (K + 1),
          ‖twistSum (Ioc (dyadicFloor n (j + 1)) (dyadicFloor n j)) a x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ #(range (K + 1)) * ∑ j ∈ range (K + 1),
          ‖twistSum (Ioc (dyadicFloor n (j + 1)) (dyadicFloor n j)) a x‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ ((K : ℝ) + 1) * dyadicEnergy a K x := by
        rw [card_range, dyadicEnergy]
        push_cast
        gcongr with j hj
        exact sq_norm_piece_le a hn (Nat.lt_succ_iff.mp (mem_range.mp hj)) x

/-! ### The gauge mean of the dyadic energy -/

theorem continuous_dyadicEnergy (a : ℕ → ℂ) (K : ℕ) : Continuous (dyadicEnergy a K) :=
  continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
    ((continuous_twistSum _ _).norm).pow 2

theorem integrable_dyadicEnergy (a : ℕ → ℂ) (K : ℕ) : Integrable (dyadicEnergy a K) gaugeHaar :=
  (continuous_dyadicEnergy a K).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **The dyadic energy has gauge mean `(K+1) Σ_{n ≤ 2^{K+1}} |a_n|²`**: each level tiles
`(0, 2^{K+1}]`, and each block has the coefficient energy as gauge mean square. -/
theorem integral_dyadicEnergy (a : ℕ → ℂ) (K : ℕ) :
    ∫ x, dyadicEnergy a K x ∂gaugeHaar = ((K : ℝ) + 1) * ∑ n ∈ Ioc 0 (2 ^ (K + 1)), ‖a n‖ ^ 2 := by
  have hint : ∀ j i, Integrable (fun x => ‖dyadicBlock a j i x‖ ^ 2) gaugeHaar := fun j i =>
    (((continuous_twistSum _ _).norm).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hblock : ∀ j i, ∫ x, ‖dyadicBlock a j i x‖ ^ 2 ∂gaugeHaar =
      ∑ n ∈ Ioc (2 ^ j * i) (2 ^ j * (i + 1)), ‖a n‖ ^ 2 := fun j i =>
    integral_normSq_twistSum (fun n hn => by have := (mem_Ioc.mp hn).1; omega) a
  have hlevel : ∀ j ∈ range (K + 1), ∑ i ∈ range (2 ^ (K + 1 - j)),
      ∑ n ∈ Ioc (2 ^ j * i) (2 ^ j * (i + 1)), ‖a n‖ ^ 2 = ∑ n ∈ Ioc 0 (2 ^ (K + 1)), ‖a n‖ ^ 2 := by
    intro j hj
    have hj' : j ≤ K + 1 := by have := mem_range.mp hj; omega
    rw [sum_Ioc_tile_mono (fun n => ‖a n‖ ^ 2) (e := fun i => 2 ^ j * i)
      (fun _ _ h => Nat.mul_le_mul_left _ h), mul_zero, ← pow_add, Nat.add_sub_cancel' hj']
  rw [dyadicEnergy, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ => hint j i]
  simp_rw [integral_finset_sum _ fun i _ => hint _ i, hblock]
  rw [sum_congr rfl hlevel, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-! ### Borel–Cantelli on the gauge torus -/

/-- The exceptional event at depth `K`: dyadic energy at least `2^{K+1} (K+1)³`. -/
def dyadicExceptional (a : ℕ → ℂ) (K : ℕ) : Set GaugeTorus :=
  {x | (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 3 ≤ dyadicEnergy a K x}

theorem measureReal_dyadicExceptional_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (K : ℕ) :
    gaugeHaar.real (dyadicExceptional a K) ≤ 1 / ((K : ℝ) + 1) ^ 2 := by
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hP : (0 : ℝ) < (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 3 := by positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => (show 0 ≤ dyadicEnergy a K x from
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity))
    (integrable_dyadicEnergy a K) ((2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 3)
  have henergy : ∑ n ∈ Ioc 0 (2 ^ (K + 1)), ‖a n‖ ^ 2 ≤ (2 : ℝ) ^ (K + 1) := by
    calc ∑ n ∈ Ioc 0 (2 ^ (K + 1)), ‖a n‖ ^ 2 ≤ ∑ _n ∈ Ioc 0 (2 ^ (K + 1)), (1 : ℝ) :=
          sum_le_sum fun n _ => by
            have := ha n
            nlinarith [norm_nonneg (a n)]
      _ = (2 : ℝ) ^ (K + 1) := by simp
  rw [integral_dyadicEnergy] at hmarkov
  rw [le_div_iff₀ (by positivity)]
  have h1 : gaugeHaar.real (dyadicExceptional a K) * ((2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 3) ≤
      ((K : ℝ) + 1) * (2 : ℝ) ^ (K + 1) := by
    rw [mul_comm]
    exact hmarkov.trans (mul_le_mul_of_nonneg_left henergy hK.le)
  have h2 : gaugeHaar.real (dyadicExceptional a K) * ((K : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (K + 1) *
      ((K : ℝ) + 1)) ≤ 1 * ((2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1)) := by nlinarith
  exact le_of_mul_le_mul_right h2 (by positivity)

theorem tsum_measure_dyadicExceptional_ne_top (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∑' K, gaugeHaar (dyadicExceptional a K) ≠ ⊤ := by
  have hsum : Summable fun K : ℕ => 1 / ((K : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' K : ℕ, 1 / ((K : ℝ) + 1) ^ 2)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum]
  refine ENNReal.tsum_le_tsum fun K => ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top gaugeHaar (dyadicExceptional a K)), ← measureReal_def]
  exact ENNReal.ofReal_le_ofReal (measureReal_dyadicExceptional_le a ha K)

/-- **Almost-sure dyadic square-root law.** For a source bounded by one, at Haar-almost every gauge
point, eventually in `K`, every partial sum below `2^{K+1}` satisfies `|S_n|² ≤ 2^{K+1} (K+1)⁴`. -/
theorem ae_eventually_sq_norm_gaugePartialSum_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ᵐ x ∂gaugeHaar, ∀ᶠ K in atTop, ∀ n < 2 ^ (K + 1),
      ‖gaugePartialSum a n x‖ ^ 2 ≤ (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 4 := by
  filter_upwards [ae_eventually_notMem (tsum_measure_dyadicExceptional_ne_top a ha)] with x hx
  filter_upwards [hx] with K hK n hn
  have hE : dyadicEnergy a K x < (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 3 := not_le.mp hK
  calc ‖gaugePartialSum a n x‖ ^ 2 ≤ ((K : ℝ) + 1) * dyadicEnergy a K x :=
        sq_norm_gaugePartialSum_le a hn x
    _ ≤ ((K : ℝ) + 1) * ((2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left hE.le (by positivity)
    _ = (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 4 := by ring

/-- The level of `N` is at most `2 (1 + log (N+1)) - 1`. -/
theorem nat_log_add_one_le (N : ℕ) : ((Nat.log 2 N : ℕ) : ℝ) + 1 ≤ 2 * (1 + Real.log (N + 1)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
    positivity
  have hpow : ((2 : ℝ) ^ Nat.log 2 N) ≤ (N : ℝ) + 1 := by
    have := Nat.pow_log_le_self 2 hN.ne'
    exact_mod_cast this.trans (Nat.le_succ N)
  have hlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log ((N : ℝ) + 1) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hl2 := Real.log_two_gt_d9
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  nlinarith [(Nat.log 2 N).cast_nonneg (α := ℝ)]

/-- **Almost every gauge point cancels to the square root.** For a source bounded by one, at
Haar-almost every gauge point, `|S_N(x)| ≤ C_x √(N+1) (1 + log (N+1))²` for every `N`. -/
theorem ae_exists_norm_gaugePartialSum_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ᵐ x ∂gaugeHaar, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖gaugePartialSum a N x‖ ≤ C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 := by
  filter_upwards [ae_eventually_sq_norm_gaugePartialSum_le a ha] with x hx
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hx
  set C₀ := ∑ n ∈ range (2 ^ (K₀ + 1)), ‖gaugePartialSum a n x‖
  refine ⟨C₀ + 6, by positivity, fun N => ?_⟩
  have hsqrt : 1 ≤ Real.sqrt ((N : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith [N.cast_nonneg (α := ℝ)])
  have hlog0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
  have hfac : 1 ≤ Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hsqrt (one_le_pow₀ (by linarith))
  by_cases hsmall : N < 2 ^ (K₀ + 1)
  · have hC₀ : ‖gaugePartialSum a N x‖ ≤ C₀ :=
      single_le_sum (f := fun n => ‖gaugePartialSum a n x‖) (fun _ _ => norm_nonneg _)
        (mem_range.mpr hsmall)
    calc ‖gaugePartialSum a N x‖ ≤ C₀ := hC₀
      _ ≤ (C₀ + 6) * 1 := by linarith
      _ ≤ (C₀ + 6) * (Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := by ring
  · push_neg at hsmall
    have hN : N ≠ 0 := by
      intro h
      rw [h] at hsmall
      exact absurd hsmall (not_le.mpr (by positivity))
    set K := Nat.log 2 N
    have hKK₀ : K₀ ≤ K := by
      have := Nat.le_log_of_pow_le one_lt_two hsmall
      omega
    have hlt : N < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self one_lt_two N
    have hbound := hK₀ K hKK₀ N hlt
    have h2K : (2 : ℝ) ^ (K + 1) ≤ 2 * ((N : ℝ) + 1) := by
      have := Nat.pow_log_le_self 2 hN
      rw [pow_succ]
      have : ((2 ^ K : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      push_cast at this
      linarith
    have hKlog := nat_log_add_one_le N
    have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
    have hsq : ‖gaugePartialSum a N x‖ ^ 2 ≤
        (6 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2) ^ 2 := by
      have hs : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 :=
        Real.sq_sqrt (by linarith [N.cast_nonneg (α := ℝ)])
      have h4 : ((K : ℝ) + 1) ^ 4 ≤ (2 * (1 + Real.log ((N : ℝ) + 1))) ^ 4 :=
        pow_le_pow_left₀ hK1 hKlog 4
      calc ‖gaugePartialSum a N x‖ ^ 2 ≤ (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 4 := hbound
        _ ≤ (2 * ((N : ℝ) + 1)) * (2 * (1 + Real.log ((N : ℝ) + 1))) ^ 4 :=
            mul_le_mul h2K h4 (by positivity) (by positivity)
        _ = 32 * ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 4 := by ring
        _ ≤ 36 * ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 4 := by
            have : 0 ≤ ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 4 := by positivity
            nlinarith
        _ = (6 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2) ^ 2 := by
            rw [mul_pow, mul_pow, hs]
            ring
    have h6 : ‖gaugePartialSum a N x‖ ≤ 6 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
    calc ‖gaugePartialSum a N x‖ ≤ 6 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 := h6
      _ ≤ (C₀ + 6) * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 := by
          have : 0 ≤ Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 := by positivity
          have hC0 : 0 ≤ C₀ := sum_nonneg fun _ _ => norm_nonneg _
          nlinarith

/-! ### The half-power law on the Möbius orbit -/

/-- **The half-power law at a gauge point**: `Σ_{n ≤ N} a_n χ_x(n) = O(N^{1/2+δ})` for every
`δ > 0`. -/
def GaugeHalfPowerLaw (a : ℕ → ℂ) (x : GaugeTorus) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    ‖∑ n ∈ range (N + 1), a n * twist x n‖ ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)

/-- A polylogarithmic loss is below every power: `√X (1 + log X)² ≤ (1 + 4/δ)² X^{1/2+δ}`. -/
theorem sqrt_mul_one_add_log_sq_le {X δ : ℝ} (hX : 1 ≤ X) (hδ : 0 < δ) :
    Real.sqrt X * (1 + Real.log X) ^ 2 ≤ (1 + 4 / δ) ^ 2 * X ^ ((1 / 2 : ℝ) + δ) := by
  have hX0 : 0 < X := by linarith
  have hlog : Real.log X ≤ X ^ (δ / 2) / (δ / 2) := Real.log_le_rpow_div hX0.le (by linarith)
  have hpow1 : 1 ≤ X ^ (δ / 2) := Real.one_le_rpow hX (by linarith)
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have h1 : 1 + Real.log X ≤ (1 + 4 / δ) * X ^ (δ / 2) := by
    have : X ^ (δ / 2) / (δ / 2) = (2 / δ) * X ^ (δ / 2) := by field_simp
    rw [this] at hlog
    have h4 : (2 / δ) * X ^ (δ / 2) ≤ (4 / δ) * X ^ (δ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [div_le_div_iff_of_pos_right hδ]
      norm_num
    nlinarith
  have hsq : (1 + Real.log X) ^ 2 ≤ ((1 + 4 / δ) * X ^ (δ / 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h1 2
  have hsplit : ((1 + 4 / δ) * X ^ (δ / 2)) ^ 2 = (1 + 4 / δ) ^ 2 * X ^ δ := by
    rw [mul_pow, ← Real.rpow_natCast (X ^ (δ / 2)), ← Real.rpow_mul hX0.le]
    norm_num
  rw [hsplit] at hsq
  calc Real.sqrt X * (1 + Real.log X) ^ 2 ≤ Real.sqrt X * ((1 + 4 / δ) ^ 2 * X ^ δ) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    _ = (1 + 4 / δ) ^ 2 * (X ^ (1 / 2 : ℝ) * X ^ δ) := by
        rw [Real.sqrt_eq_rpow]
        ring
    _ = (1 + 4 / δ) ^ 2 * X ^ ((1 / 2 : ℝ) + δ) := by rw [Real.rpow_add hX0]

/-- **The half-power law holds at almost every gauge point** for every source bounded by one. -/
theorem ae_gaugeHalfPowerLaw (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ᵐ x ∂gaugeHaar, GaugeHalfPowerLaw a x := by
  filter_upwards [ae_exists_norm_gaugePartialSum_le a ha] with x ⟨C, hC, hbound⟩
  intro δ hδ
  refine ⟨1 + C * (1 + 4 / δ) ^ 2, by positivity, fun N => ?_⟩
  have hX : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  have hpow : 1 ≤ ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := Real.one_le_rpow hX (by positivity)
  have hsplit : ∑ n ∈ range (N + 1), a n * twist x n = a 0 * twist x 0 + gaugePartialSum a N x := by
    rw [range_eq_Ico, ← Ico_insert_succ_left (Nat.succ_pos N), sum_insert (by simp),
      gaugePartialSum, twistSum, Nat.Ico_succ_right_eq_Ioc]
  rw [hsplit]
  have h0 : ‖a 0 * twist x 0‖ ≤ 1 := by rw [norm_mul, norm_twist, mul_one]; exact ha 0
  have hS := (hbound N).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (sqrt_mul_one_add_log_sq_le hX hδ) hC)
  calc ‖a 0 * twist x 0 + gaugePartialSum a N x‖ ≤ 1 + C * ((1 + 4 / δ) ^ 2 *
        ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) := (norm_add_le _ _).trans (add_le_add h0 hS)
    _ ≤ (1 + C * (1 + 4 / δ) ^ 2) * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by nlinarith

/-- The gauge point `0` is the untwisted source. -/
theorem twist_zero (n : ℕ) : twist 0 n = 1 := by
  have h := twist_add 0 0 n
  rw [add_zero] at h
  have hne : twist 0 n ≠ 0 := by
    intro h0
    have := norm_twist 0 n
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact (mul_eq_left₀ hne).mp h.symm

/-- **At the gauge point `0` the Möbius half-power law is the Riemann hypothesis.** -/
theorem gaugeHalfPowerLaw_moebius_zero_iff :
    GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) 0 ↔ RiemannHypothesis := by
  rw [← RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis]
  simp only [GaugeHalfPowerLaw, RHTower.MobiusMertensAllStrictHalfPowerBound,
    RHTower.mobiusMertensPartialSum, RHTower.mobiusComplexCoefficient, twist_zero, mul_one]

/-- The Liouville gauge point: the twist `χ(n) = (−1)^{Ω(n)}`. -/
theorem exists_liouville_gaugePoint :
    ∃ x : GaugeTorus, ∀ n, n ≠ 0 → twist x n = (-1 : ℂ) ^ Ω n := by
  refine exists_twist_eq (fun n => (-1 : ℂ) ^ Ω n) (by simp) (fun m n hm hn => ?_) (fun p _ => ?_)
  · simp only
    rw [ArithmeticFunction.cardFactors_mul hm hn, pow_add]
  · simp

/-- On squarefree support the Liouville twist of `μ` is `μ²`. -/
theorem moebius_mul_neg_one_pow_cardFactors (n : ℕ) :
    ((μ n : ℤ) : ℂ) * (-1 : ℂ) ^ Ω n = (((μ n : ℤ) ^ 2 : ℤ) : ℂ) := by
  by_cases hsq : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    push_cast
    rw [← pow_mul, ← pow_mul, mul_comm (Ω n) 2, pow_mul, pow_mul]
    norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- **The Liouville twin violates the half-power law**: its partial sums count squarefree
integers, at least `K/50` of them up to `2K`. -/
theorem not_gaugeHalfPowerLaw_moebius_liouville {x : GaugeTorus}
    (hx : ∀ n, n ≠ 0 → twist x n = (-1 : ℂ) ^ Ω n) :
    ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x := by
  classical
  intro h
  obtain ⟨C, hC, hbound⟩ := h (1 / 4) (by norm_num)
  -- the twisted partial sum is the squarefree count
  have hcount : ∀ N, ((#((Ioc N (2 * N)).filter Squarefree) : ℕ) : ℝ) ≤
      ‖∑ n ∈ range (2 * N + 1), ((μ n : ℤ) : ℂ) * twist x n‖ := by
    intro N
    have hterm : ∀ n ∈ range (2 * N + 1), ((μ n : ℤ) : ℂ) * twist x n =
        ((((μ n : ℤ) ^ 2 : ℤ) : ℝ) : ℂ) := by
      intro n _
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [hx n hn.ne', moebius_mul_neg_one_pow_cardFactors]
        push_cast
        rfl
    rw [sum_congr rfl hterm, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    have hsub : (Ioc N (2 * N)).filter Squarefree ⊆ range (2 * N + 1) := fun n hn => by
      have := (mem_Ioc.mp (mem_filter.mp hn).1).2
      exact mem_range.mpr (by omega)
    calc ((#((Ioc N (2 * N)).filter Squarefree) : ℕ) : ℝ)
        = ∑ n ∈ (Ioc N (2 * N)).filter Squarefree, (((μ n : ℤ) ^ 2 : ℤ) : ℝ) := by
          rw [cast_card]
          refine sum_congr rfl fun n hn => ?_
          rw [ArithmeticFunction.moebius_apply_of_squarefree (mem_filter.mp hn).2]
          push_cast
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
      _ ≤ ∑ n ∈ range (2 * N + 1), (((μ n : ℤ) ^ 2 : ℤ) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by push_cast; positivity
  -- compare `N/50` with `C (2N+1)^{3/4}` at a large `N`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (150 * C + 1) ^ 4 ≤ (N : ℝ) ∧ 1 ≤ (N : ℝ) :=
    ⟨⌈(150 * C + 1) ^ 4⌉₊ + 1, by
      constructor <;> push_cast <;> linarith [Nat.le_ceil ((150 * C + 1) ^ 4),
        (show (0 : ℝ) ≤ (150 * C + 1) ^ 4 by positivity)]⟩
  have hlow := (card_filter_squarefree_Ioc_ge N).trans (hcount N)
  have hup := hbound (2 * N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hX : ((2 * N : ℕ) : ℝ) + 1 ≤ 3 * (N : ℝ) := by push_cast; linarith
  have hrpow : (((2 * N : ℕ) : ℝ) + 1) ^ ((1 / 2 : ℝ) + 1 / 4) ≤ (3 * (N : ℝ)) ^ ((3 / 4 : ℝ)) := by
    rw [show (1 / 2 : ℝ) + 1 / 4 = 3 / 4 by norm_num]
    exact Real.rpow_le_rpow (by positivity) hX (by norm_num)
  -- `N^{1/4} ≥ 150 C + 1`
  have hquart : 150 * C + 1 ≤ (N : ℝ) ^ ((1 / 4 : ℝ)) := by
    have := Real.rpow_le_rpow (by positivity) hN.1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
    |>.trans_eq' (by norm_num)
  have hsplitN : (N : ℝ) = (N : ℝ) ^ ((3 / 4 : ℝ)) * (N : ℝ) ^ ((1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hN0]
    norm_num
  have h3 : (3 * (N : ℝ)) ^ ((3 / 4 : ℝ)) ≤ 3 * (N : ℝ) ^ ((3 / 4 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hN0.le]
    gcongr
    calc (3 : ℝ) ^ ((3 / 4 : ℝ)) ≤ (3 : ℝ) ^ ((1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  have hN34 : 0 < (N : ℝ) ^ ((3 / 4 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have : (N : ℝ) / 50 ≤ C * (3 * (N : ℝ) ^ ((3 / 4 : ℝ))) :=
    hlow.trans (hup.trans (mul_le_mul_of_nonneg_left (hrpow.trans h3) hC))
  rw [hsplitN] at this
  nlinarith

/-- **The Möbius gauge orbit.** The half-power law for `μ` holds at Haar-almost every gauge point,
fails at the Liouville twin, and holds at the gauge point `0` exactly under the Riemann
hypothesis. -/
theorem moebius_gauge_trichotomy :
    (∀ᵐ x ∂gaugeHaar, GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x) ∧
    (∃ x : GaugeTorus, ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x ∧
      ∀ n, n ≠ 0 → twist x n = (-1 : ℂ) ^ Ω n) ∧
    (GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) 0 ↔ RiemannHypothesis) := by
  refine ⟨ae_gaugeHalfPowerLaw _ fun n => ?_, ?_, gaugeHalfPowerLaw_moebius_zero_iff⟩
  · rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · obtain ⟨x, hx⟩ := exists_liouville_gaugePoint
    exact ⟨x, not_gaugeHalfPowerLaw_moebius_liouville hx, hx⟩

end GaloisForLFunctions.ArithmeticCorrelationGeometry
