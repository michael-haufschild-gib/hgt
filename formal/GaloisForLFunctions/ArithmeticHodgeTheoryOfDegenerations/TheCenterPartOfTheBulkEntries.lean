import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkEntriesAreReadByTheStieltjesConstants
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermIsDiagonalInTheRamanujanBasis
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HyperbolaSumsOfAVonMangoldtTail
import GaloisForLFunctions.ArithmeticElectrostatics.TheArithmeticPointCarriesTheDivergence
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasAnExactErrorDecomposition
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PeriodicPairSumsOfADecreasingKernelAreLinear
import GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair
import GaloisForLFunctions.RHTower.DiscreteVanDerCorput

/-!
# The center part of the bulk entries

At overlap `c` the complete Weil matrix carries the joint pole and archimedean center matrix
`Cen(n, j) = (α/N)(√(n/j) + √(j/n) − ω(|log(j/n)|))`, `α = c(∫φ)²/∫φ²` (RAPT). In pole gauge it is
rational (`centerPairing_eq`): for `n ≠ j`,
`Cen(n, j)/√(nj) = (α/N)(1/n + 1/j − ½(1/|n − j| + 1/(n + j)))`. Its second order on conductor
packets (`tendsto_centerPairing_sub`):

  `⟨Cen R_e, R_{e'}⟩ − [e = 1] α ⟨R_e, R_{e'}⟩ → C_α(e, e')`,

with `C_α(1, 1) = α(1 − log 2)`, `C_α(e, e) = αΛ(e)/φ(e)` and `C_α(e, 1) = −αΛ(e)/√φ(e)` for
`e ≥ 2`, and `0` otherwise (`centerSecondOrder`).

* The pole kernel reads `Σ_{n ≤ N} c_e(n) = [e = 1]N + O(1)` and `Σ_{n ≤ N} c_e(n)/n → −Λ(e)`.
* The difference kernel reads the autocorrelation `Σ_{r<M} c_{e'}(r) c_e(r + δ) = [e = e'] M c_e(δ)`
  (`tendsto_diffPairSum_sub`): `(1/N)Σ_{n ≠ j} c_{e'}(n)c_e(j)/|n − j| = 2[e = e'](Σ_{δ ≤ N} c_e(δ)/δ
  − (1/N)Σ_{δ ≤ N} c_e(δ)) + o(1)`.
* The sum kernel is `o(N)` unless `e = e' = 1`, where `(1/N)Σ_{n,j ≤ N} 1/(n + j) → 2 log 2`.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticFunction (vonMangoldt)
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence ArithmeticEffectivityTheory
  CompletedArithmeticForms

/-! ### Ramanujan sums -/

theorem ramTwist_eq_ramanujanLagCoefficient (m n : ℕ) :
    ramTwist m n = ramanujanLagCoefficient m n := by
  rw [ramTwist, Nat.sum_divisorsAntidiagonal'
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * (if b ∣ n then (b : ℝ) else 0)),
    ramanujanLagCoefficient]
  rfl

theorem ramanujanLagCoefficient_one (n : ℕ) : ramanujanLagCoefficient 1 n = 1 := by
  simp [ramanujanLagCoefficient, moebiusReal]

/-- The divisor sum `σ(e)` bounds every Ramanujan sum. -/
theorem abs_ramanujanLagCoefficient_le (e n : ℕ) :
    |ramanujanLagCoefficient e n| ≤ ∑ d ∈ e.divisors, (d : ℝ) := by
  unfold ramanujanLagCoefficient
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul]
  have h1 : |moebiusReal (e / d)| ≤ 1 := by
    unfold moebiusReal
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e / d)
  have h2 : |(if d ∣ n then (d : ℝ) else 0)| ≤ d := by
    split_ifs <;> simp
  calc |moebiusReal (e / d)| * |(if d ∣ n then (d : ℝ) else 0)| ≤ 1 * d :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = d := one_mul _

theorem ramanujanLagCoefficient_add_mul (e n k : ℕ) :
    ramanujanLagCoefficient e (n + e * k) = ramanujanLagCoefficient e n := by
  unfold ramanujanLagCoefficient
  refine Finset.sum_congr rfl fun d hd => ?_
  have hde : d ∣ e * k := (Nat.dvd_of_mem_divisors hd).mul_right k
  by_cases h : d ∣ n
  · rw [if_pos h, if_pos ((Nat.dvd_add_left hde).mpr h)]
  · rw [if_neg h, if_neg fun h' => h ((Nat.dvd_add_left hde).mp h')]

/-- The autocorrelation: `Σ_{r<M} c_{e'}(r) c_e(r + δ) = [e' = e] M c_{e'}(δ)`, `M = e' e`. -/
theorem sum_range_lag_mul_lag_add {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (δ : ℕ) :
    ∑ r ∈ range (e' * e), ramanujanLagCoefficient e' r * ramanujanLagCoefficient e (r + δ) =
      if e' = e then ((e' * e : ℕ) : ℝ) * ramanujanLagCoefficient e' δ else 0 := by
  have h := sum_ramTwist_mul_ramTwist_add he' he (dvd_mul_right e' e) (dvd_mul_left e e') δ
  simp only [ramTwist_eq_ramanujanLagCoefficient] at h
  exact h

/-- One period of `c_e` sums to `[e = 1]`. -/
theorem sum_range_ramanujanLagCoefficient {e : ℕ} (he : 0 < e) :
    ∑ r ∈ range e, ramanujanLagCoefficient e r = if e = 1 then 1 else 0 := by
  have h := sum_ramTwist_mul_ramTwist_add he one_pos (dvd_refl e) (one_dvd e) 0
  simp only [ramTwist_eq_ramanujanLagCoefficient, ramanujanLagCoefficient_one, mul_one,
    add_zero] at h
  rw [h]
  split_ifs with h1
  · subst h1; simp [ramanujanLagCoefficient_one]
  · rfl

/-- `C_N(e) = Σ_{n ≤ N} c_e(n)`. -/
def lagSum (e N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, ramanujanLagCoefficient e n

/-- `L_N(e) = Σ_{n ≤ N} c_e(n)/n`. -/
def lagHarmonic (e N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, ramanujanLagCoefficient e n / n

theorem lagSum_one (N : ℕ) : lagSum 1 N = N := by
  simp [lagSum, ramanujanLagCoefficient_one]

theorem lagHarmonic_one (N : ℕ) : lagHarmonic 1 N = harmonic N := by
  rw [lagHarmonic, harmonic_eq_sum_Icc_real]
  simp [ramanujanLagCoefficient_one, one_div]

/-- For `e ≥ 2` the partial sums of `c_e` are bounded. -/
theorem abs_lagSum_le {e : ℕ} (he : 2 ≤ e) (N : ℕ) :
    |lagSum e N| ≤ (2 * e + 1) * ∑ d ∈ e.divisors, (d : ℝ) := by
  set σ : ℝ := ∑ d ∈ e.divisors, (d : ℝ)
  have hper : ∀ i, ramanujanLagCoefficient e (i + e) = ramanujanLagCoefficient e i := fun i => by
    simpa using ramanujanLagCoefficient_add_mul e i 1
  have h := abs_sum_range_sub_mul_mean_le (by omega : 1 ≤ e) (ramanujanLagCoefficient e) hper
    (abs_ramanujanLagCoefficient_le e) (N + 1)
  rw [sum_range_ramanujanLagCoefficient (by omega), if_neg (by omega), zero_div, mul_zero,
    sub_zero] at h
  have hs : lagSum e N = ∑ i ∈ range (N + 1), ramanujanLagCoefficient e i -
      ramanujanLagCoefficient e 0 := by
    rw [lagSum, ← sum_range_succ_eq_sum_Icc, Finset.sum_range_succ']
    ring
  rw [hs]
  have h0 := abs_ramanujanLagCoefficient_le e 0
  calc |∑ i ∈ range (N + 1), ramanujanLagCoefficient e i - ramanujanLagCoefficient e 0|
      ≤ |∑ i ∈ range (N + 1), ramanujanLagCoefficient e i| + |ramanujanLagCoefficient e 0| :=
        abs_sub _ _
    _ ≤ 2 * e * σ + σ := add_le_add h h0
    _ = (2 * e + 1) * σ := by ring

/-- `Σ_{n ≤ N} c_e(n)/n → −Λ(e)` for `e ≥ 2`. -/
theorem tendsto_lagHarmonic {e : ℕ} (he : 2 ≤ e) :
    Tendsto (lagHarmonic e) atTop (𝓝 (-vonMangoldt e)) := by
  have hlim : Tendsto (fun N : ℕ => doubleMoebius 1 e (fun d t =>
      (Nat.gcd d t : ℝ) * harmonicFloorError N (Nat.lcm d t))) atTop (𝓝 0) :=
    tendsto_doubleMoebius_zero fun d hd t ht => by
      have hL : 0 < Nat.lcm d t :=
        Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors ht)
      have := (tendsto_harmonicFloorError hL).const_mul (Nat.gcd d t : ℝ)
      rwa [mul_zero] at this
  have h2 := hlim.const_add (-vonMangoldt e)
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop e] with N hN
  have h := sum_ramanujanLagCoefficient_mul_div_eq one_pos (by omega : 0 < e)
    (by omega : 1 * e ≤ N)
  rw [if_neg (by omega), ArithmeticElectrostatics.orbitIntersection_one_left he] at h
  simp only [ramanujanLagCoefficient_one, one_mul] at h
  rw [lagHarmonic, h]
  ring

/-! ### Pair sums against the difference and sum kernels -/

/-- The triangle `n < j` reindexed by the gap `δ = j − n`. -/
theorem sum_sum_ite_lt (g : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (if n < j then g n j else 0) =
      ∑ δ ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - δ), g n (n + δ) := by
  have h1 : ∀ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (if n < j then g n j else 0) =
      ∑ δ ∈ Icc 1 (N - n), g n (n + δ) := fun n _ => by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun j => j - n) (fun δ => n + δ) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      omega
    · intro δ hδ
      simp only [Finset.mem_filter, Finset.mem_Icc] at hδ ⊢
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      omega
    · intro δ _
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      congr 1
      omega
  rw [Finset.sum_congr rfl h1]
  exact Finset.sum_comm' fun n δ => by simp only [Finset.mem_Icc]; omega

/-- The difference-kernel pair sum `Σ_{n ≠ j} u(n) v(j)/|n − j|`. -/
def diffPairSum (u v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, u n * v j * (if n = j then 0 else 1 / |(n : ℝ) - j|)

/-- The sum-kernel pair sum `Σ_{n ≠ j} u(n) v(j)/(n + j)`. -/
def sumPairSum (u v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, u n * v j * (if n = j then 0 else 1 / ((n : ℝ) + j))

/-- The difference kernel by gaps: `Σ_{δ ≤ N} (1/δ) Σ_{n ≤ N − δ} (u(n)v(n+δ) + u(n+δ)v(n))`. -/
theorem diffPairSum_eq (u v : ℕ → ℝ) (N : ℕ) :
    diffPairSum u v N = ∑ δ ∈ Icc 1 N, (1 / (δ : ℝ)) *
      ∑ n ∈ Icc 1 (N - δ), (u n * v (n + δ) + u (n + δ) * v n) := by
  have hsplit : ∀ n j : ℕ, u n * v j * (if n = j then 0 else 1 / |(n : ℝ) - j|) =
      (if n < j then u n * v j / ((j : ℝ) - n) else 0) +
        (if j < n then u n * v j / ((n : ℝ) - j) else 0) := fun n j => by
    rcases lt_trichotomy n j with h | h | h
    · have hR : (n : ℝ) < j := by exact_mod_cast h
      rw [if_neg h.ne, if_pos h, if_neg (by omega), abs_of_neg (by linarith), neg_sub]
      ring
    · subst h; simp
    · have hR : (j : ℝ) < n := by exact_mod_cast h
      rw [if_neg h.ne', if_neg (by omega), if_pos h, abs_of_pos (by linarith)]
      ring
  calc diffPairSum u v N
      = ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ((if n < j then u n * v j / ((j : ℝ) - n) else 0) +
          (if j < n then u n * v j / ((n : ℝ) - j) else 0)) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => hsplit n j
    _ = ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (if n < j then u n * v j / ((j : ℝ) - n) else 0) +
          ∑ j ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if j < n then u n * v j / ((n : ℝ) - j) else 0) := by
        rw [Finset.sum_comm (s := Icc 1 N) (t := Icc 1 N)
          (f := fun j n => if j < n then u n * v j / ((n : ℝ) - j) else 0)]
        simp only [Finset.sum_add_distrib]
    _ = ∑ δ ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - δ), u n * v (n + δ) / (((n + δ : ℕ) : ℝ) - n) +
          ∑ δ ∈ Icc 1 N, ∑ j ∈ Icc 1 (N - δ), u (j + δ) * v j / (((j + δ : ℕ) : ℝ) - j) := by
        rw [sum_sum_ite_lt (fun n j => u n * v j / ((j : ℝ) - n)) N,
          sum_sum_ite_lt (fun j n => u n * v j / ((n : ℝ) - j)) N]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun δ hδ => ?_
        have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast (show δ ≠ 0 by simp at hδ; omega)
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        push_cast
        ring

/-- The mean of a gap row: `Σ_{n ≤ L} (c_{e'}(n)c_e(n+δ) + c_{e'}(n+δ)c_e(n))` is `2L[e = e']c_e(δ)`
up to a uniform constant. -/
theorem abs_gapRow_sub_le {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (δ L : ℕ) :
    |∑ n ∈ Icc 1 L, (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + δ) +
        ramanujanLagCoefficient e' (n + δ) * ramanujanLagCoefficient e n) -
      L * (2 * (if e = e' then ramanujanLagCoefficient e δ else 0))| ≤
      2 * (e' * e : ℕ) * (2 * (∑ d ∈ e'.divisors, (d : ℝ)) * ∑ d ∈ e.divisors, (d : ℝ)) := by
  set M := e' * e with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hP1 : ∀ n, ramanujanLagCoefficient e' (n + M) = ramanujanLagCoefficient e' n :=
    fun n => ramanujanLagCoefficient_add_mul e' n e
  have hP2 : ∀ n, ramanujanLagCoefficient e (n + M) = ramanujanLagCoefficient e n := fun n => by
    rw [hM, mul_comm]; exact ramanujanLagCoefficient_add_mul e n e'
  set w : ℕ → ℝ := fun i => ramanujanLagCoefficient e' i * ramanujanLagCoefficient e (i + δ) +
    ramanujanLagCoefficient e' (i + δ) * ramanujanLagCoefficient e i with hw
  have hperw : ∀ i, w (i + M) = w i := fun i => by
    simp only [hw]
    rw [show i + M + δ = i + δ + M by ring]
    simp only [hP1, hP2]
  have hper : ∀ i, w (i + M + 1) = w (i + 1) := fun i => by
    rw [show i + M + 1 = i + 1 + M by ring]; exact hperw (i + 1)
  have hbound : ∀ i, |w (i + 1)| ≤ 2 * (∑ d ∈ e'.divisors, (d : ℝ)) * ∑ d ∈ e.divisors, (d : ℝ) :=
    fun i => by
      simp only [hw]
      have a1 := abs_ramanujanLagCoefficient_le e' (i + 1)
      have a2 := abs_ramanujanLagCoefficient_le e (i + 1 + δ)
      have a3 := abs_ramanujanLagCoefficient_le e' (i + 1 + δ)
      have a4 := abs_ramanujanLagCoefficient_le e (i + 1)
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have b1 := mul_le_mul a1 a2 (abs_nonneg _) ((abs_nonneg _).trans a1)
      have b2 := mul_le_mul a3 a4 (abs_nonneg _) ((abs_nonneg _).trans a3)
      linarith
  have h := abs_sum_range_sub_mul_mean_le hM1 (fun i => w (i + 1)) hper hbound L
  -- the mean over a period
  have hmean : (∑ i ∈ range M, w (i + 1)) / M =
      2 * (if e = e' then ramanujanLagCoefficient e δ else 0) := by
    have hshift := sum_range_shift_of_periodic w hperw 1
    simp only [add_comm 1] at hshift
    rw [hshift]
    simp only [hw, Finset.sum_add_distrib]
    rw [sum_range_lag_mul_lag_add he he' δ]
    have h2 := sum_range_lag_mul_lag_add he' he δ
    rw [show ∑ i ∈ range M, ramanujanLagCoefficient e' (i + δ) * ramanujanLagCoefficient e i =
      ∑ i ∈ range (e * e'), ramanujanLagCoefficient e i * ramanujanLagCoefficient e' (i + δ) by
        rw [hM, mul_comm e' e]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _, h2]
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    by_cases hee : e = e'
    · subst hee
      simp only [if_true]
      rw [show ((e * e : ℕ) : ℝ) = (M : ℝ) by rw [hM]]
      field_simp
      ring
    · rw [if_neg (Ne.symm hee), if_neg hee, if_neg hee]; simp
  rw [hmean] at h
  rw [← sum_range_succ_eq_sum_Icc (fun n => ramanujanLagCoefficient e' n *
    ramanujanLagCoefficient e (n + δ) + ramanujanLagCoefficient e' (n + δ) *
      ramanujanLagCoefficient e n)]
  exact h

theorem tendsto_harmonic_div_self : Tendsto (fun N : ℕ => (harmonic N : ℝ) / N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (1 + Real.log N) / N) atTop (𝓝 0) := by
    have ha := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    have hb := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have := ha.add hb
    rw [add_zero] at this
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    ring
  refine squeeze_zero (fun N => div_nonneg (by
      rw [harmonic_eq_sum_Icc_real]; exact Finset.sum_nonneg fun i _ => by positivity)
      (Nat.cast_nonneg _))
    (fun N => div_le_div_of_nonneg_right (harmonic_le_one_add_log N) (Nat.cast_nonneg _)) h1

/-- **The difference kernel**: `(1/N) diffPairSum − 2[e = e'](L_N(e) − C_N(e)/N) → 0`. -/
theorem tendsto_diffPairSum_sub {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ => diffPairSum (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) N / N -
      2 * (if e = e' then lagHarmonic e N - lagSum e N / N else 0)) atTop (𝓝 0) := by
  set K : ℝ := 2 * (e' * e : ℕ) * (2 * (∑ d ∈ e'.divisors, (d : ℝ)) * ∑ d ∈ e.divisors, (d : ℝ))
  have hK : 0 ≤ K := by positivity
  have hmaj := tendsto_harmonic_div_self.const_mul K
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℕ → ℝ := fun δ => if e = e' then ramanujanLagCoefficient e δ else 0 with ha
  set E : ℕ → ℝ := fun δ => ∑ n ∈ Icc 1 (N - δ), (ramanujanLagCoefficient e' n *
      ramanujanLagCoefficient e (n + δ) + ramanujanLagCoefficient e' (n + δ) *
        ramanujanLagCoefficient e n) - ((N - δ : ℕ) : ℝ) * (2 * a δ) with hE
  have hEb : ∀ δ, |E δ| ≤ K := fun δ => abs_gapRow_sub_le he he' δ (N - δ)
  have hmain : 2 * (if e = e' then lagHarmonic e N - lagSum e N / N else 0) =
      (∑ δ ∈ Icc 1 N, (1 / (δ : ℝ)) * (((N - δ : ℕ) : ℝ) * (2 * a δ))) / N := by
    have e1 : ∀ δ ∈ Icc 1 N, (1 / (δ : ℝ)) * (((N - δ : ℕ) : ℝ) * (2 * a δ)) =
        2 * (N * (a δ / δ) - a δ) := fun δ hδ => by
      have hδ1 : 1 ≤ δ := (Finset.mem_Icc.mp hδ).1
      have hδN : δ ≤ N := (Finset.mem_Icc.mp hδ).2
      have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
      rw [Nat.cast_sub hδN]
      field_simp
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    by_cases hee : e = e'
    · simp only [ha, if_pos hee, lagHarmonic, lagSum]
      field_simp
    · simp only [ha, if_neg hee, zero_div, Finset.sum_const_zero, mul_zero, sub_zero]
  rw [hmain, diffPairSum_eq, ← sub_div]
  have hsplit : ∑ δ ∈ Icc 1 N, (1 / (δ : ℝ)) * ∑ n ∈ Icc 1 (N - δ),
      (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + δ) +
        ramanujanLagCoefficient e' (n + δ) * ramanujanLagCoefficient e n) -
      ∑ δ ∈ Icc 1 N, (1 / (δ : ℝ)) * (((N - δ : ℕ) : ℝ) * (2 * a δ)) =
      ∑ δ ∈ Icc 1 N, (1 / (δ : ℝ)) * E δ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun δ _ => ?_
    simp only [hE]
    ring
  rw [hsplit, Real.norm_eq_abs, abs_div, abs_of_pos hN0, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hN0.le
  rw [harmonic_eq_sum_Icc_real, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun δ hδ => ?_)
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast (Finset.mem_Icc.mp hδ).1
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / δ), one_div, mul_comm]
  exact mul_le_mul_of_nonneg_right (hEb δ) (by positivity)

/-! ### The sum kernel -/

theorem sum_mul_ite_eq_sub (f g : ℕ → ℝ) {n N : ℕ} (hn : n ∈ Icc 1 N) :
    ∑ j ∈ Icc 1 N, f j * (if n = j then 0 else g j) = ∑ j ∈ Icc 1 N, f j * g j - f n * g n := by
  have : ∀ j, f j * (if n = j then 0 else g j) = f j * g j - (if n = j then f j * g j else 0) :=
    fun j => by split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos hn]

/-- Abel: `|Σ_{j ≤ N} v(j)/(n + j)| ≤ B/(n + 1)` for partial sums of `v` bounded by `B`. -/
theorem abs_sum_div_add_le {v : ℕ → ℝ} {B : ℝ} (hB : ∀ k, |∑ i ∈ range k, v (i + 1)| ≤ B)
    (n N : ℕ) : |∑ j ∈ Icc 1 N, v j / ((n : ℝ) + j)| ≤ B / (n + 1) := by
  have hanti : Antitone fun m : ℕ => 1 / ((n : ℝ) + m + 1) := fun a b hab => by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have h := RHTower.norm_sum_amplitude_phase_le hanti (fun m => by positivity)
    (b := fun m => (v (m + 1) : ℂ)) (M := B) (fun k => by
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]; exact hB k) N
  rw [← sum_range_succ_eq_sum_Icc]
  have e : ∑ m ∈ range N, ((1 / ((n : ℝ) + m + 1) : ℝ) : ℂ) * (v (m + 1) : ℂ) =
      ((∑ i ∈ range N, v (i + 1) / ((n : ℝ) + (i + 1 : ℕ)) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  simpa [div_eq_inv_mul] using h

/-- The sum kernel against bounded weights with bounded partial sums is `O(log N)`. -/
theorem abs_sumPairSum_le (u v : ℕ → ℝ) {B U V : ℝ}
    (hB : ∀ k, |∑ i ∈ range k, v (i + 1)| ≤ B) (hU : ∀ n, |u n| ≤ U) (hV : ∀ n, |v n| ≤ V)
    (N : ℕ) : |sumPairSum u v N| ≤ U * (B + V) * harmonic N := by
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  unfold sumPairSum
  rw [harmonic_eq_sum_Icc_real, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have e : ∑ j ∈ Icc 1 N, u n * v j * (if n = j then 0 else 1 / ((n : ℝ) + j)) =
      u n * (∑ j ∈ Icc 1 N, v j / ((n : ℝ) + j) - v n * (1 / ((n : ℝ) + n))) := by
    rw [show (∑ j ∈ Icc 1 N, u n * v j * (if n = j then 0 else 1 / ((n : ℝ) + j))) =
      u n * ∑ j ∈ Icc 1 N, v j * (if n = j then 0 else 1 / ((n : ℝ) + j)) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    rw [sum_mul_ite_eq_sub v (fun j => 1 / ((n : ℝ) + j)) hn]
    simp only [mul_one_div]
  rw [e, abs_mul]
  have h1 := abs_sum_div_add_le hB n N
  have h2 : |v n * (1 / ((n : ℝ) + n))| ≤ V / n := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + n))]
    calc |v n| * (1 / ((n : ℝ) + n)) ≤ V * (1 / n) :=
          mul_le_mul (hV n) (one_div_le_one_div_of_le (by positivity) (by linarith))
            (by positivity) hV0
      _ = V / n := by ring
  have h3 : B / (n + 1) ≤ B / n := div_le_div_of_nonneg_left hB0 (by positivity) (by linarith)
  calc |u n| * |∑ j ∈ Icc 1 N, v j / ((n : ℝ) + j) - v n * (1 / ((n : ℝ) + n))|
      ≤ U * (B / n + V / n) :=
        mul_le_mul (hU n) ((abs_sub _ _).trans (add_le_add (h1.trans h3) h2))
          (abs_nonneg _) hU0
    _ = U * (B + V) * (n : ℝ)⁻¹ := by field_simp

theorem sumPairSum_comm (u v : ℕ → ℝ) (N : ℕ) : sumPairSum u v N = sumPairSum v u N := by
  unfold sumPairSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = n
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

/-- The full sum kernel `S(N) = Σ_{n, j ≤ N} 1/(n + j)`. -/
def sumKernelTotal (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, 1 / ((n : ℝ) + j)

theorem sum_Icc_inv_add_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, 1 / ((n : ℝ) + (N + 1)) = harmonic (2 * N + 1) - harmonic (N + 1) := by
  have h1 : (harmonic (2 * N + 1) : ℝ) = ∑ k ∈ Ioc 0 (N + 1), (k : ℝ)⁻¹ +
      ∑ k ∈ Ioc (N + 1) (2 * N + 1), (k : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc_real, Icc_one_eq_Ioc_zero,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)]
  have h2 : (harmonic (N + 1) : ℝ) = ∑ k ∈ Ioc 0 (N + 1), (k : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc_real, Icc_one_eq_Ioc_zero]
  rw [h1, h2, add_sub_cancel_left]
  refine Finset.sum_nbij' (fun n => n + (N + 1)) (fun k => k - (N + 1)) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk ⊢; omega
  · intro n _; omega
  · intro k hk; simp only [Finset.mem_Ioc] at hk; omega
  · intro n _; push_cast; ring

theorem sumKernelTotal_succ (N : ℕ) :
    sumKernelTotal (N + 1) - sumKernelTotal N =
      2 * (harmonic (2 * N + 1) - harmonic (N + 1) : ℝ) + 1 / (2 * ((N : ℝ) + 1)) := by
  unfold sumKernelTotal
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp only [Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega)]
  rw [Finset.sum_add_distrib, ← sum_Icc_inv_add_eq N]
  have e : ∑ j ∈ Icc 1 N, 1 / (((N + 1 : ℕ) : ℝ) + j) = ∑ n ∈ Icc 1 N, 1 / ((n : ℝ) + (N + 1)) :=
    Finset.sum_congr rfl fun j _ => by push_cast; ring_nf
  rw [e]
  push_cast
  ring

/-- `(1/N) Σ_{n, j ≤ N} 1/(n + j) → 2 log 2`. -/
theorem tendsto_sumKernelTotal_div :
    Tendsto (fun N : ℕ => sumKernelTotal N / N) atTop (𝓝 (2 * Real.log 2)) := by
  have hΔ : Tendsto (fun N : ℕ => sumKernelTotal (N + 1) - sumKernelTotal N) atTop
      (𝓝 (2 * Real.log 2)) := by
    have h1 := GaloisForLFunctions.HTGeometry.tendsto_harmonic_two_mul_sub_harmonic
    have h2 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    have hsucc : ∀ N : ℕ, (harmonic (2 * N + 1) - harmonic (N + 1) : ℝ) =
        (harmonic (2 * N) - harmonic N : ℝ) + 1 / (2 * (N : ℝ) + 1) - 1 / ((N : ℝ) + 1) := by
      intro N
      rw [harmonic_succ, harmonic_succ]
      push_cast
      ring
    have h3 : Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ) + 1)) atTop (𝓝 0) := by
      refine squeeze_zero (fun N => by positivity) (fun N => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h4 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h5 : Tendsto (fun N : ℕ => 1 / (2 * ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have := h4.const_mul (1 / 2)
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      field_simp
    have := ((((h1.add h3).sub h4).const_mul 2).add h5)
    simp only [add_zero, sub_zero] at this
    refine this.congr fun N => ?_
    rw [sumKernelTotal_succ, hsucc]
  have hc := hΔ.cesaro
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsum : ∑ i ∈ range N, (sumKernelTotal (i + 1) - sumKernelTotal i) = sumKernelTotal N := by
    rw [Finset.sum_range_sub]
    simp [sumKernelTotal]
  rw [hsum, inv_mul_eq_div]

theorem sum_ite_eq_zero_sub (g : ℕ → ℝ) {n N : ℕ} (hn : n ∈ Icc 1 N) :
    ∑ j ∈ Icc 1 N, (if n = j then 0 else g j) = ∑ j ∈ Icc 1 N, g j - g n := by
  have := sum_mul_ite_eq_sub (fun _ => (1 : ℝ)) g hn
  simpa using this

theorem sumPairSum_one (N : ℕ) :
    sumPairSum (fun _ => 1) (fun _ => 1) N = sumKernelTotal N - harmonic N / 2 := by
  unfold sumPairSum sumKernelTotal
  rw [harmonic_eq_sum_Icc_real, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [one_mul]
  rw [sum_ite_eq_zero_sub (fun j => 1 / ((n : ℝ) + j)) hn]
  ring

/-! ### The center pairing in pole gauge -/

/-- The center kernel in pole gauge: `1/n + 1/j − [n ≠ j] ½ (1/|n − j| + 1/(n + j))`. -/
def centerKernel (n j : ℕ) : ℝ :=
  1 / n + 1 / j - (if n = j then 0 else 1 / 2 * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)))

theorem centerKernel_eq {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    (arithmeticPoleKernel n j - archimedeanCenterKernel n j) / (Real.sqrt n * Real.sqrt j) =
      centerKernel n j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hpole : arithmeticPoleKernel n j / (Real.sqrt n * Real.sqrt j) = 1 / n + 1 / j := by
    unfold arithmeticPoleKernel
    obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt n = r := ⟨_, Real.sqrt_pos.mpr hn0, rfl⟩
    obtain ⟨t, ht0, ht⟩ : ∃ t, 0 < t ∧ Real.sqrt j = t := ⟨_, Real.sqrt_pos.mpr hj0, rfl⟩
    have hnr : (n : ℝ) = r ^ 2 := by rw [← hr, Real.sq_sqrt hn0.le]
    have hjt : (j : ℝ) = t ^ 2 := by rw [← ht, Real.sq_sqrt hj0.le]
    have hr0' := hr0.ne'
    have ht0' := ht0.ne'
    rw [hr, ht, hnr, hjt]
    field_simp
    ring
  rw [sub_div, hpole, centerKernel]
  by_cases h : n = j
  · subst h
    rw [archimedeanCenterKernel_self, zero_div, if_pos rfl]
  · rw [archimedeanCenterKernel_div_sqrt_mul hn hj h, if_neg h]

/-- **The center pairing in pole gauge**:
`⟨Cen R_e, R_{e'}⟩ = (α/N)/√(φ(e)φ(e')) · Σ_{n, j ≤ N} c_{e'}(n) c_e(j) κ(n, j)`. -/
theorem centerPairing_eq (α : ℝ) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (N : ℕ) :
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (ramanujanHorizonVector e N),
      ramanujanHorizonVector e' N⟫ =
      α / N / (Real.sqrt e.totient * Real.sqrt e'.totient) *
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j * centerKernel n j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile e' n *
    ∑ j : PrimeHorizonIndex N, (α / N * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) *
      ramanujanPoleProfile e j = _
  rw [Finset.sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile e' n *
    ∑ j : PrimeHorizonIndex N, (α / N * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) *
      ramanujanPoleProfile e j)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_coe_sort (Icc 1 N) (fun j => (α / N * (arithmeticPoleKernel n j -
    archimedeanCenterKernel n j)) * ramanujanPoleProfile e j), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ramanujanPoleProfile_eq he, ramanujanPoleProfile_eq he',
    ← centerKernel_eq (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hj).1]
  ring

/-- The center sum split into its pole, difference and sum kernels. -/
theorem sum_centerKernel_eq (e e' N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j * centerKernel n j =
      lagHarmonic e' N * lagSum e N + lagSum e' N * lagHarmonic e N -
        1 / 2 * diffPairSum (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) N -
        1 / 2 * sumPairSum (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) N := by
  unfold lagHarmonic lagSum diffPairSum sumPairSum
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold centerKernel
  split_ifs <;> ring

/-! ### The limits -/

/-- The center coefficient `K(e, e')`: the limit of `(1/N)Σ c_{e'}c_e κ − [e = 1] L_N(e')`. -/
def centerLimitCoeff (e e' : ℕ) : ℝ :=
  if e = 1 ∧ e' = 1 then 1 - Real.log 2
  else if e = e' then vonMangoldt e
  else if e' = 1 then -vonMangoldt e else 0

theorem abs_lagSum_one_add_le {e : ℕ} (he : 2 ≤ e) (k : ℕ) :
    |∑ i ∈ range k, ramanujanLagCoefficient e (i + 1)| ≤ (2 * e + 1) * ∑ d ∈ e.divisors, (d : ℝ) := by
  rw [sum_range_succ_eq_sum_Icc]; exact abs_lagSum_le he k

/-- The sum kernel is `o(N)` unless both conductors are `1`. -/
theorem tendsto_sumPairSum_div {e e' : ℕ} (h : 2 ≤ e ∨ 2 ≤ e') :
    Tendsto (fun N : ℕ =>
      sumPairSum (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) N / N) atTop (𝓝 0) := by
  set σ : ℝ := ∑ d ∈ e.divisors, (d : ℝ)
  set σ' : ℝ := ∑ d ∈ e'.divisors, (d : ℝ)
  have hσ : 0 ≤ σ := by positivity
  have hσ' : 0 ≤ σ' := by positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ N, |sumPairSum (ramanujanLagCoefficient e')
      (ramanujanLagCoefficient e) N| ≤ C * harmonic N := by
    rcases h with h | h
    · exact ⟨σ' * ((2 * e + 1) * σ + σ), abs_sumPairSum_le _ _ (abs_lagSum_one_add_le h)
        (abs_ramanujanLagCoefficient_le e') (abs_ramanujanLagCoefficient_le e)⟩
    · refine ⟨σ * ((2 * e' + 1) * σ' + σ'), fun N => ?_⟩
      rw [sumPairSum_comm]
      exact abs_sumPairSum_le _ _ (abs_lagSum_one_add_le h) (abs_ramanujanLagCoefficient_le e)
        (abs_ramanujanLagCoefficient_le e') N
  have hmaj := tendsto_harmonic_div_self.const_mul C
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, mul_div_assoc']
  exact div_le_div_of_nonneg_right (hC N) (Nat.cast_nonneg _)

theorem tendsto_bdd_mul_harmonic_div {f : ℕ → ℝ} {B : ℝ} (hf : ∀ N, |f N| ≤ B) :
    Tendsto (fun N : ℕ => f N * harmonic N / N) atTop (𝓝 0) := by
  have hmaj := tendsto_harmonic_div_self.const_mul B
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm (fun N => ?_) hmaj
  have hH : (0 : ℝ) ≤ harmonic N := by
    rw [harmonic_eq_sum_Icc_real]; exact Finset.sum_nonneg fun i _ => by positivity
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast, abs_of_nonneg hH, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (hf N) (div_nonneg hH (Nat.cast_nonneg _))

theorem tendsto_bdd_mul_bdd_div {f g : ℕ → ℝ} {A B : ℝ} (hf : ∀ N, |f N| ≤ A)
    (hg : ∀ N, |g N| ≤ B) : Tendsto (fun N : ℕ => f N * g N / N) atTop (𝓝 0) := by
  have hmaj := (tendsto_const_div_atTop_nhds_zero_nat (A * B))
  refine squeeze_zero_norm (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact mul_le_mul (hf N) (hg N) (abs_nonneg _) ((abs_nonneg _).trans (hf 0))

theorem exists_abs_lagHarmonic_le {e : ℕ} (he : 2 ≤ e) : ∃ B, ∀ N, |lagHarmonic e N| ≤ B := by
  obtain ⟨B, hB⟩ := (tendsto_lagHarmonic he).abs.bddAbove_range
  exact ⟨B, fun N => hB ⟨N, rfl⟩⟩

/-- **The center limit**: `(1/N)Σ c_{e'}(n)c_e(j)κ(n, j) − [e = 1] L_N(e') → K(e, e')`. -/
theorem tendsto_centerSum_sub {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j * centerKernel n j) / N -
      (if e = 1 then lagHarmonic e' N else 0)) atTop (𝓝 (centerLimitCoeff e e')) := by
  simp only [sum_centerKernel_eq]
  have hdiff := tendsto_diffPairSum_sub he he'
  rcases Nat.lt_or_ge e 2 with he2 | he2 <;> rcases Nat.lt_or_ge e' 2 with he2' | he2'
  · -- `e = e' = 1`
    obtain rfl : e = 1 := by omega
    obtain rfl : e' = 1 := by omega
    have hc : ramanujanLagCoefficient 1 = fun _ => 1 := funext ramanujanLagCoefficient_one
    have hS : Tendsto (fun N : ℕ => sumPairSum (ramanujanLagCoefficient 1)
        (ramanujanLagCoefficient 1) N / N) atTop (𝓝 (2 * Real.log 2)) := by
      have h1 := tendsto_sumKernelTotal_div.sub (tendsto_harmonic_div_self.div_const 2)
      rw [zero_div, sub_zero] at h1
      refine h1.congr fun N => ?_
      rw [hc, sumPairSum_one]
      ring
    simp only [ite_true, lagHarmonic_one, lagSum_one] at hdiff
    have htot := ((hdiff.const_mul (-(1 / 2))).add (hS.const_mul (-(1 / 2)))).const_add 1
    rw [show (1 : ℝ) + (-(1 / 2) * 0 + -(1 / 2) * (2 * Real.log 2)) = centerLimitCoeff 1 1 by
      simp [centerLimitCoeff]; ring] at htot
    refine htot.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp only [ite_true, lagHarmonic_one, lagSum_one]
    field_simp
    ring
  · -- `e = 1`, `e' ≥ 2`
    obtain rfl : e = 1 := by omega
    have hne : (1 : ℕ) ≠ e' := by omega
    simp only [if_neg hne, mul_zero, sub_zero] at hdiff
    have hS := tendsto_sumPairSum_div (e := 1) (e' := e') (Or.inr he2')
    have hL := tendsto_bdd_mul_harmonic_div (abs_lagSum_le he2')
    have htot := (hL.sub (hdiff.const_mul (1 / 2))).sub (hS.const_mul (1 / 2))
    rw [show (0 : ℝ) - 1 / 2 * 0 - 1 / 2 * 0 = centerLimitCoeff 1 e' by
      simp [centerLimitCoeff, Ne.symm hne]] at htot
    refine htot.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp only [ite_true, lagHarmonic_one, lagSum_one]
    field_simp
    ring
  · -- `e ≥ 2`, `e' = 1`
    obtain rfl : e' = 1 := by omega
    have hne : e ≠ 1 := by omega
    simp only [if_neg hne, mul_zero, sub_zero] at hdiff
    have hS := tendsto_sumPairSum_div (e := e) (e' := 1) (Or.inl he2)
    have hL := tendsto_bdd_mul_harmonic_div (abs_lagSum_le he2)
    have hH := tendsto_lagHarmonic he2
    have htot := ((hL.add hH).sub (hdiff.const_mul (1 / 2))).sub (hS.const_mul (1 / 2))
    rw [show (0 : ℝ) + -vonMangoldt e - 1 / 2 * 0 - 1 / 2 * 0 = centerLimitCoeff e 1 by
      simp [centerLimitCoeff, hne]] at htot
    refine htot.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp only [if_neg hne, lagHarmonic_one, lagSum_one, sub_zero]
    field_simp
  · -- `e, e' ≥ 2`
    have hS := tendsto_sumPairSum_div (e := e) (e' := e') (Or.inl he2)
    obtain ⟨A, hA⟩ := exists_abs_lagHarmonic_le he2
    obtain ⟨A', hA'⟩ := exists_abs_lagHarmonic_le he2'
    have h1 := tendsto_bdd_mul_bdd_div hA' (abs_lagSum_le he2)
    have h2 := tendsto_bdd_mul_bdd_div (abs_lagSum_le he2') hA
    have hne : e ≠ 1 := by omega
    -- the difference kernel
    have hD : Tendsto (fun N : ℕ => diffPairSum (ramanujanLagCoefficient e')
        (ramanujanLagCoefficient e) N / N) atTop
        (𝓝 (2 * (if e = e' then -vonMangoldt e else 0))) := by
      by_cases hee : e = e'
      · subst hee
        simp only [ite_true] at hdiff ⊢
        have hm := ((tendsto_lagHarmonic he2).sub
          (tendsto_bdd_mul_bdd_div (f := fun _ => (1 : ℝ)) (A := 1) (fun _ => by simp)
            (abs_lagSum_le he2))).const_mul 2
        rw [sub_zero] at hm
        have := hdiff.add hm
        rw [zero_add] at this
        refine this.congr fun N => ?_
        simp only [one_mul]
        ring
      · simp only [if_neg hee, mul_zero, sub_zero] at hdiff ⊢
        exact hdiff
    have htot := ((h1.add h2).sub (hD.const_mul (1 / 2))).sub (hS.const_mul (1 / 2))
    have hc1 : ¬(e = 1 ∧ e' = 1) := fun h => absurd h.1 hne
    have hc2 : e' ≠ 1 := by omega
    rw [show (0 : ℝ) + 0 - 1 / 2 * (2 * (if e = e' then -vonMangoldt e else 0)) - 1 / 2 * 0 =
      centerLimitCoeff e e' by
        unfold centerLimitCoeff
        rw [if_neg hc1]
        by_cases hee : e = e'
        · rw [if_pos hee, if_pos hee]; ring
        · rw [if_neg hee, if_neg hee, if_neg hc2]; ring] at htot
    refine htot.congr fun N => ?_
    simp only [if_neg hne, sub_zero]
    ring

/-- The center second order `C_α(e, e') = α K(e, e')/√(φ(e)φ(e'))`. -/
def centerSecondOrder (α : ℝ) (e e' : ℕ) : ℝ :=
  α * centerLimitCoeff e e' / (Real.sqrt e.totient * Real.sqrt e'.totient)

/-- **The center part of the bulk entries**:
`⟨Cen R_e, R_{e'}⟩ − [e = 1] α ⟨R_e, R_{e'}⟩ → C_α(e, e')`. -/
theorem tendsto_centerPairing_sub (α : ℝ) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        (if e = 1 then α else 0) * ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫)
      atTop (𝓝 (centerSecondOrder α e e')) := by
  have h := (tendsto_centerSum_sub he he').const_mul
    (α / (Real.sqrt e.totient * Real.sqrt e'.totient))
  rw [show α / (Real.sqrt e.totient * Real.sqrt e'.totient) * centerLimitCoeff e e' =
    centerSecondOrder α e e' by unfold centerSecondOrder; ring] at h
  refine h.congr fun N => ?_
  rw [centerPairing_eq α he he', inner_ramanujanHorizonVector_eq he he']
  by_cases he1 : e = 1
  · subst he1
    simp only [ite_true, ramanujanLagCoefficient_one, one_mul, lagHarmonic]
    ring
  · simp only [if_neg he1, zero_mul, sub_zero]
    ring

theorem centerSecondOrder_one_one (α : ℝ) : centerSecondOrder α 1 1 = α * (1 - Real.log 2) := by
  simp [centerSecondOrder, centerLimitCoeff]

theorem centerSecondOrder_self {e : ℕ} (he : 2 ≤ e) (α : ℝ) :
    centerSecondOrder α e e = α * vonMangoldt e / e.totient := by
  have hφ : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  unfold centerSecondOrder centerLimitCoeff
  rw [if_neg (fun h : e = 1 ∧ e = 1 => absurd h.1 (by omega)), if_pos rfl,
    Real.mul_self_sqrt hφ.le]

theorem centerSecondOrder_conductor_one {e : ℕ} (he : 2 ≤ e) (α : ℝ) :
    centerSecondOrder α e 1 = -(α * vonMangoldt e / Real.sqrt e.totient) := by
  unfold centerSecondOrder centerLimitCoeff
  rw [if_neg (fun h : e = 1 ∧ 1 = 1 => absurd h.1 (by omega)), if_neg (show e ≠ 1 by omega),
    if_pos rfl, Nat.totient_one, Nat.cast_one, Real.sqrt_one, mul_one]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
