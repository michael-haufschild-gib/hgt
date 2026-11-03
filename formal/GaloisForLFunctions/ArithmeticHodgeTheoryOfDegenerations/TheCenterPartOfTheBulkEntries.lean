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
  unfold diffPairSum
  simp only [hsplit, Finset.sum_add_distrib]
  rw [sum_sum_ite_lt (fun n j => u n * v j / ((j : ℝ) - n)) N]
  rw [Finset.sum_comm (s := Icc 1 N) (t := Icc 1 N)
    (f := fun n j => if j < n then u n * v j / ((n : ℝ) - j) else 0)]
  rw [sum_sum_ite_lt (fun j n => u n * v j / ((n : ℝ) - j)) N, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast (Finset.mem_Icc.mp hδ).1
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  field_simp
  ring

/-- The mean of a gap row: `|Σ_{n ≤ L} (c_{e'}(n)c_e(n+δ) + c_{e'}(n+δ)c_e(n)) − 2L[e = e']c_e(δ)|`
is bounded uniformly. -/
theorem abs_gapRow_sub_le {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (δ L : ℕ) :
    |∑ n ∈ Icc 1 L, (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + δ) +
        ramanujanLagCoefficient e' (n + δ) * ramanujanLagCoefficient e n) -
      L * (2 * (if e = e' then ramanujanLagCoefficient e δ else 0))| ≤
      2 * (e' * e : ℕ) * (2 * (∑ d ∈ e'.divisors, (d : ℝ)) * ∑ d ∈ e.divisors, (d : ℝ)) := by
  set M := e' * e with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set w : ℕ → ℝ := fun i => ramanujanLagCoefficient e' i * ramanujanLagCoefficient e (i + δ) +
    ramanujanLagCoefficient e' (i + δ) * ramanujanLagCoefficient e i with hw
  have hperM : ∀ (f : ℕ) (i : ℕ), ramanujanLagCoefficient f (i + f * k) =
      ramanujanLagCoefficient f i := fun f i => ramanujanLagCoefficient_add_mul f i k
  have hper : ∀ i, w (i + 1 + M) = w (i + 1) := fun i => by
    simp only [hw]
    have a1 : i + 1 + M = i + 1 + e' * e := rfl
    rw [show i + 1 + M + δ = i + 1 + δ + e * e' by rw [hM]; ring,
      show i + 1 + M = i + 1 + e * e' by rw [hM]; ring,
      ramanujanLagCoefficient_add_mul e, ramanujanLagCoefficient_add_mul e]
    rw [show i + 1 + e * e' = i + 1 + e' * e by ring,
      show i + 1 + δ + e * e' = i + 1 + δ + e' * e by ring,
      ramanujanLagCoefficient_add_mul e', ramanujanLagCoefficient_add_mul e']
  have hbound : ∀ i, |w (i + 1)| ≤ 2 * (∑ d ∈ e'.divisors, (d : ℝ)) * ∑ d ∈ e.divisors, (d : ℝ) :=
    fun i => by
      simp only [hw]
      have a1 := abs_ramanujanLagCoefficient_le e' (i + 1)
      have a2 := abs_ramanujanLagCoefficient_le e (i + 1 + δ)
      have a3 := abs_ramanujanLagCoefficient_le e' (i + 1 + δ)
      have a4 := abs_ramanujanLagCoefficient_le e (i + 1)
      calc |_| ≤ |ramanujanLagCoefficient e' (i + 1) * ramanujanLagCoefficient e (i + 1 + δ)| +
            |ramanujanLagCoefficient e' (i + 1 + δ) * ramanujanLagCoefficient e (i + 1)| :=
            abs_add_le _ _
        _ ≤ (∑ d ∈ e'.divisors, (d : ℝ)) * (∑ d ∈ e.divisors, (d : ℝ)) +
            (∑ d ∈ e'.divisors, (d : ℝ)) * (∑ d ∈ e.divisors, (d : ℝ)) := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul a1 a2 (abs_nonneg _) ((abs_nonneg _).trans a1))
              (mul_le_mul a3 a4 (abs_nonneg _) ((abs_nonneg _).trans a3))
        _ = _ := by ring
  have h := abs_sum_range_sub_mul_mean_le hM1 (fun i => w (i + 1)) hper hbound L
  -- the mean over a period
  have hmean : (∑ i ∈ range M, w (i + 1)) / M =
      2 * (if e = e' then ramanujanLagCoefficient e δ else 0) := by
    have hshift := sum_range_shift_of_periodic w (fun i => by
      simp only [hw]
      rw [show i + M + δ = i + δ + e' * e by rw [hM]; ring, show i + M = i + e' * e by rw [hM],
        ramanujanLagCoefficient_add_mul e', ramanujanLagCoefficient_add_mul e']
      rw [show i + δ + e' * e = i + δ + e * e' by ring, show i + e' * e = i + e * e' by ring,
        ramanujanLagCoefficient_add_mul e, ramanujanLagCoefficient_add_mul e]) 1
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
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      rw [hM]; push_cast; field_simp; ring
    · rw [if_neg (Ne.symm hee), if_neg hee, if_neg hee]; simp
  rw [hmean] at h
  rw [← sum_range_succ_eq_sum_Icc (fun n => ramanujanLagCoefficient e' n *
    ramanujanLagCoefficient e (n + δ) + ramanujanLagCoefficient e' (n + δ) *
      ramanujanLagCoefficient e n)]
  exact h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
