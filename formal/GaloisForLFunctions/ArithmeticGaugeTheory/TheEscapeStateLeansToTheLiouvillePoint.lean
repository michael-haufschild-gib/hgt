import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponent
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeSquarefreeDensityAndMobiusDilationMeans

/-!
# The escape state leans to the Liouville point

Weight Haar measure on the gauge torus by the square of the twisted Möbius sums: `|S_N(x)|² dx / N`.
This is where the energy of `S_N` sits on `G`; call its limit the **escape state** of the Möbius
source. Its Fourier coefficients are computable.

* **The coefficients** (`integral_normSq_moebiusGaugeSum_mul_twist_eq`). Against the character
  `χ_x(a)`, the weighted mass is the dilation correlation `Σ_{m ≤ N/a} μ(m) μ(am)`.
* **The limit** (`tendsto_escapeCoefficient`). Divided by `N` it tends to `μ(a) d(a)/a`, where
  `d(a) = (6/π²) Π_{p ∣ a} p/(p + 1)` is the density of squarefree integers prime to `a`. At `a = 1`
  the total mass is `6/π²` (`tendsto_escapeMass`).
* **The tilt** (`tendsto_escapeCoefficient_prime`, `eventually_re_escapeCoefficient_prime_neg`). At a
  prime `p` the coefficient is `−(6/π²)/(p + 1) < 0`: the energy of the Möbius sums leans toward the
  gauge points with `χ(p) = −1`, i.e. toward the Liouville point, where `μχ = μ²` is coherent, and away
  from the trivial point, where `χ(p) = +1`.

The escape state is an Euler product in its coefficients: multiplicative data, the same at every
height, with no trace of the zeros of `ζ`. An off-line zero would make `|S_N(0)|²` large at the single
point `0`; the escape state does not see it. Off-line energy is visible only at the point.
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The weighted mass `∫ |S_N|² χ(a)` as a double sum over coinciding products. -/
theorem integral_normSq_moebiusGaugeSum_mul_twist {a : ℕ} (ha : a ≠ 0) (N : ℕ) :
    ∫ x, ((‖moebiusGaugeSum N x‖ ^ 2 : ℝ) : ℂ) * twist x a ∂gaugeHaar =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if m * a = n then ((μ m : ℤ) : ℂ) * ((μ n : ℤ) : ℂ) else 0 := by
  have hpos : ∀ n ∈ Icc 1 N, n ≠ 0 := fun n hn => Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1
  have hpt : ∀ x : GaugeTorus, ((‖moebiusGaugeSum N x‖ ^ 2 : ℝ) : ℂ) * twist x a =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ((μ m : ℤ) : ℂ) * ((μ n : ℤ) : ℂ) *
        (twist x (m * a) * conj (twist x n)) := by
    intro x
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, moebiusGaugeSum, map_sum, sum_mul_sum,
      sum_mul]
    refine sum_congr rfl fun m hm => ?_
    rw [sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [twist_mul x (hpos m hm) ha, map_mul, map_intCast]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_twist_mul_conj _ _).const_mul _]
  refine sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun n _ => (integrable_twist_mul_conj _ _).const_mul _]
  refine sum_congr rfl fun n hn => ?_
  rw [integral_const_mul, integral_twist_mul_conj (mul_ne_zero (hpos m hm) ha) (hpos n hn)]
  split_ifs <;> simp

/-- **The coefficients.** `∫ |S_N|² χ(a) = Σ_{m ≤ N/a} μ(m) μ(am)`. -/
theorem integral_normSq_moebiusGaugeSum_mul_twist_eq {a : ℕ} (ha : a ≠ 0) (N : ℕ) :
    ∫ x, ((‖moebiusGaugeSum N x‖ ^ 2 : ℝ) : ℂ) * twist x a ∂gaugeHaar =
      ((∑ m ∈ Icc 1 (N / a), ((μ (1 * m) : ℤ) : ℝ) * ((μ (a * m) : ℤ) : ℝ) : ℝ) : ℂ) := by
  rw [integral_normSq_moebiusGaugeSum_mul_twist ha]
  simp_rw [sum_ite_eq]
  rw [← sum_filter]
  have hset : (Icc 1 N).filter (fun m => m * a ∈ Icc 1 N) = Icc 1 (N / a) := by
    ext m
    simp only [mem_filter, mem_Icc]
    have ha0 : 0 < a := Nat.pos_of_ne_zero ha
    constructor
    · rintro ⟨⟨h1, -⟩, -, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le ha0).mpr h2⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.le_div_iff_mul_le ha0).mp h2
      exact ⟨⟨h1, le_trans (Nat.le_mul_of_pos_right m ha0) h3⟩,
        le_trans h1 (Nat.le_mul_of_pos_right m ha0), h3⟩
  rw [hset]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [one_mul, mul_comm m a]

/-- The squarefree densities are positive. -/
theorem coprimeSquarefreeDensity_pos (Q : ℕ) :
    0 < BezoutValuationIncidence.coprimeSquarefreeDensity Q := by
  rw [BezoutValuationIncidence.coprimeSquarefreeDensity]
  refine mul_pos (by rw [RHTower.Sieve.squarefreeDensity_eq]; positivity)
    (prod_pos fun p hp => div_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by positivity))

/-- **The limit of the coefficients.** `(1/N) ∫ |S_N|² χ(a) → μ(a) d(a)/a`. -/
theorem tendsto_escapeCoefficient {a : ℕ} (ha : a ≠ 0) :
    Tendsto (fun N : ℕ => (∫ x, ((‖moebiusGaugeSum N x‖ ^ 2 : ℝ) : ℂ) * twist x a ∂gaugeHaar) / N)
      atTop (𝓝 ((((μ a : ℤ) : ℝ) * BezoutValuationIncidence.coprimeSquarefreeDensity a / a : ℝ) :
        ℂ)) := by
  have har : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hmean := BezoutValuationIncidence.tendsto_moebius_coprime_dilation_pair_mean
    (Nat.coprime_one_left a)
  rw [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, one_mul] at hmean
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) / a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const har
  have hreal := (hmean.comp hscale).div_const (a : ℝ)
  have hcpx := (Complex.continuous_ofReal.tendsto _).comp hreal
  refine hcpx.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [integral_normSq_moebiusGaugeSum_mul_twist_eq ha, Nat.floor_div_eq_div]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp

/-- **The total escape mass** is the squarefree density `6/π²`. -/
theorem tendsto_escapeMass :
    Tendsto (fun N : ℕ => (∫ x, ((‖moebiusGaugeSum N x‖ ^ 2 : ℝ) : ℂ) ∂gaugeHaar) / N) atTop
      (𝓝 ((BezoutValuationIncidence.coprimeSquarefreeDensity 1 : ℝ) : ℂ)) := by
  have h := tendsto_escapeCoefficient (a := 1) one_ne_zero
  simp only [twist_one, mul_one, ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul,
    Nat.cast_one, div_one] at h
  exact h

/-- **The tilt at a prime.** `(1/N) ∫ |S_N|² χ(p) → −d(1)/(p + 1)`. -/
theorem tendsto_escapeCoefficient_prime {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N : ℕ => (∫ x, ((‖moebiusGaugeSum N x‖ ^ 2 : ℝ) : ℂ) * twist x p ∂gaugeHaar) / N)
      atTop (𝓝 ((-(BezoutValuationIncidence.coprimeSquarefreeDensity 1 / ((p : ℝ) + 1)) : ℝ) :
        ℂ)) := by
  have h := tendsto_escapeCoefficient hp.ne_zero
  have hd : BezoutValuationIncidence.coprimeSquarefreeDensity p =
      (p : ℝ) / ((p : ℝ) + 1) * BezoutValuationIncidence.coprimeSquarefreeDensity 1 := by
    have := BezoutValuationIncidence.coprimeSquarefreeDensity_prime_mul hp
      (Nat.Prime.not_dvd_one hp) one_ne_zero
    rwa [mul_one] at this
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hval : ((μ p : ℤ) : ℝ) * BezoutValuationIncidence.coprimeSquarefreeDensity p / p =
      -(BezoutValuationIncidence.coprimeSquarefreeDensity 1 / ((p : ℝ) + 1)) := by
    rw [ArithmeticFunction.moebius_apply_prime hp, hd]
    field_simp
    push_cast
    ring
  rwa [hval] at h

/-- **The escape state leans to the Liouville point.** At every prime the weighted mass of `χ(p)`
is eventually negative: the energy of the Möbius sums sits where `χ(p)` points to `−1`. -/
theorem eventually_re_escapeCoefficient_prime_neg {p : ℕ} (hp : p.Prime) :
    ∀ᶠ N : ℕ in atTop,
      (∫ x, ((‖moebiusGaugeSum N x‖ ^ 2 : ℝ) : ℂ) * twist x p ∂gaugeHaar).re < 0 := by
  have hlim := (Complex.continuous_re.tendsto _).comp (tendsto_escapeCoefficient_prime hp)
  simp only [Complex.ofReal_re] at hlim
  have hneg : -(BezoutValuationIncidence.coprimeSquarefreeDensity 1 / ((p : ℝ) + 1)) < 0 := by
    have := coprimeSquarefreeDensity_pos 1
    have : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have : 0 < BezoutValuationIncidence.coprimeSquarefreeDensity 1 / ((p : ℝ) + 1) := by positivity
    linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hneg), eventually_gt_atTop 0] with N hN hN0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  simp only [Function.comp_apply, Complex.div_natCast_re] at hN
  exact (div_neg_iff.mp hN).elim (fun h => absurd h.2 (not_lt.mpr hNr.le)) (fun h => h.1)

end GaloisForLFunctions.ArithmeticGaugeTheory
