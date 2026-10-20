import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeHorizonCrossoverScale
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusResponseWhiteNoiseLaw

/-!
# The damped period variance and the non-commuting limits

For the power-damped Möbius weight `c_ε(d) = μ(d) d^{-ε}`, `ε > 0`, the complete response is the
damped divisor function `τ_ε(n) = Σ_{d | n} μ(d) d^{-ε}`, and the horizon-`N` response differs from
it only through divisors above the horizon: `τ_ε(n) - s_N(n) = Σ_{d | n, d > N} μ(d) d^{-ε}`. Its
mean square over any range is at most the tail beyond `N` of the gcd series

`G(d, e) = (de)^{-ε} / lcm(d, e)`,

which converges: its boxes are the Selberg forms of the weight `d^{-ε}`, bounded by
`ζ(1+ε)² ζ(1+2ε)`. Comparing complete periods of `s_N` with Cesàro means of `τ_ε` gives

`Q_Sel(N; c_ε) → E[τ_ε²]` and `Cov_N(0; c_ε) → V(ε) = E[τ_ε²] - E[τ_ε]²`:

the period variance of the damped response converges to the variance of the complete damped divisor
function, and `V(ε) ~ ε/2` as `ε → 0`. The Möbius response keeps its period variance above `1/288`
at every large horizon, so the cofinal limit and the damping limit do not commute:

`lim_{ε→0} lim_{N→∞} Cov_N(0; c_ε) = 0 < 1/288 ≤ liminf_{N→∞} Cov_N(0; μ)`,

and for every small fixed damping the damped response has strictly smaller period variance than the
Möbius response at all large horizons. The Möbius variance floor is a horizon phenomenon: it lives in
the trans-horizon divisors that every fixed damping suppresses.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The gcd series -/

/-- The gcd kernel `G(d, e) = (de)^{-ε}/lcm(d, e)`. -/
def dampedGcdKernel (ε : ℝ) (p : ℕ × ℕ) : ℝ :=
  (p.1 : ℝ) ^ (-ε) * (p.2 : ℝ) ^ (-ε) / (Nat.lcm p.1 p.2 : ℝ)

theorem dampedGcdKernel_nonneg (ε : ℝ) (p : ℕ × ℕ) : 0 ≤ dampedGcdKernel ε p := by
  unfold dampedGcdKernel; positivity

/-- `Σ_{g | d ≤ N} d^{-1-ε} ≤ g^{-1-ε} ζ(1+ε)`. -/
private theorem sum_multiples_rpow_le {ε : ℝ} (hε : 0 < ε) (N g : ℕ) (hg : 0 < g) :
    ∑ d ∈ (Icc 1 N).filter (fun d => g ∣ d), (d : ℝ) ^ (-ε) / d ≤
      (g : ℝ) ^ (-1 - ε) * ∑' m : ℕ, (m : ℝ) ^ (-1 - ε) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hsum : Summable (fun m : ℕ => (m : ℝ) ^ (-1 - ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hset : (Icc 1 N).filter (fun d => g ∣ d) = (Icc 1 (N / g)).image (fun m => g * m) := by
    ext d
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hg).mpr (by linarith [mul_comm g k])⟩, rfl⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h1
      · exact hk
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      have := (Nat.le_div_iff_mul_le hg).mp h2
      exact ⟨⟨by nlinarith, by linarith [mul_comm g m]⟩, dvd_mul_right g m⟩
  rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hg h)]
  have hterm : ∀ m ∈ Icc 1 (N / g), ((g * m : ℕ) : ℝ) ^ (-ε) / ((g * m : ℕ) : ℝ) =
      (g : ℝ) ^ (-1 - ε) * (m : ℝ) ^ (-1 - ε) := by
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    push_cast
    rw [← Real.mul_rpow hgR.le hmR.le, show (-1 - ε) = -ε - 1 by ring,
      Real.rpow_sub_one (by positivity)]
  rw [sum_congr rfl hterm, ← mul_sum]
  exact mul_le_mul_of_nonneg_left
    (hsum.sum_le_tsum _ fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _) (by positivity)

/-- **Box bound.** `Σ_{d, e ≤ N} G(d, e) ≤ ζ(1+ε)² ζ(1+2ε)` (as `tsum`s), uniformly in `N`. -/
theorem sum_box_dampedGcdKernel_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), dampedGcdKernel ε p ≤
      (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * ∑' g : ℕ, (g : ℝ) ^ (-1 - 2 * ε) := by
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  have hZ : 0 ≤ Z := tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hsum2 : Summable (fun g : ℕ => (g : ℝ) ^ (-1 - 2 * ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbox := sum_div_lcm_eq_selbergTotientDiagonalForm N (fun d => (d : ℝ) ^ (-ε))
  unfold dampedGcdKernel
  rw [hbox, selbergTotientDiagonalForm]
  calc ∑ g ∈ Icc 1 N, (Nat.totient g : ℝ) *
        selbergMultiplesCoord N (fun d => (d : ℝ) ^ (-ε)) g ^ (2 : ℕ)
      ≤ ∑ g ∈ Icc 1 N, Z ^ 2 * (g : ℝ) ^ (-1 - 2 * ε) := by
        refine sum_le_sum fun g hg => ?_
        have hg0 : 0 < g := (mem_Icc.mp hg).1
        have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
        have hY0 : 0 ≤ selbergMultiplesCoord N (fun d => (d : ℝ) ^ (-ε)) g :=
          sum_nonneg fun d _ => by positivity
        have hY := sum_multiples_rpow_le hε N g hg0
        have hφ : (Nat.totient g : ℝ) ≤ g := by exact_mod_cast Nat.totient_le g
        have hpow : (g : ℝ) * ((g : ℝ) ^ (-1 - ε)) ^ 2 = (g : ℝ) ^ (-1 - 2 * ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hgR.le, ← Real.rpow_one_add' hgR.le
            (by push_cast; linarith)]
          push_cast; ring_nf
        calc (Nat.totient g : ℝ) * selbergMultiplesCoord N (fun d => (d : ℝ) ^ (-ε)) g ^ (2 : ℕ)
            ≤ (g : ℝ) * ((g : ℝ) ^ (-1 - ε) * Z) ^ 2 :=
              mul_le_mul hφ (pow_le_pow_left₀ hY0 hY 2) (sq_nonneg _) hgR.le
          _ = Z ^ 2 * ((g : ℝ) * ((g : ℝ) ^ (-1 - ε)) ^ 2) := by ring
          _ = Z ^ 2 * (g : ℝ) ^ (-1 - 2 * ε) := by rw [hpow]
    _ = Z ^ 2 * ∑ g ∈ Icc 1 N, (g : ℝ) ^ (-1 - 2 * ε) := by rw [mul_sum]
    _ ≤ Z ^ 2 * ∑' g : ℕ, (g : ℝ) ^ (-1 - 2 * ε) :=
        mul_le_mul_of_nonneg_left (hsum2.sum_le_tsum _ fun g _ =>
          Real.rpow_nonneg (Nat.cast_nonneg g) _) (sq_nonneg Z)

/-- The gcd series converges. -/
theorem summable_dampedGcdKernel {ε : ℝ} (hε : 0 < ε) : Summable (dampedGcdKernel ε) := by
  refine summable_of_sum_le (c := (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 *
    ∑' g : ℕ, (g : ℝ) ^ (-1 - 2 * ε)) (dampedGcdKernel_nonneg ε) fun s => ?_
  set K := s.sup (fun p => max p.1 p.2)
  have hzero : ∀ p ∈ s, p ∉ s.filter (fun p => 0 < p.1 ∧ 0 < p.2) → dampedGcdKernel ε p = 0 := by
    intro p hp hnot
    simp only [mem_filter, not_and, not_lt] at hnot
    have : p.1 = 0 ∨ p.2 = 0 := by
      by_contra h; push Not at h; exact absurd (hnot hp (by omega)) (by omega)
    rcases this with h | h <;> simp [dampedGcdKernel, h]
  calc ∑ p ∈ s, dampedGcdKernel ε p
      = ∑ p ∈ s.filter (fun p => 0 < p.1 ∧ 0 < p.2), dampedGcdKernel ε p :=
        (sum_subset (filter_subset _ _) hzero).symm
    _ ≤ ∑ p ∈ (Icc 1 K) ×ˢ (Icc 1 K), dampedGcdKernel ε p := by
        refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
          fun p _ _ => dampedGcdKernel_nonneg ε p
        simp only [mem_filter] at hp
        have hle : max p.1 p.2 ≤ K := le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp.1
        simp only [mem_product, mem_Icc]
        omega
    _ ≤ _ := sum_box_dampedGcdKernel_le hε K

/-! ### The trans-horizon tail of the damped response -/

/-- `τ_ε(n) - s_N(n)` is the sum over the divisors of `n` above the horizon. -/
theorem pmPowerDampedDivisorCoeff_sub_sieveSeq (ε : ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    RHTower.pmPowerDampedDivisorCoeff ε n - sieveSeq N (pmPowerDampedRealWeight ε) n =
      ∑ d ∈ n.divisors.filter (fun d => N < d), pmPowerDampedRealWeight ε d := by
  unfold RHTower.pmPowerDampedDivisorCoeff sieveSeq
  rw [filter_dvd_Icc_eq_divisors_filter_le N hn]
  have hsplit := (sum_filter_add_sum_filter_not n.divisors (fun d => d ≤ N)
    (pmPowerDampedRealWeight ε)).symm
  have hnot : n.divisors.filter (fun d => ¬ d ≤ N) = n.divisors.filter (fun d => N < d) := by
    ext d; simp only [mem_filter, not_le]
  rw [hnot] at hsplit
  have hc : ∀ d, (moebius d : ℝ) * (d : ℝ) ^ (-ε) = pmPowerDampedRealWeight ε d := fun d => by
    simp [pmPowerDampedRealWeight, moebiusReal]
  simp_rw [hc]
  linarith

/-- **Trans-horizon mean square.** Over every range `[1, X]` the mean square of `τ_ε - s_N` is at
most the gcd series over the box `(N, X]²`. -/
theorem sum_sq_divisorCoeff_sub_sieveSeq_le (ε : ℝ) (N X : ℕ) :
    ∑ n ∈ Icc 1 X, (RHTower.pmPowerDampedDivisorCoeff ε n -
        sieveSeq N (pmPowerDampedRealWeight ε) n) ^ 2 ≤
      X * ∑ p ∈ (Icc (N + 1) X) ×ˢ (Icc (N + 1) X), dampedGcdKernel ε p := by
  set B := (Icc (N + 1) X) ×ˢ (Icc (N + 1) X)
  set w : ℕ → ℝ := fun d => (d : ℝ) ^ (-ε)
  have hpt : ∀ n ∈ Icc 1 X, (RHTower.pmPowerDampedDivisorCoeff ε n -
      sieveSeq N (pmPowerDampedRealWeight ε) n) ^ 2 ≤
        ∑ p ∈ B, if p.1 ∣ n ∧ p.2 ∣ n then w p.1 * w p.2 else 0 := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := mem_Icc.mp hn
    rw [pmPowerDampedDivisorCoeff_sub_sieveSeq ε N hn1]
    set D := n.divisors.filter (fun d => N < d)
    have hD : D = (Icc (N + 1) X).filter (· ∣ n) := by
      ext d
      simp only [D, mem_filter, Nat.mem_divisors, mem_Icc]
      constructor
      · rintro ⟨⟨hd, -⟩, hNd⟩; exact ⟨⟨hNd, (Nat.le_of_dvd hn1 hd).trans hnX⟩, hd⟩
      · rintro ⟨⟨hNd, -⟩, hd⟩; exact ⟨⟨hd, by omega⟩, hNd⟩
    have habs : |∑ d ∈ D, pmPowerDampedRealWeight ε d| ≤ ∑ d ∈ D, w d :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => by
        simp only [pmPowerDampedRealWeight, w, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
        have : |moebiusReal d| ≤ 1 := by
          unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) d) (-ε)])
    calc (∑ d ∈ D, pmPowerDampedRealWeight ε d) ^ 2
        ≤ (∑ d ∈ D, w d) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = ∑ p ∈ B, if p.1 ∣ n ∧ p.2 ∣ n then w p.1 * w p.2 else 0 := by
          rw [sq, sum_mul_sum, ← sum_product', hD, ← sum_filter]
          congr 1
          ext p
          simp only [B, mem_product, mem_filter]
          tauto
  calc ∑ n ∈ Icc 1 X, (RHTower.pmPowerDampedDivisorCoeff ε n -
        sieveSeq N (pmPowerDampedRealWeight ε) n) ^ 2
      ≤ ∑ n ∈ Icc 1 X, ∑ p ∈ B, if p.1 ∣ n ∧ p.2 ∣ n then w p.1 * w p.2 else 0 :=
        sum_le_sum hpt
    _ = ∑ p ∈ B, w p.1 * w p.2 * ((X / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
        rw [sum_comm]
        refine sum_congr rfl fun p _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
        congr 2
        have hIoc : Icc 1 X = Ioc 0 X := by ext; simp only [mem_Icc, mem_Ioc]; omega
        rw [hIoc, ← Nat.Ioc_filter_dvd_card_eq_div]
        congr 1
        ext n
        simp only [mem_filter, Nat.lcm_dvd_iff]
    _ ≤ ∑ p ∈ B, w p.1 * w p.2 * ((X : ℝ) / Nat.lcm p.1 p.2) :=
        sum_le_sum fun p _ => mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
    _ = X * ∑ p ∈ B, dampedGcdKernel ε p := by
        rw [mul_sum]
        exact sum_congr rfl fun p _ => by simp only [dampedGcdKernel, w]; ring

/-- The tail of the gcd series above the horizon. -/
def dampedGcdTail (ε : ℝ) (N : ℕ) : ℝ :=
  ∑' p : ℕ × ℕ, if N < p.1 ∧ N < p.2 then dampedGcdKernel ε p else 0

theorem dampedGcdTail_nonneg (ε : ℝ) (N : ℕ) : 0 ≤ dampedGcdTail ε N :=
  tsum_nonneg fun p => by split_ifs <;> simp [dampedGcdKernel_nonneg]

theorem sum_box_le_dampedGcdTail {ε : ℝ} (hε : 0 < ε) (N X : ℕ) :
    ∑ p ∈ (Icc (N + 1) X) ×ˢ (Icc (N + 1) X), dampedGcdKernel ε p ≤ dampedGcdTail ε N := by
  have hs : Summable (fun p : ℕ × ℕ => if N < p.1 ∧ N < p.2 then dampedGcdKernel ε p else 0) :=
    (summable_dampedGcdKernel hε).of_nonneg_of_le
      (fun p => by split_ifs <;> simp [dampedGcdKernel_nonneg])
      (fun p => by split_ifs <;> simp [dampedGcdKernel_nonneg])
  calc ∑ p ∈ (Icc (N + 1) X) ×ˢ (Icc (N + 1) X), dampedGcdKernel ε p
      = ∑ p ∈ (Icc (N + 1) X) ×ˢ (Icc (N + 1) X),
          (if N < p.1 ∧ N < p.2 then dampedGcdKernel ε p else 0) :=
        sum_congr rfl fun p hp => by
          simp only [mem_product, mem_Icc] at hp
          rw [if_pos ⟨by omega, by omega⟩]
    _ ≤ dampedGcdTail ε N :=
        hs.sum_le_tsum _ fun p _ => by split_ifs <;> simp [dampedGcdKernel_nonneg]

/-- The tail of the gcd series vanishes as the horizon grows. -/
theorem tendsto_dampedGcdTail {ε : ℝ} (hε : 0 < ε) :
    Tendsto (dampedGcdTail ε) atTop (𝓝 0) := by
  rw [← tsum_zero]
  refine tendsto_tsum_of_dominated_convergence (bound := dampedGcdKernel ε)
    (summable_dampedGcdKernel hε) (fun p => ?_) (Eventually.of_forall fun N p => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop p.1] with N hN
    rw [if_neg (by omega)]
  · split_ifs
    · rw [Real.norm_of_nonneg (dampedGcdKernel_nonneg ε p)]
    · simp [dampedGcdKernel_nonneg]

/-! ### Convergence of the damped period forms -/

/-- Complete periods: `Σ_{n ≤ qN!} s_N(n)² = qN! · Q_Sel(N)`. -/
private theorem sum_sq_factorial_period (N q : ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ Icc 1 (q * N.factorial), sieveSeq N c n ^ 2 =
      ((q * N.factorial : ℕ) : ℝ) * selbergTotientDiagonalForm N c := by
  have hL : ∀ d ∈ Icc 1 N, d ∣ q * N.factorial := fun d hd =>
    Dvd.dvd.mul_left (Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2) q
  have h := sum_sieveSeq_sq_sliding_period_eq hL c 0
  simpa using h

/-- `(a + b)² ≤ (1+η) a² + (1 + 1/η) b²`. -/
private theorem sq_add_le_weighted (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := by
  have h : 0 ≤ (η * a - b) ^ 2 / η := by positivity
  have h2 : (η * a - b) ^ 2 / η = η * a ^ 2 - 2 * a * b + b ^ 2 / η := by
    field_simp; ring
  rw [h2] at h
  have h3 : (1 + 1 / η) * b ^ 2 = b ^ 2 + b ^ 2 / η := by ring
  nlinarith

/-- The two comparison inequalities between `Q_Sel(N; c_ε)` and `E[τ_ε²]`. -/
private theorem selberg_secondDensity_compare {ε : ℝ} (hε : 0 < ε) (N : ℕ) {η : ℝ} (hη : 0 < η) :
    selbergTotientDiagonalForm N (pmPowerDampedRealWeight ε) ≤
        (1 + η) * RHTower.pmPowerDampedSecondDensity ε + (1 + 1 / η) * dampedGcdTail ε N ∧
      RHTower.pmPowerDampedSecondDensity ε ≤
        (1 + η) * selbergTotientDiagonalForm N (pmPowerDampedRealWeight ε) +
          (1 + 1 / η) * dampedGcdTail ε N := by
  set c := pmPowerDampedRealWeight ε
  set Q := selbergTotientDiagonalForm N c
  set T := dampedGcdTail ε N
  set τ := RHTower.pmPowerDampedDivisorCoeff ε
  -- Cesàro means of `τ²` along complete periods `X_q = (q+1) N!`
  set X : ℕ → ℕ := fun q => (q + 1) * N.factorial
  have hXpos : ∀ q, (0 : ℝ) < X q := fun q => by
    simp only [X]; exact_mod_cast Nat.mul_pos (Nat.succ_pos q) (Nat.factorial_pos N)
  have hXtend : Tendsto (fun q => ((X q : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono
      (fun q => Nat.le_mul_of_pos_right (q + 1) (Nat.factorial_pos N)) (tendsto_add_atTop_nat 1))
  have hmean := (RHTower.tendsto_pmPowerDampedDivisorCoeff_sq_mean hε).comp hXtend
  simp only [Function.comp_def, Nat.floor_natCast] at hmean
  -- per-period inequalities
  have hdiff : ∀ q, ∑ n ∈ Icc 1 (X q), (τ n - sieveSeq N c n) ^ 2 ≤ (X q : ℝ) * T := fun q =>
    (sum_sq_divisorCoeff_sub_sieveSeq_le ε N (X q)).trans
      (mul_le_mul_of_nonneg_left (sum_box_le_dampedGcdTail hε N (X q)) (Nat.cast_nonneg _))
  have hper : ∀ q, ∑ n ∈ Icc 1 (X q), sieveSeq N c n ^ 2 = (X q : ℝ) * Q := fun q =>
    sum_sq_factorial_period N (q + 1) c
  have hc1 : 0 ≤ 1 + 1 / η := by positivity
  constructor
  · refine ge_of_tendsto (hmean.const_mul (1 + η) |>.add_const ((1 + 1 / η) * T))
      (Eventually.of_forall fun q => ?_)
    have hpt : ∀ n ∈ Icc 1 (X q), sieveSeq N c n ^ 2 ≤
        (1 + η) * τ n ^ 2 + (1 + 1 / η) * (τ n - sieveSeq N c n) ^ 2 := fun n _ => by
      have := sq_add_le_weighted (τ n) (sieveSeq N c n - τ n) hη
      rw [add_sub_cancel, show (sieveSeq N c n - τ n) ^ 2 = (τ n - sieveSeq N c n) ^ 2 by ring]
        at this
      exact this
    have hs := sum_le_sum hpt
    rw [hper, sum_add_distrib, ← mul_sum, ← mul_sum] at hs
    have hX := hXpos q
    have key : (X q : ℝ) * Q ≤ (1 + η) * ∑ n ∈ Icc 1 (X q), τ n ^ 2 + (1 + 1 / η) * ((X q : ℝ) * T) :=
      hs.trans (by gcongr; exact hdiff q)
    calc Q = ((X q : ℝ) * Q) / X q := by field_simp
      _ ≤ ((1 + η) * ∑ n ∈ Icc 1 (X q), τ n ^ 2 + (1 + 1 / η) * ((X q : ℝ) * T)) / X q :=
          div_le_div_of_nonneg_right key hX.le
      _ = (1 + η) * ((∑ n ∈ Icc 1 (X q), τ n ^ 2) / X q) + (1 + 1 / η) * T := by
          field_simp
  · refine le_of_tendsto hmean (Eventually.of_forall fun q => ?_)
    have hpt : ∀ n ∈ Icc 1 (X q), τ n ^ 2 ≤
        (1 + η) * sieveSeq N c n ^ 2 + (1 + 1 / η) * (τ n - sieveSeq N c n) ^ 2 := fun n _ => by
      have := sq_add_le_weighted (sieveSeq N c n) (τ n - sieveSeq N c n) hη
      rwa [add_sub_cancel] at this
    have hs := sum_le_sum hpt
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hper] at hs
    have hX := hXpos q
    have key : ∑ n ∈ Icc 1 (X q), τ n ^ 2 ≤ (1 + η) * ((X q : ℝ) * Q) + (1 + 1 / η) * ((X q : ℝ) * T) :=
      hs.trans (by gcongr; exact hdiff q)
    rw [div_le_iff₀ hX]
    nlinarith

/-- **Cofinal Selberg form.** `Q_Sel(N; c_ε) → E[τ_ε²]`. -/
theorem tendsto_selbergTotientDiagonalForm_pmPowerDamped {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => selbergTotientDiagonalForm N (pmPowerDampedRealWeight ε)) atTop
      (𝓝 (RHTower.pmPowerDampedSecondDensity ε)) := by
  set D := RHTower.pmPowerDampedSecondDensity ε
  set T := dampedGcdTail ε
  set Q := fun N : ℕ => selbergTotientDiagonalForm N (pmPowerDampedRealWeight ε)
  have hT := tendsto_dampedGcdTail hε
  have hT0 := dampedGcdTail_nonneg ε
  -- the adapted parameter `η_N = √T_N + 1/(N+1)`
  set η : ℕ → ℝ := fun N => Real.sqrt (T N) + 1 / ((N : ℝ) + 1)
  have hη : ∀ N, 0 < η N := fun N => by simp only [η]; positivity
  have hηT : ∀ N, T N / η N ≤ Real.sqrt (T N) := fun N => by
    rw [div_le_iff₀ (hη N)]
    have h1 := Real.mul_self_sqrt (hT0 N)
    have h2 : 0 ≤ Real.sqrt (T N) := Real.sqrt_nonneg _
    have h3 : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    simp only [η]; nlinarith
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => Real.sqrt (T N)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hT
      rwa [Real.sqrt_zero] at this
    have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  have hsqrt : Tendsto (fun N => Real.sqrt (T N)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hT
    rwa [Real.sqrt_zero] at this
  -- a uniform bound from `η = 1`
  have hQB : ∀ N, Q N ≤ 2 * D + 2 * T N := fun N => by
    have := (selberg_secondDensity_compare hε N one_pos).1
    norm_num at this; linarith
  have hD0 : 0 ≤ D := by
    have := (selberg_secondDensity_compare hε 0 one_pos).2
    have hQ0 : 0 ≤ Q 0 := selbergTotientDiagonalForm_nonneg _ _
    have := RHTower.pmPowerDampedDivisorVariance_nonneg hε
    unfold RHTower.pmPowerDampedDivisorVariance at this
    nlinarith [sq_nonneg (RHTower.pmPowerDampedDivisorDensity ε).re]
  -- squeeze `Q N - D`
  have hup : ∀ N, Q N - D ≤ η N * D + T N + Real.sqrt (T N) := fun N => by
    have h := (selberg_secondDensity_compare hε N (hη N)).1
    have : (1 + 1 / η N) * T N = T N + T N / η N := by ring
    linarith [hηT N]
  have hlow : ∀ N, -(η N * (2 * D + 2 * T N) + T N + Real.sqrt (T N)) ≤ Q N - D := fun N => by
    have h := (selberg_secondDensity_compare hε N (hη N)).2
    have : (1 + 1 / η N) * T N = T N + T N / η N := by ring
    have hb : η N * Q N ≤ η N * (2 * D + 2 * T N) :=
      mul_le_mul_of_nonneg_left (hQB N) (hη N).le
    linarith [hηT N]
  have hU : Tendsto (fun N => η N * D + T N + Real.sqrt (T N)) atTop (𝓝 0) := by
    simpa using ((hηlim.mul_const D).add hT).add hsqrt
  have hL : Tendsto (fun N => -(η N * (2 * D + 2 * T N) + T N + Real.sqrt (T N))) atTop (𝓝 0) := by
    simpa using (((hηlim.mul ((hT.const_mul 2).const_add (2 * D))).add hT).add hsqrt).neg
  have hsq := tendsto_of_tendsto_of_tendsto_of_le_of_le hL hU hlow hup
  simpa using hsq.add_const D

/-- **The damped period variance converges to the variance of `τ_ε`.**
`Cov_N(0; c_ε) → V(ε) = E[τ_ε²] - E[τ_ε]²`. -/
theorem tendsto_periodCovariance_pmPowerDamped_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N (pmPowerDampedRealWeight ε) 0) atTop
      (𝓝 (RHTower.pmPowerDampedDivisorVariance ε)) := by
  have hH := tendsto_finiteHarmonicSum_pmPowerDamped hε
  have h := (tendsto_selbergTotientDiagonalForm_pmPowerDamped hε).sub (hH.pow 2)
  refine h.congr fun N => ?_
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal, selbergTotientDiagonalForm]
  rcases N with _ | N
  · simp [finiteHarmonicSum]
  · have hI : Icc 1 (N + 1) = insert 1 (Icc 2 (N + 1)) := by
      ext e; simp only [mem_Icc, mem_insert]; omega
    rw [hI, sum_insert (by simp), selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    simp only [Nat.totient_one, Nat.cast_one, one_mul, ramanujanLagWeight_zero_left]
    ring

/-! ### Non-commuting limits -/

/-- The iterated limit vanishes: `lim_{ε→0} lim_{N→∞} Cov_N(0; c_ε) = 0`. -/
theorem tendsto_pmPowerDampedDivisorVariance_zero :
    Tendsto RHTower.pmPowerDampedDivisorVariance (𝓝[>] 0) (𝓝 0) := by
  have h := RHTower.tendsto_pmPowerDampedDivisorVariance_div_parameter.mul
    (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have : ε ≠ 0 := ne_of_gt hε
  simp only [id]
  field_simp

/-- **The cofinal and damping limits do not commute.** For every sufficiently small damping
`ε > 0`, at all large horizons the damped response has strictly smaller period variance than the
Möbius response, whose variance stays above `1/288`. -/
theorem eventually_periodCovariance_pmPowerDamped_lt_moebius :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      TwoLagSieve.periodCovariance N (pmPowerDampedRealWeight ε) 0 <
        TwoLagSieve.periodCovariance N moebiusReal 0 := by
  filter_upwards [tendsto_pmPowerDampedDivisorVariance_zero.eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 288 by norm_num)), self_mem_nhdsWithin]
    with ε hV hε
  filter_upwards [(tendsto_periodCovariance_pmPowerDamped_zero hε).eventually
      (eventually_lt_nhds hV), eventually_periodCovariance_moebius_zero_ge] with N h1 h2
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
