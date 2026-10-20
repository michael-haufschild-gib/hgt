import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedLinearDissipationExactRate
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusResponseWhiteNoiseLaw
import GaloisForLFunctions.BezoutValuationIncidence.JordanUpperBoundAndGcdOrbitPrimitiveEnergy
import GaloisForLFunctions.BezoutValuationIncidence.DiscretePrimitiveEnergyAndJordanComparison

/-!
# The primitive energy of the damped response: the threshold at one half

The zero-mean primitive of a sieve response (its centered discrepancy
`Σ_{j ≤ n} s_N(j) - n H_N`) has complete-period mean square with the Jordan spectrum

`12 E_prim(N; c) = Σ_{2 ≤ q ≤ N} J₂(q) Y_N(q)²`,   `J₂(q) = q² ∏_{p|q}(1 - p^{-2}) ≤ q²`.

For the damped Möbius row the coordinates are dominated by `q^{-1-ε} ζ(1+ε)` and converge to the
Ramanujan coefficients `w_ε(q) = E[τ_ε] μ(q)/∏_{p|q}(p^{1+ε} - 1)`, so the mode masses are of size
`q^{-2ε}`. This gives a sharp threshold at `ε = 1/2`:

* for `ε > 1/2` the primitive energy is bounded uniformly in the horizon and converges to
  `(1/12) Σ_{q ≥ 2} J₂(q) w_ε(q)²`;
* for `0 < ε ≤ 1/2` the prime modes alone carry `J₂(p) w_ε(p)² ≥ (3/4) E[τ_ε]² p^{-2ε} ≥
  (3/4) E[τ_ε]²/p`, whose sum diverges, so the primitive energy tends to infinity;
* for the Möbius row (`ε = 0`) the top octave alone forces linear growth in the horizon.

This is the barrier `ε = 1/2` of the PM receiver, seen on the period torus: below one half no
horizon-uniform bound on the discrepancy can come from complete-period averages, and a receiver
estimate must use the pronic weighting of small arguments.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- `J₂(n) ≤ n²`: `J₂(n)` is one of the nonnegative divisor terms of `Σ_{e | n} J₂(e) = n²`. -/
theorem jordanTotient2_le_sq (n : ℕ) : jordanTotient2 n ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [jordanTotient2]
  · rw [← sum_divisors_jordanTotient2 hn]
    exact single_le_sum (fun e _ => jordanTotient2_nonneg e) (Nat.mem_divisors_self n hn.ne')

/-- The damped coordinates are dominated: `|Y_N(q; c_ε)| ≤ q^{-1-ε} ζ(1+ε)`. -/
theorem abs_selbergMultiplesCoord_pmPowerDamped_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) {q : ℕ}
    (hq : 0 < q) :
    |selbergMultiplesCoord N (pmPowerDampedRealWeight ε) q| ≤
      (q : ℝ) ^ (-1 - ε) * ∑' m : ℕ, (m : ℝ) ^ (-1 - ε) :=
  (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun d _ =>
    abs_pmPowerDampedRealWeight_div_le d).trans (sum_multiples_rpow_le hε N q hq))

/-- Mode masses are dominated by `ζ(1+ε)² q^{-2ε}`. -/
private theorem jordan_mode_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) {q : ℕ} (hq : 0 < q) :
    jordanTotient2 q * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) q ^ 2 ≤
      (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * (q : ℝ) ^ (-2 * ε) := by
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hY := abs_selbergMultiplesCoord_pmPowerDamped_le hε N hq
  have hpow : (q : ℝ) ^ 2 * ((q : ℝ) ^ (-1 - ε)) ^ 2 = (q : ℝ) ^ (-2 * ε) := by
    rw [← Real.rpow_natCast ((q : ℝ) ^ (-1 - ε)) 2, ← Real.rpow_mul hqR.le,
      ← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_add hqR]
    push_cast; ring_nf
  calc jordanTotient2 q * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) q ^ 2
      ≤ (q : ℝ) ^ 2 * ((q : ℝ) ^ (-1 - ε) * Z) ^ 2 := by
        rw [← sq_abs (selbergMultiplesCoord N _ q)]
        exact mul_le_mul (jordanTotient2_le_sq q) (pow_le_pow_left₀ (abs_nonneg _) hY 2)
          (sq_nonneg _) (sq_nonneg _)
    _ = Z ^ 2 * (q : ℝ) ^ (-2 * ε) := by rw [mul_pow, ← hpow]; ring

/-! ### Above one half: uniform bound and convergence -/

/-- **Uniform bound above one half.** For `ε > 1/2`,
`12 E_prim(N; c_ε) ≤ ζ(1+ε)² Σ_q q^{-2ε}` at every horizon. -/
theorem sievePrimitiveEnergy_pmPowerDamped_le {ε : ℝ} (hε : 1 / 2 < ε) (N : ℕ) :
    12 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) ≤
      (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * ∑' q : ℕ, (q : ℝ) ^ (-2 * ε) := by
  have hε0 : 0 < ε := by linarith
  have hs : Summable (fun q : ℕ => (q : ℝ) ^ (-2 * ε)) := Real.summable_nat_rpow.mpr (by linarith)
  rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
  calc ∑ q ∈ Icc 2 N, jordanTotient2 q * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) q ^ 2
      ≤ ∑ q ∈ Icc 2 N, (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * (q : ℝ) ^ (-2 * ε) :=
        sum_le_sum fun q hq => jordan_mode_le hε0 N (by have := (mem_Icc.mp hq).1; omega)
    _ = (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * ∑ q ∈ Icc 2 N, (q : ℝ) ^ (-2 * ε) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun q _ =>
          Real.rpow_nonneg (Nat.cast_nonneg q) _) (sq_nonneg _)

/-- **Convergence above one half.** For `ε > 1/2`,
`12 E_prim(N; c_ε) → Σ_{q ≥ 2} J₂(q) w_ε(q)²`. -/
theorem tendsto_sievePrimitiveEnergy_pmPowerDamped {ε : ℝ} (hε : 1 / 2 < ε) :
    Tendsto (fun N : ℕ => 12 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)) atTop
      (𝓝 (∑' q : ℕ, if 2 ≤ q then jordanTotient2 q * dampedRamanujanCoeff ε q ^ 2 else 0)) := by
  have hε0 : 0 < ε := by linarith
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  set G : ℕ → ℕ → ℝ := fun N q =>
    if q ∈ Icc 2 N then jordanTotient2 q * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) q ^ 2
    else 0
  have hfin : ∀ N, 12 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) = ∑' q, G N q := by
    intro N
    rw [tsum_eq_sum (s := Icc 2 N) (fun q hq => by simp only [G]; rw [if_neg hq]),
      twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
    exact sum_congr rfl fun q hq => by simp only [G]; rw [if_pos hq]
  simp_rw [hfin]
  refine tendsto_tsum_of_dominated_convergence (bound := fun q => Z ^ 2 * (q : ℝ) ^ (-2 * ε))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _) (fun q => ?_) ?_
  · by_cases hq : 2 ≤ q
    · rw [if_pos hq]
      refine ((tendsto_selbergMultiplesCoord_pmPowerDamped hε0 (e := q) (by omega)).pow 2
        |>.const_mul (jordanTotient2 q)).congr' ?_
      filter_upwards [eventually_ge_atTop q] with N hN
      simp only [G, mem_Icc, hq, hN, and_self, if_true]
    · rw [if_neg hq]
      simp only [G, mem_Icc, hq, false_and, if_false]
      exact tendsto_const_nhds
  · filter_upwards with N q
    simp only [G]
    split_ifs with hq
    · have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
      rw [Real.norm_of_nonneg (mul_nonneg (jordanTotient2_nonneg q) (sq_nonneg _))]
      exact jordan_mode_le hε0 N hq0
    · rw [norm_zero]
      exact mul_nonneg (sq_nonneg Z) (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-! ### At and below one half: divergence -/

/-- The prime mode mass: `J₂(p) w_ε(p)² ≥ (3/4) E[τ_ε]² / p` for `0 < ε ≤ 1/2`. -/
private theorem prime_mode_ge {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {p : ℕ} (hp : p.Prime) :
    3 / 4 * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 * (1 / (p : ℝ)) ≤
      jordanTotient2 p * dampedRamanujanCoeff ε p ^ 2 := by
  set ρ := (RHTower.pmPowerDampedDivisorDensity ε).re
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hJ : jordanTotient2 p = (p : ℝ) ^ 2 - 1 := by
    have := jordanTotient2_prime_pow_succ hp 0
    simpa using this
  have hD : RHTower.pmPowerDampedRamanujanDenominator ε p = (p : ℝ) ^ (1 + ε) - 1 := by
    rw [RHTower.pmPowerDampedRamanujanDenominator, hp.primeFactors, prod_singleton]
  have hpe : (p : ℝ) ≤ (p : ℝ) ^ (1 + ε) :=
    Real.self_le_rpow_of_one_le (by linarith) (by linarith)
  have hDpos : 0 < (p : ℝ) ^ (1 + ε) - 1 := by linarith
  have hw : dampedRamanujanCoeff ε p ^ 2 = ρ ^ 2 / ((p : ℝ) ^ (1 + ε) - 1) ^ 2 := by
    rw [dampedRamanujanCoeff, RHTower.pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re,
      moebius_apply_prime hp, hD, div_pow]
    simp only [ρ]
    push_cast
    ring
  have hsq : ((p : ℝ) ^ (1 + ε) - 1) ^ 2 ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ (2 * ε) := by
    have h1 : ((p : ℝ) ^ (1 + ε)) ^ 2 = (p : ℝ) ^ 2 * (p : ℝ) ^ (2 * ε) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (1 + ε)) 2, ← Real.rpow_mul hp0.le,
        ← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_add hp0]
      push_cast; ring_nf
    rw [← h1]
    exact pow_le_pow_left₀ hDpos.le (by linarith) 2
  have hpow : (p : ℝ) ^ (2 * ε) ≤ p := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p) (by linarith : 2 * ε ≤ 1)
    rwa [Real.rpow_one] at this
  have hpe2 : 0 < (p : ℝ) ^ (2 * ε) := Real.rpow_pos_of_pos hp0 _
  rw [hJ, hw]
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  -- `(p² - 1)/(p^{1+ε} - 1)² ≥ (p² - 1)/(p² p^{2ε}) ≥ (3/4)/p`
  calc 3 / 4 * ρ ^ 2 * (1 / (p : ℝ))
      ≤ ρ ^ 2 * (((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ 2 * (p : ℝ) ^ (2 * ε))) := by
        rw [mul_comm (3 / 4 : ℝ), mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hρ2
        have h1 : ((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ 2 * p) ≤
            ((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ 2 * (p : ℝ) ^ (2 * ε)) :=
          div_le_div_of_nonneg_left (by nlinarith) (by positivity)
            (mul_le_mul_of_nonneg_left hpow (by positivity))
        have h2 : 3 / 4 * (1 / (p : ℝ)) ≤ ((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ 2 * p) := by
          rw [show (3 : ℝ) / 4 * (1 / p) = 3 / (4 * p) by ring,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
    _ ≤ ρ ^ 2 * (((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ (1 + ε) - 1) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by nlinarith) (by positivity)
          hsq) hρ2
    _ = ((p : ℝ) ^ 2 - 1) * (ρ ^ 2 / ((p : ℝ) ^ (1 + ε) - 1) ^ 2) := by ring

/-- **Divergence at and below one half.** For `0 < ε ≤ 1/2` the primitive energy of the damped
row tends to infinity. -/
theorem tendsto_sievePrimitiveEnergy_pmPowerDamped_atTop {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Tendsto (fun N : ℕ => sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)) atTop atTop := by
  set ρ := (RHTower.pmPowerDampedDivisorDensity ε).re
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  -- prime partial sums of the limit modes diverge
  set f : ℕ → ℝ := {p : ℕ | p.Prime}.indicator fun n => 1 / (n : ℝ)
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [f, Set.indicator]; split_ifs <;> positivity
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  set G : ℕ → ℝ := fun X => ∑ p ∈ (range X).filter Nat.Prime,
    jordanTotient2 p * dampedRamanujanCoeff ε p ^ 2
  have hGlow : ∀ X, 3 / 4 * ρ ^ 2 * ∑ n ∈ range X, f n ≤ G X := by
    intro X
    rw [mul_sum]
    calc ∑ n ∈ range X, 3 / 4 * ρ ^ 2 * f n
        = ∑ p ∈ (range X).filter Nat.Prime, 3 / 4 * ρ ^ 2 * (1 / (p : ℝ)) := by
          rw [sum_filter]
          refine sum_congr rfl fun n _ => ?_
          simp only [f, Set.indicator, Set.mem_setOf_eq]
          split_ifs <;> simp
      _ ≤ G X := sum_le_sum fun p hp => prime_mode_ge hε hε2 (mem_filter.mp hp).2
  have hG : Tendsto G atTop atTop :=
    tendsto_atTop_mono hGlow (Tendsto.const_mul_atTop (by positivity) hdiv)
  rw [tendsto_atTop]
  intro K
  obtain ⟨X, hX⟩ := (hG.eventually_gt_atTop (12 * K + 1)).exists
  -- the finitely many prime modes below `X` converge
  have hfin : Tendsto (fun N : ℕ => ∑ p ∈ (range X).filter Nat.Prime,
      jordanTotient2 p * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) p ^ 2) atTop (𝓝 (G X)) :=
    tendsto_finsetSum _ fun p hp =>
      ((tendsto_selbergMultiplesCoord_pmPowerDamped hε (e := p)
        (mem_filter.mp hp).2.pos).pow 2).const_mul _
  filter_upwards [hfin.eventually (eventually_gt_nhds hX), eventually_ge_atTop X] with N hN hNX
  have hsub : (range X).filter Nat.Prime ⊆ Icc 2 N := fun p hp => by
    obtain ⟨hpX, hpp⟩ := mem_filter.mp hp
    simp only [mem_range] at hpX
    simp only [mem_Icc]; exact ⟨hpp.two_le, by omega⟩
  have hle : ∑ p ∈ (range X).filter Nat.Prime,
      jordanTotient2 p * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) p ^ 2 ≤
      12 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) := by
    rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
    exact sum_le_sum_of_subset_of_nonneg hsub fun q _ _ =>
      mul_nonneg (jordanTotient2_nonneg q) (sq_nonneg _)
  linarith

/-! ### The Möbius row -/

/-- **Linear growth for the Möbius row.** At all large horizons
`⌊N/2⌋ ≤ 3456 E_prim(N; μ)`: the top octave forces the discrepancy energy up linearly. -/
theorem eventually_sievePrimitiveEnergy_moebius_ge :
    ∀ᶠ N : ℕ in atTop, ((N / 2 : ℕ) : ℝ) ≤ 3456 * sievePrimitiveEnergy N moebiusReal := by
  have hD : (1 : ℝ) / 3 < RHTower.Sieve.squarefreeDensity * 2 / 3 := by
    rw [RHTower.Sieve.squarefreeDensity_eq]
    have hpi : Real.pi ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h6 : (1 : ℝ) / 2 < 6 / Real.pi ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  have hcount := (tendsto_oddSquarefreeWindow_card_div.eventually (eventually_gt_nhds hD)).and
    (eventually_gt_atTop 0)
  filter_upwards [(Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually hcount]
    with N ⟨hW, hM⟩
  set M := N / 2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hWc : (M : ℝ) / 3 ≤ (oddSquarefreeWindow M).card := by
    rw [lt_div_iff₀ hMR] at hW; linarith
  have hinv : (1 : ℝ) / 6 ≤ ∑ e ∈ oddSquarefreeWindow M, (1 : ℝ) / e := by
    calc (1 : ℝ) / 6 ≤ (oddSquarefreeWindow M).card * (1 / (2 * M)) := by
          rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
      _ = ∑ e ∈ oddSquarefreeWindow M, (1 : ℝ) / (2 * M) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ oddSquarefreeWindow M, (1 : ℝ) / e := by
          refine sum_le_sum fun e he => ?_
          simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
          have h1 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
          have h2 : (e : ℝ) ≤ 2 * M := by exact_mod_cast he.1.2
          exact one_div_le_one_div_of_le h1 h2
  have hcs := sq_sum_inv_window_le M
  -- on the window the Jordan modes carry at least `M φ(e)/e²`
  have hwin : (M : ℝ) * ∑ e ∈ oddSquarefreeWindow M, (Nat.totient e : ℝ) / (e : ℝ) ^ 2 ≤
      12 * sievePrimitiveEnergy N moebiusReal := by
    rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal, mul_sum]
    have hsub : oddSquarefreeWindow M ⊆ Icc 2 N := fun e he => by
      simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
      simp only [mem_Icc]; omega
    refine le_trans (sum_le_sum fun e he => ?_) (sum_le_sum_of_subset_of_nonneg hsub
      fun q _ _ => mul_nonneg (jordanTotient2_nonneg q) (sq_nonneg _))
    simp only [oddSquarefreeWindow, mem_filter, mem_Ioc] at he
    obtain ⟨⟨h1, h2⟩, -, hsq⟩ := he
    have he0 : 0 < e := by omega
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have hNe : N / e = 1 := by
      have h1' : N / e < 2 := (Nat.div_lt_iff_lt_mul he0).mpr (by omega)
      have h2' : 1 ≤ N / e := (Nat.le_div_iff_mul_le he0).mpr (by omega)
      omega
    have hμ : moebiusReal e ^ 2 = 1 := by
      unfold moebiusReal
      have h1 : |(μ e : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
      rw [← sq_abs, h1]; norm_num
    have hm1 : coprimeHarmonicMoebius e 1 = 1 := by simp [coprimeHarmonicMoebius, moebiusReal]
    have hY : selbergMultiplesCoord N moebiusReal e ^ 2 = 1 / (e : ℝ) ^ 2 := by
      rw [selbergMultiplesCoord_moebiusReal_sq, hNe, hm1, hμ]; ring
    have hJ := jordanTotient2_ge_mul_totient e
    have hMe : (M : ℝ) ≤ e := by exact_mod_cast h1.le
    rw [hY]
    calc (M : ℝ) * ((Nat.totient e : ℝ) / (e : ℝ) ^ 2)
        ≤ (e : ℝ) * ((Nat.totient e : ℝ) / (e : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hMe (by positivity)
      _ ≤ jordanTotient2 e * (1 / (e : ℝ) ^ 2) := by
          rw [mul_one_div, mul_div_assoc']
          exact div_le_div_of_nonneg_right hJ (by positivity)
  have hφ : (1 : ℝ) / 288 ≤ ∑ e ∈ oddSquarefreeWindow M, (Nat.totient e : ℝ) / (e : ℝ) ^ 2 := by
    nlinarith
  nlinarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
