import GaloisForLFunctions.SelbergClass.Primon.AveragedExplicitFormula
import GaloisForLFunctions.RHTower.PrimeHigherMertens
import GaloisForLFunctions.RHTower.MertensFirst
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The exact logarithmic correction to averaged prime-power mass

Split the tower deficit at `sqrt(N)`. Above this threshold the exponent is
one, so the contribution is the difference of two Mertens sums. Below it,
the terms are bounded by the summable sequence `log(p)/p²` and tend
pointwise to zero. The common Mertens constants cancel, giving
`θ(N) - A(N) - log(N)/2 → 0`. At a real cutoff `x`, this is the additive
correction `log(x)/4` to `θ(sqrt(x))`.
-/

open Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The deficit contributed by primes with at least two powers below the square-root cutoff. -/
def averagedSmallPrimeDefect (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE N).filter (fun p => p ^ 2 ≤ N),
    Real.log p / (p : ℝ) ^ Nat.log p N

private def smallPrimeDefectTerm (N p : ℕ) : ℝ :=
  if p.Prime ∧ p ^ 2 ≤ N then Real.log p / (p : ℝ) ^ Nat.log p N else 0

private theorem smallPrimeDefectTerm_nonneg (N p : ℕ) : 0 ≤ smallPrimeDefectTerm N p := by
  unfold smallPrimeDefectTerm
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  · exact le_rfl

private theorem smallPrimeDefectTerm_le (N p : ℕ) :
    smallPrimeDefectTerm N p ≤ Real.log p / (p : ℝ) ^ 2 := by
  unfold smallPrimeDefectTerm
  split_ifs with h
  · have hN : N ≠ 0 := ne_of_gt (lt_of_lt_of_le (pow_pos h.1.pos 2) h.2)
    have he : 2 ≤ Nat.log p N := (Nat.le_log_iff_pow_le h.1.one_lt hN).mpr h.2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.1.one_lt.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast h.1.pos
    exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (pow_pos hp0 2)
      (pow_le_pow_right₀ hp1 he)
  · exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)

private theorem smallPrimeDefectTerm_tendsto (p : ℕ) :
    Tendsto (fun N => smallPrimeDefectTerm N p) atTop (𝓝 0) := by
  by_cases hp : p.Prime
  · have hl : Tendsto (fun N => Nat.log p N) atTop atTop := by
      apply tendsto_atTop.mpr
      intro M
      filter_upwards [eventually_ge_atTop (p ^ M)] with N hN
      exact (Nat.le_log_iff_pow_le hp.one_lt
        (ne_of_gt (lt_of_lt_of_le (pow_pos hp.pos M) hN))).mpr hN
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr hp0.le) ((inv_lt_one₀ hp0).mpr hp1)).comp hl
    have h := hg.const_mul (Real.log p)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (p ^ 2)] with N hN
    simp only [Function.comp_apply, smallPrimeDefectTerm, hp, hN, and_self, ite_true,
      div_eq_mul_inv, inv_pow]
  · simp only [smallPrimeDefectTerm, hp, false_and, ite_false]
    exact tendsto_const_nhds

private theorem averagedSmallPrimeDefect_eq_tsum (N : ℕ) :
    averagedSmallPrimeDefect N = ∑' p, smallPrimeDefectTerm N p := by
  rw [tsum_eq_sum (s := Nat.primesLE N) (fun p hp => ?_)]
  · rw [averagedSmallPrimeDefect, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [smallPrimeDefectTerm, (Nat.mem_primesLE.mp hp).2, true_and]
  · by_cases h : p.Prime ∧ p ^ 2 ≤ N
    · exact False.elim (hp (Nat.mem_primesLE.mpr
        ⟨(Nat.le_pow (by decide : 0 < 2)).trans h.2, h.1⟩))
    · exact if_neg h

/-- The residual deficit below the square-root prime threshold tends to zero absolutely. -/
theorem tendsto_averagedSmallPrimeDefect :
    Tendsto averagedSmallPrimeDefect atTop (𝓝 0) := by
  have hs : Summable (fun p : ℕ => Real.log p / (p : ℝ) ^ 2) := by
    simpa only [Real.rpow_natCast] using
      (RHTower.Mertens.summable_log_div_rpow (s := (2 : ℕ)) (by norm_num))
  have h := tendsto_tsum_of_dominated_convergence hs smallPrimeDefectTerm_tendsto
    (Eventually.of_forall fun N p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (smallPrimeDefectTerm_nonneg N p)]
      exact smallPrimeDefectTerm_le N p)
  simpa only [← averagedSmallPrimeDefect_eq_tsum, tsum_zero] using h

private theorem primeLogPowSum_one_eq (x : ℝ) :
    RHTower.primeLogPowSum 1 x =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / (p : ℝ) := by
  have he : (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime = Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and, Nat.mem_primesLE]
  simp only [RHTower.primeLogPowSum, RHTower.primeLogPowWeight, pow_one]
  rw [← Finset.sum_filter, he]

private theorem primesLE_filter_square (N : ℕ) :
    (Nat.primesLE N).filter (fun p => p ^ 2 ≤ N) = Nat.primesLE ⌊Real.sqrt N⌋₊ := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_, hp⟩, hpN⟩
    refine ⟨(Nat.le_floor_iff (Real.sqrt_nonneg (N : ℝ))).mpr ?_, hp⟩
    exact (Real.le_sqrt (Nat.cast_nonneg p) (Nat.cast_nonneg N)).mpr (by exact_mod_cast hpN)
  · rintro ⟨hpN, hp⟩
    have hreal := (Nat.le_floor_iff (Real.sqrt_nonneg (N : ℝ))).mp hpN
    have hsq : p ^ 2 ≤ N := by
      exact_mod_cast (Real.le_sqrt (Nat.cast_nonneg p) (Nat.cast_nonneg N)).mp hreal
    exact ⟨⟨(Nat.le_pow (by decide : 0 < 2)).trans hsq, hp⟩, hsq⟩

/-- The deficit is a Mertens shell plus the vanishing small-prime residual. -/
theorem averagedPrimePowerDefect_eq_mertens_difference (N : ℕ) :
    averagedPrimePowerDefect N =
      RHTower.primeLogPowSum 1 N - RHTower.primeLogPowSum 1 (Real.sqrt N) +
        averagedSmallPrimeDefect N := by
  have ht : (∑ p ∈ (Nat.primesLE N).filter (fun p => ¬p ^ 2 ≤ N),
      Real.log p / (p : ℝ) ^ Nat.log p N) =
      ∑ p ∈ (Nat.primesLE N).filter (fun p => ¬p ^ 2 ≤ N), Real.log p / (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hmem, hsq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hmem
    have hN : N ≠ 0 := ne_of_gt (lt_of_lt_of_le hprime.pos hpN)
    have h1 : 1 ≤ Nat.log p N := Nat.log_pos_iff.mpr ⟨hpN, hprime.one_lt⟩
    have h2 : Nat.log p N < 2 :=
      (Nat.log_lt_iff_lt_pow hprime.one_lt hN).mpr (lt_of_not_ge hsq)
    rw [show Nat.log p N = 1 by omega, pow_one]
  have hd := Finset.sum_filter_add_sum_filter_not (Nat.primesLE N)
    (fun p => p ^ 2 ≤ N) (fun p => Real.log p / (p : ℝ) ^ Nat.log p N)
  change averagedSmallPrimeDefect N + _ = averagedPrimePowerDefect N at hd
  rw [ht] at hd
  have hh := Finset.sum_filter_add_sum_filter_not (Nat.primesLE N)
    (fun p => p ^ 2 ≤ N) (fun p => Real.log p / (p : ℝ))
  have hsmall : (∑ p ∈ (Nat.primesLE N).filter (fun p => p ^ 2 ≤ N),
      Real.log p / (p : ℝ)) = RHTower.primeLogPowSum 1 (Real.sqrt N) := by
    rw [primesLE_filter_square, primeLogPowSum_one_eq]
  have hfull : (∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ)) =
      RHTower.primeLogPowSum 1 N := by rw [primeLogPowSum_one_eq, Nat.floor_natCast]
  rw [hsmall, hfull] at hh
  linarith only [hd, hh]

/-- The exact tower deficit equals one half-logarithm, with an error tending to zero. -/
theorem tendsto_averagedPrimePowerDefect_sub_halfLog :
    Tendsto (fun N : ℕ => averagedPrimePowerDefect N - Real.log N / 2) atTop (𝓝 0) := by
  have hm : Tendsto (fun x : ℝ => RHTower.primeLogPowSum 1 x - Real.log x) atTop
      (𝓝 (RHTower.mertensLogPowConstantFull 0)) := by
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add, pow_one, div_one] using
      RHTower.tendsto_primeLogPowSum_sub 0
  have h := ((hm.comp (tendsto_natCast_atTop_atTop (R := ℝ))).sub
    (hm.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))).add
      tendsto_averagedSmallPrimeDefect
  simp only [sub_self, add_zero] at h
  apply h.congr'
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [averagedPrimePowerDefect_eq_mertens_difference, Real.log_sqrt (Nat.cast_nonneg N)]
  ring

/-- The averaged staircase retains Chebyshev's mass with an exact asymptotic half-log correction. -/
theorem tendsto_theta_sub_averagedPrimePowerCount_sub_halfLog :
    Tendsto (fun N : ℕ => Chebyshev.theta N - averagedPrimePowerCount N - Real.log N / 2)
      atTop (𝓝 0) := by
  simp_rw [averagedPrimePowerCount_eq_theta_sub_defect,
    sub_sub_cancel]
  exact tendsto_averagedPrimePowerDefect_sub_halfLog

private theorem tendsto_log_floor_sqrt_sub_log_sqrt :
    Tendsto (fun x : ℝ => Real.log (⌊Real.sqrt x⌋₊ : ℝ) - Real.log (Real.sqrt x))
      atTop (𝓝 0) := by
  have hf : Tendsto (fun x : ℝ => ⌊Real.sqrt x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop
  have h := (Real.continuousAt_log one_ne_zero).tendsto.comp
    (tendsto_nat_floor_div_atTop.comp Real.tendsto_sqrt_atTop)
  simp only [Real.log_one] at h
  apply h.congr'
  filter_upwards [hf.eventually (eventually_ge_atTop 1), eventually_ge_atTop (1 : ℝ)] with x hN hx
  have hN0 : (⌊Real.sqrt x⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ⌊Real.sqrt x⌋₊ ≠ 0)
  have hs0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hx))
  exact Real.log_div hN0 hs0

/-- At the original real cutoff, the averaged arithmetic mass has an additive quarter-log correction. -/
theorem tendsto_theta_sqrt_sub_averagedExplicitFormulaMass_sub_quarterLog :
    Tendsto (fun x : ℝ => Chebyshev.theta (Real.sqrt x) - averagedExplicitFormulaMass x -
      Real.log x / 4) atTop (𝓝 0) := by
  have hf : Tendsto (fun x : ℝ => ⌊Real.sqrt x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop
  have h := (tendsto_averagedPrimePowerDefect_sub_halfLog.comp hf).add
    (tendsto_log_floor_sqrt_sub_log_sqrt.div_const 2)
  simp only [zero_div, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_apply]
  have ht : Chebyshev.theta (⌊Real.sqrt x⌋₊ : ℝ) = Chebyshev.theta (Real.sqrt x) := by
    simp only [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  rw [averagedExplicitFormulaMass, averagedPrimePowerCount_eq_theta_sub_defect, ht,
    Real.log_sqrt hx]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
