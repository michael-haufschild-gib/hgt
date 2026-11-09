import GaloisForLFunctions.RHTower.PrimePowerSumBound
import GaloisForLFunctions.RHTower.Sieve.PrimeCountRelativeWindow
import GaloisForLFunctions.PNTPlus.Consequences
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Prime mass in a logarithmic comb

The prime number theorem determines the logarithmic mass in all geometric
windows simultaneously. A summable geometric majorant controls the infinite
tail. At phase-aligned cutoffs these windows give actual prime subsets which
return at height one, with an exact limiting fraction of Chebyshev mass.
-/

open Filter Topology Real Finset

namespace GaloisForLFunctions.CollectiveDiophantineGeometry

noncomputable section

/-- Sum of logarithmic prime masses over the geometric windows `(rxqʲ,xqʲ]`. -/
def geometricPrimeMass (q r x : ℝ) : ℝ :=
  ∑' j : ℕ, (Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j)))

private theorem theta_below_one {x : ℝ} (hx : x < 1) : Chebyshev.theta x = 0 := by
  simp [Chebyshev.theta, Nat.floor_eq_zero.mpr hx]

private theorem theta_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → Chebyshev.theta x ≤ C * x := by
  obtain ⟨C, hC, h⟩ := RHTower.exists_chebyshevTheta_le_linear
  refine ⟨C, hC, fun x hx => ?_⟩
  rcases le_or_gt 1 x with h1 | h1
  · exact h x h1
  · rw [theta_below_one h1]
    exact mul_nonneg hC.le hx

private theorem theta_ratio_limit :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hne : ∀ᶠ x : ℝ in atTop, x ≠ 0 :=
    (eventually_gt_atTop 0).mono fun _ hx => hx.ne'
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp chebyshev_asymptotic

private theorem scaled_theta_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Chebyshev.theta (x * c) / x) atTop (𝓝 c) := by
  have h := (theta_ratio_limit.comp (Filter.Tendsto.atTop_mul_const hc tendsto_id)).mul_const c
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp
  field_simp [hx.ne', hc.ne']

/-- Exact mass of the infinite comb, with no restriction on the number of windows. -/
theorem geometricPrimeMass_ratio_limit {q r : ℝ}
    (hq : 0 < q) (hqr : q < r) (hr : r < 1) :
    Tendsto (fun x : ℝ => geometricPrimeMass q r x / x) atTop
      (𝓝 ((1 - r) / (1 - q))) := by
  have hr0 : 0 < r := hq.trans hqr
  have hq1 : q < 1 := hqr.trans hr
  obtain ⟨C, hC0, hC⟩ := theta_linear
  have hs : Summable (fun j : ℕ => C * q ^ j) :=
    (summable_geometric_of_lt_one hq.le hq1).mul_left C
  have hterm (j : ℕ) :
      Tendsto (fun x : ℝ =>
        (Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j))) / x)
        atTop (𝓝 ((1 - r) * q ^ j)) := by
    have h := (scaled_theta_limit (pow_pos hq j)).sub
      (scaled_theta_limit (mul_pos hr0 (pow_pos hq j)))
    have heq : q ^ j - r * q ^ j = (1 - r) * q ^ j := by ring
    simpa only [← sub_div, heq] using h
  have hb : ∀ᶠ x : ℝ in atTop, ∀ j : ℕ,
      ‖(Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j))) / x‖
        ≤ C * q ^ j := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx j
    have hnonneg : 0 ≤ Chebyshev.theta (x * q ^ j) -
        Chebyshev.theta (x * (r * q ^ j)) := by
      apply sub_nonneg.mpr
      apply RHTower.chebyshevTheta_mono
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (pow_nonneg hq.le j) hr.le) hx.le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnonneg hx.le)]
    apply (div_le_iff₀ hx).mpr
    calc
      Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j))
          ≤ Chebyshev.theta (x * q ^ j) :=
        sub_le_self _ (RHTower.chebyshevTheta_nonneg _)
      _ ≤ C * (x * q ^ j) := hC _ (mul_nonneg hx.le (pow_nonneg hq.le j))
      _ = C * q ^ j * x := by ring
  have h := tendsto_tsum_of_dominated_convergence hs hterm hb
  simpa only [geometricPrimeMass, tsum_div_const, tsum_mul_left,
    tsum_geometric_of_lt_one hq.le hq1, ← div_eq_mul_inv] using h

/-- The first `N+1` geometric windows, as a finite set of primes. -/
def primeComb (q r x : ℝ) (N : ℕ) : Finset ℕ :=
  (range (N + 1)).biUnion fun j =>
    RHTower.Sieve.primesIn (x * (r * q ^ j)) (x * q ^ j)

private theorem primeWindows_disjoint {q r x : ℝ}
    (hq : 0 < q) (hqr : q < r) (hr : r < 1) (hx : 0 < x)
    {j k : ℕ} (hjk : j < k) :
    Disjoint (RHTower.Sieve.primesIn (x * (r * q ^ j)) (x * q ^ j))
      (RHTower.Sieve.primesIn (x * (r * q ^ k)) (x * q ^ k)) := by
  have hr0 : 0 < r := hq.trans hqr
  refine Finset.disjoint_left.mpr fun p hpj hpk => ?_
  have hj := RHTower.Sieve.mem_primesIn (by positivity) hpj
  have hk := RHTower.Sieve.mem_primesIn (by positivity) hpk
  have hgap : x * q ^ k < x * (r * q ^ j) := by
    calc
      x * q ^ k ≤ x * q ^ (j + 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hq.le (hqr.trans hr).le hjk) hx.le
      _ = x * (q * q ^ j) := by rw [pow_succ]; ring
      _ < x * (r * q ^ j) := mul_lt_mul_of_pos_left
        (mul_lt_mul_of_pos_right hqr (pow_pos hq j)) hx
  exact lt_asymm hgap (hj.2.1.trans_le hk.2.2)

private theorem primeComb_mass {q r x : ℝ}
    (hq : 0 < q) (hqr : q < r) (hr : r < 1) (hx : 0 < x) (N : ℕ) :
    (∑ p ∈ primeComb q r x N, log (p : ℝ)) =
      ∑ j ∈ range (N + 1),
        (Chebyshev.theta (x * q ^ j) - Chebyshev.theta (x * (r * q ^ j))) := by
  have hd : (↑(range (N + 1)) : Set ℕ).PairwiseDisjoint
      (fun j => RHTower.Sieve.primesIn (x * (r * q ^ j)) (x * q ^ j)) := by
    intro j hj k hk hne
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · exact primeWindows_disjoint hq hqr hr hx hjk
    · exact (primeWindows_disjoint hq hqr hr hx hkj).symm
  rw [primeComb, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro j hj
  symm
  apply RHTower.Sieve.theta_sub_theta_eq_sum_primesIn
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (pow_nonneg hq.le j) hr.le) hx.le

/-- Cutoffs aligned with the right edge of a return window at height one. -/
def alignedCutoff (δ : ℝ) (N : ℕ) : ℝ := exp (2 * π * N + δ)

/-- Prime windows with phase error between `-δ` and `δ` at height one. -/
def returningPrimeComb (δ : ℝ) (N : ℕ) : Finset ℕ :=
  primeComb (exp (-2 * π)) (exp (-2 * δ)) (alignedCutoff δ N) N

private theorem alignedCutoff_pos (δ : ℝ) (N : ℕ) : 0 < alignedCutoff δ N :=
  exp_pos _

private theorem returnRatio_lt {δ : ℝ} (hδ : δ < 1) :
    exp (-2 * π) < exp (-2 * δ) := by
  apply Real.exp_lt_exp.mpr
  linarith [Real.pi_gt_three]

private theorem returnRatio_lt_one {δ : ℝ} (hδ : 0 < δ) : exp (-2 * δ) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  linarith

private theorem comb_upper_endpoint (δ : ℝ) (N j : ℕ) :
    alignedCutoff δ N * exp (-2 * π) ^ j = exp (2 * π * ((N : ℝ) - j) + δ) := by
  rw [alignedCutoff, ← exp_nat_mul, ← exp_add]
  congr 1
  ring

private theorem comb_lower_endpoint (δ : ℝ) (N j : ℕ) :
    alignedCutoff δ N * (exp (-2 * δ) * exp (-2 * π) ^ j) =
      exp (2 * π * ((N : ℝ) - j) - δ) := by
  rw [alignedCutoff, ← exp_nat_mul, ← exp_add, ← exp_add]
  congr 1
  ring

private theorem comb_tail_zero {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (N j : ℕ) (hj : N < j) :
    Chebyshev.theta (alignedCutoff δ N * exp (-2 * π) ^ j) -
      Chebyshev.theta (alignedCutoff δ N * (exp (-2 * δ) * exp (-2 * π) ^ j)) = 0 := by
  have hcast : (N : ℝ) + 1 ≤ j := by exact_mod_cast hj
  have hdiff : (N : ℝ) - j ≤ -1 := by linarith
  have hexp : 2 * π * ((N : ℝ) - j) + δ < 0 := by
    have h := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 2 * π)
    linarith [Real.pi_gt_three]
  have hu : alignedCutoff δ N * exp (-2 * π) ^ j < 1 := by
    rw [comb_upper_endpoint]
    exact Real.exp_lt_one_iff.mpr hexp
  have hl : alignedCutoff δ N * (exp (-2 * δ) * exp (-2 * π) ^ j) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (by positivity) (returnRatio_lt_one hδ0).le)
      (alignedCutoff_pos δ N).le) hu
  rw [theta_below_one hu, theta_below_one hl, sub_self]

private theorem geometricPrimeMass_eq_returningComb {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (N : ℕ) :
    geometricPrimeMass (exp (-2 * π)) (exp (-2 * δ)) (alignedCutoff δ N) =
      ∑ p ∈ returningPrimeComb δ N, log (p : ℝ) := by
  unfold geometricPrimeMass returningPrimeComb
  rw [tsum_eq_sum (s := range (N + 1)) (fun j hj =>
    comb_tail_zero hδ0 hδ1 N j (by simp only [mem_range] at hj; omega))]
  exact (primeComb_mass (exp_pos _) (returnRatio_lt hδ1)
    (returnRatio_lt_one hδ0) (alignedCutoff_pos δ N) N).symm

/-- Every selected prime returns at height one, in the original radian convention. -/
theorem mem_returningPrimeComb {δ : ℝ} (N : ℕ) {p : ℕ}
    (hp : p ∈ returningPrimeComb δ N) :
    p.Prime ∧ (p : ℝ) ≤ alignedCutoff δ N ∧
      ∃ m : ℤ, |log (p : ℝ) - 2 * π * m| ≤ δ := by
  have hx := alignedCutoff_pos δ N
  rcases mem_biUnion.mp hp with ⟨j, hj, hpj⟩
  have hm := RHTower.Sieve.mem_primesIn (by positivity) hpj
  have hq : exp (-2 * π) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  have hpow : exp (-2 * π) ^ j ≤ 1 := by
    simpa only [pow_zero] using pow_le_pow_of_le_one (exp_pos (-2 * π)).le hq
      (Nat.zero_le j)
  have hup : (p : ℝ) ≤ alignedCutoff δ N :=
    hm.2.2.trans (mul_le_of_le_one_right (alignedCutoff_pos δ N).le hpow)
  refine ⟨hm.1, hup, (N : ℤ) - j, ?_⟩
  have hlo := Real.log_lt_log (by positivity) hm.2.1
  have hhi := Real.log_le_log (by exact_mod_cast hm.1.pos) hm.2.2
  rw [comb_lower_endpoint, log_exp] at hlo
  rw [comb_upper_endpoint, log_exp] at hhi
  rw [abs_le]
  push_cast
  constructor <;> linarith

/-- The aligned cutoffs tend to infinity. -/
theorem alignedCutoff_atTop (δ : ℝ) :
    Tendsto (alignedCutoff δ) atTop atTop := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hm := Filter.Tendsto.const_mul_atTop (show 0 < 2 * π by positivity) hn
  have ha : Tendsto (fun N : ℕ => 2 * π * N + δ) atTop atTop :=
    tendsto_atTop_add_const_right atTop δ hm
  exact Real.tendsto_exp_atTop.comp ha

/-- Exact returning logarithmic prime mass along an unbounded sequence of cutoffs. -/
theorem returningPrimeComb_mass_limit {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ returningPrimeComb δ N, log (p : ℝ)) / Chebyshev.theta (alignedCutoff δ N))
      atTop (𝓝 ((1 - exp (-2 * δ)) / (1 - exp (-2 * π)))) := by
  have hnum := (geometricPrimeMass_ratio_limit (exp_pos (-2 * π))
    (returnRatio_lt hδ1) (returnRatio_lt_one hδ0)).comp (alignedCutoff_atTop δ)
  simp only [Function.comp_def, geometricPrimeMass_eq_returningComb hδ0 hδ1] at hnum
  have hden := theta_ratio_limit.comp (alignedCutoff_atTop δ)
  have h := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  convert h using 1
  ext N
  exact (div_div_div_cancel_right₀ (alignedCutoff_pos δ N).ne' _ _).symm

/-- Below the exact comb mass, no lower bound tending to infinity can hold for
all returning subsets of the required logarithmic mass. The witnesses return
at height one and have arbitrarily large prime cutoffs. -/
theorem arbitrarily_large_heavy_returns_at_one {δ β : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hβ : β < (1 - exp (-2 * δ)) / (1 - exp (-2 * π))) (Y : ℝ) :
    ∃ x : ℝ, Y ≤ x ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ x ∧
        ∃ m : ℤ, |log (p : ℝ) - 2 * π * m| ≤ δ) ∧
      β * Chebyshev.theta x < ∑ p ∈ P, log (p : ℝ) := by
  have hm := (returningPrimeComb_mass_limit hδ0 hδ1).eventually (Ioi_mem_nhds hβ)
  have hx := (alignedCutoff_atTop δ).eventually (eventually_ge_atTop Y)
  have ht := (theta_ratio_limit.comp (alignedCutoff_atTop δ)).eventually
    (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN, hYN, hθN⟩ := (hm.and (hx.and ht)).exists
  have hθ : 0 < Chebyshev.theta (alignedCutoff δ N) := by
    have h := (lt_div_iff₀ (alignedCutoff_pos δ N)).mp hθN
    simpa only [zero_mul] using h
  refine ⟨alignedCutoff δ N, hYN, returningPrimeComb δ N, ?_, ?_⟩
  · exact fun p hp => mem_returningPrimeComb N hp
  · exact (lt_div_iff₀ hθ).mp hN

private theorem half_lt_comb_mass :
    (1 / 2 : ℝ) < (1 - exp (-2 * (1 / 2 : ℝ))) / (1 - exp (-2 * π)) := by
  have he := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  have he' := mul_lt_mul_of_pos_right he (exp_pos (-1))
  rw [← exp_add] at he'
  norm_num at he'
  have hq : exp (-2 * π) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  apply (lt_div_iff₀ (sub_pos.mpr hq)).mpr
  norm_num
  linarith only [he', exp_pos (-(2 * π))]

/-- A half-mass subset can return at height one with half-radian error,
even as the cutoff tends to infinity. -/
theorem arbitrarily_large_half_mass_returns (Y : ℝ) :
    ∃ x : ℝ, Y ≤ x ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ x ∧
        ∃ m : ℤ, |log (p : ℝ) - 2 * π * m| ≤ 1 / 2) ∧
      Chebyshev.theta x / 2 < ∑ p ∈ P, log (p : ℝ) := by
  simpa only [one_div_mul_eq_div] using
    arbitrarily_large_heavy_returns_at_one (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) half_lt_comb_mass Y

end

end GaloisForLFunctions.CollectiveDiophantineGeometry
