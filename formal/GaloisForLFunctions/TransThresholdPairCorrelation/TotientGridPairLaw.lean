import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import GaloisForLFunctions.RHTower.PMAdjacentDivisorCorrelation
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import GaloisForLFunctions.HTGeometry.EtemadiWeightedAverage

/-!
# Totient mixtures of equally spaced grids

Mix the uniform laws on the first `L` cyclic grids with weights `φ(m)/L²`,
and put the remaining weight on the grid of order `L+1`. Every Fourier
coefficient is nonnegative. The divisor identity for the totient gives the
exact coefficients `k/L²` for `1 ≤ k ≤ L`. The origin mass tends to
`1 + 3/π²`, strictly above `13/10`.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Weight assigned to the cyclic grid of order `m`. -/
def totientGridWeight (L m : ℕ) : ℝ := (Nat.totient m : ℝ) / (L : ℝ) ^ 2

/-- Unused probability mass is assigned to the next grid. -/
def totientGridRemainder (L : ℕ) : ℝ :=
  1 - ∑ m ∈ Icc 1 L, totientGridWeight L m

/-- Fourier coefficient of the finite mixture of cyclic grid laws. -/
def totientGridCoefficient (L k : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 L, if m ∣ k then totientGridWeight L m else 0) +
    if L + 1 ∣ k then totientGridRemainder L else 0

/-- Mass at the common origin after normalizing the period mass to `L`. -/
def totientGridOriginMass (L : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 L, (Nat.totient m : ℝ) / m) / L +
    (L : ℝ) / ((L : ℝ) + 1) * totientGridRemainder L

theorem totientGridWeight_nonneg (L m : ℕ) : 0 ≤ totientGridWeight L m :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem totientGridRemainder_nonneg {L : ℕ} (hL : 1 ≤ L) :
    0 ≤ totientGridRemainder L := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hsum : (∑ m ∈ Icc 1 L, (Nat.totient m : ℝ)) ≤ (L : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 L, (L : ℝ) := by
        apply sum_le_sum
        intro m hm
        exact_mod_cast (Nat.totient_le m).trans (mem_Icc.mp hm).2
      _ = (L : ℝ) ^ 2 := by simp [Nat.card_Icc, pow_two]
  unfold totientGridRemainder totientGridWeight
  rw [← sum_div]
  exact sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hLR)).mpr hsum)

theorem totientGridCoefficient_zero (L : ℕ) : totientGridCoefficient L 0 = 1 := by
  simp only [totientGridCoefficient, Nat.dvd_zero, ite_true, totientGridRemainder]
  ring

theorem totientGridCoefficient_nonneg {L : ℕ} (hL : 1 ≤ L) (k : ℕ) :
    0 ≤ totientGridCoefficient L k := by
  apply add_nonneg
  · apply sum_nonneg
    intro m hm
    split_ifs
    · exact totientGridWeight_nonneg L m
    · exact le_rfl
  · split_ifs
    · exact totientGridRemainder_nonneg hL
    · exact le_rfl

/-- Every low nonzero Fourier coefficient is exactly the linear ramp. -/
theorem totientGridCoefficient_eq_ramp {L k : ℕ} (hk : k ∈ Icc 1 L) :
    totientGridCoefficient L k = (k : ℝ) / (L : ℝ) ^ 2 := by
  have hk0 : 0 < k := (mem_Icc.mp hk).1
  have hnext : ¬L + 1 ∣ k := by
    intro h
    have hh := Nat.le_of_dvd hk0 h
    have := (mem_Icc.mp hk).2
    omega
  have hdiv : {m ∈ Icc 1 L | m ∣ k} = k.divisors := by
    ext m
    constructor
    · intro hm
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hm).2, Nat.ne_of_gt hk0⟩
    · intro hm
      have hmk := Nat.dvd_of_mem_divisors hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hm,
        (Nat.le_of_dvd hk0 hmk).trans (mem_Icc.mp hk).2⟩, hmk⟩
  unfold totientGridCoefficient
  rw [if_neg hnext, add_zero, ← sum_filter, hdiv]
  unfold totientGridWeight
  rw [← sum_div, ← Nat.cast_sum, Nat.sum_totient]

/-- The grid of order one supplies a strict positive margin at every frequency. -/
theorem one_div_sq_le_totientGridCoefficient {L : ℕ} (hL : 1 ≤ L) (k : ℕ) :
    1 / (L : ℝ) ^ 2 ≤ totientGridCoefficient L k := by
  have hterm (m : ℕ) (_ : m ∈ Icc 1 L) :
      0 ≤ if m ∣ k then totientGridWeight L m else 0 := by
    split_ifs
    · exact totientGridWeight_nonneg L m
    · exact le_rfl
  have hfirst := single_le_sum hterm (mem_Icc.mpr ⟨le_rfl, hL⟩ : 1 ∈ Icc 1 L)
  have hrest : 0 ≤ if L + 1 ∣ k then totientGridRemainder L else 0 := by
    split_ifs
    · exact totientGridRemainder_nonneg hL
    · exact le_rfl
  have hw1 : totientGridWeight L 1 = 1 / (L : ℝ) ^ 2 := by
    simp only [totientGridWeight, Nat.totient_one, Nat.cast_one]
  simp only [one_dvd, ite_true, hw1] at hfirst
  exact hfirst.trans (le_add_of_nonneg_right hrest)

/-- The proportion of reduced residue classes modulo `n`. -/
def totientRatio (n : ℕ) : ℝ := (Nat.totient n : ℝ) / n

def totientRatioSum (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, totientRatio n

theorem totientRatio_nonneg (n : ℕ) : 0 ≤ totientRatio n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem totientRatio_le_one (n : ℕ) : totientRatio n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [totientRatio, Nat.cast_zero, div_zero, zero_le_one]
  · apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    exact_mod_cast Nat.totient_le n

@[simp] theorem totientRatio_one : totientRatio 1 = 1 := by
  simp only [totientRatio, Nat.totient_one, Nat.cast_one, div_one]

/-- The Möbius divisor mean computes the mean reduced-residue proportion. -/
theorem tendsto_shifted_totientRatio_mean :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, totientRatio (n + 1)) / N)
      atTop (𝓝 (6 / Real.pi ^ 2)) := by
  have hc : Summable (fun m : ℕ => ((μ m : ℝ) / m) / m) := by
    simpa only [div_div, pow_two] using _root_.RHTower.hasSum_moebius_div_sq.summable
  have hdiv (n : ℕ) : (∑ m ∈ (n + 1).divisors, (μ m : ℝ) / m) =
      totientRatio (n + 1) :=
    _root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div (Nat.succ_pos n)
  have hval (m : ℕ) : ((μ m : ℝ) / m) *
      (if m.Coprime 1 then 1 / ((m : ℝ) * 1) else 0) = (μ m : ℝ) / (m : ℝ) ^ 2 := by
    simp [pow_two, div_eq_mul_inv, mul_inv_rev, mul_assoc]
  have h := _root_.RHTower.pm_divisor_progression_mean hc 1
  simpa only [Nat.cast_one, one_dvd, ite_true, hdiv, hval,
    _root_.RHTower.hasSum_moebius_div_sq.tsum_eq] using h

private theorem shifted_totientRatio_sum (N : ℕ) :
    (∑ n ∈ Icc 1 N, totientRatio (n + 1)) =
      totientRatioSum N + totientRatio (N + 1) - 1 := by
  induction N with
  | zero => simp [totientRatioSum]
  | succ N ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      unfold totientRatioSum
      rw [sum_Icc_succ_top (by omega)]
      ring

theorem tendsto_totientRatio_mean :
    Tendsto (fun N : ℕ => totientRatioSum N / N) atTop (𝓝 (6 / Real.pi ^ 2)) := by
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    convert tendsto_inv_atTop_zero.comp hcast using 1
    funext N
    simp only [one_div, Function.comp_apply]
  have herr : Tendsto (fun N : ℕ => (1 - totientRatio (N + 1)) / N) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun N => div_nonneg (sub_nonneg.mpr (totientRatio_le_one _)) (Nat.cast_nonneg N))
      (fun N => div_le_div_of_nonneg_right (sub_le_self 1 (totientRatio_nonneg _)) (Nat.cast_nonneg N))
      hinv
  have h := tendsto_shifted_totientRatio_mean.add herr
  simp only [add_zero] at h
  apply h.congr
  intro N
  rw [shifted_totientRatio_sum]
  ring

private theorem sum_range_succ_eq_sum_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ i ∈ Icc 1 N, f i := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

private theorem sum_linear_weights (N : ℕ) :
    (∑ i ∈ range N, ((i : ℝ) + 1)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Linear weighting of the reduced-residue mean gives the summatory totient constant. -/
theorem tendsto_sum_totient_div_sq :
    Tendsto (fun N : ℕ => (∑ m ∈ Icc 1 N, (Nat.totient m : ℝ)) / (N : ℝ) ^ 2)
      atTop (𝓝 (3 / Real.pi ^ 2)) := by
  let w : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hw (n : ℕ) : 0 < w n := by dsimp only [w]; positivity
  have hW (N : ℕ) : HTGeometry.Etemadi.totalWeight w N =
      (N : ℝ) * ((N : ℝ) + 1) / 2 := sum_linear_weights N
  have hWnonneg (N : ℕ) : 0 ≤ HTGeometry.Etemadi.totalWeight w N := by
    rw [hW]
    positivity
  have hWlim : Tendsto (HTGeometry.Etemadi.totalWeight w) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hcast.eventually (eventually_ge_atTop (max b 1))] with N hN
    have hNb : b ≤ (N : ℝ) := (le_max_left b 1).trans hN
    have hN1 : (1 : ℝ) ≤ N := (le_max_right b 1).trans hN
    rw [hW]
    have hmul := mul_le_mul_of_nonneg_left hN1 (zero_le_one.trans hN1)
    nlinarith only [hNb, hmul]
  have hK1 (N : ℕ) : (N : ℝ) * w (N - 1) ≤
      2 * HTGeometry.Etemadi.totalWeight w N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [HTGeometry.Etemadi.totalWeight]
    · have hpred : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
      rw [hW]
      dsimp only [w]
      rw [hpred]
      nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hK2 (N : ℕ) : HTGeometry.Etemadi.totalVar w N ≤
      2 * HTGeometry.Etemadi.totalWeight w N := by
    have hdiff (i : ℕ) : w (i + 1) - w i = 1 := by
      dsimp only [w]
      push_cast
      ring
    have hvar : HTGeometry.Etemadi.totalVar w N = HTGeometry.Etemadi.totalWeight w N := by
      simp only [HTGeometry.Etemadi.totalVar, hdiff, abs_one, mul_one,
        HTGeometry.Etemadi.totalWeight, w]
    rw [hvar]
    linarith only [hWnonneg N]
  have hx : Tendsto (fun N : ℕ =>
      HTGeometry.Etemadi.partialSum (fun n => totientRatio (n + 1)) N / N)
      atTop (𝓝 (6 / Real.pi ^ 2)) := by
    simpa only [HTGeometry.Etemadi.partialSum, sum_range_succ_eq_sum_Icc, totientRatioSum]
      using tendsto_totientRatio_mean
  have hweighted := HTGeometry.Etemadi.tendsto_weightedAverage hw hWlim hK1 hK2 hx
  have hnum (N : ℕ) : (∑ i ∈ range N, w i * totientRatio (i + 1)) =
      ∑ m ∈ Icc 1 N, (Nat.totient m : ℝ) := by
    calc
      _ = ∑ i ∈ range N, ((i + 1 : ℕ) : ℝ) * totientRatio (i + 1) := by
        apply sum_congr rfl
        intro i hi
        simp only [w, Nat.cast_add, Nat.cast_one]
      _ = ∑ m ∈ Icc 1 N, (m : ℝ) * totientRatio m :=
        sum_range_succ_eq_sum_Icc (fun m => (m : ℝ) * totientRatio m) N
      _ = _ := by
        apply sum_congr rfl
        intro m hm
        have hm0 : (m : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (mem_Icc.mp hm).1
        dsimp only [totientRatio]
        field_simp
  have hnmean : Tendsto (fun N : ℕ =>
      (∑ m ∈ Icc 1 N, (Nat.totient m : ℝ)) / HTGeometry.Etemadi.totalWeight w N)
      atTop (𝓝 (6 / Real.pi ^ 2)) := by
    simpa only [hnum] using hweighted
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    convert tendsto_inv_atTop_zero.comp hcast using 1
    funext N
    simp only [one_div, Function.comp_apply]
  have hfactor : Tendsto (fun N : ℕ => (1 + 1 / (N : ℝ)) / 2) atTop (𝓝 (1 / 2)) := by
    simpa only [add_zero] using (hinv.const_add 1).div_const 2
  have h := hnmean.mul hfactor
  rw [show (6 / Real.pi ^ 2) * (1 / 2) = 3 / Real.pi ^ 2 by ring] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  rw [hW]
  field_simp

/-- The origin mass of the explicit grid law tends to a value above the 70% threshold. -/
theorem tendsto_totientGridOriginMass :
    Tendsto totientGridOriginMass atTop (𝓝 (1 + 3 / Real.pi ^ 2)) := by
  have hrem : Tendsto totientGridRemainder atTop (𝓝 (1 - 3 / Real.pi ^ 2)) := by
    apply (tendsto_sum_totient_div_sq.const_sub 1).congr
    intro N
    unfold totientGridRemainder totientGridWeight
    rw [sum_div]
  have hfrac : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    have hi : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := hi.const_sub 1
    simp only [sub_zero] at h
    apply h.congr
    intro N
    have hn : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have h := tendsto_totientRatio_mean.add (hfrac.mul hrem)
  have hlim : 6 / Real.pi ^ 2 + 1 * (1 - 3 / Real.pi ^ 2) = 1 + 3 / Real.pi ^ 2 := by ring
  rw [hlim] at h
  exact h.congr (fun N => rfl)

theorem eventually_totientGridOriginMass_gt :
    ∀ᶠ L : ℕ in atTop, 13 / 10 < totientGridOriginMass L := by
  have hπ : Real.pi ^ 2 < 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
  have hπ0 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hfrac : (3 : ℝ) / 10 < 3 / Real.pi ^ 2 := by
    apply (lt_div_iff₀ hπ0).mpr
    nlinarith only [hπ]
  exact tendsto_totientGridOriginMass.eventually (Ioi_mem_nhds (by linarith only [hfrac]))

/-- Exact grid laws with origin mass above `13/10` exist beyond every cutoff. -/
theorem exists_totientGridOriginMass_gt (N₀ : ℕ) :
    ∃ L : ℕ, max 1 N₀ ≤ L ∧ 13 / 10 < totientGridOriginMass L := by
  exact ((eventually_ge_atTop (max 1 N₀)).and eventually_totientGridOriginMass_gt).exists

end GaloisForLFunctions.TransThresholdPairCorrelation
