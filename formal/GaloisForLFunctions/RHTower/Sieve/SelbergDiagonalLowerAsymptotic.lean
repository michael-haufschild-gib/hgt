import GaloisForLFunctions.RHTower.Sieve.LcmQuadraticDiagonalization
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovWeight
import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientLogMean
import GaloisForLFunctions.RHTower.Sieve.SelbergInversion

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Multiples-coordinate in the Selberg diagonalization. -/
def selbergMultiplesInner (X : ℕ) (a : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 X).filter (fun m => e ∣ m), a m / (m : ℝ)

/-- Möbius inversion recovers the first coefficient from the multiples-coordinates. -/
theorem sum_moebius_mul_selbergMultiplesInner {X : ℕ} (hX : 1 ≤ X) (a : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 1 X, (μ e : ℝ) * selbergMultiplesInner X a e) = a 1 := by
  have hexpand : ∀ e ∈ Finset.Icc 1 X,
      (μ e : ℝ) * selbergMultiplesInner X a e =
        ∑ m ∈ (Finset.Icc 1 X).filter (fun m => e ∣ m),
          (μ e : ℝ) * (a m / (m : ℝ)) := by
    intro e he
    rw [selbergMultiplesInner, Finset.mul_sum]
  rw [Finset.sum_congr rfl hexpand]
  have hmem : ∀ (e m : ℕ),
      e ∈ Finset.Icc 1 X ∧ m ∈ (Finset.Icc 1 X).filter (fun m => e ∣ m) ↔
        e ∈ m.divisors ∧ m ∈ Finset.Icc 1 X := by
    intro e m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨he, hm, hem⟩
      exact ⟨⟨hem, (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)⟩, hm⟩
    · rintro ⟨⟨hem, hm0⟩, hm⟩
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos hem (Nat.pos_of_ne_zero hm0)
      have hemle : e ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hem
      exact ⟨Finset.mem_Icc.mpr ⟨hepos, hemle.trans (Finset.mem_Icc.mp hm).2⟩, hm, hem⟩
  rw [Finset.sum_comm' hmem]
  have hinner : ∀ m ∈ Finset.Icc 1 X,
      (∑ e ∈ m.divisors, (μ e : ℝ) * (a m / (m : ℝ))) =
        (a m / (m : ℝ)) * (if m = 1 then 1 else 0) := by
    intro m hm
    rw [← Finset.sum_mul, sum_divisors_moebius_real]
    ring
  rw [Finset.sum_congr rfl hinner]
  have h1mem : 1 ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨by omega, hX⟩
  rw [Finset.sum_eq_single_of_mem 1 h1mem]
  · norm_num
  · intro m hm hm1
    simp [hm1]

/-- Selberg's squarefree Cauchy lower bound for any finite coefficient vector. -/
theorem sq_div_sum_sqfreeTotientInv_le_totientDiagonal {X : ℕ} (hX : 1 ≤ X)
    (a : ℕ → ℝ) :
    (a 1) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e) ≤
      ∑ e ∈ Finset.Icc 1 X, (Nat.totient e : ℝ) * (selbergMultiplesInner X a e) ^ (2 : ℕ) := by
  let S := (Finset.Icc 1 X).filter Squarefree
  have hphi : ∀ e ∈ S, 0 < (1 / (Nat.totient e : ℝ)) := by
    intro e he
    have hepos : 0 < e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    have htot : 0 < Nat.totient e := Nat.totient_pos.mpr hepos
    positivity
  have hconstraint :
      (∑ e ∈ S, (μ e : ℝ) * selbergMultiplesInner X a e) = a 1 := by
    calc
      (∑ e ∈ S, (μ e : ℝ) * selbergMultiplesInner X a e) =
          ∑ e ∈ Finset.Icc 1 X, (μ e : ℝ) * selbergMultiplesInner X a e := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro e he heS
        have hnsq : ¬ Squarefree e := by
          intro hsq
          exact heS (Finset.mem_filter.mpr ⟨he, hsq⟩)
        rw [show (μ e : ℝ) = 0 by
          exact_mod_cast moebius_eq_zero_of_not_squarefree hnsq]
        simp
      _ = a 1 := sum_moebius_mul_selbergMultiplesInner hX a
  have hcs := Finset.sq_sum_div_le_sum_sq_div S
    (fun e => (μ e : ℝ) * selbergMultiplesInner X a e) hphi
  rw [hconstraint] at hcs
  have hdenom :
      (∑ e ∈ S, 1 / (Nat.totient e : ℝ)) =
        ∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e := by
    dsimp [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    rw [sqfreeTotientInv_apply]
  rw [hdenom] at hcs
  have hrhs :
      (∑ e ∈ S,
        ((μ e : ℝ) * selbergMultiplesInner X a e) ^ (2 : ℕ) /
          (1 / (Nat.totient e : ℝ))) =
        ∑ e ∈ S, (Nat.totient e : ℝ) * (selbergMultiplesInner X a e) ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro e he
    have hsq : Squarefree e := (Finset.mem_filter.mp he).2
    have hepos : 0 < e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    have htot : (Nat.totient e : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hepos).ne'
    have hmu : (μ e : ℝ) ^ (2 : ℕ) = 1 := by
      have h := ArithmeticFunction.moebius_sq (n := e)
      rw [if_pos hsq] at h
      exact_mod_cast h
    rw [mul_pow, hmu, one_mul]
    field_simp
  rw [hrhs] at hcs
  exact hcs.trans (by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro e he heS
    positivity)

/-! ### Sharp lower half of Graham's diagonal -/

/-- The diagonal quadratic form for the linear Barban--Vehov weight. -/
def barbanVehovSelbergDiagonal (X : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 X, (Nat.totient e : ℝ) *
    (selbergMultiplesInner X (barbanVehovWeight X) e) ^ (2 : ℕ)

theorem barbanVehovWeight_one {X : ℕ} (hX : 1 ≤ X) :
    barbanVehovWeight X 1 = Real.log X := by
  rw [barbanVehovWeight, if_pos hX]
  norm_num

/-- Exact Cauchy lower bound for the Barban--Vehov Selberg diagonal. -/
theorem sq_log_div_sum_sqfreeTotientInv_le_barbanVehovSelbergDiagonal
    {X : ℕ} (hX : 1 ≤ X) :
    (Real.log X) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e) ≤
      barbanVehovSelbergDiagonal X := by
  simpa [barbanVehovSelbergDiagonal, barbanVehovWeight_one hX] using
    sq_div_sum_sqfreeTotientInv_le_totientDiagonal hX (barbanVehovWeight X)

/-- The exact Selberg lower benchmark has normalized limit one. -/
theorem tendsto_barbanVehovSelbergLowerBenchmark_one :
    Tendsto
      (fun X : ℕ =>
        ((Real.log X) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e)) /
          Real.log X)
      atTop (𝓝 1) := by
  have hinv := tendsto_sum_sqfreeTotientInv_div_log_one.inv₀ one_ne_zero
  simpa only [inv_one] using hinv.congr' (by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hlog : Real.log X ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hX)).ne'
    field_simp)

/-- Sharp lower half of Graham's theorem in epsilon form. -/
theorem eventually_one_sub_le_barbanVehovSelbergDiagonal_div_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      1 - ε ≤ barbanVehovSelbergDiagonal X / Real.log X := by
  have hnear : ∀ᶠ X : ℕ in atTop,
      dist (((Real.log X) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e)) /
        Real.log X) 1 < ε :=
    tendsto_barbanVehovSelbergLowerBenchmark_one.eventually
      (Metric.ball_mem_nhds _ hε)
  filter_upwards [hnear, eventually_ge_atTop 2] with X hnearX hX
  have hlogpos : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hlower := sq_log_div_sum_sqfreeTotientInv_le_barbanVehovSelbergDiagonal
    (show 1 ≤ X by omega)
  have hdiv := div_le_div_of_nonneg_right hlower hlogpos.le
  rw [Real.dist_eq] at hnearX
  have habsLower : -ε <
      ((Real.log X) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e)) /
        Real.log X - 1 := (abs_lt.mp hnearX).1
  exact le_trans (by linarith) hdiv

end

end RHTower.Sieve
