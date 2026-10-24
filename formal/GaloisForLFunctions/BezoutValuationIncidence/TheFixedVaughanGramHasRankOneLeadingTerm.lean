import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanDiagonalContainsLinearPoleMass

/-!
# The leading matrix of the fixed-cutoff Vaughan Gram

At fixed cutoffs each Vaughan piece has a linear mean. The normalized Gram therefore
converges entrywise to the outer product of five explicit means. Its positive diagonal
and negative mixed part cancel exactly at leading order. The remaining interior energy
is not bounded by this limit theorem.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-- The absolutely convergent density of the unsigned damped divisor sum. -/
def pmPronicPowerDensity (ε : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-ε) / n

/-- The linear density of a finite Möbius floor leg. -/
def pmPronicVaughanSmallDensity (ε : ℝ) (U : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 U, (moebius d : ℝ) * ((d : ℝ) ^ (-ε) / d)

/-- The five linear means, including the density removed from the source. -/
def pmPronicVaughanMean (ε : ℝ) (U V : ℕ) : Fin 5 → ℝ :=
  ![pmPronicVaughanSmallDensity ε U,
    pmPronicVaughanSmallDensity ε V,
    -pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
      pmPronicVaughanSmallDensity ε V,
    (pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U -
      pmPronicVaughanSmallDensity ε V +
        pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
          pmPronicVaughanSmallDensity ε V,
    -(pmPowerDampedDivisorDensity ε).re]

private theorem tendsto_nat_floor_ratio (d : ℕ) :
    Tendsto (fun n : ℕ => ((n / d : ℕ) : ℝ) / n) atTop (𝓝 (1 / (d : ℝ))) := by
  have h := (tendsto_nat_floor_mul_div_atTop (a := 1 / (d : ℝ)) (by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_natCast,
    Nat.floor_natCast] using h

private theorem tendsto_finite_moebius_floor_mean (ε : ℝ) (U : ℕ) :
    Tendsto (fun n : ℕ =>
      (∑ d ∈ Icc 1 (min U n), (moebius d : ℝ) * pmPronicFloorWeight ε n d) / n)
      atTop (𝓝 (pmPronicVaughanSmallDensity ε U)) := by
  have hd (d : ℕ) : Tendsto
      (fun n : ℕ => (moebius d : ℝ) * pmPronicFloorWeight ε n d / n)
      atTop (𝓝 ((moebius d : ℝ) * ((d : ℝ) ^ (-ε) / d))) := by
    have h := (tendsto_nat_floor_ratio d).const_mul
      ((moebius d : ℝ) * (d : ℝ) ^ (-ε))
    simpa only [pmPronicFloorWeight, mul_div_assoc, mul_one_div] using h
  have h := tendsto_finset_sum (Icc 1 U) (fun d _ => hd d)
  apply h.congr'
  filter_upwards [eventually_ge_atTop U] with n hn
  simp only [min_eq_left hn, sum_div, pmPronicVaughanSmallDensity]

private theorem summable_pronic_power_density {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-ε) / n) := by
  have h := Real.summable_nat_rpow.mpr (show -ε - 1 < -1 by linarith)
  apply h.congr
  intro n
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, div_zero,
      Real.zero_rpow (by linarith : -ε - 1 ≠ 0)]
  · exact Real.rpow_sub_one (by exact_mod_cast hn) (-ε)

private theorem tendsto_damped_floor_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (∑ d ∈ Icc 1 n, (d : ℝ) ^ (-ε) * (n / d : ℕ)) / n)
      atTop (𝓝 (pmPronicPowerDensity ε)) := by
  have heq (n : ℕ) :
      (∑ d ∈ Icc 1 n, (d : ℝ) ^ (-ε) * (n / d : ℕ)) =
        ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, (d : ℝ) ^ (-ε) := by
    have h := congrArg Complex.re
      (pm_divisor_floor_sum_nat (fun d => ((d : ℝ) ^ (-ε) : ℂ)) n)
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] using h
  have h := (pm_tendsto_divisor_average (summable_pronic_power_density hε)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Nat.floor_natCast, heq, pmPronicPowerDensity] using h

private theorem tendsto_multiple_floor_mean {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ =>
      (∑ k ∈ Icc 1 (n / m), pmPronicFloorWeight ε n (m * k)) / n)
      atTop (𝓝 ((m : ℝ) ^ (-ε) / m * pmPronicPowerDensity ε)) := by
  let F := fun N : ℕ => ∑ k ∈ Icc 1 N, (k : ℝ) ^ (-ε) * (N / k : ℕ)
  have hF : Tendsto (fun N : ℕ => F N / N) atTop (𝓝 (pmPronicPowerDensity ε)) :=
    tendsto_damped_floor_mean hε
  have hN := Nat.tendsto_div_const_atTop hm.ne'
  have h := (hF.comp hN).mul (tendsto_nat_floor_ratio m)
  have h' : Tendsto (fun n : ℕ => F (n / m) / n)
      atTop (𝓝 (pmPronicPowerDensity ε / m)) := by
    simp only [mul_one_div] at h
    apply h.congr'
    filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
    have hn0 : ((n / m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n / m ≠ 0)
    simp only [Function.comp_def]
    field_simp [hn0]
  have heq (n : ℕ) :
      (∑ k ∈ Icc 1 (n / m), pmPronicFloorWeight ε n (m * k)) =
        (m : ℝ) ^ (-ε) * F (n / m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [pmPronicFloorWeight, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg k),
      Nat.div_div_eq_div_mul, mul_assoc]
  convert h'.const_mul ((m : ℝ) ^ (-ε)) using 1
  · ext n
    rw [heq]
    ring
  · ring

private theorem small_small_mean_factorization (ε : ℝ) (U V : ℕ) :
    (∑ a ∈ Icc 1 U, (moebius a : ℝ) *
      ∑ b ∈ Icc 1 V, (moebius b : ℝ) *
        (((a * b : ℕ) : ℝ) ^ (-ε) / (a * b : ℕ) * pmPronicPowerDensity ε)) =
      pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
        pmPronicVaughanSmallDensity ε V := by
  simp only [pmPronicVaughanSmallDensity, mul_sum, sum_mul]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

private theorem tendsto_small_small_mean {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    Tendsto (fun n : ℕ => pmPronicVaughanPiece ε U V n 2 / n)
      atTop (𝓝 (-pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
        pmPronicVaughanSmallDensity ε V)) := by
  have h := tendsto_finset_sum (Icc 1 U) fun a ha =>
    (tendsto_finset_sum (Icc 1 V) fun b hb =>
      (tendsto_multiple_floor_mean hε
        (Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1)).const_mul
          (moebius b : ℝ)).const_mul (moebius a : ℝ)
  have hneg := h.neg
  rw [small_small_mean_factorization] at hneg
  simp only [neg_mul] at hneg
  apply hneg.congr'
  filter_upwards [eventually_ge_atTop U, eventually_ge_atTop V] with n hnU hnV
  change -(∑ a ∈ Icc 1 U, (moebius a : ℝ) *
    ∑ b ∈ Icc 1 V, (moebius b : ℝ) *
      ((∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k)) / n)) = _
  change _ = (-(∑ a ∈ Icc 1 (min U n), (moebius a : ℝ) *
    ∑ b ∈ Icc 1 (min V n), (moebius b : ℝ) *
      ∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k))) / n
  simp only [min_eq_left hnU, min_eq_left hnV, neg_div, sum_div, mul_div_assoc]

/-- Every fixed-cutoff Vaughan piece has its explicit linear mean. -/
theorem tendsto_pmPronicVaughanPiece_div_nat {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (i : Fin 5) :
    Tendsto (fun n : ℕ => pmPronicVaughanPiece ε U V n i / n)
      atTop (𝓝 (pmPronicVaughanMean ε U V i)) := by
  have h0 : Tendsto (fun n : ℕ => pmPronicVaughanPiece ε U V n 0 / n)
      atTop (𝓝 (pmPronicVaughanSmallDensity ε U)) :=
    tendsto_finite_moebius_floor_mean ε U
  have h1 : Tendsto (fun n : ℕ => pmPronicVaughanPiece ε U V n 1 / n)
      atTop (𝓝 (pmPronicVaughanSmallDensity ε V)) :=
    tendsto_finite_moebius_floor_mean ε V
  have h2 := tendsto_small_small_mean hε U V
  have h4 := tendsto_pmPronicVaughanPiece_pole_div_nat hε.le U V
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · have h := ((((tendsto_pmBezoutInteriorPrefix_div_nat hε).sub h0).sub h1).sub h2).sub h4
    convert h using 1
    · ext n
      have hs := sum_pmPronicVaughanPiece ε U V n
      simp [Fin.sum_univ_succ] at hs
      linear_combination (norm := ring_nf) -hs / (n : ℝ)
    · change (pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U -
        pmPronicVaughanSmallDensity ε V +
          pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
            pmPronicVaughanSmallDensity ε V = _
      ring
  · exact h4

/-- The leading Gram matrix is the outer product of the component means. -/
theorem tendsto_pmPronicVaughanGram_div_nat {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (i j : Fin 5) :
    Tendsto (fun T : ℕ => pmPronicVaughanGram ε U V T i j / T)
      atTop (𝓝 (pmPronicVaughanMean ε U V i * pmPronicVaughanMean ε U V j)) := by
  exact tendsto_pronic_pair_mean (tendsto_pmPronicVaughanPiece_div_nat hε U V i)
    (tendsto_pmPronicVaughanPiece_div_nat hε U V j)

/-- The means sum to zero because the pole has already been removed from the source. -/
theorem sum_pmPronicVaughanMean (ε : ℝ) (U V : ℕ) :
    (∑ i : Fin 5, pmPronicVaughanMean ε U V i) = 0 := by
  simp [pmPronicVaughanMean, Fin.sum_univ_succ]
  <;> ring

/-- At fixed cutoffs the diagonal has an explicit, strictly positive linear density. -/
theorem tendsto_pmPronicVaughanDiagonal_div_nat {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    Tendsto (fun T : ℕ => pmPronicVaughanDiagonal ε U V T / T)
      atTop (𝓝 (∑ i : Fin 5, pmPronicVaughanMean ε U V i ^ 2)) := by
  have h := tendsto_finset_sum univ (fun i _ => tendsto_pmPronicVaughanGram_div_nat hε U V i i)
  simpa only [pmPronicVaughanDiagonal, sum_div, ← sq] using h

theorem pmPronicVaughanMean_sq_sum_pos {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    0 < ∑ i : Fin 5, pmPronicVaughanMean ε U V i ^ 2 := by
  have h := single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 5))) =>
    sq_nonneg (pmPronicVaughanMean ε U V i)) (mem_univ (4 : Fin 5))
  have hp : 0 < pmPronicVaughanMean ε U V 4 ^ 2 := by
    change 0 < (-(pmPowerDampedDivisorDensity ε).re) ^ 2
    rw [neg_sq]
    exact sq_pos_of_pos (pmPowerDampedDivisorDensity_re_pos hε)
  exact hp.trans_le h

/-- Every finite superposition has the square of its mean as its linear energy density. -/
theorem tendsto_pmPronicVaughan_combinationEnergy_div_nat {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (w : Fin 5 → ℝ) :
    Tendsto (fun T : ℕ =>
      (∑ n ∈ Icc 1 T, (∑ i : Fin 5, w i * pmPronicVaughanPiece ε U V n i) ^ 2 /
        (pronicSeq n : ℝ)) / T)
      atTop (𝓝 ((∑ i : Fin 5, w i * pmPronicVaughanMean ε U V i) ^ 2)) := by
  have h : Tendsto (fun n : ℕ =>
      (∑ i : Fin 5, w i * pmPronicVaughanPiece ε U V n i) / n)
      atTop (𝓝 (∑ i : Fin 5, w i * pmPronicVaughanMean ε U V i)) := by
    have h := tendsto_finset_sum univ fun i _ =>
      (tendsto_pmPronicVaughanPiece_div_nat hε U V i).const_mul (w i)
    simpa only [sum_div, mul_div_assoc] using h
  simpa only [← sq] using tendsto_pronic_pair_mean h h

/-- Bounded interior energy requires a reciprocal-horizon relative error, not merely
relative cancellation tending to one. -/
theorem bounded_pmInteriorPronicEnergy_iff_reciprocal_vaughan_relative_error
    {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ C) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop,
        |pmPronicVaughanMixedRemainder ε U V T / pmPronicVaughanDiagonal ε U V T + 1| ≤
          C / T := by
  let d := ∑ i : Fin 5, pmPronicVaughanMean ε U V i ^ 2
  have hd : 0 < d := pmPronicVaughanMean_sq_sum_pos hε U V
  have hl := tendsto_pmPronicVaughanDiagonal_div_nat hε U V
  have hlo := hl.eventually (eventually_ge_nhds (half_lt_self hd))
  have hhi := hl.eventually (eventually_le_nhds (lt_add_one d))
  have hb : ∀ᶠ T : ℕ in atTop,
      0 < (T : ℝ) ∧ 0 < pmPronicVaughanDiagonal ε U V T ∧
        d / 2 * T ≤ pmPronicVaughanDiagonal ε U V T ∧
          pmPronicVaughanDiagonal ε U V T ≤ (d + 1) * T := by
    filter_upwards [hlo, hhi, eventually_ge_atTop 1] with T hloT hhiT hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hlow := (le_div_iff₀ hTpos).mp hloT
    refine ⟨hTpos, (mul_pos (half_pos hd) hTpos).trans_le hlow, hlow, ?_⟩
    exact (div_le_iff₀ hTpos).mp hhiT
  have hr (T : ℕ) (hD : 0 < pmPronicVaughanDiagonal ε U V T) :
      |pmPronicVaughanMixedRemainder ε U V T / pmPronicVaughanDiagonal ε U V T + 1| =
        pmBezoutInteriorPronicEnergy ε T / pmPronicVaughanDiagonal ε U V T := by
    have h := pmPronicVaughan_cancellation_error ε U V T
    have he : pmPronicVaughanMixedRemainder ε U V T / pmPronicVaughanDiagonal ε U V T + 1 =
        pmBezoutInteriorPronicEnergy ε T / pmPronicVaughanDiagonal ε U V T := by
      rw [← h, add_div, div_self hD.ne']
      ring
    rw [he, abs_of_nonneg (div_nonneg (pmBezoutInteriorPronicEnergy_nonneg ε T) hD.le)]
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨2 * C / d, by positivity, ?_⟩
    filter_upwards [hb] with T hT
    rw [hr T hT.2.1]
    calc
      _ ≤ C / pmPronicVaughanDiagonal ε U V T :=
        div_le_div_of_nonneg_right (hbound T) hT.2.1.le
      _ ≤ C / (d / 2 * T) :=
        div_le_div_of_nonneg_left hC (mul_pos (half_pos hd) hT.1) hT.2.2.1
      _ = (2 * C / d) / T := by
        field_simp [hd.ne', hT.1.ne']
  · rintro ⟨C, hC, hbound⟩
    have hev : ∀ᶠ T : ℕ in atTop, pmBezoutInteriorPronicEnergy ε T ≤ C * (d + 1) := by
      filter_upwards [hb, hbound] with T hT hboundT
      rw [hr T hT.2.1] at hboundT
      have h := (div_le_iff₀ hT.2.1).mp hboundT
      calc
        _ ≤ (C / T) * pmPronicVaughanDiagonal ε U V T := h
        _ ≤ (C / T) * ((d + 1) * T) :=
          mul_le_mul_of_nonneg_left hT.2.2.2 (div_nonneg hC hT.1.le)
        _ = C * (d + 1) := by field_simp [hT.1.ne']
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨C * (d + 1), by positivity, fun T => ?_⟩
    apply le_trans ?_ (hN (max T N) (le_max_right _ _))
    unfold pmBezoutInteriorPronicEnergy
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (le_max_left _ _))
      (fun n _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

end GaloisForLFunctions.BezoutValuationIncidence
