import GaloisForLFunctions.ExceptionalLayerTheory.AFactorialCorrectionForTheSquareRootDensity
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount
import GaloisForLFunctions.RHTower.WeilPositivityPrimePowersForced

/-!
# Ordinary primes in a moving factorial interval

A third factorial correction cancels the square-root density of the proper
prime powers. Their signed contribution is then bounded by the cell errors
above the split and the total positive mass below it. Both Vaughan widths
reduce to one ordinary-prime interval at the original horizon.
-/

noncomputable section

open Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def powerMass (n : ℕ) : ℝ := ∑ m ∈ Ioc 0 n, primePowerPart m

private theorem powerMass_eq (n : ℕ) :
    powerMass n = Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
  exact sum_congr rfl fun m _ => by by_cases h : m.Prime <;> simp [primePowerPart, h]

private theorem powerPart_nonneg (m : ℕ) : 0 ≤ primePowerPart m := by
  unfold primePowerPart
  split <;> first | exact le_rfl | exact vonMangoldt_nonneg

/-- The error in the square-root density has a strict power saving, uniformly
down to the empty prefix. -/
private theorem power_density :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |powerMass n - Real.sqrt n| ≤ C * (n : ℝ) ^ (9/20 : ℝ) := by
  have hz : zeroReSup ≤ 7/8 := zeroReSup_le_of_forall_re_le fun q =>
    le_of_not_gt fun h =>
      MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_seven_eighths_lt_re h
        (riemannZeta_xiZeroCopy_eq_zero q)
  obtain ⟨C, hC, hb⟩ := exists_abs_chebyshevPsi_sub_le_rpow
    (show zeroReSup < (9/10 : ℝ) by linarith only [hz])
  let L := Real.log 4 + 4
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨2*L+C+2, by positivity, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [powerMass]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have h₁ := abs_psi_sub_theta_sub_sqrt_le hn
  have h₂ := hb _ (Real.one_le_sqrt.mpr hn1)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0] at h₂
  norm_num only [show (1/2 : ℝ)*(9/10) = 9/20 by norm_num] at h₂
  have hc : Chebyshev.psi ((n : ℝ)^(1/3 : ℝ)) ≤ L * (n : ℝ)^(9/20 : ℝ) :=
    (Chebyshev.psi_le_const_mul_self (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) hL)
  have hr := Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 9/20)
  rw [powerMass_eq, abs_le]
  rw [abs_le] at h₁
  rw [Real.sqrt_eq_rpow] at h₁ ⊢
  constructor <;> linarith only [h₁.1, h₁.2, h₂, hc, hr]

private def remainder (w : ℕ → ℝ) (X L : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 L, w (X/m) * primePowerPart m

private def cell (X j : ℕ) : ℝ := powerMass (X/j) - powerMass (X/(j+1))

/-- Split off the first J quotient cells. The residue consists of the small
prime powers up to X/(J+1), regardless of their floor quotient. -/
private theorem split_cells (w : ℕ → ℝ) (X J : ℕ) :
    remainder w X X = (∑ j ∈ Icc 1 J, w j * cell X j) + remainder w X (X/(J+1)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    let j := J+1
    have hj : 0 < j := Nat.succ_pos J
    have hkj : X/(j+1) ≤ X/j := Nat.div_le_div_left (by omega) hj
    have hval (m : ℕ) (hm : m ∈ Ioc (X/(j+1)) (X/j)) : X/m = j := by
      obtain ⟨h₁, h₂⟩ := mem_Ioc.mp hm
      have hmpos : 0 < m := (Nat.zero_le _).trans_lt h₁
      have hl := (Nat.le_div_iff_mul_le hj).mp h₂
      have hu := (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp h₁
      have h₃ : j ≤ X/m := (Nat.le_div_iff_mul_le hmpos).mpr (by simpa [Nat.mul_comm] using hl)
      have h₄ : X/m < j+1 := (Nat.div_lt_iff_lt_mul hmpos).mpr (by simpa [Nat.mul_comm] using hu)
      omega
    have hmass := sum_Ioc_consecutive primePowerPart (Nat.zero_le _) hkj
    have hcell : (∑ m ∈ Ioc (X/(j+1)) (X/j), w (X/m)*primePowerPart m) = w j * cell X j := by
      rw [cell, sub_eq_of_eq_add (show powerMass (X/j) =
          (∑ m ∈ Ioc (X/(j+1)) (X/j), primePowerPart m) + powerMass (X/(j+1)) by
        unfold powerMass; rw [add_comm]; exact hmass.symm), mul_sum]
      exact sum_congr rfl fun m hm => by rw [hval m hm]
    have hsplit := sum_Ioc_consecutive (fun m => w (X/m)*primePowerPart m) (Nat.zero_le _) hkj
    rw [hcell] at hsplit
    change remainder w X (X/(j+1)) + w j * cell X j = remainder w X (X/j) at hsplit
    rw [ih, sum_Icc_succ_top (by omega : 1 ≤ J + 1)]
    change _ + remainder w X (X/j) = _ + remainder w X (X/(j+1))
    rw [← hsplit]
    ring

private theorem remainder_bound {w : ℕ → ℝ} {M K : ℝ} (hM : 0 ≤ M) (hw : ∀ j, |w j| ≤ M)
    (hK : ∀ n : ℕ, powerMass n ≤ K * Real.sqrt n) (X L : ℕ) :
    |remainder w X L| ≤ M * (K * Real.sqrt L) := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ m ∈ Ioc 0 L, M * primePowerPart m := by
      apply sum_le_sum
      intro m _
      rw [abs_mul, abs_of_nonneg (powerPart_nonneg m)]
      exact mul_le_mul_of_nonneg_right (hw _) (powerPart_nonneg m)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hK L) hM

private theorem cutoff {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ ⌊(N : ℝ)^(1/64 : ℝ)⌋₊ :=
  (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow (by exact_mod_cast hN) (by norm_num))

/-- Rounding a nonnegative quotient changes its square root by at most one. -/
private theorem sqrt_div_gap (X : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    |Real.sqrt (X/j : ℕ) - Real.sqrt X * edge j| ≤ 1 := by
  have e : Real.sqrt X * edge j = Real.sqrt ((X : ℝ)/j) := by
    calc
      _ = Real.sqrt X / Real.sqrt j := (div_eq_mul_inv _ _).symm
      _ = _ := (Real.sqrt_div (Nat.cast_nonneg X) j).symm
  rw [e, abs_of_nonpos (sub_nonpos.mpr (Real.sqrt_le_sqrt (Nat.cast_div_le)))]
  have hh := (abs_le.mp (Sieve.abs_natDiv_sub_div_le (N := X) hj)).1
  have hq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (X/j))
  have hs : Real.sqrt ((X : ℝ)/j) ≤ Real.sqrt (X/j : ℕ) + 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hh,hq,Real.sqrt_nonneg (X/j : ℕ)]⟩
  linarith only [hs]

private theorem cell_and_tail_bounds :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ n : ℕ, powerMass n ≤ K * Real.sqrt n) ∧
      ∀ N X j : ℕ, 1 ≤ N → X ≤ N → 1 ≤ j →
        |cell X j - Real.sqrt X * cellSize j| ≤ K*(N : ℝ)^(9/20 : ℝ) := by
  obtain ⟨C, hC, hc⟩ := power_density
  refine ⟨2*C+2, by positivity, fun n => ?_, fun N X j hN hX hj => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [powerMass]
    have he : (n : ℝ)^(9/20 : ℝ) ≤ Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
    have h := (abs_le.mp (hc n)).2
    have hs := Real.sqrt_nonneg (n : ℝ)
    nlinarith only [h, mul_le_mul_of_nonneg_left he hC, mul_nonneg hC hs, hs]
  · have hr := Real.one_le_rpow (by exact_mod_cast hN : (1 : ℝ) ≤ N) (by norm_num : (0 : ℝ) ≤ 9/20)
    have hend (i : ℕ) (hi : 1 ≤ i) :
        |powerMass (X/i) - Real.sqrt X * edge i| ≤ C*(N : ℝ)^(9/20 : ℝ)+1 := by
      have hn : (X/i : ℕ) ≤ N := (Nat.div_le_self ..).trans hX
      exact (abs_sub_le _ (Real.sqrt (X/i : ℕ)) _).trans (add_le_add ((hc _).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by norm_num)) hC))
        (sqrt_div_gap X hi))
    have h₁ := abs_le.mp (hend j hj)
    have h₂ := abs_le.mp (hend (j+1) (Nat.succ_pos _))
    rw [cell,cellSize,abs_le]
    constructor <;> linarith only [hr,h₁.1,h₁.2,h₂.1,h₂.2]

private theorem abs_weighted_powers {N X J : ℕ} (hN : 1 ≤ N) (hX : X ≤ N)
    {w : ℕ → ℝ} {M K : ℝ} (hM : 0 ≤ M) (hw : ∀ j, |w j| ≤ M)
    (hzero : squareMoment J w = 0)
    (hpos : ∀ n : ℕ, powerMass n ≤ K * Real.sqrt n)
    (hcell : ∀ N X j : ℕ, 1 ≤ N → X ≤ N → 1 ≤ j →
      |cell X j - Real.sqrt X * cellSize j| ≤ K*(N : ℝ)^(9/20 : ℝ)) :
    |remainder w X X| ≤ (J : ℝ)*M*(K*(N : ℝ)^(9/20 : ℝ)) + M*(K*Real.sqrt (X/(J+1) : ℕ)) := by
  have hi : Icc 1 J = Ico 1 (J+1) := by ext j; simp only [mem_Ico,mem_Icc]; omega
  have hmodel : ∑ j ∈ Icc 1 J, w j*(Real.sqrt X*cellSize j) = 0 := by
    simp only [hi, mul_left_comm (w _) (Real.sqrt X), ← mul_sum]
    exact mul_eq_zero_of_right _ hzero
  have hsum : |∑ j ∈ Icc 1 J, w j*cell X j| ≤ (J : ℝ)*M*(K*(N : ℝ)^(9/20 : ℝ)) := by
    have hdiff : (∑ j ∈ Icc 1 J, w j*(cell X j - Real.sqrt X*cellSize j)) =
        ∑ j ∈ Icc 1 J, w j*cell X j := by simp only [mul_sub,sum_sub_distrib,hmodel,sub_zero]
    rw [← hdiff]
    calc
      _ ≤ ∑ _j ∈ Icc 1 J, M*(K*(N : ℝ)^(9/20 : ℝ)) := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul (hw _) (hcell N X j hN hX (mem_Icc.mp hj).1) (abs_nonneg _) hM
      _ = _ := by simp; ring
  rw [split_cells w X J]
  exact (abs_add_le _ _).trans (add_le_add hsum (remainder_bound hM hw hpos ..))

/-- Uniform square-root error for bounded quotient weights with vanishing
square-root moment on the first 128 R² cells. -/
theorem proper_powers_of_zero_moment {B : ℝ} (hB : 0 ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N X R : ℕ, 1 ≤ N → X ≤ N →
      (R : ℝ) ≤ (N : ℝ)^(1/64 : ℝ) → ∀ w : ℕ → ℝ, (∀ j, |w j| ≤ B*R) →
      squareMoment (128*R^2) w = 0 →
      |∑ m ∈ Ioc 0 X, w (X/m) * primePowerPart m| ≤ A*Real.sqrt N := by
  obtain ⟨K,hK,hpos,hcell⟩ := cell_and_tail_bounds
  refine ⟨129*B*K, by positivity, fun N X R hN hX hRr w hw hmoment => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have he : (R : ℝ)^3 * (N : ℝ)^(9/20 : ℝ) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow,pow_succ,pow_two]
    calc
      _ ≤ (((N : ℝ)^(1/64 : ℝ) * (N : ℝ)^(1/64 : ℝ)) * (N : ℝ)^(1/64 : ℝ)) *
          (N : ℝ)^(9/20 : ℝ) := by gcongr
      _ ≤ _ := by
        simp only [← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  let q := X/(128*R^2+1)
  have hb : R^2*q ≤ N := ((Nat.mul_le_mul_right q (show R^2 ≤ 128*R^2+1 by omega)).trans
    (Nat.mul_div_le ..)).trans hX
  have hsq := Real.sqrt_le_sqrt (show (R : ℝ)^2*(q : ℝ) ≤ N by exact_mod_cast hb)
  rw [Real.sqrt_mul (sq_nonneg (R : ℝ)), Real.sqrt_sq (Nat.cast_nonneg R)] at hsq
  apply (abs_weighted_powers hN hX (show 0 ≤ B*R by positivity)
    hw hmoment hpos hcell).trans
  change (↑(128*R^2 : ℕ) : ℝ) * (B*R) * _ + B*R*(K*Real.sqrt q) ≤ _
  push_cast
  calc
    _ = 128*B*K*((R : ℝ)^3*(N : ℝ)^(9/20 : ℝ)) + B*K*((R : ℝ)*Real.sqrt q) := by ring
    _ ≤ 128*B*K*Real.sqrt N + B*K*Real.sqrt N := by gcongr
    _ = _ := by ring

/-- Signed sum of every proper prime power in the corrected factorial
weight is of square-root size, uniformly throughout the divided horizons. -/
theorem proper_prime_power_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N X R : ℕ, 1 ≤ N → X ≤ N → 1 ≤ R →
      (R : ℝ) ≤ (N : ℝ)^(1/64 : ℝ) →
      |∑ m ∈ Ioc 0 X, primeWeight R (X/m) * primePowerPart m| ≤ A*Real.sqrt N := by
  obtain ⟨C,hC,hm⟩ := mass_uniform
  obtain ⟨A,hA,h⟩ := proper_powers_of_zero_moment (B := 66*(1+C)) (by positivity)
  refine ⟨A,hA,fun N X R hN hX hR hRr => h N X R hN hX hRr _ (fun j => ?_) (primeWeight_moment hR)⟩
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  exact (primeWeight_bound hR j).trans (by linarith only [hm R hR,hr])

/-- Long ordinary primes in the factorial interval, weighted by log p. -/
def ordinaryMiddle (R U X : ℕ) : ℝ :=
  ∑ p ∈ Ioc U (X/R) with p.Prime, primeWeight R (X/p) * Real.log p

private def primeTerm (R X m : ℕ) : ℝ :=
  if m.Prime then primeWeight R (X/m)*vonMangoldt m else 0

/-- Removing the small ordinary primes costs at most the Chebyshev mass of
the cutoff times the size of the complementary weight. -/
private theorem ordinary_head {R : ℕ} (hR : 1 ≤ R) (U X : ℕ) :
    |(∑ m ∈ Ioc 0 X, primeTerm R X m) - ordinaryMiddle R U X| ≤ (66*(1+mass R))*(7*U) := by
  let S := Ioc 0 X
  have hsplit := sum_filter_add_sum_filter_not S (fun m => m ≤ U) (primeTerm R X)
  have hsub : Ioc U (X/R) ⊆ S.filter (fun m => ¬m ≤ U) := by
    intro m hm
    obtain ⟨hU,hmax⟩ := mem_Ioc.mp hm
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hmax.trans (Nat.div_le_self ..)⟩, by omega⟩
  have htail : (∑ m ∈ S.filter (fun m => ¬m ≤ U), primeTerm R X m) = ordinaryMiddle R U X := by
    rw [← sum_subset (f := primeTerm R X) hsub (by
      intro m hm hnot
      obtain ⟨hmS,hU⟩ := mem_filter.mp hm
      obtain ⟨hm1,hmX⟩ := mem_Ioc.mp hmS
      have hgt : X/R < m := by
        by_contra! h
        exact hnot (mem_Ioc.mpr ⟨by omega,h⟩)
      have hlt : X/m < R := (Nat.div_lt_iff_lt_mul hm1).mpr (by
        simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hR).mp hgt)
      simp [primeTerm, primeWeight_small ((Nat.one_le_div_iff hm1).mpr hmX) hlt])]
    rw [ordinaryMiddle, sum_filter]
    apply sum_congr rfl
    intro m _
    by_cases hp : m.Prime <;> simp [primeTerm, hp, vonMangoldt_apply_prime]
  rw [htail] at hsplit
  change |(∑ m ∈ S, primeTerm R X m) - _| ≤ _
  rw [← hsplit, add_sub_cancel_right]
  have hM : 0 ≤ 66*(1+mass R) := (abs_nonneg _).trans (primeWeight_bound hR 0)
  have hsubU : S.filter (fun m => m ≤ U) ⊆ Icc 1 U := fun m hm =>
    mem_Icc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hm).1).1, (mem_filter.mp hm).2⟩
  calc
    _ ≤ ∑ m ∈ S.filter (fun m => m ≤ U), (66*(1+mass R))*vonMangoldt m := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro m _
      by_cases hp : m.Prime
      · rw [primeTerm, if_pos hp, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_right (primeWeight_bound hR _) vonMangoldt_nonneg
      · rw [primeTerm, if_neg hp, abs_zero]
        exact mul_nonneg hM vonMangoldt_nonneg
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg hsubU
        (fun _ _ _ => vonMangoldt_nonneg)).trans (chebyshevPsi_le_seven U)) hM

private theorem split_prime_row {R : ℕ} (hR : 1 ≤ R) (U X : ℕ) :
    |(Chebyshev.psi X - X) - ordinaryMiddle R U X - remainder (primeWeight R) X X| ≤
      196*(1+mass R)*(3+Real.log (128*R : ℕ)+2*Real.log X) + 66*(1+mass R)*(7*U) := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
    simp only [Nat.cast_zero,Nat.zero_div,Chebyshev.psi_zero,sub_zero,Real.log_zero,mul_zero,
      add_zero,ordinaryMiddle,remainder,Ioc_eq_empty_of_le (Nat.zero_le _),filter_empty,
      sum_empty,abs_zero]
    have := Real.log_natCast_nonneg (128*R)
    positivity
  have hs : (∑ m ∈ Ioc 0 X, primeTerm R X m) + remainder (primeWeight R) X X =
      ∑ m ∈ Icc 1 X, vonMangoldt m * primeWeight R (X/m) := by
    rw [remainder, ← sum_add_distrib]
    change _ = ∑ m ∈ Ioc 0 X, _
    apply sum_congr rfl
    intro m _
    by_cases hp : m.Prime <;> simp [primeTerm,primePowerPart,hp,mul_comm]
  have hh := abs_le.mp (ordinary_head hR U X)
  have hf := abs_le.mp (primeWeight_factorial hR hX)
  rw [abs_le]
  constructor <;> linarith only [hs,hh.1,hh.2,hf.1,hf.2]

/-- Each divided ordinary-prime error is carried by one middle interval;
the same weight and interval cutoffs work for every X up to N. -/
theorem ordinary_prime_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N X : ℕ, 1 ≤ N → X ≤ N →
      let R := ⌊(N : ℝ)^(1/64 : ℝ)⌋₊
      let U := ⌊(N : ℝ)^(31/64 : ℝ)⌋₊
      |(Chebyshev.psi X-X)-ordinaryMiddle R U X| ≤ K*Real.sqrt N := by
  obtain ⟨C,hC,hm⟩ := mass_uniform
  obtain ⟨A,hA,ha⟩ := proper_prime_power_bound
  let K := (196*137 + 66*7)*(1+C)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+A, by positivity, fun N X hN hX => ?_⟩
  intro R U
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans_le hn
  let r := (N : ℝ)^(1/64 : ℝ)
  let u := (N : ℝ)^(31/64 : ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow hn (by norm_num)
  have hru : r ≤ u := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hu := hr.trans hru
  have hR : (R : ℝ) ≤ r := Nat.floor_le (zero_le_one.trans hr)
  have hU : (U : ℝ) ≤ u := Nat.floor_le (zero_le_one.trans hu)
  have hpos : 1 ≤ R := cutoff hN
  have hmR : 1+mass R ≤ (1+C)*r := by
    have h := (hm R hpos).trans (mul_le_mul_of_nonneg_left hR hC)
    linarith only [h,hr]
  have hl : Real.log X ≤ 3*u := by
    rcases Nat.eq_zero_or_pos X with rfl | hx
    · rw [Nat.cast_zero,Real.log_zero]; linarith only [hu]
    have h₁ := Real.log_le_log (by exact_mod_cast hx : (0 : ℝ) < X) (by exact_mod_cast hX : (X : ℝ) ≤ N)
    have h₂ := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 31/64)
    change Real.log N ≤ u / (31/64) at h₂
    linarith only [h₁,h₂,hu]
  have hlR : Real.log (128*R : ℕ) ≤ 128*u := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (128*R : ℕ) by
      exact_mod_cast (show 0 < 128*R by omega))
    push_cast at h ⊢
    linarith only [hR,hru,h]
  have hs : r*u = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, show r*u = (N : ℝ)^((1/64 : ℝ)+31/64) from
      (Real.rpow_add hn0 ..).symm]
    norm_num
  have hL := Real.log_natCast_nonneg X
  have hL' := Real.log_natCast_nonneg (128*R)
  have hb : |(Chebyshev.psi X-X)-ordinaryMiddle R U X-remainder (primeWeight R) X X| ≤ K*Real.sqrt N := by
    apply (split_prime_row hpos U X).trans
    calc
      _ ≤ (196*((1+C)*r))*(137*u) + (66*((1+C)*r))*(7*u) := by
        apply add_le_add
        · exact mul_le_mul (by gcongr) (by linarith only [hl,hlR,hu]) (by positivity) (by positivity)
        · exact mul_le_mul (by gcongr) (by gcongr) (by positivity) (by positivity)
      _ = _ := by rw [← hs]; dsimp [K]; ring
  have hp : |remainder (primeWeight R) X X| ≤ A*Real.sqrt N := ha N X R hN hX hpos hR
  have h₁ := abs_le.mp hb
  have h₂ := abs_le.mp hp
  rw [abs_le]
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2]

/-- At both Vaughan widths ordinary primes alone carry the signed count,
with square-root error uniform in the horizon and the short coefficients. -/
theorem ordinary_prime_middle_interval :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ, 1 ≤ N →
      let R := ⌊(N : ℝ)^(1/64 : ℝ)⌋₊
      let U := ⌊(N : ℝ)^(31/64 : ℝ)⌋₊
      |cofactorCountError V W N - ∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d *
        ordinaryMiddle R U (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|) * (K*Real.sqrt N) := by
  obtain ⟨K,hK,h⟩ := ordinary_prime_row
  refine ⟨K,hK,fun V W N hN => ?_⟩
  intro R U
  rw [cofactorCountError_eq, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ d ∈ Icc 1 (min N W), |Sieve.typeIIShort V d| * (K*Real.sqrt N) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h N _ hN (Nat.div_le_self ..)) (abs_nonneg _)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc_right (min_le_right N W)) (fun _ _ _ => abs_nonneg _)) (by positivity)

#print axioms ordinary_prime_middle_interval

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
