import GaloisForLFunctions.RHTower.CCM.CCMFirstClockHalfWaveReflection
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open scoped BigOperators
open Finset

noncomputable section

namespace RHTower

/-- Damped sine packet with modes `1, ..., N`. -/
def firstClockGeometricTower (r θ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, r ^ (j + 1) * Real.sin ((j + 1 : ℕ) * θ)

lemma sin_nat_succ_succ_mul
    (θ : ℝ) (N : ℕ) :
    Real.sin ((N + 2 : ℕ) * θ) =
      2 * Real.cos θ * Real.sin ((N + 1 : ℕ) * θ) -
        Real.sin (N * θ) := by
  rw [show ((N + 2 : ℕ) : ℝ) * θ =
      ((N + 1 : ℕ) : ℝ) * θ + θ by push_cast; ring,
    Real.sin_add,
    show (N : ℝ) * θ = ((N + 1 : ℕ) : ℝ) * θ - θ by push_cast; ring,
    Real.sin_sub]
  ring

/-- Denominator-free finite damped-sine geometric identity. -/
theorem firstClockGeometricTower_mul_denominator
    (r θ : ℝ) (N : ℕ) :
    firstClockGeometricTower r θ N *
        (1 - 2 * r * Real.cos θ + r ^ 2) =
      r * Real.sin θ -
        r ^ (N + 1) * Real.sin ((N + 1 : ℕ) * θ) +
        r ^ (N + 2) * Real.sin (N * θ) := by
  induction N with
  | zero =>
      simp [firstClockGeometricTower]
  | succ N ih =>
      rw [firstClockGeometricTower, Finset.sum_range_succ]
      change
        (firstClockGeometricTower r θ N +
            r ^ (N + 1) * Real.sin ((N + 1 : ℕ) * θ)) *
            (1 - 2 * r * Real.cos θ + r ^ 2) =
          r * Real.sin θ -
            r ^ (N + 2) * Real.sin ((N + 2 : ℕ) * θ) +
            r ^ (N + 3) * Real.sin ((N + 1 : ℕ) * θ)
      rw [add_mul, ih, sin_nat_succ_succ_mul]
      ring

theorem firstClockGeometricTower_two
    (r θ : ℝ) :
    firstClockGeometricTower r θ 2 =
      r * Real.sin θ * (1 + 2 * r * Real.cos θ) := by
  norm_num [firstClockGeometricTower, Finset.sum_range_succ,
    Real.sin_two_mul]
  ring

theorem firstClockGeometricTower_three
    (r θ : ℝ) :
    firstClockGeometricTower r θ 3 =
      r * Real.sin θ *
        (4 * r ^ 2 * Real.cos θ ^ 2 +
          2 * r * Real.cos θ + 1 - r ^ 2) := by
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsinCube :
      Real.sin θ ^ 3 = Real.sin θ * (1 - Real.cos θ ^ 2) := by
    calc
      Real.sin θ ^ 3 = Real.sin θ * Real.sin θ ^ 2 := by ring
      _ = Real.sin θ * (1 - Real.cos θ ^ 2) := by
        rw [show Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 by linarith]
  norm_num [firstClockGeometricTower, Finset.sum_range_succ,
    Real.sin_two_mul, Real.sin_three_mul]
  rw [hsinCube]
  ring

theorem firstClockGeometricTower_two_nonneg
    {r θ : ℝ} (hr0 : 0 ≤ r) (hrHalf : r ≤ 1 / 2)
    (hsin : 0 ≤ Real.sin θ) :
    0 ≤ firstClockGeometricTower r θ 2 := by
  rw [firstClockGeometricTower_two]
  have hcos := Real.neg_one_le_cos θ
  have hwall : 0 ≤ 1 + 2 * r * Real.cos θ := by
    nlinarith
  positivity

theorem firstClockGeometricTower_three_pos
    {r θ : ℝ} (hr : 0 < r) (hrSq : r ^ 2 ≤ 1 / 2)
    (hsin : 0 < Real.sin θ) :
    0 < firstClockGeometricTower r θ 3 := by
  rw [firstClockGeometricTower_three]
  have hsq :
      0 ≤ (2 * r * Real.cos θ + 1 / 2) ^ 2 := sq_nonneg _
  have hfactor :
      0 < 4 * r ^ 2 * Real.cos θ ^ 2 +
          2 * r * Real.cos θ + 1 - r ^ 2 := by
    nlinarith
  positivity

lemma firstClockGeometricDenominator_pos
    {r θ : ℝ} (hsin : 0 < Real.sin θ) :
    0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsinSq : 0 < Real.sin θ ^ 2 := sq_pos_of_pos hsin
  nlinarith [sq_nonneg (r - Real.cos θ)]

/-- Abstract tail theorem: once the two terminal residual sines fit below the first mode,
the damped packet is positive. -/
theorem firstClockGeometricTower_pos_of_terminal_bounds
    {r θ : ℝ} {N : ℕ}
    (hr : 0 < r)
    (hbudget : r ^ N * (1 + r) < 1)
    (hsin : 0 < Real.sin θ)
    (hnext : Real.sin ((N + 1 : ℕ) * θ) ≤ Real.sin θ)
    (hlast : -Real.sin θ ≤ Real.sin (N * θ)) :
    0 < firstClockGeometricTower r θ N := by
  have hr0 : 0 ≤ r := hr.le
  have hpowN : 0 ≤ r ^ N := pow_nonneg hr0 N
  have hpowN1 : 0 ≤ r ^ (N + 1) := pow_nonneg hr0 (N + 1)
  have hpowN2 : 0 ≤ r ^ (N + 2) := pow_nonneg hr0 (N + 2)
  have hnextMul :
      r ^ (N + 1) * Real.sin ((N + 1 : ℕ) * θ) ≤
        r ^ (N + 1) * Real.sin θ :=
    mul_le_mul_of_nonneg_left hnext hpowN1
  have hlastMul :
      -(r ^ (N + 2) * Real.sin θ) ≤
        r ^ (N + 2) * Real.sin (N * θ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlast hpowN2]
  have hnumerator :
      0 <
        r * Real.sin θ -
          r ^ (N + 1) * Real.sin ((N + 1 : ℕ) * θ) +
          r ^ (N + 2) * Real.sin (N * θ) := by
    have hcore : 0 < 1 - r ^ N * (1 + r) := sub_pos.mpr hbudget
    have hpows :
        r ^ (N + 1) = r * r ^ N := by
      rw [pow_succ']
    have hpows2 :
        r ^ (N + 2) = r * r ^ N * r := by
      rw [show N + 2 = (N + 1) + 1 by omega, pow_succ', hpows]
      ring
    have hlower :
        0 <
          r * Real.sin θ -
            r ^ (N + 1) * Real.sin θ -
            r ^ (N + 2) * Real.sin θ := by
      rw [hpows, hpows2]
      nlinarith [mul_pos (mul_pos hr hsin) hcore]
    linarith
  have hden := firstClockGeometricDenominator_pos (r := r) hsin
  have hid := firstClockGeometricTower_mul_denominator r θ N
  nlinarith

/-- A square-root critical radius has enough geometric decay for every tower of length at least
four. -/
lemma firstClockGeometricBudget_of_sq_le_half
    {r : ℝ} {N : ℕ}
    (hr : 0 < r) (hrSq : r ^ 2 ≤ 1 / 2) (hN : 4 ≤ N) :
    r ^ N * (1 + r) < 1 := by
  have hr0 : 0 ≤ r := hr.le
  have hrOne : r ≤ 1 := by
    nlinarith [sq_nonneg (r - 1)]
  have hrFour : r ^ 4 ≤ 1 / 4 := by
    have hmul :
        0 ≤ r ^ 2 * (1 / 2 - r ^ 2) :=
      mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrSq)
    nlinarith
  have hpow : r ^ N ≤ r ^ 4 :=
    pow_le_pow_of_le_one hr0 hrOne hN
  have hsum : 1 + r ≤ 2 := by linarith
  have hmul :
      r ^ N * (1 + r) ≤ r ^ 4 * 2 :=
    mul_le_mul hpow hsum (by positivity) (pow_nonneg hr0 4)
  nlinarith

/-- Complete first-clock tower with a fractional terminal aperture. -/
def firstClockFractionalTower
    (r δ : ℝ) (N : ℕ) : ℝ :=
  firstClockGeometricTower r
    (2 * Real.pi / ((N : ℝ) + δ)) N

/-- Every complete tower of length at least four is strictly positive at the physical first
clock, provided its critical radius satisfies `r² ≤ 1/2`. -/
theorem firstClockFractionalTower_pos_of_four_le
    {r δ : ℝ} {N : ℕ}
    (hr : 0 < r) (hrSq : r ^ 2 ≤ 1 / 2)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hN : 4 ≤ N) :
    0 < firstClockFractionalTower r δ N := by
  let T : ℝ := (N : ℝ) + δ
  let θ : ℝ := 2 * Real.pi / T
  have hTfour : 4 ≤ T := by
    have hNreal : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    dsimp only [T]
    linarith
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTfour
  have hθpos : 0 < θ := by
    dsimp only [θ]
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) hTpos
  have hθhalf : θ ≤ Real.pi / 2 := by
    dsimp only [θ]
    apply (div_le_iff₀ hTpos).2
    nlinarith [Real.pi_pos]
  have hθpi : θ < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθpi
  have hperiod : θ * T = 2 * Real.pi := by
    dsimp only [θ]
    field_simp
  have hδθ0 : 0 ≤ δ * θ := mul_nonneg hδ0 hθpos.le
  have hδθle : δ * θ ≤ θ := by
    nlinarith
  have honeδ0 : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1.le
  have honeδθ0 : 0 ≤ (1 - δ) * θ :=
    mul_nonneg honeδ0 hθpos.le
  have honeδθle : (1 - δ) * θ ≤ θ := by
    nlinarith
  have hsinδ :
      Real.sin (δ * θ) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) hθhalf hδθle
  have hsinOneδ :
      Real.sin ((1 - δ) * θ) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) hθhalf honeδθle
  have hNphase :
      (N : ℝ) * θ = 2 * Real.pi - δ * θ := by
    dsimp only [T] at hperiod
    nlinarith
  have hNextPhase :
      ((N + 1 : ℕ) : ℝ) * θ =
        (1 - δ) * θ + 2 * Real.pi := by
    push_cast
    dsimp only [T] at hperiod
    nlinarith
  have hlast :
      -Real.sin θ ≤ Real.sin ((N : ℝ) * θ) := by
    rw [hNphase, Real.sin_two_pi_sub]
    exact neg_le_neg hsinδ
  have hnext :
      Real.sin (((N + 1 : ℕ) : ℝ) * θ) ≤ Real.sin θ := by
    rw [hNextPhase, Real.sin_add_two_pi]
    exact hsinOneδ
  have hbudget :=
    firstClockGeometricBudget_of_sq_le_half hr hrSq hN
  dsimp only [firstClockFractionalTower]
  change 0 < firstClockGeometricTower r θ N
  exact firstClockGeometricTower_pos_of_terminal_bounds
    hr hbudget hsin hnext hlast

/-- A complete three-mode first-clock tower is strictly positive. -/
theorem firstClockFractionalTower_three_pos
    {r δ : ℝ}
    (hr : 0 < r) (hrSq : r ^ 2 ≤ 1 / 2)
    (hδ0 : 0 ≤ δ) :
    0 < firstClockFractionalTower r δ 3 := by
  let θ : ℝ := 2 * Real.pi / ((3 : ℝ) + δ)
  have hTpos : 0 < (3 : ℝ) + δ := by linarith
  have hθpos : 0 < θ := by
    dsimp only [θ]
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) hTpos
  have hθpi : θ < Real.pi := by
    dsimp only [θ]
    apply (div_lt_iff₀ hTpos).2
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθpi
  dsimp only [firstClockFractionalTower]
  change 0 < firstClockGeometricTower r θ 3
  exact firstClockGeometricTower_three_pos hr hrSq hsin

/-- A complete two-mode first-clock tower is nonnegative once `r ≤ 1/2`. -/
theorem firstClockFractionalTower_two_nonneg
    {r δ : ℝ}
    (hr0 : 0 ≤ r) (hrHalf : r ≤ 1 / 2)
    (hδ0 : 0 ≤ δ) :
    0 ≤ firstClockFractionalTower r δ 2 := by
  let θ : ℝ := 2 * Real.pi / ((2 : ℝ) + δ)
  have hTpos : 0 < (2 : ℝ) + δ := by linarith
  have hθpos : 0 < θ := by
    dsimp only [θ]
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) hTpos
  have hθpi : θ ≤ Real.pi := by
    dsimp only [θ]
    apply (div_le_iff₀ hTpos).2
    nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθpos.le hθpi
  dsimp only [firstClockFractionalTower]
  change 0 ≤ firstClockGeometricTower r θ 2
  exact firstClockGeometricTower_two_nonneg hr0 hrHalf hsin

/-- A complete one-mode first-clock tower lies in the counter-phased half-wave. -/
theorem firstClockFractionalTower_one_nonpos
    {r δ : ℝ} (hr0 : 0 ≤ r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    firstClockFractionalTower r δ 1 ≤ 0 := by
  let T : ℝ := 1 + δ
  let θ : ℝ := 2 * Real.pi / T
  have hTone : 1 ≤ T := by
    dsimp only [T]
    linarith
  have hTtwo : T < 2 := by
    dsimp only [T]
    linarith
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTone
  have hθleTwoPi : θ ≤ 2 * Real.pi := by
    dsimp only [θ]
    apply (div_le_iff₀ hTpos).2
    nlinarith [Real.pi_pos]
  have hpiLeθ : Real.pi ≤ θ := by
    dsimp only [θ]
    apply (le_div_iff₀ hTpos).2
    nlinarith [Real.pi_pos]
  have hres0 : 0 ≤ 2 * Real.pi - θ := sub_nonneg.mpr hθleTwoPi
  have hresPi : 2 * Real.pi - θ ≤ Real.pi := by linarith
  have hresSin :
      0 ≤ Real.sin (2 * Real.pi - θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hres0 hresPi
  have hsin : Real.sin θ ≤ 0 := by
    rw [Real.sin_two_pi_sub] at hresSin
    linarith
  have hsin' :
      Real.sin (2 * Real.pi / (1 + δ)) ≤ 0 := by
    simpa only [θ, T] using hsin
  dsimp only [firstClockFractionalTower]
  norm_num [firstClockGeometricTower, Finset.sum_range_succ]
  exact mul_nonpos_of_nonneg_of_nonpos hr0 hsin'

def criticalPrimeTowerRadius (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-1 / 2 : ℝ)

lemma criticalPrimeTowerRadius_pos
    {p : ℕ} (hp : 0 < p) :
    0 < criticalPrimeTowerRadius p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp) _

lemma criticalPrimeTowerRadius_sq
    (p : ℕ) :
    criticalPrimeTowerRadius p ^ 2 = (p : ℝ)⁻¹ := by
  rw [criticalPrimeTowerRadius, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg p)]
  norm_num [Real.rpow_neg_one]

lemma criticalPrimeTowerRadius_sq_le_half
    {p : ℕ} (hp : 2 ≤ p) :
    criticalPrimeTowerRadius p ^ 2 ≤ 1 / 2 := by
  rw [criticalPrimeTowerRadius_sq p]
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    apply (inv_le_inv₀ (a := (p : ℝ)) (b := (2 : ℝ))
      (by exact_mod_cast (show 0 < p by omega))
      (by norm_num)).2
    exact_mod_cast hp
  norm_num at hinv ⊢
  exact hinv

lemma criticalPrimeTowerRadius_le_half
    {p : ℕ} (hp : 4 ≤ p) :
    criticalPrimeTowerRadius p ≤ 1 / 2 := by
  have hr := criticalPrimeTowerRadius_pos (show 0 < p by omega)
  have hrsq := criticalPrimeTowerRadius_sq p
  have hinv :
      (p : ℝ)⁻¹ ≤ (4 : ℝ)⁻¹ :=
    (inv_le_inv₀ (a := (p : ℝ)) (b := (4 : ℝ))
      (by exact_mod_cast (show 0 < p by omega))
      (by norm_num : (0 : ℝ) < 4)).2 (by exact_mod_cast hp)
  norm_num at hinv
  nlinarith

theorem criticalPrimeFractionalTower_pos_of_three_le
    {p N : ℕ} {δ : ℝ}
    (hp : p.Prime) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hN : 3 ≤ N) :
    0 < firstClockFractionalTower
      (criticalPrimeTowerRadius p) δ N := by
  have hr := criticalPrimeTowerRadius_pos hp.pos
  have hrSq := criticalPrimeTowerRadius_sq_le_half hp.two_le
  rcases eq_or_lt_of_le hN with rfl | hNfour
  · exact firstClockFractionalTower_three_pos hr hrSq hδ0
  · exact firstClockFractionalTower_pos_of_four_le
      hr hrSq hδ0 hδ1 (by omega)

theorem criticalPrimeFractionalTower_two_nonneg_of_five_le
    {p : ℕ} {δ : ℝ}
    (hp : p.Prime) (hpFive : 5 ≤ p)
    (hδ0 : 0 ≤ δ) :
    0 ≤ firstClockFractionalTower
      (criticalPrimeTowerRadius p) δ 2 := by
  exact firstClockFractionalTower_two_nonneg
    (criticalPrimeTowerRadius_pos hp.pos).le
    (criticalPrimeTowerRadius_le_half (by omega))
    hδ0

/-- Prime-first finite reindexing of any sum supported on prime powers. -/
theorem sum_primePow_Icc_eq_sum_primesLE
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∑ m ∈ (Finset.Icc 1 n).filter IsPrimePow, f m =
      ∑ p ∈ Nat.primesLE n,
        ∑ e ∈ Finset.Icc 1 (p.log n), f (p ^ e) := by
  have hset :
      (Finset.Icc 1 n).filter IsPrimePow =
        ((Finset.Icc 1 n).filter Nat.Prime).biUnion
          (fun p ↦ Finset.image (p ^ ·) (Finset.Icc 1 (p.log n))) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion,
      Finset.mem_image]
    constructor
    · rintro ⟨hq, hqpow⟩
      obtain ⟨p, e, hp, he, rfl⟩ :=
        (isPrimePow_nat_iff q).mp hqpow
      have hpn : p ≤ n :=
        (Nat.le_of_dvd (by lia) (dvd_pow_self p he.ne')).trans hq.2
      exact ⟨p, ⟨⟨hp.one_le, hpn⟩, hp⟩, e,
        ⟨by omega, Nat.le_log_of_pow_le hp.one_lt hq.2⟩, rfl⟩
    · rintro ⟨p, ⟨hpIcc, hp⟩, e, he, rfl⟩
      exact ⟨
        ⟨by
          exact one_le_pow₀ hp.one_le,
          Nat.pow_le_of_le_log (by omega) he.2⟩,
        (isPrimePow_nat_iff (p ^ e)).2
          ⟨p, e, hp, by omega, rfl⟩⟩
  calc
    ∑ m ∈ (Finset.Icc 1 n).filter IsPrimePow, f m =
        ∑ m ∈ ((Finset.Icc 1 n).filter Nat.Prime).biUnion
          (fun p ↦ Finset.image (p ^ ·) (Finset.Icc 1 (p.log n))), f m := by
      rw [hset]
    _ = ∑ p ∈ Finset.Icc 1 n with p.Prime,
          ∑ q ∈ Finset.image (fun e ↦ p ^ e) (Finset.Icc 1 (p.log n)), f q := by
      rw [Finset.sum_biUnion <| by
        rw [Finset.pairwiseDisjoint_iff]
        grind [Nat.Prime.pow_inj']]
    _ = ∑ p ∈ Nat.primesLE n,
          ∑ e ∈ Finset.Icc 1 (p.log n), f (p ^ e) := by
      refine Finset.sum_congr (Nat.primesLE_eq_filter_Icc_one n).symm
        fun p hp ↦ ?_
      exact Finset.sum_image fun a _ b _ hab ↦
        Nat.pow_right_injective
          (Nat.two_le_of_mem_primesLE hp) hab

/-- Literal first-clock prime mass, reindexed as complete one-prime towers. -/
theorem ccmFirstClockPrimeSineMass_eq_sum_primePower_towers
    (L ξ : ℝ) :
    ccmFirstClockPrimeSineMass L ξ =
      ∑ p ∈ Nat.primesLE ⌊Real.exp L⌋₊,
        ∑ e ∈ Finset.Icc 1 (p.log ⌊Real.exp L⌋₊),
          criticalMellinAtomWeight (p ^ e) *
            Real.sin (ξ * Real.log (p ^ e)) := by
  rw [ccmFirstClockPrimeSineMass]
  let n : ℕ := ⌊Real.exp L⌋₊
  let f : ℕ → ℝ := fun k =>
    criticalMellinAtomWeight k * Real.sin (ξ * Real.log k)
  have hrestrict :
      (∑ k ∈ Finset.Icc 2 n, f k) =
        ∑ k ∈ (Finset.Icc 1 n).filter IsPrimePow, f k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      exact ⟨(IsPrimePow.one_lt hk.2), hk.1.2⟩
    · intro k hk hnot
      have hkIcc : 2 ≤ k ∧ k ≤ n := by
        simpa only [Finset.mem_Icc] using hk
      have hnpp : ¬IsPrimePow k := by
        intro hkpp
        have hkfilter :
            k ∈ (Finset.Icc 1 n).filter IsPrimePow := by
          simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, hkIcc.2⟩, hkpp⟩
        exact hnot hkfilter
      dsimp only [f, criticalMellinAtomWeight]
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnpp]
      ring
  change (∑ k ∈ Finset.Icc 2 n, f k) = _
  rw [hrestrict, sum_primePow_Icc_eq_sum_primesLE]
  simp only [n, f, Nat.cast_pow]

/-- One complete prime-power tower in the literal first-clock mass. -/
def ccmFirstClockPrimePowerTowerMass
    (L ξ : ℝ) (p : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 (p.log ⌊Real.exp L⌋₊),
    criticalMellinAtomWeight (p ^ e) *
      Real.sin (ξ * Real.log (p ^ e))

theorem ccmFirstClockPrimeSineMass_eq_sum_primePowerTowerMass
    (L ξ : ℝ) :
    ccmFirstClockPrimeSineMass L ξ =
      ∑ p ∈ Nat.primesLE ⌊Real.exp L⌋₊,
        ccmFirstClockPrimePowerTowerMass L ξ p := by
  exact ccmFirstClockPrimeSineMass_eq_sum_primePower_towers L ξ

lemma criticalMellinAtomWeight_prime_pow
    {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    criticalMellinAtomWeight (p ^ e) =
      Real.log p * criticalPrimeTowerRadius p ^ e := by
  rw [criticalMellinAtomWeight,
    ArithmeticFunction.vonMangoldt_apply_pow he,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    Nat.cast_pow]
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [← Real.rpow_natCast_mul hp0]
  dsimp only [criticalPrimeTowerRadius]
  rw [show (e : ℝ) * (-1 / 2 : ℝ) =
      (-1 / 2 : ℝ) * (e : ℝ) by ring,
    Real.rpow_mul_natCast hp0]
  ring

lemma real_log_prime_pow
    {p e : ℕ} :
    Real.log (p ^ e) = (e : ℝ) * Real.log p := by
  rw [Real.log_pow]

theorem ccmFirstClockPrimePowerTowerMass_eq_geometric
    {L ξ : ℝ} {p : ℕ} (hp : p.Prime) :
    ccmFirstClockPrimePowerTowerMass L ξ p =
      Real.log p *
        firstClockGeometricTower
          (criticalPrimeTowerRadius p) (ξ * Real.log p)
          (p.log ⌊Real.exp L⌋₊) := by
  let N : ℕ := p.log ⌊Real.exp L⌋₊
  let r : ℝ := criticalPrimeTowerRadius p
  let θ : ℝ := ξ * Real.log p
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [ccmFirstClockPrimePowerTowerMass]
  change
    (∑ e ∈ Finset.Icc 1 N,
      criticalMellinAtomWeight (p ^ e) *
        Real.sin (ξ * Real.log (p ^ e))) =
      Real.log p * firstClockGeometricTower r θ N
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [firstClockGeometricTower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [criticalMellinAtomWeight_prime_pow hp (by omega),
    real_log_prime_pow]
  dsimp only [r, θ]
  push_cast
  ring_nf

/-- Number of admitted powers in the complete `p`-tower at aperture `L`. -/
def ccmFirstClockPrimePowerLength (L : ℝ) (p : ℕ) : ℕ :=
  p.log ⌊Real.exp L⌋₊

/-- Fractional part of the logarithmic tower length. -/
def ccmFirstClockPrimePowerFraction (L : ℝ) (p : ℕ) : ℝ :=
  L / Real.log p - ccmFirstClockPrimePowerLength L p

lemma ccmFirstClockPrimePowerFraction_nonneg
    {L : ℝ} {p : ℕ} (hp : p.Prime)
    (hpCut : p ≤ ⌊Real.exp L⌋₊) :
    0 ≤ ccmFirstClockPrimePowerFraction L p := by
  let n : ℕ := ⌊Real.exp L⌋₊
  let N : ℕ := p.log n
  have hn0 : n ≠ 0 := by
    dsimp only [n]
    exact (lt_of_lt_of_le hp.pos hpCut).ne'
  have hpowNat : p ^ N ≤ n := Nat.pow_log_le_self p hn0
  have hpowExp : ((p ^ N : ℕ) : ℝ) ≤ Real.exp L := by
    exact (Nat.le_floor_iff (Real.exp_pos L).le).mp
      (hpowNat.trans_eq (by rfl))
  have hpowPos : (0 : ℝ) < (p ^ N : ℕ) := by
    exact_mod_cast pow_pos hp.pos N
  have hlogLower :
      (N : ℝ) * Real.log p ≤ L := by
    have h :=
      (Real.log_le_iff_le_exp hpowPos).2 hpowExp
    rw [Nat.cast_pow, Real.log_pow] at h
    exact h
  have hlogp : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [ccmFirstClockPrimePowerFraction,
    ccmFirstClockPrimePowerLength]
  dsimp only [N, n] at hlogLower
  exact sub_nonneg.mpr ((le_div_iff₀ hlogp).2 hlogLower)

lemma ccmFirstClockPrimePowerFraction_lt_one
    {L : ℝ} {p : ℕ} (hp : p.Prime) :
    ccmFirstClockPrimePowerFraction L p < 1 := by
  let n : ℕ := ⌊Real.exp L⌋₊
  let N : ℕ := p.log n
  have hpowNat : n < p ^ (N + 1) := by
    simpa only [N, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hp.one_lt n
  have hExpPow : Real.exp L < ((p ^ (N + 1) : ℕ) : ℝ) := by
    exact (Nat.floor_lt (Real.exp_pos L).le).mp hpowNat
  have hpowPos : (0 : ℝ) < (p ^ (N + 1) : ℕ) := by
    exact_mod_cast pow_pos hp.pos (N + 1)
  have hlogUpper :
      L < ((N + 1 : ℕ) : ℝ) * Real.log p := by
    have h :=
      (Real.lt_log_iff_exp_lt hpowPos).2 hExpPow
    rw [Nat.cast_pow, Real.log_pow] at h
    exact h
  have hlogp : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [ccmFirstClockPrimePowerFraction,
    ccmFirstClockPrimePowerLength]
  dsimp only [N, n] at hlogUpper
  have hdiv :
      L / Real.log p < (N : ℝ) + 1 := by
    apply (div_lt_iff₀ hlogp).2
    push_cast at hlogUpper
    nlinarith
  have hdiv' :
      L / Real.log p <
        (p.log ⌊Real.exp L⌋₊ : ℝ) + 1 := by
    simpa only [N, n] using hdiv
  linarith

lemma ccmFirstClock_primePower_phase_eq_fractional
    {L : ℝ} {p : ℕ} (hL : 0 < L) (hp : p.Prime) :
    (2 * Real.pi / L) * Real.log p =
      2 * Real.pi /
        ((ccmFirstClockPrimePowerLength L p : ℝ) +
          ccmFirstClockPrimePowerFraction L p) := by
  have hlogp : Real.log p ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [ccmFirstClockPrimePowerFraction]
  field_simp [hL.ne', hlogp]
  ring

/-- The literal first-clock `p`-tower is exactly the fractional damped-sine packet. -/
theorem ccmFirstClockPrimePowerTowerMass_firstClock_eq_fractional
    {L : ℝ} {p : ℕ} (hL : 0 < L) (hp : p.Prime) :
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p =
      Real.log p *
        firstClockFractionalTower
          (criticalPrimeTowerRadius p)
          (ccmFirstClockPrimePowerFraction L p)
          (ccmFirstClockPrimePowerLength L p) := by
  rw [ccmFirstClockPrimePowerTowerMass_eq_geometric hp]
  unfold firstClockFractionalTower
  rw [ccmFirstClock_primePower_phase_eq_fractional hL hp]
  rfl

/-- Every literal complete first-clock prime tower with at least three admitted modes is strictly
positive. -/
theorem ccmFirstClockPrimePowerTowerMass_firstClock_pos_of_three_le
    {L : ℝ} {p : ℕ} (hL : 0 < L) (hp : p.Prime)
    (hpCut : p ≤ ⌊Real.exp L⌋₊)
    (hLength : 3 ≤ ccmFirstClockPrimePowerLength L p) :
    0 < ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p := by
  rw [ccmFirstClockPrimePowerTowerMass_firstClock_eq_fractional hL hp]
  apply mul_pos
  · exact Real.log_pos (by exact_mod_cast hp.one_lt)
  · exact criticalPrimeFractionalTower_pos_of_three_le hp
      (ccmFirstClockPrimePowerFraction_nonneg hp hpCut)
      (ccmFirstClockPrimePowerFraction_lt_one hp)
      hLength

/-- Every literal complete two-mode tower at a prime `p ≥ 5` is nonnegative. -/
theorem ccmFirstClockPrimePowerTowerMass_firstClock_nonneg_of_length_two_of_five_le
    {L : ℝ} {p : ℕ} (hL : 0 < L) (hp : p.Prime)
    (hpCut : p ≤ ⌊Real.exp L⌋₊)
    (hLength : ccmFirstClockPrimePowerLength L p = 2)
    (hpFive : 5 ≤ p) :
    0 ≤ ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p := by
  rw [ccmFirstClockPrimePowerTowerMass_firstClock_eq_fractional hL hp,
    hLength]
  exact mul_nonneg
    (Real.log_pos (by exact_mod_cast hp.one_lt)).le
    (criticalPrimeFractionalTower_two_nonneg_of_five_le hp hpFive
      (ccmFirstClockPrimePowerFraction_nonneg hp hpCut))

/-- Every literal one-mode prime tower is nonpositive. -/
theorem ccmFirstClockPrimePowerTowerMass_firstClock_nonpos_of_length_one
    {L : ℝ} {p : ℕ} (hL : 0 < L) (hp : p.Prime)
    (hpCut : p ≤ ⌊Real.exp L⌋₊)
    (hLength : ccmFirstClockPrimePowerLength L p = 1) :
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p ≤ 0 := by
  rw [ccmFirstClockPrimePowerTowerMass_firstClock_eq_fractional hL hp,
    hLength]
  exact mul_nonpos_of_nonneg_of_nonpos
    (Real.log_pos (by exact_mod_cast hp.one_lt)).le
    (firstClockFractionalTower_one_nonpos
      (criticalPrimeTowerRadius_pos hp.pos).le
      (ccmFirstClockPrimePowerFraction_nonneg hp hpCut)
      (ccmFirstClockPrimePowerFraction_lt_one hp))

/-- Tower contribution already proved nonnegative by the local classification. -/
def ccmFirstClockStableTowerTerm (L : ℝ) (p : ℕ) : ℝ :=
  if 3 ≤ ccmFirstClockPrimePowerLength L p ∨
      (ccmFirstClockPrimePowerLength L p = 2 ∧ 5 ≤ p) then
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p
  else
    0

/-- Positive part of the only unresolved two-mode towers, necessarily at `p=2` or `p=3`. -/
def ccmFirstClockSmallSquarePositiveTerm (L : ℝ) (p : ℕ) : ℝ :=
  if ccmFirstClockPrimePowerLength L p = 2 ∧ p < 5 then
    max (ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p) 0
  else
    0

/-- Good mass after complete prime-power tower collapse. -/
def ccmFirstClockReducedGoodTowerMass (L : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp L⌋₊,
    (ccmFirstClockStableTowerTerm L p +
      ccmFirstClockSmallSquarePositiveTerm L p)

/-- Remaining negative mass: one-mode outer primes plus negative parts of the `p=2,3`
two-mode towers. -/
def ccmFirstClockReducedBadTowerResidual (L : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp L⌋₊,
    if ccmFirstClockPrimePowerLength L p = 1 then
      -ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p
    else if ccmFirstClockPrimePowerLength L p = 2 ∧ p < 5 then
      max (-ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p) 0
    else
      0

lemma ccmFirstClockPrimePowerLength_pos_of_mem_primesLE
    {L : ℝ} {p : ℕ}
    (hpMem : p ∈ Nat.primesLE ⌊Real.exp L⌋₊) :
    0 < ccmFirstClockPrimePowerLength L p := by
  rw [ccmFirstClockPrimePowerLength]
  exact Nat.log_pos
    (Nat.prime_of_mem_primesLE hpMem).one_lt
    (Nat.le_of_mem_primesLE hpMem)

lemma ccmFirstClockPrimePowerTowerTerm_eq_reducedGood_sub_bad
    {L : ℝ} {p : ℕ}
    (hpMem : p ∈ Nat.primesLE ⌊Real.exp L⌋₊) :
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p =
      (ccmFirstClockStableTowerTerm L p +
        ccmFirstClockSmallSquarePositiveTerm L p) -
      (if ccmFirstClockPrimePowerLength L p = 1 then
        -ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p
      else if ccmFirstClockPrimePowerLength L p = 2 ∧ p < 5 then
        max (-ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p) 0
      else
        0) := by
  let N := ccmFirstClockPrimePowerLength L p
  let T := ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p
  change
    T =
      ((if 3 ≤ N ∨ (N = 2 ∧ 5 ≤ p) then T else 0) +
        if N = 2 ∧ p < 5 then max T 0 else 0) -
      (if N = 1 then -T
      else if N = 2 ∧ p < 5 then max (-T) 0
      else 0)
  have hNpos : 0 < N :=
    ccmFirstClockPrimePowerLength_pos_of_mem_primesLE hpMem
  by_cases hNthree : 3 ≤ N
  · have hNneOne : N ≠ 1 := by omega
    have hNneTwo : N ≠ 2 := by omega
    simp [hNthree, hNneOne, hNneTwo]
  · have hNle : N ≤ 2 := by omega
    by_cases hNtwo : N = 2
    · by_cases hpFive : 5 ≤ p
      · have hpNotLt : ¬p < 5 := by omega
        simp [hNtwo, hpFive, hpNotLt]
      · have hpLt : p < 5 := by omega
        simp [hNtwo, hpFive, hpLt]
    · have hNone : N = 1 := by omega
      simp [hNone]

theorem ccmFirstClockReducedGoodTowerMass_nonneg
    {L : ℝ} (hL : 0 < L) :
    0 ≤ ccmFirstClockReducedGoodTowerMass L := by
  rw [ccmFirstClockReducedGoodTowerMass]
  apply Finset.sum_nonneg
  intro p hpMem
  have hp := Nat.prime_of_mem_primesLE hpMem
  have hpCut := Nat.le_of_mem_primesLE hpMem
  apply add_nonneg
  · rw [ccmFirstClockStableTowerTerm]
    split_ifs with hstable
    · rcases hstable with hthree | ⟨htwo, hpFive⟩
      · exact
          (ccmFirstClockPrimePowerTowerMass_firstClock_pos_of_three_le
            hL hp hpCut hthree).le
      · exact
          ccmFirstClockPrimePowerTowerMass_firstClock_nonneg_of_length_two_of_five_le
            hL hp hpCut htwo hpFive
    · exact le_rfl
  · rw [ccmFirstClockSmallSquarePositiveTerm]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl

theorem ccmFirstClockReducedBadTowerResidual_nonneg
    {L : ℝ} (hL : 0 < L) :
    0 ≤ ccmFirstClockReducedBadTowerResidual L := by
  rw [ccmFirstClockReducedBadTowerResidual]
  apply Finset.sum_nonneg
  intro p hpMem
  have hp := Nat.prime_of_mem_primesLE hpMem
  have hpCut := Nat.le_of_mem_primesLE hpMem
  split_ifs with hOne hSmall
  · exact neg_nonneg.mpr
      (ccmFirstClockPrimePowerTowerMass_firstClock_nonpos_of_length_one
        hL hp hpCut hOne)
  · exact le_max_right _ _
  · exact le_rfl

/-- Exact source decomposition after collapsing every unconditionally oriented complete tower. -/
theorem ccmFirstClockPrimeSineMass_eq_reducedGood_sub_bad
    {L : ℝ} :
    ccmFirstClockPrimeSineMass L (2 * Real.pi / L) =
      ccmFirstClockReducedGoodTowerMass L -
        ccmFirstClockReducedBadTowerResidual L := by
  rw [ccmFirstClockPrimeSineMass_eq_sum_primePowerTowerMass,
    ccmFirstClockReducedGoodTowerMass,
    ccmFirstClockReducedBadTowerResidual,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hpMem
  exact ccmFirstClockPrimePowerTowerTerm_eq_reducedGood_sub_bad hpMem

/-- Reduced source frontier after all one-prime tower geometry has been discharged. -/
def CCMFirstClockReducedTowerDominance : Prop :=
  ∀ L : ℝ, Real.pi / 2 ≤ L →
    ccmFirstClockReducedBadTowerResidual L ≤
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ccmFirstClockReducedGoodTowerMass L

theorem ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_reducedTowerDominance
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    0 ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) ↔
      ccmFirstClockReducedBadTowerResidual L ≤
        ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
          ccmFirstClockReducedGoodTowerMass L := by
  rw [ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_primeMass hL,
    ccmFirstClockPrimeSineMass_eq_reducedGood_sub_bad]
  constructor <;> intro h <;> linarith

theorem ccmFirstClockReducedTowerDominance_iff_publishedSourceNonnegative :
    CCMFirstClockReducedTowerDominance ↔
      CCMFirstClockPublishedSourceNonnegative := by
  constructor
  · intro hdom L hL
    exact
      (ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_reducedTowerDominance
        hL).2 (hdom L hL)
  · intro hsource L hL
    exact
      (ccmPublishedSourceSineCoefficient_firstClock_nonneg_iff_reducedTowerDominance
        hL).1 (hsource L hL)

/-- RH is equivalent to absorbing only irreducible outer-prime mass and the two small square
windows after every other complete prime-power tower has been proved nonnegative. -/
theorem ccmFirstClockReducedTowerDominance_iff_rh :
    CCMFirstClockReducedTowerDominance ↔ RiemannHypothesis := by
  rw [ccmFirstClockReducedTowerDominance_iff_publishedSourceNonnegative,
    ccmFirstClockPublishedSourceNonnegative_iff_rh]

end RHTower
