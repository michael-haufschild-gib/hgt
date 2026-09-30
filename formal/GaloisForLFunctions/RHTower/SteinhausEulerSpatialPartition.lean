import GaloisForLFunctions.RHTower.SteinhausEulerSecondMoment
import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# Uniform finite Euler second moments near the critical line

At radius `1 / (16 * (1 + log N))`, the arithmetic partition function remains
within a fixed factor of its critical value throughout the resulting half-strip.
The proof bounds each shifted prime factor by an exponential prime-log cost and
uses the proved elementary upper bound for `sum (log p)/p`.

The exact critical partition also dominates both one and `log N`, so it absorbs
the reciprocal-radius cost in the forthcoming spatial mean-square estimate.
Every moment bound specializes the literal product identity already proved;
no probabilistic moment, Mertens asymptotic, or recurrence premise is supplied.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower
open SteinhausModel
open GaloisForLFunctions.RHTower

/-- A pole-free radius at the reciprocal logarithmic scale. -/
def steinhausEulerSpatialRadius (N : ℕ) : ℝ := (16 * (1 + Real.log N))⁻¹

private theorem spatial_radius_bounds {N : ℕ} (hN : 3 ≤ N) :
    0 < steinhausEulerSpatialRadius N ∧ steinhausEulerSpatialRadius N ≤ 1 / 16 ∧
      steinhausEulerSpatialRadius N * (1 + Real.log N) = 1 / 16 := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hL : 0 < 1 + Real.log (N : ℝ) := by linarith
  have hr : 0 < steinhausEulerSpatialRadius N := by unfold steinhausEulerSpatialRadius; positivity
  have heq : steinhausEulerSpatialRadius N * (1 + Real.log N) = 1 / 16 := by
    unfold steinhausEulerSpatialRadius
    field_simp
  refine ⟨hr, ?_, heq⟩
  nlinarith [mul_nonneg hr.le hlog]

theorem steinhausEulerSpatialRadius_pos {N : ℕ} (hN : 3 ≤ N) :
    0 < steinhausEulerSpatialRadius N := (spatial_radius_bounds hN).1

/-- The spatial radius stays uniformly inside the positive half-plane. -/
theorem steinhausEulerSpatialRadius_le {N : ℕ} (hN : 3 ≤ N) :
    steinhausEulerSpatialRadius N ≤ 1 / 16 := (spatial_radius_bounds hN).2.1

private theorem prime_factor_shift_le {N p : ℕ} (hN : 3 ≤ N) (hp : p.Prime) (hpN : p ≤ N)
    {σ : ℝ} (hσ : 1 / 2 - steinhausEulerSpatialRadius N ≤ σ) :
    (1 - (p : ℝ) ^ (-(2 * σ)))⁻¹ ≤
      Real.exp (8 * steinhausEulerSpatialRadius N * Real.exp 1 * (Real.log p / p)) *
        (1 - (p : ℝ)⁻¹)⁻¹ := by
  obtain ⟨hr, hr16, hrL⟩ := spatial_radius_bounds hN
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hp0 (by exact_mod_cast hpN)
  let a : ℝ := (p : ℝ)⁻¹
  let b : ℝ := (p : ℝ) ^ (-(2 * σ))
  let t : ℝ := 2 * steinhausEulerSpatialRadius N * Real.log p
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a ≤ 1 / 2 := by
    simpa only [a, inv_eq_one_div] using (inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2)
  have hb : b ≤ 3 / 4 := by
    calc
      b ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = steinhausCriticalPrimeRadius p := by simp [steinhausCriticalPrimeRadius, randomEulerRadius, hp]
      _ ≤ _ := steinhausCriticalPrimeRadius_le p
  have hb1 : 0 < 1 - b := by linarith
  have ha1 : 0 < 1 - a := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hlog hr.le
    dsimp [t]
    nlinarith
  have hbt : b ≤ a * Real.exp t := by
    calc
      b = Real.exp (Real.log p * (-(2 * σ))) := Real.rpow_def_of_pos hp0 _
      _ ≤ Real.exp (-Real.log p + t) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left hσ hlp
        dsimp [t]
        nlinarith
      _ = a * Real.exp t := by rw [Real.exp_add, Real.exp_neg, Real.exp_log hp0]
  have he : Real.exp t - 1 ≤ t * Real.exp t := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hh
    nlinarith
  let q : ℝ := a * t * Real.exp 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hd : b - a ≤ q := by
    have hm := mul_le_mul_of_nonneg_left
      (he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht1) ht0)) ha
    dsimp [q]
    nlinarith [hbt]
  have hratio : (1 - a) / (1 - b) ≤ Real.exp (4 * q) := by
    have hlin : (1 - a) / (1 - b) ≤ 1 + 4 * q := by
      apply (div_le_iff₀ hb1).mpr
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hb)]
    exact hlin.trans (by linarith [Real.add_one_le_exp (4 * q)])
  change (1 - b)⁻¹ ≤ Real.exp (8 * steinhausEulerSpatialRadius N * Real.exp 1 *
    (Real.log p / p)) * (1 - a)⁻¹
  calc
    (1 - b)⁻¹ = ((1 - a) / (1 - b)) * (1 - a)⁻¹ := by field_simp
    _ ≤ Real.exp (4 * q) * (1 - a)⁻¹ :=
      mul_le_mul_of_nonneg_right hratio (inv_pos.mpr ha1).le
    _ = _ := by
      congr 2
      dsimp [q, a, t]
      ring

/-- A single absolute constant controls the moment throughout the narrow critical strip. -/
def steinhausEulerSpatialMomentConstant : ℝ := Real.exp (8 * Real.exp 1 * (1 + Real.log 4))

theorem steinhausEulerSpatialMomentConstant_pos : 0 < steinhausEulerSpatialMomentConstant :=
  Real.exp_pos _

/-- Uniform arithmetic partition comparison on the literal reciprocal-logarithmic strip. -/
theorem steinhausEulerPartition_le_spatial {N : ℕ} (hN : 3 ≤ N) {σ : ℝ}
    (hσ : 1 / 2 - steinhausEulerSpatialRadius N ≤ σ) :
    steinhausEulerPartition (Nat.primesBelow N) σ ≤
      steinhausEulerSpatialMomentConstant * steinhausEulerPartition (Nat.primesBelow N) (1 / 2) := by
  obtain ⟨hr, hr16, hrL⟩ := spatial_radius_bounds hN
  have hs : 0 < σ := by linarith
  have hsum : (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) / p) ≤ Real.log N + Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (Sieve.mertensFirst_upper (show 1 ≤ N by omega))
    · intro p hp
      obtain ⟨hpN, hpp⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpN.le, hpp⟩
    · intro p hp _
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))
        (Nat.cast_nonneg _)
  have hexp : 8 * steinhausEulerSpatialRadius N * Real.exp 1 *
      (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) / p) ≤
      8 * Real.exp 1 * (1 + Real.log 4) := by
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    have hfirst := mul_le_mul_of_nonneg_left hsum hr.le
    have hlast := mul_le_mul_of_nonneg_right (show steinhausEulerSpatialRadius N ≤ 1 by linarith) hlog4
    have hmid : steinhausEulerSpatialRadius N *
        (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) / p) ≤ 1 + Real.log 4 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hmid (by positivity : 0 ≤ 8 * Real.exp 1)
    nlinarith
  calc
    _ ≤ ∏ p ∈ Nat.primesBelow N,
        Real.exp (8 * steinhausEulerSpatialRadius N * Real.exp 1 * (Real.log p / p)) *
          (1 - (p : ℝ)⁻¹)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        have hlt := (prime_rpow_neg_le_rho (by linarith : 0 < 2 * σ)
          (Nat.mem_primesBelow.mp hp).2).trans_lt (randomEulerRho_lt_one (by linarith))
        exact (inv_pos.mpr (sub_pos.mpr hlt)).le
      · intro p hp
        exact prime_factor_shift_le hN (Nat.mem_primesBelow.mp hp).2
          (Nat.mem_primesBelow.mp hp).1.le hσ
    _ = Real.exp (8 * steinhausEulerSpatialRadius N * Real.exp 1 *
        (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) / p)) *
          steinhausEulerPartition (Nat.primesBelow N) (1 / 2) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum, steinhausEulerPartition_half]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
      (steinhausEulerPartition_pos _ (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (by norm_num)).le

/-- The uniform strip comparison is an actual second-moment bound for the finite Euler product. -/
theorem integral_norm_sq_steinhausFiniteEulerProduct_le_spatial {N : ℕ} (hN : 3 ≤ N) {s : ℂ}
    (hs : 1 / 2 - steinhausEulerSpatialRadius N ≤ s.re) :
    (∫ ω, ‖steinhausFiniteEulerProduct (Nat.primesBelow N) s ω‖ ^ 2 ∂steinhausMeasure) ≤
      steinhausEulerSpatialMomentConstant * steinhausEulerPartition (Nat.primesBelow N) (1 / 2) := by
  have hs0 : 0 < s.re := by have := (spatial_radius_bounds hN).2.1; linarith
  rw [integral_norm_sq_steinhausFiniteEulerProduct _ (fun _ hp => (Nat.mem_primesBelow.mp hp).2) hs0]
  exact steinhausEulerPartition_le_spatial hN hs

/-- The exact critical partition dominates the harmonic logarithmic lower bound. -/
theorem log_le_steinhausEulerPartition_half {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ≤ steinhausEulerPartition (Nat.primesBelow N) (1 / 2) := by
  have hh := harmonic_le_prod_primesBelow (N - 1)
  have hl := log_add_one_le_harmonic (N - 1)
  rw [Nat.sub_add_cancel hN] at hh hl
  rw [steinhausEulerPartition_half]
  apply le_trans _ hh
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using hl

/-- The critical partition is at least one, including an empty prime cutoff. -/
theorem one_le_steinhausEulerPartition_half (N : ℕ) :
    1 ≤ steinhausEulerPartition (Nat.primesBelow N) (1 / 2) := by
  rw [steinhausEulerPartition_half]
  apply Finset.one_le_prod
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
  have hi : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := by norm_num at hi; linarith
  rw [← one_div]
  apply (le_div_iff₀ hpos).mpr
  have : 0 ≤ (p : ℝ)⁻¹ := by positivity
  nlinarith

/-- The reciprocal spatial radius costs at most a fixed multiple of the exact partition. -/
theorem one_add_log_le_two_mul_steinhausEulerPartition_half {N : ℕ} (hN : 1 ≤ N) :
    1 + Real.log N ≤ 2 * steinhausEulerPartition (Nat.primesBelow N) (1 / 2) := by
  have := log_le_steinhausEulerPartition_half hN
  have := one_le_steinhausEulerPartition_half N
  linarith

end RHTower
