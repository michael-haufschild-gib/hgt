import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesJetStability
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume

/-!
# Prime-valuation Hellinger--Rees reflection fracture

The finite-prime Hellinger affinity between the critical geometric valuation law and its coherent
radial twist has a reflection-asymmetric Rees type.  This module works with the squared affinity,
which removes an inessential outer square root while preserving zero, positivity, and all-orders
flatness.

For every radial parameter in the strip `|c| < 1/2`, the finite-prime product is flat beyond
every power of the canonical Wold vacuum scale exactly when `c > 0`.  Consequently every
noncritical reflected pair `c, -c` has opposite asymptotic types.  Every operator family whose
full norm has any fixed finite Rees order preserves the flat radical, in arbitrary dimension, and
therefore cannot sew the reflected pair.
-/

open Filter Asymptotics
open GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

def squaredHellingerAffinity (q r u : ℝ) : ℝ :=
  (1 - q) * (1 - r) / (1 - u) ^ 2

theorem inv_one_sub_sq_le_exp_six_mul
    {u : ℝ} (hu0 : 0 ≤ u) (huHalf : u ≤ 1 / 2) :
    1 / (1 - u) ^ 2 ≤ Real.exp (6 * u) := by
  have hden : 0 < (1 - u) ^ 2 := by
    exact sq_pos_of_pos (sub_pos.mpr (by linarith))
  have hpoly : 0 ≤ u * (2 * u - 1) * (3 * u - 4) := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hu0 (by linarith))
      (by linarith)
  have hrat : 1 / (1 - u) ^ 2 ≤ 1 + 6 * u := by
    rw [div_le_iff₀ hden]
    nlinarith
  exact hrat.trans
    (by simpa [add_comm] using Real.add_one_le_exp (6 * u))

theorem squaredHellingerAffinity_nonneg
    {q r u : ℝ} (hq1 : q ≤ 1) (hr1 : r ≤ 1) :
    0 ≤ squaredHellingerAffinity q r u := by
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hq1)
    (sub_nonneg.mpr hr1)) (sq_nonneg _)

theorem squaredHellingerAffinity_self
    {q : ℝ} (hq : q ≠ 1) :
    squaredHellingerAffinity q q q = 1 := by
  rw [squaredHellingerAffinity, ← pow_two]
  exact div_self (pow_ne_zero 2 (sub_ne_zero.mpr hq.symm))

theorem squaredHellingerAffinity_le_one
    {q r u : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hu1 : u < 1) (hu2 : u ^ 2 = q * r) :
    squaredHellingerAffinity q r u ≤ 1 := by
  have hden : 0 < (1 - u) ^ 2 := sq_pos_of_pos (sub_pos.mpr hu1)
  rw [squaredHellingerAffinity, div_le_one hden]
  nlinarith [sq_nonneg (q - r)]

theorem one_sub_q_le_squaredHellingerAffinity
    {q r u : ℝ} (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hu1 : u < 1)
    (hu2 : u ^ 2 = q * r) (hru : r ≤ u) :
    1 - q ≤ squaredHellingerAffinity q r u := by
  have hden : 0 < (1 - u) ^ 2 := sq_pos_of_pos (sub_pos.mpr hu1)
  rw [squaredHellingerAffinity, le_div_iff₀ hden]
  have hu2le : u ^ 2 ≤ r := by
    rw [hu2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hr0]
  nlinarith

theorem squaredHellingerAffinity_le_one_sub_quarter_r
    {q r u : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : u ^ 2 = q * r) (hu : 8 * u ≤ 3 * r) :
    squaredHellingerAffinity q r u ≤ 1 - r / 4 := by
  have hden : 0 < (1 - u) ^ 2 := sq_pos_of_pos (sub_pos.mpr hu1)
  rw [squaredHellingerAffinity, div_le_iff₀ hden]
  have hden_le : (1 - u) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg u]
  nlinarith

theorem squaredHellingerAffinity_le_woldPower
    {q r u : ℝ} (L : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : u ^ 2 = q * r)
    (hu : 8 * u ≤ 3 * r)
    (hqr : 4 * (L : ℝ) * q ≤ r) :
    squaredHellingerAffinity q r u ≤ (1 - q) ^ L := by
  calc
    squaredHellingerAffinity q r u ≤ 1 - r / 4 :=
      squaredHellingerAffinity_le_one_sub_quarter_r
        hq0 hr0 hr1 hu0 hu1 hu2 hu
    _ ≤ 1 - (L : ℝ) * q := by linarith
    _ = 1 + (L : ℝ) * (-q) := by ring
    _ ≤ (1 + (-q)) ^ L :=
      one_add_mul_le_pow (by linarith) L
    _ = (1 - q) ^ L := by ring_nf

def primeRadialCriticalMass (p : Nat.Primes) : ℝ :=
  ((p.1 : ℝ))⁻¹

def primeRadialTwistedMass (c : ℝ) (p : Nat.Primes) : ℝ :=
  (p.1 : ℝ) ^ (-(1 - 2 * c))

def primeRadialCrossMass (c : ℝ) (p : Nat.Primes) : ℝ :=
  (p.1 : ℝ) ^ (-(1 - c))

def primeValuationSquaredHellingerFactor (c : ℝ) (p : Nat.Primes) : ℝ :=
  squaredHellingerAffinity
    (primeRadialCriticalMass p)
    (primeRadialTwistedMass c p)
    (primeRadialCrossMass c p)

theorem primeRadialCrossMass_le_half_of_nonpos
    {c : ℝ} (hc : c ≤ 0) (p : Nat.Primes) :
    primeRadialCrossMass c p ≤ 1 / 2 := by
  have hpOne : (1 : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast p.2.one_lt.le
  have hcross :
      primeRadialCrossMass c p ≤ ((p.1 : ℝ))⁻¹ := by
    rw [primeRadialCrossMass, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
  have hpTwo : (2 : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast p.2.two_le
  have hinv : ((p.1 : ℝ))⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpTwo
  exact hcross.trans hinv

theorem primeRadialCrossMass_sq
    (c : ℝ) (p : Nat.Primes) :
    primeRadialCrossMass c p ^ 2 =
      primeRadialCriticalMass p * primeRadialTwistedMass c p := by
  have hp0 : 0 ≤ (p.1 : ℝ) := by exact_mod_cast p.2.pos.le
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  rw [primeRadialCrossMass, primeRadialCriticalMass,
    primeRadialTwistedMass]
  rw [← Real.rpow_mul_natCast hp0 (-(1 - c)) 2]
  rw [← Real.rpow_neg_one]
  rw [← Real.rpow_add hp]
  rw [show -(1 - c) * (2 : ℕ) =
      (-1 : ℝ) + -(1 - 2 * c) by norm_num; ring]

theorem primeRadialCrossMass_mul_rpow
    (c : ℝ) (p : Nat.Primes) :
    primeRadialCrossMass c p * (p.1 : ℝ) ^ c =
      primeRadialTwistedMass c p := by
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  rw [primeRadialCrossMass, primeRadialTwistedMass,
    ← Real.rpow_add hp]
  congr 1
  ring

theorem primeRadialCriticalMass_mul_rpow
    (c : ℝ) (p : Nat.Primes) :
    primeRadialCriticalMass p * (p.1 : ℝ) ^ (2 * c) =
      primeRadialTwistedMass c p := by
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  rw [primeRadialCriticalMass, primeRadialTwistedMass,
    ← Real.rpow_neg_one, ← Real.rpow_add hp]
  congr 1
  ring

theorem primeRadialCrossMass_lt_one
    {c : ℝ} (hc : c < 1) (p : Nat.Primes) :
    primeRadialCrossMass c p < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.2.one_lt) (by simp only [neg_lt_zero]; linarith)

theorem primeRadialTwistedMass_le_one
    {c : ℝ} (hc : c ≤ 1 / 2) (p : Nat.Primes) :
    primeRadialTwistedMass c p ≤ 1 := by
  exact (Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.2.one_lt.le) (by linarith))

theorem primeRadialTwistedMass_le_crossMass_of_nonpos
    {c : ℝ} (hc : c ≤ 0) (p : Nat.Primes) :
    primeRadialTwistedMass c p ≤ primeRadialCrossMass c p := by
  exact (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast p.2.one_lt.le) (by linarith))

theorem one_sub_primeMass_le_squaredHellingerFactor_of_nonpos
    {c : ℝ} (hc : c ≤ 0) (p : Nat.Primes) :
    1 - primeRadialCriticalMass p ≤
      primeValuationSquaredHellingerFactor c p := by
  apply one_sub_q_le_squaredHellingerAffinity
  · apply (inv_le_one₀ (by exact_mod_cast p.2.pos)).2
    exact_mod_cast p.2.one_lt.le
  · exact Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  · exact primeRadialCrossMass_lt_one (by linarith) p
  · exact primeRadialCrossMass_sq c p
  · exact primeRadialTwistedMass_le_crossMass_of_nonpos hc p

theorem primeSquaredHellingerFactor_le_wold_mul_exp_of_nonpos
    {c : ℝ} (hc : c ≤ 0) (p : Nat.Primes) :
    primeValuationSquaredHellingerFactor c p ≤
      (1 - primeRadialCriticalMass p) *
        Real.exp (6 * primeRadialCrossMass c p) := by
  have hq1 : primeRadialCriticalMass p ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast p.2.pos)).2
    exact_mod_cast p.2.one_lt.le
  have hr0 : 0 ≤ primeRadialTwistedMass c p :=
    Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have hr1 : primeRadialTwistedMass c p ≤ 1 :=
    primeRadialTwistedMass_le_one (by linarith) p
  have hu0 : 0 ≤ primeRadialCrossMass c p :=
    Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have huHalf : primeRadialCrossMass c p ≤ 1 / 2 :=
    primeRadialCrossMass_le_half_of_nonpos hc p
  have hu1 : primeRadialCrossMass c p < 1 := by linarith
  have hden : 0 < (1 - primeRadialCrossMass c p) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hu1)
  rw [primeValuationSquaredHellingerFactor,
    squaredHellingerAffinity]
  calc
    (1 - primeRadialCriticalMass p) *
          (1 - primeRadialTwistedMass c p) /
        (1 - primeRadialCrossMass c p) ^ 2 =
        (1 - primeRadialCriticalMass p) *
          ((1 - primeRadialTwistedMass c p) /
            (1 - primeRadialCrossMass c p) ^ 2) := by ring
    _ ≤ (1 - primeRadialCriticalMass p) *
          (1 / (1 - primeRadialCrossMass c p) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
      · exact sub_nonneg.mpr hq1
    _ ≤ (1 - primeRadialCriticalMass p) *
          Real.exp (6 * primeRadialCrossMass c p) := by
      exact mul_le_mul_of_nonneg_left
        (inv_one_sub_sq_le_exp_six_mul hu0 huHalf)
        (sub_nonneg.mpr hq1)

theorem eventually_primeSquaredHellingerFactor_le_woldPower
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (L : ℕ) :
    ∃ P : ℕ, ∀ p : Nat.Primes, P ≤ p.1 →
      primeValuationSquaredHellingerFactor c p ≤
        (1 - primeRadialCriticalMass p) ^ L := by
  have hc2 : 0 < 2 * c := by positivity
  have hpowc :
      Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hpow2c :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * c)) atTop atTop :=
    (tendsto_rpow_atTop hc2).comp tendsto_natCast_atTop_atTop
  have hlargeC :
      ∀ᶠ n : ℕ in atTop, (8 / 3 : ℝ) ≤ (n : ℝ) ^ c :=
    hpowc.eventually (eventually_ge_atTop (8 / 3 : ℝ))
  have hlarge2C :
      ∀ᶠ n : ℕ in atTop, (4 * (L : ℝ)) ≤ (n : ℝ) ^ (2 * c) :=
    hpow2c.eventually (eventually_ge_atTop (4 * (L : ℝ)))
  have hlargeNat : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_ge_atTop 2
  rw [eventually_atTop] at hlargeC hlarge2C hlargeNat
  rcases hlargeC with ⟨P₁, hP₁⟩
  rcases hlarge2C with ⟨P₂, hP₂⟩
  rcases hlargeNat with ⟨P₃, hP₃⟩
  refine ⟨max P₁ (max P₂ P₃), fun p hp => ?_⟩
  have hp1 := hP₁ p.1 (le_trans (le_max_left _ _) hp)
  have hp2 := hP₂ p.1
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp)
  have hp3 := hP₃ p.1
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hp)
  have hq0 : 0 ≤ primeRadialCriticalMass p := by
    exact inv_nonneg.mpr (by exact_mod_cast p.2.pos.le)
  have hq1 : primeRadialCriticalMass p ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast p.2.pos)).2
    exact_mod_cast p.2.one_lt.le
  have hr0 : 0 ≤ primeRadialTwistedMass c p := by
    exact Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have hr1 : primeRadialTwistedMass c p ≤ 1 :=
    primeRadialTwistedMass_le_one hcHalf.le p
  have hu0 : 0 ≤ primeRadialCrossMass c p := by
    exact Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have hu1 : primeRadialCrossMass c p < 1 :=
    primeRadialCrossMass_lt_one (by linarith) p
  have hu :
      8 * primeRadialCrossMass c p ≤
        3 * primeRadialTwistedMass c p := by
    have hcrossPos : 0 ≤ primeRadialCrossMass c p := hu0
    rw [← primeRadialCrossMass_mul_rpow c p]
    nlinarith
  have hqr :
      4 * (L : ℝ) * primeRadialCriticalMass p ≤
        primeRadialTwistedMass c p := by
    rw [← primeRadialCriticalMass_mul_rpow c p]
    simpa [mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hp2 hq0)
  exact squaredHellingerAffinity_le_woldPower L
    hq0 hq1 hr0 hr1 hu0 hu1
    (primeRadialCrossMass_sq c p) hu hqr

def primeValuationSquaredHellingerFactorNat (c : ℝ) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    primeValuationSquaredHellingerFactor c ⟨p, hp⟩
  else 1

def primeValuationSquaredHellingerBelow (c : ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N, primeValuationSquaredHellingerFactorNat c p

theorem primeValuationSquaredHellingerFactorNat_of_prime
    (c : ℝ) {p : ℕ} (hp : p.Prime) :
    primeValuationSquaredHellingerFactorNat c p =
      primeValuationSquaredHellingerFactor c ⟨p, hp⟩ := by
  simp [primeValuationSquaredHellingerFactorNat, hp]

theorem primeValuationSquaredHellingerFactor_zero
    (p : Nat.Primes) :
    primeValuationSquaredHellingerFactor 0 p = 1 := by
  have hq :
      primeRadialCriticalMass p ≠ 1 := by
    exact ne_of_lt
      ((inv_lt_one₀ (by exact_mod_cast p.2.pos)).2
        (by exact_mod_cast p.2.one_lt))
  have hr :
      primeRadialTwistedMass 0 p = primeRadialCriticalMass p := by
    rw [primeRadialTwistedMass, primeRadialCriticalMass]
    norm_num
    exact Real.rpow_neg_one _
  have hu :
      primeRadialCrossMass 0 p = primeRadialCriticalMass p := by
    rw [primeRadialCrossMass, primeRadialCriticalMass]
    norm_num
    exact Real.rpow_neg_one _
  rw [primeValuationSquaredHellingerFactor, hr, hu]
  exact squaredHellingerAffinity_self hq

theorem primeValuationSquaredHellingerBelow_zero
    (N : ℕ) :
    primeValuationSquaredHellingerBelow 0 N = 1 := by
  rw [primeValuationSquaredHellingerBelow]
  apply Finset.prod_eq_one
  intro p hpN
  have hp := Nat.prime_of_mem_primesBelow hpN
  rw [primeValuationSquaredHellingerFactorNat_of_prime 0 hp]
  exact primeValuationSquaredHellingerFactor_zero ⟨p, hp⟩

theorem primeValuationSquaredHellingerBelow_nonneg
    {c : ℝ} (hc : c ≤ 1 / 2) (N : ℕ) :
    0 ≤ primeValuationSquaredHellingerBelow c N := by
  rw [primeValuationSquaredHellingerBelow]
  apply Finset.prod_nonneg
  intro p hpN
  have hp := Nat.prime_of_mem_primesBelow hpN
  rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
  apply squaredHellingerAffinity_nonneg
  · apply (inv_le_one₀ (by exact_mod_cast hp.pos)).2
    exact_mod_cast hp.one_lt.le
  · exact primeRadialTwistedMass_le_one hc ⟨p, hp⟩

/-- Every finite-prime squared Hellinger sector is strictly positive in the open radial strip. -/
theorem primeValuationSquaredHellingerBelow_pos
    {c : ℝ} (hc : c < 1 / 2) (N : ℕ) :
    0 < primeValuationSquaredHellingerBelow c N := by
  rw [primeValuationSquaredHellingerBelow]
  apply Finset.prod_pos
  intro p hpN
  have hp := Nat.prime_of_mem_primesBelow hpN
  rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
  rw [primeValuationSquaredHellingerFactor, squaredHellingerAffinity]
  apply div_pos
  · apply mul_pos
    · exact sub_pos.mpr
        ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2
          (by exact_mod_cast hp.one_lt))
    · exact sub_pos.mpr
        (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast hp.one_lt) (by linarith))
  · exact sq_pos_of_pos
      (sub_pos.mpr (primeRadialCrossMass_lt_one (by linarith) ⟨p, hp⟩))

theorem primeValuationSquaredHellingerBelow_le_one
    {c : ℝ} (hc : c < 1 / 2) (N : ℕ) :
    primeValuationSquaredHellingerBelow c N ≤ 1 := by
  rw [primeValuationSquaredHellingerBelow]
  calc
    (∏ p ∈ Nat.primesBelow N,
      primeValuationSquaredHellingerFactorNat c p) ≤
        ∏ _p ∈ Nat.primesBelow N, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro p hpN
            have hp := Nat.prime_of_mem_primesBelow hpN
            rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
            apply squaredHellingerAffinity_nonneg
            · apply (inv_le_one₀ (by exact_mod_cast hp.pos)).2
              exact_mod_cast hp.one_lt.le
            · exact primeRadialTwistedMass_le_one hc.le ⟨p, hp⟩
          · intro p hpN
            have hp := Nat.prime_of_mem_primesBelow hpN
            rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
            apply squaredHellingerAffinity_le_one
            · exact inv_nonneg.mpr (by exact_mod_cast hp.pos.le)
            · exact Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _
            · exact primeRadialCrossMass_lt_one (by linarith) ⟨p, hp⟩
            · exact primeRadialCrossMass_sq c ⟨p, hp⟩
    _ = 1 := by simp

def primeValuationNegativeFaceCorrectionBound (c : ℝ) : ℝ :=
  Real.exp
    (6 * ∑' n : ℕ, (n : ℝ) ^ (-(1 - c)))

theorem primeValuationNegativeFaceCorrectionBound_pos (c : ℝ) :
    0 < primeValuationNegativeFaceCorrectionBound c :=
  Real.exp_pos _

theorem primeValuationSquaredHellingerBelow_le_wold_mul_correction_of_neg
    {c : ℝ} (hc : c < 0) (N : ℕ) :
    primeValuationSquaredHellingerBelow c N ≤
      primeWoldBoundaryVolumeBelow N *
        primeValuationNegativeFaceCorrectionBound c := by
  have hsummable :
      Summable (fun n : ℕ => (n : ℝ) ^ (-(1 - c))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsum :
      (∑ p ∈ Nat.primesBelow N,
          (p : ℝ) ^ (-(1 - c))) ≤
        ∑' n : ℕ, (n : ℝ) ^ (-(1 - c)) :=
    hsummable.sum_le_tsum (Nat.primesBelow N)
      (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hexp :
      (∏ p ∈ Nat.primesBelow N,
          Real.exp (6 * (p : ℝ) ^ (-(1 - c)))) ≤
        primeValuationNegativeFaceCorrectionBound c := by
    rw [← Real.exp_sum]
    rw [primeValuationNegativeFaceCorrectionBound]
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [primeValuationSquaredHellingerBelow,
    primeWoldBoundaryVolumeBelow_eq]
  calc
    (∏ p ∈ Nat.primesBelow N,
        primeValuationSquaredHellingerFactorNat c p) ≤
      ∏ p ∈ Nat.primesBelow N,
        ((1 - (p : ℝ)⁻¹) *
          Real.exp (6 * (p : ℝ) ^ (-(1 - c)))) := by
      apply Finset.prod_le_prod
      · intro p hpN
        have hp := Nat.prime_of_mem_primesBelow hpN
        rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
        apply squaredHellingerAffinity_nonneg
        · apply (inv_le_one₀ (by exact_mod_cast hp.pos)).2
          exact_mod_cast hp.one_lt.le
        · exact primeRadialTwistedMass_le_one (by linarith) ⟨p, hp⟩
      · intro p hpN
        have hp := Nat.prime_of_mem_primesBelow hpN
        rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
        simpa [primeRadialCriticalMass, primeRadialCrossMass] using
          primeSquaredHellingerFactor_le_wold_mul_exp_of_nonpos
            (c := c) hc.le ⟨p, hp⟩
    _ = (∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ)⁻¹)) *
          (∏ p ∈ Nat.primesBelow N,
            Real.exp (6 * (p : ℝ) ^ (-(1 - c)))) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ (∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ)⁻¹)) *
          primeValuationNegativeFaceCorrectionBound c := by
      apply mul_le_mul_of_nonneg_left hexp
      apply Finset.prod_nonneg
      intro p hpN
      have hp := Nat.prime_of_mem_primesBelow hpN
      exact sub_nonneg.mpr ((inv_le_one₀ (by exact_mod_cast hp.pos)).2
        (by exact_mod_cast hp.one_lt.le))

theorem primeWoldBoundaryVolumeBelow_le_squaredHellinger_of_nonpos
    {c : ℝ} (hc : c ≤ 0) (N : ℕ) :
    primeWoldBoundaryVolumeBelow N ≤
      primeValuationSquaredHellingerBelow c N := by
  rw [primeWoldBoundaryVolumeBelow_eq,
    primeValuationSquaredHellingerBelow]
  apply Finset.prod_le_prod
  · intro p hpN
    have hp := Nat.prime_of_mem_primesBelow hpN
    exact sub_nonneg.mpr ((inv_le_one₀ (by exact_mod_cast hp.pos)).2
      (by exact_mod_cast hp.one_lt.le))
  · intro p hpN
    have hp := Nat.prime_of_mem_primesBelow hpN
    rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
    exact one_sub_primeMass_le_squaredHellingerFactor_of_nonpos hc ⟨p, hp⟩

theorem primeValuationSquaredHellingerBelow_isTheta_wold_of_neg
    {c : ℝ} (hc : c < 0) :
    (primeValuationSquaredHellingerBelow c) =Θ[atTop]
      primeWoldBoundaryVolumeBelow := by
  apply IsBigO.antisymm
  · apply IsBigO.of_bound
      (primeValuationNegativeFaceCorrectionBound c)
    filter_upwards [] with N
    have hHnonneg :
        0 ≤ primeValuationSquaredHellingerBelow c N :=
      primeValuationSquaredHellingerBelow_nonneg (by linarith) N
    have hvolnonneg : 0 ≤ primeWoldBoundaryVolumeBelow N :=
      primeWoldBoundaryVolumeBelow_nonneg N
    have hCnonneg :
        0 ≤ primeValuationNegativeFaceCorrectionBound c :=
      (primeValuationNegativeFaceCorrectionBound_pos c).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hHnonneg,
      abs_of_nonneg hvolnonneg, mul_comm] using
      primeValuationSquaredHellingerBelow_le_wold_mul_correction_of_neg
        hc N
  · apply IsBigO.of_bound 1
    filter_upwards [] with N
    have hHnonneg :
        0 ≤ primeValuationSquaredHellingerBelow c N :=
      primeValuationSquaredHellingerBelow_nonneg (by linarith) N
    have hvolnonneg : 0 ≤ primeWoldBoundaryVolumeBelow N :=
      primeWoldBoundaryVolumeBelow_nonneg N
    simpa only [Real.norm_eq_abs, abs_of_nonneg hHnonneg,
      abs_of_nonneg hvolnonneg, one_mul] using
      primeWoldBoundaryVolumeBelow_le_squaredHellinger_of_nonpos
        hc.le N

/-! ## Exact Euler--Hellinger curvature on the convergent face -/

/-- Finite ordinary-prime partition function at inverse temperature `sigma`. -/
def realPrimeEulerPartitionBelow (sigma : ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ) ^ (-sigma))⁻¹

/-- On the convergent side of the Euler wall, the real prime partition tends to zeta. -/
theorem realPrimeEulerPartitionBelow_tendsto
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto (realPrimeEulerPartitionBelow sigma) atTop
      (nhds (riemannZeta (sigma : ℂ)).re) := by
  have hcomplex :=
    riemannZeta_eulerProduct (s := (sigma : ℂ)) (by
      simpa using hsigma)
  have hre :=
    (Complex.continuous_re.tendsto (riemannZeta (sigma : ℂ))).comp
      hcomplex
  have hsource :
      (fun N : ℕ =>
        (∏ p ∈ Nat.primesBelow N,
          (1 - (p : ℂ) ^ (-(sigma : ℂ)))⁻¹).re) =
        realPrimeEulerPartitionBelow sigma := by
    funext N
    rw [realPrimeEulerPartitionBelow]
    have heq :
        (∏ p ∈ Nat.primesBelow N,
          (1 - (p : ℂ) ^ (-(sigma : ℂ)))⁻¹) =
        ((∏ p ∈ Nat.primesBelow N,
          (1 - (p : ℝ) ^ (-sigma))⁻¹ : ℝ) : ℂ) := by
      calc
        (∏ p ∈ Nat.primesBelow N,
            (1 - (p : ℂ) ^ (-(sigma : ℂ)))⁻¹) =
            ∏ p ∈ Nat.primesBelow N,
              (((1 - (p : ℝ) ^ (-sigma))⁻¹ : ℝ) : ℂ) := by
                apply Finset.prod_congr rfl
                intro p hp
                have hpow :
                    (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) =
                      (p : ℂ) ^ (-(sigma : ℂ)) := by
                  simpa using
                    (Complex.ofReal_cpow
                      (show (0 : ℝ) ≤ p by positivity) (-sigma))
                rw [← hpow]
                norm_cast
        _ = ((∏ p ∈ Nat.primesBelow N,
            (1 - (p : ℝ) ^ (-sigma))⁻¹ : ℝ) : ℂ) := by
              push_cast
              rfl
    rw [heq, Complex.ofReal_re]
  change Tendsto
    (fun N : ℕ =>
      (∏ p ∈ Nat.primesBelow N,
        (1 - (p : ℂ) ^ (-(sigma : ℂ)))⁻¹).re)
      atTop (nhds (riemannZeta (sigma : ℂ)).re) at hre
  rw [hsource] at hre
  exact hre

/-- Finite Euler correction to the critical Wold boundary volume. -/
def primeValuationHellingerEulerCorrectionBelow
    (c : ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N,
    (1 - (p : ℝ) ^ (-(1 - 2 * c))) /
      (1 - (p : ℝ) ^ (-(1 - c))) ^ 2

/-- Exact finite Euler factorization of squared Hellinger affinity into the critical Wold
volume and a midpoint-curvature correction. -/
theorem primeValuationSquaredHellingerBelow_eq_wold_mul_eulerCorrection
    (c : ℝ) (N : ℕ) :
    primeValuationSquaredHellingerBelow c N =
      primeWoldBoundaryVolumeBelow N *
        primeValuationHellingerEulerCorrectionBelow c N := by
  rw [primeValuationSquaredHellingerBelow,
    primeWoldBoundaryVolumeBelow_eq,
    primeValuationHellingerEulerCorrectionBelow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpN
  have hp := Nat.prime_of_mem_primesBelow hpN
  rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
  simp only [primeValuationSquaredHellingerFactor,
    squaredHellingerAffinity, primeRadialCriticalMass,
    primeRadialTwistedMass, primeRadialCrossMass]
  ring

/-- The Euler correction is exactly the midpoint Jensen ratio of finite prime partition
functions. -/
theorem primeValuationHellingerEulerCorrectionBelow_eq_partitionRatio
    {c : ℝ} (hc : c < 0) (N : ℕ) :
    primeValuationHellingerEulerCorrectionBelow c N =
      realPrimeEulerPartitionBelow (1 - c) N ^ 2 /
        realPrimeEulerPartitionBelow (1 - 2 * c) N := by
  rw [primeValuationHellingerEulerCorrectionBelow,
    realPrimeEulerPartitionBelow, realPrimeEulerPartitionBelow]
  have hmid :
      ∀ p ∈ Nat.primesBelow N,
        1 - (p : ℝ) ^ (-(1 - c)) ≠ 0 := by
    intro p hpN
    have hp := Nat.prime_of_mem_primesBelow hpN
    have hbase : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hexp : -(1 - c) < 0 := by linarith
    exact sub_ne_zero.mpr
      (ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hbase hexp)).symm
  have hden :
      ∀ p ∈ Nat.primesBelow N,
        1 - (p : ℝ) ^ (-(1 - 2 * c)) ≠ 0 := by
    intro p hpN
    have hp := Nat.prime_of_mem_primesBelow hpN
    have hbase : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hexp : -(1 - 2 * c) < 0 := by linarith
    exact sub_ne_zero.mpr
      (ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hbase hexp)).symm
  rw [Finset.prod_div_distrib, Finset.prod_pow]
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  field_simp [Finset.prod_ne_zero_iff.mpr hmid,
    Finset.prod_ne_zero_iff.mpr hden]

/-- Exact negative-face normalization: the squared affinity divided by Wold volume converges
to the zeta midpoint-curvature constant. -/
theorem tendsto_primeValuationSquaredHellinger_div_wold_of_neg
    {c : ℝ} (hc : c < 0) :
    Tendsto
      (fun N =>
        primeValuationSquaredHellingerBelow c N /
          primeWoldBoundaryVolumeBelow N)
      atTop
      (nhds
        ((riemannZeta ((1 - c : ℝ) : ℂ)).re ^ 2 /
          (riemannZeta ((1 - 2 * c : ℝ) : ℂ)).re)) := by
  have hmid :=
    realPrimeEulerPartitionBelow_tendsto (sigma := 1 - c) (by linarith)
  have hden :=
    realPrimeEulerPartitionBelow_tendsto (sigma := 1 - 2 * c) (by linarith)
  have hzetaDen :
      (riemannZeta ((1 - 2 * c : ℝ) : ℂ)).re ≠ 0 := by
    have hpos :
        ∀ N, 1 ≤ realPrimeEulerPartitionBelow (1 - 2 * c) N := by
      intro N
      rw [realPrimeEulerPartitionBelow]
      apply Finset.one_le_prod
      intro p hpN
      have hp := Nat.prime_of_mem_primesBelow hpN
      have hbase : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hexp : -(1 - 2 * c) < 0 := by linarith
      have hpow := Real.rpow_lt_one_of_one_lt_of_neg hbase hexp
      have hposDen : 0 < 1 - (p : ℝ) ^ (-(1 - 2 * c)) := sub_pos.mpr hpow
      exact (one_le_inv₀ hposDen).2
        (by
          have hrpowPos :
              0 < (p : ℝ) ^ (-(1 - 2 * c)) :=
            Real.rpow_pos_of_pos (by linarith) _
          linarith)
    have hlim :
        1 ≤ (riemannZeta ((1 - 2 * c : ℝ) : ℂ)).re :=
      ge_of_tendsto' hden hpos
    linarith
  have hratio := (hmid.pow 2).div hden hzetaDen
  apply hratio.congr'
  filter_upwards [] with N
  rw [primeValuationSquaredHellingerBelow_eq_wold_mul_eulerCorrection,
    mul_div_cancel_left₀ _
      (primeWoldBoundaryVolumeBelow_pos N).ne',
    primeValuationHellingerEulerCorrectionBelow_eq_partitionRatio hc N]
  rfl

/-- Unsquared finite-prime Hellinger affinity. -/
def primeValuationHellingerBelow (c : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (primeValuationSquaredHellingerBelow c N)

theorem primeValuationHellingerBelow_sq
    {c : ℝ} (hc : c ≤ 1 / 2) (N : ℕ) :
    primeValuationHellingerBelow c N ^ 2 =
      primeValuationSquaredHellingerBelow c N := by
  rw [primeValuationHellingerBelow,
    Real.sq_sqrt (primeValuationSquaredHellingerBelow_nonneg hc N)]

theorem primeValuationHellingerBelow_zero
    (N : ℕ) :
    primeValuationHellingerBelow 0 N = 1 := by
  rw [primeValuationHellingerBelow,
    primeValuationSquaredHellingerBelow_zero, Real.sqrt_one]

/-- On the nonpositive reflected face, the Hellinger affinity reaches at least the canonical
half-normal Wold scale. -/
theorem primeWoldHalfNormal_le_Hellinger_of_nonpos
    {c : ℝ} (hc : c ≤ 0) (N : ℕ) :
    Real.sqrt (primeWoldBoundaryVolumeBelow N) ≤
      primeValuationHellingerBelow c N := by
  rw [primeValuationHellingerBelow]
  exact Real.sqrt_le_sqrt
    (primeWoldBoundaryVolumeBelow_le_squaredHellinger_of_nonpos hc N)

/-- On the negative reflected face, the Hellinger amplitude has exactly the half-normal Wold
grade.  Its square is comparable to the Wold boundary volume, while the amplitude itself is
comparable to the square root of that volume. -/
theorem primeValuationHellingerBelow_isTheta_halfNormal_of_neg
    {c : ℝ} (hc : c < 0) :
    (primeValuationHellingerBelow c) =Θ[atTop]
      (fun N => Real.sqrt (primeWoldBoundaryVolumeBelow N)) := by
  have htheta :=
    (primeValuationSquaredHellingerBelow_isTheta_wold_of_neg hc).sqrt
      (Filter.Eventually.of_forall fun N =>
        primeValuationSquaredHellingerBelow_nonneg (by linarith) N)
      (Filter.Eventually.of_forall
        primeWoldBoundaryVolumeBelow_nonneg)
  change
    (fun N => Real.sqrt (primeValuationSquaredHellingerBelow c N)) =Θ[atTop]
      (fun N => Real.sqrt (primeWoldBoundaryVolumeBelow N))
  exact htheta

theorem primeValuationSquaredHellingerBelow_not_reesAllOrdersFlat_of_nonpos
    {c : ℝ} (hc : c ≤ 0) :
    ¬ ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
      (primeValuationSquaredHellingerBelow c) := by
  intro hflat
  have hbound := (hflat 2).bound one_pos
  have hsmall :
      ∀ᶠ N : ℕ in atTop, primeWoldBoundaryVolumeBelow N < 1 :=
    tendsto_primeWoldBoundaryVolumeBelow_zero.eventually
      (eventually_lt_nhds zero_lt_one)
  obtain ⟨N, hNbound, hNsmall⟩ := (hbound.and hsmall).exists
  have hvolPos := primeWoldBoundaryVolumeBelow_pos N
  have hHnonneg : 0 ≤ primeValuationSquaredHellingerBelow c N :=
    primeValuationSquaredHellingerBelow_nonneg (by linarith) N
  have hlower :=
    primeWoldBoundaryVolumeBelow_le_squaredHellinger_of_nonpos hc N
  have hpowlt :
      primeWoldBoundaryVolumeBelow N ^ 2 <
        primeWoldBoundaryVolumeBelow N := by
    nlinarith
  simp only [Real.norm_eq_abs, one_mul, abs_of_nonneg hHnonneg,
    abs_of_pos (pow_pos hvolPos 2)] at hNbound
  linarith

def primeWoldLocalMassNat (p : ℕ) : ℝ :=
  1 - (p : ℝ)⁻¹

def primeHellingerFinitePrefixCorrection
    (L P p : ℕ) : ℝ :=
  if p < P then (primeWoldLocalMassNat p ^ L)⁻¹ else 1

theorem primeHellingerFactor_le_correction_mul_woldPower
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (L P : ℕ)
    (hP : ∀ p : Nat.Primes, P ≤ p.1 →
      primeValuationSquaredHellingerFactor c p ≤
        (1 - primeRadialCriticalMass p) ^ L)
    {p : ℕ} (hp : p.Prime) :
    primeValuationSquaredHellingerFactorNat c p ≤
      primeHellingerFinitePrefixCorrection L P p *
        primeWoldLocalMassNat p ^ L := by
  rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
  by_cases hpP : p < P
  · rw [primeHellingerFinitePrefixCorrection, if_pos hpP]
    have hlocalPos : 0 < primeWoldLocalMassNat p := by
      rw [primeWoldLocalMassNat]
      exact sub_pos.mpr ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2
        (by exact_mod_cast hp.one_lt))
    have hpowNe : primeWoldLocalMassNat p ^ L ≠ 0 :=
      (pow_pos hlocalPos L).ne'
    rw [inv_mul_cancel₀ hpowNe]
    apply squaredHellingerAffinity_le_one
    · exact inv_nonneg.mpr (by exact_mod_cast hp.pos.le)
    · exact Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _
    · exact primeRadialCrossMass_lt_one (by linarith) ⟨p, hp⟩
    · exact primeRadialCrossMass_sq c ⟨p, hp⟩
  · rw [primeHellingerFinitePrefixCorrection, if_neg hpP, one_mul]
    simpa [primeWoldLocalMassNat, primeRadialCriticalMass] using
      hP ⟨p, hp⟩ (Nat.le_of_not_gt hpP)

theorem primeHellingerFinitePrefixCorrection_prod_stable
    (L P N : ℕ) (hPN : P ≤ N) :
    (∏ p ∈ Nat.primesBelow N,
        primeHellingerFinitePrefixCorrection L P p) =
      ∏ p ∈ Nat.primesBelow P,
        primeHellingerFinitePrefixCorrection L P p := by
  symm
  apply Finset.prod_subset (Nat.primesBelow_mono hPN)
  intro p hpN hpP
  rw [primeHellingerFinitePrefixCorrection, if_neg]
  intro hlt
  exact hpP (Nat.mem_primesBelow.mpr
    ⟨hlt, Nat.prime_of_mem_primesBelow hpN⟩)

theorem primeValuationSquaredHellingerBelow_isBigO_woldPower
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (L : ℕ) :
    (primeValuationSquaredHellingerBelow c) =O[atTop]
      (fun N => primeWoldBoundaryVolumeBelow N ^ L) := by
  obtain ⟨P, hP⟩ :=
    eventually_primeSquaredHellingerFactor_le_woldPower hc hcHalf L
  let C : ℝ :=
    ∏ p ∈ Nat.primesBelow P,
      primeHellingerFinitePrefixCorrection L P p
  apply IsBigO.of_bound ‖C‖
  filter_upwards [eventually_ge_atTop P] with N hPN
  have hprod :
      primeValuationSquaredHellingerBelow c N ≤
        C * primeWoldBoundaryVolumeBelow N ^ L := by
    dsimp only [C]
    rw [primeValuationSquaredHellingerBelow,
      primeWoldBoundaryVolumeBelow_eq]
    calc
      (∏ p ∈ Nat.primesBelow N,
          primeValuationSquaredHellingerFactorNat c p) ≤
          ∏ p ∈ Nat.primesBelow N,
            (primeHellingerFinitePrefixCorrection L P p *
              primeWoldLocalMassNat p ^ L) := by
        apply Finset.prod_le_prod
        · intro p hpN
          have hp := Nat.prime_of_mem_primesBelow hpN
          rw [primeValuationSquaredHellingerFactorNat_of_prime c hp]
          apply squaredHellingerAffinity_nonneg
          · apply (inv_le_one₀ (by exact_mod_cast hp.pos)).2
            exact_mod_cast hp.one_lt.le
          · exact primeRadialTwistedMass_le_one hcHalf.le ⟨p, hp⟩
        · intro p hpN
          exact primeHellingerFactor_le_correction_mul_woldPower
            hc hcHalf L P hP (Nat.prime_of_mem_primesBelow hpN)
      _ = (∏ p ∈ Nat.primesBelow N,
              primeHellingerFinitePrefixCorrection L P p) *
            (∏ p ∈ Nat.primesBelow N,
              primeWoldLocalMassNat p) ^ L := by
        rw [Finset.prod_mul_distrib, ← Finset.prod_pow]
      _ = (∏ p ∈ Nat.primesBelow P,
              primeHellingerFinitePrefixCorrection L P p) *
            (∏ p ∈ Nat.primesBelow N,
              (1 - (p : ℝ)⁻¹)) ^ L := by
        rw [primeHellingerFinitePrefixCorrection_prod_stable L P N hPN]
        rfl
  have hHnonneg : 0 ≤ primeValuationSquaredHellingerBelow c N :=
    primeValuationSquaredHellingerBelow_nonneg hcHalf.le N
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    apply Finset.prod_nonneg
    intro p hpP
    have hp := Nat.prime_of_mem_primesBelow hpP
    have hlocal : 0 ≤ primeWoldLocalMassNat p := by
      rw [primeWoldLocalMassNat]
      exact sub_nonneg.mpr ((inv_le_one₀ (by exact_mod_cast hp.pos)).2
        (by exact_mod_cast hp.one_lt.le))
    rw [primeHellingerFinitePrefixCorrection]
    split_ifs
    · exact inv_nonneg.mpr (pow_nonneg hlocal L)
    · norm_num
  have hvolnonneg : 0 ≤ primeWoldBoundaryVolumeBelow N ^ L :=
    pow_nonneg (primeWoldBoundaryVolumeBelow_nonneg N) L
  simpa only [Real.norm_eq_abs, abs_of_nonneg hHnonneg,
    abs_of_nonneg hCnonneg, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg (primeWoldBoundaryVolumeBelow_nonneg N)] using hprod

theorem primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
      (primeValuationSquaredHellingerBelow c) := by
  intro K
  have hbig :=
    primeValuationSquaredHellingerBelow_isBigO_woldPower
      hc hcHalf (K + 1)
  have hpow :
      (fun N => primeWoldBoundaryVolumeBelow N ^ (K + 1)) =o[atTop]
        (fun N => primeWoldBoundaryVolumeBelow N ^ K) :=
    (isLittleO_pow_pow (Nat.lt_succ_self K)).comp_tendsto
      tendsto_primeWoldBoundaryVolumeBelow_zero
  exact hbig.trans_isLittleO hpow

/-- The unsquared Hellinger affinity is also flat beyond every Wold Rees order on the positive
radial face. -/
theorem primeValuationHellingerBelow_reesAllOrdersFlat_of_pos
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) :
    ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
      (primeValuationHellingerBelow c) := by
  intro K
  have hsq :=
    (primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos
      hc hcHalf) (2 * K)
  have hpow :
      (fun N => primeValuationHellingerBelow c N ^ 2) =o[atTop]
        (fun N => (primeWoldBoundaryVolumeBelow N ^ K) ^ 2) := by
    apply hsq.congr'
    · filter_upwards [] with N
      exact (primeValuationHellingerBelow_sq hcHalf.le N).symm
    · filter_upwards [] with N
      rw [← pow_mul]
      rw [Nat.mul_comm K 2]
  exact hpow.of_pow (by norm_num)

/-- Exact three-phase law for the unsquared affinity: negative twists have half-normal Wold
grade, the critical law has unit affinity, and positive twists are flat beyond every Wold Rees
order. -/
theorem primeValuationHellinger_reesType_trichotomy
    {c : ℝ} (hcHalf : c < 1 / 2) :
    (c < 0 ∧
        (primeValuationHellingerBelow c) =Θ[atTop]
          (fun N => Real.sqrt (primeWoldBoundaryVolumeBelow N))) ∨
      (c = 0 ∧ ∀ N, primeValuationHellingerBelow c N = 1) ∨
      (0 < c ∧
        ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
          (primeValuationHellingerBelow c)) := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · exact Or.inl
      ⟨hc, primeValuationHellingerBelow_isTheta_halfNormal_of_neg hc⟩
  · exact Or.inr (Or.inl
      ⟨hc, fun N => by simpa only [hc] using
        primeValuationHellingerBelow_zero N⟩)
  · exact Or.inr (Or.inr
      ⟨hc, primeValuationHellingerBelow_reesAllOrdersFlat_of_pos
        hc hcHalf⟩)

/-- On the nonpositive face, the half-normal lower bound prevents all-orders flatness. -/
theorem primeValuationHellingerBelow_not_reesAllOrdersFlat_of_nonpos
    {c : ℝ} (hc : c ≤ 0) :
    ¬ ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
      (primeValuationHellingerBelow c) := by
  intro hflat
  have hbound := (hflat 1).bound one_pos
  have hsmall :
      ∀ᶠ N : ℕ in atTop, primeWoldBoundaryVolumeBelow N < 1 :=
    tendsto_primeWoldBoundaryVolumeBelow_zero.eventually
      (eventually_lt_nhds zero_lt_one)
  obtain ⟨N, hNbound, hNsmall⟩ := (hbound.and hsmall).exists
  have hvolPos := primeWoldBoundaryVolumeBelow_pos N
  have hHnonneg : 0 ≤ primeValuationHellingerBelow c N := by
    exact Real.sqrt_nonneg _
  have hlower := primeWoldHalfNormal_le_Hellinger_of_nonpos hc N
  have hvolLtSqrt :
      primeWoldBoundaryVolumeBelow N <
        Real.sqrt (primeWoldBoundaryVolumeBelow N) := by
    rw [Real.lt_sqrt hvolPos.le]
    nlinarith
  simp only [Real.norm_eq_abs, one_mul, pow_one,
    abs_of_nonneg hHnonneg, abs_of_pos hvolPos] at hNbound
  linarith

theorem primeValuationSquaredHellingerBelow_reesAllOrdersFlat_iff
    {c : ℝ} (hcAbs : |c| < 1 / 2) :
    ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (primeValuationSquaredHellingerBelow c) ↔
      0 < c := by
  constructor
  · intro hflat
    by_contra hc
    exact primeValuationSquaredHellingerBelow_not_reesAllOrdersFlat_of_nonpos
      (le_of_not_gt hc) hflat
  · intro hc
    exact primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos
      hc (lt_of_le_of_lt (le_abs_self c) hcAbs)

theorem reflected_primeValuationSquaredHellinger_type_fracture
    {c : ℝ} (hcAbs : |c| < 1 / 2) (hc0 : c ≠ 0) :
    ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (primeValuationSquaredHellingerBelow c) ↔
      ¬ ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (primeValuationSquaredHellingerBelow (-c)) := by
  rw [primeValuationSquaredHellingerBelow_reesAllOrdersFlat_iff hcAbs]
  have hnegAbs : |-c| < 1 / 2 := by simpa only [abs_neg] using hcAbs
  rw [primeValuationSquaredHellingerBelow_reesAllOrdersFlat_iff hnegAbs]
  constructor <;> intro h
  · linarith
  · have hcNonneg : 0 ≤ c := by linarith
    exact lt_of_le_of_ne hcNonneg (Ne.symm hc0)

theorem no_finiteReesOperator_sews_reflected_Hellinger_sectors
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hR : ReesOperatorGradeAtMost atTop
      primeWoldBoundaryVolumeBelow K R) :
    (fun N => R N (primeValuationSquaredHellingerBelow c N)) ≠
      primeValuationSquaredHellingerBelow (-c) := by
  intro hsew
  have hscale :
      ∀ᶠ N : ℕ in atTop, primeWoldBoundaryVolumeBelow N ≠ 0 :=
    Filter.Eventually.of_forall fun N =>
      (primeWoldBoundaryVolumeBelow_pos N).ne'
  have hflat :
      ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (fun N => R N (primeValuationSquaredHellingerBelow c N)) :=
    reesAllOrdersFlat_apply_reesOperatorGradeAtMost
      atTop primeWoldBoundaryVolumeBelow K R
      (primeValuationSquaredHellingerBelow c)
      hscale hR
      (primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos
        hc hcHalf)
  have hreflectedNonflat :
      ¬ ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (primeValuationSquaredHellingerBelow (-c)) :=
    primeValuationSquaredHellingerBelow_not_reesAllOrdersFlat_of_nonpos
      (by linarith)
  apply hreflectedNonflat
  simpa only [hsew] using hflat

/-- Quantitative sewing cost: the unique scalar multiplier from the flat positive sector to the
half-normal reflected sector dominates every inverse Wold Rees power. -/
theorem reflectedHellingerSewingCost_beyondEveryReesOrder
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
      (fun N =>
        primeValuationSquaredHellingerBelow (-c) N /
          primeValuationSquaredHellingerBelow c N) := by
  let a := primeWoldBoundaryVolumeBelow
  let f := primeValuationSquaredHellingerBelow c
  let g := primeValuationSquaredHellingerBelow (-c)
  have ha : ∀ᶠ N : ℕ in atTop, a N ≠ 0 :=
    Filter.Eventually.of_forall fun N =>
      (primeWoldBoundaryVolumeBelow_pos N).ne'
  have hf : ∀ᶠ N : ℕ in atTop, f N ≠ 0 :=
    Filter.Eventually.of_forall fun N =>
      (primeValuationSquaredHellingerBelow_pos hcHalf N).ne'
  have hflat :
      f =o[atTop] (fun N => a N ^ (K + 1)) :=
    (primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos
      hc hcHalf) (K + 1)
  have hinv :
      (fun N => (a N ^ (K + 1))⁻¹) =o[atTop]
        (fun N => (f N)⁻¹) :=
    hflat.inv_rev (hf.mono fun N hfn hfzero => (hfn hfzero).elim)
  have hmul :
      (fun N => g N * (a N ^ (K + 1))⁻¹) =o[atTop]
        (fun N => g N * (f N)⁻¹) :=
    (isBigO_refl g atTop).mul_isLittleO hinv
  have htheta :
      (fun N => g N * (a N ^ (K + 1))⁻¹) =Θ[atTop]
        (fun N => (a N)⁻¹ ^ K) := by
    apply (primeValuationSquaredHellingerBelow_isTheta_wold_of_neg
      (by linarith : -c < 0)).mul (isTheta_refl _ atTop) |>.trans_eventuallyEq
    filter_upwards [ha] with N hN
    dsimp only [a, g]
    rw [pow_succ, mul_inv, ← inv_pow]
    calc
      primeWoldBoundaryVolumeBelow N *
          ((primeWoldBoundaryVolumeBelow N)⁻¹ ^ K *
            (primeWoldBoundaryVolumeBelow N)⁻¹) =
        (primeWoldBoundaryVolumeBelow N *
          (primeWoldBoundaryVolumeBelow N)⁻¹) *
          (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K := by ring
      _ = (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K := by
        rw [mul_inv_cancel₀ hN, one_mul]
  simpa only [a, f, g, div_eq_mul_inv] using
    htheta.symm.trans_isLittleO hmul

/-- Any exact bounded linear sewing of the actual reflected scalar sectors has operator norm
beyond every finite Wold Rees order.  Boundedness at each cutoff does not regularize the
thermodynamic family. -/
theorem reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N => R N (primeValuationSquaredHellingerBelow c N)) =
        primeValuationSquaredHellingerBelow (-c))
    (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
      (fun N => ‖R N‖) := by
  have hcost :=
    reflectedHellingerSewingCost_beyondEveryReesOrder hc hcHalf K
  have hratio :
      (fun N =>
        primeValuationSquaredHellingerBelow (-c) N /
          primeValuationSquaredHellingerBelow c N) =O[atTop]
        (fun N => ‖R N‖) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with N
    have hfpos :=
      primeValuationSquaredHellingerBelow_pos hcHalf N
    have hgnonneg :
        0 ≤ primeValuationSquaredHellingerBelow (-c) N :=
      primeValuationSquaredHellingerBelow_nonneg (by linarith) N
    have hop := (R N).le_opNorm
      (primeValuationSquaredHellingerBelow c N)
    rw [congrFun hsew N] at hop
    have hdiv :
        primeValuationSquaredHellingerBelow (-c) N /
            primeValuationSquaredHellingerBelow c N ≤ ‖R N‖ :=
      (div_le_iff₀ hfpos).2 (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hgnonneg,
          abs_of_pos hfpos] using hop)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hgnonneg hfpos.le),
      abs_norm, one_mul] using hdiv
  exact hcost.trans_isBigO hratio

/-! ## Positive escape: modular retuning in a rank-one Weyl block -/

/-- Complementary eigenvalue of the normalized rank-one rational Weyl block. -/
def normalizedRankOneWeylComplementaryEigenvalue
    (p : ℝ) (z : ℂ) : ℂ :=
  ((p : ℂ) * z ^ 2 - 1) / ((p : ℂ) - z ^ 2)

/-- Exact numerator--denominator modulus defect of the Weyl complementary channel. -/
theorem normalizedRankOneWeyl_normSq_numerator_sub_denominator
    (p : ℝ) (z : ℂ) :
    Complex.normSq ((p : ℂ) * z ^ 2 - 1) -
        Complex.normSq ((p : ℂ) - z ^ 2) =
      (p ^ 2 - 1) * (‖z‖ ^ 4 - 1) := by
  have hz4 : ‖z‖ ^ 4 = Complex.normSq z ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = Complex.normSq z ^ 2 := by rw [Complex.sq_norm]
  rw [hz4]
  simp only [pow_two, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, zero_mul, sub_zero, zero_sub]
  ring

/-- The normalized Weyl block is locally unitary exactly on the unitary parameter circle. -/
theorem norm_normalizedRankOneWeylComplementaryEigenvalue_eq_one_iff
    {p : ℝ} (hp : 1 < p) {z : ℂ}
    (hden : (p : ℂ) - z ^ 2 ≠ 0) :
    ‖normalizedRankOneWeylComplementaryEigenvalue p z‖ = 1 ↔
      ‖z‖ = 1 := by
  rw [normalizedRankOneWeylComplementaryEigenvalue, norm_div]
  constructor
  · intro hnorm
    have hnormeq :
        ‖(p : ℂ) * z ^ 2 - 1‖ =
          ‖(p : ℂ) - z ^ 2‖ := by
      have hdenpos := norm_pos_iff.mpr hden
      apply (div_eq_one_iff_eq (ne_of_gt hdenpos)).mp hnorm
    have hsquares := congrArg (fun x : ℝ => x ^ 2) hnormeq
    rw [Complex.sq_norm, Complex.sq_norm] at hsquares
    have hidentity :=
      normalizedRankOneWeyl_normSq_numerator_sub_denominator p z
    have hpFactor : 0 < p ^ 2 - 1 := by nlinarith
    have hz4 : ‖z‖ ^ 4 = 1 := by nlinarith
    have hz2 : ‖z‖ ^ 2 = 1 := by
      have hz4' : (‖z‖ ^ 2) ^ 2 = 1 := by nlinarith
      nlinarith [sq_nonneg (‖z‖ ^ 2 - 1), sq_nonneg ‖z‖]
    nlinarith [norm_nonneg z]
  · intro hz
    have hidentity :=
      normalizedRankOneWeyl_normSq_numerator_sub_denominator p z
    have hsquares :
        ‖(p : ℂ) * z ^ 2 - 1‖ ^ 2 =
          ‖(p : ℂ) - z ^ 2‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      rw [hz] at hidentity
      norm_num at hidentity
      exact sub_eq_zero.mp hidentity
    have hnormeq :
        ‖(p : ℂ) * z ^ 2 - 1‖ =
          ‖(p : ℂ) - z ^ 2‖ := by
      nlinarith [norm_nonneg ((p : ℂ) * z ^ 2 - 1),
        norm_nonneg ((p : ℂ) - z ^ 2)]
    exact (div_eq_one_iff_eq
      (ne_of_gt (norm_pos_iff.mpr hden))).2 hnormeq

/-- Off the unitary circle, the complementary Weyl channel is expansive on the outward face. -/
theorem norm_normalizedRankOneWeylComplementaryEigenvalue_gt_one
    {p : ℝ} (hp : 1 < p) {z : ℂ} (hz : 1 < ‖z‖)
    (hden : (p : ℂ) - z ^ 2 ≠ 0) :
    1 < ‖normalizedRankOneWeylComplementaryEigenvalue p z‖ := by
  rw [normalizedRankOneWeylComplementaryEigenvalue, norm_div,
    one_lt_div (norm_pos_iff.mpr hden)]
  have hidentity :=
    normalizedRankOneWeyl_normSq_numerator_sub_denominator p z
  have hpFactor : 0 < p ^ 2 - 1 := by nlinarith
  have hz2 : 1 < ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hz4 : 1 < ‖z‖ ^ 4 := by
    have : 1 < (‖z‖ ^ 2) ^ 2 := by nlinarith
    nlinarith
  have hsquares :
      ‖(p : ℂ) - z ^ 2‖ ^ 2 <
        ‖(p : ℂ) * z ^ 2 - 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    nlinarith
  nlinarith [norm_nonneg ((p : ℂ) * z ^ 2 - 1),
    norm_nonneg ((p : ℂ) - z ^ 2)]

/-- Real radial specialization of the complementary Weyl modular cost. -/
def radialRankOneWeylModularCost (p c : ℝ) : ℝ :=
  (p * p ^ (2 * c) - 1) / (p - p ^ (2 * c))

/-- The real outward Weyl channel pays more than the literal modular retuning `p^(2c)` at every
prime scale. -/
theorem radialRankOneWeylModularCost_gt_rpow
    {p c : ℝ} (hp : 1 < p) (hc0 : 0 < c) (hcHalf : c < 1 / 2) :
    p ^ (2 * c) < radialRankOneWeylModularCost p c := by
  have hrOne : 1 < p ^ (2 * c) :=
    Real.one_lt_rpow hp (by linarith)
  have hrP : p ^ (2 * c) < p := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hp (by linarith : 2 * c < 1)
  rw [radialRankOneWeylModularCost, lt_div_iff₀ (sub_pos.mpr hrP)]
  nlinarith

/-- Scalar normalization cannot change the ratio between the spherical and complementary
channels of the rank-one Weyl block. -/
theorem normalizedRankOneWeyl_scalarGauge_ratio
    {p : ℝ} {z gauge : ℂ} (hgauge : gauge ≠ 0) :
    (gauge * normalizedRankOneWeylComplementaryEigenvalue p z) / gauge =
      normalizedRankOneWeylComplementaryEigenvalue p z := by
  field_simp

end

end RHTower
