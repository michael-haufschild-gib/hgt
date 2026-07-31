import GaloisForLFunctions.RHTower.PrimeClockCriticalProfile
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture
import GaloisForLFunctions.HTGeometry.LogSquaredTailIntegral

/-!
# Reflected prime-valuation Hellinger critical profile

The fixed-displacement Hellinger--Rees law has two different oriented faces.  At the shrinking
critical window `ε = c / log N`, their direct reflected-pair affinity has a universal nonlinear
limit.  Its exponent is exactly the already source-derived prime-clock/Dickman--Wick profile

`4 ∫₀¹ sinh²(cu) / u du`.

This identifies the prime-clock critical profile as an information-geometric Hellinger angle,
not an auxiliary clock normalization.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Squared Hellinger affinity of the two geometric prime-valuation laws at reflected
displacements `ε` and `-ε`. -/
def reflectedPrimeValuationSquaredHellingerFactor
    (ε : ℝ) (p : ℕ) : ℝ :=
  squaredHellingerAffinity
    ((p : ℝ) ^ (-(1 - 2 * ε)))
    ((p : ℝ) ^ (-(1 + 2 * ε)))
    ((p : ℝ)⁻¹)

/-- Exact local defect from unit Hellinger affinity in the critical window. -/
def reflectedPrimeValuationHellingerDefect
    (N : ℕ) (c : ℝ) (p : ℕ) : ℝ :=
  (4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p) /
    (1 - ((p : ℝ)⁻¹)) ^ 2

/-- Finite reflected-pair squared Hellinger affinity. -/
def reflectedPrimeValuationSquaredHellingerLE
    (N : ℕ) (c : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE N,
    reflectedPrimeValuationSquaredHellingerFactor (c / Real.log N) p

/-- Sum of exact local Hellinger defects. -/
def reflectedPrimeValuationHellingerDefectSum
    (N : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N,
    reflectedPrimeValuationHellingerDefect N c p

private lemma reflected_rpow_product_eq_inv_sq
    (ε : ℝ) {p : ℕ} (hpPrime : p.Prime) :
    (p : ℝ) ^ (-(1 - 2 * ε)) *
        (p : ℝ) ^ (-(1 + 2 * ε)) =
      ((p : ℝ)⁻¹) ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  calc
    (p : ℝ) ^ (-(1 - 2 * ε)) *
        (p : ℝ) ^ (-(1 + 2 * ε)) =
        (p : ℝ) ^ (-(1 - 2 * ε) + -(1 + 2 * ε)) := by
          rw [← Real.rpow_add hp]
    _ = (p : ℝ) ^ (-2 : ℝ) := by congr 1; ring
    _ = ((p : ℝ)⁻¹) ^ 2 := by
      rw [← Real.rpow_neg_one, ← Real.rpow_mul_natCast hp.le]
      norm_num

private lemma reflected_rpow_sum_sub_two_inv_eq_clock
    (ε : ℝ) {p : ℕ} (hpPrime : p.Prime) :
    (p : ℝ) ^ (-(1 - 2 * ε)) +
          (p : ℝ) ^ (-(1 + 2 * ε)) -
          2 * (p : ℝ)⁻¹ =
      4 * Real.sinh (ε * Real.log p) ^ 2 / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hplus :
      ((p : ℝ) ^ (-(1 / 2 + ε))) ^ 2 =
        (p : ℝ) ^ (-(1 + 2 * ε)) := by
    rw [← Real.rpow_mul_natCast hp.le]
    congr 1
    norm_num
    ring
  have hminus :
      ((p : ℝ) ^ (-(1 / 2 - ε))) ^ 2 =
        (p : ℝ) ^ (-(1 - 2 * ε)) := by
    rw [← Real.rpow_mul_natCast hp.le]
    congr 1
    norm_num
    ring
  have hcross :
      (p : ℝ) ^ (-(1 / 2 + ε)) *
          (p : ℝ) ^ (-(1 / 2 - ε)) =
        (p : ℝ)⁻¹ := by
    rw [← Real.rpow_add hp, ← Real.rpow_neg_one]
    congr 1
    ring
  have hclock := reflected_rpow_diff_sq_eq_sinh hp ε
  rw [sub_sq, hplus, hminus] at hclock
  calc
    (p : ℝ) ^ (-(1 - 2 * ε)) +
          (p : ℝ) ^ (-(1 + 2 * ε)) -
          2 * (p : ℝ)⁻¹ =
        (p : ℝ) ^ (-(1 + 2 * ε)) -
          2 * ((p : ℝ) ^ (-(1 / 2 + ε)) *
            (p : ℝ) ^ (-(1 / 2 - ε))) +
          (p : ℝ) ^ (-(1 - 2 * ε)) := by rw [hcross]; ring
    _ = 4 * Real.sinh (ε * Real.log p) ^ 2 / p := by
      simpa only [mul_assoc] using hclock

/-- The reflected local Hellinger factor is exactly one minus the prime-clock energy divided by
the square of the critical vacuum mass. -/
theorem reflectedPrimeValuationSquaredHellingerFactor_eq_one_sub_defect
    (N : ℕ) (c : ℝ) {p : ℕ} (hpPrime : p.Prime) :
    reflectedPrimeValuationSquaredHellingerFactor (c / Real.log N) p =
      1 - reflectedPrimeValuationHellingerDefect N c p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hden : (1 - ((p : ℝ)⁻¹)) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    have hinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp).2 hp1
    linarith
  have hprod := reflected_rpow_product_eq_inv_sq (c / Real.log N) hpPrime
  have hsum := reflected_rpow_sum_sub_two_inv_eq_clock (c / Real.log N) hpPrime
  rw [reflectedPrimeValuationSquaredHellingerFactor,
    squaredHellingerAffinity, reflectedPrimeValuationHellingerDefect]
  rw [← hsum]
  calc
    (1 - (p : ℝ) ^ (-(1 - 2 * (c / Real.log N)))) *
          (1 - (p : ℝ) ^ (-(1 + 2 * (c / Real.log N)))) /
          (1 - (p : ℝ)⁻¹) ^ 2 =
        ((1 - (p : ℝ)⁻¹) ^ 2 -
          ((p : ℝ) ^ (-(1 - 2 * (c / Real.log N))) +
            (p : ℝ) ^ (-(1 + 2 * (c / Real.log N))) -
            2 * (p : ℝ)⁻¹)) /
          (1 - (p : ℝ)⁻¹) ^ 2 := by
            congr 1
            nlinarith [hprod]
    _ = 1 -
          ((p : ℝ) ^ (-(1 - 2 * (c / Real.log N))) +
            (p : ℝ) ^ (-(1 + 2 * (c / Real.log N))) -
            2 * (p : ℝ)⁻¹) /
          (1 - (p : ℝ)⁻¹) ^ 2 := by
            rw [sub_div, div_self hden]

private lemma prime_vacuum_renormalization_sub_one_nonneg_le
    {p : ℕ} (hpPrime : p.Prime) :
    0 ≤ 1 / (1 - ((p : ℝ)⁻¹)) ^ 2 - 1 ∧
      1 / (1 - ((p : ℝ)⁻¹)) ^ 2 - 1 ≤ 8 / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
  let u : ℝ := (p : ℝ)⁻¹
  have hu0 : 0 ≤ u := inv_nonneg.mpr hp.le
  have hu2 : u ≤ 1 / 2 := by
    dsimp [u]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hp2
  have hden : 0 < (1 - u) ^ 2 := sq_pos_of_pos (by linarith)
  constructor
  · rw [sub_nonneg, one_div]
    exact (one_le_inv₀ hden).2 (by nlinarith [sq_nonneg u])
  · have hpoly : 0 ≤ 8 * (u - 1 / 2) ^ 2 + (4 - 7 * u) := by
      nlinarith [sq_nonneg (u - 1 / 2)]
    have hcleared : 1 ≤ (8 * u + 1) * (1 - u) ^ 2 := by
      nlinarith
    have hquot : 1 / (1 - u) ^ 2 ≤ 8 * u + 1 :=
      (div_le_iff₀ hden).2 (by simpa [one_mul] using hcleared)
    dsimp [u] at hquot ⊢
    simpa only [div_eq_mul_inv] using sub_le_iff_le_add.mpr hquot

private lemma reflected_hyperbolic_energy_bound
    {N p : ℕ} (c : ℝ) (hN : 2 ≤ N) (hp : p ∈ Nat.primesLE N) :
    4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p ≤
      4 * c ^ 2 * Real.cosh |c| ^ 2 *
        (Real.log p ^ 2 / (Real.log N ^ 2 * p)) := by
  have hpdata := Nat.mem_primesLE.mp hp
  have hpPrime : p.Prime := hpdata.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogp0 : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hlogpN : Real.log p ≤ Real.log N :=
    Real.log_le_log hp0 (by exact_mod_cast hpdata.1)
  let u : ℝ := Real.log p / Real.log N
  have hu0 : 0 ≤ u := div_nonneg hlogp0 hlogN.le
  have hu1 : u ≤ 1 := (div_le_one hlogN).2 hlogpN
  have hcu : |c * u| ≤ |c| := by
    rw [abs_mul, abs_of_nonneg hu0]
    exact mul_le_of_le_one_right (abs_nonneg c) hu1
  have hsinh := abs_sinh_le_abs_mul_cosh (abs_nonneg c) hcu
  have hsinhSq :
      Real.sinh (c * u) ^ 2 ≤ (|c * u| * Real.cosh |c|) ^ 2 := by
    have hpow := pow_le_pow_left₀ (abs_nonneg (Real.sinh (c * u))) hsinh 2
    simpa only [sq_abs] using hpow
  have harg : c / Real.log N * Real.log p = c * u := by
    dsimp [u]
    ring
  rw [harg]
  calc
    4 * Real.sinh (c * u) ^ 2 / p ≤
        4 * (|c * u| * Real.cosh |c|) ^ 2 / p := by
          gcongr
    _ = 4 * c ^ 2 * Real.cosh |c| ^ 2 *
        (Real.log p ^ 2 / (Real.log N ^ 2 * p)) := by
          dsimp [u]
          rw [abs_mul, abs_of_nonneg hu0]
          have hcabsSq : |c| ^ 2 = c ^ 2 := sq_abs c
          simp only [u]
          field_simp
          ring_nf
          rw [hcabsSq]
          ring

private theorem reflectedPrimeValuationHellingerDefectSum_sub_energy_bound
    (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    0 ≤ reflectedPrimeValuationHellingerDefectSum N c -
        primeClockCutoffEnergy N (c / Real.log N) ∧
      reflectedPrimeValuationHellingerDefectSum N c -
          primeClockCutoffEnergy N (c / Real.log N) ≤
        (32 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2) *
          ∑' n : ℕ, (Real.log n / n) ^ 2 := by
  rw [reflectedPrimeValuationHellingerDefectSum,
    primeClockCutoffEnergy_eq_sinh, ← Finset.sum_sub_distrib]
  have hterm : ∀ p ∈ Nat.primesLE N,
      0 ≤ reflectedPrimeValuationHellingerDefect N c p -
          4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p ∧
        reflectedPrimeValuationHellingerDefect N c p -
            4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p ≤
          (32 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2) *
            (Real.log p / p) ^ 2 := by
    intro p hp
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    let e : ℝ := 4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p
    let g : ℝ := 1 / (1 - ((p : ℝ)⁻¹)) ^ 2
    have he0 : 0 ≤ e := by dsimp [e]; positivity
    have hg := prime_vacuum_renormalization_sub_one_nonneg_le hpPrime
    have heBound := reflected_hyperbolic_energy_bound c hN hp
    have hg' : 0 ≤ g - 1 ∧ g - 1 ≤ 8 / (p : ℝ) := by
      simpa [g] using hg
    have heBound' : e ≤
        4 * c ^ 2 * Real.cosh |c| ^ 2 *
          (Real.log p ^ 2 / (Real.log N ^ 2 * p)) := by
      simpa [e] using heBound
    have hrewrite :
        reflectedPrimeValuationHellingerDefect N c p -
            4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p =
          e * (g - 1) := by
      dsimp [reflectedPrimeValuationHellingerDefect, e, g]
      ring
    rw [hrewrite]
    constructor
    · exact mul_nonneg he0 hg'.1
    · calc
        e * (g - 1) ≤
            (4 * c ^ 2 * Real.cosh |c| ^ 2 *
              (Real.log p ^ 2 / (Real.log N ^ 2 * p))) *
              (8 / p) := by
                exact mul_le_mul heBound' hg'.2 hg'.1 (by positivity)
        _ = (32 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2) *
              (Real.log p / p) ^ 2 := by
                field_simp
                ring
  constructor
  · exact Finset.sum_nonneg fun p hp => (hterm p hp).1
  · calc
      ∑ p ∈ Nat.primesLE N,
          (reflectedPrimeValuationHellingerDefect N c p -
            4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p) ≤
          ∑ p ∈ Nat.primesLE N,
            (32 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2) *
              (Real.log p / p) ^ 2 := by
                exact Finset.sum_le_sum fun p hp => (hterm p hp).2
      _ = (32 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2) *
          ∑ p ∈ Nat.primesLE N, (Real.log p / p) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ (32 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2) *
          ∑' n : ℕ, (Real.log n / n) ^ 2 := by
            gcongr
            exact GaloisForLFunctions.HTGeometry.summable_logSq_div_sq.sum_le_tsum
              (Nat.primesLE N) (fun n _ => sq_nonneg _)

private theorem tendsto_reflectedPrimeValuationHellingerDefectSum_sub_energy_zero
    (c : ℝ) :
    Tendsto (fun N : ℕ =>
      reflectedPrimeValuationHellingerDefectSum N c -
        primeClockCutoffEnergy N (c / Real.log N)) atTop (𝓝 0) := by
  let T : ℝ := ∑' n : ℕ, (Real.log n / n) ^ 2
  let K : ℝ := 32 * c ^ 2 * Real.cosh |c| ^ 2
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogSq : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ) ^ 2)⁻¹)
      atTop (𝓝 0) := hlogSq.inv_tendsto_atTop
  have hupper : Tendsto (fun N : ℕ => K * T * (Real.log (N : ℝ) ^ 2)⁻¹)
      atTop (𝓝 0) := by
    simpa using hinv.const_mul (K * T)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (reflectedPrimeValuationHellingerDefectSum_sub_energy_bound N c hN).1
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hbound :=
      (reflectedPrimeValuationHellingerDefectSum_sub_energy_bound N c hN).2
    exact hbound
  · have heq :
        (fun N : ℕ =>
          (32 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2) *
            ∑' n : ℕ, (Real.log n / n) ^ 2) =
        (fun N : ℕ => K * T * (Real.log N ^ 2)⁻¹) := by
          funext N
          simp only [K, T, div_eq_mul_inv]
          ring
    rw [heq]
    exact hupper

/-- The exact reflected Hellinger defect sum has the same universal critical profile as the
prime clock.  Vacuum renormalization changes only a vanishing second-order term. -/
theorem tendsto_reflectedPrimeValuationHellingerDefectSum_critical_profile
    (c : ℝ) :
    Tendsto (fun N : ℕ => reflectedPrimeValuationHellingerDefectSum N c)
      atTop (𝓝 (primeClockUniversalProfile c)) := by
  have hdiff :=
    tendsto_reflectedPrimeValuationHellingerDefectSum_sub_energy_zero c
  have henergy := tendsto_primeClockCutoffEnergy_critical_profile c
  have hsum := hdiff.add henergy
  have ht := hsum.congr' (Eventually.of_forall fun N => by ring)
  simpa only [zero_add] using ht

private lemma prime_log_sq_div_le_four {p : ℕ} (hpPrime : p.Prime) :
    Real.log p ^ 2 / p ≤ 4 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlog0 : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hlog := Real.log_le_rpow_div (x := (p : ℝ)) (ε := (1 : ℝ) / 2)
    hp0.le (by norm_num)
  have hsq :
      Real.log p ^ 2 ≤ ((p : ℝ) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  calc
    Real.log p ^ 2 / p ≤
        ((p : ℝ) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)) ^ 2 / p := by
          exact div_le_div_of_nonneg_right hsq hp0.le
    _ = 4 := by
      rw [div_pow]
      norm_num
      rw [← Real.rpow_mul_natCast hp0.le]
      norm_num
      field_simp

private lemma reflectedPrimeValuationHellingerDefect_nonneg_le
    {N p : ℕ} (c : ℝ) (hN : 2 ≤ N) (hp : p ∈ Nat.primesLE N) :
    0 ≤ reflectedPrimeValuationHellingerDefect N c p ∧
      reflectedPrimeValuationHellingerDefect N c p ≤
        80 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2 := by
  have hpPrime := (Nat.mem_primesLE.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  let e : ℝ := 4 * Real.sinh (c / Real.log N * Real.log p) ^ 2 / p
  let g : ℝ := 1 / (1 - ((p : ℝ)⁻¹)) ^ 2
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hgRaw := prime_vacuum_renormalization_sub_one_nonneg_le hpPrime
  have hg0 : 0 ≤ g := by
    dsimp [g]
    positivity
  have hg5 : g ≤ 5 := by
    have hpdiv : 8 / (p : ℝ) ≤ 4 := by
      rw [div_le_iff₀ hp0]
      nlinarith
    dsimp [g]
    linarith [hgRaw.2]
  have heBound := reflected_hyperbolic_energy_bound c hN hp
  have hlogSq := prime_log_sq_div_le_four hpPrime
  have hrewrite :
      reflectedPrimeValuationHellingerDefect N c p = e * g := by
    dsimp [reflectedPrimeValuationHellingerDefect, e, g]
    ring
  rw [hrewrite]
  constructor
  · exact mul_nonneg he0 hg0
  · calc
      e * g ≤
          (4 * c ^ 2 * Real.cosh |c| ^ 2 *
            (Real.log p ^ 2 / (Real.log N ^ 2 * p))) * 5 := by
              apply mul_le_mul
              · simpa [e] using heBound
              · exact hg5
              · exact hg0
              · positivity
      _ ≤ 80 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2 := by
        rw [show Real.log p ^ 2 / (Real.log N ^ 2 * p) =
            (Real.log p ^ 2 / p) / Real.log N ^ 2 by field_simp]
        have hnonneg : 0 ≤ 4 * c ^ 2 * Real.cosh |c| ^ 2 := by positivity
        have hscaled :
            4 * c ^ 2 * Real.cosh |c| ^ 2 * (Real.log p ^ 2 / p) ≤
              4 * c ^ 2 * Real.cosh |c| ^ 2 * 4 :=
          mul_le_mul_of_nonneg_left hlogSq hnonneg
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hinv0 : 0 ≤ (Real.log (N : ℝ) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
        have hscaledInv := mul_le_mul_of_nonneg_right hscaled hinv0
        calc
          4 * c ^ 2 * Real.cosh |c| ^ 2 *
                (Real.log p ^ 2 * (p : ℝ)⁻¹ * (Real.log N ^ 2)⁻¹) * 5 =
              (4 * c ^ 2 * Real.cosh |c| ^ 2 *
                (Real.log p ^ 2 / p)) * (Real.log N ^ 2)⁻¹ * 5 := by ring
          _ ≤ (4 * c ^ 2 * Real.cosh |c| ^ 2 * 4) *
                (Real.log N ^ 2)⁻¹ * 5 := by
                  gcongr
          _ = 80 * c ^ 2 * Real.cosh |c| ^ 2 *
                (Real.log N ^ 2)⁻¹ := by ring

/-- Uniform envelope for every local critical-window Hellinger defect. -/
def reflectedPrimeValuationHellingerUniformBound (N : ℕ) (c : ℝ) : ℝ :=
  80 * c ^ 2 * Real.cosh |c| ^ 2 / Real.log N ^ 2

private theorem tendsto_reflectedPrimeValuationHellingerUniformBound_zero
    (c : ℝ) :
    Tendsto (fun N : ℕ => reflectedPrimeValuationHellingerUniformBound N c)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogSq : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ) ^ 2)⁻¹)
      atTop (𝓝 0) := hlogSq.inv_tendsto_atTop
  simpa [reflectedPrimeValuationHellingerUniformBound, div_eq_mul_inv] using
    hinv.const_mul (80 * c ^ 2 * Real.cosh |c| ^ 2)

private lemma neg_log_one_sub_sub_nonneg_le_two_sq
    {x : ℝ} (_hx0 : 0 ≤ x) (hxHalf : x ≤ 1 / 2) :
    0 ≤ -Real.log (1 - x) - x ∧
      -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  have hlogUpper := Real.log_le_sub_one_of_pos hpos
  have hlogLower := Real.one_sub_inv_le_log_of_pos hpos
  constructor
  · linarith
  · have hratio :
        (1 - x)⁻¹ - 1 - x ≤ 2 * x ^ 2 := by
      have hmul :
          ((1 - x)⁻¹ - 1 - x) * (1 - x) ≤
            (2 * x ^ 2) * (1 - x) := by
        field_simp
        nlinarith [sq_nonneg x]
      exact (mul_le_mul_iff_left₀ hpos).mp hmul
    linarith

/-- Sum of local logarithmic remainders between multiplication and addition. -/
def reflectedPrimeValuationHellingerLogRemainderSum
    (N : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N,
    (-Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) -
      reflectedPrimeValuationHellingerDefect N c p)

private theorem tendsto_reflectedPrimeValuationHellingerLogRemainderSum_zero
    (c : ℝ) :
    Tendsto (fun N : ℕ =>
      reflectedPrimeValuationHellingerLogRemainderSum N c)
      atTop (𝓝 0) := by
  have hB := tendsto_reflectedPrimeValuationHellingerUniformBound_zero c
  have hD := tendsto_reflectedPrimeValuationHellingerDefectSum_critical_profile c
  have hupper :
      Tendsto (fun N : ℕ =>
        2 * reflectedPrimeValuationHellingerUniformBound N c *
          reflectedPrimeValuationHellingerDefectSum N c)
        atTop (𝓝 0) := by
    have ht := (hB.const_mul 2).mul hD
    simpa using ht
  have hBHalf : ∀ᶠ N : ℕ in atTop,
      reflectedPrimeValuationHellingerUniformBound N c ≤ 1 / 2 := by
    have ht := (tendsto_order.1 hB).2 (1 / 2) (by norm_num)
    filter_upwards [ht] with N hN
    exact hN.le
  apply squeeze_zero'
    (g := fun N : ℕ =>
      2 * reflectedPrimeValuationHellingerUniformBound N c *
        reflectedPrimeValuationHellingerDefectSum N c)
  · filter_upwards [eventually_ge_atTop 2, hBHalf] with N hN hBhalf
    rw [reflectedPrimeValuationHellingerLogRemainderSum]
    apply Finset.sum_nonneg
    intro p hp
    have hx :=
      reflectedPrimeValuationHellingerDefect_nonneg_le c hN hp
    exact (neg_log_one_sub_sub_nonneg_le_two_sq hx.1 (hx.2.trans hBhalf)).1
  · filter_upwards [eventually_ge_atTop 2, hBHalf] with N hN hBhalf
    rw [reflectedPrimeValuationHellingerLogRemainderSum]
    calc
      ∑ p ∈ Nat.primesLE N,
          (-Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) -
            reflectedPrimeValuationHellingerDefect N c p) ≤
          ∑ p ∈ Nat.primesLE N,
            2 * reflectedPrimeValuationHellingerUniformBound N c *
              reflectedPrimeValuationHellingerDefect N c p := by
                apply Finset.sum_le_sum
                intro p hp
                have hx :=
                  reflectedPrimeValuationHellingerDefect_nonneg_le c hN hp
                have hxB :
                    reflectedPrimeValuationHellingerDefect N c p ≤
                      reflectedPrimeValuationHellingerUniformBound N c := by
                  simpa [reflectedPrimeValuationHellingerUniformBound] using hx.2
                have herr :=
                  neg_log_one_sub_sub_nonneg_le_two_sq hx.1 (hxB.trans hBhalf)
                calc
                  -Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) -
                        reflectedPrimeValuationHellingerDefect N c p ≤
                      2 * reflectedPrimeValuationHellingerDefect N c p ^ 2 :=
                    herr.2
                  _ ≤ 2 * reflectedPrimeValuationHellingerUniformBound N c *
                        reflectedPrimeValuationHellingerDefect N c p := by
                    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hxB)]
      _ = 2 * reflectedPrimeValuationHellingerUniformBound N c *
          reflectedPrimeValuationHellingerDefectSum N c := by
            rw [reflectedPrimeValuationHellingerDefectSum, Finset.mul_sum]
  · exact hupper

/-- **Universal reflected Hellinger critical-window law.**  At displacement
`ε_N = c / log N`, the squared Hellinger affinity between the two reflected prime-valuation
product states converges to

`exp (-4 ∫₀¹ sinh²(cu) / u du)`.

Thus the prime-clock/Dickman--Wick profile is exactly the asymptotic Hellinger angle of the
reflected valuation sectors. -/
theorem tendsto_reflectedPrimeValuationSquaredHellingerLE_critical_profile
    (c : ℝ) :
    Tendsto (fun N : ℕ =>
      reflectedPrimeValuationSquaredHellingerLE N c)
      atTop (𝓝 (Real.exp (-primeClockUniversalProfile c))) := by
  have hB := tendsto_reflectedPrimeValuationHellingerUniformBound_zero c
  have hBHalf : ∀ᶠ N : ℕ in atTop,
      reflectedPrimeValuationHellingerUniformBound N c ≤ 1 / 2 := by
    have ht := (tendsto_order.1 hB).2 (1 / 2) (by norm_num)
    filter_upwards [ht] with N hN
    exact hN.le
  have hlogEq : ∀ᶠ N : ℕ in atTop,
      Real.log (reflectedPrimeValuationSquaredHellingerLE N c) =
        -reflectedPrimeValuationHellingerDefectSum N c -
          reflectedPrimeValuationHellingerLogRemainderSum N c := by
    filter_upwards [eventually_ge_atTop 2, hBHalf] with N hN hBhalf
    have hne : ∀ p ∈ Nat.primesLE N,
        reflectedPrimeValuationSquaredHellingerFactor
            (c / Real.log N) p ≠ 0 := by
      intro p hp
      have hpPrime := (Nat.mem_primesLE.mp hp).2
      have hx := reflectedPrimeValuationHellingerDefect_nonneg_le c hN hp
      have hxB :
          reflectedPrimeValuationHellingerDefect N c p ≤
            reflectedPrimeValuationHellingerUniformBound N c := by
        simpa [reflectedPrimeValuationHellingerUniformBound] using hx.2
      rw [reflectedPrimeValuationSquaredHellingerFactor_eq_one_sub_defect
        N c hpPrime]
      nlinarith
    rw [reflectedPrimeValuationSquaredHellingerLE, Real.log_prod hne]
    have hfactor :
        ∑ p ∈ Nat.primesLE N,
            Real.log
              (reflectedPrimeValuationSquaredHellingerFactor
                (c / Real.log N) p) =
          ∑ p ∈ Nat.primesLE N,
            Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [reflectedPrimeValuationSquaredHellingerFactor_eq_one_sub_defect
        N c (Nat.mem_primesLE.mp hp).2]
    rw [hfactor, reflectedPrimeValuationHellingerDefectSum,
      reflectedPrimeValuationHellingerLogRemainderSum]
    calc
      ∑ p ∈ Nat.primesLE N,
          Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) =
          ∑ p ∈ Nat.primesLE N,
            (-reflectedPrimeValuationHellingerDefect N c p -
              (-Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) -
                reflectedPrimeValuationHellingerDefect N c p)) := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  ring
      _ = (∑ p ∈ Nat.primesLE N,
              -reflectedPrimeValuationHellingerDefect N c p) -
            ∑ p ∈ Nat.primesLE N,
              (-Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) -
                reflectedPrimeValuationHellingerDefect N c p) := by
                  rw [Finset.sum_sub_distrib]
      _ = -(∑ p ∈ Nat.primesLE N,
              reflectedPrimeValuationHellingerDefect N c p) -
            ∑ p ∈ Nat.primesLE N,
              (-Real.log (1 - reflectedPrimeValuationHellingerDefect N c p) -
                reflectedPrimeValuationHellingerDefect N c p) := by
                  rw [Finset.sum_neg_distrib]
  have hD := tendsto_reflectedPrimeValuationHellingerDefectSum_critical_profile c
  have hR := tendsto_reflectedPrimeValuationHellingerLogRemainderSum_zero c
  have hlogBase := hD.neg.sub hR
  have hlog :
      Tendsto (fun N : ℕ =>
        Real.log (reflectedPrimeValuationSquaredHellingerLE N c))
        atTop (𝓝 (-primeClockUniversalProfile c)) := by
    have hEq : (fun N : ℕ =>
        -reflectedPrimeValuationHellingerDefectSum N c -
          reflectedPrimeValuationHellingerLogRemainderSum N c) =ᶠ[atTop]
        (fun N : ℕ =>
          Real.log (reflectedPrimeValuationSquaredHellingerLE N c)) :=
      hlogEq.mono fun N hN => hN.symm
    have ht := hlogBase.congr' hEq
    simpa using ht
  have hExp :
      Tendsto (fun N : ℕ =>
        Real.exp
          (Real.log (reflectedPrimeValuationSquaredHellingerLE N c)))
        atTop (𝓝 (Real.exp (-primeClockUniversalProfile c))) :=
    (Real.continuous_exp.tendsto _).comp hlog
  have hExpEq : ∀ᶠ N : ℕ in atTop,
      Real.exp
          (Real.log (reflectedPrimeValuationSquaredHellingerLE N c)) =
        reflectedPrimeValuationSquaredHellingerLE N c := by
    filter_upwards [eventually_ge_atTop 2, hBHalf] with N hN hBhalf
    apply Real.exp_log
    rw [reflectedPrimeValuationSquaredHellingerLE]
    apply Finset.prod_pos
    intro p hp
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    have hx := reflectedPrimeValuationHellingerDefect_nonneg_le c hN hp
    have hxB :
        reflectedPrimeValuationHellingerDefect N c p ≤
          reflectedPrimeValuationHellingerUniformBound N c := by
      simpa [reflectedPrimeValuationHellingerUniformBound] using hx.2
    rw [reflectedPrimeValuationSquaredHellingerFactor_eq_one_sub_defect
      N c hpPrime]
    nlinarith
  exact hExp.congr' hExpEq

/-- The reflected Hellinger partition and the exponentiated prime-clock energy are asymptotic
reciprocals in the critical window. -/
theorem tendsto_reflectedHellinger_mul_exp_primeClockEnergy_one
    (c : ℝ) :
    Tendsto (fun N : ℕ =>
      reflectedPrimeValuationSquaredHellingerLE N c *
        Real.exp (primeClockCutoffEnergy N (c / Real.log N)))
      atTop (𝓝 1) := by
  have hH :=
    tendsto_reflectedPrimeValuationSquaredHellingerLE_critical_profile c
  have hE := tendsto_primeClockCutoffEnergy_critical_profile c
  have hExp :
      Tendsto (fun N : ℕ =>
        Real.exp (primeClockCutoffEnergy N (c / Real.log N)))
        atTop (𝓝 (Real.exp (primeClockUniversalProfile c))) :=
    (Real.continuous_exp.tendsto _).comp hE
  have hmul := hH.mul hExp
  simpa [← Real.exp_add] using hmul

end

end RHTower
