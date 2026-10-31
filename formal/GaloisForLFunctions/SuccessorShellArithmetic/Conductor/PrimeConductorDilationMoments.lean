import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorHeadNorm
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorDilationEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimePowerMangoldtReindex
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

/-!
# Logarithmic moments of conductor dilation

A prime dilation descends one valuation chain. A mixed transition is
supported either at one exponent or on a geometric tail after the
conductor has lost its whole prime factor. The latter tail has mean
logarithmic excess at most one.
-/

open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence ArithmeticIntersectionTheory
noncomputable section

/-- A positive prime-power dilation fixes its own conductor exactly when the prime is coprime to it. -/
theorem primeConductorDilationMean_self_prime_pow {m p j : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hj : 0 < j) :
    primeConductorDilationMean m m (p ^ j) = if p ∣ m then 0 else 1 := by
  rw [primeConductorDilationMean_eq_reduced hm hm]
  by_cases hpm : p ∣ m
  · have hpg : p ≤ Nat.gcd m (p ^ j) := Nat.le_of_dvd
      (Nat.gcd_pos_of_pos_left _ hm) (Nat.dvd_gcd hpm (dvd_pow_self p hj.ne'))
    have hquot : m / Nat.gcd m (p ^ j) < m := Nat.div_lt_self hm (hp.one_lt.trans_le hpg)
    rw [if_pos hpm, if_neg hquot.ne']
  · have hcop := ((hp.coprime_iff_not_dvd.mpr hpm).symm).pow_right j
    rw [hcop.gcd_eq_one, Nat.div_one, if_pos rfl, if_neg hpm,
      ← sq, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
    exact div_self (by exact_mod_cast (Nat.totient_pos.mpr hm).ne')

private theorem hasSum_primePower_logMoment {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) * Real.log p ^ 2 / (p : ℝ) ^ (j + 1))
      ((p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith only [hpR]
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := (div_lt_one (by positivity)).mpr hpR
  have hr : ‖(1 : ℝ) / p‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
    (hasSum_geometric_of_lt_one hr0 hr1)).mul_left (Real.log p ^ 2 / p)
  have heq : Real.log p ^ 2 / p * ((1 / (p : ℝ)) / (1 - (1 : ℝ) / p) ^ 2 + (1 - (1 : ℝ) / p)⁻¹) =
      (p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2 := by
    field_simp [hp0, hp1]
    ring
  rw [heq] at h
  apply h.congr_fun
  intro j
  rw [pow_succ, _root_.one_div_pow]
  ring

/-- The logarithmic reciprocal Mangoldt mass on one prime tower is an exact geometric moment. -/
theorem hasSum_localMangoldt_logMoment {p : ℕ} (hp : p.Prime) :
    HasSum (fun t : ℕ => if p ∣ t then Real.log t * vonMangoldt t / (t : ℝ) else 0)
      ((p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2) := by
  apply hasSum_primePower_mangoldt hp (fun t => Real.log (t : ℝ))
  apply (hasSum_primePower_logMoment hp).congr_fun
  intro j
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  ring

/-- The prime-tower logarithmic moment costs at most one excess logarithm. -/
theorem localMangoldt_logMoment_le {p : ℕ} (hp : p.Prime) :
    (p : ℝ) * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2 ≤
      (Real.log p + 1) * (Real.log p / ((p : ℝ) - 1)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp1 : 0 < (p : ℝ) - 1 := by linarith only [hpR]
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p by positivity)
  have hm := mul_le_mul_of_nonneg_left hlog (Real.log_natCast_nonneg p)
  rw [div_le_iff₀ (sq_pos_of_pos hp1)]
  field_simp [hp1.ne']
  nlinarith only [hm]

private theorem reduced_conductor_eq_iff {l m : ℕ} (hl : 0 < l) (k : ℕ) :
    m = l / Nat.gcd l k ↔ l = m * Nat.gcd l k := by
  have hg : 0 < Nat.gcd l k := Nat.gcd_pos_of_pos_left k hl
  constructor
  · intro h
    rw [h]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left l k)).symm
  · intro h
    exact ((congrArg (fun z : ℕ => z / Nat.gcd l k) h).trans (Nat.mul_div_cancel m hg)).symm

private theorem gcd_primeShift (m p a j : ℕ) :
    Nat.gcd (m * p ^ a) (p ^ (a + j)) = p ^ a * Nat.gcd m (p ^ j) := by
  rw [pow_add, Nat.mul_comm m (p ^ a), Nat.gcd_mul_left]

private theorem reduced_primeShift_eq_iff {m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (a j : ℕ) :
    m = (m * p ^ a) / Nat.gcd (m * p ^ a) (p ^ (a + j)) ↔
      j = 0 ∨ ¬p ∣ m := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  rw [reduced_conductor_eq_iff (Nat.mul_pos hm hpa), gcd_primeShift]
  by_cases hj : j = 0
  · simp only [hj, pow_zero, Nat.gcd_one_right, mul_one, true_or]
  by_cases hpm : p ∣ m
  · have hg : 1 < Nat.gcd m (p ^ j) := hp.one_lt.trans_le
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hm)
        (Nat.dvd_gcd hpm (dvd_pow_self p hj)))
    have hlt : m * p ^ a < m * (p ^ a * Nat.gcd m (p ^ j)) := by
      simpa only [mul_one, Nat.mul_assoc] using
        Nat.mul_lt_mul_of_pos_left hg (Nat.mul_pos hm hpa)
    simp only [hj, hpm, not_true_eq_false, or_self]
    exact iff_false_intro hlt.ne
  · have hcop := ((hp.coprime_iff_not_dvd.mpr hpm).symm).pow_right j
    simp only [hcop.gcd_eq_one, mul_one, hpm, not_false_eq_true, or_true]

private theorem reduced_primePow_ne_of_lt {m p a j : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hja : j < a) :
    m ≠ (m * p ^ a) / Nat.gcd (m * p ^ a) (p ^ j) := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hg : Nat.gcd (m * p ^ a) (p ^ j) < p ^ a :=
    (Nat.gcd_le_right _ (pow_pos hp.pos j)).trans_lt (Nat.pow_lt_pow_right hp.one_lt hja)
  have hlt : m * Nat.gcd (m * p ^ a) (p ^ j) < m * p ^ a :=
    Nat.mul_lt_mul_of_pos_left hg hm
  intro h
  exact hlt.ne' ((reduced_conductor_eq_iff (Nat.mul_pos hm hpa) _).mp h)

/-- A mixed dilation entry follows one valuation chain, with an exact saturation condition. -/
theorem primeConductorDilationMean_prime_chain {m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (a : ℕ) (j : ℕ) :
    primeConductorDilationMean m (m * p ^ a) (p ^ j) =
      if a ≤ j ∧ (j = a ∨ ¬p ∣ m) then
        ((m * p ^ a).totient : ℝ) /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt ((m * p ^ a).totient : ℝ)) else 0 := by
  rw [primeConductorDilationMean_eq_reduced hm (Nat.mul_pos hm (pow_pos hp.pos a))]
  have hsel : m = (m * p ^ a) / Nat.gcd (m * p ^ a) (p ^ j) ↔
      a ≤ j ∧ (j = a ∨ ¬p ∣ m) := by
    by_cases haj : a ≤ j
    · have hj : j = a + (j - a) := by omega
      rw [hj, reduced_primeShift_eq_iff hm hp]
      omega
    · have hne := reduced_primePow_ne_of_lt hm hp (Nat.lt_of_not_ge haj)
      simp only [hne, haj, false_and]
  simp only [hsel]


private theorem gcd_primePower_stable {p l Q V j : ℕ}
    (hp : p.Prime) (hl : 0 < l) (hlQ : l ≤ Q) (hQ : Q < p ^ (V + 1)) (hVj : V ≤ j) :
    Nat.gcd l (p ^ j) = Nat.gcd l (p ^ V) := by
  obtain ⟨a, _haj, ha⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right l (p ^ j))
  have hpa : p ^ a ≤ l := by
    rw [← ha]
    exact Nat.gcd_le_left _ hl
  have haV : a ≤ V := by
    by_contra h
    have hVa : V + 1 ≤ a := by omega
    have hpow := Nat.pow_le_pow_right hp.pos hVa
    exact (hQ.trans_le (hpow.trans (hpa.trans hlQ))).false
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left l (p ^ j))
    rw [ha]
    exact pow_dvd_pow p haV
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left l (p ^ V))
      ((Nat.gcd_dvd_right l (p ^ V)).trans (pow_dvd_pow p hVj))

/-- Above the largest possible prime valuation, the complete dilation matrix is constant. -/
theorem primeConductorDilationMean_prime_power_stabilizes {Q m l p j : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hlQ : l ≤ Q) (hp : p.Prime) (hj : Nat.log p Q ≤ j) :
    primeConductorDilationMean m l (p ^ j) =
      primeConductorDilationMean m l (p ^ (Nat.log p Q)) := by
  rw [primeConductorDilationMean_eq_reduced hm hl,
    primeConductorDilationMean_eq_reduced hm hl,
    gcd_primePower_stable hp hl hlQ (Nat.lt_pow_succ_log_self hp.one_lt Q) hj]

private theorem log_primePower_cutoff_le {Q p : ℕ} (hQ : 0 < Q) (hp : p.Prime) :
    (Nat.log p Q : ℝ) * Real.log p ≤ Real.log Q := by
  have hlog := Real.log_le_log (show (0 : ℝ) < (p ^ (Nat.log p Q) : ℕ) by
      exact_mod_cast pow_pos hp.pos (Nat.log p Q))
    (show ((p ^ (Nat.log p Q) : ℕ) : ℝ) ≤ Q by exact_mod_cast Nat.pow_log_le_self p hQ.ne')
  simpa only [Nat.cast_pow, Real.log_pow] using hlog

/-- The total mass of primes capable of changing a conductor packet grows only logarithmically. -/
theorem sum_primeDilationMass_le_log {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) ≤
      14 * (1 + Real.log Q) := by
  have hterm (p : ℕ) (hp : p.Prime) :
      Real.log p / ((p : ℝ) - 1) ≤ 2 * (vonMangoldt p / (p : ℝ)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : 0 < (p : ℝ) - 1 := by linarith only [hp2]
    rw [vonMangoldt_apply_prime hp]
    calc
      _ ≤ (2 * Real.log p) / (p : ℝ) := by
        apply (div_le_div_iff₀ hp1 hp0).mpr
        have h := mul_nonneg (Real.log_natCast_nonneg p)
          (show 0 ≤ (p : ℝ) - 2 by linarith only [hp2])
        nlinarith only [h]
      _ = _ := by ring
  have hsum : (∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) ≤
      2 * mertensSum Q := by
    calc
      _ ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 2 * (vonMangoldt p / (p : ℝ)) :=
        sum_le_sum fun p hp => hterm p (mem_filter.mp hp).2
      _ ≤ ∑ p ∈ Icc 1 Q, 2 * (vonMangoldt p / (p : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ =>
          mul_nonneg (by norm_num) (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg p))
      _ = _ := by rw [← mul_sum]; rfl
  have hM := (abs_le.mp (_root_.RHTower.Mertens.mertens_first Q hQ)).2
  change mertensSum Q - Real.log Q ≤ Real.log 4 + 4 at hM
  have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
  linarith only [hsum, hM, hfour, Real.log_natCast_nonneg Q]

private theorem finite_geometric_moment (r : ℝ) (L : ℕ) :
    (1 - r) * (∑ i ∈ range L, (i : ℝ) * r ^ i) =
      r * (∑ i ∈ range L, r ^ i) - (L : ℝ) * r ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih,
      Nat.cast_add, Nat.cast_one, pow_succ]
    ring

private theorem finite_geometric_moment_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    (∑ i ∈ range L, (i : ℝ) * r ^ i) ≤
      r / (1 - r) * (∑ i ∈ range L, r ^ i) := by
  have h := finite_geometric_moment r L
  have hn : 0 ≤ (L : ℝ) * r ^ L := by positivity
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  calc
    _ ≤ (r * (∑ i ∈ range L, r ^ i)) / (1 - r) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [h, hn]
    _ = _ := by ring

private theorem prime_geometric_tail_log_mean {p : ℕ} (hp : p.Prime) (V L : ℕ) :
    (∑ i ∈ range L, ((V : ℝ) + i) * Real.log p * ((1 : ℝ) / p) ^ i) ≤
      ((V : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1)) *
        (∑ i ∈ range L, ((1 : ℝ) / p) ^ i) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith only [hpR]
  have hgeom := mul_le_mul_of_nonneg_left
    (finite_geometric_moment_le (by positivity : (0 : ℝ) ≤ 1 / p)
      ((div_lt_one (by positivity)).mpr hpR) L) (Real.log_natCast_nonneg p)
  have hratio : ((1 : ℝ) / p) / (1 - 1 / p) = 1 / ((p : ℝ) - 1) := by
    field_simp [hp0, hp1]
  rw [hratio] at hgeom
  calc
    _ = (V : ℝ) * Real.log p * (∑ i ∈ range L, ((1 : ℝ) / p) ^ i) +
        Real.log p * (∑ i ∈ range L, (i : ℝ) * ((1 : ℝ) / p) ^ i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ (V : ℝ) * Real.log p * (∑ i ∈ range L, ((1 : ℝ) / p) ^ i) +
        Real.log p * (1 / ((p : ℝ) - 1) * (∑ i ∈ range L, ((1 : ℝ) / p) ^ i)) :=
      add_le_add le_rfl hgeom
    _ = _ := by ring

private theorem saturated_primePower_logMoment_le {p V : ℕ} (hp : p.Prime) (hV : 1 ≤ V)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hstable : ∀ j, V ≤ j → b j = b V) (K : ℕ) :
    (∑ i ∈ range K, ((i + 1 : ℕ) : ℝ) * Real.log p *
      (Real.log p / (p : ℝ) ^ (i + 1) * b (i + 1))) ≤
      ((V : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1)) *
        (∑ i ∈ range K, Real.log p / (p : ℝ) ^ (i + 1) * b (i + 1)) := by
  let β : ℝ := (V : ℝ) * Real.log p + Real.log p / ((p : ℝ) - 1)
  -- The tail starts at the first saturated exponent.
  let d : ℕ := V - 1
  let r : ℝ := 1 / p
  let C : ℝ := Real.log p / (p : ℝ) ^ V * b V
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by linarith only [hpR]
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hC : 0 ≤ C := mul_nonneg (div_nonneg hlog (pow_nonneg (Nat.cast_nonneg p) V)) (hb V)
  have hβ : (V : ℝ) * Real.log p ≤ β :=
    le_add_of_nonneg_right (div_nonneg hlog hpden.le)
  have hhead (T : ℕ) (hT : T ≤ V) :
      (∑ i ∈ range T, ((i + 1 : ℕ) : ℝ) * Real.log p *
        (Real.log p / (p : ℝ) ^ (i + 1) * b (i + 1))) ≤
        β * (∑ i ∈ range T, Real.log p / (p : ℝ) ^ (i + 1) * b (i + 1)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hiV : ((i + 1 : ℕ) : ℝ) ≤ V := by
      exact_mod_cast (show i + 1 ≤ V by have := mem_range.mp hi; omega)
    have hcoef := (mul_le_mul_of_nonneg_right hiV hlog).trans hβ
    exact mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (div_nonneg hlog (pow_nonneg (Nat.cast_nonneg p) _)) (hb _))
  have hidx (i : ℕ) : d + i + 1 = V + i := by dsimp only [d]; omega
  have hweight (i : ℕ) : Real.log p / (p : ℝ) ^ (d + i + 1) * b (d + i + 1) = C * r ^ i := by
    rw [hidx, hstable (V + i) (by omega)]
    dsimp only [C, r]
    rw [pow_add, one_div_pow]
    ring
  have htail (T : ℕ) :
      (∑ i ∈ range T, ((d + i + 1 : ℕ) : ℝ) * Real.log p *
        (Real.log p / (p : ℝ) ^ (d + i + 1) * b (d + i + 1))) ≤
        β * (∑ i ∈ range T, Real.log p / (p : ℝ) ^ (d + i + 1) * b (d + i + 1)) := by
    have hleft : (∑ i ∈ range T, ((d + i + 1 : ℕ) : ℝ) * Real.log p *
        (Real.log p / (p : ℝ) ^ (d + i + 1) * b (d + i + 1))) =
        C * (∑ i ∈ range T, ((V : ℝ) + i) * Real.log p * r ^ i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [hweight, hidx, Nat.cast_add]
      ring
    have hright : (∑ i ∈ range T, Real.log p / (p : ℝ) ^ (d + i + 1) * b (d + i + 1)) =
        C * (∑ i ∈ range T, r ^ i) := by
      simp only [hweight, mul_sum]
    rw [hleft, hright]
    have h := mul_le_mul_of_nonneg_left (prime_geometric_tail_log_mean hp V T) hC
    change C * (∑ i ∈ range T, ((V : ℝ) + i) * Real.log p * r ^ i) ≤
      C * (β * (∑ i ∈ range T, r ^ i)) at h
    exact h.trans_eq (by ring)
  by_cases hK : K ≤ d
  · exact hhead K (hK.trans (Nat.sub_le V 1))
  · have hdK : d ≤ K := (Nat.lt_of_not_ge hK).le
    have hsplit : K = d + (K - d) := by omega
    rw [hsplit, Finset.sum_range_add, Finset.sum_range_add, mul_add]
    exact add_le_add (hhead d (Nat.sub_le V 1)) (htail (K - d))


private def dilationJumpMass (Q : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2

private theorem dilationJumpMass_nonneg (Q : ℕ) (a : ℕ → ℝ) (k : ℕ) :
    0 ≤ dilationJumpMass Q a k := sum_nonneg fun _ _ => sq_nonneg _

private theorem dilationJumpMass_one (Q : ℕ) (a : ℕ → ℝ) :
    dilationJumpMass Q a 1 = 0 := by
  have h := primeConductorDilationJump_period_sq Q a 1
  simp only [one_mul, sub_self, zero_pow (by norm_num : 2 ≠ 0), sum_const_zero, mul_zero] at h
  exact h.symm

private theorem dilationJumpMass_stable {Q p j : ℕ} (a : ℕ → ℝ)
    (hp : p.Prime) (hj : Nat.log p Q ≤ j) :
    dilationJumpMass Q a (p ^ j) = dilationJumpMass Q a (p ^ (Nat.log p Q)) := by
  apply sum_congr rfl
  intro m hm
  congr 1
  dsimp only [primeConductorDilationJump]
  congr 1
  apply sum_congr rfl
  intro l hl
  rw [primeConductorDilationMean_prime_power_stabilizes
    (mem_Icc.mp hm).1 (mem_Icc.mp hl).1 (mem_Icc.mp hl).2 hp hj]

private theorem dilationJumpMass_large_prime {Q p : ℕ} (a : ℕ → ℝ)
    (hp : p.Prime) (hQp : Q < p) (j : ℕ) : dilationJumpMass Q a (p ^ j) = 0 := by
  have hlog : Nat.log p Q = 0 := Nat.log_of_lt hQp
  rw [dilationJumpMass_stable a hp (by rw [hlog]; exact Nat.zero_le j),
    hlog, pow_zero, dilationJumpMass_one]

/-- Primes larger than the conductor cutoff act trivially on every packet coefficient. -/
theorem primeConductorDilationJump_eq_zero_of_prime_gt {Q p m : ℕ}
    (a : ℕ → ℝ) (hp : p.Prime) (hQp : Q < p) (hm : m ∈ Icc 1 Q) (j : ℕ) :
    primeConductorDilationJump Q a (p ^ j) m = 0 := by
  have hsq : primeConductorDilationJump Q a (p ^ j) m ^ 2 ≤ 0 := by
    calc
      _ ≤ ∑ l ∈ Icc 1 Q, primeConductorDilationJump Q a (p ^ j) l ^ 2 :=
        single_le_sum (fun l _ => sq_nonneg _) hm
      _ = 0 := dilationJumpMass_large_prime a hp hQp j
  exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))

private def primePowerBox (Q K : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q).filter Nat.Prime) ×ˢ range K

private theorem primePowerBox_inj (Q K : ℕ) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 ^ (x.2 + 1)) (primePowerBox Q K) := by
  intro x hx y hy hxy
  have hpx := (mem_filter.mp (mem_product.mp hx).1).2
  have hpy := (mem_filter.mp (mem_product.mp hy).1).2
  obtain ⟨hp, hj⟩ := Nat.Prime.pow_inj hpx hpy hxy
  exact Prod.ext hp (by omega)

private theorem sum_primePowerBox (Q K : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ (primePowerBox Q K).image (fun x => x.1 ^ (x.2 + 1)), f k) =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ i ∈ range K, f (p ^ (i + 1)) := by
  rw [sum_image (primePowerBox_inj Q K), primePowerBox, sum_product]

private theorem sum_primePowerBox_energy_le (Q K : ℕ) (a : ℕ → ℝ) :
    (∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ i ∈ range K,
      Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1))) ≤
      ∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2 := by
  have h := hasSum_primeConductorDilationJump_sq Q a
  change HasSum (fun k : ℕ => vonMangoldt k / (k : ℝ) * dilationJumpMass Q a k)
    (∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2) at h
  have hs := h.summable.sum_le_tsum
    ((primePowerBox Q K).image (fun x => x.1 ^ (x.2 + 1)))
    (fun k _ => mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      (dilationJumpMass_nonneg Q a k))
  rw [h.tsum_eq] at hs
  change (∑ k ∈ (primePowerBox Q K).image (fun x => x.1 ^ (x.2 + 1)),
    vonMangoldt k / (k : ℝ) * dilationJumpMass Q a k) ≤ _ at hs
  rw [sum_primePowerBox] at hs
  have he : (∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ i ∈ range K,
      vonMangoldt (p ^ (i + 1)) / ((p ^ (i + 1) : ℕ) : ℝ) *
        dilationJumpMass Q a (p ^ (i + 1))) =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ i ∈ range K,
        Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1)) := by
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro i _
    rw [vonMangoldt_prime_pow (mem_filter.mp hp).2 (Nat.succ_pos i), Nat.cast_pow]
  rwa [he] at hs

private theorem sum_primePowerBox_logMoment_le {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (K : ℕ) :
    (∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ i ∈ range K,
      Real.log (p ^ (i + 1) : ℕ) *
        (Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1)))) ≤
      (1 + Real.log Q) *
        ∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2 := by
  have hprime (p : ℕ) (hpQ : p ∈ (Icc 1 Q).filter Nat.Prime) :
      (∑ i ∈ range K, Real.log (p ^ (i + 1) : ℕ) *
        (Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1)))) ≤
        (1 + Real.log Q) * (∑ i ∈ range K,
          Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1))) := by
    have hp := (mem_filter.mp hpQ).2
    have hp_le_Q := (mem_Icc.mp (mem_filter.mp hpQ).1).2
    have hV : 1 ≤ Nat.log p Q := Nat.log_pos hp.one_lt hp_le_Q
    have hsat := saturated_primePower_logMoment_le hp hV
      (fun j => dilationJumpMass Q a (p ^ j))
      (fun j => dilationJumpMass_nonneg Q a (p ^ j))
      (fun j hj => dilationJumpMass_stable a hp hj) K
    have htau : Real.log p / ((p : ℝ) - 1) ≤ 1 := by
      have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      apply (div_le_one (sub_pos.mpr hpR)).mpr
      exact Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hpR)
    have hcoef : (Nat.log p Q : ℝ) * Real.log p +
        Real.log p / ((p : ℝ) - 1) ≤ 1 + Real.log Q := by
      linarith only [log_primePower_cutoff_le hQ hp, htau]
    calc
      _ = ∑ i ∈ range K, ((i + 1 : ℕ) : ℝ) * Real.log p *
          (Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1))) := by
        simp only [Nat.cast_pow, Real.log_pow]
      _ ≤ _ := hsat
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef
        (sum_nonneg fun i _ => mul_nonneg
          (div_nonneg (Real.log_natCast_nonneg p) (pow_nonneg (Nat.cast_nonneg p) _))
          (dilationJumpMass_nonneg Q a _))
  calc
    _ ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        (1 + Real.log Q) * (∑ i ∈ range K,
          Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1))) :=
      sum_le_sum hprime
    _ = (1 + Real.log Q) * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ i ∈ range K,
        Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1))) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_primePowerBox_energy_le Q K a)
      (by linarith only [Real.log_natCast_nonneg Q])

/-- Every finite prime cutoff has logarithmic dilation energy at most `1 + log Q` times adjunction. -/
theorem sum_primeConductorDilationJump_logMoment_le {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Icc 1 K, vonMangoldt k * Real.log k / (k : ℝ) *
      (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2)) ≤
      (1 + Real.log Q) * ∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2 := by
  let f : ℕ → ℝ := fun k => vonMangoldt k * Real.log k / (k : ℝ) * dilationJumpMass Q a k
  let S := (Icc 1 K).filter (fun k => vonMangoldt k ≠ 0 ∧ dilationJumpMass Q a k ≠ 0)
  have hf (k : ℕ) : 0 ≤ f k := mul_nonneg
    (div_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg k)) (Nat.cast_nonneg k))
    (dilationJumpMass_nonneg Q a k)
  have hfilter : (∑ k ∈ Icc 1 K, f k) = ∑ k ∈ S, f k := by
    apply (sum_filter_of_ne (fun k _ hk => ?_)).symm
    constructor
    · intro hz
      apply hk
      dsimp only [f]
      rw [hz, zero_mul, zero_div, zero_mul]
    · intro hz
      apply hk
      dsimp only [f]
      rw [hz, mul_zero]
  -- Each nonzero Mangoldt atom has one prime and one positive exponent.
  have hsub : S ⊆ (primePowerBox Q K).image (fun x => x.1 ^ (x.2 + 1)) := by
    intro k hk
    obtain ⟨hkK, hΛ, hb⟩ := mem_filter.mp hk
    have hpp : IsPrimePow k := by
      by_contra h
      exact hΛ (vonMangoldt_eq_zero_iff.mpr h)
    obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpQ : p ≤ Q := by
      by_contra h
      exact hb (dilationJumpMass_large_prime a hp (Nat.lt_of_not_ge h) j)
    have hjK : j ≤ K := (Nat.lt_pow_self hp.one_lt).le.trans (mem_Icc.mp hkK).2
    refine mem_image.mpr ⟨(p, j - 1), ?_, ?_⟩
    · exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos, hpQ⟩, hp⟩,
        mem_range.mpr (by omega)⟩
    · simp only [Nat.sub_add_cancel hj]
  change (∑ k ∈ Icc 1 K, f k) ≤ _
  calc
    _ = ∑ k ∈ S, f k := hfilter
    _ ≤ ∑ k ∈ (primePowerBox Q K).image (fun x => x.1 ^ (x.2 + 1)), f k :=
      sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hf k
    _ = ∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ i ∈ range K,
        Real.log (p ^ (i + 1) : ℕ) *
          (Real.log p / (p : ℝ) ^ (i + 1) * dilationJumpMass Q a (p ^ (i + 1))) := by
      rw [sum_primePowerBox]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro i _
      dsimp only [f]
      rw [vonMangoldt_prime_pow (mem_filter.mp hp).2 (Nat.succ_pos i), Nat.cast_pow]
      ring
    _ ≤ _ := sum_primePowerBox_logMoment_le hQ a K


private theorem sum_finset_primeDilation_logMoment_le {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (S : Finset ℕ) :
    (∑ k ∈ S, vonMangoldt k * Real.log k / (k : ℝ) *
      (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2)) ≤
      (1 + Real.log Q) * ∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2 := by
  have hsub : S ⊆ insert 0 (Icc 1 (S.sup id)) := by
    intro k hk
    by_cases hk0 : k = 0
    · exact mem_insert.mpr (Or.inl hk0)
    · exact mem_insert.mpr (Or.inr (mem_Icc.mpr
        ⟨Nat.pos_of_ne_zero hk0, Finset.le_sup (f := id) hk⟩))
  calc
    _ ≤ ∑ k ∈ insert 0 (Icc 1 (S.sup id)), vonMangoldt k * Real.log k / (k : ℝ) *
        (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) :=
      sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
        mul_nonneg (div_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg k))
          (Nat.cast_nonneg k)) (sum_nonneg fun _ _ => sq_nonneg _)
    _ = ∑ k ∈ Icc 1 (S.sup id), vonMangoldt k * Real.log k / (k : ℝ) *
        (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) := by
      rw [sum_insert (by simp)]
      simp only [Nat.cast_zero, div_zero, zero_mul, zero_add]
    _ ≤ _ := sum_primeConductorDilationJump_logMoment_le hQ a (S.sup id)

/-- The first logarithmic moment of the full prime-dilation square energy is summable. -/
theorem summable_primeConductorDilationJump_logMoment {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) :
    Summable (fun k : ℕ => vonMangoldt k * Real.log k / (k : ℝ) *
      (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2)) :=
  summable_of_sum_le (fun k =>
    mul_nonneg (div_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg k))
      (Nat.cast_nonneg k)) (sum_nonneg fun _ _ => sq_nonneg _))
    (sum_finset_primeDilation_logMoment_le hQ a)

/-- The complete logarithmic moment costs at most `1 + log Q` times the exact adjunction energy. -/
theorem tsum_primeConductorDilationJump_logMoment_le {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) :
    (∑' k : ℕ, vonMangoldt k * Real.log k / (k : ℝ) *
      (∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2)) ≤
      (1 + Real.log Q) * ∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2 :=
  Real.tsum_le_of_sum_le (fun k =>
    mul_nonneg (div_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg k))
      (Nat.cast_nonneg k)) (sum_nonneg fun _ _ => sq_nonneg _))
    (sum_finset_primeDilation_logMoment_le hQ a)

#print axioms primeConductorDilationMean_self_prime_pow
#print axioms hasSum_localMangoldt_logMoment
#print axioms localMangoldt_logMoment_le
#print axioms primeConductorDilationMean_prime_chain
#print axioms primeConductorDilationMean_prime_power_stabilizes
#print axioms sum_primeDilationMass_le_log
#print axioms primeConductorDilationJump_eq_zero_of_prime_gt
#print axioms sum_primeConductorDilationJump_logMoment_le
#print axioms summable_primeConductorDilationJump_logMoment
#print axioms tsum_primeConductorDilationJump_logMoment_le

end
end GaloisForLFunctions.SuccessorShellArithmetic
