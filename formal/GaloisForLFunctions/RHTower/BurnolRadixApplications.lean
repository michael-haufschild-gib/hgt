import GaloisForLFunctions.RHTower.DQPTBernoulliBound
import GaloisForLFunctions.RHTower.GeometricMomentRational
import GaloisForLFunctions.HTGeometry.OnsiteEnergySeparation

/-!
# Burnol radix-moment applications

Unconditional finite and formal-series forms of identities from arXiv:2602.05511,
arXiv:2404.13763, arXiv:2601.23158, and arXiv:2603.29998, connected to the
corpus's Bernoulli recurrence and finite radix-word energy coordinates.
-/

namespace RHTower.Burnol

open Finset

noncomputable section

theorem bernoulli_Icc_sum_eq_neg_one {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 m, ((m + 1).choose k : ℚ) * bernoulli k = -1 := by
  have h := RHTower.DQPT.dqpt_bernoulli_recurrence (q := m) hm
  have hzero : 0 ∈ Finset.range (m + 1) := by simp
  have herase : (Finset.range (m + 1)).erase 0 = Finset.Icc 1 m := by
    ext k
    simp
    omega
  rw [← Finset.sum_erase_add _ _ hzero, herase] at h
  norm_num [bernoulli_zero] at h ⊢
  linarith

theorem bernoulli_range_sum_eq_zero (m : ℕ) :
    ∑ k ∈ Finset.range (m + 2), ((m + 2).choose k : ℚ) * bernoulli k = 0 := by
  exact RHTower.DQPT.dqpt_bernoulli_recurrence
    (q := m + 1) (Nat.succ_le_succ (Nat.zero_le m))

/-- Equation (1) of arXiv:2602.05511 at radix `b+2` and integer exponent `s+2`. -/
def zetaMomentCoefficient (b s m : ℕ) : ℚ :=
  1 / (m + 1 : ℚ) * ∑ j ∈ Finset.range (m + 1),
    ((m + 1).choose j : ℚ) * bernoulli j *
      ((b + 2 : ℚ) ^ (s + 2 + j) / ((b + 2 : ℚ) ^ (s + 2 + j) - (b + 2 : ℚ)))

/-- Equation (9) of arXiv:2602.05511, with constant numerator. -/
def zetaMomentCoefficientReduced (b s m : ℕ) : ℚ :=
  1 / (m + 1 : ℚ) * ∑ j ∈ Finset.range (m + 1),
    ((m + 1).choose j : ℚ) * bernoulli j *
      ((b + 2 : ℚ) / ((b + 2 : ℚ) ^ (s + 2 + j) - (b + 2 : ℚ)))

theorem zetaMomentCoefficient_eq_reduced (b s m : ℕ) :
    zetaMomentCoefficient b s (m + 1) = zetaMomentCoefficientReduced b s (m + 1) := by
  have hterm : ∀ j ∈ Finset.range (m + 2),
      (((m + 2).choose j : ℚ) * bernoulli j *
          ((b + 2 : ℚ) ^ (s + 2 + j) /
            ((b + 2 : ℚ) ^ (s + 2 + j) - (b + 2 : ℚ)))) =
        ((m + 2).choose j : ℚ) * bernoulli j *
            ((b + 2 : ℚ) /
              ((b + 2 : ℚ) ^ (s + 2 + j) - (b + 2 : ℚ))) +
          ((m + 2).choose j : ℚ) * bernoulli j := by
    intro j hj
    have hbase : (1 : ℚ) < (b + 2 : ℚ) := by
      exact_mod_cast (show 1 < b + 2 by omega)
    have htail : (1 : ℚ) < (b + 2 : ℚ) ^ (s + 1 + j) :=
      one_lt_pow₀ hbase (by omega)
    have hpow : (b + 2 : ℚ) < (b + 2 : ℚ) ^ (s + 2 + j) := by
      calc
        (b + 2 : ℚ) = (b + 2 : ℚ) * 1 := by ring
        _ < (b + 2 : ℚ) * (b + 2 : ℚ) ^ (s + 1 + j) :=
          mul_lt_mul_of_pos_left htail (by positivity)
        _ = (b + 2 : ℚ) ^ (s + 2 + j) := by
          rw [show s + 2 + j = (s + 1 + j) + 1 by omega, pow_succ]
          ring
    have hden : (b + 2 : ℚ) ^ (s + 2 + j) - (b + 2 : ℚ) ≠ 0 := by
      linarith
    field_simp
    ring
  rw [zetaMomentCoefficient, zetaMomentCoefficientReduced]
  simp only [show m + 1 + 1 = m + 2 by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    bernoulli_range_sum_eq_zero]
  ring

/-- A denominator kernel in arXiv:2602.05511 is the corpus's zeroth geometric moment. -/
theorem zetaKernel_eq_geomMoment_zero (b s j : ℕ) :
    (b + 2 : ℝ) ^ (s + 2 + j) /
        ((b + 2 : ℝ) ^ (s + 2 + j) - (b + 2 : ℝ)) =
      RHTower.geomMoment (1 / (b + 2 : ℝ) ^ (s + 1 + j)) 0 := by
  have hbase : (1 : ℝ) < (b + 2 : ℝ) := by
    exact_mod_cast (show 1 < b + 2 by omega)
  have hpow : (1 : ℝ) < (b + 2 : ℝ) ^ (s + 1 + j) :=
    one_lt_pow₀ hbase (by omega)
  have hratio : |1 / (b + 2 : ℝ) ^ (s + 1 + j)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    exact hpow
  rw [RHTower.geomMoment_zero hratio]
  have hden : (b + 2 : ℝ) ^ (s + 1 + j) - 1 ≠ 0 := by linarith
  rw [show s + 2 + j = (s + 1 + j) + 1 by omega, pow_succ]
  field_simp

/-- All odd Bernoulli summands beyond `B₁` vanish in Equation (9). -/
theorem zetaReduced_odd_term_zero (b s m k : ℕ) :
    ((m + 1).choose (2 * k + 3) : ℚ) * bernoulli (2 * k + 3) *
      ((b + 2 : ℚ) /
        ((b + 2 : ℚ) ^ (s + 2 + (2 * k + 3)) - (b + 2 : ℚ))) = 0 := by
  have hodd : Odd (2 * k + 3) := by
    refine ⟨k + 1, ?_⟩
    omega
  rw [bernoulli_eq_zero_of_odd hodd (by omega)]
  ring

/-- Bernoulli closed form for leader-election generating function, regularized at `z = 1`. -/
def leaderGenerating (m : ℕ) (z : ℚ) : ℚ :=
  1 + ∑ k ∈ Finset.Icc 1 m, ((m + 1).choose k : ℚ) *
    ((2 : ℚ) ^ k * (1 - z) * bernoulli k / ((2 : ℚ) ^ k - z))

theorem leaderGenerating_one (m : ℕ) : leaderGenerating m 1 = 1 := by
  simp [leaderGenerating]

theorem leaderGenerating_zero (m : ℕ) : leaderGenerating (m + 1) 0 = 0 := by
  have hsum := bernoulli_Icc_sum_eq_neg_one (m := m + 1) (by omega)
  rw [leaderGenerating]
  simp only [sub_zero]
  have hterm : ∀ k ∈ Finset.Icc 1 (m + 1),
      (((m + 1 + 1).choose k : ℚ) *
          ((2 : ℚ) ^ k * 1 * bernoulli k / (2 : ℚ) ^ k)) =
        ((m + 1 + 1).choose k : ℚ) * bernoulli k := by
    intro k hk
    field_simp
  rw [Finset.sum_congr rfl hterm, hsum]
  ring

def eWeight (k : ℕ) : ℚ :=
  bernoulli k * (2 : ℚ) ^ k / ((2 : ℚ) ^ k - 1)

theorem eWeight_odd_succ_succ_zero (k : ℕ) : eWeight (2 * k + 3) = 0 := by
  have hodd : Odd (2 * k + 3) := by
    refine ⟨k + 1, ?_⟩
    omega
  rw [eWeight, bernoulli_eq_zero_of_odd hodd (by omega)]
  ring

def eCoeff (m : ℕ) : ℚ :=
  -∑ k ∈ Finset.Icc 1 m,
    ((m + 1).choose k : ℚ) * eWeight k

def eCoeffUnit (m : ℕ) : ℚ :=
  1 - ∑ k ∈ Finset.Icc 1 m,
    ((m + 1).choose k : ℚ) * bernoulli k / ((2 : ℚ) ^ k - 1)

theorem eCoeff_eq_eCoeffUnit {m : ℕ} (hm : 1 ≤ m) : eCoeff m = eCoeffUnit m := by
  have hsum := bernoulli_Icc_sum_eq_neg_one hm
  have hterm : ∀ k ∈ Finset.Icc 1 m,
      ((m + 1).choose k : ℚ) * eWeight k
        = ((m + 1).choose k : ℚ) * bernoulli k
          + ((m + 1).choose k : ℚ) * bernoulli k / ((2 : ℚ) ^ k - 1) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hden : (2 : ℚ) ^ k - 1 ≠ 0 := by
      have hp : (1 : ℚ) < (2 : ℚ) ^ k := by
        exact one_lt_pow₀ (by norm_num) (by omega)
      linarith
    rw [eWeight]
    field_simp
    ring
  rw [eCoeff, eCoeffUnit, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, hsum]
  ring

theorem eCoeff_eq_eCoeffUnit_succ (m : ℕ) : eCoeff (m + 1) = eCoeffUnit (m + 1) := by
  exact eCoeff_eq_eCoeffUnit (by omega)

theorem choose_exchange (n j k : ℕ) :
    n.choose j * (n - j).choose k = n.choose k * (n - k).choose j := by
  have h1 := Nat.choose_mul (n := n) (k := j + k) (s := j) (by omega)
  have h2 := Nat.choose_mul (n := n) (k := j + k) (s := k) (by omega)
  calc
    n.choose j * (n - j).choose k = n.choose (j + k) * (j + k).choose j := by
      simpa using h1.symm
    _ = n.choose (j + k) * (j + k).choose k := by
      rw [Nat.choose_symm_add]
    _ = n.choose k * (n - k).choose j := by
      simpa [Nat.add_comm] using h2

theorem Icc_sub_eq_filter (m j : ℕ) (_hj : j ∈ Finset.Icc 1 m) :
    Finset.Icc 1 (m - j) = (Finset.Icc 1 m).filter (fun k => j + k ≤ m) := by
  ext k
  simp
  constructor <;> omega

def cOne (m : ℕ) : ℚ := 1 / (m + 1 : ℚ)

theorem cOne_zero : cOne 0 = 1 := by norm_num [cOne]

theorem choose_mul_cOne_sub {m j : ℕ} (hj : j ≤ m) :
    (m.choose j : ℚ) * cOne (m - j) = ((m + 1).choose j : ℚ) / (m + 1 : ℚ) := by
  have hsub : m + 1 - j = m - j + 1 := by omega
  have hnat := Nat.choose_mul_succ_eq m j
  rw [hsub] at hnat
  rw [cOne]
  have hden1 : (m - j + 1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (m - j)
  have hden2 : (m + 1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  field_simp
  have hrat : (m.choose j : ℚ) * (m + 1 : ℚ) =
      ((m + 1).choose j : ℚ) * (m - j + 1 : ℚ) := by
    exact_mod_cast hnat
  simpa [Nat.cast_sub hj, mul_comm] using hrat

theorem sum_Icc_choose_eq (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (m + 1).choose j = 2 ^ (m + 1) - 2 := by
  have h := Nat.sum_range_choose (m + 1)
  rw [Finset.sum_range_succ, Nat.choose_self] at h
  have hzero : 0 ∈ Finset.range (m + 1) := by simp
  have herase : (Finset.range (m + 1)).erase 0 = Finset.Icc 1 m := by
    ext j
    simp
    omega
  rw [← Finset.sum_erase_add _ _ hzero, herase] at h
  norm_num at h ⊢
  omega

theorem binomial_lower_convolution (q : ℕ → ℚ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, ((m + 1).choose j : ℚ) *
        (∑ k ∈ Finset.Icc 1 (m - j), ((m - j + 1).choose k : ℚ) * q k) =
      ∑ k ∈ Finset.Icc 1 m, ((m + 1).choose k : ℚ) *
        ((2 : ℚ) ^ (m + 1 - k) - 2) * q k := by
  classical
  calc
    _ = ∑ j ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 m,
          if j + k ≤ m then
            ((m + 1).choose j : ℚ) * ((m - j + 1).choose k : ℚ) * q k
          else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Icc_sub_eq_filter m j hj, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hjk : j + k ≤ m <;> simp [hjk, mul_assoc]
    _ = ∑ k ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 m,
          if j + k ≤ m then
            ((m + 1).choose j : ℚ) * ((m - j + 1).choose k : ℚ) * q k
          else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.Icc 1 m).filter (fun j => j + k ≤ m) = Finset.Icc 1 (m - k) := by
        rw [Icc_sub_eq_filter m k hk]
        ext j
        simp [Nat.add_comm]
      rw [hfilter, ← Finset.sum_mul]
      have hchoose : ∀ j ∈ Finset.Icc 1 (m - k),
          ((m + 1).choose j : ℚ) * ((m - j + 1).choose k : ℚ) =
            ((m + 1).choose k : ℚ) * ((m + 1 - k).choose j : ℚ) := by
        intro j hj
        have hjm : j ≤ m := by
          have hk0 : k ≤ m := (Finset.mem_Icc.mp hk).2
          exact le_trans (Finset.mem_Icc.mp hj).2 (Nat.sub_le m k)
        have hn := choose_exchange (m + 1) j k
        have hsub : m + 1 - j = m - j + 1 := by omega
        rw [hsub] at hn
        exact_mod_cast hn
      rw [Finset.sum_congr rfl hchoose]
      rw [← Finset.mul_sum]
      have hsum := sum_Icc_choose_eq (m - k)
      have hsumQ :
          ∑ j ∈ Finset.Icc 1 (m - k), ((m + 1 - k).choose j : ℚ) =
            (2 : ℚ) ^ (m + 1 - k) - 2 := by
        have hk0 : k ≤ m := (Finset.mem_Icc.mp hk).2
        have hidx : m - k + 1 = m + 1 - k := by omega
        rw [hidx] at hsum
        have hpow : 2 ≤ 2 ^ (m + 1 - k) := by
          have hk1 : 1 ≤ m + 1 - k := by omega
          have hgt : 1 < (2 : ℕ) ^ (m + 1 - k) :=
            one_lt_pow₀ (by omega) (by omega)
          omega
        have hcast := congrArg (fun n : ℕ => (n : ℚ)) hsum
        push_cast [Nat.cast_sub hpow] at hcast
        exact hcast
      rw [hsumQ]

theorem cOne_recurrence (m : ℕ) :
    ((2 : ℚ) ^ (m + 1) - 2) * cOne m =
      ∑ j ∈ Finset.Icc 1 m, (m.choose j : ℚ) * cOne (m - j) := by
  have hterm : ∀ j ∈ Finset.Icc 1 m,
      (m.choose j : ℚ) * cOne (m - j) = ((m + 1).choose j : ℚ) / (m + 1 : ℚ) := by
    intro j hj
    exact choose_mul_cOne_sub (Finset.mem_Icc.mp hj).2
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hsum := sum_Icc_choose_eq m
  have hsumQ : ∑ j ∈ Finset.Icc 1 m, ((m + 1).choose j : ℚ) =
      (2 : ℚ) ^ (m + 1) - 2 := by
    have hpow : 2 ≤ 2 ^ (m + 1) := by
      have hmono := pow_right_mono₀ (by simp : 1 ≤ (2 : ℕ))
        (Nat.le_add_left 1 m : 1 ≤ m + 1)
      simpa using hmono
    have hcast := congrArg (fun n : ℕ => (n : ℚ)) hsum
    push_cast [Nat.cast_sub hpow] at hcast
    exact hcast
  rw [hsumQ, cOne]
  ring

/-- Equation (17) of arXiv:2404.13763: the cancellation driving complementary moments. -/
theorem weighted_binomial_antiderivative (b x : ℚ) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * b * x ^ j / (m - j + 1 : ℚ) =
      b / (m + 1 : ℚ) * ((x + 1) ^ (m + 1) - x ^ (m + 1)) := by
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (m.choose j : ℚ) * b * x ^ j / (m - j + 1 : ℚ) =
        b / (m + 1 : ℚ) * (((m + 1).choose j : ℚ) * x ^ j) := by
    intro j hj
    have hjm : j ≤ m := by simpa using (Finset.mem_range.mp hj)
    have h := choose_mul_cOne_sub hjm
    rw [cOne] at h
    push_cast [Nat.cast_sub hjm] at h
    calc
      (m.choose j : ℚ) * b * x ^ j / (m - j + 1 : ℚ) =
          b * x ^ j * ((m.choose j : ℚ) * (1 / (m - j + 1 : ℚ))) := by ring
      _ = b * x ^ j * (((m + 1).choose j : ℚ) / (m + 1 : ℚ)) := by rw [h]
      _ = b / (m + 1 : ℚ) * (((m + 1).choose j : ℚ) * x ^ j) := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbin := add_pow x 1 (m + 1)
  rw [Finset.sum_range_succ] at hbin
  simp only [one_pow, mul_one, Nat.choose_self] at hbin
  norm_num at hbin
  have hsum :
      ∑ j ∈ Finset.range (m + 1), ((m + 1).choose j : ℚ) * x ^ j =
        (x + 1) ^ (m + 1) - x ^ (m + 1) := by
    calc
      _ = ∑ j ∈ Finset.range (m + 1), x ^ j * ((m + 1).choose j : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by linarith
  rw [hsum]

/-- Equation (18) of arXiv:2404.13763: summing the discrete antiderivative over all digits. -/
theorem digit_weighted_binomial_cancellation (b m : ℕ) :
    ∑ a : Fin b, ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * b * (a : ℚ) ^ j / (m - j + 1 : ℚ) =
      (b : ℚ) / (m + 1 : ℚ) * (b : ℚ) ^ (m + 1) := by
  have hterm : ∀ a : Fin b,
      (∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℚ) * b * (a : ℚ) ^ j / (m - j + 1 : ℚ)) =
        (b : ℚ) / (m + 1 : ℚ) *
          (((a : ℚ) + 1) ^ (m + 1) - (a : ℚ) ^ (m + 1)) := by
    intro a
    exact weighted_binomial_antiderivative b a m
  rw [Finset.sum_congr rfl (fun a ha => hterm a), ← Finset.mul_sum]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun a : ℕ => ((a : ℚ) + 1) ^ (m + 1) - (a : ℚ) ^ (m + 1)) b
  rw [hfin]
  have htel := Finset.sum_range_sub (fun a : ℕ => (a : ℚ) ^ (m + 1)) b
  norm_num at htel
  simpa only [Finset.sum_sub_distrib, Nat.cast_add, Nat.cast_one] using
    congrArg ((b : ℚ) / (m + 1 : ℚ) * ·) htel

def uniformMoment (b m : ℕ) : ℚ := (b : ℚ) / (m + 1 : ℚ)

/-- Uniform moments are an exact fixed point of the full radix transfer.
This is the cancellation behind complementary moments in arXiv:2404.13763. -/
theorem uniformMoment_fullRadix_fixed (b m : ℕ) :
    (b : ℚ) ^ (m + 1) * uniformMoment b m =
      ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * (∑ a : Fin b, (a : ℚ) ^ j) * uniformMoment b (m - j) := by
  have h := digit_weighted_binomial_cancellation b m
  rw [uniformMoment]
  calc
    (b : ℚ) ^ (m + 1) * ((b : ℚ) / (m + 1 : ℚ)) =
        ∑ a : Fin b, ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℚ) * b * (a : ℚ) ^ j / (m - j + 1 : ℚ) := by
      rw [h]
      ring
    _ = ∑ j ∈ Finset.range (m + 1), ∑ a : Fin b,
          (m.choose j : ℚ) * b * (a : ℚ) ^ j / (m - j + 1 : ℚ) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℚ) * (∑ a : Fin b, (a : ℚ) ^ j) *
            ((b : ℚ) / (m - j + 1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ a : Fin b, (m.choose j : ℚ) * b * (a : ℚ) ^ j /
            (m - j + 1 : ℚ)) =
            ∑ a : Fin b, ((m.choose j : ℚ) * b / (m - j + 1 : ℚ)) * (a : ℚ) ^ j := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = ((m.choose j : ℚ) * b / (m - j + 1 : ℚ)) *
            (∑ a : Fin b, (a : ℚ) ^ j) := by rw [Finset.mul_sum]
        _ = _ := by ring
    _ = _ := by
      simp only [uniformMoment]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := by simpa using Finset.mem_range.mp hj
      rw [Nat.cast_sub hjm]

/-! ## Bernoulli discrete antiderivatives and oscillation polynomials -/

/-- Polynomial discrete antiderivative normalized to vanish at zero. -/
def discreteAntiderivative (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ n ∈ Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff n / (n + 1 : ℚ)) *
      (Polynomial.bernoulli (n + 1) - Polynomial.C (bernoulli (n + 1)))

theorem discreteAntiderivative_eval_zero (p : Polynomial ℚ) :
    (discreteAntiderivative p).eval 0 = 0 := by
  rw [discreteAntiderivative, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro n hn
  simp [Polynomial.bernoulli_eval_zero]

theorem discreteAntiderivative_eval_add_one_sub (p : Polynomial ℚ) (x : ℚ) :
    (discreteAntiderivative p).eval (x + 1) - (discreteAntiderivative p).eval x = p.eval x := by
  rw [discreteAntiderivative, Polynomial.eval_finsetSum, Polynomial.eval_finsetSum,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.range (p.natDegree + 1),
      (Polynomial.C (p.coeff n / (n + 1 : ℚ)) *
          (Polynomial.bernoulli (n + 1) - Polynomial.C (bernoulli (n + 1)))).eval (x + 1) -
        (Polynomial.C (p.coeff n / (n + 1 : ℚ)) *
          (Polynomial.bernoulli (n + 1) - Polynomial.C (bernoulli (n + 1)))).eval x =
        p.coeff n * x ^ n := by
    intro n hn
    have hbern := Polynomial.bernoulli_eval_one_add (n + 1) x
    rw [show x + 1 = 1 + x by ring]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    rw [hbern]
    have hden : (n + 1 : ℚ) ≠ 0 := by positivity
    field_simp
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  rw [Finset.sum_congr rfl hterm]
  exact (Polynomial.eval_eq_sum_range x).symm

theorem discreteAntiderivative_comp_add_one_sub (p : Polynomial ℚ) :
    (discreteAntiderivative p).comp (Polynomial.X + 1) - discreteAntiderivative p = p := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  exact discreteAntiderivative_eval_add_one_sub p x

/-- Polynomials `P_{j,a}` from Theorem 3 of arXiv:2603.29998. -/
def oscillationPolynomial (a : ℚ) : ℕ → Polynomial ℚ
  | 0 => 1
  | j + 1 =>
      -discreteAntiderivative
        ((Polynomial.X + Polynomial.C a) *
          (oscillationPolynomial a j).comp (Polynomial.X + 1))

theorem oscillationPolynomial_zero (a : ℚ) : oscillationPolynomial a 0 = 1 := rfl

theorem oscillationPolynomial_succ_eval_zero (a : ℚ) (j : ℕ) :
    (oscillationPolynomial a (j + 1)).eval 0 = 0 := by
  rw [oscillationPolynomial]
  simp [discreteAntiderivative_eval_zero]

theorem oscillationPolynomial_recurrence (a : ℚ) (j : ℕ) (t : ℚ) :
    (oscillationPolynomial a (j + 1)).eval (t + 1) -
        (oscillationPolynomial a (j + 1)).eval t =
      -(t + a) * (oscillationPolynomial a j).eval (t + 1) := by
  rw [oscillationPolynomial]
  simp only [Polynomial.eval_neg]
  have h := discreteAntiderivative_eval_add_one_sub
    ((Polynomial.X + Polynomial.C a) *
      (oscillationPolynomial a j).comp (Polynomial.X + 1)) t
  have hq :
      (((Polynomial.X + Polynomial.C a) *
        (oscillationPolynomial a j).comp (Polynomial.X + 1)).eval t) =
          (t + a) * (oscillationPolynomial a j).eval (t + 1) := by
    simp [Polynomial.eval_comp]
  rw [hq] at h
  linear_combination -h

/-- Polynomial identity behind Theorem 3 of arXiv:2603.29998, hence stable under scalar extension. -/
theorem oscillationPolynomial_polynomial_recurrence (a : ℚ) (j : ℕ) :
    (oscillationPolynomial a (j + 1)).comp (Polynomial.X + 1) -
        oscillationPolynomial a (j + 1) =
      -(Polynomial.X + Polynomial.C a) *
        (oscillationPolynomial a j).comp (Polynomial.X + 1) := by
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_neg,
    Polynomial.eval_C]
  exact oscillationPolynomial_recurrence a j t

/-- Complex scalar extension used by the corpus's Gamma-function modules. -/
def complexOscillationPolynomial (a : ℚ) (j : ℕ) : Polynomial ℂ :=
  (oscillationPolynomial a j).map (algebraMap ℚ ℂ)

theorem complexOscillationPolynomial_polynomial_recurrence (a : ℚ) (j : ℕ) :
    (complexOscillationPolynomial a (j + 1)).comp (Polynomial.X + 1) -
        complexOscillationPolynomial a (j + 1) =
      -(Polynomial.X + Polynomial.C (a : ℂ)) *
        (complexOscillationPolynomial a j).comp (Polynomial.X + 1) := by
  have h := congrArg (Polynomial.map (algebraMap ℚ ℂ))
    (oscillationPolynomial_polynomial_recurrence a j)
  simpa [complexOscillationPolynomial, Polynomial.map_comp] using h

theorem dyadic_weight_cancel {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (((2 : ℚ) ^ n - 2) - ((2 : ℚ) ^ (n - k) - 2)) *
        ((2 : ℚ) ^ k / ((2 : ℚ) ^ k - 1)) = (2 : ℚ) ^ n := by
  have hden : (2 : ℚ) ^ k - 1 ≠ 0 := by
    have hp : (1 : ℚ) < (2 : ℚ) ^ k :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - k) * (2 : ℚ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [hpow]
  field_simp
  ring

theorem eCoeff_recurrence {m : ℕ} (hm : 1 ≤ m) :
    ((2 : ℚ) ^ (m + 1) - 2) * eCoeff m =
      (2 : ℚ) ^ (m + 1) +
        ∑ j ∈ Finset.Icc 1 m, ((m + 1).choose j : ℚ) * eCoeff (m - j) := by
  have hconv := binomial_lower_convolution eWeight m
  have heSum :
      ∑ j ∈ Finset.Icc 1 m, ((m + 1).choose j : ℚ) * eCoeff (m - j) =
        -∑ k ∈ Finset.Icc 1 m, ((m + 1).choose k : ℚ) *
          ((2 : ℚ) ^ (m + 1 - k) - 2) * eWeight k := by
    change ∑ j ∈ Finset.Icc 1 m, ((m + 1).choose j : ℚ) *
        (-∑ k ∈ Finset.Icc 1 (m - j), ((m - j + 1).choose k : ℚ) * eWeight k) = _
    simpa only [mul_neg, Finset.sum_neg_distrib] using congrArg Neg.neg hconv
  have hterm : ∀ k ∈ Finset.Icc 1 m,
      ((m + 1).choose k : ℚ) * ((2 : ℚ) ^ (m + 1 - k) - 2) * eWeight k =
        ((2 : ℚ) ^ (m + 1) - 2) *
            (((m + 1).choose k : ℚ) * eWeight k) -
          (2 : ℚ) ^ (m + 1) * (((m + 1).choose k : ℚ) * bernoulli k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
    have hkn : k ≤ m + 1 := by omega
    have hcancel := dyadic_weight_cancel hk1 hkn
    rw [eWeight]
    linear_combination
      -(((m + 1).choose k : ℚ) * bernoulli k) * hcancel
  have hweighted :
      ∑ k ∈ Finset.Icc 1 m, ((m + 1).choose k : ℚ) *
          ((2 : ℚ) ^ (m + 1 - k) - 2) * eWeight k =
        ((2 : ℚ) ^ (m + 1) - 2) *
            (∑ k ∈ Finset.Icc 1 m, ((m + 1).choose k : ℚ) * eWeight k) +
          (2 : ℚ) ^ (m + 1) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
    rw [bernoulli_Icc_sum_eq_neg_one hm]
    ring
  rw [heSum, hweighted, eCoeff]
  ring

/-- Assumption-free indexing of the dyadic coefficient recurrence in arXiv:2603.29998. -/
theorem eCoeff_recurrence_succ (m : ℕ) :
    ((2 : ℚ) ^ (m + 2) - 2) * eCoeff (m + 1) =
      (2 : ℚ) ^ (m + 2) +
        ∑ j ∈ Finset.Icc 1 (m + 1),
          ((m + 2).choose j : ℚ) * eCoeff (m + 1 - j) := by
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (eCoeff_recurrence (m := m + 1) (by omega))

/-! ## Fixed-length radix words -/

/-- Integer represented by a little-endian fixed-length radix word. -/
def radixNumeral {n b : ℕ} (w : Fin n → Fin b) : ℕ :=
  (finFunctionFinEquiv w : Fin (b ^ n))

/-- Burnol's normalized coordinate `x(w) = n(w) / b^length(w)`. -/
def radixCoordinate {n b : ℕ} (w : Fin n → Fin b) : ℚ :=
  (radixNumeral w : ℚ) / (b : ℚ) ^ n

theorem radixNumeral_eq_sum {n b : ℕ} (w : Fin n → Fin b) :
    radixNumeral w = ∑ i : Fin n, (w i : ℕ) * b ^ (i : ℕ) := by
  exact finFunctionFinEquiv_apply w

theorem radixNumeral_snoc {n b : ℕ} (w : Fin n → Fin b) (a : Fin b) :
    radixNumeral (Fin.snoc w a) = radixNumeral w + (a : ℕ) * b ^ n := by
  rw [radixNumeral_eq_sum, radixNumeral_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem radixCoordinate_snoc {n b : ℕ} (hb : 2 ≤ b) (w : Fin n → Fin b) (a : Fin b) :
    radixCoordinate (Fin.snoc w a) = ((a : ℚ) + radixCoordinate w) / b := by
  have hb0 : (b : ℚ) ≠ 0 := by positivity
  rw [radixCoordinate, radixCoordinate, radixNumeral_snoc, pow_succ]
  push_cast
  field_simp
  ring

/-- Assumption-free radix form, encoding every paper radix `b > 1` as `b+2`. -/
theorem radixCoordinate_snoc_shifted {n b : ℕ}
    (w : Fin n → Fin (b + 2)) (a : Fin (b + 2)) :
    radixCoordinate (Fin.snoc w a) = ((a : ℚ) + radixCoordinate w) / (b + 2) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using radixCoordinate_snoc (by omega) w a

theorem radixCoordinate_mem_Ico {n b : ℕ} (hb : 2 ≤ b) (w : Fin n → Fin b) :
    radixCoordinate w ∈ Set.Ico (0 : ℚ) 1 := by
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · rw [radixCoordinate, div_lt_one (by positivity)]
    have hw := (finFunctionFinEquiv w).isLt
    exact_mod_cast hw

theorem injective_radixCoordinate (n : ℕ) {b : ℕ} (hb : 2 ≤ b) :
    Function.Injective (radixCoordinate : (Fin n → Fin b) → ℚ) := by
  intro w v h
  have hden : (b : ℚ) ^ n ≠ 0 := by positivity
  have hnum : (radixNumeral w : ℚ) = (radixNumeral v : ℚ) := by
    exact (div_left_inj' hden).mp h
  have hnumNat : radixNumeral w = radixNumeral v := by exact_mod_cast hnum
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  exact hnumNat

theorem cast_radixCoordinate_eq_digitOnsite {n b : ℕ} (w : Fin n → Fin b) :
    ((radixCoordinate w : ℚ) : ℝ) =
      GaloisForLFunctions.HTGeometry.onsiteProductEnergy
        (GaloisForLFunctions.HTGeometry.digitOnsite n b) w / (b : ℝ) ^ n := by
  rw [radixCoordinate, radixNumeral_eq_sum]
  push_cast
  simp [GaloisForLFunctions.HTGeometry.onsiteProductEnergy,
    GaloisForLFunctions.HTGeometry.digitOnsite]

def digitPowerSum (b j : ℕ) : ℚ := ∑ a : Fin b, (a : ℚ) ^ j

/-- Faulhaber--Bernoulli formula for the digit power sum `γ_j` in Burnol's recurrences. -/
theorem digitPowerSum_eq_bernoulli (b j : ℕ) :
    (j + 1 : ℚ) * digitPowerSum b j =
      (Polynomial.bernoulli (j + 1)).eval (b : ℚ) - bernoulli (j + 1) := by
  simpa [digitPowerSum, Nat.succ_eq_add_one, ← Fin.sum_univ_eq_sum_range] using
    Polynomial.sum_range_pow_eq_bernoulli_sub b j

theorem digitPowerSum_eq_bernoulli_div (b j : ℕ) :
    digitPowerSum b j =
      ((Polynomial.bernoulli (j + 1)).eval (b : ℚ) - bernoulli (j + 1)) / (j + 1 : ℚ) := by
  rw [eq_div_iff (by positivity)]
  simpa [mul_comm] using digitPowerSum_eq_bernoulli b j

/-- Paper 2603.29998's finite Riemann-sum moment, with positive size encoded as `n+1`. -/
def finiteRiemannMoment (n m : ℕ) : ℚ :=
  1 / (n + 1 : ℚ) * ∑ k ∈ Finset.range (n + 1), ((k : ℚ) / (n + 1 : ℚ)) ^ m

/-- Equation (24) of arXiv:2603.29998. -/
theorem finiteRiemannMoment_eq_bernoulli (n m : ℕ) :
    (m + 1 : ℚ) * finiteRiemannMoment n m =
      ((Polynomial.bernoulli (m + 1)).eval (n + 1 : ℚ) - bernoulli (m + 1)) /
        (n + 1 : ℚ) ^ (m + 1) := by
  have hbern := Polynomial.sum_range_pow_eq_bernoulli_sub (n + 1) m
  rw [finiteRiemannMoment]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  push_cast at hbern
  rw [← hbern, pow_succ]
  field_simp

def dyadicRiemannMoment (l m : ℕ) : ℚ :=
  1 / (2 : ℚ) ^ l * ∑ k ∈ Finset.range (2 ^ l), ((k : ℚ) / (2 : ℚ) ^ l) ^ m

theorem dyadicRiemannMoment_eq_bernoulli (l m : ℕ) :
    (m + 1 : ℚ) * dyadicRiemannMoment l m =
      ((Polynomial.bernoulli (m + 1)).eval ((2 : ℚ) ^ l) - bernoulli (m + 1)) /
        (2 : ℚ) ^ ((m + 1) * l) := by
  have hbern := Polynomial.sum_range_pow_eq_bernoulli_sub (2 ^ l) m
  rw [dyadicRiemannMoment]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  push_cast at hbern
  rw [mul_comm (m + 1) l]
  rw [pow_mul, ← hbern, pow_succ]
  field_simp

def finiteRadixMoment (b n m : ℕ) : ℚ :=
  ∑ w : Fin n → Fin b, radixCoordinate w ^ m

/-- Fixed-length radix words are exactly the uniform mesh used by the paper's Riemann sums. -/
theorem finiteRadixMoment_eq_range_sum (b n m : ℕ) :
    finiteRadixMoment b n m =
      ∑ k ∈ Finset.range (b ^ n), ((k : ℚ) / (b : ℚ) ^ n) ^ m := by
  rw [finiteRadixMoment, ← Fin.sum_univ_eq_sum_range]
  simpa only [radixCoordinate, radixNumeral] using
    (Equiv.sum_comp (finFunctionFinEquiv : (Fin n → Fin b) ≃ Fin (b ^ n))
      (fun k : Fin (b ^ n) => ((k : ℚ) / (b : ℚ) ^ n) ^ m))

/-- Faulhaber closes every positive-radix fixed-word moment in Bernoulli form. -/
theorem finiteRadixMoment_eq_bernoulli_shifted (b n m : ℕ) :
    (m + 1 : ℚ) * finiteRadixMoment (b + 2) n m =
      ((Polynomial.bernoulli (m + 1)).eval ((b + 2 : ℚ) ^ n) - bernoulli (m + 1)) /
        ((b + 2 : ℚ) ^ n) ^ m := by
  have hbern := Polynomial.sum_range_pow_eq_bernoulli_sub ((b + 2) ^ n) m
  rw [finiteRadixMoment_eq_range_sum]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  push_cast at hbern
  norm_num [Nat.cast_add] at hbern ⊢
  rw [← hbern]
  field_simp

/-- Equation (20)'s dyadic mesh is normalized finite-word moment already present in corpus. -/
theorem dyadicRiemannMoment_eq_finiteRadixMoment (l m : ℕ) :
    dyadicRiemannMoment l m =
      1 / (2 : ℚ) ^ l * finiteRadixMoment 2 l m := by
  rw [dyadicRiemannMoment, finiteRadixMoment_eq_range_sum]
  norm_num

theorem sum_radixWords_succ {M : Type*} [AddCommMonoid M]
    (b n : ℕ) (f : (Fin (n + 1) → Fin b) → M) :
    ∑ w, f w = ∑ a : Fin b, ∑ w : Fin n → Fin b, f (Fin.snoc w a) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin b)) f,
    Fintype.sum_prod_type]
  rfl

theorem finiteRadixMoment_succ (b n m : ℕ) (hb : 2 ≤ b) :
    finiteRadixMoment b (n + 1) m =
      (1 / (b : ℚ) ^ m) * ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * digitPowerSum b j * finiteRadixMoment b n (m - j) := by
  rw [finiteRadixMoment, sum_radixWords_succ]
  simp_rw [radixCoordinate_snoc hb, div_pow, add_pow]
  simp only [digitPowerSum, finiteRadixMoment]
  have hb0 : (b : ℚ) ^ m ≠ 0 := by positivity
  simp_rw [← Finset.sum_div]
  field_simp
  have hswap1 :
      (∑ a : Fin b, ∑ w : Fin n → Fin b, ∑ j ∈ Finset.range (m + 1),
        (a : ℚ) ^ j * radixCoordinate w ^ (m - j) * (m.choose j : ℚ)) =
      ∑ a : Fin b, ∑ j ∈ Finset.range (m + 1), ∑ w : Fin n → Fin b,
        (a : ℚ) ^ j * radixCoordinate w ^ (m - j) * (m.choose j : ℚ) := by
    apply Fintype.sum_congr
    intro a
    exact Finset.sum_comm
  rw [hswap1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ a : Fin b, ∑ w : Fin n → Fin b,
        (a : ℚ) ^ j * radixCoordinate w ^ (m - j) * (m.choose j : ℚ)) =
        ∑ a : Fin b, ∑ w : Fin n → Fin b,
          ((m.choose j : ℚ) * (a : ℚ) ^ j) * radixCoordinate w ^ (m - j) := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro w
      ring
    _ = ∑ a : Fin b, ((m.choose j : ℚ) * (a : ℚ) ^ j) *
          (∑ w : Fin n → Fin b, radixCoordinate w ^ (m - j)) := by
      apply Fintype.sum_congr
      intro a
      rw [Finset.mul_sum]
    _ = ((m.choose j : ℚ) * (∑ a : Fin b, (a : ℚ) ^ j)) *
          (∑ w : Fin n → Fin b, radixCoordinate w ^ (m - j)) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]

theorem finiteRadixMoment_succ_shifted (b n m : ℕ) :
    finiteRadixMoment (b + 2) (n + 1) m =
      (1 / (b + 2 : ℚ) ^ m) * ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * digitPowerSum (b + 2) j *
          finiteRadixMoment (b + 2) n (m - j) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    finiteRadixMoment_succ (b + 2) n m (by omega)

/-! ## Arbitrary admissible alphabets -/

def wordCoordinate {D : Type*} {n b : ℕ} (digit : D → Fin b) (w : Fin n → D) : ℚ :=
  radixCoordinate (digit ∘ w)

def alphabetPowerSum {D : Type*} [Fintype D] {b : ℕ} (digit : D → Fin b) (j : ℕ) : ℚ :=
  ∑ a : D, (digit a : ℚ) ^ j

def finiteWordMoment {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin b) (n m : ℕ) : ℚ :=
  ∑ w : Fin n → D, wordCoordinate digit w ^ m

theorem alphabetPowerSum_zero {D : Type*} [Fintype D] {b : ℕ} (digit : D → Fin b) :
    alphabetPowerSum digit 0 = Fintype.card D := by
  simp [alphabetPowerSum]

theorem finiteWordMoment_zero {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin b) (n : ℕ) :
    finiteWordMoment b digit n 0 = Fintype.card D ^ n := by
  simp [finiteWordMoment]

theorem finiteWordMoment_nonneg {D : Type*} [Fintype D]
    (b : ℕ) (hb : 2 ≤ b) (digit : D → Fin b) (n m : ℕ) :
    0 ≤ finiteWordMoment b digit n m := by
  apply Finset.sum_nonneg
  intro w hw
  exact pow_nonneg (radixCoordinate_mem_Ico hb (digit ∘ w)).1 m

theorem finiteWordMoment_antitone {D : Type*} [Fintype D]
    (b : ℕ) (hb : 2 ≤ b) (digit : D → Fin b) (n : ℕ) :
    Antitone (finiteWordMoment b digit n) := by
  intro j k hjk
  apply Finset.sum_le_sum
  intro w hw
  have hx : wordCoordinate digit w ∈ Set.Ico (0 : ℚ) 1 := by
    exact radixCoordinate_mem_Ico hb (digit ∘ w)
  exact pow_le_pow_of_le_one hx.1 hx.2.le hjk

theorem wordCoordinate_snoc {D : Type*} {n b : ℕ} (hb : 2 ≤ b)
    (digit : D → Fin b) (w : Fin n → D) (a : D) :
    wordCoordinate digit (Fin.snoc w a) = ((digit a : ℚ) + wordCoordinate digit w) / b := by
  rw [wordCoordinate, Fin.comp_snoc, radixCoordinate_snoc hb]
  rfl

theorem wordCoordinate_mem_Ico {D : Type*} {n b : ℕ} (hb : 2 ≤ b)
    (digit : D → Fin b) (w : Fin n → D) :
    wordCoordinate digit w ∈ Set.Ico (0 : ℚ) 1 :=
  radixCoordinate_mem_Ico hb (digit ∘ w)

theorem injective_wordCoordinate {D : Type*} {n b : ℕ} (hb : 2 ≤ b)
    {digit : D → Fin b} (hdigit : Function.Injective digit) :
    Function.Injective (wordCoordinate digit : (Fin n → D) → ℚ) := by
  intro w v h
  have hcomp : digit ∘ w = digit ∘ v := injective_radixCoordinate n hb h
  funext i
  exact hdigit (congrFun hcomp i)

theorem sum_words_succ {D M : Type*} [Fintype D] [AddCommMonoid M]
    (n : ℕ) (f : (Fin (n + 1) → D) → M) :
    ∑ w, f w = ∑ a : D, ∑ w : Fin n → D, f (Fin.snoc w a) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => D)) f,
    Fintype.sum_prod_type]
  rfl

theorem finiteWordMoment_succ {D : Type*} [Fintype D]
    (b : ℕ) (hb : 2 ≤ b) (digit : D → Fin b) (n m : ℕ) :
    finiteWordMoment b digit (n + 1) m =
      (1 / (b : ℚ) ^ m) * ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * alphabetPowerSum digit j *
          finiteWordMoment b digit n (m - j) := by
  rw [finiteWordMoment, sum_words_succ]
  simp_rw [wordCoordinate_snoc hb, div_pow, add_pow]
  simp only [alphabetPowerSum, finiteWordMoment]
  have hb0 : (b : ℚ) ^ m ≠ 0 := by positivity
  simp_rw [← Finset.sum_div]
  field_simp
  have hswap1 :
      (∑ a : D, ∑ w : Fin n → D, ∑ j ∈ Finset.range (m + 1),
        (digit a : ℚ) ^ j * wordCoordinate digit w ^ (m - j) * (m.choose j : ℚ)) =
      ∑ a : D, ∑ j ∈ Finset.range (m + 1), ∑ w : Fin n → D,
        (digit a : ℚ) ^ j * wordCoordinate digit w ^ (m - j) * (m.choose j : ℚ) := by
    apply Fintype.sum_congr
    intro a
    exact Finset.sum_comm
  rw [hswap1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ a : D, ∑ w : Fin n → D,
        (digit a : ℚ) ^ j * wordCoordinate digit w ^ (m - j) * (m.choose j : ℚ)) =
        ∑ a : D, ∑ w : Fin n → D,
          ((m.choose j : ℚ) * (digit a : ℚ) ^ j) * wordCoordinate digit w ^ (m - j) := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro w
      ring
    _ = ∑ a : D, ((m.choose j : ℚ) * (digit a : ℚ) ^ j) *
          (∑ w : Fin n → D, wordCoordinate digit w ^ (m - j)) := by
      apply Fintype.sum_congr
      intro a
      rw [Finset.mul_sum]
    _ = ((m.choose j : ℚ) * (∑ a : D, (digit a : ℚ) ^ j)) *
          (∑ w : Fin n → D, wordCoordinate digit w ^ (m - j)) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]

theorem finiteWordMoment_succ_shifted {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin (b + 2)) (n m : ℕ) :
    finiteWordMoment (b + 2) digit (n + 1) m =
      (1 / (b + 2 : ℚ) ^ m) * ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * alphabetPowerSum digit j *
          finiteWordMoment (b + 2) digit n (m - j) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    finiteWordMoment_succ (b + 2) (by omega) digit n m

/-- Formal length-generating series for Burnol's word moments. -/
def wordMomentSeries {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin b) (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => finiteWordMoment b digit n m

theorem coeff_wordMomentSeries {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin b) (m n : ℕ) :
    PowerSeries.coeff n (wordMomentSeries b digit m) = finiteWordMoment b digit n m := by
  simp [wordMomentSeries]

theorem finiteWordMoment_empty_succ {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin b) (m : ℕ) :
    finiteWordMoment b digit 0 (m + 1) = 0 := by
  simp [finiteWordMoment, wordCoordinate, radixCoordinate, radixNumeral]

/-- Formal-series form of Proposition 2.5 of arXiv:2601.23158.
Coefficient specialization at `X = b⁻ˢ` gives the paper's moment recurrence. -/
theorem wordMomentSeries_functional {D : Type*} [Fintype D]
    (b : ℕ) (hb : 2 ≤ b) (digit : D → Fin b) (m : ℕ) :
    PowerSeries.C ((b : ℚ) ^ (m + 1)) * wordMomentSeries b digit (m + 1) =
      PowerSeries.X *
        (∑ j ∈ Finset.range (m + 2),
          PowerSeries.C (((m + 1).choose j : ℚ) * alphabetPowerSum digit j) *
            wordMomentSeries b digit (m + 1 - j)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_C_mul, coeff_wordMomentSeries,
        finiteWordMoment_empty_succ, PowerSeries.coeff_zero_X_mul]
      ring
  | succ n =>
      rw [PowerSeries.coeff_C_mul, coeff_wordMomentSeries,
        PowerSeries.coeff_succ_X_mul]
      simp_rw [map_sum, PowerSeries.coeff_C_mul, coeff_wordMomentSeries]
      have hrec := finiteWordMoment_succ b hb digit n (m + 1)
      rw [hrec]
      have hbpow : (b : ℚ) ^ (m + 1) ≠ 0 := by positivity
      field_simp

theorem wordMomentSeries_recurrence {D : Type*} [Fintype D]
    (b : ℕ) (hb : 2 ≤ b) (digit : D → Fin b) (m : ℕ) :
    (PowerSeries.C ((b : ℚ) ^ (m + 1)) -
        PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
          wordMomentSeries b digit (m + 1) =
      PowerSeries.X *
        (∑ j ∈ Finset.Icc 1 (m + 1),
          PowerSeries.C (((m + 1).choose j : ℚ) * alphabetPowerSum digit j) *
            wordMomentSeries b digit (m + 1 - j)) := by
  have hfun := wordMomentSeries_functional b hb digit m
  let f : ℕ → PowerSeries ℚ := fun j =>
    PowerSeries.C (((m + 1).choose j : ℚ) * alphabetPowerSum digit j) *
      wordMomentSeries b digit (m + 1 - j)
  have hzero : 0 ∈ Finset.range (m + 2) := by simp
  have herase : (Finset.range (m + 2)).erase 0 = Finset.Icc 1 (m + 1) := by
    ext j
    simp
    omega
  change PowerSeries.C ((b : ℚ) ^ (m + 1)) * wordMomentSeries b digit (m + 1) =
      PowerSeries.X * (∑ j ∈ Finset.range (m + 2), f j) at hfun
  rw [← Finset.sum_erase_add _ _ hzero, herase] at hfun
  simp [f, alphabetPowerSum_zero] at hfun
  simp only [map_mul, map_pow, map_natCast] at hfun ⊢
  linear_combination hfun

theorem wordMomentSeries_zero_geometric {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin b) :
    wordMomentSeries b digit 0 =
      1 + PowerSeries.X *
        (PowerSeries.C (Fintype.card D : ℚ) * wordMomentSeries b digit 0) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [coeff_wordMomentSeries, finiteWordMoment_zero]
  | succ n =>
      rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
        coeff_wordMomentSeries, coeff_wordMomentSeries,
        finiteWordMoment_zero, finiteWordMoment_zero]
      rw [pow_succ]
      ring

theorem wordMomentSeries_zero_resolvent {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin b) :
    (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        wordMomentSeries b digit 0 = 1 := by
  have h := wordMomentSeries_zero_geometric b digit
  linear_combination h

theorem firstMomentSeries_recurrence {D : Type*} [Fintype D]
    (b : ℕ) (hb : 2 ≤ b) (digit : D → Fin b) :
    (PowerSeries.C (b : ℚ) - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        wordMomentSeries b digit 1 =
      PowerSeries.X *
        (PowerSeries.C (alphabetPowerSum digit 1) * wordMomentSeries b digit 0) := by
  simpa using wordMomentSeries_recurrence b hb digit 0

theorem secondMomentSeries_recurrence {D : Type*} [Fintype D]
    (b : ℕ) (hb : 2 ≤ b) (digit : D → Fin b) :
    ((b : PowerSeries ℚ) ^ (2 : ℕ) -
        PowerSeries.X * (Fintype.card D : PowerSeries ℚ)) *
        wordMomentSeries b digit 2 =
      PowerSeries.X *
        (2 * PowerSeries.C (alphabetPowerSum digit 1) * wordMomentSeries b digit 1 +
          PowerSeries.C (alphabetPowerSum digit 2) * wordMomentSeries b digit 0) := by
  have h := wordMomentSeries_recurrence b hb digit 1
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 1 + 1)] at h
  norm_num at h
  exact h

/-- Denominator-cleared first-moment formula from Proposition 2.5 of arXiv:2601.23158. -/
theorem firstMomentSeries_closed_shifted {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin (b + 2)) :
    (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        wordMomentSeries (b + 2) digit 1 =
      PowerSeries.X * PowerSeries.C (alphabetPowerSum digit 1) := by
  have hfirst := firstMomentSeries_recurrence (b + 2) (by omega) digit
  have hzero := wordMomentSeries_zero_resolvent (b + 2) digit
  calc
    (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        wordMomentSeries (b + 2) digit 1 =
      (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        ((PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
            wordMomentSeries (b + 2) digit 1) := by ring
    _ = (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.X *
          (PowerSeries.C (alphabetPowerSum digit 1) *
            wordMomentSeries (b + 2) digit 0)) := by
      rw [hfirst]
    _ = PowerSeries.X * PowerSeries.C (alphabetPowerSum digit 1) *
        ((1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
          wordMomentSeries (b + 2) digit 0) := by ring
    _ = PowerSeries.X * PowerSeries.C (alphabetPowerSum digit 1) := by
      rw [hzero]
      ring

/-- Denominator-cleared second-moment formula from Proposition 2.5 of arXiv:2601.23158. -/
theorem secondMomentSeries_closed_shifted {D : Type*} [Fintype D]
    (b : ℕ) (digit : D → Fin (b + 2)) :
    (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ) ^ (2 : ℕ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        wordMomentSeries (b + 2) digit 2 =
      PowerSeries.X *
        (2 * PowerSeries.C (alphabetPowerSum digit 1) * PowerSeries.X *
            PowerSeries.C (alphabetPowerSum digit 1) +
          PowerSeries.C (alphabetPowerSum digit 2) *
            (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
              PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ))) := by
  have hsecond := secondMomentSeries_recurrence (b + 2) (by omega) digit
  have hpow : PowerSeries.C (((b + 2 : ℕ) : ℚ) ^ (2 : ℕ)) =
      ((b + 2 : ℕ) : PowerSeries ℚ) ^ (2 : ℕ) := by
    rw [map_pow, map_natCast]
  have hcard : PowerSeries.C (Fintype.card D : ℚ) =
      (Fintype.card D : PowerSeries ℚ) := by
    rw [map_natCast]
  have hfirst := firstMomentSeries_closed_shifted b digit
  have hzero := wordMomentSeries_zero_resolvent (b + 2) digit
  calc
    (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ) ^ (2 : ℕ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        wordMomentSeries (b + 2) digit 2 =
      (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        ((PowerSeries.C (((b + 2 : ℕ) : ℚ) ^ (2 : ℕ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
            wordMomentSeries (b + 2) digit 2) := by ring
    _ = (1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
          PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
        (PowerSeries.X *
          (2 * PowerSeries.C (alphabetPowerSum digit 1) *
              wordMomentSeries (b + 2) digit 1 +
            PowerSeries.C (alphabetPowerSum digit 2) *
              wordMomentSeries (b + 2) digit 0)) := by
      rw [hpow, hcard, hsecond]
    _ = PowerSeries.X *
        (2 * PowerSeries.C (alphabetPowerSum digit 1) *
            ((1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
              (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
                PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
                  wordMomentSeries (b + 2) digit 1) +
          PowerSeries.C (alphabetPowerSum digit 2) *
            (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
              PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
                ((1 - PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ)) *
                  wordMomentSeries (b + 2) digit 0)) := by ring
    _ = PowerSeries.X *
        (2 * PowerSeries.C (alphabetPowerSum digit 1) * PowerSeries.X *
            PowerSeries.C (alphabetPowerSum digit 1) +
          PowerSeries.C (alphabetPowerSum digit 2) *
            (PowerSeries.C (((b + 2 : ℕ) : ℚ)) -
              PowerSeries.X * PowerSeries.C (Fintype.card D : ℚ))) := by
      rw [hfirst, hzero]
      ring

abbrev ExcludedDigit {b : ℕ} (d : Fin b) :=
  ↥((Finset.univ : Finset (Fin b)).erase d)

instance instFintypeExcludedDigit {b : ℕ} (d : Fin b) : Fintype (ExcludedDigit d) :=
  Fintype.ofFinite _

def excludedDigitEmbedding {b : ℕ} (d : Fin b) : ExcludedDigit d → Fin b := fun a => a.1

theorem card_excludedDigit {b : ℕ} (d : Fin b) : Fintype.card (ExcludedDigit d) = b - 1 := by
  simp [ExcludedDigit]

theorem alphabetPowerSum_excludedDigit {b j : ℕ} (d : Fin b) :
    alphabetPowerSum (excludedDigitEmbedding d) j = digitPowerSum b j - (d : ℚ) ^ j := by
  rw [alphabetPowerSum, digitPowerSum]
  change (∑ a : ExcludedDigit d, (a.1 : ℚ) ^ j) =
    (∑ a : Fin b, (a : ℚ) ^ j) - (d : ℚ) ^ j
  have hsub := Finset.sum_subtype
    (F := instFintypeExcludedDigit d)
    (p := fun a : Fin b => a ∈ Finset.univ.erase d)
    (Finset.univ.erase d) (by intro a; rfl)
    (fun a : Fin b => (a : ℚ) ^ j)
  rw [← hsub]
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin b))
    (fun a : Fin b => (a : ℚ) ^ j) (by simp : d ∈ (Finset.univ : Finset (Fin b)))
  linear_combination herase

/-- Missing-one-digit moment series, with radix `b+2` encoding the paper's `b>1`. -/
def kempnerWordMomentSeries (b : ℕ) (d : Fin (b + 2)) (m : ℕ) : PowerSeries ℚ :=
  wordMomentSeries (b + 2) (excludedDigitEmbedding d) m

/-- Equations (9)/(21) of arXiv:2404.13763 in formal length-generating-series form. -/
theorem kempnerWordMomentSeries_recurrence
    (b : ℕ) (d : Fin (b + 2)) (m : ℕ) :
    (PowerSeries.C ((b + 2 : ℚ) ^ (m + 1)) -
        PowerSeries.X * PowerSeries.C (b + 1 : ℚ)) *
          kempnerWordMomentSeries b d (m + 1) =
      PowerSeries.X *
        (∑ j ∈ Finset.Icc 1 (m + 1),
          PowerSeries.C (((m + 1).choose j : ℚ) *
            (digitPowerSum (b + 2) j - (d : ℚ) ^ j)) *
              kempnerWordMomentSeries b d (m + 1 - j)) := by
  have h := wordMomentSeries_recurrence (b + 2) (by omega)
    (excludedDigitEmbedding d) m
  simp only [kempnerWordMomentSeries, card_excludedDigit,
    alphabetPowerSum_excludedDigit] at h ⊢
  norm_num at h ⊢
  exact h

/-- Closed first moment for a single forbidden digit, without analytic convergence assumptions. -/
theorem kempnerFirstMomentSeries_closed
    (b : ℕ) (d : Fin (b + 2)) :
    (1 - PowerSeries.X * PowerSeries.C (b + 1 : ℚ)) *
        (PowerSeries.C (b + 2 : ℚ) -
          PowerSeries.X * PowerSeries.C (b + 1 : ℚ)) *
        kempnerWordMomentSeries b d 1 =
      PowerSeries.X *
        PowerSeries.C (digitPowerSum (b + 2) 1 - (d : ℚ) ^ (1 : ℕ)) := by
  have h := firstMomentSeries_closed_shifted b (excludedDigitEmbedding d)
  simp only [kempnerWordMomentSeries, card_excludedDigit,
    alphabetPowerSum_excludedDigit] at h ⊢
  norm_num at h ⊢
  exact h

/-- Closed second moment for a single forbidden digit. -/
theorem kempnerSecondMomentSeries_closed
    (b : ℕ) (d : Fin (b + 2)) :
    (1 - PowerSeries.X * PowerSeries.C (b + 1 : ℚ)) *
        (PowerSeries.C (b + 2 : ℚ) -
          PowerSeries.X * PowerSeries.C (b + 1 : ℚ)) *
        (PowerSeries.C ((b + 2 : ℚ) ^ (2 : ℕ)) -
          PowerSeries.X * PowerSeries.C (b + 1 : ℚ)) *
        kempnerWordMomentSeries b d 2 =
      PowerSeries.X *
        (2 * PowerSeries.C (digitPowerSum (b + 2) 1 - (d : ℚ) ^ (1 : ℕ)) *
            PowerSeries.X *
              PowerSeries.C (digitPowerSum (b + 2) 1 - (d : ℚ) ^ (1 : ℕ)) +
          PowerSeries.C (digitPowerSum (b + 2) 2 - (d : ℚ) ^ (2 : ℕ)) *
            (PowerSeries.C (b + 2 : ℚ) -
              PowerSeries.X * PowerSeries.C (b + 1 : ℚ))) := by
  have h := secondMomentSeries_closed_shifted b (excludedDigitEmbedding d)
  simp only [kempnerWordMomentSeries, card_excludedDigit,
    alphabetPowerSum_excludedDigit] at h ⊢
  norm_num at h ⊢
  exact h

/-- Paper's admissible-digit specialization, with `D` the subtype cut out by `A`. -/
def admissibleFiniteMoment {b : ℕ} (A : Finset (Fin b)) (n m : ℕ) : ℚ :=
  finiteWordMoment b (fun a : ↑A => a.1) n m

theorem admissibleFiniteMoment_succ {b : ℕ} (hb : 2 ≤ b)
    (A : Finset (Fin b)) (n m : ℕ) :
    admissibleFiniteMoment A (n + 1) m =
      (1 / (b : ℚ) ^ m) * ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * (∑ a : ↑A, (a.1 : ℚ) ^ j) *
          admissibleFiniteMoment A n (m - j) := by
  simpa [admissibleFiniteMoment, alphabetPowerSum] using
    (finiteWordMoment_succ b hb (fun a : ↑A => a.1) n m)

theorem admissibleFiniteMoment_succ_shifted (b : ℕ)
    (A : Finset (Fin (b + 2))) (n m : ℕ) :
    admissibleFiniteMoment A (n + 1) m =
      (1 / (b + 2 : ℚ) ^ m) * ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ) * (∑ a : ↑A, (a.1 : ℚ) ^ j) *
          admissibleFiniteMoment A n (m - j) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    admissibleFiniteMoment_succ (by omega) A n m

end

end RHTower.Burnol
