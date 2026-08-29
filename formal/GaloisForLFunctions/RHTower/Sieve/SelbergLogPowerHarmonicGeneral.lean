import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowGeneralMoment
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerPrincipalAsymptotics

/-!
# The Selberg harmonic main term at every pair of logarithmic powers

`selbergLogPowerHarmonicMain q r a b N` is the harmonic model that replaces the principal Selberg
model of the `(log^{q+1}, log^{r+1})` moment.  This file evaluates it at **every** pair `(q, r)`:

`selbergLogPowerHarmonicMain q r a b N / (log N)^{q+r+1} → (q+1)(r+1)/(q+r+1)`.

Two single binomial expansions do the work.  The inner one reduces one shifted logarithmic power
to the harmonic logarithmic moments of `HarmonicLogWindowGeneralMoment`; the outer one converts the
second shift `b` into the first shift `a`, after which only the top-degree term survives the
normalization.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- `∑_{s ≤ m} (-1)^s binom(m+1, s+1) = 1`. -/
theorem sum_alternating_choose_succ (m : ℕ) :
    ∑ s ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ s * (((m + 1).choose (s + 1) : ℕ) : ℝ) = 1 := by
  have hz : ∑ k ∈ Finset.range (m + 1 + 1),
      (-1 : ℤ) ^ k * (((m + 1).choose k : ℕ) : ℤ) = 0 := by
    rw [Int.alternating_sum_range_choose]
    simp
  have hsplit := Finset.sum_range_succ'
    (fun k => (-1 : ℤ) ^ k * (((m + 1).choose k : ℕ) : ℤ)) (m + 1)
  rw [hsplit] at hz
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at hz
  have hZ : ∑ s ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ s * (((m + 1).choose (s + 1) : ℕ) : ℤ) = 1 := by
    have hneg : ∀ s ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (s + 1) * (((m + 1).choose (s + 1) : ℕ) : ℤ) =
          -((-1 : ℤ) ^ s * (((m + 1).choose (s + 1) : ℕ) : ℤ)) := by
      intro s _
      rw [pow_succ]
      ring
    rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib] at hz
    linarith
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hZ

/-- The alternating binomial harmonic identity `∑_{s ≤ m} (-1)^s binom(m,s)/(s+1) = 1/(m+1)`. -/
theorem sum_choose_alternating_div_succ (m : ℕ) :
    ∑ s ∈ Finset.range (m + 1),
        ((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s / ((s : ℝ) + 1) = 1 / ((m : ℝ) + 1) := by
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hkey : ∀ s ∈ Finset.range (m + 1),
      ((m : ℝ) + 1) * (((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s / ((s : ℝ) + 1)) =
        (-1 : ℝ) ^ s * (((m + 1).choose (s + 1) : ℕ) : ℝ) := by
    intro s _
    have hnat := Nat.add_one_mul_choose_eq m s
    have hcast : ((m : ℝ) + 1) * ((m.choose s : ℕ) : ℝ) =
        (((m + 1).choose (s + 1) : ℕ) : ℝ) * ((s : ℝ) + 1) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hnat
    have hs1 : ((s : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    linarith [hcast]
  have hmul : ((m : ℝ) + 1) *
      (∑ s ∈ Finset.range (m + 1),
        ((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s / ((s : ℝ) + 1)) = 1 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hkey]
    exact sum_alternating_choose_succ m
  field_simp at hmul ⊢
  linarith [hmul]

/-- One-shift harmonic logarithmic power sum. -/
def selbergShiftedLogPowerHarmonic (m a c N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / c), Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ m / (d : ℝ)

/-- Exact binomial reduction of the shifted harmonic power sum to harmonic logarithmic moments. -/
theorem selbergShiftedLogPowerHarmonic_eq_moments
    (m : ℕ) {a c N : ℕ} (ha : 0 < a) (hN : 0 < N) :
    selbergShiftedLogPowerHarmonic m a c N =
      ∑ s ∈ Finset.range (m + 1),
        ((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s *
          (Real.log (N : ℝ) - Real.log (a : ℝ)) ^ (m - s) *
          harmonicLogWindowMoment s 0 (N / c) := by
  have hset : Finset.Ioc 0 (N / c) = Finset.Icc 1 (N / c) := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hexp : ∀ d ∈ Finset.Icc 1 (N / c),
      Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ m / (d : ℝ) =
        ∑ s ∈ Finset.range (m + 1),
          ((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s *
            (Real.log (N : ℝ) - Real.log (a : ℝ)) ^ (m - s) *
            (Real.log (d : ℝ) ^ s / (d : ℝ)) := by
    intro d hd
    have hd1 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hlogeq : Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) =
        (-Real.log (d : ℝ)) + (Real.log (N : ℝ) - Real.log (a : ℝ)) := by
      push_cast
      rw [Real.log_div hNR.ne' (by positivity), Real.log_mul haR.ne' hdR.ne']
      ring
    rw [hlogeq, add_pow, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    rw [neg_pow]
    ring
  rw [selbergShiftedLogPowerHarmonic, Finset.sum_congr rfl hexp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [harmonicLogWindowMoment, hset, Finset.mul_sum]

/-- **The shifted harmonic logarithmic power sum has leading coefficient `1/(m+1)`.** -/
theorem tendsto_selbergShiftedLogPowerHarmonic
    (m : ℕ) {a c : ℕ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      selbergShiftedLogPowerHarmonic m a c N / Real.log N ^ (m + 1))
      atTop (𝓝 (1 / ((m : ℝ) + 1))) := by
  have hshift := tendsto_log_sub_const_div_log_one (Real.log (a : ℝ))
  have hterms : ∀ s ∈ Finset.range (m + 1),
      Tendsto (fun N : ℕ =>
        ((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s *
          ((Real.log (N : ℝ) - Real.log (a : ℝ)) / Real.log (N : ℝ)) ^ (m - s) *
          (harmonicLogWindowMoment s 0 (N / c) / Real.log (N : ℝ) ^ (s + 1)))
        atTop (𝓝 (((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s * (1 : ℝ) ^ (m - s) *
          (1 / ((s : ℝ) + 1)))) := by
    intro s _
    exact ((tendsto_const_nhds.mul (hshift.pow (m - s))).mul
      (tendsto_harmonicLogWindowMoment_natDiv_div_log_pow s hc))
  have hsum := tendsto_finsetSum (Finset.range (m + 1)) hterms
  have hval : (∑ s ∈ Finset.range (m + 1),
      ((m.choose s : ℕ) : ℝ) * (-1 : ℝ) ^ s * (1 : ℝ) ^ (m - s) *
        (1 / ((s : ℝ) + 1))) = 1 / ((m : ℝ) + 1) := by
    rw [← sum_choose_alternating_div_succ m]
    apply Finset.sum_congr rfl
    intro s _
    rw [one_pow]
    ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergShiftedLogPowerHarmonic_eq_moments m ha hNpos, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hpow : Real.log (N : ℝ) ^ (m - s) * Real.log (N : ℝ) ^ (s + 1) =
      Real.log (N : ℝ) ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [div_pow, ← hpow]
  field_simp

/-- **The Selberg harmonic main term at every pair of logarithmic powers.** -/
theorem tendsto_selbergLogPowerHarmonicMain_div_log_pow
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergLogPowerHarmonicMain q r a b N / Real.log N ^ (q + r + 1))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1))) := by
  classical
  have hc : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  -- outer binomial: convert the `b`-shift into the `a`-shift
  have hmain : ∀ N : ℕ, 0 < N →
      selbergLogPowerHarmonicMain q r a b N =
        ∑ s ∈ Finset.range (r + 1),
          (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) * ((r.choose s : ℕ) : ℝ) *
            (Real.log (a : ℝ) - Real.log (b : ℝ)) ^ (r - s)) *
            selbergShiftedLogPowerHarmonic (q + s) a (max a b) N := by
    intro N hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [selbergLogPowerHarmonicMain]
    have hterm : ∀ d ∈ Finset.Icc 1 (N / max a b),
        (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) *
          Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
          Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r) / (d : ℝ) =
          ∑ s ∈ Finset.range (r + 1),
            (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) * ((r.choose s : ℕ) : ℝ) *
              (Real.log (a : ℝ) - Real.log (b : ℝ)) ^ (r - s)) *
              (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ (q + s) / (d : ℝ)) := by
      intro d hd
      have hd1 : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hb_eq : Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) =
          Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) +
            (Real.log (a : ℝ) - Real.log (b : ℝ)) := by
        push_cast
        rw [Real.log_div hNR.ne' (by positivity), Real.log_div hNR.ne' (by positivity),
          Real.log_mul haR.ne' hdR.ne', Real.log_mul hbR.ne' hdR.ne']
        ring
      rw [hb_eq, add_pow, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [pow_add]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [selbergShiftedLogPowerHarmonic, Finset.mul_sum]
  -- each lower-degree summand is killed by the normalization
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : ∀ s ∈ Finset.range (r + 1),
      Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ) ^ (r - s)) atTop
        (𝓝 (if s = r then (1 : ℝ) else 0)) := by
    intro s hs
    have hsr : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    by_cases hcase : s = r
    · subst hcase
      have hz : s - s = 0 := by omega
      rw [if_pos rfl]
      simp only [hz, pow_zero, div_one]
      exact tendsto_const_nhds
    · have hpos : r - s ≠ 0 := by omega
      have hscale : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (r - s)) atTop atTop :=
        (tendsto_pow_atTop hpos).comp hlogTop
      rw [if_neg hcase]
      exact hscale.const_div_atTop 1
  have hterms : ∀ s ∈ Finset.range (r + 1),
      Tendsto (fun N : ℕ =>
        (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) * ((r.choose s : ℕ) : ℝ) *
          (Real.log (a : ℝ) - Real.log (b : ℝ)) ^ (r - s)) *
          (selbergShiftedLogPowerHarmonic (q + s) a (max a b) N /
            Real.log (N : ℝ) ^ (q + s + 1)) *
          (1 / Real.log (N : ℝ) ^ (r - s)))
        atTop (𝓝 ((((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) * ((r.choose s : ℕ) : ℝ) *
          (Real.log (a : ℝ) - Real.log (b : ℝ)) ^ (r - s)) *
          (1 / (((q + s : ℕ) : ℝ) + 1)) * (if s = r then (1 : ℝ) else 0))) := by
    intro s hs
    exact (tendsto_const_nhds.mul
      (tendsto_selbergShiftedLogPowerHarmonic (q + s) ha hc)).mul (hinv s hs)
  have hsum := tendsto_finsetSum (Finset.range (r + 1)) hterms
  have hval : (∑ s ∈ Finset.range (r + 1),
      (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) * ((r.choose s : ℕ) : ℝ) *
        (Real.log (a : ℝ) - Real.log (b : ℝ)) ^ (r - s)) *
        (1 / (((q + s : ℕ) : ℝ) + 1)) * (if s = r then (1 : ℝ) else 0)) =
      (((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1) := by
    rw [Finset.sum_eq_single r]
    · rw [if_pos rfl, Nat.sub_self, pow_zero, Nat.choose_self]
      push_cast
      ring
    · intro s _ hne
      rw [if_neg hne]
      ring
    · intro hmem
      exact absurd (Finset.self_mem_range_succ r) hmem
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [hmain N hNpos, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  have hsr : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hpow : Real.log (N : ℝ) ^ (q + s + 1) * Real.log (N : ℝ) ^ (r - s) =
      Real.log (N : ℝ) ^ (q + r + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← hpow]
  field_simp

end

end RHTower.Sieve
