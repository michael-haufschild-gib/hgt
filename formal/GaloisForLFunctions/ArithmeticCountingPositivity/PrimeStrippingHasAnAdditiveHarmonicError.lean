import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# Prime stripping has an additive harmonic error

The exact divisibility recurrence expresses a one-prime stripping error
as two signed harmonic shells. Their unsigned mass bounds add over a
finite prime set, uniformly in the remaining sign pattern and the integer
horizon. The first Mertens bound makes the growing-cutoff cost logarithmic.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  RHTower.Sieve

open private harmonicMass_shell finiteFlip_unflipped_prime
  finiteFlipHarmonicDensity_insert from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity

/-- The additive harmonic shell cost of stripping a finite prime set. -/
def finitePrimeStrippingCost (F : Finset ℕ) : ℝ :=
  ∑ p ∈ F, 2 * (1 + Real.log p) / ((p : ℝ) + 1)

private theorem signGauge_mul (ω ν : ℕ → ℝ) (hω : IsSignGauge ω) (hν : IsSignGauge ν) :
    IsSignGauge (fun n => ω n * ν n) := by
  constructor
  · intro m n hm hn
    rw [hω.mul hm hn, hν.mul hm hn]
    ring
  · intro n hn
    calc
      _ = (ω n * ω n) * (ν n * ν n) := by ring
      _ = 1 := by rw [hω.mul_self hn, hν.mul_self hn, one_mul]

private theorem signed_harmonic_shell_le (ω : ℕ → ℝ) (hω : IsSignGauge ω)
    {M N : ℕ} (hMN : M ≤ N) :
    |gaugeHarmonicSum ω N - gaugeHarmonicSum ω M| ≤
      gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum (fun _ => 1) M := by
  have hsub : Icc 1 M ⊆ Icc 1 N := by
    intro n hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
  calc
    _ = |∑ n ∈ (Icc 1 N) \ (Icc 1 M), ω n / n| := by
      congr 1
      change (∑ n ∈ Icc 1 N, ω n / n) - (∑ n ∈ Icc 1 M, ω n / n) = _
      exact (eq_sub_iff_add_eq.mpr (sum_sdiff hsub)).symm
    _ ≤ ∑ n ∈ (Icc 1 N) \ (Icc 1 M), |ω n / n| := abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ (Icc 1 N) \ (Icc 1 M), (1 : ℝ) / n := by
      apply sum_congr rfl
      intro n hn
      have hnN := (mem_sdiff.mp hn).1
      have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hnN).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnN).1
      have habs : |ω n| = 1 := by
        rcases mul_self_eq_one_iff.mp (hω.mul_self hn0) with h | h <;> simp only [h, abs_one, abs_neg]
      rw [abs_div, habs, abs_of_pos hnR]
    _ = _ := eq_sub_iff_add_eq.mpr (sum_sdiff hsub)

private theorem prime_stripping_error (ω : ℕ → ℝ) (hω : IsSignGauge ω)
    {p : ℕ} (hp : p.Prime) (hωp : ω p = 1) (N : ℕ) :
    |gaugeHarmonicSum (fun n => finiteFlip {p} n * ω n) N -
        (((p : ℝ) - 1) / ((p : ℝ) + 1)) * gaugeHarmonicSum ω N| ≤
      2 * (1 + Real.log p) / ((p : ℝ) + 1) := by
  let ν : ℕ → ℝ := fun n => finiteFlip {p} n * ω n
  have hν : IsSignGauge ν := signGauge_mul _ _ (finiteFlip_isSignGauge {p}) hω
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpp : 0 < (p : ℝ) + 1 := by positivity
  have hνp : ν p = -1 := by
    simp only [ν, finiteFlip, prod_singleton, hp.factorization_self, pow_one, hωp, mul_one]
  have hsame {n : ℕ} (hn : ¬ p ∣ n) : ν n = ω n := by
    dsimp only [ν]
    rw [finiteFlip_eq_one_of_coprime (by simpa using hn), one_mul]
  have hdiff : gaugeHarmonicSum ω N - gaugeHarmonicSum ν N =
      (∑ n ∈ (Icc 1 N).filter (p ∣ ·), ω n / n) -
        ∑ n ∈ (Icc 1 N).filter (p ∣ ·), ν n / n := by
    rw [gaugeHarmonicSum, gaugeHarmonicSum, ← sum_sub_distrib,
      ← sum_sub_distrib, sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : p ∣ n
    · rw [if_pos hn]
    · rw [if_neg hn, hsame hn, sub_self]
  rw [gaugeHarmonicSum_multiples ω hω hp.pos,
    gaugeHarmonicSum_multiples ν hν hp.pos, hωp, hνp] at hdiff
  have hrec : (p : ℝ) * gaugeHarmonicSum ν N + gaugeHarmonicSum ν (N / p) =
      (p : ℝ) * gaugeHarmonicSum ω N - gaugeHarmonicSum ω (N / p) := by
    field_simp [hp0] at hdiff
    linarith only [hdiff]
  have he : ((p : ℝ) + 1) *
      (gaugeHarmonicSum ν N -
        (((p : ℝ) - 1) / ((p : ℝ) + 1)) * gaugeHarmonicSum ω N) =
      (gaugeHarmonicSum ν N - gaugeHarmonicSum ν (N / p)) +
        (gaugeHarmonicSum ω N - gaugeHarmonicSum ω (N / p)) := by
    calc
      _ = ((p : ℝ) + 1) * gaugeHarmonicSum ν N -
          ((p : ℝ) - 1) * gaugeHarmonicSum ω N := by
        field_simp [hpp.ne']
      _ = _ := by nlinarith only [hrec]
  have hνshell := (signed_harmonic_shell_le ν hν (Nat.div_le_self N p)).trans
    (harmonicMass_shell hp.pos N).2
  have hωshell := (signed_harmonic_shell_le ω hω (Nat.div_le_self N p)).trans
    (harmonicMass_shell hp.pos N).2
  have hbound : ((p : ℝ) + 1) *
      |gaugeHarmonicSum ν N -
        (((p : ℝ) - 1) / ((p : ℝ) + 1)) * gaugeHarmonicSum ω N| ≤
      2 * (1 + Real.log p) := by
    calc
      _ = |((p : ℝ) + 1) * (gaugeHarmonicSum ν N -
          (((p : ℝ) - 1) / ((p : ℝ) + 1)) * gaugeHarmonicSum ω N)| := by
        rw [abs_mul, abs_of_pos hpp]
      _ = _ := congrArg abs he
      _ ≤ _ := (abs_add_le _ _).trans (by linarith only [hνshell, hωshell])
  apply (le_div_iff₀ hpp).mpr
  nlinarith only [hbound]

private theorem strippingCost_nonneg (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    0 ≤ finitePrimeStrippingCost F := by
  apply sum_nonneg
  intro p hp
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg
    (by exact_mod_cast (hF p hp).one_le)
  positivity

/-- Stripping a finite prime set has an explicit additive harmonic error,
uniform in the horizon and every remaining multiplicative sign pattern. -/
theorem finiteFlip_harmonic_stripping_error (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (ω : ℕ → ℝ) (hω : IsSignGauge ω) (hfree : ∀ p ∈ F, ω p = 1) (N : ℕ) :
    |gaugeHarmonicSum (fun n => finiteFlip F n * ω n) N -
        finiteFlipHarmonicDensity F * gaugeHarmonicSum ω N| ≤ finitePrimeStrippingCost F := by
  classical
  revert hF hfree
  induction F using Finset.induction_on with
  | empty =>
      intro _ _
      simp only [finiteFlip, finiteFlipHarmonicDensity, finitePrimeStrippingCost,
        prod_empty, one_mul, sub_self, abs_zero, sum_empty, le_refl]
  | @insert p F hpF ih =>
      intro hF hfree
      have hp := hF p (mem_insert_self p F)
      have hF' : ∀ q ∈ F, q.Prime := fun q hq => hF q (mem_insert_of_mem hq)
      have hfree' : ∀ q ∈ F, ω q = 1 := fun q hq => hfree q (mem_insert_of_mem hq)
      let ν : ℕ → ℝ := fun n => finiteFlip F n * ω n
      have hν : IsSignGauge ν := signGauge_mul _ _ (finiteFlip_isSignGauge F) hω
      have hνp : ν p = 1 := by
        change finiteFlip F p * ω p = 1
        rw [finiteFlip_unflipped_prime hp hpF, hfree p (mem_insert_self p F), one_mul]
      have hstep := prime_stripping_error ν hν hp hνp N
      have hfun : (fun n => finiteFlip {p} n * ν n) =
          (fun n => finiteFlip (insert p F) n * ω n) := by
        funext n
        simp only [ν, finiteFlip, prod_singleton, prod_insert hpF]
        ring
      rw [hfun] at hstep
      have hI := ih hF' hfree'
      have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hpp : 0 < (p : ℝ) + 1 := by positivity
      have hc0 : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) :=
        (div_pos (sub_pos.mpr hpR) hpp).le
      have hc1 : ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤ 1 := by
        apply (div_le_one hpp).mpr
        linarith
      rw [finiteFlipHarmonicDensity_insert hpF, finitePrimeStrippingCost, sum_insert hpF]
      have he : gaugeHarmonicSum (fun n => finiteFlip (insert p F) n * ω n) N -
          ((((p : ℝ) - 1) / ((p : ℝ) + 1)) * finiteFlipHarmonicDensity F) *
            gaugeHarmonicSum ω N =
          (gaugeHarmonicSum (fun n => finiteFlip (insert p F) n * ω n) N -
            (((p : ℝ) - 1) / ((p : ℝ) + 1)) * gaugeHarmonicSum ν N) +
          (((p : ℝ) - 1) / ((p : ℝ) + 1)) *
            (gaugeHarmonicSum ν N - finiteFlipHarmonicDensity F * gaugeHarmonicSum ω N) := by
        ring
      rw [he]
      have hpaid := mul_le_mul_of_nonneg_left hI hc0
      have hcost := mul_le_mul_of_nonneg_right hc1 (strippingCost_nonneg F hF')
      calc
        _ ≤ |gaugeHarmonicSum (fun n => finiteFlip (insert p F) n * ω n) N -
              (((p : ℝ) - 1) / ((p : ℝ) + 1)) * gaugeHarmonicSum ν N| +
            (((p : ℝ) - 1) / ((p : ℝ) + 1)) *
              |gaugeHarmonicSum ν N - finiteFlipHarmonicDensity F * gaugeHarmonicSum ω N| := by
          simpa only [abs_mul, abs_of_nonneg hc0] using abs_add_le
            (gaugeHarmonicSum (fun n => finiteFlip (insert p F) n * ω n) N -
              (((p : ℝ) - 1) / ((p : ℝ) + 1)) * gaugeHarmonicSum ν N)
            ((((p : ℝ) - 1) / ((p : ℝ) + 1)) *
              (gaugeHarmonicSum ν N - finiteFlipHarmonicDensity F * gaugeHarmonicSum ω N))
        _ ≤ _ := by
          change _ ≤ 2 * (1 + Real.log p) / ((p : ℝ) + 1) + finitePrimeStrippingCost F
          nlinarith only [hstep, hpaid, hcost]

private theorem prime_stripping_cost_le {p : ℕ} (hp : p.Prime) :
    2 * (1 + Real.log p) / ((p : ℝ) + 1) ≤
      (2 * (1 + 1 / Real.log 2)) * (Real.log p / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpp : 0 < (p : ℝ) + 1 := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlogp : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hlog : 0 ≤ Real.log (p : ℝ) := (hlog2.trans_le hlogp).le
  have hratio : 1 ≤ Real.log (p : ℝ) / Real.log 2 := by
    apply (one_le_div hlog2).mpr
    exact hlogp
  have hnum : 1 + Real.log (p : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log p := by
    calc
      _ ≤ Real.log (p : ℝ) / Real.log 2 + Real.log p := by linarith only [hratio]
      _ = _ := by ring
  calc
    _ ≤ 2 * (1 + Real.log p) / (p : ℝ) := by
      rw [div_le_div_iff₀ hpp hp0]
      nlinarith only [hlog]
    _ ≤ (2 * ((1 + 1 / Real.log 2) * Real.log p)) / (p : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num)) hp0.le
    _ = _ := by ring

private theorem strippingCost_le_log_cutoff (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) {Q : ℕ} (hQ : 1 ≤ Q) (hcut : ∀ p ∈ F, p ≤ Q) :
    finitePrimeStrippingCost F ≤
      (2 * (1 + 1 / Real.log 2)) * (Real.log (Q : ℝ) + mertensFirstConst) := by
  have hC : 0 ≤ 2 * (1 + 1 / Real.log 2) := by
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    positivity
  have hsum : (∑ p ∈ F, Real.log p / (p : ℝ)) ≤ mertensA Q := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Nat.mem_primesLE.mpr ⟨hcut p hp, hF p hp⟩
    · intro p hp _
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
      exact div_nonneg (Real.log_nonneg hp1) (Nat.cast_nonneg _)
  have hM : mertensA Q ≤ Real.log (Q : ℝ) + mertensFirstConst := by
    have h := (abs_le.mp (abs_mertensA_sub_log_le hQ)).2
    linarith only [h]
  calc
    _ ≤ ∑ p ∈ F, (2 * (1 + 1 / Real.log 2)) * (Real.log p / (p : ℝ)) :=
      sum_le_sum fun p hp => prime_stripping_cost_le (hF p hp)
    _ = (2 * (1 + 1 / Real.log 2)) * ∑ p ∈ F, Real.log p / (p : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.trans hM) hC

/-- The harmonic stripping error is logarithmic in the largest allowed
prime, uniformly in the integer horizon and the residual sign pattern. -/
theorem finiteFlip_harmonic_stripping_error_le_log_cutoff (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) (ω : ℕ → ℝ) (hω : IsSignGauge ω)
    (hfree : ∀ p ∈ F, ω p = 1) {Q : ℕ} (hQ : 1 ≤ Q)
    (hcut : ∀ p ∈ F, p ≤ Q) (N : ℕ) :
    |gaugeHarmonicSum (fun n => finiteFlip F n * ω n) N -
        finiteFlipHarmonicDensity F * gaugeHarmonicSum ω N| ≤
      (2 * (1 + 1 / Real.log 2)) * (Real.log (Q : ℝ) + mertensFirstConst) :=
  (finiteFlip_harmonic_stripping_error F hF ω hω hfree N).trans
    (strippingCost_le_log_cutoff F hF hQ hcut)

end GaloisForLFunctions.ArithmeticCountingPositivity
