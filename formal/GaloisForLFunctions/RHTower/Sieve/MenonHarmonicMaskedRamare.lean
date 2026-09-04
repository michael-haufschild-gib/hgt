import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamare
import GaloisForLFunctions.RHTower.Sieve.JointOmegaFactorisation

/-!
# Harmonic Ramaré factorization after an earlier non-rough projection

Menon's two-range argument first keeps integers carrying a prime from an initial range, then
factorizes that projected polynomial over a disjoint final prime range.  Multiplication by a final
prime does not change the initial-range mask, so the final prime factor remains the ordinary
harmonic prime polynomial.  This file records that exact identity, including its final-range rough
remainder, without replacing either prime range or any finite support.
-/

namespace RHTower.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Harmonic Möbius coefficient restricted to integers carrying an initial-range prime. -/
def harmonicNonRoughMoebiusC (P₀ : Finset ℕ) (n : ℕ) : ℂ :=
  if primeFactorsIn P₀ n = ∅ then 0 else harmonicMoebiusC n

/-- Phase-carrying form of the initial-range non-rough harmonic coefficient. -/
def harmonicNonRoughMoebiusPhase (P₀ : Finset ℕ) (w : ℝ) (n : ℕ) : ℂ :=
  if primeFactorsIn P₀ n = ∅ then 0 else harmonicMoebiusPhase w n

/-- The masked harmonic Dirichlet polynomial is the sum of its masked phases. -/
theorem logPoly_harmonicNonRoughMoebius_eq_sum_phase
    (P₀ s : Finset ℕ) (w : ℝ) :
    logPoly (harmonicNonRoughMoebiusC P₀) s w =
      ∑ n ∈ s, harmonicNonRoughMoebiusPhase P₀ w n := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [harmonicNonRoughMoebiusC, harmonicNonRoughMoebiusPhase]
  by_cases hn : primeFactorsIn P₀ n = ∅
  · simp [hn]
  · simp only [hn, if_false, harmonicMoebiusPhase, harmonicMoebiusC, moebiusPhase,
      unitLogPhase]
    ring

/-- Masking coefficients is exactly restriction of the finite support. -/
theorem logPoly_harmonicNonRoughMoebius_eq_filter
    (P₀ s : Finset ℕ) (w : ℝ) :
    logPoly (harmonicNonRoughMoebiusC P₀) s w =
      logPoly harmonicMoebiusC {n ∈ s | primeFactorsIn P₀ n ≠ ∅} w := by
  rw [logPoly, logPoly, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [harmonicNonRoughMoebiusC]
  by_cases hn : primeFactorsIn P₀ n = ∅
  · simp [hn]
  · simp [hn]

/-- Initial non-rough projection is exactly the initial harmonic Ramaré bilinear form. -/
theorem logPoly_harmonicNonRoughMoebius_eq_harmonicRamareBilinear
    {P₀ : Finset ℕ} (hP₀prime : ∀ p ∈ P₀, p.Prime) (s : Finset ℕ) (w : ℝ) :
    logPoly (harmonicNonRoughMoebiusC P₀) s w =
      harmonicRamareBilinear P₀ s w := by
  classical
  have hsplit := logPoly_harmonicMoebius_eq_ramare_add_rough hP₀prime s w
  have hpartition :
      logPoly harmonicMoebiusC s w =
        logPoly harmonicMoebiusC {n ∈ s | primeFactorsIn P₀ n ≠ ∅} w +
          logPoly harmonicMoebiusC {n ∈ s | primeFactorsIn P₀ n = ∅} w := by
    rw [logPoly, logPoly, logPoly]
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not s
      (fun n => primeFactorsIn P₀ n = ∅)
      (fun n => harmonicMoebiusC n *
        Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I))).symm
  rw [logPoly_harmonicNonRoughMoebius_eq_filter]
  calc
    logPoly harmonicMoebiusC {n ∈ s | primeFactorsIn P₀ n ≠ ∅} w =
        logPoly harmonicMoebiusC s w -
          logPoly harmonicMoebiusC {n ∈ s | primeFactorsIn P₀ n = ∅} w := by
            rw [hpartition]
            ring
    _ = harmonicRamareBilinear P₀ s w := by rw [hsplit]; ring

/-- A final prime outside the initial range preserves the initial non-rough mask. -/
theorem harmonicNonRoughMoebiusPhase_mul_prime_not_mem
    {P₀ : Finset ℕ} (hP₀prime : ∀ q ∈ P₀, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP₀ : p ∉ P₀) (w : ℝ) (m : ℕ)
    (hpm : ¬ p ∣ m) :
    harmonicNonRoughMoebiusPhase P₀ w (p * m) =
      harmonicMoebiusPhase w p * harmonicNonRoughMoebiusPhase P₀ w m := by
  rw [harmonicNonRoughMoebiusPhase, harmonicNonRoughMoebiusPhase,
    primeFactorsIn_mul_prime_not_mem hP₀prime hp hpP₀]
  by_cases hm : primeFactorsIn P₀ m = ∅
  · simp [hm]
  · simp only [hm, if_false]
    exact harmonicMoebiusPhase_mul_of_coprime w p m (hp.coprime_iff_not_dvd.mpr hpm)

/-- Final-range cofactor coefficient retaining the initial non-rough mask. -/
def harmonicNonRoughRamareCofactorCoeff
    (P₀ P : Finset ℕ) (m : ℕ) : ℂ :=
  harmonicNonRoughMoebiusC P₀ m / (((primeFactorsIn P m).card : ℂ) + 1)

/-- The masked damped cofactor phase is its literal Dirichlet polynomial. -/
theorem sum_harmonicNonRoughMoebiusPhase_div_eq_logPoly
    (P₀ P U : Finset ℕ) (w : ℝ) :
    ∑ m ∈ U, harmonicNonRoughMoebiusPhase P₀ w m /
        (((primeFactorsIn P m).card : ℂ) + 1) =
      logPoly (harmonicNonRoughRamareCofactorCoeff P₀ P) U w := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [harmonicNonRoughMoebiusPhase, harmonicNonRoughRamareCofactorCoeff,
    harmonicNonRoughMoebiusC]
  by_cases hm : primeFactorsIn P₀ m = ∅
  · simp [hm]
  · simp only [hm, if_false, harmonicMoebiusPhase, harmonicMoebiusC, moebiusPhase,
      unitLogPhase]
    ring

/-- Final Ramaré bilinear form of the initial-range non-rough harmonic polynomial. -/
def harmonicNonRoughRamareBilinear
    (P₀ P s : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ p ∈ P, harmonicMoebiusPhase w p *
    logPoly (harmonicNonRoughRamareCofactorCoeff P₀ P)
      {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w

/-- Exact second Ramaré factorization over a prime range disjoint from the initial mask. -/
theorem logPoly_harmonicNonRoughMoebius_eq_ramare_add_rough
    {P₀ P : Finset ℕ}
    (hP₀prime : ∀ q ∈ P₀, q.Prime)
    (hPprime : ∀ p ∈ P, p.Prime) (hdisj : Disjoint P₀ P)
    (s : Finset ℕ) (w : ℝ) :
    logPoly (harmonicNonRoughMoebiusC P₀) s w =
      harmonicNonRoughRamareBilinear P₀ P s w +
        logPoly (harmonicNonRoughMoebiusC P₀)
          {n ∈ s | primeFactorsIn P n = ∅} w := by
  classical
  have hinner : ∀ p ∈ P,
      ∑ n ∈ {n ∈ s | p ∣ n},
          harmonicNonRoughMoebiusPhase P₀ w n /
            ((primeFactorsIn P n).card : ℂ) =
        harmonicMoebiusPhase w p *
          ∑ m ∈ {m ∈ ramareCofactorSet s p | ¬ p ∣ m},
            harmonicNonRoughMoebiusPhase P₀ w m /
              (((primeFactorsIn P m).card : ℂ) + 1) := by
    intro p hp
    have hprime := hPprime p hp
    have hpP₀ : p ∉ P₀ := Finset.disjoint_right.1 hdisj hp
    have hreindex :
        ∑ n ∈ {n ∈ s | p ∣ n},
            harmonicNonRoughMoebiusPhase P₀ w n /
              ((primeFactorsIn P n).card : ℂ) =
          ∑ m ∈ ramareCofactorSet s p,
            harmonicNonRoughMoebiusPhase P₀ w (p * m) /
              ((primeFactorsIn P (p * m)).card : ℂ) :=
      (sum_div_image_complex p {n ∈ s | p ∣ n}
        (fun n hn => (Finset.mem_filter.1 hn).2)
        (fun n => harmonicNonRoughMoebiusPhase P₀ w n /
          ((primeFactorsIn P n).card : ℂ))).symm
    rw [hreindex]
    have hsplit := sum_ramare_bilinear_split_complex hPprime
      (fun a b hab => harmonicMoebiusPhase_mul_of_coprime w a b hab)
      hprime hp (ramareCofactorSet s p)
    have hrewrite : ∀ m ∈ {m ∈ ramareCofactorSet s p | ¬ p ∣ m},
        harmonicNonRoughMoebiusPhase P₀ w (p * m) /
            ((primeFactorsIn P (p * m)).card : ℂ) =
          harmonicMoebiusPhase w p *
            (harmonicNonRoughMoebiusPhase P₀ w m /
              (((primeFactorsIn P m).card : ℂ) + 1)) := by
      intro m hm
      have hpm : ¬ p ∣ m := (Finset.mem_filter.1 hm).2
      rw [harmonicNonRoughMoebiusPhase_mul_prime_not_mem hP₀prime hprime hpP₀ w m hpm,
        card_primeFactorsIn_mul_prime hPprime hprime hp hpm]
      push_cast
      ring
    have hzero :
        ∑ m ∈ {m ∈ ramareCofactorSet s p | p ∣ m},
            harmonicNonRoughMoebiusPhase P₀ w (p * m) /
              ((primeFactorsIn P (p * m)).card : ℂ) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [harmonicNonRoughMoebiusPhase]
      split_ifs
      · simp
      · rw [harmonicMoebiusPhase, moebiusPhase_eq_zero_of_dvd hprime
          (Finset.mem_filter.1 hm).2 w, zero_div, zero_div]
    have hpartition :
        (∑ m ∈ ramareCofactorSet s p,
            harmonicNonRoughMoebiusPhase P₀ w (p * m) /
              ((primeFactorsIn P (p * m)).card : ℂ)) =
          (∑ m ∈ {m ∈ ramareCofactorSet s p | ¬ p ∣ m},
            harmonicNonRoughMoebiusPhase P₀ w (p * m) /
              ((primeFactorsIn P (p * m)).card : ℂ)) +
          ∑ m ∈ {m ∈ ramareCofactorSet s p | p ∣ m},
            harmonicNonRoughMoebiusPhase P₀ w (p * m) /
              ((primeFactorsIn P (p * m)).card : ℂ) := by
      rw [add_comm]
      exact (Finset.sum_filter_add_sum_filter_not
        (ramareCofactorSet s p) (fun m => p ∣ m) _).symm
    rw [hpartition, hzero, add_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl hrewrite
  rw [logPoly_harmonicNonRoughMoebius_eq_sum_phase,
    sum_eq_ramare_add_rough_complex P s (harmonicNonRoughMoebiusPhase P₀ w),
    harmonicNonRoughRamareBilinear]
  have hb :
      (∑ p ∈ P, ∑ n ∈ {n ∈ s | p ∣ n},
          harmonicNonRoughMoebiusPhase P₀ w n /
            ((primeFactorsIn P n).card : ℂ)) =
        ∑ p ∈ P, harmonicMoebiusPhase w p *
          logPoly (harmonicNonRoughRamareCofactorCoeff P₀ P)
            {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hinner p hp, sum_harmonicNonRoughMoebiusPhase_div_eq_logPoly]
  rw [hb, logPoly_harmonicNonRoughMoebius_eq_sum_phase]

/-- The masked final cofactor remains pointwise dominated by `1/m`. -/
theorem norm_harmonicNonRoughRamareCofactorCoeff_le_inv
    (P₀ P : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    ‖harmonicNonRoughRamareCofactorCoeff P₀ P m‖ ≤ 1 / (m : ℝ) := by
  rw [harmonicNonRoughRamareCofactorCoeff, norm_div]
  have hden : 1 ≤ ‖(((primeFactorsIn P m).card : ℂ) + 1)‖ := by
    rw [show (((primeFactorsIn P m).card : ℂ) + 1) =
      (((primeFactorsIn P m).card + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    exact_mod_cast Nat.le_add_left 1 (primeFactorsIn P m).card
  have hmu : ‖harmonicNonRoughMoebiusC P₀ m‖ ≤ 1 / (m : ℝ) := by
    rw [harmonicNonRoughMoebiusC]
    split_ifs
    · have hzero : (0 : ℝ) ≤ 1 / (m : ℝ) :=
        one_div_nonneg.mpr (Nat.cast_nonneg m)
      simpa using hzero
    · rw [harmonicMoebiusC, norm_div, Complex.norm_intCast, Complex.norm_natCast]
      have hmoebius : ‖(ArithmeticFunction.moebius m : ℤ)‖ ≤ 1 := by
        simpa [Int.norm_eq_abs] using abs_moebius_real_le_one m
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact (div_le_div_of_nonneg_right hmoebius hmR.le).trans_eq (by ring)
  have hinv : (0 : ℝ) ≤ 1 / (m : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg m)
  exact (div_le_div_of_nonneg_right hmu (norm_nonneg _)).trans
    (by simpa only [div_one] using div_le_self hinv hden)

end

end RHTower.Sieve
