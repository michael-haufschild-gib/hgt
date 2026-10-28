import GaloisForLFunctions.BezoutValuationIncidence.DilationJumpValuationClock
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanExpansion
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes

/-!
# Finite Ramanujan expansions of gcd profiles

Finite Möbius inversion first expands a function of `gcd(n,M)` in divisibility
indicators. The divisor sum of Ramanujan coefficients changes this to the
normalized conductor modes with conductors dividing `M`.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open BezoutValuationIncidence

/-- The finite divisor coefficient of an arbitrary real arithmetic profile. -/
def gcdProfileMobiusCoefficient (F : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ d.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • F x.2

theorem sum_gcdProfileMobiusCoefficient (F : ℕ → ℝ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ d.divisors, gcdProfileMobiusCoefficient F q) = F d :=
  ((ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (R := ℝ) (f := gcdProfileMobiusCoefficient F) (g := F)).2
      (by intro q hq; rfl)) d hd

/-- The real Ramanujan coefficients sum to the divisibility indicator times its modulus. -/
theorem sum_divisors_ramanujanLagCoefficient {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (∑ q ∈ d.divisors, ramanujanLagCoefficient q n) =
      if d ∣ n then (d : ℝ) else 0 := by
  have h := congrArg Complex.re (_root_.RHTower.pm_ramanujan_sum_divisors hn hd)
  simpa only [Complex.re_sum, ramanujanNaturalCoefficient_re_eq_lagCoefficient,
    apply_ite, Complex.natCast_re, Complex.zero_re] using h

private theorem divisors_eq_filter_of_dvd {d M : ℕ} (hd : d ≠ 0) (hM : M ≠ 0)
    (hdM : d ∣ M) : d.divisors = M.divisors.filter (fun q => q ∣ d) := by
  ext q
  simp only [Nat.mem_divisors, mem_filter]
  exact ⟨fun h => ⟨⟨h.1.trans hdM, hM⟩, h.1⟩, fun h => ⟨h.2, hd⟩⟩

/-- Möbius inversion on the gcd is a finite expansion in divisibility indicators. -/
theorem gcdProfile_eq_divisor_sum (F : ℕ → ℝ) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    F (n.gcd M) = ∑ d ∈ M.divisors,
      if d ∣ n then gcdProfileMobiusCoefficient F d else 0 := by
  classical
  rw [← sum_gcdProfileMobiusCoefficient F (Nat.gcd_pos_of_pos_right n hM)]
  have hset : (n.gcd M).divisors = M.divisors.filter (fun d => d ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdn, hdM⟩, _⟩
      exact ⟨⟨hdM, hM.ne'⟩, hdn⟩
    · rintro ⟨⟨hdM, _⟩, hdn⟩
      exact ⟨⟨hdn, hdM⟩, Nat.gcd_ne_zero_right hM.ne'⟩
  rw [hset, sum_filter]

/-- Every gcd profile is a finite linear combination of real Ramanujan coefficients. -/
theorem exists_gcdProfile_ramanujan_expansion (F : ℕ → ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ a : ℕ → ℝ, ∀ n : ℕ, 0 < n →
      F (n.gcd M) = ∑ q ∈ M.divisors, a q * ramanujanLagCoefficient q n := by
  classical
  let a : ℕ → ℝ := fun q => ∑ d ∈ M.divisors,
    if q ∣ d then gcdProfileMobiusCoefficient F d / (d : ℝ) else 0
  refine ⟨a, fun n hn => ?_⟩
  rw [gcdProfile_eq_divisor_sum F hM n]
  have hterm : ∀ d ∈ M.divisors,
      (if d ∣ n then gcdProfileMobiusCoefficient F d else 0) =
        ∑ q ∈ M.divisors,
          (if q ∣ d then gcdProfileMobiusCoefficient F d / (d : ℝ) else 0) *
            ramanujanLagCoefficient q n := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hq : d.divisors = M.divisors.filter (fun q => q ∣ d) :=
      divisors_eq_filter_of_dvd hd0.ne' hM.ne' (Nat.dvd_of_mem_divisors hd)
    have hs := sum_divisors_ramanujanLagCoefficient hn hd0
    calc
      _ = gcdProfileMobiusCoefficient F d / (d : ℝ) *
          (∑ q ∈ d.divisors, ramanujanLagCoefficient q n) := by
        rw [hs]
        by_cases hdn : d ∣ n
        · rw [if_pos hdn, if_pos hdn, div_mul_cancel₀ _ hdR]
        · rw [if_neg hdn, if_neg hdn, mul_zero]
      _ = _ := by
        rw [hq, sum_filter, mul_sum]
        refine sum_congr rfl fun q _ => ?_
        by_cases hqd : q ∣ d
        · rw [if_pos hqd, if_pos hqd]
        · rw [if_neg hqd, if_neg hqd, mul_zero, zero_mul]
  rw [sum_congr rfl hterm, Finset.sum_comm]
  exact sum_congr rfl fun q _ => (sum_mul _ _ _).symm

/-- Complete-period normalization preserves the finite conductor span. -/
theorem exists_gcdProfile_normalizedRamanujan_expansion
    (F : ℕ → ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ a : ℕ → ℝ, ∀ n : ℕ, 0 < n →
      F (n.gcd M) = ∑ q ∈ M.divisors, a q * normalizedRamanujanMode q n := by
  obtain ⟨a, ha⟩ := exists_gcdProfile_ramanujan_expansion F hM
  refine ⟨fun q => a q * Real.sqrt (q.totient : ℝ), fun n hn => ?_⟩
  rw [ha n hn]
  refine sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := Nat.pos_of_mem_divisors hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hs : Real.sqrt (q.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφ).ne'
  rw [normalizedRamanujanMode_eq_coefficient hq0]
  field_simp

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

