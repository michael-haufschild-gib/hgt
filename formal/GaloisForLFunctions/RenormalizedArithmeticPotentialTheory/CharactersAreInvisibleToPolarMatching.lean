import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremForCharacters
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingReadsTheDensityOfTheGauge

/-!
# Characters are invisible to polar matching

The matching law (`PolarMatchingReadsTheDensityOfTheGauge`) turns `A_ε(y) = κ log y + O(1)` into the
horizon divergence `κ ℓ(x)²` of the gauged step profiles. Mertens' theorem for characters computes
`κ` for the gauges of real characters.

Let `χ` be a non-trivial real character mod a prime `ℓ` (the Legendre symbol for odd `ℓ`).

* **The character gauge** (`charGauge`, `charGauge_isSignGauge`): `ε(n) = χ(n')`, with `n'` the
  `ℓ`-free part of `n`, is a sign gauge. It agrees with `χ` off `ℓ` and is `1` on the powers of `ℓ`
  (`charGauge_mul_vonMangoldt`).
* **Matching coefficient zero** (`charGauge_matching`): `A_ε(y) = Re A_χ(y) + Σ_{ℓ^k ≤ y} log ℓ/ℓ^k`,
  so `|A_ε(y)| ≤ C_χ + log ℓ/(ℓ − 1)`.
* **No horizon divergence** (`abs_charGaugeForm_stepProfile_le`): on uniform step profiles
  `|P_N(εx)| ≤ C Σ_{i,j} |c_i||c_j| H_{min(M_i, M_j)}`, with no polar term `ℓ(x)²`.

So the horizon counterterm is blind to characters. The divergence `ℓ(x)²` is carried by `ζ`
(`κ = 1`), flipped by Liouville (`κ = −1`) and annihilated by a character gauge, whose flipped and
unflipped primes have the same logarithmic density. The bound rests on `L(1, χ) ≠ 0`: at the
horizon, Dirichlet's theorem is the vanishing of a matching coefficient.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {ℓ : ℕ} [NeZero ℓ]

/-- The **character gauge** `ε(n) = Re χ(n')`, `n' = n/ℓ^{v_ℓ(n)}` the `ℓ`-free part of `n`. -/
def charGauge (χ : DirichletCharacter ℂ ℓ) (n : ℕ) : ℝ := (χ ((ordCompl[ℓ] n : ℕ) : ZMod ℓ)).re

omit [NeZero ℓ] in
/-- A real character is `±1` on units: `(Re χ(a))² = 1` for `a` coprime to `ℓ`. -/
theorem re_mul_self_eq_one (χ : DirichletCharacter ℂ ℓ) (hreal : ∀ a, (χ a).im = 0) {a : ℕ}
    (ha : a.Coprime ℓ) : (χ (a : ZMod ℓ)).re * (χ (a : ZMod ℓ)).re = 1 := by
  have hu : IsUnit (a : ZMod ℓ) := (ZMod.isUnit_iff_coprime a ℓ).mpr ha
  have hn : ‖χ (a : ZMod ℓ)‖ = 1 := by
    have h := DirichletCharacter.unit_norm_eq_one χ hu.unit
    rwa [IsUnit.unit_spec] at h
  have h := Complex.normSq_eq_norm_sq (χ (a : ZMod ℓ))
  rw [Complex.normSq_apply, hreal, hn] at h
  linarith

omit [NeZero ℓ] in
/-- **The character gauge is a sign gauge.** -/
theorem charGauge_isSignGauge (hℓ : ℓ.Prime) (χ : DirichletCharacter ℂ ℓ)
    (hreal : ∀ a, (χ a).im = 0) : IsSignGauge (charGauge χ) := by
  refine ⟨fun {m n} _ _ => ?_, fun {n} hn => ?_⟩
  · simp only [charGauge]
    rw [Nat.ordCompl_mul, Nat.cast_mul, map_mul, Complex.mul_re, hreal, hreal, mul_zero, sub_zero]
  · exact re_mul_self_eq_one χ hreal (Nat.coprime_ordCompl hℓ hn).symm

omit [NeZero ℓ] in
/-- `ε(t)Λ(t) = Re χ(t) Λ(t) + [ℓ ∣ t] Λ(t)`: the gauge is `χ` off `ℓ` and `1` on the powers of
`ℓ`. -/
theorem charGauge_mul_vonMangoldt (hℓ : ℓ.Prime) (χ : DirichletCharacter ℂ ℓ) (t : ℕ) :
    charGauge χ t * Λ t = (χ (t : ZMod ℓ)).re * Λ t + (if ℓ ∣ t then Λ t else 0) := by
  by_cases hΛ : Λ t = 0
  · simp [hΛ]
  by_cases hdvd : ℓ ∣ t
  · obtain ⟨k, hk, rfl⟩ := eq_pow_of_dvd_of_vonMangoldt_ne_zero hℓ hdvd hΛ
    have h1 : ordCompl[ℓ] (ℓ ^ k) = 1 := by
      rw [hℓ.factorization_pow, Finsupp.single_eq_same, Nat.div_self (pow_pos hℓ.pos k)]
    have h0 : χ ((ℓ ^ k : ℕ) : ZMod ℓ) = 0 := by
      refine MulChar.map_nonunit χ ?_
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_left_iff hk, Nat.coprime_self]
      exact hℓ.one_lt.ne'
    rw [if_pos hdvd, charGauge, h1, h0]
    simp
  · have h1 : ordCompl[ℓ] t = t := by
      rw [Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero, Nat.div_one]
    rw [if_neg hdvd, charGauge, h1, add_zero]

/-- **Character gauges have matching coefficient `0`**: `|A_ε(y)| ≤ C_χ + log ℓ/(ℓ − 1)`. -/
theorem charGauge_matching (hℓ : ℓ.Prime) (χ : DirichletCharacter ℂ ℓ) (hχ : χ ≠ 1)
    (hreal : ∀ a, (χ a).im = 0) :
    ∃ K : ℝ, IsSignGauge (charGauge χ) ∧
      ∀ y : ℕ, 1 ≤ y → |gaugeMertensSum (charGauge χ) y - 0 * Real.log y| ≤ K := by
  obtain ⟨C, hC⟩ := exists_norm_charMertensSum_le χ hχ
  refine ⟨C + Real.log ℓ / ((ℓ : ℝ) - 1), charGauge_isSignGauge hℓ χ hreal, fun y _ => ?_⟩
  -- `A_ε = Re A_χ + Σ_{ℓ ∣ t} Λ(t)/t`
  have hsplit : gaugeMertensSum (charGauge χ) y = (charMertensSum χ y).re +
      ∑ t ∈ Icc 1 y, (if ℓ ∣ t then Λ t / t else 0) := by
    rw [gaugeMertensSum, charMertensSum, Complex.re_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [charGauge_mul_vonMangoldt hℓ χ t]
    split_ifs <;> ring
  have h1 : |(charMertensSum χ y).re| ≤ C := (Complex.abs_re_le_norm _).trans (hC y)
  have h2 := sum_dvd_vonMangoldt_div_le hℓ (Icc 1 y)
  have h3 : 0 ≤ ∑ t ∈ Icc 1 y, (if ℓ ∣ t then Λ t / t else 0) :=
    sum_nonneg fun t _ => by
      split_ifs
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
      · exact le_rfl
  rw [hsplit, zero_mul, sub_zero, abs_le]
  rw [abs_le] at h1
  constructor <;> linarith [h1.1, h1.2]

/-- **No horizon divergence for character gauges**: on uniform step profiles the gauged prime form
is bounded by the mass, `|P_N(εx)| ≤ C Σ_{i,j} |c_i||c_j| H_{min(M_i, M_j)}`. -/
theorem abs_charGaugeForm_stepProfile_le (hℓ : ℓ.Prime) (χ : DirichletCharacter ℂ ℓ)
    (hχ : χ ≠ 1) (hreal : ∀ a, (χ a).im = 0) :
    ∃ K : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) → (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n => charGauge χ n * stepProfile c M n)| ≤
        (2 * K + 2 * Real.log 2 + 4) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) := by
  obtain ⟨K, hε, hA⟩ := charGauge_matching hℓ χ hχ hreal
  refine ⟨K, fun c M hM hM1 => ?_⟩
  have h := abs_gaugeForm_stepProfile_sub_le hε (κ := 0) (by simp) hA c M hM hM1
  simpa using h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
