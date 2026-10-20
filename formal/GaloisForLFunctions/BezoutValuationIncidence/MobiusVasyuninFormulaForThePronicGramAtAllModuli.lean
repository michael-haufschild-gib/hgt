import GaloisForLFunctions.BezoutValuationIncidence.VasyuninReciprocityForAllModuliFromPronicCovariance

/-!
# The Möbius–Vasyunin formula for the pronic Gram at all moduli

The Ramanujan primitives of the divisors of `m` sum to a floor: since `Σ_{d ∣ m} c_d(n) = m [m ∣ n]`,

`Σ_{d ∣ m} R_d(M) = m ⌊M/m⌋`,  so  `M mod m = -Σ_{d ∣ m, d ≥ 2} R_d(M)`

(the divisor `d = 1` contributes `R_1(M) = M`). Taking pronic second moments,

`S(m₁, m₂) = Σ_{d₁ ∣ m₁, d₂ ∣ m₂, d₁, d₂ ≥ 2} G(d₁, d₂)`,

where `S` is the Vasyunin second moment of residues and `G` the pronic Gram of Ramanujan primitives.
Möbius inversion in both variables gives every entry of the pronic Gram explicitly:

`G(m₁, m₂) = Σ_{a₁ b₁ = m₁} Σ_{a₂ b₂ = m₂} μ(a₁) μ(a₂) S(b₁, b₂)`,  `m₁, m₂ ≥ 2`,

with `S(b₁, b₂) = ((b₁-1) log b₂ + (b₂-1) log b₁)/2 - (π/2)(V(b₂,b₁) - V(1,b₁) + V(b₁,b₂) - V(1,b₂))`.
The pronic Gram of the divisor theory is a Möbius transform of the Nyman–Beurling cotangent sums.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The Ramanujan primitive in Ramanujan sums. -/
theorem pmRamanujanPrimitive_re_eq_sum (d M : ℕ) (hd : 0 < d) :
    (pmRamanujanPrimitive d M).re = ∑ n ∈ Icc 1 M, ramanujanLagCoefficient d n := by
  unfold pmRamanujanPrimitive
  rw [Complex.re_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [d4BMRamanujanNaturalCoefficient_eq_sum_primitiveRoots (mem_Icc.mp hn).1 hd,
    sum_primitiveRoots_pow n hd, Complex.ofReal_re, ramanujanLagWeight_eq_ramanujanLagCoefficient]

/-- **The divisor sum of Ramanujan primitives.** `Σ_{d ∣ m} R_d(M) = m ⌊M/m⌋`. -/
theorem sum_divisors_pmRamanujanPrimitive_re (m M : ℕ) :
    ∑ d ∈ m.divisors, (pmRamanujanPrimitive d M).re = (m : ℝ) * (M / m : ℕ) := by
  rw [sum_congr rfl fun d hd => pmRamanujanPrimitive_re_eq_sum d M (Nat.pos_of_mem_divisors hd),
    sum_comm]
  simp_rw [sum_divisors_ramanujanLagCoefficient]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hIcc : Icc 1 M = Ioc 0 M := by ext; simp only [mem_Icc, mem_Ioc]; omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  ring

/-- **The residue in Ramanujan primitives.** `M mod m = -Σ_{d ∣ m, d ≠ 1} R_d(M)`. -/
theorem natMod_eq_neg_sum_pmRamanujanPrimitive {m : ℕ} (hm : 0 < m) (M : ℕ) :
    ((M % m : ℕ) : ℝ) = -∑ d ∈ m.divisors.erase 1, (pmRamanujanPrimitive d M).re := by
  have h := sum_divisors_pmRamanujanPrimitive_re m M
  rw [← add_sum_erase _ _ (Nat.one_mem_divisors.mpr hm.ne'), pmRamanujanPrimitive_re_eq_sum 1 M one_pos] at h
  have hcoef : ∀ n, ramanujanLagCoefficient 1 n = 1 := fun n => by
    simp [ramanujanLagCoefficient, moebiusReal]
  have h1 : ∑ n ∈ Icc 1 M, ramanujanLagCoefficient 1 n = M := by
    rw [sum_congr rfl fun n _ => hcoef n]
    simp
  rw [h1] at h
  have hdiv : ((M % m : ℕ) : ℝ) + (m : ℝ) * (M / m : ℕ) = M := by exact_mod_cast Nat.mod_add_div M m
  linarith

/-- **The Vasyunin moment as a divisor sum of pronic Gram entries.** -/
theorem vasyuninSecondMoment_eq_sum_divisors_gram {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    vasyuninSecondMoment m₁ m₂ = ∑ d₁ ∈ m₁.divisors.erase 1, ∑ d₂ ∈ m₂.divisors.erase 1,
      pmRamanujanPrimitiveGram d₁ d₂ := by
  have hgt : ∀ {m d : ℕ}, d ∈ m.divisors.erase 1 → 1 < d := fun hd => by
    obtain ⟨hne, hdm⟩ := mem_erase.mp hd
    have := Nat.pos_of_mem_divisors hdm
    omega
  have hS : HasSum (fun M : ℕ => ∑ d₁ ∈ m₁.divisors.erase 1, ∑ d₂ ∈ m₂.divisors.erase 1,
      pmRamanujanPrimitiveGramTerm d₁ d₂ M)
      (∑ d₁ ∈ m₁.divisors.erase 1, ∑ d₂ ∈ m₂.divisors.erase 1, pmRamanujanPrimitiveGram d₁ d₂) :=
    hasSum_sum fun d₁ hd₁ => hasSum_sum fun d₂ hd₂ =>
      (summable_pmRamanujanPrimitiveGramTerm (hgt hd₁) (hgt hd₂)).hasSum
  refine (hasSum_natMod_mul_natMod_vasyunin h₁ h₂).unique (hS.congr_fun fun M => ?_)
  rw [natMod_eq_neg_sum_pmRamanujanPrimitive h₁, natMod_eq_neg_sum_pmRamanujanPrimitive h₂,
    neg_mul_neg, sum_mul_sum, sum_div]
  refine sum_congr rfl fun d₁ _ => ?_
  rw [sum_div]
  rfl

/-- The pronic Gram extended by zero at the modulus `1`. -/
def gramExtended (d₁ d₂ : ℕ) : ℝ := if d₁ = 1 ∨ d₂ = 1 then 0 else pmRamanujanPrimitiveGram d₁ d₂

theorem sum_divisors_gramExtended {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    ∑ d₁ ∈ m₁.divisors, ∑ d₂ ∈ m₂.divisors, gramExtended d₁ d₂ = vasyuninSecondMoment m₁ m₂ := by
  rw [vasyuninSecondMoment_eq_sum_divisors_gram h₁ h₂,
    ← add_sum_erase _ _ (Nat.one_mem_divisors.mpr h₁.ne')]
  rw [show ∑ d₂ ∈ m₂.divisors, gramExtended 1 d₂ = 0 from
    sum_eq_zero fun d₂ _ => by simp [gramExtended], zero_add]
  refine sum_congr rfl fun d₁ hd₁ => ?_
  rw [← add_sum_erase _ _ (Nat.one_mem_divisors.mpr h₂.ne'),
    show gramExtended d₁ 1 = 0 by simp [gramExtended], zero_add]
  refine sum_congr rfl fun d₂ hd₂ => ?_
  rw [gramExtended, if_neg]
  rintro (h | h)
  · exact (mem_erase.mp hd₁).1 h
  · exact (mem_erase.mp hd₂).1 h

/-- **The Möbius–Vasyunin formula.** For `m₁, m₂ ≥ 2`,
`G(m₁, m₂) = Σ_{a₁b₁ = m₁} Σ_{a₂b₂ = m₂} μ(a₁) μ(a₂) S(b₁, b₂)`. -/
theorem pmRamanujanPrimitiveGram_eq_mobius_vasyunin {m₁ m₂ : ℕ} (h₁ : 2 ≤ m₁) (h₂ : 2 ≤ m₂) :
    pmRamanujanPrimitiveGram m₁ m₂ =
      ∑ x ∈ m₁.divisorsAntidiagonal, ∑ y ∈ m₂.divisorsAntidiagonal,
        ((μ x.1 : ℤ) : ℝ) * ((μ y.1 : ℤ) : ℝ) * vasyuninSecondMoment x.2 y.2 := by
  -- invert in the first variable at every fixed second modulus
  have hfirst : ∀ n₂ > 0, ∀ n₁ > 0, ∑ x ∈ n₁.divisorsAntidiagonal,
      ((μ x.1 : ℤ) : ℝ) * vasyuninSecondMoment x.2 n₂ =
        ∑ d₂ ∈ n₂.divisors, gramExtended n₁ d₂ := by
    intro n₂ hn₂
    refine (sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
      (f := fun n₁ => ∑ d₂ ∈ n₂.divisors, gramExtended n₁ d₂)
      (g := fun n₁ => vasyuninSecondMoment n₁ n₂)).mp ?_
    intro n₁ hn₁
    exact sum_divisors_gramExtended hn₁ hn₂
  -- then in the second variable
  have hsecond : ∀ n₂ > 0, ∑ y ∈ n₂.divisorsAntidiagonal,
      ((μ y.1 : ℤ) : ℝ) * (∑ x ∈ m₁.divisorsAntidiagonal,
        ((μ x.1 : ℤ) : ℝ) * vasyuninSecondMoment x.2 y.2) = gramExtended m₁ n₂ := by
    have hinv := (sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
      (f := fun n₂ => gramExtended m₁ n₂)
      (g := fun n₂ => ∑ x ∈ m₁.divisorsAntidiagonal,
        ((μ x.1 : ℤ) : ℝ) * vasyuninSecondMoment x.2 n₂)).mp fun n₂ hn₂ =>
      (hfirst n₂ hn₂ m₁ (by omega)).symm
    intro n₂ hn₂
    have h := hinv n₂ hn₂
    refine Eq.trans ?_ h
    refine sum_congr rfl fun y hy => ?_
    have hy2 : 0 < y.2 := Nat.pos_of_ne_zero fun h0 => by
      have := Nat.mem_divisorsAntidiagonal.mp hy
      rw [h0, mul_zero] at this
      omega
    rfl
  have h := hsecond m₂ (by omega)
  rw [gramExtended, if_neg (by omega)] at h
  rw [← h, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun x _ => by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
