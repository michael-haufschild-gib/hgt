import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global

/-! Inertia fixes the roots of unity of order prime to the residue characteristic.
Its action on a prime-to-characteristic radical therefore gives a character
independent of the choice of root. -/

noncomputable section

open IsLocalRing
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

variable {K : Type} [Field K] (A : ValuationSubring K) {p : ℕ} [Fact p.Prime]

theorem natCast_valuation_not_lt_one (hp : A.valuation (p : K) < 1) {n : ℕ}
    (hn : p.Coprime n) : ¬ A.valuation (n : K) < 1 := by
  have hmem {j : ℕ} (hj : A.valuation (j : K) < 1) : (j : ResidueField A) = 0 := by
    rw [← map_natCast (residue A), residue_eq_zero_iff]
    exact (A.valuation_lt_one_iff _).mpr (by simpa only [SubringClass.coe_natCast] using hj)
  letI : CharP (ResidueField A) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (hmem hp)
  intro h
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hn
    ((CharP.cast_eq_zero_iff (ResidueField A) p n).mp (hmem h))

theorem coprime_pow_sub_one {d : ℕ} (hd : 0 < d) : p.Coprime (p ^ d - 1) := by
  have hp : p.Prime := Fact.out
  refine hp.coprime_iff_not_dvd.mpr fun h => ?_
  have hdvd := Nat.dvd_sub (dvd_pow_self p hd.ne') h
  rw [Nat.sub_sub_self (Nat.one_lt_pow hd.ne' hp.one_lt).le] at hdvd
  exact hp.not_dvd_one hdvd

section Ratios

variable {E : Type} [Field E] [NumberField E] [Algebra E K]

/-- A root of unity of order prime to the residue characteristic is fixed by inertia. -/
theorem inertia_fixes_rootOfUnity (hp : A.valuation (p : K) < 1) {σ : G E K}
    (hσ : σ ∈ Ine (F := E) A) {n : ℕ} (hn : 0 < n) (hpn : p.Coprime n)
    {μ : K} (hμ : μ ^ n = 1) : σ μ = μ := by
  apply eq_of_pow_eq_one A (natCast_valuation_not_lt_one A hp hpn)
    (show σ μ ^ n = 1 by rw [← map_pow, hμ, map_one]) hμ
  exact hσ.2 μ (valuation_eq_one_of_pow_eq_one A hn.ne' hμ).le

omit [NumberField E] in
theorem ratio_pow_eq_one (σ : G E K) {g n : ℕ} (hg : (g : K) ≠ 0)
    {y : K} (hy : y ^ n = (g : K)) : (σ y / y) ^ n = 1 := by
  rw [div_pow, ← map_pow, hy, map_natCast, div_self hg]

variable [CharZero K] {σ : G E K} (hp : A.valuation (p : K) < 1)
variable (hσ : σ ∈ Ine (F := E) A) {n : ℕ} (hn : 0 < n) (hpn : p.Coprime n)

include hn in
private theorem ne_zero_of_radical {y : K} (hy : y ^ n = (p : K)) : y ≠ 0 := by
  rintro rfl
  rw [zero_pow hn.ne'] at hy
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hy.symm

include hp hσ hn hpn

theorem ratio_indep {y z : K} (hy : y ^ n = (p : K)) (hz : z ^ n = (p : K)) :
    σ z / z = σ y / y := by
  have hy0 := ne_zero_of_radical hn hy
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨μ, rfl⟩ : ∃ μ, z = μ * y := ⟨z / y, (div_mul_cancel₀ z hy0).symm⟩
  have hμ : μ ^ n = 1 := by
    rw [mul_pow, hy] at hz
    exact (mul_eq_right₀ hp0).mp hz
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hμ
    exact zero_ne_one hμ
  rw [map_mul, inertia_fixes_rootOfUnity A hp hσ hn hpn hμ]
  field_simp

theorem ratio_mul (τ : G E K) {y : K} (hy : y ^ n = (p : K)) :
    (σ * τ) y / y = (σ y / y) * (τ y / y) := by
  have hy0 := ne_zero_of_radical hn hy
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let a := τ y / y
  have ha : a ^ n = 1 := ratio_pow_eq_one τ hp0 hy
  have hτ : τ y = a * y := (div_mul_cancel₀ _ hy0).symm
  change σ (τ y) / y = (σ y / y) * a
  rw [hτ, map_mul, inertia_fixes_rootOfUnity A hp hσ hn hpn ha, mul_div_assoc, mul_comm a]

theorem ratio_npow {y : K} (hy : y ^ n = (p : K)) (k : ℕ) :
    (σ ^ k) y / y = (σ y / y) ^ k := by
  have hy0 := ne_zero_of_radical hn hy
  induction k with
  | zero => simp [hy0]
  | succ k ih =>
    rw [pow_succ, ratio_mul A hp (pow_mem hσ k) hn hpn σ hy, ih, pow_succ]

end Ratios
end GlobalTheory.TameKummer
