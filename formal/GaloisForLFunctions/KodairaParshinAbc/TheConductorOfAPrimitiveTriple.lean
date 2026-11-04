import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfAnAbcTriple
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheWallIsADirichletInversion

/-!
# The conductor and height of a primitive `abc` triple

For a triple `(a, b, c)` of nonzero elements of a number field with `a + b = c`, the uniform
`abc` inequality is phrased with the adelic height `H(a,b,c) = ∏_v max(‖a‖_v, ‖b‖_v, ‖c‖_v)` and
the conductor `N(a,b,c) = ∏_{v ∈ I} N v`, where `I` is the set of finite places at which the three
norms are not all equal.  Over `ℚ`, for coprime integers `a, b`:

* at every prime `p` one of `a, b, a + b` is a `p`-adic unit, so the `p`-adic factor of the height
  is `1` and `H(a, b, a+b) = max(|a|, |b|, |a+b|)`;
* the three `p`-adic norms differ exactly when `p ∣ ab(a+b)`, so `I` is the prime support of
  `ab(a+b)` and `N(a, b, a+b) = rad |ab(a+b)| = rad|a| · rad|b| · rad|a+b|`.

The Frey model `y² = x(x-a)(x+b)` of the triple has `c₄ = 16 (a²+ab+b²)` and
`Δ = 16 (ab(a+b))²`, with `gcd(c₄, Δ) = 16`; its bad primes are `2` and the support of `N`.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

open GaloisForLFunctions.DimensionZeroGeometryOfSpecZ (radical radical_mul)

/-! ## Local norms of a primitive triple -/

section Local

variable (p : ℕ) [hp : Fact p.Prime]

/-- At every prime one of `a, b, a+b` is a unit: the `p`-adic factor of the height is `1`. -/
theorem max_padicNorm_triple {a b : ℤ} (h : IsCoprime a b) :
    max (padicNorm p a) (max (padicNorm p b) (padicNorm p ((a + b : ℤ) : ℚ))) = 1 := by
  refine le_antisymm (max_le (padicNorm.of_int a)
    (max_le (padicNorm.of_int b) (padicNorm.of_int _))) ?_
  by_cases ha : (p : ℤ) ∣ a
  · have hb : ¬ (p : ℤ) ∣ b := fun hb =>
      hp.out.not_dvd_one (Int.natCast_dvd_natCast.mp
        (by simpa using h.isUnit_of_dvd' ha hb |>.dvd))
    exact ((padicNorm.int_eq_one_iff b).mpr hb).symm.le.trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact ((padicNorm.int_eq_one_iff a).mpr ha).symm.le.trans (le_max_left _ _)

/-- The three `p`-adic norms of a primitive triple differ exactly at the primes of `ab(a+b)`. -/
theorem min_lt_max_padicNorm_iff {a b : ℤ} (h : IsCoprime a b) :
    min (padicNorm p a) (min (padicNorm p b) (padicNorm p ((a + b : ℤ) : ℚ))) <
        max (padicNorm p a) (max (padicNorm p b) (padicNorm p ((a + b : ℤ) : ℚ))) ↔
      (p : ℤ) ∣ a * b * (a + b) := by
  rw [max_padicNorm_triple p h]
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rw [hprime.dvd_mul, hprime.dvd_mul, ← padicNorm.int_lt_one_iff, ← padicNorm.int_lt_one_iff,
    ← padicNorm.int_lt_one_iff]
  simp only [min_lt_iff, or_assoc]

end Local

/-! ## The conductor is the radical -/

/-- **The conductor set of a primitive triple.**  For coprime `a, b` with `ab(a+b) ≠ 0`, the
primes at which the three `p`-adic norms of `(a, b, a+b)` are not all equal are exactly the prime
factors of `|ab(a+b)|`. -/
theorem conductorPrimes_eq {a b : ℤ} (h : IsCoprime a b) (habc : a * b * (a + b) ≠ 0) :
    {p : ℕ | ∃ hp : p.Prime, haveI := Fact.mk hp;
        min (padicNorm p a) (min (padicNorm p b) (padicNorm p ((a + b : ℤ) : ℚ))) <
          max (padicNorm p a) (max (padicNorm p b) (padicNorm p ((a + b : ℤ) : ℚ)))} =
      ((a * b * (a + b)).natAbs.primeFactors : Set ℕ) := by
  ext p
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hlt⟩
    haveI := Fact.mk hp
    refine ⟨hp, ?_, Int.natAbs_ne_zero.mpr habc⟩
    exact Int.natCast_dvd.mp ((min_lt_max_padicNorm_iff p h).mp hlt)
  · rintro ⟨hp, hdvd, -⟩
    haveI := Fact.mk hp
    exact ⟨hp, (min_lt_max_padicNorm_iff p h).mpr (Int.natCast_dvd.mpr hdvd)⟩

/-- **`N(a, b, a+b) = rad|ab(a+b)| = rad|a| · rad|b| · rad|a+b|`** for coprime `a, b`. -/
theorem radical_triple {a b : ℤ} (h : IsCoprime a b) :
    radical (a * b * (a + b)).natAbs =
      radical a.natAbs * radical b.natAbs * radical (a + b).natAbs := by
  have hac : IsCoprime a (a + b) := by
    have := h.add_mul_left_right 1
    rwa [mul_one, add_comm] at this
  have hbc : IsCoprime b (a + b) := by
    have := h.symm.add_mul_left_right 1
    simpa [add_comm] using this
  have h1 : a.natAbs.Coprime b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
  have h2 : (a * b).natAbs.Coprime (a + b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.Coprime.mul_left (Int.isCoprime_iff_gcd_eq_one.mp hac)
      (Int.isCoprime_iff_gcd_eq_one.mp hbc)
  rw [Int.natAbs_mul, radical_mul h2, Int.natAbs_mul,
    radical_mul h1]

/-! ## The Frey model -/

/-- The Frey curve `y² = x(x-a)(x+b) = x³ + (b-a)x² - ab x` of the triple `(a, b, a+b)`. -/
def freyCurve (a b : ℤ) : WeierstrassCurve ℤ := ⟨0, b - a, 0, -(a * b), 0⟩

theorem freyCurve_c₄ (a b : ℤ) : (freyCurve a b).c₄ = 16 * (a ^ 2 + a * b + b ^ 2) := by
  simp only [freyCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem freyCurve_Δ (a b : ℤ) : (freyCurve a b).Δ = 16 * (a * b * (a + b)) ^ 2 := by
  simp only [freyCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The integral form of `j = 256 (a²+ab+b²)³ / (ab(a+b))²` on the Frey model. -/
theorem freyCurve_c₄_cube (a b : ℤ) :
    (freyCurve a b).c₄ ^ 3 * (a * b * (a + b)) ^ 2 =
      256 * (a ^ 2 + a * b + b ^ 2) ^ 3 * (freyCurve a b).Δ := by
  rw [freyCurve_c₄, freyCurve_Δ]
  ring

/-- For a primitive triple the Frey invariants `c₄` and `Δ` share exactly the factor `16`. -/
theorem gcd_freyCurve_c₄_Δ {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (freyCurve a b).c₄ (freyCurve a b).Δ = 16 := by
  rw [freyCurve_c₄, freyCurve_Δ, Int.gcd_mul_left,
    Int.isCoprime_iff_gcd_eq_one.mp ((isCoprime_abcQuadratic h).pow_right (n := 2))]
  rfl

/-- **The bad primes of the Frey model** are `2` together with the conductor primes of the
triple. -/
theorem freyCurve_Δ_primeFactors {a b : ℤ} (habc : a * b * (a + b) ≠ 0) :
    (freyCurve a b).Δ.natAbs.primeFactors = insert 2 (a * b * (a + b)).natAbs.primeFactors := by
  rw [freyCurve_Δ, Int.natAbs_mul, Int.natAbs_pow,
    Nat.primeFactors_mul (by norm_num) (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr habc)),
    Nat.primeFactors_pow _ two_ne_zero]
  have h16 : (Int.natAbs 16).primeFactors = {2} := by
    rw [show Int.natAbs 16 = 2 ^ 4 by rfl, Nat.primeFactors_prime_pow (by norm_num)
      Nat.prime_two]
  rw [h16]
  rfl

/-- The radical of the Frey discriminant is `rad(2 ab(a+b))`. -/
theorem radical_freyCurve_Δ {a b : ℤ} (habc : a * b * (a + b) ≠ 0) :
    radical (freyCurve a b).Δ.natAbs = radical (2 * (a * b * (a + b)).natAbs) := by
  have hne : (a * b * (a + b)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr habc
  unfold radical
  rw [freyCurve_Δ_primeFactors habc, Nat.primeFactors_mul two_ne_zero hne,
    Nat.Prime.primeFactors Nat.prime_two]
  rfl

end GaloisForLFunctions.KodairaParshinAbc
