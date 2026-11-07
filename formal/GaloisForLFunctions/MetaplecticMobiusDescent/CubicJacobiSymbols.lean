/-
Ideal-factor symbol proofs are adapted from OpenAI’s formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicReciprocityAtACommonCharacteristic

/-!
# Cubic Jacobi symbols with arbitrary prime multiplicities

The ideal symbol multiplies actual residue characters over the normalized
prime factors. Primary factorization extends prime reciprocity to composite
arguments, including common factors. Coprime symbols are cubic roots of unity.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent
namespace CubicJacobi
open Eisenstein
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

/-- Actual cubic residue value, extended by zero at bad primes. -/
def primeValue (P : Ideal O) (x : O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    cubicChar P h.2 (Ideal.Quotient.mk P x)
  else 0

@[simp] theorem primeValue_eq (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O) :
    primeValue P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  simp only [primeValue, dif_pos (show P.IsMaximal ∧ lambda ∉ P from
    ⟨inferInstance, hgood⟩)]

/-- The cubic ideal symbol, with prime multiplicities retained. -/
def idealSymbol (I : Ideal O) (x : O) : O :=
  if I = 0 then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors I).map (fun P => primeValue P x)).prod

@[simp] theorem idealSymbol_zero (x : O) : idealSymbol 0 x = 0 := by simp [idealSymbol]
@[simp] theorem idealSymbol_bot (x : O) : idealSymbol ⊥ x = 0 := idealSymbol_zero x
@[simp] theorem idealSymbol_one (x : O) : idealSymbol 1 x = 1 := by
  rw [idealSymbol, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl
@[simp] theorem idealSymbol_top (x : O) : idealSymbol ⊤ x = 1 := by
  simpa only [Ideal.one_eq_top] using idealSymbol_one x

/-- Factoring a product splits its ideal symbol. -/
theorem idealSymbol_mul (I J : Ideal O) (x : O) :
    idealSymbol (I * J) x = idealSymbol I x * idealSymbol J x := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [idealSymbol, if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add,
    Multiset.prod_add]

/-- The cubic symbol with a principal denominator. -/
def symbol (x y : O) : O := idealSymbol (Ideal.span {y}) x

@[simp] theorem symbol_one (x : O) : symbol x 1 = 1 := by simp [symbol]
@[simp] theorem symbol_zero (x : O) : symbol x 0 = 0 := by simp [symbol]

theorem symbol_mul_denominator (x y z : O) :
    symbol x (y * z) = symbol x y * symbol x z := by
  rw [symbol, ← Ideal.span_singleton_mul_span_singleton, idealSymbol_mul]
  rfl

theorem idealSymbol_prime (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (x : O) :
    idealSymbol P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  have hP0 : P ≠ 0 := NeZero.ne _
  have hp : Prime P := Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)
  rw [idealSymbol, if_neg hP0,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible]
  simpa using primeValue_eq P hgood x


/-- Multiplicativity holds also for the zero extension at bad primes. -/
theorem primeValue_map_mul (P : Ideal O) (x y : O) :
    primeValue P (x*y) = primeValue P x * primeValue P y := by
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · letI := hg.1
    simp only [primeValue_eq P hg.2, map_mul]
  · simp only [primeValue, dif_neg hg, zero_mul]

/-- The ideal cubic symbol is multiplicative in its numerator. -/
theorem idealSymbol_map_mul (I : Ideal O) (x y : O) :
    idealSymbol I (x*y) = idealSymbol I x * idealSymbol I y := by
  by_cases hI : I = 0
  · simp only [hI, idealSymbol_zero, zero_mul]
  simp only [idealSymbol, if_neg hI]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P _
  exact primeValue_map_mul P x y

/-- Every prime factor of a primary principal ideal is away from three. -/
private theorem factor_good (a : O) (ha : lambda ^ 2 ∣ a-1)
    (P : Ideal O) (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) :
    P.IsMaximal ∧ lambda ∉ P := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  refine ⟨inferInstance, ?_⟩
  have ha0 : (Ideal.span {a} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primary_ne_zero a ha)
  have hle := ((Ideal.mem_normalizedFactors_iff ha0).mp hP).2
  exact primary_maximal_divisor_good a ha P (hle (Ideal.subset_span (by simp)))

/-- The symbol at one is one for a primary denominator. -/
theorem symbol_one_numerator (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol 1 a = 1 := by
  have ha0 : (Ideal.span {a} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primary_ne_zero a ha)
  rw [symbol, idealSymbol, if_neg ha0]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hy
  have hg := factor_good a ha P hP
  letI := hg.1
  simp only [primeValue_eq P hg.2, map_one]

/-- The cubic symbol is multiplicative in its numerator. -/
theorem symbol_mul_numerator (x y a : O) :
    symbol (x*y) a = symbol x a * symbol y a := idealSymbol_map_mul _ _ _

/-- Numerator products can be evaluated factor by factor. -/
theorem symbol_multiset_numerator (a : O) (ha : lambda ^ 2 ∣ a-1) (s : Multiset O) :
    symbol s.prod a = (s.map (fun x => symbol x a)).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa only [Multiset.prod_zero, Multiset.map_zero] using symbol_one_numerator a ha
  | @cons x s ih => simp only [Multiset.prod_cons, Multiset.map_cons, symbol_mul_numerator, ih]

/-- Denominator products can be evaluated factor by factor. -/
theorem symbol_multiset_denominator (x : O) (s : Multiset O) :
    symbol x s.prod = (s.map (symbol x)).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa only [Multiset.prod_zero, Multiset.map_zero] using symbol_one x
  | @cons a s ih => simp only [Multiset.prod_cons, Multiset.map_cons, symbol_mul_denominator, ih]

theorem symbol_prime (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (x : O) :
    symbol x p = primeValue (Ideal.span {p}) x := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol, idealSymbol_prime _ hg, primeValue_eq _ hg]


/-- Prime reciprocity extends to arbitrary primary elements, with multiplicities and common factors. -/
theorem symbol_reciprocity (a b : O)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) : symbol a b = symbol b a := by
  obtain ⟨s,hs,hsp⟩ := exists_primary_prime_factorization a (primary_ne_zero a ha) ha
  obtain ⟨t,ht,htp⟩ := exists_primary_prime_factorization b (primary_ne_zero b hb) hb
  rw [← hs, ← ht, symbol_multiset_denominator, symbol_multiset_denominator]
  have hleft : (t.map (symbol s.prod)).prod =
      (t.map (fun q => (s.map (fun p => symbol p q)).prod)).prod := by
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro q hq
    exact symbol_multiset_numerator q (htp q hq).2 s
  have hright : (s.map (symbol t.prod)).prod =
      (s.map (fun p => (t.map (fun q => symbol q p)).prod)).prod := by
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro p hp
    exact symbol_multiset_numerator p (hsp p hp).2 t
  rw [hleft,hright,Multiset.prod_map_prod_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro p hp
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro q hq
  have hpp := hsp p hp
  have hqp := htp q hq
  letI : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpp.1.irreducible
  letI : (Ideal.span {q} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hqp.1.irreducible
  have hpg := primary_maximal_divisor_good p hpp.2 (Ideal.span {p})
    (Ideal.subset_span (by simp))
  have hqg := primary_maximal_divisor_good q hqp.2 (Ideal.span {q})
    (Ideal.subset_span (by simp))
  rw [symbol_prime p hpp.1 hpp.2, symbol_prime q hqp.1 hqp.2,
    primeValue_eq _ hpg, primeValue_eq _ hqg]
  exact cubic_reciprocity_primary _ _ hqg hpg q p rfl rfl hqp.2 hpp.2

/-- The numerator is read only modulo the ideal denominator. -/
theorem idealSymbol_congr (I : Ideal O) {x y : O} (hxy : x - y ∈ I) :
    idealSymbol I x = idealSymbol I y := by
  classical
  by_cases hI : I = 0
  · simp only [hI, idealSymbol_zero]
  simp only [idealSymbol, if_neg hI]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hle := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    rw [primeValue_eq P hg.2, primeValue_eq P hg.2,
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hle hxy)]
  · simp only [primeValue, dif_neg hg]

theorem symbol_congr {x y d : O} (hxy : d ∣ x - y) :
    symbol x d = symbol y d :=
  idealSymbol_congr _ (Ideal.mem_span_singleton.mpr hxy)


/-- A prime cubic symbol at an invertible residue is a cubic root of unity. -/
theorem cubicValue_cube (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    (cubicChar P hg (Ideal.Quotient.mk P x)) ^ 3 = 1 := by
  rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr
    (Ideal.Quotient.eq_zero_iff_mem.not.mpr hx))

theorem cubicValue_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    cubicChar P hg (Ideal.Quotient.mk P x) ≠ 0 := by
  have h := cubicValue_cube P hg x hx
  intro hz
  rw [hz, zero_pow (by decide)] at h
  exact zero_ne_one h

private theorem numerator_not_mem (P : Ideal O) [P.IsMaximal]
    (x a : O) (haP : a ∈ P) (hcop : IsCoprime x a) : x ∉ P := by
  intro hxP
  obtain ⟨r,t,hrt⟩ := hcop
  have hmem := P.add_mem (P.mul_mem_left r hxP) (P.mul_mem_left t haP)
  rw [hrt] at hmem
  exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
    ((Ideal.eq_top_iff_one P).mpr hmem)

/-- The composite symbol at coprime arguments is a cubic root of unity. -/
theorem symbol_cube_of_isCoprime (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : symbol x a ^ 3 = 1 := by
  have hI0 : (Ideal.span {a} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primary_ne_zero a ha)
  rw [symbol, idealSymbol, if_neg hI0, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hy
  have hg := factor_good a ha P hP
  letI := hg.1
  have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
  have haP : a ∈ P := hle (Ideal.subset_span (by simp))
  rw [primeValue_eq P hg.2]
  exact cubicValue_cube P hg.2 x (numerator_not_mem P x a haP hcop)

/-- Coprime symbols can be cancelled. -/
theorem symbol_ne_zero_of_isCoprime (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : symbol x a ≠ 0 := by
  intro hz
  have h := symbol_cube_of_isCoprime x a ha hcop
  rw [hz, zero_pow (by decide)] at h
  exact zero_ne_one h

/-- The complex cubic symbol has unit norm at coprime arguments. -/
theorem symbol_norm_one (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : ‖ringComplex (symbol x a)‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
  have h : ringComplex (symbol x a) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime x a ha hcop, map_one]
  simpa only [norm_pow, norm_one] using congrArg norm h

/-- Raising the numerator raises the cubic symbol. -/
theorem symbol_pow_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) (n : ℕ) :
    symbol (x^n) a = symbol x a ^ n := by
  induction n with
  | zero => simp only [pow_zero, symbol_one_numerator a ha]
  | succ n ih => rw [pow_succ, symbol_mul_numerator, ih, pow_succ]

/-- Denominator powers retain their factor multiplicities. -/
theorem symbol_pow_denominator (x a : O) (n : ℕ) :
    symbol x (a^n) = symbol x a ^ n := by
  induction n with
  | zero => simp only [pow_zero, symbol_one]
  | succ n ih => rw [pow_succ, symbol_mul_denominator, ih, pow_succ]

/-- Minus one has trivial cubic symbol for every primary denominator. -/
theorem symbol_neg_one (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol (-1) a = 1 := by
  have hI0 : (Ideal.span {a} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primary_ne_zero a ha)
  rw [symbol, idealSymbol, if_neg hI0]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hy
  have hg := factor_good a ha P hP
  letI := hg.1
  rw [primeValue_eq P hg.2, map_neg, map_one, cubicChar_neg_one]

theorem symbol_neg_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) :
    symbol (-x) a = symbol x a := by
  rw [neg_eq_neg_one_mul, symbol_mul_numerator, symbol_neg_one a ha, one_mul]

/-- The symbol of a unit is nonzero. -/
theorem symbol_isUnit_ne_zero (x a : O) (hx : IsUnit x) (ha : lambda ^ 2 ∣ a-1) :
    symbol x a ≠ 0 := by
  obtain ⟨u,rfl⟩ := hx
  have h : symbol (u : O) a * symbol (↑u⁻¹ : O) a = 1 := by
    rw [← symbol_mul_numerator, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, symbol_one_numerator a ha]
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

end CubicJacobi
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.idealSymbol_mul
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.idealSymbol_map_mul
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.symbol_reciprocity
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.symbol_congr
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.symbol_cube_of_isCoprime
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.symbol_norm_one
