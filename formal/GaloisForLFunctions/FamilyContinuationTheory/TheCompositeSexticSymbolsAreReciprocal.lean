import GaloisForLFunctions.FamilyContinuationTheory.TheQuadraticPhaseIsABicharacterModuloFour
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobiSymbols

/-!
# The composite sextic symbols are reciprocal

For `x, y ∈ O = ℤ[ω]` the quadratic Jacobi symbol `(x/y)₂` multiplies the quadratic residue
characters of the prime factors of `(y)` (with multiplicity, zero at the prime over two), and the
sextic symbol is `χ_y(x) = ((x/y)₃)² (x/y)₂` with the cubic Jacobi symbol of
`MetaplecticMobiusDescent`.

* `quadSymbol_reciprocity`: for coprime primary `a, b` prime to `2`,
  `(b/a)₂ (a/b)₂ = r(a, b)`, `r(a, b) = Γ(ab)/(Γ(a)Γ(b))`;
* `sexticSymbol_reciprocity`: `χ_b(a) = r(a, b) χ_a(b)`.

The prime case is `quadratic_reciprocity`; the composite case expands both symbols over the
prime factors and uses that `r` is a bicharacter of the odd classes (`quadraticPhase_mul_left`).
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

private instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### The quadratic Jacobi symbol -/

/-- The quadratic residue value at a prime ideal, zero at the prime over two. -/
def quadPrimeValue (P : Ideal O) (x : O) : ℂ :=
  if h : P.IsMaximal ∧ (2 : O) ∉ P then
    letI : P.IsMaximal := h.1
    complexQuadraticChar P (Ideal.Quotient.mk P x)
  else 0

theorem quadPrimeValue_eq (P : Ideal O) [P.IsMaximal] (h2 : (2 : O) ∉ P) (x : O) :
    quadPrimeValue P x = complexQuadraticChar P (Ideal.Quotient.mk P x) := by
  simp only [quadPrimeValue, dif_pos (show P.IsMaximal ∧ (2 : O) ∉ P from ⟨inferInstance, h2⟩)]

theorem quadPrimeValue_map_mul (P : Ideal O) (x y : O) :
    quadPrimeValue P (x * y) = quadPrimeValue P x * quadPrimeValue P y := by
  by_cases hg : P.IsMaximal ∧ (2 : O) ∉ P
  · letI := hg.1
    simp only [quadPrimeValue_eq P hg.2, map_mul]
  · simp only [quadPrimeValue, dif_neg hg, zero_mul]

/-- The quadratic ideal symbol, with prime multiplicities. -/
def quadIdealSymbol (I : Ideal O) (x : O) : ℂ :=
  if I = 0 then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors I).map (fun P => quadPrimeValue P x)).prod

theorem quadIdealSymbol_one (x : O) : quadIdealSymbol 1 x = 1 := by
  rw [quadIdealSymbol, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl

theorem quadIdealSymbol_mul (I J : Ideal O) (x : O) :
    quadIdealSymbol (I * J) x = quadIdealSymbol I x * quadIdealSymbol J x := by
  by_cases hI : I = 0
  · simp [hI, quadIdealSymbol]
  by_cases hJ : J = 0
  · simp [hJ, quadIdealSymbol]
  simp only [quadIdealSymbol, if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

theorem quadIdealSymbol_map_mul (I : Ideal O) (x y : O) :
    quadIdealSymbol I (x * y) = quadIdealSymbol I x * quadIdealSymbol I y := by
  by_cases hI : I = 0
  · simp [hI, quadIdealSymbol]
  simp only [quadIdealSymbol, if_neg hI]
  rw [← Multiset.prod_map_mul]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun P _ => quadPrimeValue_map_mul P x y)

theorem quadIdealSymbol_prime (P : Ideal O) [P.IsMaximal] (h2 : (2 : O) ∉ P) (x : O) :
    quadIdealSymbol P x = complexQuadraticChar P (Ideal.Quotient.mk P x) := by
  have hP0 : P ≠ 0 := NeZero.ne _
  have hp : Prime P := Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)
  rw [quadIdealSymbol, if_neg hP0,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible]
  simpa using quadPrimeValue_eq P h2 x

/-- The quadratic Jacobi symbol `(x/y)₂`. -/
def quadSymbol (x y : O) : ℂ := quadIdealSymbol (Ideal.span {y}) x

theorem quadSymbol_one_denominator (x : O) : quadSymbol x 1 = 1 := by
  rw [quadSymbol, Ideal.span_singleton_one, ← Ideal.one_eq_top, quadIdealSymbol_one]

theorem quadSymbol_mul_denominator (x y z : O) :
    quadSymbol x (y * z) = quadSymbol x y * quadSymbol x z := by
  rw [quadSymbol, ← Ideal.span_singleton_mul_span_singleton, quadIdealSymbol_mul]
  rfl

theorem quadSymbol_mul_numerator (x y a : O) :
    quadSymbol (x * y) a = quadSymbol x a * quadSymbol y a := quadIdealSymbol_map_mul _ _ _

theorem quadSymbol_multiset_denominator (x : O) (s : Multiset O) :
    quadSymbol x s.prod = (s.map (quadSymbol x)).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using quadSymbol_one_denominator x
  | cons a s ih => simp only [Multiset.prod_cons, Multiset.map_cons, quadSymbol_mul_denominator, ih]

/-- An element prime to `2` is outside every prime ideal containing `2`. -/
theorem two_not_mem_span_of_dvd {p a : O} (hpa : p ∣ a) (ha2 : IsCoprime a 2)
    (hp : ¬ IsUnit p) : (2 : O) ∉ Ideal.span {p} := by
  intro h
  exact hp (ha2.isUnit_of_dvd' hpa (Ideal.mem_span_singleton.mp h))

/-- At a prime prime to two the symbol is the quadratic residue character. -/
theorem quadSymbol_prime (p : O) [(Ideal.span {p}).IsMaximal] (h2 : (2 : O) ∉ Ideal.span {p})
    (x : O) : quadSymbol x p = complexQuadraticChar (Ideal.span {p}) (Ideal.Quotient.mk _ x) := by
  rw [quadSymbol, quadIdealSymbol_prime _ h2]

/-- `2` is not a unit of `O`. -/
theorem two_not_isUnit : ¬ IsUnit (2 : O) := by
  intro hu
  have h1 : (1 : O) ∈ Ideal.span {(2 : O)} := by
    rw [Ideal.span_singleton_eq_top.mpr hu]
    trivial
  exact not_mem_of_oddCoord 1 0 (by decide) (by simpa [Coordinates.eval] using h1)

/-- An element prime to `2` is odd. -/
theorem not_mem_two_of_isCoprime {a : O} (ha2 : IsCoprime a 2) : a ∉ Ideal.span {(2 : O)} :=
  fun h => two_not_isUnit (ha2.isUnit_of_dvd' (Ideal.mem_span_singleton.mp h) (dvd_refl 2))

/-- The prime factors of an element prime to two are good for the quadratic symbol. -/
theorem quadPrimeValue_one_of_factor {a : O} (ha0 : a ≠ 0) (ha2 : IsCoprime a 2) {P : Ideal O}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) :
    quadPrimeValue P 1 = 1 := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hspan0 : (Ideal.span {a} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr ha0
  have haP : a ∈ P := ((Ideal.mem_normalizedFactors_iff hspan0).mp hP).2 (Ideal.subset_span rfl)
  have h2 : (2 : O) ∉ P := by
    intro h2P
    obtain ⟨x, y, hxy⟩ := ha2
    exact (inferInstance : P.IsMaximal).ne_top ((Ideal.eq_top_iff_one P).mpr
      (hxy ▸ P.add_mem (P.mul_mem_left x haP) (P.mul_mem_left y h2P)))
  rw [quadPrimeValue_eq P h2, map_one, MulChar.map_one]

theorem quadSymbol_one_numerator {a : O} (ha0 : a ≠ 0) (ha2 : IsCoprime a 2) :
    quadSymbol 1 a = 1 := by
  rw [quadSymbol, quadIdealSymbol, if_neg (show Ideal.span {a} ≠ (0 : Ideal O) from
    Ideal.span_singleton_eq_bot.not.mpr ha0)]
  exact Multiset.prod_eq_one fun y hy => by
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hy
    exact quadPrimeValue_one_of_factor ha0 ha2 hP

theorem quadSymbol_multiset_numerator {a : O} (ha0 : a ≠ 0) (ha2 : IsCoprime a 2)
    (s : Multiset O) : quadSymbol s.prod a = (s.map fun x => quadSymbol x a).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using quadSymbol_one_numerator ha0 ha2
  | cons x s ih => simp only [Multiset.prod_cons, Multiset.map_cons, quadSymbol_mul_numerator, ih]

/-- A quadratic symbol at a coprime numerator is a sign. -/
theorem quadSymbol_sq {x a : O} (ha0 : a ≠ 0) (ha2 : IsCoprime a 2) (hxa : IsCoprime x a) :
    quadSymbol x a ^ 2 = 1 := by
  rw [quadSymbol, quadIdealSymbol, if_neg (show Ideal.span {a} ≠ (0 : Ideal O) from
    Ideal.span_singleton_eq_bot.not.mpr ha0), ← Multiset.prod_map_pow]
  refine Multiset.prod_eq_one fun y hy => ?_
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hy
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  have hspan0 : (Ideal.span {a} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr ha0
  have haP : a ∈ P := ((Ideal.mem_normalizedFactors_iff hspan0).mp hP).2 (Ideal.subset_span rfl)
  have hmax : P.IsMaximal := inferInstance
  have hcop : ∀ z : O, IsCoprime z a → z ∈ P → False := fun z hz hzP => by
    obtain ⟨u, v, huv⟩ := hz
    exact hmax.ne_top ((Ideal.eq_top_iff_one P).mpr
      (huv ▸ P.add_mem (P.mul_mem_left u hzP) (P.mul_mem_left v haP)))
  have h2 : (2 : O) ∉ P := fun h => hcop 2 ha2.symm h
  have hx : Ideal.Quotient.mk P x ≠ 0 := fun h =>
    hcop x hxa (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [quadPrimeValue_eq P h2]
  simp only [complexQuadraticChar, MulChar.ringHomComp_apply, eq_intCast]
  rw [← Int.cast_pow, quadraticChar_sq_one hx, Int.cast_one]

/-! ### Reciprocity -/

/-- `Γ(1) = 1`, so `r(1, b) = 1`. -/
theorem quadraticPhase_one_left {b : O} (hb : b ∉ Ideal.span {(2 : O)}) : quadraticPhase 1 b = 1 := by
  rw [quadraticPhase, one_mul, fixedDualAverage_one, one_mul, div_self (gamma_ne_zero hb)]

/-- A product of odd elements is odd. -/
theorem odd_multiset_prod (s : Multiset O) (hs : ∀ x ∈ s, x ∉ Ideal.span {(2 : O)}) :
    s.prod ∉ Ideal.span {(2 : O)} := by
  induction s using Multiset.induction_on with
  | empty =>
    simpa [Coordinates.eval] using not_mem_of_oddCoord 1 0 (by decide)
  | cons x s ih =>
    rw [Multiset.prod_cons]
    exact odd_mul (hs x (Multiset.mem_cons_self x s))
      (ih fun y hy => hs y (Multiset.mem_cons_of_mem hy))

/-- `r` expands over a factorization of its first argument. -/
theorem quadraticPhase_multiset_left (s : Multiset O) (hs : ∀ x ∈ s, x ∉ Ideal.span {(2 : O)})
    {b : O} (hb : b ∉ Ideal.span {(2 : O)}) :
    quadraticPhase s.prod b = (s.map fun x => quadraticPhase x b).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using quadraticPhase_one_left hb
  | cons x s ih =>
    have hs' : ∀ y ∈ s, y ∉ Ideal.span {(2 : O)} := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      quadraticPhase_mul_left (hs x (Multiset.mem_cons_self x s)) (odd_multiset_prod s hs') hb,
      ih hs']

/-- **Quadratic reciprocity at two primes, in symbol form.** -/
theorem quadSymbol_prime_reciprocity {p q : O} (hp : Prime p) (hq : Prime q)
    (hp2 : IsCoprime p 2) (hq2 : IsCoprime q 2) (hpq : IsCoprime p q) :
    quadSymbol q p * quadSymbol p q = quadraticPhase p q := by
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq.irreducible
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have h2p : (2 : O) ∉ Ideal.span {p} := fun h =>
    hp.not_unit (hp2.isUnit_of_dvd' (dvd_refl p) (Ideal.mem_span_singleton.mp h))
  have h2q : (2 : O) ∉ Ideal.span {q} := fun h =>
    hq.not_unit (hq2.isUnit_of_dvd' (dvd_refl q) (Ideal.mem_span_singleton.mp h))
  have h := quadratic_reciprocity p q h2p h2q hpq
  rw [normalizedQuadraticTraceGauss_eq_fixedDualAverage,
    normalizedQuadraticTraceGauss_eq_fixedDualAverage,
    normalizedQuadraticTraceGauss_eq_fixedDualAverage] at h
  rw [quadSymbol_prime p h2p, quadSymbol_prime q h2q, quadraticPhase,
    eq_div_iff (mul_ne_zero (gamma_ne_zero (not_mem_two_of_isCoprime hp2))
      (gamma_ne_zero (not_mem_two_of_isCoprime hq2)))]
  linear_combination h

/-- **Composite quadratic reciprocity.** For coprime primary `a, b` prime to `2`,
`(b/a)₂ (a/b)₂ = r(a, b)`. -/
theorem quadSymbol_reciprocity {a b : O} (ha : lambda ^ 2 ∣ a - 1) (hb : lambda ^ 2 ∣ b - 1)
    (ha2 : IsCoprime a 2) (hb2 : IsCoprime b 2) (hab : IsCoprime a b) :
    quadSymbol b a * quadSymbol a b = quadraticPhase a b := by
  obtain ⟨s, hs, hsp⟩ := exists_primary_prime_factorization a (primary_ne_zero a ha) ha
  obtain ⟨t, ht, htp⟩ := exists_primary_prime_factorization b (primary_ne_zero b hb) hb
  have hsd : ∀ p ∈ s, p ∣ a := fun p hp => hs ▸ Multiset.dvd_prod hp
  have htd : ∀ q ∈ t, q ∣ b := fun q hq => ht ▸ Multiset.dvd_prod hq
  have hs2 : ∀ p ∈ s, IsCoprime p 2 := fun p hp => ha2.of_isCoprime_of_dvd_left (hsd p hp)
  have ht2 : ∀ q ∈ t, IsCoprime q 2 := fun q hq => hb2.of_isCoprime_of_dvd_left (htd q hq)
  have hst : ∀ p ∈ s, ∀ q ∈ t, IsCoprime p q := fun p hp q hq =>
    (hab.of_isCoprime_of_dvd_left (hsd p hp)).of_isCoprime_of_dvd_right (htd q hq)
  have hsodd : ∀ p ∈ s, p ∉ Ideal.span {(2 : O)} := fun p hp => not_mem_two_of_isCoprime (hs2 p hp)
  have htodd : ∀ q ∈ t, q ∉ Ideal.span {(2 : O)} := fun q hq => not_mem_two_of_isCoprime (ht2 q hq)
  -- the left side over the prime pairs
  have hL : quadSymbol b a * quadSymbol a b =
      (s.map fun p => (t.map fun q => quadSymbol q p * quadSymbol p q).prod).prod := by
    rw [← hs, ← ht, quadSymbol_multiset_denominator, quadSymbol_multiset_denominator]
    have h1 : (s.map (quadSymbol t.prod)).prod =
        (s.map fun p => (t.map fun q => quadSymbol q p).prod).prod :=
      congrArg Multiset.prod (Multiset.map_congr rfl fun p hp =>
        quadSymbol_multiset_numerator (hsp p hp).1.ne_zero (hs2 p hp) t)
    have h2 : (t.map (quadSymbol s.prod)).prod =
        (t.map fun q => (s.map fun p => quadSymbol p q).prod).prod :=
      congrArg Multiset.prod (Multiset.map_congr rfl fun q hq =>
        quadSymbol_multiset_numerator (htp q hq).1.ne_zero (ht2 q hq) s)
    rw [h1, h2, Multiset.prod_map_prod_map t s, ← Multiset.prod_map_mul]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun p _ => (Multiset.prod_map_mul).symm)
  -- the right side over the prime pairs
  have hR : quadraticPhase a b =
      (s.map fun p => (t.map fun q => quadraticPhase p q).prod).prod := by
    have hbodd : b ∉ Ideal.span {(2 : O)} := not_mem_two_of_isCoprime hb2
    rw [← hs, quadraticPhase_multiset_left s hsodd (ht ▸ hbodd)]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun p hp => ?_)
    rw [quadraticPhase_comm, ← ht, quadraticPhase_multiset_left t htodd (hsodd p hp)]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun q _ => quadraticPhase_comm q p)
  rw [hL, hR]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun p hp => ?_)
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun q hq =>
    quadSymbol_prime_reciprocity (hsp p hp).1 (htp q hq).1 (hs2 p hp) (ht2 q hq) (hst p hp q hq))

/-! ### The sextic symbol -/

/-- The sextic symbol `χ_y(x) = ((x/y)₃)² (x/y)₂`. -/
def sexticSymbol (x y : O) : ℂ := ringComplex (CubicJacobi.symbol x y) ^ 2 * quadSymbol x y

/-- **Composite sextic reciprocity.** For coprime primary `a, b` prime to `2`,
`χ_b(a) = r(a, b) χ_a(b)`. -/
theorem sexticSymbol_reciprocity {a b : O} (ha : lambda ^ 2 ∣ a - 1) (hb : lambda ^ 2 ∣ b - 1)
    (ha2 : IsCoprime a 2) (hb2 : IsCoprime b 2) (hab : IsCoprime a b) :
    sexticSymbol a b = quadraticPhase a b * sexticSymbol b a := by
  have hq := quadSymbol_reciprocity ha hb ha2 hb2 hab
  have hsq : quadSymbol b a ^ 2 = 1 := quadSymbol_sq (primary_ne_zero a ha) ha2 hab.symm
  unfold sexticSymbol
  rw [CubicJacobi.symbol_reciprocity a b ha hb, ← hq]
  linear_combination (-(ringComplex (CubicJacobi.symbol b a) ^ 2 * quadSymbol a b)) * hsq

end GaloisForLFunctions.FamilyContinuationTheory
