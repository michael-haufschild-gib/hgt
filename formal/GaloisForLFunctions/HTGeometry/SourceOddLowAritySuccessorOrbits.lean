import GaloisForLFunctions.HTGeometry.SourceOddQuinticSuccessorModulus
import Mathlib.Data.Complex.Basic

/-!
# Source-odd successor orbits: arities two to four are rigid, arity five carries a modulus

Labeled source polarity keeps exactly the monomials whose `y`-exponent is odd, and source-preserving
changes of presentation act diagonally together with a projective rescaling of the top record.  This
file completes the orbit classification of the *fully supported* source-odd binary forms:

* arities two, three and four each have **one** projective source orbit;
* arity five has the complete invariant `κ = b²/(a c)` — equal `κ` is not only necessary but also
  **sufficient** for equivalence — and hence infinitely many orbits.

Everything is elementary torus-weight bookkeeping over a field in which every element is a square,
which is what supplies the needed reparametrization `u`.

## Main results

* `sourceOddQuadratic_single_orbit`, `sourceOddCubic_single_orbit`, `sourceOddQuartic_single_orbit`;
* `sourceProjectivelyEquivalentOddQuintic_of_cross_invariant` — completeness of `κ`;
* `sourceProjectivelyEquivalentOddQuintic_iff_cross_invariant` — the exact orbit criterion;
* `pairwise_not_sourceProjectivelyEquivalent_normalized` — infinitely many quintic orbits.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

omit [Field K] in
private theorem quinticCoeff_ext {q r : SourceOddQuinticCoefficients K}
    (h1 : q.lead = r.lead) (h2 : q.middle = r.middle) (h3 : q.tail = r.tail) : q = r := by
  cases q
  cases r
  simp_all

/-- Given a square root `u` of `a' b / (a b')`, the product form of the defining relation. -/
private theorem sq_relation {a b a' b' u : K} (ha : a ≠ 0) (hb' : b' ≠ 0)
    (hu : u ^ (2 : ℕ) = a' * b / (a * b')) : u ^ (2 : ℕ) * (a * b') = a' * b := by
  rw [hu, div_mul_cancel₀]
  exact mul_ne_zero ha hb'

private theorem sqrt_ne_zero {a b a' b' u : K} (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0)
    (hb' : b' ≠ 0) (hu : u ^ (2 : ℕ) = a' * b / (a * b')) : u ≠ 0 := by
  intro h
  rw [h] at hu
  have hne : a' * b / (a * b') ≠ 0 :=
    div_ne_zero (mul_ne_zero ha' hb) (mul_ne_zero ha hb')
  exact hne (by simpa using hu.symm)

/-! ### Arity two -/

/-- Reparametrization of the source-odd quadratic `a x y`. -/
def sourceOddQuadraticReparam (lam u v a : K) : K := lam * a * u * v

/-- **Arity two is rigid.**  Any two fully supported source-odd quadratics are equivalent. -/
theorem sourceOddQuadratic_single_orbit {a a' : K} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    ∃ lam u v : K, lam ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ sourceOddQuadraticReparam lam u v a = a' := by
  refine ⟨a' / a, 1, 1, div_ne_zero ha' ha, one_ne_zero, one_ne_zero, ?_⟩
  show a' / a * a * 1 * 1 = a'
  field_simp

/-! ### Arity three -/

/-- Reparametrization of the source-odd cubic `a x²y + b y³`. -/
def sourceOddCubicReparam (lam u v : K) (ab : K × K) : K × K :=
  (lam * ab.1 * u ^ (2 : ℕ) * v, lam * ab.2 * v ^ (3 : ℕ))

/-- **Arity three is rigid** over a field with square roots. -/
theorem sourceOddCubic_single_orbit (hsq : ∀ z : K, ∃ w : K, w ^ (2 : ℕ) = z)
    {a b a' b' : K} (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
    ∃ lam u v : K, lam ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      sourceOddCubicReparam lam u v (a, b) = (a', b') := by
  obtain ⟨u, hu⟩ := hsq (a' * b / (a * b'))
  have hu0 : u ≠ 0 := sqrt_ne_zero ha hb ha' hb' hu
  have hu' : u ^ (2 : ℕ) * (a * b') = a' * b := sq_relation ha hb' hu
  refine ⟨b' / b, u, 1, div_ne_zero hb' hb, hu0, one_ne_zero, ?_⟩
  refine Prod.ext ?_ ?_
  · show b' / b * a * u ^ (2 : ℕ) * 1 = a'
    rw [mul_one, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hb]
    calc b' * a * u ^ (2 : ℕ) = u ^ (2 : ℕ) * (a * b') := by ring
      _ = a' * b := hu'
  · show b' / b * b * 1 ^ (3 : ℕ) = b'
    field_simp

/-! ### Arity four -/

/-- Reparametrization of the source-odd quartic `a x³y + b x y³`. -/
def sourceOddQuarticReparam (lam u v : K) (ab : K × K) : K × K :=
  (lam * ab.1 * u ^ (3 : ℕ) * v, lam * ab.2 * u * v ^ (3 : ℕ))

/-- **Arity four is rigid** over a field with square roots. -/
theorem sourceOddQuartic_single_orbit (hsq : ∀ z : K, ∃ w : K, w ^ (2 : ℕ) = z)
    {a b a' b' : K} (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
    ∃ lam u v : K, lam ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      sourceOddQuarticReparam lam u v (a, b) = (a', b') := by
  obtain ⟨u, hu⟩ := hsq (a' * b / (a * b'))
  have hu0 : u ≠ 0 := sqrt_ne_zero ha hb ha' hb' hu
  have hu' : u ^ (2 : ℕ) * (a * b') = a' * b := sq_relation ha hb' hu
  refine ⟨b' / (b * u), u, 1, div_ne_zero hb' (mul_ne_zero hb hu0), hu0, one_ne_zero, ?_⟩
  refine Prod.ext ?_ ?_
  · show b' / (b * u) * a * u ^ (3 : ℕ) * 1 = a'
    rw [mul_one, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hb hu0)]
    calc b' * a * u ^ (3 : ℕ) = u ^ (2 : ℕ) * (a * b') * u := by ring
      _ = a' * b * u := by rw [hu']
      _ = a' * (b * u) := by ring
  · show b' / (b * u) * b * u * 1 ^ (3 : ℕ) = b'
    rw [one_pow, mul_one, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_iff (mul_ne_zero hb hu0)]
    ring

/-! ### Arity five: the modulus -/

/-- **Completeness of the quintic invariant.**  Two fully supported source-odd quintics with the
same cross invariant are source-projectively equivalent. -/
theorem sourceProjectivelyEquivalentOddQuintic_of_cross_invariant
    (hsq : ∀ z : K, ∃ w : K, w ^ (2 : ℕ) = z)
    {q r : SourceOddQuinticCoefficients K}
    (_hq : q.lead ≠ 0) (hqm : q.middle ≠ 0) (hqt : q.tail ≠ 0)
    (_hr : r.lead ≠ 0) (hrm : r.middle ≠ 0) (hrt : r.tail ≠ 0)
    (hcross : r.middle ^ (2 : ℕ) * q.lead * q.tail = q.middle ^ (2 : ℕ) * r.lead * r.tail) :
    SourceProjectivelyEquivalentOddQuintic q r := by
  obtain ⟨u, hu⟩ := hsq (r.middle * q.tail / (q.middle * r.tail))
  have hu0 : u ≠ 0 := sqrt_ne_zero hqm hqt hrm hrt hu
  have hu' : u ^ (2 : ℕ) * (q.middle * r.tail) = r.middle * q.tail := sq_relation hqm hrt hu
  refine ⟨r.tail / q.tail, u, 1, div_ne_zero hrt hqt, hu0, one_ne_zero, ?_⟩
  refine quinticCoeff_ext ?_ ?_ ?_ <;> simp only [sourceOddQuinticReparam]
  · -- lead
    symm
    rw [mul_one, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hqt]
    have hcancel : (q.middle * r.tail) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (mul_ne_zero hqm hrt)
    refine mul_right_cancel₀ hcancel ?_
    calc r.tail * q.lead * u ^ (4 : ℕ) * (q.middle * r.tail) ^ (2 : ℕ)
        = r.tail * q.lead * (u ^ (2 : ℕ) * (q.middle * r.tail)) ^ (2 : ℕ) := by ring
      _ = r.tail * q.lead * (r.middle * q.tail) ^ (2 : ℕ) := by rw [hu']
      _ = q.tail * (r.middle ^ (2 : ℕ) * q.lead * q.tail) * r.tail := by ring
      _ = q.tail * (q.middle ^ (2 : ℕ) * r.lead * r.tail) * r.tail := by rw [hcross]
      _ = r.lead * q.tail * (q.middle * r.tail) ^ (2 : ℕ) := by ring
  · -- middle
    symm
    rw [one_pow, mul_one, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hqt]
    calc r.tail * q.middle * u ^ (2 : ℕ) = u ^ (2 : ℕ) * (q.middle * r.tail) := by ring
      _ = r.middle * q.tail := hu'
  · -- tail
    symm
    rw [one_pow, mul_one, div_mul_eq_mul_div, div_eq_iff hqt]

/-- **The exact quintic orbit criterion.**  Fully supported source-odd quintics are equivalent
exactly when their cross invariants agree. -/
theorem sourceProjectivelyEquivalentOddQuintic_iff_cross_invariant
    (hsq : ∀ z : K, ∃ w : K, w ^ (2 : ℕ) = z)
    {q r : SourceOddQuinticCoefficients K}
    (hq : q.lead ≠ 0) (hqm : q.middle ≠ 0) (hqt : q.tail ≠ 0)
    (hr : r.lead ≠ 0) (hrm : r.middle ≠ 0) (hrt : r.tail ≠ 0) :
    SourceProjectivelyEquivalentOddQuintic q r ↔
      r.middle ^ (2 : ℕ) * q.lead * q.tail = q.middle ^ (2 : ℕ) * r.lead * r.tail :=
  ⟨sourceProjectivelyEquivalentOddQuintic_cross_invariant,
    sourceProjectivelyEquivalentOddQuintic_of_cross_invariant hsq hq hqm hqt hr hrm hrt⟩

/-- **Infinitely many quintic orbits.**  Over the complex numbers the normalized quintics
`(1, n+1, 1)` are pairwise source-inequivalent, so arity five carries a continuous modulus. -/
theorem pairwise_not_sourceProjectivelyEquivalent_normalized :
    Pairwise (fun m n : ℕ =>
      ¬ SourceProjectivelyEquivalentOddQuintic
        (normalizedSourceOddQuintic (K := ℂ) (((m + 1 : ℕ) : ℂ)))
        (normalizedSourceOddQuintic (K := ℂ) (((n + 1 : ℕ) : ℂ)))) := by
  intro m n hmn
  refine normalizedSourceOddQuintic_not_projectivelyEquivalent_of_sq_ne ?_
  intro hsq
  have hnat : ((((n + 1) ^ (2 : ℕ) : ℕ)) : ℂ) = ((((m + 1) ^ (2 : ℕ) : ℕ)) : ℂ) := by
    push_cast at hsq ⊢
    exact hsq
  have hnat' : (n + 1) ^ (2 : ℕ) = (m + 1) ^ (2 : ℕ) := by exact_mod_cast hnat
  have : n + 1 = m + 1 := Nat.pow_left_injective (by norm_num) hnat'
  omega

end GaloisForLFunctions.HTGeometry
