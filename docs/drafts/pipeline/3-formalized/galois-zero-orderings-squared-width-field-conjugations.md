# Orderings of the squared-width field and the conjugations they define

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** review-1211 §2.19 Q1 (an automorphism besides conjugation), Q3 (relations
  among the radicands); tool: Artin–Schreier theory of real fields.

`D = K(δ_q²)`, `L = D(√a_q)`, `a_q = −δ_q²` over the nonzero widths. An ordering of `D` is a
subsemiring `Q ∋` all squares, `−1 ∉ Q`, `Q ∪ −Q = D`.

## Theorems

1. **Artin–Schreier extension.** In a field, an element `a` outside a preordering `P` is
   negative in some ordering `Q ⊇ P`.
2. **Artin.** In a field with a preordering, `x` is a sum of squares iff `x` lies in every
   ordering.
3. **Conjugation of an ordering.** For an ordering `Q` of `D` there is exactly one
   `σ_Q ∈ Gal(L/D)` with `σ_Q √a_q = sgn_Q(a_q) √a_q` for all `q`. `σ_Q² = 1`. `σ_Q` fixes
   `√a_q` iff `a_q ∈ Q`.
4. `σ_Q` is complex conjugation iff every `δ_q²` is positive in `Q`; `σ_Q = 1` iff every
   `δ_q²` is negative in `Q`. The ordering induced by `ℝ` gives complex conjugation.
5. If `a_q ∈ Q` and `a_r ∉ Q` then `σ_Q` is neither `1` nor complex conjugation.
6. Every ordering of `D` defines complex conjugation iff every `δ_q²` is a sum of squares
   in `D`.
7. Every ordering of `D` defines `1` or complex conjugation iff every product `a_q a_r` is a
   sum of squares in `D`.

## Proof

1. `P − aP` is a preordering: if `−1 = x − a y` with `x, y ∈ P`, then `y ≠ 0` and
   `a = (1 + x) y (y⁻¹)² ∈ P`. A chain of preorderings has its union as upper bound; take a
   maximal `Q ⊇ P − aP`. For `b ∉ Q` maximality gives `Q − bQ = Q`, so `−b ∈ Q`. If
   `−(bc) ∈ Q` and `b, c ∉ Q` then `bc = (−b)(−c) ∈ Q`, so `bc = 0`, a contradiction; hence `Q`
   is an ordering.
2. The sums of squares form a preordering (they lie in the given one, so `−1` is not among
   them). If `x` is not a sum of squares, 1 gives an ordering with `−x ∈ Q`; with `x ∈ Q` this
   forces `x = 0`.
3. The sign `sgn_Q` is multiplicative on nonzero elements and `1` on squares. So the sign
   family `sgn_Q(a_q)` kills every square relation `∏_{q∈S} a_q ∈ D²`, and the Kummer theorem
   for `L/D` gives a unique automorphism with these signs.
4. Complex conjugation has all signs `−1`, the identity all signs `+1`; `a_q < 0` in `ℝ`.
6. By 4 and 2 applied to `−a_q = δ_q²`.
7. If all `a_q a_r` are sums of squares, the signs of an ordering are constant. Conversely an
   ordering with `−(a_q a_r) ∈ Q` (from 1) has different signs at `q` and `r`.

## Formalization

`GaloisTheoryOfZeros/TheOrderingsOfTheSquaredWidthFieldAndTheirConjugations.lean`:
`exists_isOrdering_neg_mem`, `isSumSq_iff_forall_isOrdering_mem`, `orderingSign_mul`,
`embeddingOrdering`, `orderingConjugation`, `orderingConjugation_radical`,
`orderingConjugation_radical_eq_iff`, `orderingConjugation_mul_self`,
`orderingConjugation_eq_conjugation_iff`, `orderingConjugation_eq_one_iff`,
`orderingConjugation_real`, `orderingConjugation_ne_of_mem_of_notMem`,
`forall_orderingConjugation_eq_conjugation_iff`,
`forall_orderingConjugation_eq_one_or_conjugation_iff`.

Checked with `lake --old env lean`; umbrella import wired.

## Open

Whether `δ_q²` or `a_q a_r` is a sum of squares in `D` for the zeros of ζ. An ordering of
`D` other than the real one with a negative squared width is not known to exist.
