# Imperfect-field rational-Witt inseparability descent

- **ID:** `deninger-imperfect-field-rational-witt-inseparability-descent`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) · LITERATURE PARITY · SOURCE CORRECTION INFRASTRUCTURE
- **Route:** L — rational-Witt source foundation
- **Primary source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1, Theorem 1.2.
- **Status:** `[LEAN-PROVED] [DEPENDENCY-CLOSED] [NOVELTY-UNCLEAR]`

## Statement

Let `K` be any field, `L` an algebraic closure, and `G = Aut_K(L)`.  For nonzero
`a in L`, put

```text
d(a) = [K(a) : K]_insep.
```

For `x = sum_a n_a [a] in Z[L^x]`, the following are equivalent:

```text
(i)  x is G-invariant and d(a) divides n_a for every a;
(ii) the literal rational-Witt vector represented by x lies in
     image(W_rat(K) -> W_rat(L)).
```

No perfectness assumption is made.  This is field-level imperfect clause needed before the
normal-domain repair of Deninger's unrestricted domain statement.

## Complete proof

For `a in L^x`, let `m_a` be its monic minimal polynomial over `K`.  Its roots in `L`, counted
with multiplicity, form canonical unit multiset `C(a)`.  Separably contract `m_a` in
characteristic exponent `q`:

```text
m_a(X) = g(X^(q^r)),   g separable.
```

After mapping to `L`, Frobenius is bijective and

```text
roots(m_a) = q^r · Frobenius^{-r}(roots(g)).
```

Roots of `g` are distinct.  Degree formula

```text
deg(m_a) = deg_sep(m_a) d(a)
```

therefore gives exact count

```text
count_b C(a) = d(a) if b is K-conjugate to a, and 0 otherwise.       (1)
```

Moreover, reversing split factorization of `m_a` gives

```text
reverse(m_a) mapped to L = product_{b in C(a)} (1-bT).               (2)
```

Now let finite unit multiset `s` be `G`-invariant and satisfy
`d(a) | count_a(s)`.  Choose `a in s`.  Galois invariance makes counts constant on conjugacy
orbit.  Positivity plus divisibility implies `d(a) <= count_a(s)`.  Equation (1) yields
`C(a) <= s`.  Subtracting `C(a)` preserves Galois invariance and divisibility, and strictly lowers
cardinality.  Induction and (2) construct normalized `P in K[T]` with

```text
P mapped to L = product_{b in s} (1-bT).                              (3)
```

Apply this independently to canonical positive and negative atom multisets of `x`; their quotient
is a rational-Witt vector over `K`, proving `(i) -> (ii)`.

For converse, first prove root-multiplicity divisibility for every `P in K[T]` and `z in L`:

```text
d(z) | rootMultiplicity_z(P mapped to L).                             (4)
```

If `z` is not root, claim is trivial.  Otherwise `m_z | P`.  Write `P=m_z Q`.  Equation (1) says
root multiplicity of `z` in mapped `m_z` is `d(z)`; multiplicities add under product.  Induction
on degree of `P` proves (4).  For normalized atom polynomial, polynomial reversal turns its roots
into its atom multiset exactly, so (4) gives divisibility of every atom count.  A base-field
rational-Witt fraction yields positive and negative multisets with this property, hence every
integer coefficient is divisible by `d(a)`.  Naturality gives Galois invariance.  Thus `(ii) ->
(i)`.

## Hostile audit

- No desired conclusion is assumed; only field, algebraic-closure, minimal-polynomial, and finite
  multiset facts enter.
- No perfect-field fixed-point theorem is used in forward direction; inseparable multiplicities
  are retained explicitly.
- Galois invariance alone is insufficient in imperfect characteristic; divisibility is used at
  exact orbit-block removal step.
- Result does not repair arbitrary nonnormal domains by itself.  Normality and normalization
  incidence remain necessary for descent from fraction field to domain.
- This is literature parity/source correction, not RH progress.

## Gates

- [x] 0 -> 1: exact imperfect-field source claim isolated
- [x] 1 -> 2: dependency-closed proof above
- [x] 2 -> 3: Lean module and umbrella audit
- [ ] 3 -> 4: publication treatment/external review


## Lean formalization

- **Field module:** `GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittInseparabilityDescent`
- **Field capstone:**
  `deningerRationalWittIntegralGaloisInvariantInsepDivisible_iff_exists_base`
- **Normal-domain module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittInseparabilityNormalDomainDescent`
- **Normal capstone:**
  `deningerRationalWittNormalDomain_galoisInvariant_insepDivisible_normalization_iff_exists_base`
- **Axiom audit:** only `propext`, `Classical.choice`, `Quot.sound`

## Log

- 2026-08-13 — exact inseparability-weighted conjugacy block and two-way field classification
  proved on paper; Lean scratch compiles without extra axioms.\n- 2026-08-13 — promoted to two umbrella-wired modules. Direct checks and exact downstream module\n  build pass; axiom audit reports only standard quotient/classical axioms.

