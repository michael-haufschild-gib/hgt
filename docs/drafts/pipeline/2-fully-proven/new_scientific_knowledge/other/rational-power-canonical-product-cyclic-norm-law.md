# Rational-power canonical products have an exact cyclic-norm parity law

- **ID:** `rational-power-canonical-product-cyclic-norm-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HYPERTRANSCENDENCE / COMPLETION LAW
- **Scientific status:** `[PROVED HERE] [PRELIMINARY NOVELTY PASS] [NOT AN RH RESULT]`
- **Source:** Bank's integer-power canonical-product theorem, the publication-ready
  multiple-elliptic-Gamma completion law, and the corpus search for a completion-stable
  hypertranscendence invariant
- **Statement:** For a reduced positive rational exponent `a=p/q`, the `q`-fold
  root-of-unity norm of the canonical product with zeros `-n^a` is exactly the
  integer-power product `W_p((-1)^(q+1)z^q)`.  Consequently the norm is DA exactly when
  `p` is even, and `W_(p/q)` itself is HT whenever `p` is odd.

## Goal

Replace the false heuristic

```text
finite HT stages should remain HT after completion
```

by an exact completion law for one classical parameterized family.  The theorem identifies two
separate pieces of arithmetic:

```text
q = finite monodromy orbit needed to close the completion,
p mod 2 = differential-algebraic phase of the completed orbit.
```

It strictly extends the known odd-integer hypertranscendence theorem to a dense set of
noninteger rational exponents.  It does not constrain a zeta zero and is not advertised as an
RH theorem.

## 1. Canonical products

For `g>=0`, put

```text
E_g(w)=(1-w) exp(sum_(r=1)^g w^r/r).
```

For a positive real `a`, let

```text
g(a)=floor(1/a),
W_a(z)=product_(n>=1) E_(g(a))(-z/n^a).                    (1)
```

The choice `g(a)` is admissible because

```text
a(g(a)+1)>1.
```

Thus `(1)` converges locally uniformly, is entire of order `1/a`, and has simple zeros exactly
at `-n^a`, `n>=1`.

Let `a=p/q` with coprime positive integers `p,q`, and let

```text
omega=exp(2 pi i/q).
```

Define the finite cyclic norm

```text
N_(p/q)(z)=product_(j=0)^(q-1) W_(p/q)(omega^j z).         (2)
```

## 2. Root-of-unity primary-factor identity

Let `g>=0`, `q>=1`, and put `h=floor(g/q)`.  For every complex `u`,

```text
product_(j=0)^(q-1) E_g(-omega^j u)
  =E_h((-1)^q u^q).                                       (3)
```

Indeed,

```text
product_j (1+omega^j u)=1-(-u)^q,
sum_(j=0)^(q-1) omega^(jr)
  = q  if q divides r,
  = 0  otherwise.
```

The exponential part of the left side of `(3)` is therefore

```text
exp(sum_(ell=1)^h (-1)^(q ell)u^(q ell)/ell),
```

which is exactly the exponential part on the right.

For `g=g(p/q)=floor(q/p)`,

```text
floor(g/q)=floor(1/p).                                    (4)
```

If `p=1`, both sides are one.  If `p>=2`, then `g<q`, so both sides are zero.

## 3. Exact cyclic-norm theorem

Apply `(3)` with `u=z/n^(p/q)` and use `(4)`.  Local uniform convergence permits grouping the
finite root-of-unity packet at each `n`, and gives

```text
N_(p/q)(z)
 = product_(n>=1) E_(floor(1/p))((-1)^q z^q/n^p)
 = W_p((-1)^(q+1) z^q).                                  (5)
```

No asymptotic equivalence, regularization, or exponential-polynomial counterterm occurs:
`(5)` is an exact identity for the standard minimal primary factors.

## 4. Algebraic-change lemma

Differential algebraicity over `C(z)` is invariant under the nonconstant algebraic change

```text
z |-> c z^q,   c!=0.                                      (6)
```

The forward direction follows by repeated chain rule.  Conversely, suppose `F(cz^q)` is DA.
On a simply connected punctured sector choose an algebraic branch

```text
phi(w)=(w/c)^(1/q).
```

Substitution `z=phi(w)` in an ADE for `F(cz^q)` and the triangular chain-rule conversion from
`z`-jets to `w`-jets show that `F(w)` is DA over the finite algebraic extension
`C(w,phi)`.  Differential algebraicity is unchanged by a finite algebraic extension of the
coefficient field, so `F` is DA over `C(w)`.  Hence

```text
F is DA  iff  F(cz^q) is DA.                              (7)
```

The same statement can be expressed by taking the field norm of the substituted differential
polynomial from `C(w,phi)` down to `C(w)`.

## 5. Hypertranscendence consequence

Bank's theorem, with the harmless sign change `z |-> -z`, gives

```text
W_p is DA over C(z)   iff p is even,
W_p is HT over C(z)   iff p is odd.                        (8)
```

For `p=1`, the odd branch is Holder's theorem; Bank's theorem includes it by reference to that
case.  For odd `p>1`, Bank proves the stronger conclusion over the Nevanlinna field
`Lambda_p`.

Equations `(5)`, `(7)`, and `(8)` imply the exact norm classification

```text
N_(p/q) is DA  iff p is even,
N_(p/q) is HT  iff p is odd.                              (9)
```

If `p` is odd and `W_(p/q)` were DA, every rotation
`W_(p/q)(omega^j z)` would be DA and their finite product `N_(p/q)` would be DA, contradicting
`(9)`.  Therefore

```text
p odd  ->  W_(p/q) is HT over C(z).                       (10)
```

The reduced positive rationals with odd numerator are dense in `R_(>0)`: use odd numerators
over powers-of-two denominators.  Thus `(10)` supplies a dense rational HT stratum, not merely
isolated integer examples.

## 6. Hostile audit and exact boundary

1. **Even numerator does not classify the factor.**  If `p` is even, `(9)` says only that the
   complete cyclic norm is DA.  For `q=1`, Bank gives that `W_p` is DA.  For `q>1`, no implication
   from a DA product to its individual factors is valid; the DA/HT status of `W_(p/q)` remains
   open here.
2. **Reduced form is load-bearing.**  Numerator parity before cancelling `p/q` is meaningless.
   The monodromy orbit has size the reduced denominator `q`.
3. **No factorization converse is smuggled in.**  The odd branch uses only the valid direction
   “all factors DA implies their product DA.”
4. **Algebraic pullback does not hide HT.**  Lemma `(7)` rules out the possible loophole that an
   HT integer product becomes DA after `z |-> z^q`.
5. **The primary genus is exact at reciprocal integers.**  When `p=1`, `g(1/q)=q`, and the
   root-of-unity filter leaves genus one, exactly matching `W_1`.
6. **The factor identity is elementary parent mathematics.**  Novelty is not claimed for
   root-of-unity filtering of primary factors.  The candidate new content is the resulting
   rational-exponent DA/HT norm classification and the individual odd-numerator consequence.
7. **Real rational exponents do not reach RH zeros.**  For a nonreal exponent, `n^s` lies on a
   logarithmic spiral and the rotation/monodromy orbit is infinite.  No finite norm like `(2)`
   closes it.  Proving HT for that infinite-orbit family is the next mathematical open core;
   connecting it to a source-forced reflection equality is a separate RH open core.

## 7. Completion insight

The theorem exhibits a direction of completion change not covered by the corpus's
stagewise-DA/limit-HT inverse-limit law:

```text
one rational-power factor
  --complete its finite monodromy orbit of size q-->
integer-power canonical product indexed by p
  --central ray pairing-->
DA exactly when p is even.                                 (11)
```

Thus “HT versus DA” is not the stable datum.  The stable finite datum is the monodromy orbit
together with its oriented ray charge.  Denominator records orbit closure; numerator parity
records whether the closed orbit admits complete opposite-ray pairing.

This also sharpens the completion warning from the multiple-elliptic-Gamma paper: a
regularized determinant can change differential phase not only through local counterterms, but
through finite monodromy completion of its entire divisor.

## 8. Literature audit

- S. B. Bank, *On Certain Canonical Products which Cannot Satisfy Algebraic Differential
  Equations*, Funkcial. Ekvac. 23 (1980), 335--349, proves `(8)` for integer `p` by pulling back
  to a finite Gamma-ray product.  It does not state `(5)`, `(9)`, or the noninteger conclusion
  `(10)`.
- C. Miller and P. Speissegger, *Expansions of the Real Field by Canonical Products*, Canad.
  Math. Bull. 63 (2020), 506--521, define the full real family `W_s`, obtain Barnes-type
  asymptotics and model-theoretic definability results, and cite Bank for odd integer members.
  Their paper does not state a rational-exponent DA/HT classification or cyclic-norm law.
- E. W. Barnes' 1905 asymptotic theory and A. A. Yukhimenko's 2010 asymptotics for products with
  zeros `-n^alpha l(n)` are analytic parent theory, not ADE classifications.
- Exact searches for rational powers, odd numerators, root-of-unity norms, and canonical-product
  hypertranscendence found no equivalent theorem.  This is an absence-of-hit result, not a
  priority certificate.

## Lean status

No Lean edit is claimed.  The finite primary-factor filter `(3)` is elementary, but formalizing
it alone would not formalize the scientific theorem.  The unconditional HT consequence depends
on Bank's analytic theorem, which is not available in the project's Lean analytic stack.
Encoding Bank as a hypothesis would violate the unconditional-proof rule.  Lean work is deferred
until the integer canonical-product theorem itself can be formalized without an axiom wrapper.

## Gates

- [x] internal corpus audit: no rational-exponent cyclic-norm classification found
- [x] exact conjecture and falsifiers stated
- [x] primary-factor identity proved for every positive rational exponent
- [x] algebraic-change loophole closed
- [x] odd-numerator HT consequence proved
- [x] even-numerator overclaim rejected
- [x] preliminary primary-source novelty audit completed
- [ ] independent full-text priority audit
- [ ] even-numerator noninteger factor classified or counterexample found
- [ ] infinite-monodromy/nonreal exponent theorem proved
- [ ] unconditional analytic Lean formalization

## Log

- 2026-07-27 — Bank's integer parity law was found, killing the proposed integer-temperature
  novelty claim.
- 2026-07-27 — Replaced it by the exact rational cyclic norm `(5)` and proved the
  odd-numerator individual HT theorem `(10)`.
- 2026-07-27 — Hostile audit isolated even-numerator factors and nonreal infinite monodromy as
  the two genuine open cores.
