# Residual differential independence of countable translate families

- **ID:** `residual-countable-translate-differential-independence`
- **Stage:** 5-failed / retired as new scientific knowledge
- **Type:** THEOREM (paper) / GENERIC HT TRANSLATION BRIDGE
- **Scientific status:** `[PROVED HERE] [PROJECT-LOCAL REDISCOVERY] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Significance score:** `not 90/100`; current evidence supports a specialist theorem, not a
  field-changing result
- **Statement:** For every discrete infinite real support, every positive summable base-mass
  sequence, and every prescribed countable set of distinct complex translations, a dense residual
  set of bounded positive mass gauges produces a meromorphic Herglotz function whose translated
  family is differentially algebraically independent over `C(z)`.

## The theorem

Let `lambda_n` be distinct real numbers with `|lambda_n| -> infinity`, let `b_n > 0` with
`sum b_n < infinity`, and let `H subset C` be countable. For `u in l-infinity(N,R)`, define

```text
f_u(z) = sum_n b_n exp(u_n)/(lambda_n-z).
```

There is a dense residual set `G_H` of gauges such that

```text
(f_u(z+h))_(h in H)
```

is differentially algebraically independent over `C(z)` for every `u in G_H`. Every `f_u` maps
the upper half-plane into itself.

## Complete paper proof

### 1. Finite real Cauchy-jet controllability

At finitely many distinct upper-half-plane nodes and finitely many jet orders, the vectors

```text
((lambda_n-zeta_j)^(-k))_(j,k)
```

span the complete complex jet space as a real vector space. If a real functional annihilated all
of them, a rational function would have purely imaginary values at infinitely many real support
points. Adding its reflected conjugate produces a rational function with infinitely many zeros.
The upper- and lower-half-plane pole sets are disjoint, so all principal parts vanish.

Choose finitely many support indices giving a surjective real-linear mass-to-jet map. A surjective
finite-dimensional real-linear map is open. Exponential gauge coordinates are local
diffeomorphisms onto open intervals of positive masses. Hence every sufficiently small gauge ball
moves the actual finite jet packet through a full real neighbourhood while preserving positivity.

### 2. Coefficient-uniform relation escape

Fix finitely many translates and jets, distinct differential monomials `M_r`, and a polynomial
coefficient-degree bound `q`. The functions `z^d M_r(x)` are linearly independent polynomials.
Choose `s(q+1)` upper evaluation pairs so that their square evaluation determinant is a nonzero
polynomial in the target jet packets.

Local openness lets every gauge neighbourhood reach a real-open set of packets. A nonzero complex
polynomial cannot vanish on such a set, so the nonvanishing gauges are dense. Uniform summable
majorants on bounded gauge balls give continuity, hence this set is open.

### 3. Baire argument and identity continuation

There are countably many finite relation patterns. Intersect their open dense escape sets in the
complete space `l-infinity(N,R)`. A differential relation over `C(z)` clears to one enumerated
polynomial-coefficient pattern and contradicts its invertible evaluation matrix.

If a relation is initially stated only as an upper-half-plane germ identity, all functions are
globally meromorphic, so the meromorphic identity theorem extends it to the fixed evaluation
nodes. This closes the domain gap identified by the referee.

## Retirement verdict

This theorem is a discrete/countable special case of
`herglotz-full-translation-ht-krein-index-orthogonality.md`, whose measure-universal theorem treats
bounded positive reweightings of every infinite-support Herglotz measure and whose discrete
corollary allows the same arbitrary real supports. Its finite-support Baire mechanism is also an
instance of the earlier fixed-fiber genericity method in
`fixed-divisor-maximal-translation-ht-genericity.md`, already classified as a bridge.

The referee repair produced a correct and cleaner proof, but it did not produce a new theorem.
The TeX and PDF are retained in this retired folder as a self-contained exposition and as evidence
of the repaired proof. They must not be cited as a publication-ready new result.

## What is and is not new

The candidate new component is the residual compatibility of positive discrete Cauchy masses with
differential algebraic independence of an arbitrary prescribed countable translation family.

The following are not claimed as new:

- rational additions preserve the generated differential field;
- sign changes of isolated Cauchy residues can destroy the Herglotz property;
- facet restriction gives coordinate embeddings for Stanley--Reisner modules;
- independently constructed encodings can coexist in one large free differential field.

The prime-log specialization has no arithmetic content: the proof uses only infinitely many
distinct real support points. The paper makes no RH claim or RH-route claim.

## Literature boundary

The exact theorem is compared with:

1. common hypercyclic vectors for translation operators, which concern orbit density rather than
   differential-algebraic rank;
2. Adamczewski--Dreyfus--Hardouin on hypertranscendence of solutions to fixed linear shift,
   `q`-difference, and Mahler equations;
3. Adamczewski--Dreyfus--Hardouin--Wibmer on algebraic independence for solutions governed by
   independent difference operators.

Targeted searches have not located the exact residual positive-Cauchy theorem. Priority remains
`NEEDS SPECIALIST AUDIT`; absence from a targeted search is not proof of novelty.

## Referee response

The controlling repair checklist is
`docs/reports/universal-constraint-orientation-referee-repair-1207.md`. The prior `90/100` score,
product title, nonlinear Stanley--Reisner realization claim, pointing law, and RH rhetoric are
withdrawn.

## Standalone retired exposition

The revised source and rendered manuscript are in
`docs/drafts/pipeline/5-failed/residual-countable-translate-differential-independence/`.
The manuscript is publication-formatted but retired from the publication pipeline.
