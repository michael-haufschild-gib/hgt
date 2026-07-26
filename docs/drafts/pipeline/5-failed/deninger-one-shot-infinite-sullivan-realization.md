# One-shot infinite Sullivan realization

- **ID:** `deninger-one-shot-infinite-sullivan-realization`
- **Stage:** 5-failed
- **Type:** LITERATURE-CLOSED REALIZATION NO-GO
- **Parent:** `deninger-relative-sullivan-milnor-character-space`
- **Positive survivor:** `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`

## Proposed shortcut

Apply ordinary rational Sullivan spatial realization directly to the
rational form of the relative model
\[
 \Lambda(V_{F,\mathbb Q})\longrightarrow Q_{F,\mathbb Q}
 \xrightarrow{\sim}\mathbb Q\oplus V_{F,\mathbb Q}
\]
and declare \(|Q_F|\to|\Lambda(V_F)|\) to be the local Milnor character
map.

## Failure

For every algebraic \(F/\mathbb Q\) containing all roots of unity,
\[
 V_{F,\mathbb Q}=(F^\times/\mu_\infty)\otimes\mathbb Q
\]
is infinite-dimensional.  Indeed, the rational primes give an infinite
linearly independent family: a rational linear relation can be cleared of
denominators to give a product of integral prime powers equal to a root of
unity; positivity and unique factorization force every exponent to vanish.

Hence
\[
 H^1(Q_{F,\mathbb Q})\cong V_{F,\mathbb Q}
\]
is not of finite type.  Zhou's Theorem 1.1 and Corollary 1.2 state that a
minimal Sullivan algebra can be quasi-isomorphic to the polynomial forms on
its ordinary realization only if its generator space, equivalently in the
applicable conclusion its cohomology, is of finite type.  After replacing
\(Q_{F,\mathbb Q}\) by a minimal Sullivan model, the canonical one-shot realization
therefore cannot have
\[
 A_{PL}(|Q_{F,\mathbb Q}|)\simeq Q_{F,\mathbb Q}.
\]

Thus ordinary rational spatial realization of the full infinite unit
algebra cannot prove the required Milnor cohomology comparison; tensoring
the failed comparison with \(\mathbb R\) does not repair it.

## Positive survivor

Finite-unit Sullivan realization also fails at rank two, as recorded in
`deninger-fiberwise-finite-sullivan-pro-realization`.  The surviving
finite-stage topological object is instead the classifying space of
Baumslag's free rational group.  It retains free-group rational homology
and has a divisible kernel over its rational abelianization.  Coherent
finite-unit assembly is formulated in
`deninger-baumslag-milnor-pro-realization`.

## No-go closure

- **Negative statement:** one-shot ordinary Sullivan realization cannot
  recover the infinite-dimensional Milnor algebra.
- **Sharp boundary:** ordinary Sullivan realization is safe only when its
  minimal generator space satisfies the finite-type criterion; rank-two
  free fundamental groups already fail it.
- **Positive replacement:** Baumslag free-rational packets assembled
  fiberwise.
- **Lean status:** literature/topological realization theorem; not yet
  formalized in Lean.

**Verdict:** `FAILED; FINITE-STAGE PRO-REALIZATION SURVIVES`.

## Reference

- Jiawei Zhou, *Cohomology of minimal Sullivan algebras of non-finite type
  and their realizations*, Theorem 1.1 and Corollary 1.2:
  https://arxiv.org/abs/2407.20881
