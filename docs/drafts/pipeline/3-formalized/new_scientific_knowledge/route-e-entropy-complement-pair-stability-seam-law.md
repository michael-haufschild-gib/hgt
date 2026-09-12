# Route E entropy-complement pair-stability and seam law

- **ID:** `ROUTE-E-ENTROPY-COMPLEMENT-PAIR-STABILITY-001`
- **Stage:** 3-formalized
- **Type:** `[LEAN-CERTIFIED] [POSITIVE SURVIVOR] [EXACT SEAM CLASSIFICATION]`
- **Parent:** `route-e-entropy-complement-breadth-mixture-load-law.md`,
  `route-e-approximate-transpose-divergence-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteEEntropyComplementPairStability.lean`

## Intrinsic factorization

For a fixed prime cutoff `P`, split the prime support of `n` into

\[
  L_P(n)=\{p\mid n:p\le P\},\qquad R_P(n)=\{p\mid n:P<p\}.
\]

These supports are disjoint and have union `primeFactors(n)`. If `n` is squarefree, then

\[
  n=\prod_{p\in L_P(n)}p\prod_{p\in R_P(n)}p,
\tag{1}
\]

and their cardinalities add to the complete distinct-prime breadth. Thus a reverse certificate
does not reuse the reservoir inserted at the other endpoint. It uses its own endpoint's unique
low/rough split.

## Exact pair-stability

Fix a seam `z` and any symmetric physical-shell predicate `S(n,q)`. On pairs satisfying

1. `n` and `q` are squarefree;
2. both are `z`-friable;
3. `gcd(n,q)=1`;
4. `S(n,q)`;
5. `Ω(q)=Ω(n)+1`,

swapping endpoints gives exactly the downward certificate from `q` to `n`. Freshness reverses by
coprimality symmetry, the shell reverses by assumption, and the breadth equality becomes the
downward equality without changing any branch after the fact. In Lean,

\[
  \operatorname{Up}(n,q)\iff\operatorname{Down}(q,n).
\tag{2}
\]

Every such edge reverses the squarefree Möbius sign. The concrete shell

\[
  |n-q|\le h(n),\qquad |n-q|\le h(q)
\tag{3}
\]

is symmetric and therefore satisfies (2).

## Exact seam boundary

For the one-sided seam relation, require only the terminal `q` to be `z`-friable; the source may
carry the single large prime. For every admitted upward edge,

\[
  \operatorname{Down}(q,n)iff n\text{ is }z\text{-friable}.
\tag{4}
\]

Equivalently, reverse-certification failure is exactly source nonfriability. It is not an
additional factor-decoder defect. On the friable/friable sector, intrinsic entropy-complement
factorization is pair-stable; the literal one-large-prime seam is the complete endpoint-sector
obstruction.

## Route consequence

The same-reservoir whole-anchor no-go does not retire the entropy-complement construction. Its
factorization is terminal-intrinsic, so the raw transpose mismatch no longer needs a generic
decoder-error term on the friable sector. Remaining arithmetic producers are:

1. loss from restricting one-sided supplied tokens to the symmetric shell (3);
2. row-normalizer variation;
3. pair-switch/history recombination collisions;
4. literal nonfriable-to-friable seam flux classified by (4).

The cutoff-separated low/rough projection itself has no collision multiplicity: its fibre over a
squarefree physical endpoint is exactly the intrinsic split. Companion
`route-e-entropy-complement-physical-incidence-fibre-law.md` proves this and identifies unit-weight
row mass with one physical adjacent-grade endpoint count. The one-radius oscillation theorem
bounds the purely numerical part of item 1. No joint short-interval mass,
chi-square/load-gradient estimate, or normalized seam-flux estimate is proved here.

## Verification

Direct foreground check passed:

```text
lake env lean GaloisForLFunctions/RHTower/RouteEEntropyComplementPairStability.lean
```

Targeted module build passed:

```text
lake build GaloisForLFunctions.RHTower.RouteEEntropyComplementPairStability
```

Module is wired into `formal/GaloisForLFunctions/RHTower.lean`. `#print axioms` on every public
theorem reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
