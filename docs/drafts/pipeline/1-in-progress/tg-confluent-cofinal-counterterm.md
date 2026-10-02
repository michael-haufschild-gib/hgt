# TG cofinal test of the mixed collision counterterm

- **ID:** TG-C6-CONFLUENT-COFINAL
- **Stage:** 1-in-progress; cofinal source theorem formalized, joint Gamma cancellation open
- **Route:** TG
- **Parent:** `tg-mixed-reflection-collision-counterterm.md`

## Hard question

Does the exact mixed source counterterm survive growing packets as a bounded operator/current
that can participate in a sub-unit source-to-Hardy transgression? Finite invertibility and
finite cancellation do not answer this question.

The current direct-subunit-anchor ledger, sections 12–14, rules out central Gamma ghosts,
equivariant absorption, and existing scalar-continuable Krein repairs. Its surviving target is
a noncentral signed/relative polar–Gamma colligation that remains an operator across the wall.
This card tests the new confluent counterterm against that operator requirement.

## Corpus evidence

`RHTower.dense_primeBurnolLiteralDepthSpan` proves that the literal unsquared columns at every
single prime already span a dense subspace of physical half-line L2. The new
`PrimeBurnolConfluentMomentGram` proves finite confluent independence, exact moment Grams and
Schur invertibility. `PrimeBurnolMixedCubicPrincipal` gives the actual reflected source's
principal coefficient. The existing two-prime depth-aliasing capacity theorem is a different
finite mechanism; it does not state the confluent single-prime conclusion below.

The targeted density search was partial (text/source stages interrupted), but returned the
literal density declarations, which were read directly. The separate Gamma search completed
with full inventory; it did not identify a matching mixed-inverse countercurrent. Compiler
freshness of broad corpus hits is incomplete, so proposed applications still require Lean checks.

The follow-up canonical-dual search completed (`partial=false`, no errors, complete inventory).
It returned generic inverse-Gram ingredients, but no matching single-prime cofinal escape result.
The exact source applications were subsequently verified in the production and axiom audits.

## Conjecture: canonical dual norms diverge

Fix a prime p and the packet of depths 0,...,N. Write f_j for its original Burnol columns,
h_j=r f_j, and P_N for orthogonal projection onto span(f_0,...,f_N). Let

```
w_j=(I-P_N)h_j,
K_N=Gram(w_j)=M_2-M_1 G_N^-1 M_1,
b_j=<f_j,f_0>,
z_N=sum_j (K_N^-1 b)_j w_j.
```

The exact finite identities should give

```
<f_j,z_N>=0,  <h_j,z_N>=b_j  (j<=N),
||z_N||²=(G_N K_N^-1 G_N)_(0,0).
```

For each fixed finite original-column combination y, all sufficiently large N satisfy
`<y,z_N>=0`, while `<h_0,z_N>=||f_0||²>0`. Density allows y to approximate h_0 arbitrarily
well. Cauchy–Schwarz gives

```
||f_0||² <= ||h_0-y|| ||z_N||,
```

forcing `||z_N|| -> infinity`. Consequently the positive matrix trace
`Tr(G_N K_N^-1 G_N)` should tend to infinity. For a single prime, actual theta U and V are
scalar matrices, so the checked cubic coefficient reduces to
`-v(u-1/2) Tr(G_N K_N^-1 G_N)`. This would exclude a uniform bound for that principal
counterterm at every grade with nonzero scalar factor. It would not exclude cancellation in
a new jointly renormalized prime–Gamma carrier.

## Positive survivor required before any retirement

The normalized dual directions `e_N=z_N/||z_N||` are unit vectors orthogonal to each fixed
original-column packet eventually. Density should give weak convergence to zero. Their
rank-one orthogonal projections consequently converge strongly to zero while each retains
rank one (and trace one in the appropriate trace interface). This is an explicit source-native
charge-escape mechanism, not merely a negative boundedness assertion. Its exact paper proof
and Lean formulation must be audited before retiring the bounded-counterterm candidate.

## Direct construction used in Lean

The proof avoids a separate orthogonal-projection API. For the complete family
`v=(f_0,...,f_N,h_0,...,h_N)`, set `H=Gram(v)` and `D=H^-1 [0;G]`. Define
`z_j=sum_i D_ij v_i`. The literal confluent inverse gives
`<f_i,z_j>=0`, `<h_i,z_j>=G_ij`, and `Gram(z)=G K^-1 G` directly. This is the
canonical residual dual described above, and these identities suffice for the density proof.
No separate unproved identification of an infinite projection or its inverse is used.

The operator conclusion is stronger than trace divergence: the finite positive synthesis
`B_N=sum_j |z_j><z_j|` satisfies `||B_N||>=||z_0||²`, hence its operator norm diverges.
The estimate follows by testing its quadratic form on `z_0`; every other summand is nonnegative.
This excludes growth caused solely by increasing rank. It does not identify `B_N` with a
joint prime–Gamma cubic operator or exclude cancellation in such an operator.

## Gates

- [x] Dependency-closed paper proof by the direct full-Gram construction above.
- [x] Production audit: canonical dual identities and squared-norm formula.
- [x] Production audit: cofinal dual, energy and operator-norm divergence; cubic dichotomy.
- [x] Production audit: normalized unit directions and self-adjoint rank-one strong-zero survivor.
- [ ] Determine whether an actual Gamma countercurrent cancels before completion.

The production audit passes without warnings. All 25 public theorem dependency audits contain
only `propext`, `Classical.choice`, and `Quot.sound`. The exact source results and positive
survivor are recorded in `../3-formalized/tg-confluent-cofinal-counterterm-escape.md`; the
bounded-uncompensated candidate is retired in `../5-failed/tg-bounded-confluent-counterterm.md`.
RH remains unproved.
