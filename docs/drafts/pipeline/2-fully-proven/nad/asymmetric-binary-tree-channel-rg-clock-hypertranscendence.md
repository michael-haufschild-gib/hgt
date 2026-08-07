# Every strictly positive informative binary-tree channel has an HT homogeneous BP clock

- **ID:** `asymmetric-binary-tree-channel-rg-clock-hypertranscendence`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / TRANSFER-CHANNEL UNIVERSALITY
- **Scientific status:** `[PROVED HERE] [PARENT-DERIVED CLASSIFICATION]`
  `[ASYMMETRIC BINARY CHANNEL] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[FORMULA-LEVEL NOVELTY SEARCH PASSED PROVISIONALLY] [SPECIALIST AUDIT OPEN]`
  `[NOT A QUANTUM OR CONTINUUM-QFT THEOREM]`
- **Scope:** general hypertranscendence in exact tree inference and scale generation; no RH or
  distinguished-special-function input
- **Statement:** Let a strictly positive, positively informative binary channel be copied on every
  edge of a regular `p`-ary tree, `p>=2`.  On the exact homogeneous likelihood-message submanifold,
  its belief-propagation recursion has a hypertranscendental exact message-to-depth beta and clock
  in every locally invertible DA message scheme.  This holds for every channel asymmetry and every
  nonzero information strength.  The proof uses strict channel positivity to produce the
  non-superattracting real basin that excludes every Ritt-integrable rational map.

## Channel and exact homogeneous recursion

Write the row-stochastic binary channel as

```text
P(+|+)=alpha,       P(-|+)=1-alpha,
P(+|-)=gamma,       P(-|-)=1-gamma,                            (1)
```

and assume

```text
0 < gamma < alpha < 1.                                          (2)
```

Thus all four transition probabilities are positive and the child is positively informative about
the parent.  Put

```text
u=2 alpha-1,             v=2 gamma-1,
-1 < v < u < 1.                                                   (3)
```

Parameterize an incoming child likelihood message by `y in [-1,1]`:

```text
mu_y(t)=(1+t y)/2,             t in {+1,-1}.                    (4)
```

One branch contributes parent likelihoods

```text
w_+(y)=sum_t P(t|+) mu_y(t)=(1+u y)/2,
w_-(y)=sum_t P(t|-) mu_y(t)=(1+v y)/2.                          (5)
```

For `p` conditionally independent identical descendant branches, the common factor `2^(-p)`
cancels from the projective likelihood.  Exact homogeneous belief propagation is therefore

```text
                         (1+uy)^p-(1+vy)^p
R_(p;u,v)(y) = -----------------------------------------.        (6)
                         (1+uy)^p+(1+vy)^p
```

The symmetric BSC/zero-field Ising family is the slice `v=-u`.  Equation `(6)` is genuinely larger:
it contains every strictly positive positively correlated asymmetric binary channel.

## Rational degree, noncancellation, and monotonicity

Put `A(y)=1+uy` and `B(y)=1+vy`.  On `[-1,1]`, assumptions `(3)` give

```text
A(y)>0,                    B(y)>0.                              (7)
```

The primitive numerator and denominator of `(6)` have no common complex zero.  A common zero would
give `A^p=B^p=0`, hence `A=B=0`; subtracting the two affine equations gives `(u-v)y=0`, and then
`1=0`.  At least one of the leading coefficients `u^p-v^p` and `u^p+v^p` is nonzero, since their
simultaneous vanishing would force `u=v=0`.  Therefore

```text
deg R_(p;u,v)=p >= 2.                                            (8)
```

Direct differentiation gives

```text
R_(p;u,v)'(y)
  = 2p(u-v) A(y)^(p-1) B(y)^(p-1)
      / (A(y)^p+B(y)^p)^2
  > 0                         for -1 <= y <= 1.                  (9)
```

Moreover `|R(y)|<1` on the closed interval because `A^p,B^p>0`.  Thus strict stochastic
positivity becomes a global complex-dynamical discriminator: the physical real interval is mapped
strictly into its interior and the map is orientation-preserving there.

## Three multiplier regimes

The uninformative message `y=0` is a fixed point with exact multiplier

```text
lambda=R_(p;u,v)'(0)=p(u-v)/2=p(alpha-gamma)>0.                  (10)
```

### I. Contractive information: `0<lambda<1`

Zero is attracting but not superattracting.  The normalized local Schröder function `Phi` satisfies

```text
R(Phi(z))=Phi(lambda z),       Phi(0)=0,       Phi'(0)=1.        (11)
```

The Becker--Bergweiler classification permits a DA Schröder function only at a repelling fixed
point of a rational map of degree at least two.  Hence `Phi` is HT.

### II. Critical information: `lambda=1`

Zero is rationally indifferent.  The map cannot be the identity because its degree is `p>=2`.
Leau--Fatou petals therefore exist, and every sectorial Abel coordinate

```text
A_0(R(y))=A_0(y)+1                                               (12)
```

is HT by Becker--Bergweiler.  The sectorial beta `1/A_0'` is HT by the same antiderivative
argument as in the Bethe theorem.

### III. Expansive information: `lambda>1`

Let `H(y)=R(y)-y`.  Then `H(0)=0` and `H'(0)=lambda-1>0`, so `H(y)>0` for all sufficiently small
positive `y`.  Strict interval mapping gives `H(1)=R(1)-1<0`.  Let `c` be the first positive zero
after that initial positive interval.  Then

```text
0<c<1,             R(c)=c,             0<R'(c)<=1.              (13)
```

The upper bound follows from the left derivative at the first crossing; strict positivity follows
from `(9)`.  Thus `c` is either attracting but not superattracting or parabolic.

At zero, the normalized Poincare function again satisfies `(11)`, now with `lambda>1`.  If it were
DA, Ritt--Becker--Bergweiler would make `R` Möbius-conjugate to power/inverse-power, signed
Chebyshev, or elliptic/Weierstrass type.  Power and signed-Chebyshev maps have only
superattracting or repelling fixed cycles; elliptic/Weierstrass maps have no Fatou basin and all
periodic points are repelling.  None admits the non-super nonrepelling fixed point `(13)`.
Therefore the Poincare function at zero is HT.

## Exact beta, clock, and message-scheme theorem

When `lambda!=1`, let `kappa=Phi^(-1)`.  The exact homogeneous continuous iterate, beta, and
punctured depth clock are

```text
F_s(y)=Phi(lambda^s kappa(y)),
beta_y(y)=(log lambda) kappa(y)/kappa'(y),
tau_y(y)=log(kappa(y))/log lambda,
tau_y(R(y))=tau_y(y)+1.                                         (14)
```

The beta/clock equivalence proves that both are HT in regimes I and III.  At `lambda=1`, equation
`(12)` supplies the sectorial clock and beta.

If `x=h(y)` is any locally invertible DA likelihood-message chart, then local inversion,
composition, differentiation, and division transport DA in both directions.  Therefore the HT
verdict is invariant across every DA chart, including likelihood ratio, log-likelihood ratio,
odds, cavity field, and magnetization.

## Physical theorem and boundary

The theorem identifies a class-wide mechanism:

```text
strictly positive informative binary transfer
  + exact multiplicative aggregation on a regular tree
  -> an interior non-superattracting physical fixed point or an attracting zero
  -> exclusion of every finite-ADE exact message-depth generator.             (15)
```

The deterministic identity-channel boundary `alpha=1, gamma=0` is the symmetric noiseless power
map and is DA.  The uninformative boundary `alpha=gamma` collapses `(6)` to zero.  Other partially
degenerate boundary channels are not classified here.

This result concerns the deterministic homogeneous likelihood ray inside exact tree BP.  It does
not classify the full distributional BP operator, root reconstruction, mutual information,
channel capacity, loopy BP, or finite-depth decoding error.  For asymmetric channels the
Kesten--Stigum bound need not be the sharp reconstruction threshold; the present multiplier
classification must not be substituted for that stochastic theory.

## Quantum/QFT boundary and next theorem

Every positive two-state classical transfer tensor satisfying `(2)` is covered, so the theorem
applies to the diagonal binary sector of a tree tensor network whenever that sector is invariant
under contraction.  It does **not** prove the claim for a genuinely noncommutative quantum channel:
operator-valued messages need not remain on a projective line, and partial trace need not reduce to
two affine weights.

The next inheritance target is exact and falsifiable:

`[CONJECTURE]` Let a primitive completely positive transfer channel on a regular tree preserve a
faithful two-projection commutative subalgebra and let branch contraction multiply its two positive
likelihood components.  If the induced classical channel is strictly positive and informative,
then the expectation-value radial clock of that invariant sector is HT; if no such invariant sector
exists, an operator-valued replacement for the Ritt discriminator is required.

The first clause should become a theorem by proving the invariant-sector reduction, not by calling
the classical result quantum.  The second clause is the genuine noncommutative open core.

## Formula-level novelty audit

The external comparison separated three bodies of work:

1. broadcasting and reconstruction on trees, including asymmetric binary channels, studies root
   information, moment recursions, and reconstruction thresholds;
2. belief-propagation literature supplies exact sum-product recursion on trees and analyzes fixed
   points, contraction, and stability;
3. Becker--Bergweiler/Fernandes classify DA Schröder and Abel functions without applying the
   theorem to positive asymmetric channel recursions.

Searches combining asymmetric binary channels, tree BP, the affine-power formula `(6)`, rational
dynamics, Schröder/Abel functions, differential algebra, and hypertranscendence found the parent
literatures separately and no statement of `(8)`--`(15)`.  This is a provisional formula-level
novelty pass, not a priority proof.  Citation-graph and specialist audits remain required.

## Anti-theatre and dual gate

Exact BP, positive binary channels, and the functional-equation classification are parent theory.
The candidate new delta is the class theorem turning strict stochastic positivity into the global
non-Ritt fixed-point certificate `(13)`, and hence into scheme-invariant HT exact depth generation
for **every** channel in the open asymmetric parameter region `(2)`.

This is not merely the symmetric Ising theorem with renamed variables: `v` is independent of `u`,
and the proof replaces spin-flip symmetry by positivity and monotone first-crossing geometry.  The
novelty gate is provisionally positive.  The significance gate is positive as a universal theorem
for exact tree inference, but it is not Fields- or Nobel-level alone; the latter requires a
noncommutative quantum transfer theorem or an inherited continuum QFT/holographic observable.

## Lean boundary

The two affine branch likelihoods, exact rational family, symmetric Bethe specialization, fixed
anchor and multiplier, projective factor identities, noncancellation algebra, and exact derivative
cross-numerator factorization are now formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/AsymmetricBinaryTreeRG.lean`.  The real interval
first-crossing theorem and external HT classification are not represented by assumptions.

## Primary sources

- E. Mossel, *Reconstruction on trees: beating the second eigenvalue*,
  *Annals of Applied Probability* 11 (2001), <https://doi.org/10.1214/aoap/998926994>.
- W. Liu and N. Ning, *Reconstruction for the Asymmetric Ising Model on Regular Trees*,
  <https://arxiv.org/abs/1712.00395>.
- W. Liu and N. Ning, *Large Degree Asymptotics and the Reconstruction Threshold of the
  Asymmetric Binary Channels*, <https://arxiv.org/abs/1812.06039>.
- Q. Yu and Y. Polyanskiy, *Ising Model on Locally Tree-like Graphs: Uniqueness of Solutions to
  Cavity Equations*, <https://arxiv.org/abs/2211.15242>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- L. Di Vizio and G. Fernandes, *A Galoisian proof of Ritt theorem on the differential
  transcendence of Poincare functions*, <https://arxiv.org/abs/2102.08268>.

## Gates

- [x] Exact asymmetric-channel homogeneous BP map derived.
- [x] Degree `p` and primitive noncancellation proved.
- [x] Strict interval mapping and global monotonicity proved.
- [x] Attracting, parabolic, and repelling multiplier regimes classified.
- [x] Non-super nonrepelling fixed point proved in the repelling regime.
- [x] Every Ritt-integrable class excluded.
- [x] Exact beta/clock HT proved throughout the open channel region.
- [x] DA message-scheme invariance proved.
- [x] Reconstruction and QFT boundaries stated.
- [x] Formula-level novelty search completed provisionally.
- [ ] Citation-graph and specialist priority audit completed.
- [x] Unconditional asymmetric rational-family algebra formalized in HTGeometry.
- [ ] Invariant commutative sector of a primitive quantum transfer channel proved.
- [ ] Genuinely operator-valued quantum-channel discriminator proved.
