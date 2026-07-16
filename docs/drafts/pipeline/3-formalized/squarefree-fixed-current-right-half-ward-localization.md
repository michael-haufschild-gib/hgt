# The completed squarefree fixed current has exactly the Xi anti-causal divisor

- **ID:** `squarefree-fixed-current-right-half-ward-localization`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / ANTI-CAUSAL WARD LOCALIZATION
- **Lean:** `formal/GaloisForLFunctions/RHTower/SquarefreeFixedCurrentLocalization.lean`
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT A NOVELTY CLAIM] [NOT AN RH PROOF]`
- **Parents:**
  - `../3-formalized/not_new_scientific_knowledge/mfree-telescope-right-half-divisor-localization.md`
  - `mobius-fixed-current-von-mangoldt-critical-transport-weld.md`
  - `not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`
- **Statement:** Replacing the Euler logarithmic current in the infinitesimal completed Xi source
  by the logarithmic current of the positive squarefree partition function changes the symbol only
  by a doubled-zeta current holomorphic in the strict right half-plane.  Therefore the strict
  anti-causal profile is still exactly `ell_E`.

## Squarefree fixed current

Put

```text
Z_sq(s)=sum_n mu(n)^2n^(-s)=zeta(s)/zeta(2s),
A(s)=-zeta'(s)/zeta(s).                                  (1)
```

On `Re s>1`, logarithmic differentiation gives

```text
J_sq(s)=-Z_sq'(s)/Z_sq(s)=A(s)-2A(2s).                  (2)
```

This is the additive fixed current of the positive squarefree Gibbs partition function.  On the
moving critical aperture `s=sigma+u(sigma-1)`, `(2)` is equivalently the exact Ward decomposition

```text
epsilon A(s)
 =-partial_u log[Z_sq(s)/Z_sq(sigma)]
   +2epsilon A(2s).                                      (3)
```

The first term is the squarefree logarithmic score current; the second is its even-shift
correction.

## Completed current comparison `[PROVED HERE]`

Let the common archimedean/boundary current be

```text
Q_arch(s)=-2/s-2/(s-1)+log(pi)-psi(s/2).                 (4)
```

The actual infinitesimal Xi source and the squarefree-completed source are

```text
Q_Xi(s)=Q_arch(s)+2A(s)=-2Xi'(s)/Xi(s),
Q_sq(s)=Q_arch(s)+2J_sq(s).                              (5)
```

Equations `(2)` and `(5)` give

```text
Q_Xi(s)-Q_sq(s)=4A(2s).                                  (6)
```

For every `Re s>1/2`, one has `Re(2s)>1`, so zeta is holomorphic and nonzero at `2s`.  Hence
`A(2s)` is holomorphic throughout the strict right half-plane.  Its pole at `s=1/2`, coming from
the Euler pole of zeta, is a boundary contact; all continued nontrivial-zero poles `s=rho/2` lie
strictly to the left because `0<Re rho<1`.

Therefore `(6)` has no strict right-half principal part.  The anti-causal Hardy principal-part
profiles of `Q_Xi` and `Q_sq` are identical:

```text
P_anti Q_sq=P_anti Q_Xi=ell_E.                           (7)
```

No Xi zero expansion is needed to define the left side of `(7)`.  Expanding principal parts only
after `(7)` recovers

```text
ell_E(t)=2sum_j m_j exp(-(a_j+i gamma_j)t).
```

## Ward consequence

The anti-causal estimate may now be attacked entirely on the positive squarefree source:

```text
||P_anti Q_sq||_2^2<=4  implies RH.                      (8)
```

This is not merely the generic Xi criterion with a renamed symbol.  The finite-side source of
`Q_sq` is the same positive squarefree Gibbs law whose incidence curvature, Fisher tangent,
affine packet flux, and four-unit critical energy are already proved.  Equation `(7)` is the exact
right-half localization needed to attach that geometry to the divisor channel.

Together with `complementary-packet-affine-flux-fisher-ward-isometry.md`, the remaining theorem is
the cofinal closed-graph identity

```text
completed squarefree affine-flux Ward curvature
 =Hardy block curvature of Q_sq.                         (9)
```

Boundary unitarity then splits the curvature as

```text
four-unit source curvature
 =causal Ward energy+||ell_E||_2^2,                      (10)
```

which would prove the desired bound.

## Exact Fisher numerator and quotient graph

The singularity of the remaining graph theorem is explicit.  Let

```text
B_sigma(u)=Z_sq(sigma+u epsilon)/Z_sq(sigma)
```

and let `S_sigma(u)` be the Laplace matrix coefficient of the completed squarefree Fisher tangent.
Differentiation of `B_sigma` gives

```text
S_sigma(u)
 =2[partial_u B_sigma(u)+epsilon J_sq(sigma)B_sigma(u)]
 =2epsilon B_sigma(u)
   [J_sq(sigma)-J_sq(sigma+u epsilon)].                  (11)
```

Hence

```text
epsilon J_sq(sigma+u epsilon)
 =epsilon J_sq(sigma)-S_sigma(u)/(2B_sigma(u)),          (12)
```

and, without division,

```text
epsilon B_sigma(u)J_sq(sigma+u epsilon)
 =-partial_u B_sigma(u).                                 (13)
```

Equation `(13)` is the Fisher-controlled numerator.  Equation `(12)` is the logarithmic fixed
current.  On continuation, every zero of `B_sigma` produces the divisor pole of that quotient.
Thus the anti-causal Ward estimate is exactly a graph-divisibility theorem for multiplication by
the completed squarefree overlap; it is not a bounded linear image of the Fisher tangent.

This gives an anti-theatre test for `(9)`: a proof must construct the source-selected quotient on
the Gamma/Sonin graph and control its Hardy curvature.  Merely naming a current readout while
using `(12)` implicitly has assumed the exceptional divisor problem.

## No-go and positive HT consequences

### 1. Even-shift remainder no-go

The correction `2A(2s)` is nonzero and cannot be discarded as an algebraic simplification.

**Positive theorem:** it is holomorphic in the entire strict anti-causal half-plane and changes
only the causal/boundary current.

**HT consequence:** a nontrivial fixed-current correction may be geometrically invisible to one
oriented boundary sector without vanishing globally.

### 2. Positive coefficients do not prove the estimate

The squarefree coefficients are positive, but positivity of a Dirichlet series in its convergence
half-plane does not control zeros of its continuation.

**Positive theorem:** the right-half divisor nevertheless belongs exactly to this positive
partition function; no signed arithmetic channel remains in the localization step.

**HT consequence:** continuation orientation can be carried by the renormalization torsor of a
positive HT partition function rather than by signs of its coefficients.

### 3. Rational-gauge attack

A centered rational quartet multiplying Xi changes `Q_Xi` but not `Q_sq`, so `(6)` fails for the
gauged completion.

**Positive theorem:** `(6)` is source-framed by the exact identity `Xi=gamma*zeta`; it rejects the
standard symmetric rational-gauge countermodel.

**HT consequence:** equality of anti-causal currents can be rigidly source-specific even when the
ambient functional-equation class admits arbitrary divisor insertions.

### 4. Bounded Hellinger-lift no-go

The numerator `(13)` is controlled by the Fisher geometry, but the current `(12)` divides by an
overlap which may vanish after continuation.

**Positive theorem:** the exact multiplication graph and its numerator are source-defined before
the divisor is read.

**HT consequence:** fixed-current extraction is a graph quotient of a multiplicative torsor;
divisor orientation is encoded by range failure, not by the norm of the tangent numerator.

## Novelty and anti-theatre gate

The identity `Z_sq=zeta/zeta(2s)`, logarithmic differentiation, and right-half zero-freeness of
`zeta(2s)` are classical.  No novelty is claimed for those pieces or for their short combination.
Its value is proof-theoretic: it makes the Ward estimate act on the already constructed positive
squarefree HT geometry without changing the anti-causal divisor.

The card does not prove `(9)`--`(10)` and therefore does not prove RH.

## Formal surface

Lean represents the strict-right divisor statement directly by equality of local meromorphic
orders, rather than introducing an additional undefined `P_anti` operator.  The module proves:

- `squarefreePartition_eq_zero_iff_riemannZeta_eq_zero`;
- `squarefreePartition_meromorphicOrderAt_eq_riemannZeta`, preserving multiplicity away from the
  Euler pole;
- `neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent`;
- `analyticOnNhd_infinitePrimeFlux_two_mul_rightHalf`;
- `completedXi_sub_completedSquarefree_eq_four_mul_infinitePrimeFlux_two`;
- `deriv_squarefreeBoundaryOverlap_eq_neg_mul_fixedCurrent`;
- `epsilon_mul_overlap_mul_fixedCurrent_eq_neg_deriv`;
- `squarefreeFisherScore_eq_fixedCurrent_difference`.

The cached leaf build
`lake build +GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization` passes.  A separate
`#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound` for every exported
headline theorem above.

## Gates

- [x] squarefree fixed current computed
- [x] exact even-shift Ward decomposition proved
- [x] doubled-zeta correction proved strict-right holomorphic
- [x] Xi and squarefree anti-causal principal parts identified
- [x] rational-gauge falsifier passed
- [x] exact Fisher numerator/fixed-current quotient identity proved
- [x] 2 → 3 formalized: strict-right zero set, divisor multiplicities, holomorphic correction,
  completed-current comparison, and Fisher identities checked in Lean
- [ ] prove completed affine-flux/Hardy block-curvature identity
- [ ] prove source-selected graph divisibility and quotient control
- [ ] prove causal Ward energy is nonnegative on the graph core
- [ ] prove four-unit anti-causal bound
- [ ] RH
