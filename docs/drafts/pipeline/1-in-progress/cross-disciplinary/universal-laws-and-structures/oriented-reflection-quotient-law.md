# Oriented reflection quotient law

- **ID:** `oriented-reflection-quotient-law`
- **Stage:** 1-in-progress
- **Type:** `[PAPER-PROVED CORE] [FORMAL CORE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [UNCONDITIONAL] [RH-FACING]`
- **Child laws:**
  `first-moment-quadratic-zero-free-law.md`;
  `positive-source-reflection-symmetry-fracture-law.md`.

## The universal reinterpretation

Let `E` be an oriented analytic channel and `E#` its reflected channel. On a domain where
`E != 0`, set

```text
R = E#/E,
J = (1+R)/(1-R) = (E+E#)/(E-E#).
```

Reflection exchanges the two channels. Therefore

```text
R  -> 1/R,
J  -> -J.                                             (ORQ)
```

The symmetric carrier is

```text
S=E+E#,
```

so, wherever the oriented chart is regular,

```text
S=0  iff  R=-1  iff  J=0.                             (DIV)
```

The coordinate `J` is the missing signed variable. Any reflection-invariant analytic reader of
the pair is even in `J`. An entire reader therefore descends canonically through `J^2`; every odd
origin jet vanishes, in particular its first derivative at a collision is zero.

This is the **oriented reflection quotient law**:

> Reflection-invariant methods live on the quotient coordinate `J^2`. The divisor lives at the
> branch locus `J=0`. Such methods can count or measure collisions but cannot determine their
> one-sided orientation. Orientation exists only on the unsquared two-sheeted lift.

## Canonical dynamics on the lift

For arbitrary analytic channels `A,B`, define

```text
R = B/A,
W = B' A-B A',
V = A^2 conjugate(W).
```

The universal projective flow identity is

```text
R' V = |W|^2.                                         (FLOW)
```

Consequently the projective ratio moves with real nonnegative velocity along every integral curve
of `V`; it is strictly oriented exactly where `W != 0`. Every affine mixture

```text
H_(alpha,beta)=alpha A+beta B
```

has zeros on the single projective level

```text
R=-alpha/beta.                                        (LEVEL)
```

Thus affine zero motion, boundary normal velocity, winding, and index are not separate
constructions. They are pushforwards of one oriented projective flow.

## Positive-source section

The quotient law by itself does not supply a regular chart. The positive source does.

For every right-half-plane channel satisfying

```text
Re(s)|B(s)| <= |s|Re(B(s)),
0 <= B(r) <= M r,
```

the first-moment quadratic completion

```text
(kappa^2-s^2)B(s)-kappa^2 M s
```

is zero-free. The completed theta density realizes this law at `kappa=1/2`, producing the
unconditional upper-half-plane chart `E != 0`.

Source positivity therefore has one exact role: it constructs an oriented section of the
reflection quotient. It is not expected to survive after passing to the symmetric carrier.

## Riemann--Xi specialization

For the completed theta channels,

```text
E(z)  = (z^2+1/4)F(z)-1/4,
E#(z) = (z^2+1/4)F(-z)-1/4,
E+E#  = 4z^2 XiC(z).
```

The corpus proves `E(z) != 0` for `Im(z)>0`. Hence, in the open upper theta strip and away from
the central polynomial factor,

```text
XiC(z)=0  iff  R(z)=-1  iff  J(z)=0.                  (XI)
```

At every regular collision, the theta projective Wronskian satisfies

```text
W=4z^2 XiC'(z)E(z),
```

and `(FLOW)` canonically orients it. At positive simple real collisions, the normal velocity is
the real Xi slope divided by the positive source boundary value. The affine ejection theorem is
the same orientation read in the pencil parameter.

RH is therefore a statement about where the zero set of the odd lift `J` meets the symmetric
slice. It is not naturally a statement about positivity of an invariant reader of `J^2`.

## Why the known objects are shadows

| Known construction | Quotient-law interpretation |
|---|---|
| Squared Julia coordinate | literal descent `J -> J^2`; divisor retained, sign erased |
| Unsquared Julia normal | first jet of the odd lift `J`; orientation retained |
| `8 pi` Ward quantum | doubled/invariant phase charge of reflected collision packets |
| Ward index | pushforward of oriented incidence current after sign quotient |
| Projective ratio `E#/E` | regular chart of the two-sheeted reflection lift |
| Projective Wronskian | Jacobian of quotient map; generator of canonical flow |
| Affine simple-zero velocity | local pullback of projective level motion |
| Reflection-paired deck/parity laws | orbit-space counts after `J` and `-J` are identified |
| Weil, Gram, Hilbert positivity | Hermitian/invariant readers; necessarily even at collision |
| CCM symmetric screw/index | invariant collision count, not oriented displacement |
| Scalar explicit formula | reflection quotient of a signed source/divisor identity |
| First-moment source cone | construction of a zero-free oriented section before quotient |
| Hypertranscendence | local differential complexity of carrier; independent of sheet selection |
| Relative Kolchin independence | finite differential algebra cannot manufacture a canonical sheet selector |
| Zero-free homotopy failure | projective level sets cross the lift; endpoint stability does not descend |

The table makes falsifiable structural claims, not analogies. Each row must be supported by an
exact theorem or narrowed in the manuscript.

## Derived laws

### 1. Invariant first-jet blindness

If `Phi` is differentiable and even, then

```text
Phi'(0)=0.
```

Thus no reflection-invariant scalar reader can supply the missing one-sided normal derivative at
an anti-phase collision.

### 2. Entire square descent

If `Phi` is entire and even, there is an entire `Q` with

```text
Phi(J)=Q(J^2).
```

The loss is global, canonical, and not an artifact of choosing a particular formula.

### 3. Projective monotonicity

Along canonical flow `V`,

```text
dR/dt=|W|^2 >= 0.
```

Regular collisions are automatically oriented; orientation disappears only after quotient.

### 4. Affine-level foliation

Every nondegenerate affine pencil is a family of projective level sets. Its zero trajectories are
therefore one foliation of the same incidence surface, not a separate RH mechanism.

### 5. Complexity/incidence separation

Hypertranscendence can rule out finite differential-algebraic closure while leaving `J=0`
untouched. Differential complexity belongs to each sheet; zero location belongs to their
incidence.

## What this answers

1. Why all symmetric positivity routes repeatedly reach exact equivalences but not orientation.
2. Why squaring the Julia coordinate is fatal even when it preserves every zero.
3. Why the `8 pi` law counts hypothetical defects without excluding them.
4. Why a zero-free source endpoint and a hypertranscendental carrier can coexist with a nontrivial
   symmetric divisor.
5. Why affine deformation produces signed ejection rather than zero-free transport.
6. Which new object must replace the old routes: the unsquared oriented projective incidence
   current on the two-sheeted reflection lift.

No terminal-capture or RH claim is made. The paper's closed theorem is the quotient law, its
canonical flow, the invariant-reader blindness/descent theorem, the universal positive-source
section, and their exact Riemann--Xi realization.

## Formal theorem surface

- `HTGeometry.reflectedChannelOddCoordinate_swap`;
- `HTGeometry.reflectedChannelOddCoordinate_eq_zero_iff`;
- `HTGeometry.reflectedChannelOddCoordinate_eq_cayleyRatio`;
- `HTGeometry.evenReader_firstJet_zero`;
- `GaloisForLFunctions.HTGeometry.evenEntireSquareFactor_sq`;
- `HTGeometry.reflectedChannelProjectiveDerivative_mul_flow`;
- `HTGeometry.hasDerivAt_reflectedChannelProjectiveRatio_comp_flow`;
- `HTGeometry.reflectedAffineCollision_iff_projectiveLevel`;
- `HTGeometry.reflectedMidpointCollision_iff_antiphase`;
- `HTGeometry.firstMomentQuadraticCompletion_ne_zero`;
- theta chart, collision, Wronskian, normal-velocity, and affine-ejection theorems already listed
  in the child cards.

## Hostile falsifiers

1. A claimed invariant reader depends on `J` rather than `J^2`.
2. Channel exchange does not act as `J -> -J` for the actual theta pair.
3. The Xi divisor criterion has a hidden denominator zero.
4. The projective flow law is only formal and cannot orient actual analytic level sets.
5. The `8 pi`, Hilbert/Weil/CCM, or Kolchin rows require more than the exact quotient statement.
6. Prior literature already presents this theorem package and its completed-theta Xi
   specialization.
7. Manuscript implies that quotient-law diagnosis proves terminal capture or RH.

Any hit narrows the corresponding row; hits 2, 3, or 6 retire the headline claim.

## Closure ledger

- [x] abstract odd-coordinate exchange law;
- [x] abstract anti-phase divisor law;
- [x] invariant first-jet blindness;
- [x] global even-entire square descent;
- [x] universal projective flow and affine-level laws;
- [x] universal first-moment quadratic stability;
- [x] exact theta zero-free oriented chart;
- [x] exact Xi anti-phase collision law;
- [x] exact theta projective Wronskian and boundary velocity;
- [x] exact conditional affine ejection law;
- [ ] exact theta `J -> -J` wrapper under channel reflection;
- [ ] narrow every shadow-table row to a proved implication;
- [ ] primary-literature novelty audit;
- [ ] publication manuscript and claim trace;
- [ ] hostile general-journal referee report;
- [ ] final Lean, axiom, lint, PDF, and stale-process audits.

