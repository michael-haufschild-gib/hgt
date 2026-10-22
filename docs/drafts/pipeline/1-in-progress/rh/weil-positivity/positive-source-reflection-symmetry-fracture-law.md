# Positive-source / reflection-symmetry fracture law

- **ID:** `positive-source-reflection-symmetry-fracture-law`
- **Stage:** 1-in-progress
- **Type:** `[PAPER-PROVED CORE] [FORMAL CORE PARTIAL] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [UNCONDITIONAL] [RH-FACING]`
- **Question answered:** what common mechanism is seen only in fragments by the positive theta
  source, Julia orientation, the completed-density projective chart, affine zero ejection,
  hypertranscendence, Ward indices, and the failure of scalar RH criteria?

## Central answer

The corpus separates two operations that classical RH programs usually conflate.

1. **Oriented source completion.** A positive one-sided source produces a sector-contractive
   holomorphic channel. Its first moment supplies a sharp quadratic completion that is zero-free
   in the source half-plane.
2. **Reflection closure.** Functional-equation symmetry joins that channel to its oppositely
   oriented reflection. The symmetric codiagonal does not inherit the one-sided stability cone.
   Its divisor is created exactly at projective anti-phase collisions of the two channels.

This is the **source--symmetry fracture**: positivity controls an orientation, whereas reflection
restores symmetry by cancelling that orientation. Zero formation occurs at the cancellation
interface, not inside the positive source and not because the carrier lacks analytic or
differential complexity.

The Riemann problem is therefore not naturally a positivity problem and not naturally a
zero-free-homotopy problem. It is a terminal-capture problem for an oriented incidence current:
at the reflection-symmetric slice, are all anti-phase collisions captured by the fixed boundary?

## Law I: universal first-moment stability

Let `Re(s)>0`, `kappa>0`, and `M>0`. Suppose a complex channel `B` obeys

```text
Re(s) |B(s)| <= |s| Re(B(s))                       (sector)
```

at nonreal points and

```text
0 <= B(r) <= M r                                   (moment cap)
```

on the positive axis. Then

```text
Q(s) = (kappa^2-s^2) B(s) - kappa^2 M s
```

is zero-free on the open right half-plane.

For a positive source with finite first moment,

```text
B_mu(s) = integral (1-exp(-s t)) dmu(t),
M       = integral t dmu(t),
```

the source cone and moment cap follow before symmetrization. The separate card
`first-moment-quadratic-zero-free-law.md` contains the dependency-closed proof.

## Law II: exact theta reflection fracture

For the completed theta density, define

```text
F(z)  = integral rho(t) exp(i t z) dt,
E(z)  = (z^2+1/4) F(z)-1/4,
E#(z) = (z^2+1/4) F(-z)-1/4.
```

The corpus proves:

```text
E(z) != 0                         when Im(z)>0,
E(z)+E#(z) = 4 z^2 XiC(z)         when |Im(z)|<1.
```

Hence

```text
R(z)=E#(z)/E(z)
```

is a pole-free projective chart in the upper half-strip and, away from the central polynomial
factor,

```text
XiC(z)=0  iff  R(z)=-1.
```

Riemann zeros are therefore exact anti-phase collisions of two reflected source orientations.
This is a genuine object and not a decorative RH equivalence: the denominator is independently
proved zero-free by the source law.

## Law III: symmetry breaking has signed zero velocity

Put

```text
H_tau(z) = tau E(z) + (1-tau) 2 z^2 XiC(z).
```

At a positive real Xi zero `t` with negative simple slope, the corpus proves an analytic zero
branch after the incidence reparametrization `tau=c/(1+c)`:

```text
g(0)=t,
g'(0)=-E(t)/(2 t^2 XiC'(t)),
Im(g'(0))>0.
```

Thus arbitrarily small positive symmetry breaking ejects that zero into the open upper strip.
Endpoint zero-freeness cannot be transported to Xi through a zero-free homotopy. The signed normal
velocity, not an unsigned collision count, is the local datum that survives.

No existence or simplicity claim for such a zero is made here. The theorem is the exact
unconditional implication from its displayed local hypotheses.

## Law IV: differential complexity and divisor geometry are independent axes

The corpus proves that the completed Xi carrier is hypertranscendental and proves strong relative
differential-algebraic independence results for its shifts and associated frames. Yet the
one-sided completed theta channel is zero-free in its natural half-plane while the reflected
codiagonal has the Xi divisor.

Therefore:

```text
maximal differential complexity does not locate zeros;
reflection incidence, rather than differential closure, creates the divisor.
```

Hypertranscendence removes finite differential-algebraic explanations of the phase collision. It
does not itself orient or exclude the collision. This explains why a relative-independence theorem
can be a genuine obstruction while still stopping short of RH.

## The shadow map

| Corpus object | Exact information retained | Information lost |
|---|---|---|
| Positive theta source | one-sided orientation and sector contraction | reflected collision |
| Julia normal derivative | signed transverse source direction | global transport |
| Squared Julia coordinate | divisor location / magnitude | orientation |
| Projective ratio `E#/E` | exact anti-phase collision and signed Wronskian | terminal capture |
| Affine simple-zero motion | local signed incidence velocity | global component topology |
| `8 pi` Ward charge | quantized total collision count | sign and direction of each crossing |
| Weil/Hilbert/Gram scalarization | symmetric quadratic shadow | which reflected channel supplied phase |
| Kolchin independence | no finite differential-algebraic phase explanation | zero exclusion |
| Reflection parity / paired decks | orbit count modulo symmetry | displacement orientation |

These are not unrelated failed methods. They are functorial losses of the same oriented
two-channel incidence geometry.

## The new mathematical object

For a reflected pair `(E,E#)`, define the affine incidence surface

```text
Z = {(tau,z) : ((1+tau)/2)E(z)+((1-tau)/2)E#(z)=0}.
```

On the regular chart `E!=0`, this is the projective level set

```text
E#/E = -(1+tau)/(1-tau).
```

Its local orientation is the projective Wronskian

```text
W = (E#)' E-E# E',
```

and simple zeros have the universal affine velocity `-K/H'`. The object required by the RH
problem is the oriented incidence current carried by `Z`, including boundary entry, branch
coalescence, and noncompact escape. Existing Ward counts, Julia normals, and phase defects are its
scalar pushforwards.

This paper will not assert an unproved terminal-capture theorem. Its closed contribution is the
four-law package above: construction of a stable universal source class, exact identification of
the Xi divisor as reflection anti-phase incidence, exact signed ejection at simple boundary
collisions, and separation of differential complexity from divisor formation.

## What is genuinely answered

1. **Why source positivity has repeatedly stopped short of RH:** it controls one orientation;
   reflection symmetry cancels that orientation before Xi is formed.
2. **Why squaring and scalarization fail:** they quotient by the sign needed to distinguish
   inward from outward collision transport.
3. **Why a zero-free endpoint does not prove RH:** the affine ejection law permits interior zeros
   immediately after symmetry breaking.
4. **Why hypertranscendence does not locate zeros:** local differential complexity and reflected
   phase incidence are independent mathematical axes.
5. **What replaces the failed routes:** an oriented projective incidence surface with a universal
   local velocity and a source-generated zero-free chart.

## Hostile falsifiers

1. The first-moment theorem must fail for some channel satisfying both displayed hypotheses.
2. The theta completion identities or upper-half-plane zero-free chart must require RH.
3. The projective collision criterion must introduce a hidden denominator zero.
4. The affine ejection sign must disappear under exact differentiation.
5. Any claim that Xi is hypertranscendental must rely on an unproved zeta hypertranscendence
   premise.
6. Prior literature must already state the source-stability / reflection-fracture / signed-ejection
   package with the same theta channel.
7. The paper must not sell the remaining terminal-capture problem as solved.

Any hit retires or narrows the law.

## Closure ledger

- [x] paper proof of universal first-moment stability;
- [x] formal theta source cone and zero-free endpoint;
- [x] formal pole-free projective collision chart;
- [x] formal universal affine simple-zero velocity;
- [x] formal theta signed upper-strip ejection implication;
- [x] formal unconditional Xi hypertranscendence;
- [ ] formal abstract first-moment stability theorem;
- [ ] formal positive-density corollary at universal parameter;
- [ ] exact claim-to-theorem trace;
- [ ] primary-literature collision audit;
- [ ] publication manuscript;
- [ ] independent hostile referee report;
- [ ] final Lean, axiom, lint, PDF, and stale-process audits.

