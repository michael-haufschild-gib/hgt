# Persistent first-order HT tails have a tensor symbol and finite transient defect

- **ID:** nonautonomous-first-order-tail-symbol-defect-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** source-pure nonautonomous rational coarse-graining
- **Statement:** Every nonconstant differential-order-one observable surviving an arbitrary degree-expanding rational protocol has a nonzero transported integer tensor symbol; conversely every such tensor chain is a hypertranscendental persistent observable, and the positive tensor representative has only finitely many phases with zeros, bounded exactly by the initial zero divisor and prefix degree.

## Setup

Let `C` be algebraically closed of characteristic zero with trivial derivation.  At each phase
`i>=0`, let

```text
F_i=C<y_i>
```

be the differential rational field in one differential indeterminate.  Let a rational map
`R_i:P1_i->P1_(i+1)` of degree `d_i>=2` induce the injective differential pullback

```text
phi_i:F_(i+1)->F_i.
```

Write

```text
P_(i,n)=R_(i+n-1) composed ... composed R_i,
D_(i,n)=degree(P_(i,n)),
T_i=intersection_(n>=0) P_(i,n)^*F_(i+n).
```

The phase-tail isomorphism theorem gives `phi_i(T_(i+1))=T_i`.

## Theorem A: first-order symbol extraction

**[PROVED HERE]** The following are equivalent.

1. Some, hence every, `T_i` contains a nonconstant element of differential order at most one.
2. There are a nonzero integer `k` and nonzero rational `k`-differentials

   ```text
   omega_i=q_i(z)(dz)^k
   ```

   satisfying

   ```text
   R_i^*omega_(i+1)=omega_i                              (1)
   ```

   at every phase.

In this case

```text
Q_i=q_i(y_i)(delta y_i)^k                               (2)
```

is a hypertranscendental element of `T_i` and

```text
phi_i(Q_(i+1))=Q_i.                                      (3)
```

The integer `k` is the first nonzero Laurent weight at the vertical infinity of a transported
first-order observable.

## Proof of Theorem A

### 1. There is no nonconstant order-zero tail

Suppose rational functions `a_i in C(z)` satisfy

```text
a_i=a_(i+n) composed P_(i,n)                              (4)
```

for every `n`.  If `a_i` is nonconstant, then so is every `a_(i+n)`, and degree multiplicativity
gives

```text
degree(a_i)=degree(a_(i+n)) D_(i,n) >= D_(i,n) >= 2^n,
```

which is impossible for fixed `a_i`.  Hence `T_i intersect C(y_i)=C`.

### 2. Extract the vertical Laurent symbol

Choose a nonconstant `h_i in T_i` of order at most one.  Exact phase transport supplies unique
elements `h_(i+1) in T_(i+1)` with `phi_i(h_(i+1))=h_i`.  Step 1 forces every `h_i` to have order
exactly one.  In affine jet coordinates `(z,v)=(y_i,delta y_i)`, write

```text
h_i(z,v)=H_i(z,v) in C(z)(v).
```

The transport identity is

```text
H_i(z,v)=H_(i+1)(R_i(z),R_i'(z)v).                       (5)
```

Let

```text
k=degree_v(numerator H_i)-degree_v(denominator H_i).
```

Substitution of the nonzero scalar `R_i'(z)` for the vertical coordinate preserves this integer,
so `k` is phase-independent.  If `k!=0`, write the leading Laurent term at `v=infinity` as

```text
H_i(z,v)=q_i(z)v^k+lower vertical order.
```

Comparing leading terms in (5) gives

```text
q_i(z)=q_(i+1)(R_i(z)) R_i'(z)^k,                        (6)
```

which is exactly (1).

If `k=0`, the fiber-infinity value `a_i(z)=H_i(z,infinity)` obeys (4), so Step 1 makes it a
constant.  Equation (5) makes that constant independent of phase.  Since `H_i` genuinely depends
on `v`, the nonzero compatible family `H_i-a` tends to zero at vertical infinity and has a negative
Laurent weight.  Applying the preceding argument to this family again yields (1) with `k<0`.

This proves `1 implies 2`.  The construction is coordinate-independent: under an affine change of
projective coordinate the leading coefficient changes by the `k`-th power of the Jacobian, exactly
the transition law of a rational `k`-differential.

### 3. Reconstruct the persistent observable

Conversely (1) and the differential chain rule give

```text
q_(i+1)(R_i(y_i)) (R_i'(y_i) delta y_i)^k
  =q_i(y_i)(delta y_i)^k,
```

which is (3).  Iterating shows that `Q_i` lies in the image of every prefix and hence in `T_i`.

It is hypertranscendental.  Indeed, after clearing the numerator and denominator of `q_i`, equation
(2) is a nonzero algebraic differential equation for `y_i` over `C<Q_i>`; use the reciprocal
equation when `k<0`.  Thus `y_i` is differentially algebraic over `C<Q_i>`.  If `Q_i` were
differentially algebraic over `C`, transitivity would make `y_i` differentially algebraic over
`C`, contradicting its freeness.

## Theorem B: finite transient zero budget

Replace `omega_i` by `omega_i^(-1)` when `k<0`, and write the resulting positive order as `ell>0`.
Let `Z_i` be the total multiplicity of the zero divisor of this positive rational
`ell`-differential.

**[PROVED HERE]** For every prefix,

```text
Z_i >= D_(i,n) Z_(i+n).                                   (7)
```

Consequently

```text
Z_(i+n)>0  implies  D_(i,n)<=Z_i.                         (8)
```

Since `D_(i,n)>=2^n`, all sufficiently late phase tensors are zero-free.  More sharply, measured
from phase `i`, a phase with a tensor zero can occur only before

```text
n <= floor(log_2 Z_i).
```

### Proof

Let `P=P_(i,n)` and let `x` lie over a zero `y` of order `m>0` of `omega_(i+n)`.  If `e_x` is the
ramification index, the pullback order formula is

```text
ord_x(P^*omega_(i+n))=e_x m+ell(e_x-1)>=e_x m.             (9)
```

Summing (9) over the fiber of `y` gives at least

```text
m sum_(P(x)=y)e_x=m degree(P).
```

Fibers over distinct zeros are disjoint.  Summing over the terminal zero divisor proves (7), and
(8) follows.  Divergence of the prefix degree proves eventual zero-freeness.

## Corollary: eventual defect-free tensor transport

After the finite transient budget is exhausted, adjacent positive tensors are zero-free and every
map obeys the exact local order law

```text
ord_x(omega_i)+ell
  =e_x(R_i)(ord_(R_i(x))(omega_(i+1))+ell).                (10)
```

Thus the surviving first-order tail eventually becomes a defect-free meromorphic flat-structure
tower.  Formula (10) is the precise remaining holonomy data.  Proving that its rational cone
weights must be integral orbifold weights is a separate open theorem; it is not assumed here.

## Physical/topological meaning

The vertical jet coordinate is the infinitesimal resolution direction.  A persistent first-order
observable has an intrinsic high-velocity charge `k`; its leading symbol is not an arbitrary
function but a tensor field transported through every constraint layer.  Zeros of the positive
tensor are localized curvature defects.  Equation (7) says that a later defect must reproduce on
every sheet of the earlier description.  A finite initial divisor cannot pay that multiplicative
cost indefinitely, so only finitely many transient defect phases are possible.

This is a static holographic law: deep defects are replicated across inverse sheets and are
therefore forbidden by the finite boundary defect budget.  It uses no trajectory, Hamiltonian,
probability, numerical experiment, or continuous time.

## Novelty and significance gate

The ingredients are classical individually: rational-map degree, Laurent leading terms,
pullback of meromorphic tensors, and ramification order.  Targeted searches found work on
autonomous maps preserving parallel tensors and on nonautonomous rational dynamics, but no theorem
classifying persistent first-order differential-substitution tails by a transported tensor symbol
or giving the divisor inequality (7) as a finite transient law.  The closest autonomous parent is
Garofali's classification of maps with a parallel tensor:
[Dynamical systems with a parallel tensor](https://arxiv.org/abs/1806.10056).

The theorem is significant because it is a converse: no group, orbifold, or current is assumed.
Persistent first-order information forces the tensor geometry and a quantitative eventual
regularity law.  It advances the broad converse programme but does not by itself clear the
Fields-Medal gate: higher-minimal-order tails and integrality of the eventual holonomy remain open.

## RH impact audit

For any future source-pure rational protocol on a completed zeta or `L`-function differential
field, every RH-sensitive first-order persistent observable must carry the tensor symbol above and
must become zero-free after a finite phase budget.  This is a falsifiable structural obstruction,
but no zeta protocol or RH-sensitive tensor is presently supplied.  There is no direct RH
consequence.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/NonautonomousFirstOrderTailSymbol.lean` formalizes the
tensor evaluation and two-step composition laws, the local fibre multiplicity inequality, the
binary-logarithmic defect cutoff, eventual defect vanishing, and the finite exceptional-angle
budget.

`formal/GaloisForLFunctions/HTGeometry/NonautonomousFirstOrderTailSymbolLaw.lean` completes the
global finite-transient layer.  It proves that every phase-compatible tensor chain supplies an
explicit preimage through every finite protocol prefix and hence belongs to the actual
`nonautonomousTail`; a transcendental chain makes that tail nontrivial.  It also proves the exact
shifted-order identity `(10)`, sums the local ramification inequalities over the full terminal zero
divisor to obtain `(7)`, and derives zero-freeness once prefix degree exceeds the fixed source
budget.

The remaining stage-3 obligation is the converse half of Theorem A: construct the first-order
rational differential-function field, extract its nonzero Laurent symbol at vertical infinity,
and connect that extraction to the existing nonautonomous tail interface.  This is not hidden by
the abstract tensor-chain theorem, so the card remains at stage 2.

## Gates

- [x] 0 -> 1: exact first-order converse and divisor attack isolated
- [x] 1 -> 2: complete symbolic proof and finite-transient correction
- [x] exact tensor transport, prefix-tail membership, global divisor budget, and axiom audit
- [ ] 2 -> 3: Laurent-symbol extraction and the first-order tail-to-tensor converse in Lean
- [ ] 3 -> 4: independent novelty audit and standalone manuscript
