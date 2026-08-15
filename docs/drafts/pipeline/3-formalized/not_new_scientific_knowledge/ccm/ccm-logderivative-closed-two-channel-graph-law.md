# The completed logarithmic source has a canonical closed two-channel graph

- **ID:** `ccm-logderivative-closed-two-channel-graph-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Cartwright/Nevanlinna bounded-type factorization, outer-function majorants,
  closed multiplication operators, and Hardy projection
- **Statement:** The exact completed logarithmic source defines a densely defined closed graph into
  its causal and anti-causal Hardy channels, and its anti-causal Hankel component is closable.
  Rational FE--Schwarz orbit insertion acts by a bounded invertible graph gauge and a bounded
  finite-rank perturbation of the closed Hankel operator; each inserted upper-half-plane pole is an
  explicit rank-one residue/evaluation coordinate. Thus the orbit-sensitive meromorphic operator
  required by the CCM route exists canonically; the open theorem is its endpoint trace-slope bound.

## 1. Abstract two-channel graph

Let `H2_+` and `H2_-` be the upper and lower half-plane Hardy subspaces of `L2(R)`, with orthogonal
projections `P_+` and `P_-`. Let `q` be a measurable boundary function, finite almost everywhere,
such that

```text
integral_R log(1+|q(x)|)/(1+x^2) dx<infinity.             (1)
```

Define

```text
D_q={f in H2_+: qf in L2(R)},                            (2)

M_q^graph f=(P_+(qf),P_-(qf)).                           (3)
```

Then:

1. `D_q` is dense in `H2_+`;
2. `(3)` is a closed operator from `H2_+` to `H2_+ direct_sum H2_-`;
3. with

   ```text
   ||f||_(G_q)^2=||f||_2^2+||P_+(qf)||_2^2+||P_-(qf)||_2^2,   (4)
   ```

   `D_q` is a Hilbert space and both channel maps are contractions relative to the graph part of
   `(4)`.

### Dense outer core

Condition `(1)` permits an outer function `a in H-infinity_+` with boundary modulus

```text
|a(x)|=1/(1+|q(x)|)                                     (5)
```

up to an irrelevant positive normalization. Hence `aq in L-infinity`. For every `h in H2_+`,

```text
q(ah)=(aq)h in L2,
```

so

```text
aH2_+ subset D_q.                                       (6)
```

Because `a` is outer, `aH2_+` is dense in `H2_+`. This proves statement 1.

### Closedness

Suppose `f_n->f` in `H2_+` and

```text
(P_+(qf_n),P_-(qf_n))->(g_+,g_-)
```

in `H2_+ direct_sum H2_-`. Then

```text
qf_n->g_++g_- in L2.                                    (7)
```

Multiplication by a measurable finite-a.e. function is a closed operator on `L2`: from an
`L2`-convergent subsequence of `f_n` one gets pointwise convergence almost everywhere, and `(7)`
forces `qf=g_++g_-`. Thus `f in D_q`, and orthogonal uniqueness gives

```text
P_+(qf)=g_+,       P_-(qf)=g_-.                          (8)
```

This proves statement 2. Completeness of the graph norm and statement 3 are immediate.

The paired graph is essential. Neither projected channel alone is asserted to be closed in the
ambient `H2_+` norm; closedness belongs to the full source constraint `qf=g_++g_-`.

## 2. The anti-causal component is closable

Define the densely defined Hankel component

```text
H_q:D_q subset H2_+ -> H2_-,
H_q f=P_-(qf).                                            (8a)
```

Then `H_q` is closable.

### Proof

Condition `(1)` also supplies an outer function `b in H-infinity_-` in the lower half-plane with

```text
|b(x)|=1/(1+|q(x)|)                                     (8b)
```

almost everywhere. Since `b` is outer, `bH2_-` is dense in `H2_-`. For `h=bk` with `k in H2_-`,
one has `conjugate(q)h in L2` because `|q b|<=1`. For every `f in D_q`, orthogonality of the Hardy
projections gives

```text
<H_q f,h>_(H2_-)
 =<qf,h>_(L2)
 =<f,P_+(conjugate(q)h)>_(H2_+).                         (8c)
```

Thus

```text
bH2_- subset D(H_q^*).                                  (8d)
```

The adjoint domain is dense, so `H_q` is closable. Denote its closure by `bar(H_q)`.

This is stronger than paired-graph closedness: the anti-causal channel now exists as a canonical
closed unbounded operator on `H2_+`, without assuming that its kernel is Hilbert--Schmidt or that
its boundary trace is finite.

## 3. Bounded graph gauges and closed-operator covariance

Let `r in L-infinity(R)` and put `q_r=q+r`. Then

```text
D_(q_r)=D_q.                                             (9)
```

Moreover

```text
U_r(f,g_+,g_-)
 =(f,g_++P_+(rf),g_-+P_-(rf))                            (10)
```

is a bounded invertible map from the graph of `q` onto the graph of `q_r`, with inverse `U_(-r)`.

Indeed, `rf in L2` for every `f in H2_+`, proving `(9)`. Equation `(10)` is exactly the Hardy
decomposition of `(q+r)f`; its boundedness follows from `||rf||_2<=||r||_infinity||f||_2`.

Thus rational source insertion does not destroy the graph. It changes its two channel coordinates
by an exact, visible gauge action.

Its anti-causal part changes by the bounded Hankel operator

```text
H_r=P_-M_r|H2_+.                                        (10a)
```

Since a bounded perturbation commutes with closure,

```text
bar(H_(q+r))=bar(H_q)+H_r,
D(bar(H_(q+r)))=D(bar(H_q)).                             (10b)
```

Therefore rational orbit insertion is not merely a graph isomorphism: it is an exact bounded
perturbation law on the canonical closed anti-causal operator.

## 4. A pole is one residue coordinate

Let

```text
r_(w,c)(z)=c/(z-w),       Im w>0.                         (11)
```

Its boundary values belong to `L-infinity(R)` because `w` is separated from the real axis. For
every `f in H2_+` for which point evaluation is taken in the standard analytic representative,

```text
r_(w,c)(z)f(z)
 =c(f(z)-f(w))/(z-w)+c f(w)/(z-w).                       (12)
```

The first term is in the upper Hardy channel and the second is in the lower Hardy channel.
Therefore

```text
P_-(r_(w,c)f)(x)=c f(w)/(x-w).                           (13)
```

The anti-causal correction is rank one: it is the evaluation coordinate `f(w)` times the Cauchy
residue vector `c/(x-w)`. Under reflected Paley--Wiener transformation this vector is, up to the
fixed unitary normalization,

```text
c exp(-Im(w)t) exp(-i Re(w)t),       t>0.                 (14)
```

For the imaginary-axis family `w=i x`, `(14)` is exactly the Laplace feature
`c_x(t)=exp(-xt)` in the canonical diagonal Fock lift of the safe completed kernel.  Hence that
lift is the diagonal bundle of the present graph's anti-causal residue coordinates.  Sampling the
boundary vector `(x-i a)^(-1)` on the prime-log support gives the transported Cauchy family whose
all-finite-order divergence and exact finite-packet independence are formalized in
`PrimeLogHerglotz.lean` and `PrimeLogCauchySeamRank.lean`.  The resulting source-selected
contractivity criterion is recorded in `ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.

A pole of order `m` gives the expected finite jet of evaluations at `w`. Several poles give the
direct finite sum, with their mutual Cauchy Gram matrix. Hence the graph is orbit-sensitive before
any divisor is explicitly reconstructed.

## 5. Specialization to the completed Xi source

Put

```text
s=1/2-i z,
q_Xi(z)=-2 Xi'(s)/Xi(s).                                 (15)
```

The centered Xi function is Cartwright. It and its derivative are of bounded type in each
half-plane, so their quotient is meromorphic of bounded type. Its boundary values are finite away
from the discrete critical-line zero ordinates and satisfy `(1)`. Therefore Sections 1--3 give a
canonical densely defined closed graph

```text
G_Xi:
D_(q_Xi) -> H2_+ direct_sum H2_-,
f |->(P_+(q_Xi f),P_-(q_Xi f)).                           (16)
```

Section 2 additionally gives the canonical closed anti-causal operator

```text
D_Xi=bar(P_-M_(q_Xi)|D_(q_Xi)).                          (16a)
```

On the Euler half-plane, the same source is

```text
q_Xi
 =-2/s-2/(s-1)+log(pi)-psi(s/2)
   +2 sum_(n>=1)Lambda(n)n^(-s).                         (17)
```

Thus `(16)` is pointed by the exact all-prime and archimedean completion data, not merely by the Xi
divisor.

### Exact bilateral factorization of one source atom

For `t>0`, the polarized exponential atom carried by `(17)` satisfies

```text
(exp(-i conjugate(w)t)-exp(-i zt))/(z-conjugate(w))
 =i t integral_0^1
    exp(-i t(1-u)z) exp(-i t u conjugate(w)) du.          (17a)
```

Equivalently, on `L2(0,1)` put

```text
A_t(z)(u)=sqrt(t) exp(-i t(1-u)z),
B_t(w)(u)=sqrt(t) exp(i t u w).                           (17b)
```

Then `(17a)` is `i` times the cross-pairing of `A_t(z)` and `B_t(w)`. This is not a one-channel
positive Gram: the two feature maps have opposite causal orientation. It is the atomic form of the
paired graph `(16)`. Summing the von-Mangoldt atoms requires the graph domain because the critical
weight relative to the Gamma diagonal recedes like

```text
((log p)/sqrt(2)) p^(k/2)sqrt(1+p^(-4k)).                 (17c)
```

Thus the exponential Loewner kernel and the unbounded half-weight are both already native to the
canonical two-channel graph; neither should be replaced by an Euler-region Cauchy Gram.

Now multiply Xi by an FE--Schwarz orbit polynomial `A`. Its source becomes

```text
q_(Xi A)=q_Xi-2 A'/A.                                    (18)
```

For an off-real quartet, the boundary correction in `(18)` is rational and bounded. Equations
`(9)`--`(14)` show:

```text
same dense graph domain
  + bounded invertible gauge of the paired channels
  + one rank-one anti-causal coordinate per inserted right-half zero.        (19)
```

This is the exact pointed source--divisor incidence required by the rational-quartet countermodel.
The upper-half-plane poles cannot disappear into the causal channel because their coordinates are
the rank-one summands `(13)`.

## 6. Relation to inverse-horizontal charge

For `w=-gamma+i a` and the completed logarithmic residue `|c|=2m`, the residue vector in `(14)` has

```text
L2 energy=|c|^2/(2a)=2m^2/a.                             (20)
```

The full FE--Schwarz quartet has two such upper poles and energy at least `4m^2/a`. Hence the graph
gauge `U_r` is bounded for each fixed orbit but cannot have norm uniform as `a` decreases to zero.
This recovers the inverse-horizontal charge law inside the canonical graph rather than imposing it
as an external norm.

The source graph therefore has exactly the positive carrier forced by the previous obstructions:

```text
weighted all-prime source
  + archimedean completion
  + causal Hardy coordinate
  + orbit-sensitive anti-causal residue coordinate.     (21)
```

## 7. What remains open

The construction of an orbit-sensitive closed graph and closed anti-causal operator is complete.
It does not prove that the three boundary blocks of its shifted cut-downs are Hilbert--Schmidt or
that their positive relative-trace density is bounded by the incoming Euler-pole value `4`.

The exact remaining theorem is:

```text
for the distinguished Xi graph G_Xi,
construct the boundary relative trace Delta_Xi(u) and prove
limsup_(u->0+)Delta_Xi(u)/(4(1-e^(-u)))<=1.              (22)
```

By the Hankel boundary relative-trace criterion, `(22)` implies RH. The graph construction does not
assume `(22)` and remains valid for every Cartwright carrier with off-line zeros.

## 8. Scientific classification and Lean decision

The theorem is standard unbounded multiplication-operator and Hardy-space parent theory applied
to the completed logarithmic source. It is a route bridge, not new scientific knowledge. Its value
is that “construct the orbit-sensitive meromorphic graph” is no longer an undefined request: the
paired closed graph `(16)` is the canonical object, and `(22)` is the only RH-bearing analytic
estimate left on this interface.

The formal tree has no half-plane Hardy decomposition, outer majorant theorem, or closed unbounded
multiplication operators. A finite-dimensional graph shadow would not certify `(16)` or `(22)`, so
no Lean file is added.

**Superseded, 2026-08-15.**  A Lean module is added.  It does not claim `(16)` for the actual Xi
source or `(22)`; it proves the *structural* content that does not depend on the Hardy layer: the
paired-graph closedness argument in the abstract two-projection form, the exact rank-one residue
split, the inverse-horizontal energy, and the bilateral atom factorization.

## Lean status

Module `formal/GaloisForLFunctions/RHTower/CCMTwoChannelGraph.lean` (wired, axiom-clean, 5
declarations).

- **`pairedGraph_closed`** — section 1, statement 2, in the form the proof actually uses: for
  complementary bounded idempotents `P_+`, `P_-` on a normed space and a *closed* source map `T`,
  the paired map `f |-> (P_+(Tf), P_-(Tf))` is closed.  The two channels recombine to `Tf`, which
  is exactly the card's remark that closedness belongs to the full source constraint and not to
  either projected channel separately.
- **`cauchy_insertion_split`** — equation `(12)`: the exact split

  ```text
  c f(z)/(z - w) = c (f z - f w)/(z - w) + c f w /(z - w) ,
  ```

  whose second summand is the rank-one anti-causal residue coordinate `(13)`.
- **`residue_vector_energy`** — equation `(20)`: the reflected Paley--Wiener residue vector
  `c e^{-a t} e^{-i b t}` has `L^2` energy exactly `|c|^2/(2a)`.  This is the inverse-horizontal
  charge law recovered inside the graph rather than imposed.
- `integral_cexp_unit`, **`bilateral_atom_factorization`** — equation `(17a)`:

  ```text
  (e^{-i c t} - e^{-i z t})/(z - c) = i t int_0^1 e^{-i t (1-u) z} e^{-i t u c} du ,
  ```

  the atomic bilateral factorization through `L^2(0,1)` whose two feature maps have opposite causal
  orientation.

`#print axioms` on all five declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

Imported, not reproved: the half-plane Hardy decomposition and its projections, the outer-function
majorant `(5)`/`(8b)` giving the dense core and the dense adjoint core, closedness of multiplication
by a measurable a.e.-finite function on `L^2`, the Cartwright/bounded-type property of the centred
Xi source `(15)`, and the Euler-region expansion `(17)`.

## Gates

- [x] dense outer core
- [x] closed paired Hardy graph
- [x] dense adjoint core and closability of the anti-causal Hankel component
- [x] bounded invertible rational gauge covariance
- [x] bounded-perturbation covariance of the closed anti-causal operator
- [x] rank-one residue coordinate per upper-half-plane pole
- [x] specialization to the exact completed Xi source
- [x] inverse-horizontal graph charge recovered
- [ ] boundary-block Hilbert--Schmidt theorem for the Xi graph
- [ ] four-unit boundary relative-trace density bound
- [ ] RH
