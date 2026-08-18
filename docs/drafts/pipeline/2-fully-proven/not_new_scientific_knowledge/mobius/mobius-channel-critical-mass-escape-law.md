# The normalized Möbius channel is contractive but loses all finite coordinates at criticality

- **ID:** `mobius-channel-critical-mass-escape-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Source:** `shifted-euler-error-floor-mobius-tail-coupling.md`;
  `suzuki-tail-is-exact-summatory-error-transform.md`
- **Statement:** The Möbius half of Suzuki's shifted Euler source has a canonical direct-sum
  realization which is a strict Hilbert-space contraction for every positive shift.  At the
  critical limit every fixed divisor coordinate tends to zero while a nonzero amount of norm
  escapes through cofinally large divisors.  Consequently a faithful critical synthesis must be
  noncompact or must vary with the cutoff so as to track the escaping arithmetic tail.

## 1. Logarithmic shift realization

Let

```text
H=L2(R_(>=0),dt)
```

and let `V_a` denote the right shift

```text
(V_a f)(t)=1_(t>=a)f(t-a).                                (1)
```

Each `V_a` is an isometry.  For `omega>0`, put

```text
r_omega=1/zeta(1+2omega)>0.                               (2)
```

Define the normalized Möbius analysis channel

```text
C_omega:H -> direct_sum_(d>=1) H,

(C_omega f)_d
 =sqrt(r_omega) mu(d)d^(-1/2-omega)V_(log d)f.            (3)
```

The direct sum in `(3)` is the channel-resolved form of the denominator
`1/zeta(s+omega)`.  Unlike the coherent scalar shift sum, its divisor outputs are orthogonal by
construction.

## 2. Exact contraction norm

For every `f in H`,

```text
||C_omega f||^2
 =1/zeta(2+4omega) ||f||^2.                               (4)
```

In particular,

```text
||C_omega||=1/sqrt(zeta(2+4omega))<1.                     (5)
```

### Proof

Isometry of the shifts and orthogonality of the direct-sum coordinates give

```text
||C_omega f||^2
 =r_omega sum_(d>=1) mu(d)^2 d^(-1-2omega) ||f||^2.      (6)
```

For real `sigma>1`, the squarefree Dirichlet-series identity is

```text
sum_(d>=1)mu(d)^2d^(-sigma)=zeta(sigma)/zeta(2sigma).     (7)
```

Apply `(7)` with `sigma=1+2omega` and use `(2)`.  The factor
`zeta(1+2omega)` cancels, proving `(4)`.  Since `zeta(s)>1` for real `s>1`, `(5)` follows.

## 3. Critical mass escape

For every fixed finite set `F` of divisor channels,

```text
||1_F C_omega f|| ->0                                    (8)
```

as `omega` decreases to zero, but

```text
||C_omega f||^2 ->1/zeta(2)||f||^2.                      (9)
```

Therefore, if `f` is nonzero, the channel vectors `C_omega f` converge weakly to zero but do not
converge strongly.

### Proof

The pole of zeta at one gives

```text
r_omega=2omega+O(omega^2).                               (10)
```

Every fixed coefficient in `(3)` consequently tends to zero, proving `(8)`.  Equation `(9)` is
the limit of `(4)`.  To prove weak convergence, pair `C_omega f` with an arbitrary direct-sum
vector.  Its restriction to finitely many coordinates tends to zero by `(8)`, while the remaining
tail is uniformly controlled by `(5)` and can be made arbitrarily small.  This proves weak
convergence.  The positive limit `(9)` excludes strong convergence for nonzero `f`.

Equivalently, no fixed finite divisor window retains any of the limiting mass:

```text
lim_(omega downarrow 0)||1_F C_omega f||^2=0,

lim_(omega downarrow 0)||(1-1_F)C_omega f||^2
 =1/zeta(2)||f||^2.                                      (11)
```

## 4. Fixed compact synthesis cannot transport the critical tail

Let

```text
K:direct_sum_(d>=1)H -> H_0
```

be a fixed compact operator into any Hilbert space.  Then

```text
K C_omega f ->0 strongly                                 (12)
```

as `omega` decreases to zero.

Indeed, compact operators send weakly convergent sequences or nets with bounded norm to strongly
convergent images with the same limit.  Apply this to the weak convergence in Section 3.

Thus a nonvanishing critical source output cannot be recovered by a fixed finite-rank or compact
synthesis of the normalized Möbius channels.  A cutoff-dependent synthesis can follow the mass,
but only by moving through cofinally large divisor coordinates.  Such a family has explicitly
exposed the growing arithmetic state rather than compressed it into a fixed compact carrier.

## 5. Exact placement inside Suzuki's coupled source

Let

```text
(Uf)(t)=e^(t/2)f(e^t)
```

be the unitary logarithmic change from `L2((1,infinity),dx)` to `H`.  Put

```text
phi_omega(t)
 =1_(t>=0)e^(-t/2)g_omega^(1)(e^(-t)).                   (13)
```

Suzuki's causal primitive satisfies the locally finite identity

```text
U h_omega^(1)
 =sum_(n>=1)c_omega(n)n^(-1/2)V_(log n)phi_omega

 =sum_(d,m>=1)
    mu(d)d^(-1/2-omega)m^(-1/2+omega)
    V_(log d+log m)phi_omega.                             (14)
```

The first equality follows directly from

```text
h_omega^(1)(x)
 =x^(-1)sum_(n<=x)c_omega(n)g_omega^(1)(n/x).
```

The second uses

```text
c_omega(n)=sum_(dm=n)mu(d)d^(-omega)m^omega.             (15)
```

For each fixed `t`, only `dm<=e^t` contributes, so `(14)` is an exact pointwise locally finite
identity before any infinite-operator interchange.

Equation `(14)` identifies the two distinct analytic tasks.  The Möbius analysis has the exact
contractive normalization `(3)`--`(5)`.  The power-sum synthesis has coherent positive weights
`m^(-1/2+omega)` and is not an `l2` row in the RH-relevant range.  Suzuki's archimedean moment zero
and the compensating Möbius tail must therefore regularize that synthesis jointly.  Contractivity
of the channel analysis alone does not prove the boundary estimate.

## 6. Positive Hilbert--Pólya carrier law

The critical source does possess a canonical contraction, but its mass lives at infinity in the
divisor-channel index.  Hence every faithful pole-to-divisor transfer must preserve a cofinal
arithmetic incidence layer between analysis and synthesis.  It may do so through:

1. an infinite-dimensional divisor/prime channel space with a noncompact covariance;
2. a cutoff-dependent synthesis whose active coordinates grow cofinally;
3. a global completed constraint which identifies the moving tail before taking a strong limit.

A fixed compact synthesis, a fixed finite-dimensional state, or a bounded scalar autonomous ADE
cannot perform this transport.  The bounded-syntax prime-capacity law strengthens the last clause:
bounded scalar order and degree have a universal finite frequency capacity, so a cofinal scalar
realization must grow order or degree even before the boundary norm is considered.

For the direct Hilbert--Pólya attack, the remaining theorem is now more precise.  One must construct
a source-defined synthesis/covariance `A_omega` on the escaped channel mass such that the completed
floor-discrepancy plus Möbius-tail combination has a strong critical limit and

```text
||A_omega C_omega||<=1                                   (16)
```

on the pointed Euler-pole input.  Proving `(16)` from the exact archimedean moment cancellation,
without first assuming a zero-free half-plane, is the RH-bearing step.

## 7. Scope and classification

- `[PROVED]` The normalized Möbius analysis channel is a strict contraction with exact norm.
- `[PROVED]` Its critical mass escapes every finite divisor window.
- `[PROVED]` Every fixed compact synthesis kills that critical mass.
- `[PROVED]` The channel occurs exactly in Suzuki's shifted Euler source after the logarithmic
  `L2` change of variables.
- `[NOT PROVED]` No bounded synthesis/covariance for the coupled power-sum and archimedean factors
  is constructed.
- `[NOT PROVED]` The theorem does not prove the four-unit boundary norm or RH.

The analytic ingredients are the classical squarefree Dirichlet series, the pole of zeta at one,
and elementary Hilbert direct-sum theory.  Their combination is a useful source-transfer bridge,
not claimed as new scientific knowledge.

## 8. Lean status

`InfiniteMobiusShiftAnalysis.lean` now combines the formal squarefree normalization with the
actual logarithmic translation unitaries and constructs

```text
L2(R) -> ell2(N;L2(R))
```

as a complex-linear isometry for the unit-normalized Möbius amplitudes. This formalizes the
divisor-resolved infinite channel end to end. The paper normalization `(3)` differs by the scalar
`zeta(2+4omega)^(-1/2)`; its exact strict norm, the `omega->0` escape theorem, weak convergence, and
the compact-synthesis consequence are not yet formalized. Those remaining statements require a
packaged real zeta-pole limit and countable-channel weak-convergence argument, not merely another
finite-coordinate wrapper.

## Gates

- [x] exact normalized Möbius channel constructed
- [x] strict contraction norm proved
- [x] critical coordinate escape proved
- [x] compact-synthesis consequence proved
- [x] exact Suzuki source factorization proved
- [x] bounded-syntax carrier consequence attached
- [ ] source-defined archimedean synthesis/covariance contraction
- [ ] strong critical pole-to-divisor transfer
- [ ] four-unit boundary norm
- [ ] RH
