# The critical Möbius boundary requires a full half-unit exponential-moment tower

- **ID:** `mobius-half-unit-exponential-moment-rh-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE HARDY-TRANSPORT LAW / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [SEARCH] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Hardy--Laplace translation, the classical Mertens-function criterion for RH,
  and `mobius-schur-centered-boundary-limit-law.md`
- **Statement:** The unweighted critical Möbius boundary vector belongs unconditionally to `L2`,
  but transporting it through every exponential weight below `exp(t/2)` is equivalent to RH. A
  weight `exp(alpha t)` gives exactly the zero-free half-plane `Re s>1-alpha`. Thus a successful CCM
  contour transfer must carry a cofinal half-unit tower of weighted domains; ordinary strong `L2`
  convergence or one fixed bounded translation cannot do so.

## 1. Critical Möbius vector

Put

```text
m_0(t)=sum_(n<=exp(t))mu(n)/n,       t>=0.                    (1)
```

The centered-boundary theorem proves

```text
m_0 in L2(0,infinity),                                       (2)

L m_0(z)=1/[z zeta(1+z)],       Re z>0,                      (3)
```

where the value at `z=0` is removable.

For `alpha>=0`, define the weighted domain condition

```text
M(alpha):  exp(alpha t)m_0(t) belongs to L2(0,infinity).      (4)
```

## 2. One weight gives one zero-free half-plane

If `M(alpha)` holds, then zeta has no zero in

```text
Re s>1-alpha.                                                (5)
```

### Proof

By the Laplace Paley--Wiener theorem, `(4)` gives an `H2(Re z>0)` transform which, on the initial
overlap `Re z>alpha`, equals

```text
z |->L[exp(alpha .)m_0](z)=1/[(z-alpha)zeta(1+z-alpha)]       (6)
```

The identity theorem continues this expression holomorphically through the whole right half-plane.
A zeta zero `rho` with
`Re rho>1-alpha` would produce a pole of `(6)` at

```text
z=rho-1+alpha,                                              (7)
```

which lies in `Re z>0`. The factor `z-alpha` cannot cancel a nontrivial zeta zero. Therefore no
such `rho` exists. `QED`

The removable point `z=alpha` corresponds to the pole of zeta at `s=1`, exactly as in `(3)`.

## 3. Exact RH equivalence

The following are equivalent:

```text
(i)  RH;
(ii) M(alpha) holds for every 0<=alpha<1/2;
(iii) for every epsilon>0,
      exp((1/2-epsilon)t)m_0(t) belongs to L2(0,infinity).     (8)
```

The equivalence `(ii)<->(iii)` is immediate. If `(ii)` holds, Section 2 excludes zeros from every
half-plane

```text
Re s>1-alpha,       alpha<1/2.                               (9)
```

Their union is `Re s>1/2`; the functional equation then gives RH.

Conversely, RH implies the classical Mertens bound

```text
M(x):=sum_(n<=x)mu(n)=O_epsilon(x^(1/2+epsilon))              (10)
```

for every `epsilon>0`. Since `sum mu(n)/n` tends to `1/zeta(1)=0`, partial summation from `x` to
infinity gives

```text
sum_(n<=x)mu(n)/n
 =M(x)/x-integral_x^infinity M(u)u^(-2)du
 =O_epsilon(x^(-1/2+epsilon)).                               (11)
```

With `x=exp(t)`, equation `(11)` becomes

```text
m_0(t)=O_epsilon(exp(-(1/2-epsilon)t)).                       (12)
```

Given `alpha<1/2`, choose `epsilon<(1/2-alpha)`. Then
`exp(alpha t)m_0(t)` decays exponentially and belongs to `L2`, proving `(ii)`.

Thus `(8)` is an exact RH criterion, not a proof that the weighted domains exist.

## 4. The half-unit seam

Multiplication by `exp(alpha t)` in time translates the Hardy function left by `alpha`:

```text
1/[z zeta(1+z)]
  ->1/[(z-alpha)zeta(1+z-alpha)].                             (13)
```

The unconditional theorem `(2)` supplies only the base `alpha=0`. Reaching the critical line
requires every `alpha<1/2`. At each step, crossed poles are precisely zeta zeros in the newly
entered strip. Therefore the half-unit transport is not bounded functional calculus on the base
`L2` space; it is the meromorphic continuation graph and residue seam already isolated in the CCM
corpus.

The exact positive resource is the nested weighted-domain tower

```text
D_alpha={f:exp(alpha t)f(t) in L2},       0<=alpha<1/2.       (14)
```

A successful source construction must place the pointed Möbius vector in every `D_alpha` while
retaining the residue charge created by any failed inclusion.

## 5. Prelimit safe weighted width

The prelimit makes the lost width explicit. With

```text
m_omega(t)
 =c_omega(
    sum_(n<=exp(t))mu(n)n^(-1-2omega)
    -1/zeta(1+2omega)),                                     (15)
```

the centered-boundary theorem gives

```text
L m_omega(z)
 =c_omega/z(
    1/zeta(1+2omega+z)-1/zeta(1+2omega)).                    (16)
```

For every `0<=alpha<2omega`, translating `(16)` by `-alpha` stays in the absolutely convergent
zero-free half-plane

```text
Re(1+2omega+z-alpha)>1.                                    (17)
```

The same local removable estimate and line-one reciprocal-zeta majorant used in the strong-limit
theorem show

```text
exp(alpha t)m_omega(t) in L2(0,infinity),
0<=alpha<2omega.                                           (18)
```

More generally, the argument of Section 2 gives

```text
exp(alpha t)m_omega(t) in L2
 -> zeta has no zero in Re s>1+2omega-alpha.                (19)
```

Starting from the Euler base `s=1+2omega`, reaching the critical line requires weights cofinal in

```text
0<=alpha<1/2+2omega.                                       (20)
```

Thus the source supplies a safe weighted width `2omega`, while the required width is
`1/2+2omega`. Their difference is exactly

```text
1/2                                                        (21)
```

at every positive shift. As `omega->0`, the safe width collapses to zero and the required width
approaches `1/2`, but the unresolved meromorphic continuation gap remains invariantly one half.

## 6. Relation to the critical channel boundary layer

The normalized Möbius divisor channel at shift `omega>0` has its norm at logarithmic aperture

```text
log d asymptotic to 1/(2omega).                               (22)
```

As `omega` decreases to zero, every finite coordinate disappears and the state escapes to
infinity. The moment tower `(14)` is the function-side version of the same recession: a fixed
compact synthesis controls only `alpha=0`, whereas critical transport requires weights cofinal in
`[0,1/2)` and divisor apertures cofinal at the scale `(22)`.

Consequently the causal Möbius Schur contraction cannot prove RH merely by taking its strong
unweighted limit. The positive remaining theorem is a cutoff-dependent, orbit-sensitive synthesis
that is bounded on every `D_alpha` with the correct residue graph as `alpha` approaches `1/2`.

## 7. Relation to the polar--prime defect

The following three conditions are equivalent RH carriers:

```text
exp(alpha t)m_0 in L2 for every alpha<1/2;
the polar--prime defect R has zero exponential type;
the exact even polar--Euler frame has lower bound mu_a.        (23)
```

The first is the reciprocal-zeta/causal coordinate, the second is the logarithmic-derivative
coordinate, and the third is the finite-aperture Weil coordinate. A CCM proof must construct the
map between these coordinates with its meromorphic residue seam; asserting any one of them as an
estimate simply assumes an RH-equivalent endpoint.

## Classification and Lean decision

The criterion `(8)` is the classical Mertens/RH criterion after partial summation, expressed in the
weighted-Mertens boundary coordinates of the CCM source. It is a bridge, not new scientific
knowledge.

The formal tree lacks the analytic reciprocal-zeta Laplace transform, the Mertens bound, and the
weighted Hardy spaces needed for `(6)`--`(12)`. Formalizing only multiplication by an exponential
would be wrapper work, so no Lean file is added.

## Gates

- [x] weighted Möbius domain tower defined
- [x] one exponential moment converted to a zero-free half-plane
- [x] full half-unit tower proved equivalent to RH
- [x] prelimit safe weighted width proved to be only `2omega`
- [x] invariant missing continuation width proved to be exactly `1/2`
- [x] collapse of the safe width at criticality isolated
- [x] exact failure of unweighted strong convergence as a proof mechanism identified
- [x] critical divisor-aperture recession attached
- [ ] construct the source-defined weighted synthesis on every `D_alpha`
- [ ] prove the cofinal residue-boundary estimate
- [ ] RH
