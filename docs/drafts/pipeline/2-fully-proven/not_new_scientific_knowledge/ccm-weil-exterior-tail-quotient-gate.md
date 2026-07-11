# The CCM Weil defect is an exterior-tail quotient

- **ID:** `ccm-weil-exterior-tail-quotient-gate`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** Connes--Consani, *Spectral triples and zeta-cycles*; the formalized
  `finite-prime-logarithmic-boundary-transfer` theorem
- **Statement:** Cutting a global summation-map radical vector to the CCM aperture transfers its
  entire Weil defect to the discarded exterior tail. The summation map is unbounded in the source
  `L2` topology, so ordinary prolate leakage cannot furnish a uniform Weil-transfer estimate.

## Setup

Let `QW` be the global Weil sesquilinear form on a common domain `D`, and let `Rad(QW)` denote its
two-sided radical. Connes--Consani prove that

```text
E(f)(u)=u^(1/2) sum_(n>=1) f(nu)
```

belongs to `Rad(QW)` for every even Schwartz function in

```text
S_0={f : f(0)=Fourier(f)(0)=0}.
```

Let `P_lambda` be multiplication by the aperture indicator of
`[lambda^(-1),lambda]`. Whenever the two pieces below belong to the common form domain, put

```text
h=E(f),
a=P_lambda h,
b=(1-P_lambda)h.                                       (1)
```

## Exact exterior-tail identity

`[PROVED HERE; BRIDGE]` For every `g` in the common form domain,

```text
QW(a,g)=-QW(b,g),
QW(g,a)=-QW(g,b),                                      (2)
QW(a,a)=QW(b,b).                                       (3)
```

### Proof

Equation `(1)` gives `a+b=h`. Since `h` lies in the two-sided radical,

```text
0=QW(h,g)=QW(a,g)+QW(b,g),
0=QW(g,h)=QW(g,a)+QW(g,b),
```

which proves `(2)`. Expanding `QW(h-b,h-b)` and again killing every term containing `h` gives

```text
QW(a,a)=QW(h-b,h-b)=QW(b,b).
```

This proves `(3)`.

Equivalently, in the quotient `D/Rad(QW)`, the aperture vector and the negative exterior tail are
the same class:

```text
[P_lambda E(f)]=-[1_(0,lambda^(-1)) union (lambda,infinity) E(f)].   (4)
```

The near-radical eigenvalue is therefore not an unexplained error produced by cutting. It is the
Weil size of one precise arithmetic tail.

## The source `L2` topology cannot control the tail uniformly

Let

```text
w(f)(u)=u^(1/2)f(u)
```

and let `U_s=Fourier_mu o w` be the unitary source identification. Let `U_m=Fourier_mu` on the
multiplicative output space. Both are unitary up to the fixed normalization of the transform.
Connes--Consani prove on `S_0` that

```text
U_m(E(f))(t)=zeta(1/2-it) U_s(f)(t).                   (5)
```

`[PROVED HERE; BRIDGE]` There is no constant `C` such that

```text
||E(f)||_(L2(d*u)) <= C ||f||_(L2(du))                 (6)
```

for every `f in S_0`.

### Density lemma

The subspace `S_0` is dense in the even part of `L2(R)`. First approximate by even smooth compactly
supported functions vanishing near zero. If such an approximant has integral `I`, choose a fixed
even bump `beta` supported in `[-2,-1] union [1,2]` with integral one and set

```text
beta_R(x)=R^(-1) beta(x/R).
```

Then `integral beta_R=1`, `beta_R(0)=0`, and

```text
||beta_R||_2=R^(-1/2)||beta||_2 -> 0.
```

Subtracting `I beta_R` imposes zero integral at arbitrarily small `L2` cost while retaining zero
value at the origin. Hence `S_0` is dense.

### Unboundedness proof

Assume `(6)`. After applying the two unitary transforms and `(5)`, multiplication by
`zeta(1/2-it)` would be bounded on the dense subspace `U_s(S_0)`. The multiplication operator is
closed. The bound would therefore extend it to a bounded operator on all of `L2(R)`, forcing

```text
zeta(1/2-it) in L-infinity(R).                          (7)
```

But the zeta function is unbounded on the critical line; in fact unconditional results give
arbitrarily large critical-line values. This contradicts `(7)` and proves the theorem.

## The correct first topology

The maximal closed multiplier associated with `(5)` has graph norm

```text
||f||_(E,max)^2
  =||f||_2^2
   + integral_R |zeta(1/2-it)|^2 |U_s(f)(t)|^2 dt.      (8)
```

Thus an argument which passes through continuity of `E` must control `(8)`, or a stronger topology
which also controls the discrete Weil sampling functionals. The ordinary prolate concentration
numbers control additive `L2` leakage of a source and its Fourier transform. By the theorem above,
that information alone cannot imply a uniform estimate for the Weil defect in `(3)`.

This is a universal-estimate no-go, not a no-go for the specific prolate sequence. A source-specific
estimate may exploit its Hermite/prolate structure. What it must estimate is now exact:

```text
exterior E-tail in a zeta-weighted Mellin/Weil topology,
relative to the exponentially small fixed-mode spectral gaps.      (9)
```

## Cofinal RH boundary

Even a proof of `(9)` strong enough to identify the true finite-Weil low spectrum would remain a
local spectral theorem. The formalized logarithmic-boundary transfer isolates the additional
cofinal obligations:

```text
source-defined holomorphic F_N
  -> F_N converges locally uniformly and zero-preservingly to Xi,
  -> every F_N-zero has reflected energy o((log N)^2).  (10)
```

The exterior-tail estimate can support the first arrow only if it controls the determinant or
characteristic function locally uniformly. Finite positivity, self-adjointness, a small Weil
eigenvalue, or agreement of finitely many eigenvectors cannot replace `(10)`.

The live Connes route is therefore the following dependency chain:

```text
Fuchs/prolate leakage
  -> exterior E-tail control in the correct graph/sampling topology
  -> relative true-Weil spectral transfer
  -> source-defined cofinal determinant carrying the Xi divisor
  -> sub-log-square energy on its zero fibers.          (11)
```

The first line is now understood. The second line is the first analytic open core. The last two
lines are the independent cofinal open core.

## Attack record

Three candidate transfers were separated.

1. `[DEAD]` A uniform estimate from additive source `L2` leakage to `||E(f)||_2`. The multiplier
   theorem above rules it out.
2. `[OPEN CORE]` A source-specific graph-norm or Weil-sampling estimate for the fixed prolate
   contrasts. Unboundedness of `E` does not rule this out because the sequence is highly rigid.
3. `[OPEN CORE]` A Schur--Feshbach comparison of the true Weil form with the constrained prolate
   ladder, with off-diagonal coupling little-o of each minuscule ladder gap. This still needs the
   determinant/divisor transfer in `(10)`.

## Novelty and significance verdict

The quotient identity is immediate linear algebra once the global radical theorem is known. The
unboundedness statement is an operator-theoretic consequence of the Mellin multiplier formula and
the classical unboundedness of zeta on the critical line. Both are useful route corrections but
fail the dual novelty/significance gate for new scientific knowledge. Their value is precision:
they replace an ambiguous ``prolate approximation error'' by one exact exterior tail and identify
the first topology in which that tail can possibly be controlled.

## Lean decision

The abstract radical-quotient identity and closed-multiplier argument are standard shadows. The
formal tree has no analytic interface for the global summation map, its Mellin multiplier, the Weil
form domain, or critical-line zeta unboundedness. Formalizing only the abstract algebra would add a
wrapper without certifying the source-specific statement. No Lean file is added.

## Gates

- [x] exact Weil quotient/tail identity proved
- [x] density of the CCM source space in the source `L2` space proved
- [x] no bounded `L2` extension of the summation map proved
- [x] correct first graph topology isolated
- [x] cofinal logarithmic-boundary obligations integrated
- [ ] source-specific fixed-prolate graph/sampling estimate
- [ ] relative true-Weil Schur--Feshbach transfer
- [ ] source-defined zero-preserving determinant converging to `Xi`
