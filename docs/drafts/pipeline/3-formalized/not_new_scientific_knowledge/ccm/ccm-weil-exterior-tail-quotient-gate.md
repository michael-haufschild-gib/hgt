# The CCM Weil defect is an exterior-tail quotient

- **ID:** `ccm-weil-exterior-tail-quotient-gate`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** Connes--Consani, *Spectral triples and zeta-cycles*; the formalized
  `finite-prime-logarithmic-boundary-transfer` theorem
- **Statement:** Cutting a global summation-map radical vector to the CCM aperture represents its
  Weil class exactly by the negative exterior tail. The required transfer topology is therefore a
  zeta-weighted Mellin/Weil sampling topology specialized to the radial-prolate source.

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

## The required topology is the zeta-multiplier graph topology

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

Thus a successful argument through continuity of `E` controls `(8)`, or a stronger topology
which also controls the discrete Weil sampling functionals. The ordinary prolate concentration
numbers provide the additive `L2` component; source-specific oscillation supplies the additional
zeta-weighted cancellation required for the Weil defect in `(3)`.

The positive source-specific target is exact:

```text
exterior E-tail in a zeta-weighted Mellin/Weil topology,
relative to the exponentially small fixed-mode spectral gaps.      (9)
```

There is no remaining qualitative graph-domain objection from the sharp endpoint cutoff.
`ccm-bv-muntz-graph-domain-extension.md` proves that every compactly supported
bounded-variation zero-mean source, including the zero-extended CCM prolate contrast, produces a
global `L2(d*u)` summation vector and lies in the maximal zeta-multiplier graph domain. Its Mellin
transform vanishes at every nontrivial zeta zero. What remains open is quantitative: a cofinal
closed-Weil/sampling bound for that specific vector, strong enough relative to the minuscule
fixed-mode gaps.

Nor does the ambient coherent-growth example describe the leading tail of the special source.
`ccm-endpoint-oscillation-poisson-tail-bound.md` proves that its `1/y` Fourier endpoint term sums as
the uniformly bounded sawtooth series and reduces the lower-tail norm to explicit endpoint jets.
The zero-integral two-mode source also has central Poisson correction of exact deficit order. The
remaining positive target is to turn those endpoint-jet bounds into a **bilinear Rayleigh-excess**
estimate relative to the true even gap.

The preferred comparison is quadratic rather than a strong residual.
`ccm-rayleigh-excess-determinant-transfer.md` shows that it is enough to control the prolate seed's
Rayleigh excess by `O(lambda^(-1))` times the true even gap. This matches `(3)` exactly: both the
seed Rayleigh value and its comparison error can be expressed bilinearly through exterior tails.

## Cofinal RH boundary

Even a proof of `(9)` strong enough to identify the true finite-Weil low spectrum would remain a
local spectral theorem. The formalized logarithmic-boundary transfer isolates the additional
cofinal obligations. In the CCM determinant family, however, the two gates specialize
asymmetrically: whenever the finite even-simple hypothesis holds, every spectral-variable zero is
real, hence every corresponding zeta-variable zero has horizontal displacement zero. The
prime-clock energy gate is then identically satisfied. What remains is the analytic gate:

```text
source-defined holomorphic F_N
  -> every F_N-zero lies on Re(s)=1/2,
  -> F_N converges locally uniformly and nontrivially to Xi.       (10)
```

The exterior-tail estimate supports the last arrow when it controls the determinant or
characteristic function locally uniformly. Finite positivity, self-adjointness, a small Weil
eigenvalue, and finite eigenvector agreement are local inputs; `(10)` is their required cofinal
divisor certificate.

The live Connes route is therefore the following dependency chain:

```text
Fuchs/prolate leakage
  -> exterior E-tail control in the correct graph/sampling topology
  -> relative true-Weil spectral transfer
  -> finite even-simple determinant with real spectral zeros
  -> source-defined cofinal determinant carrying the Xi divisor.  (11)
```

The first line is now understood. The second line is the first analytic open core. The final line is
the cofinal open core; once it is proved, the preceding real-zero statement makes the metric gate
automatic.

## Attack record

Three candidate transfers were separated.

1. `[REQUIRED SOURCE RESTRICTION]` Control `E` on the radial-prolate sequence in its zeta-weighted
   graph/sampling topology; ambient additive `L2` supplies only one component.
2. `[AVAILABLE DOMAIN]` Qualitative maximal graph-domain membership of the zero-extended fixed prolate
   contrasts. This is `ccm-bv-muntz-graph-domain-extension.md`.
3. `[OPEN CORE]` A quantitative source-specific bilinear Weil-tail estimate for those contrasts.
4. `[PREFERRED OPEN CORE]` A Schur--Feshbach lower bound and true even-gap estimate making the seed
   Rayleigh excess `O(lambda^(-1))` relative to that gap. The Rayleigh transfer card then supplies
   the projective determinant rate in `(10)`.

## Novelty and significance verdict

The quotient identity is immediate linear algebra once the global radical theorem is known. The
unboundedness statement is an operator-theoretic consequence of the Mellin multiplier formula and
the classical unboundedness of zeta on the critical line. Both are useful route corrections but
fail the dual novelty/significance gate for new scientific knowledge. Their value is precision:
they replace an ambiguous ``prolate approximation error'' by one exact exterior tail and identify
the first topology in which that tail can possibly be controlled.

## Lean status

**Superseded, 2026-08-03.**  Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMWeilRadicalTailQuotient.lean`.

- `IsBiadditive`, `weilRadical`, `weilRadicalSubgroup` — the pairing and its two-sided radical.  Only
  **additivity in each argument** is assumed: no sesquilinearity, no scalars, no topology and no form
  domain, which is why the identity needs none of the analytic interface the previous decision waited
  for.
- **`radical_pair_left`**, **`radical_pair_right`** — equation `(2)`.
- **`radical_diag_eq`** — equation `(3)`: `QW(a,a) = QW(b,b)`, by expanding `a = h - b` and killing
  every term containing `h`.
- **`radical_quotient_eq_neg`** — equation `(4)`: in `D/Rad(QW)` the aperture class is exactly the
  negative of the exterior-tail class.
- **`integral_scaledBump`**, **`integral_sq_scaledBump`**, **`tendsto_integral_sq_scaledBump`** — the
  quantitative core of the density lemma: `β_R x = R⁻¹ β (x/R)` preserves the integral while its
  squared `L²` norm scales by `R⁻¹`, so the integral of an approximant can be corrected to zero at
  `L²` cost tending to zero.
- **`lt_setIntegral_normSq_of_exceeds`** — the unboundedness step `(6)`--`(7)` in the form that needs
  no closed-operator extension: if `‖m‖²` exceeds `C²` on a set of positive finite measure, the
  multiplier bound already fails at the indicator of that set.  The card routes `(6)` through
  closedness of the multiplication operator and its extension to all of `L²`; the Lean statement
  short-circuits that by exhibiting the failing test vector directly.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and genuinely external: Connes--Consani's radical membership `E(f) ∈ Rad(QW)` and the
Mellin multiplier formula `(5)`, which are imported source results; the Schwartz/Fourier side
conditions defining `S_0`; and unboundedness of `zeta` on the critical line, which supplies the set
`S` consumed by `lt_setIntegral_normSq_of_exceeds`.  The graph norm `(8)` is a definition, not a
theorem.

## Gates

- [x] exact Weil quotient/tail identity proved
- [x] density of the CCM source space in the source `L2` space proved
- [x] no bounded `L2` extension of the summation map proved
- [x] correct first graph topology isolated
- [x] zero-extended prolate source shown to belong qualitatively to that graph domain
- [x] cofinal logarithmic-boundary obligations integrated
- [x] Lean: radical quotient identity `(2)`--`(4)` unconditional, from additivity alone
- [x] Lean: zero-integral repair cost of the density lemma unconditional
- [x] Lean: multiplier unboundedness `(6)`--`(7)` unconditional, witnessed by one indicator
- [ ] source-specific fixed-prolate graph/sampling estimate
- [ ] relative true-Weil Schur--Feshbach transfer
- [ ] source-defined zero-preserving determinant converging to `Xi`
