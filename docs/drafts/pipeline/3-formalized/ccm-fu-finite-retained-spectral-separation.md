# CCM-FU: finite retained-source spectral separation

- **Stage:** 3-formalized
- **Type:** [BRIDGE] / derived theorem
- **Parent:** [finite source cone and coverage](../1-in-progress/ccm-fu-finite-source-cone-exhaustion.md)
- **Result:** Every nonzero functional on a finite retained prime field has a literal finite Möbius numerator that leaves simple critical poles beyond every height in the candidate source Mellin expression.

## Scope

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. The primary obligation remains complete compatible source coverage
under a uniform energy budget. This theorem supplies the spectral part of a
proof of finite clipping-stable directional control on arbitrary retained
fields, closed by the [source certificate](ccm-fu-finite-retained-directional-control.md).
The primary cofinal coverage obligation remains open.

## Exact statement

Let S be any finite set of primes and y a complex functional on its subsets,
nonzero on at least one subset. Define the finitely supported coefficients

`b_y(n) = mu(n)*y(primeFactors(n))` if `primeFactors(n) subset S`, and zero otherwise.

Non-squarefree indices vanish by their literal Möbius coefficient. Every
subset R is recovered at its squarefree product, so b_y is zero exactly when
all retained coordinates vanish. Its Dirichlet polynomial is exactly

`P_y(w) = sum_(R subset S) mu(product R)*y(R)*(product R)^(-w)`.

For every height T there is t>T with t>0, xi(1/2+it)=0, analytic multiplicity
one, and `P_y(1/2+it) != 0`. A fixed finite set of exceptional ordinates can
also be excluded. No RH premise enters.

Let E_Q(w) be the ordinary finite Euler denominator for any finite prime set
Q. Let Z(w) be zeta with its pole filled, so Z(1)=1. The candidate Mellin
expression, for any constant c, is

`M_y,Q,c(s) = P_y(s-1/2) * (-logDeriv Z(s-1/2) - dslope Z 1 (s-1/2) + c)`
`             / (E_Q(s-1/2) * 2*s*(s-1/2))`.

Its meromorphic order at s=1+it is exactly -1 at arbitrarily high simple
critical ordinates. This retains the finite Euler denominator and both
integration-clock factors. The actual proposed source uses Q=S and
c=2*gamma; the theorem allows every Q and c.

The same expression is analytic whenever Re(s)>1/2 and |Im(s)|<=4,
including the cancelled arithmetic pole at 3/2. Consequently
`z -> M_y,Q,c(4-z)` is differentiable on every closed ball centered at zero
with radius R<7/2. These are the closed balls required by the existing
positive-carrier Landau transfer theorem.

## Dependency-closed proof

A finite Dirichlet polynomial is entire and bounded by C*exp(A*|s|), with
finite A>=0 and C>=1. Its finite series converges at every argument; the
existing L-series injectivity theorem therefore recovers every coefficient.
The critical-line affine pullback preserves entirety, nonvanishing and
finite exponential type. If it vanished at all simple critical ordinates
outside a finite set E, the corpus Jensen bound would give
`N_simple(T)<=K*(1+T)+card(E)`. The unconditional corpus lower bound
`T*log(T)/(72*pi)<=N_simple(T)` eventually contradicts that estimate.
Taking E to contain the ordinates up to any chosen height gives the claim.

At a zero of Z, its logarithmic derivative has exact meromorphic order -1,
regardless of zero multiplicity. The divided difference of entire Z is
entire, so adding it and a constant cannot change this negative order.
Multiplication by a nonvanishing P_y preserves it. Finite Euler denominators
are entire and nonzero on Re(w)>0; the two clock factors are nonzero on
Re(s)>1/2. Neither division nor the affine shift changes the surviving order.

For the low-height statement, use the corpus unconditional nonvanishing of
Z at positive real part and imaginary part of absolute value at most four.
If |z|<=R<7/2, then Re(4-z)>1/2 and |Im(4-z)|<4. This supplies the asserted
closed-ball analyticity without a numerical zero census.

## Lean and validation

- `FiniteDirichletCriticalNonannihilation`: finite-polynomial injectivity,
  exponential type, cofinite and arbitrarily high critical nonannihilation.
- `FiniteDirichletDivisorPoleSurvival`: exact source and Mellin pole orders,
  finite Euler units, low-height regularity and Landau closed balls.
- `RetainedPrimeDirichletNumerator`: literal Möbius coefficient reconstruction,
  full subset-sum identity, zero classification and retained-source poles.

All three modules passed scratch and exact-file `lake env lean` checks.
Only their needed oleans were emitted; all three imports are wired into
RHTower. No umbrella or dependency build was run. All 28 new public
declarations were axiom-audited once: only `propext`, `Classical.choice`,
and `Quot.sound` occur. No computational premise or numerical experiment
was used. Global formal lint passed with existing large-file warnings;
the generated formal indexes and research search index were refreshed.

## Transport and cofinal scope

The [exact source transport](ccm-fu-retained-source-mellin-transport.md) closes
the infinite weighted Euler identity, actual source convolution, absolute
Mellin admission on Re(s)>2 and exact one-sided interpolation. The
[finite-field source certificate](ccm-fu-finite-retained-directional-control.md)
closes positive-carrier continuation and its pole contradiction, excluding
every nonzero one-sided functional. Finite actual cutoff witnesses, uniform
directional margins and common clipping tolerances are formal for each field.

No uniform bound on these witnesses or their preparation cost is proved as
the retained field changes. Complete compatible coverage, PE4/PE4G/PE4C,
SD1 and RH remain open.
