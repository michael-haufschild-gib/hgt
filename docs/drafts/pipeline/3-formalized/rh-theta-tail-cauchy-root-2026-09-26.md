# Literal theta tail: Cauchy limit and its constant correction

- **ID:** RH-THETA-TAIL-CAUCHY-ROOT-20260926
- **Stage:** 3-formalized
- **Type:** [BRIDGE]; RH remains open
- **Owner:** root
- **Parent:** `../1-in-progress/rh-nonlocal-tail-root-2026-09-26.md`

## Exact target

Let Phi be the literal complete theta source and

`K(x,y)=integral_(s>0) (x+y+2s) Phi(x+s) Phi(y+s) ds`.

For fixed real x,y set `A=pi*(exp(2x)+exp(2y))`,
`D(r)=exp(-2r)*Phi(x+r)*Phi(y+r)`. Then

1. `K(x+r,y+r)/(r*D(r)) -> 1/A`.
2. `K(x+r,y+r)/D(r) - (2r+x+y)/(2A) -> 0`.
3. For every fixed finite injective node set `x:Fin n -> Real`,
   `Matrix(i,j -> K(x_i+r,x_j+r))` is eventually positive definite.

All limits are as r tends to positive infinity. Node count and spacing are fixed
before taking the limit. The positivity threshold may depend on the entire set.

## Dependency-closed paper proof

The exact complete first-log-jet decomposition gives, for z>0,

`Phi'(z)/Phi(z) = -2s+9/2+3/q+ell(z)`,
`s=pi*exp(2z)`, `q=s-3/2`, `q>=3/2`, `|ell(z)|<=1/10`.

Thus `|Phi'/Phi+2s|<=7`. The correction ell is the derivative of the
logarithm of the complete higher-to-first likelihood factor. No theta atoms
are omitted. Consequently every fixed polynomial multiple of

`exp(-2r)*Phi'(x+r)/Phi(x+r)+2*pi*exp(2x)`

tends to zero, using `r^k exp(-2r)->0`.

Write `P(r)=Phi(x+r)Phi(y+r)` and
`T(r)=exp(-2r)*(P'(r)/P(r)-2)`. Then
`D'=P*T`, `T->-2A`, and `r^k*(T+2A)->0` for each fixed k.
The exact kernel shift derivative is `K'=-(2r+x+y)*P`.
Kernel and normalizers tend to zero by integrable-tail decay and the literal
source envelope. Applying L'Hopital to K/(rD) proves (1).

For (2), set `L(r)=(2r+x+y)/(2A)` and `N=K-D*L`. Both N and D tend to zero,
and direct differentiation gives

`N'/D'=-[(2r+x+y)*(T+2A)+2*exp(-2r)]/(2A*T) -> 0`.

The denominator is eventually nonzero since A>0. L'Hopital now proves
`N/D->0`, exactly statement (2).

For (3), multiply the normalization in (1) by pi. Its entrywise limit is
`C_ij=1/(u_i+u_j)`, `u_i=exp(2x_i)>0`. The integral Gram identity proves C
positive semidefinite. The Cauchy determinant formula proves its determinant
nonzero for distinct u_i, hence C is positive definite. Openness of positive
definiteness gives positivity of the normalized finite matrix. Positive diagonal
congruence by `diag(Phi(x_i+r))`, followed by the positive scalar
`r*exp(-2r)/pi`, recovers the literal matrix.

## Prior-art and route audit

Corpus already proves the exact common-translation derivative, separated-packet
positivity, Cauchy positive semidefiniteness, its determinant, and openness of
finite-dimensional positive definiteness. These are reused. This bridge also
allows arbitrarily close fixed distinct nodes; it does not assert global novelty.
Deep searches were partial or source-only at compiler level; applicability was
checked against source and in the scratch proof.

The constant term is the logarithmic-Cauchy model, up to a positive scalar and
positive diagonal congruence. `LogarithmicCauchyRankBoundary` shows its coefficient
model needs a correction unbounded in coefficient energy when rank increases.
Small pointwise error can still have that behavior. Neither theorem transfers
model negativity to the literal source. The open obligation is a joint estimate
in rank and translation; existing common-translation Loewner propagation is
already disproved and cannot transport tail positivity back to the seam.

## Lean scope and verification

Leaf: `formal/GaloisForLFunctions/RHTower/ThetaTailCauchyAsymptotic.lean`.
Namespace `RHTower.ThetaTailCauchy`. Main theorems:
`kernel_normalized_limit`, `kernel_two_term_limit`,
`sourceMatrix_eventually_posDef`.

Scratch check passes, including all three statements and polynomial score-error
decay. Named leaf build passes (11010 jobs, cached dependency reuse). All 16 public
theorem axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.
The combined audit with the 36 model theorems has 52 reports, none missing.
Index refreshed; `scripts/formal_tools.py lint --check-generated` passes with
existing large-file warnings. All owned proof/search/index/lint jobs exited. No numerical experiment or git command was used.
