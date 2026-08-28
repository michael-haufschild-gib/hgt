# FZZ-P HC36: full Hermitian Riesz stability hypersurface (2026-08-28)

Frontier map remained read-only and untouched.

Module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityFullHermitianRieszStabilityHypersurface.lean`

Formal card:
`docs/drafts/pipeline/3-formalized/fzz-p-full-hermitian-riesz-stability-hypersurface.md`

## Result

For literal source metric `G=[[P,Q],[Q,R]]`, gap `E=Q^2-PR>0`, canonical Krein generator `A`,
and arbitrary Hermitian reporter `H=[[a,b+ic],[b-ic,d]]`, HC36 constructs exact
source-metric Riesz representative `B=G^-1 H` and classifies `M=A+B`.

Trace and determinant are

- `T=(-Ra+2Qb-Pd)/E`;
- `D=((b^2+c^2)-(a-PE/R)(d+E))/E`.

Actual spectral reality is equivalent to `Delta=T^2-4D >= 0`. If `Delta<0`, module constructs
positive-imaginary eigenvalue, nonzero eigenvector, exact eigenpair, and proves eigenvector neutral
for literal source Krein form.

Unique reporter with `M=0` is `(a,b,c,d)=(PE/R,0,0,-E)`, equivalently `H=-GA`. Its coefficients
lie strictly inside existing universal reflection-detector cone. Thus same reporter annihilates
local dynamics identically while its reflected Mellin reading agrees iff `rho.re=1/2`.

## Route consequence

HC35 covered only diagonal–chiral slice. HC36 closes complete four-real-dimensional local Hermitian
Riesz family: local stationarity, spectral reality, and kernel selection cannot force global
parity-Mellin matching. Surviving FZZ-P mechanism must be nonlinear, nonlocal/infinite, singular,
or contain genuine divisor-incidence data.

## Audit

- Mandatory corpus searches found no existing full four-coordinate theorem.
- Primary literature search found generic pseudo-Hermitian/Krein theory and FZZ interaction papers,
  but no literal-source hypersurface/detector-annihilator result; priority claim remains bounded.
- Direct Lean check passed.
- Targeted build passed: 9763 jobs.
- Axiom audit of 13 endpoints: only `propext`, `Classical.choice`, `Quot.sound`.
- Lint has no HC36 finding; unrelated unreachable-module errors remain.
- Umbrella import added; no umbrella/full build run.
