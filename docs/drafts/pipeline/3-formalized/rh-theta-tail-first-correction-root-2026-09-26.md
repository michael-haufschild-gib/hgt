# Literal theta tail: positive squared-Cauchy correction

- **ID:** RH-THETA-TAIL-FIRST-CORRECTION-ROOT-20260926
- **Stage:** 3-formalized
- **Type:** [BRIDGE]; RH remains open
- **Owner:** root
- **Parent:** `../1-in-progress/rh-nonlocal-tail-root-2026-09-26.md`

## Exact results

For the complete theta source Phi, first-moment tail kernel K, fixed real x,y,
A=pi*(exp(2x)+exp(2y)), and D=exp(-2r)*Phi(x+r)*Phi(y+r),

`[K(x+r,y+r)/D-(2r+x+y)/(2A)]/[r*exp(-2r)] -> 7/(2A^2)`.

The positive squared-Cauchy correction, after Cayley congruence, has formal
series `(1-z)(1-w)/(1-z*w)^2`. Its coefficient matrix has diagonal 2i+1,
adjacent entries -max(i,j), and zero elsewhere. For finite support its form is
exactly `sum_i (i+1)*(a_i-a_(i+1))^2`. On the alternating cutoff of length n
this is `2n^2-n`, while ordinary coefficient energy is n. Thus this positive
repair is outside every uniform ordinary-energy bound.

## Dependency-closed paper proof

The exact first-atom logarithmic score, with q=pi*exp(2x), is
`f'/f+2q=9/2+3/(q-3/2)`. Existing complete-source relative derivative errors
e0=(Phi-f)/f, e1=(Phi'-f')/f satisfy e0,e1,q*e0 ->0. Hence
`Phi'/Phi+2q=[e1+(f'/f+2q)+2q*e0]/(1+e0) ->9/2`.

Put E=exp(-2r), P=Phi(x+r)*Phi(y+r), T=E*(P'/P-2), and A as above.
Then D=E*P, D'=P*T, `(T+2A)/E ->7`, and K'=-(2r+x+y)*P.
For N=K-D*(2r+x+y)/(2A) and G=r*E*D, direct differentiation yields

`N'/G'=-[(2+(x+y)/r)*(T+2A)/E+2/r]/[2A*(normalizedSlope-2E)]`.

The denominator factor tends to -2A; the quotient tends to 7/(2A^2).
Both N and G tend to zero by the established complete-source envelope and
kernel-tail decay. L'Hopital proves the asserted limit.

The formal series identity follows twice from the geometric recurrence.
Expanding its three bands gives the weighted difference energy, with boundary
term n*a_n^2 for a cutoff at n. Nonnegativity and the alternating energy formula
follow by finite algebra. The real Cayley identity independently checks the
normalization factor 1/(2u0).

## Whole-route consequence and exact limits

The logarithmic model excludes bounded repairs; the literal source's first
omitted term is positive and has precisely unbounded coefficient energy.
Consequently pointwise small remainder does not justify transporting model
negativity. The next open obligation is an all-rank bound for the complete
remainder. Fixed-node asymptotics do not permit exchanging translation with
rank or coefficient extraction. No source PSD or RH result is claimed.

Corpus search retrieved the complete-source approximation and existing Cauchy
and formal-series ingredients. The new bridge and exact weighted correction
were checked against their source statements; no global novelty claim.

## Lean verification

Leaf: `formal/GaloisForLFunctions/RHTower/ThetaTailCauchyFirstCorrection.lean`.
Namespace `RHTower.ThetaTailFirstCorrection`; nested `CauchySquare`.
Scratch check and named leaf build pass. All 16 public theorem axiom reports
contain only `propext`, `Classical.choice`, `Quot.sound`. Leaf wired into
`RHTower.lean`. Index refreshed; final `scripts/formal_tools.py lint --check-generated` passes
with existing large-file warnings. All owned proof/search/index/lint jobs exited.
