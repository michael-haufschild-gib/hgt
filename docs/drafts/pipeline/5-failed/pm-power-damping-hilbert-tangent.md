# Power damping has an L¹ tangent but no canonical Hilbert tangent

- **ID:** pm-power-damping-hilbert-tangent
- **Stage:** 5-failed
- **Type:** FALSIFIED (positive survivor fully formalized)
- **Source:** Route PM, PM-31; `pm-power-damped-mobius-haar.md`.
- **Statement tested:** The canonical positive-damping difference quotients have a finite uniform L² budget near zero.
- **Status:** Closed: exact L² obstruction and positive L¹ survivor fully formalized and audited.

## Dependency-closed paper proof

Write `A_ε` for the literal power-damped Möbius Fermi source, `H` for Haar
on `(0,1]`, and `D(t)=ψ(1/t)−2ψ(1/(2t))`. Pointwise differentiation gives
`(A_ε−H)/ε → D` as ε decreases to zero.

Let `h₀` be Haar supported on `(0,1]`. On the positive ray,

`D(t)=Σ_n Λ(n) h₀(nt)`.

This is an exact finite identity at each point, with both cutoff endpoints
retained. Absolute Mellin interchange on `Re s>1`, the Haar transform and
the von Mangoldt Dirichlet series give

`F(s)=Mellin(D)(s)=−(1−2^(1−s))*logDeriv(ζ)(s)/s`.

If D were canonical L², F would be analytic on `Re s>1/2`. With the entire
residue unit `U(s)=(s−1)ζ(s)`, normalized by `U(1)=1`, the identity theorem
extends the cleared formula

`s(s−1)U(s)F(s)=−(1−2^(1−s))*((s−1)U′(s)−U(s))`

throughout that half-plane, including one. At a critical zeta zero ρ,
the nontrivial entire U has finite positive zero order m. Its local analytic
factorization yields `(s−ρ)logDeriv(U)(s)→m`. Along `s=ρ+x`, x>0,

`x F(ρ+x) → −m*(1−2^(1−ρ))/ρ ≠ 0`.

The dyadic factor is nonzero because `Re ρ=1/2<1`. Meanwhile the canonical
L² Mellin–Laplace chart and Cauchy–Schwarz give `|F(ρ+x)|≤C/sqrt(2x)`,
forcing `xF(ρ+x)→0`. The existing unconditional critical-zero theorem supplies
ρ, so the assumption is impossible. Fatou then excludes every eventual
finite L² budget for the actual difference quotients.

## Strongest positive survivor

For `e_n=||R_n−H||₁`, shrinking support and the unconditional logarithmic
prefix-energy saving imply `C=Σ_n e_n/n<∞`. Finite Abel summation gives

`||A_ε−H||₁≤Cε` for every ε>0.

Its divided gaps converge to `log(n+1)−log n`, with the summable scalar error
majorant `2e_n/n`. Dominated convergence of that scalar series, finite-sum
Minkowski and Fatou prove

`||(A_ε−H)/ε−D||₁ → 0`.

Thus D is canonical L¹, has norm at most C, and its signed integral is
exactly `log 2`, by the independently certified mean formula
`∫A_ε=log 2/ζ(1+ε)`. The earlier weighted Chebyshev energy theorem also
admits D in `L²(t dt)`. These positive statements retain the literal source
and measure; they are not merely restatements of nonadmission.

## No-go closure

- **Killing mechanism:** A critical zero forces a simple logarithmic-derivative
  pole, incompatible with the canonical Hilbert boundary estimate.
- **New insight:** First-order damping control is available in L¹, with an
  exact nonzero mean, but cannot be upgraded to a bounded canonical Hilbert
  tangent. Zeroth-order canonical admission at positive damping remains a
  separate question.
- **Paper dependencies:** Exact finite cutoffs; absolute arithmetic Mellin
  interchange; Haar transform; entire residue unit; identity theorem; isolated
  zeros; Hardy critical-zero existence; canonical L² Cauchy–Schwarz; Fatou.
- **Positive Lean status:** `PMPowerDampedMobiusL1Convergence` and
  `PMPowerDampedMobiusDerivative`, fully audited. Exact survivor endpoints:
  `tendsto_pmPowerDampedDifferenceQuotient_L1`,
  `pmDyadicChebyshevSource_L1_norm_le`,
  `pmDyadicChebyshevSource_integral`. Weighted energy:
  `ChebyshevDyadicWeightedEnergy`.
- **Obstruction Lean status:** `PMPowerDampedMobiusDerivativeMellin` (153 lines /
  10 declarations) and `PMPowerDampedMobiusDerivativeBoundary` (226 lines /
  6 declarations), wired and fully audited. Exact endpoints:
  `not_memLp_pmDyadicChebyshevSource_carrier`,
  `pmPowerDampedDifferenceQuotient_L2_norm_exceeds`.

## Boundary

This does not refute canonical L² admission for every positive damping,
canonical convergence at a slower rate, or RH. No numerical experiment,
new axiom, or unproved RH premise enters the obstruction or survivor.

## Log

- 2026-10-01 — Paper proof recorded after corpus/interface audit. Full derivative
  survivor already certified. Exact Mellin identity, cleared continuation,
  generic boundary estimate, critical-residue contradiction and actual quotient
  consequence are being checked together in scratch 1034.

- Final gates closed: targeted old leaf builds passed (5.7s and 4.4s); both
  final actual `lake env lean` checks passed empty. All sixteen axiom reports
  use only `propext`, `Classical.choice`, `Quot.sound`. Exact promoted bodies,
  exhaustive unique names, all public API entries and unique umbrella imports
  passed. Global lint separately reports thirteen unrelated unwired modules
  and concurrent LEAN_API staleness; no owned or proof-debt finding.
- The strong L¹ tangent remains the nontrivial positive survivor: canonical
  convergence of the actual difference quotients, finite explicit source norm
  budget, and exact signed derivative mean log 2. The no-go is now closed.
