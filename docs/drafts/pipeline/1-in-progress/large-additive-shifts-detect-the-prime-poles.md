# Large additive shifts detect the prime poles

- **ID:** large-additive-prime-shifts
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2610/hard-obstacles-summary.md`, B3.29 and B3.28;
  `ArithmeticCorrespondencePositivity/TheSuccessorIsInvisibleAtZeros.lean`.
- **Statement:** The prime successor defect for a growing additive shift is
  asymptotic to a nonvanishing elementary function throughout the open strip.

## Exact target

For a positive integer h define

    D_h(s) = sum_(n>=1) Lambda(n) (n^(-s) - (n+h)^(-s)).

Prove, locally uniformly on 0 < Re(s) < 1,

    h^(s-1) D_h(s) -> 1/(1-s),  h -> infinity.

Consequently every compact subset K of this strip admits H such that every
integer h >= H has D_h(s) != 0 for every s in K. No zero-location, simplicity,
residue-summability, or hypothetical mean-square estimate may be assumed.

## Proposed arithmetic application

Let F=-zeta'/zeta and S_h=F-D_h be the analytically continued shifted prime
series. The mixed source F(F-S_h)=F D_h has, at any zero rho of multiplicity m,
residue -m D_h(rho). One sufficiently large h therefore retains every zero pole
in any prescribed compact part of the strip. The source is constructed from
actual additive shifts and Dirichlet convolution, before naming any zero.

This supplies a source nonvanishing input to nonlinear successor coupling.
It supplies no positivity of that coupling. An arithmetic carrier is not a
proof of RH. Contribution credit remains undecided until novelty and
significance audits; an elementary restatement of known PNT transport does not
qualify by itself.

## Proof strategy to verify

Write psi(x)=sum_(n<=x) Lambda(n), including psi(x)=0 below 1. Abel summation gives

    D_h(s) = s integral_0^infinity psi(x)
      (x^(-s-1) - (x+h)^(-s-1)) dx.

After x=h u, the normalized integral has psi(h u)/h in place of psi(x).
The prime number theorem gives psi(h u)/h -> u for every u>0. Chebyshev's
global bound psi(x)<=C x dominates this density. On compact strip subsets,
the remaining kernel is bounded by integrable powers u^(-b) near zero and
u^(-a-1) near infinity, where 0<a<=Re(s)<=b<1. Dominated convergence is then
uniform in s. Evaluate the limiting integral as 1/(1-s). Obtain nonvanishing
from a uniform positive lower bound for |1/(1-s)| on K.

## Gates

- [x] Initial corpus search and exact one-step source definitions inspected.
- [ ] Search for existing large-shift theorems and primary literature.
- [ ] Verify Abel representation, domination, uniformity, and integral value.
- [ ] Dependency-closed paper proof.
- [ ] Lean source checked individually with `lake --old env lean`.
- [ ] Transitive axiom audit and umbrella import.
- [ ] Novelty and significant-progress audit; count only if passed.

## Working state

No Lean file yet. This is a conjecture and proof strategy, not a claimed theorem.
The first significance audit does not accept this as one of the requested
contributions: replacing Lambda by any source with summatory function c*x+o(x)
gives the same proposed argument and limit c/(1-s). Compact-strip nonvanishing
therefore comes from a mean-value input and does not constrain the zero divisor.
The nonlinear residue construction alone still has no positivity law. Keep this
as an uncredited infrastructure lead, not as a solved hard obstacle or retired
research route. Do not promote it merely after proving the asymptotic.

Keep the research diary in `logs/rh-significant-contributions-2026-10-26.md`.
