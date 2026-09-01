# Monotone Schrödinger potential does not force TCD D1

- **ID:** TCD-MS-D1-NOGO
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** `g(t)=exp(-t²-t⁴/6)` is positive, even, entire; `g''/g` is negative at zero and strictly increasing on `[0,∞)`, while its central signed reflected rank-three determinant is negative.

## Goal
Kill the generic Riccati/Sturm bridge from the proved theta facts `V(0)<0` and monotonicity of `V=g''/g` to rank-three D1. That bridge would otherwise close the finite TCD gate toward RH.

## Gates
- [x] 0 → 1: exact corpus-derived countermodel and proof plan
- [ ] 1 → 2: closed paper proof
- [ ] 2 → 3: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4: publication-ready

## Approach
Differentiate the quartic exponential exactly; prove the potential law and monotonicity algebraically; evaluate the central jets through the corpus exponential-jet transfer; apply the exact reflected rank-three log-jet identity.

## No-go closure
- **Exact killing theorem/mechanism:** increasing Schrödinger potential controls only a third-order Riccati margin; the quartic exponential has negative eighth-order reflected determinant.
- **Strongest positive survivor:** any TCD proof must use theta-specific quantitative modular/source geometry beyond potential monotonicity and its central sign.
- **New insight:** generic Sturm comparison cannot discharge the missing TCD D1 interval.
- **Status:** exact proof and Lean formalization in progress.
