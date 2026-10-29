# Bounded overlap of the complete Weil form and single-prime flips

- **ID:** bounded-overlap-complete-weil-and-prime-flips
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2910/breakthrough-question-2.md`; attached task.
- **Statement:** Prove unconditional complete Weil positivity at overlap ratio two, paying successor interactions at full weight, and determine fixed-ratio selectivity of single-prime flips.

## Required outcome

1. Explicit nonzero smooth profile; eventual positivity of the actual complete form at width
   `2 / N`, for every coefficient vector, with an explicit or explicitly bounded horizon.
   Explain the signed mechanism for the successor shells, including Gamma and both poles.
2. Decide the flip at eleven at `1 + 10⁻¹⁸` and at `2`; determine the finite/infinite threshold
   question for primes at least eleven and its dependence on the profile and prime.
3. Establish the zero-side content of ratio two, including the role of finite off-line support
   and actual zeta zero density.
4. Report the exact status and obstruction for arbitrary growing overlap schedules.
5. Complete paper proofs, unconditional Lean formalization, targeted final checks, transitive
   axiom audits, and umbrella imports. Do not replace these outcomes by a criterion or no-go.

## Placement and integrity

All new Lean code for this answer belongs in
`formal/GaloisForLFunctions/TransMetzlerWeilPositivity/BoundedOverlap/`.
Only import wiring may be added outside that subfolder. Existing unrelated edits are preserved.
Corpus searches and conjecturing only; no further web searches. No numerical experiments,
trusted-computation shortcuts, added mathematical assumptions,
placeholders, raised proof limits, or full builds. Do not use the hgtl7 skill.

## Gates

- [x] Task and briefing read; existing worktree changes recorded and preserved.
- [x] Initial corpus search run before consulting Mathlib.
- [ ] Exact finite-horizon definitions and briefing's shell statements checked in source.
- [ ] Complete paper proof of ratio-two positivity and flip conclusions.
- [ ] Lean checks and transitive axiom audit of exact claimed results.
- [ ] Requirement-by-requirement completion audit.

## Current evidence

Initial corpus searches locate `eventually_completeWeilMatrix_posDef_certified` and
`eventually_completeWeilMatrix_posDef_cZero`, but no macroscopic-overlap positivity result.
`primeFlip_exists_negative_complete_test` concerns unrestricted compact tests; it does not
settle a fixed overlap ratio. These are leads pending source and dependency checks.

## Conjecture loop

1. The literal bounded-overlap row estimate contains a downward `(n/N) log n` term.
   The successor operator is not uniformly bounded merely by the upward dyadic Chebyshev
   increment. Gamma's overlapping Gram term and the downward divisor logarithm must cancel
   before an operator estimate. The corpus's exact divisor-jet identity confirms this.
2. A concrete flip witness is available for proof: put
   `F_p(n)=1-2*1_(p|n)+2*1_(p²|n)` and `x_n=F_p(n)/sqrt(n)`.
   It has square one, mean `a_p=1-2/p+2/p²`, and lies in the Ramanujan span
   of conductors `1,p,p²`, with raw coefficients
   `a_p, -2(p-1)/p², 2/p²`.
   Its untwisted adjunction excitation is exactly `4 log(p)/p`.
   Multiplication by `p` gives `F_p(n)F_p(pn)=-1+2*1_(p²|n)`.
   The twisted-minus-untwisted prime correction at this first power cancels the
   `4 log(p)/p` excitation; the remaining odd powers start at `p³`.
   Bounding their correlations above by one gives remaining cost at most
   `4 log(p)*(2/p³+1/(p²(p-1)))`.
3. At `p=11`, proposed separated complete-form upper limit at ratio `r=99/100` is
   `β/M-log(2πr)+r*q*(101/121)² +4 log(11)*(2/11³+1/(11²*10))`.
   The existing plateau bounds give `β/M≤21/20` and `q≤1`.
   Elementary bounds `log(2π)>9/5`, `log(11)<5/2`,
   `(101/121)²<7/10`, `-log(r)≤1/99`, and tail cost `<1/40`
   make this strictly negative. This is an analytic argument, not a numerical experiment.
   The finite packet limit and the literal twisted-prime correction still need to be assembled
   and checked. Integer-multiple horizons give exact padding to both requested rational ratios;
   infinitely many negative witnesses already refute eventual nonnegativity.
   This construction does not prove zeta positivity at ratio two or classify all primes.
4. At ratio two the candidate completed mode energy subtracts
   `2 μ(m)/totient(m) * integral_(1/2)^1 (G(u)/M)/u du` from the separated energy.
   For the indicator limit, conductors one and two give respectively
   `4-3*log(2)-log(2*pi)` and `log(4/pi)`, both positive. The prime successor sum
   has twice the leading short-overlap Gamma contribution; cancelling both completely
   would miss this finite spectral correction. Actual norm quasimodes and spectral exhaustion
   remain unproved. A possible coercivity input is strict variance of the periodized plateau
   for local overlap in `[1,2]`; ordinary charge variance alone does not suffice.

## Proof and Lean status

`elevenTrialUpperMargin_neg` passed Lean with only `propext`, `Classical.choice`, and
`Quot.sound`. It certifies the scalar margin only. Draft arithmetic, packet, and complete-form
bridges remain under verification. All required mathematical conclusions remain open.
