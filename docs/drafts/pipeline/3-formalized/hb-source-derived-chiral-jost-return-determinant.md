# HB source-derived chiral Jost return determinant

- **ID:** HC63
- **Stage:** 3-formalized
- **Type:** THEOREM / NONLINEAR JOST INCIDENCE / HARD FRONTIER / LEAN-PROVED
- **Routes:** HB, with HC58 clock images in FZZ-P, PW-B, and RBH
- **Source:** HC62 exact reduced `2s` Teukolsky source; branch-resolved hypergeometric Jost
  incidence; phase-cancellation and Cayley return laws
- **Statement:** Insert the source-derived reduced second-order chiral `2s` coefficient, rather
  than a free cross source, into the exact returned Jost channel. At every Xi descendant the
  resulting Evans determinant equals the HC62 source coefficient times the nonzero companion Jost
  factor. For nonzero seed it is nonzero exactly at tilted divisors, exactly when the doubled
  source weight is nonunitary. Its Cayley completion is nontrivial on precisely the same locus,
  independently of every multiplicative horizon phase. Universal determinant extinction is RH.

## Corpus-led conjecture

Define `J_ret` using `teukolskyReturnedJostWithHorizonPhase`, with arbitrary nonvanishing or
vanishing horizon phase and cross source equal to HC62's actual reduced `2s` coefficient. Prove:

1. at a plus-branch Xi QNM, `J_ret` is exactly the HC62 source coefficient;
2. the branch Evans determinant is exactly that coefficient times the nonzero minus-Jost factor;
3. for nonzero seed, determinant nonvanishing is equivalent to `Re(q) != 1/2` and to nonunitarity
   of the doubled source weight;
4. determinant vanishing for every Xi divisor is equivalent to RH;
5. the Cayley return is nontrivial exactly at tilted divisors and obeys the theta-shadow inverse
   law.

## Why this is frontier-level

Corpus separately contains an exact source-free/projective Jost determinant and HC62's exact
source-derived doubled-grade coefficient, but no theorem joins them. The topological-black-hole
Jost and Teukolsky-return modules explicitly leave a genuinely chiral nonlinear return determinant
whose nonlinear grade is tied to a doubled Eisenstein weight as open. HC63 attacks this missing
incidence without assuming a nonzero cross source, QNM completeness, optical positivity,
self-adjoint admission, or RH.

## Hostile checks

- Cross source must be HC62's composed Einstein--BM--helicity coefficient, not an arbitrary
  function or declared nonzero scalar.
- Horizon phase remains arbitrary and must cancel at the old Jost zero.
- Retain the unsquared complex determinant and its companion Jost factor.
- Do not identify this second-order returned channel with the still-uncomputed cubic `++-` AIME
  counterterm; perturbative grades remain distinct.
- Universal extinction theorem must be unconditional and closed in Lean.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Bounded primary-source audit found exact hypergeometric gravitational QNMs for massless
topological black holes (Birmingham--Mokhtari, 2006), an explicit reduced second-order Teukolsky
source (Spiers--Pound--Moxon, 2023), analytic source separation (Spiers, 2024), and numerical
quadratic Kerr-QNM excitation with angular overlap (Ma--Yang, 2024). No audited source states a
completed-zeta divisor-indexed, source-derived doubled-grade Teukolsky Evans determinant whose
zero locus is the critical line, or a universal-extinction equivalence with RH. This is a bounded,
not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC62 closed actual reduced-source incidence and corpus search showed
  the source-derived coefficient had never been installed into the branch-resolved Jost return.
- 2026-08-28 — Proved the returned Jost value and exact unsquared Evans factorization
  `transducer * clockDefect * companionJost`; arbitrary horizon phase cancels. For nonzero seed,
  Evans and Cayley excitation are equivalent to tilt and doubled-weight nonunitarity. Universal
  Evans extinction and universal Cayley triviality are each equivalent to RH; theta-shadow acts
  by Cayley inversion. Direct Lean check and target-only build passed (`12035/12035`); nine public
  theorem axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`; umbrella wired.
  Global lint reports only unrelated existing unreachable modules and no HC63 issue.
