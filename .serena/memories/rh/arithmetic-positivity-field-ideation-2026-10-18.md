# Arithmetic positivity field ideation — 2026-10-18

User asked whether the globally open WL/RW blockers imply a new mathematical field is needed, and what such a field would study, construct, and prove. This is ideation, not authorization to resume the cleared persistent RH goal or start new Lean proofs. No Lean/source files changed; no new theorem or originality claim.

## Position
No known solution does not establish that existing mathematics is insufficient. A new estimate, structural theorem, synthesis, or broader theory could suffice. A proposed programme is arithmetic positivity: derive global sign/cancellation from the exact arithmetic source, preserving prime/Gamma/polar terms and cross-scale couplings. The programme must earn substance through unconditional theorems, not axioms equivalent to RH.

## Two mechanisms
1. Analytic: exact multiscale signed-form reduction, arithmetic estimates on mixed blocks, and controlled passage in the actual form topology. For a Hermitian block form [A B; B* C] with C positive definite, sign reduces to A-B C^{-1} B*. Schur algebra is classical and already present in the corpus. Open contribution is a quantitative source-derived bound on this residual at all required scales. Positivity of both diagonal blocks alone is insufficient. A fixed positive global gap is not required; margins may shrink. Small L2 tails do not imply small Weil energy.
2. Geometric: construct from arithmetic a positive pairing and generator Theta with exact zero/trace correspondence and the weight-one relation <Theta v,w>+<v,Theta w>=<v,w> on the correct domain. A zero eigenmode then has Re rho=1/2. This is an established Deninger/Hilbert–Polya blueprint, not a new discovery. Constructing the faithful positive pairing and proving the relation remain the deep step.

Potential missing arithmetic input: quantitative compatibility of actual prime-power/divisibility data with additive order and the completed explicit formula. This is a candidate direction, NOT an established sufficient condition or identified new law. Generic positive weights and functional-equation symmetry do not suffice.

## Criteria
- Definitions and premises obtainable independently from exact arithmetic, with no hidden universal Weil positivity/critical bound.
- Faithful prime coefficients, Gamma, poles, multiplicities, all mixed terms and correct domains.
- All tests/apertures/heights; no fixed positive exponent loss for WL, no ignored finite exceptional modes.
- Controlled form-topology closure; no assumed uniform spectral gap.
- Reject applicable off-critical countermodels and recover known finite-field cases.
- Produce intermediate estimates/classifications/deformation laws useful before RH, with explicit hypotheses for any extension to other L-functions.
- First local test could be the actual ramp diagonal Schur margin A_n-M_n²/(4D_n), retaining mixed-tail and polar terms at log N/N. This remains locally unresolved; proving it would not prove RH without an all-test extension.

## Corpus evidence
Read source:
- formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilExactFiniteSchur.lean:184–264. exists_ccmRestrictedWeil_exactFiniteSchurComplement at217 constructs an exact finite Schur certificate at every aperture. Do not sell this reduction as missing/new.
- formal/GaloisForLFunctions/RHTower/ArithmeticSchurRenormalizationLaw.lean:1–145. Exact geometric/Szego kernel exhaustion and valuation translation; module explicitly disclaims the open source-to-Xi nonexpansive transport.
Read docs:
- docs/drafts/pipeline/1-in-progress/arithmetic-schur-renormalization-law.md (all295 lines): positive source laws, open transport at213–245.
- deninger-closed-generator-hodge-weil-purity-universality-law.md: equivalences, no unconditional purity.
- finite-filter-schur-saturation-2026-10-17.md: strict finite residual is not a uniform global gain.
- relational-law-renormalization-field-programme.md:1–170: an existing field programme with set-level quotient/relational results; not a source of missing Weil sign.
Prior exact blocker assessment: `mem:rh/wl-rw-blocker-classification-2026-10-18`.

Two documented hybrid searches completed partial=false/errors=[]; 20 candidate lemmas and20 source arguments inspected each. /tmp/rh-field-coercivity-search.json and /tmp/rh-field-source-transport-search.json. Compiler snapshot mixed, not a fresh proof audit. No exhaustive absence conclusion. No Lean jobs started.

## Primary literature checked
- Clay https://www.claymath.org/millennium/riemann-hypothesis/ still Unsolved.
- Deligne, La conjecture de Weil I, https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf, theorem1.6: finite-field cohomological Frobenius weights.
- Deninger, The Hilbert-Polya strategy and height pairings, https://arxiv.org/pdf/1001.1621, pp4–5: conjectural positive Hodge pairing and theta-nu/2 skew-symmetry. Illustrates existing ambitious framework, not a proved construction for zeta.
- Connes–Consani, Weil positivity and Trace formula, the archimedean place, https://arxiv.org/abs/2006.13771: established operator/trace programme.
- Connes–Consani, The Riemann-Roch strategy, Complex lift of the Scaling Site, https://arxiv.org/abs/1805.10501: existing geometric adaptation programme.

No priority/novelty claim. Search results claiming RH proofs were not treated as accepted solutions or used as evidence.
