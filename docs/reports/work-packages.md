# Work packages

## WP1 — Prime-side inequality (AIP with ACT)

Create significant and novel knowledge contributions in `ArithmeticIncidencePositivity` and
`ArithmeticCriticalityTheory` towards solving this problem: prove `J_M(u) + V_μ(u) ≥ 0` for all even
profiles `u` with support past `21/200`, in one odd gauge `M`, paying the prime atom `Λ(2)/√2` on the
first prime window without the pole-free margin.

The knowledge contribution is significant when it meets these criteria:

1. The support through which the inequality holds for all profiles increases.
2. Or a sign-changing supersolution with both moment conditions is constructed, or proved impossible
   together with the replacement hypothesis.
3. Or a Harnack inequality across the prime shifts is proved with an explicit constant.
4. Or the integrated atom-versus-pole law for the shifted ground state gives the exact set of paid `n`.
5. The statement fails for `ζ(s−a)ζ(s+a)` or for a Beurling system.

Not significant: pointwise or lattice classifications, collar constants, closed forms, the bump
bridge alone.

**Tools to use:**
1. Search: use the search tool for our lean corpus, not just rg or grep. make good use of the search tool to find existing work, building blocks, and new ideas. Try to apply existing lean research, try to identify problems and questions the field with your contribution could explain or solve.

2. Conjecture loop: use an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

the goal is met when you have made 100 such significant contributions.

## WP2 — Lag face (SRT)

Create significant and novel knowledge contributions in `SquareRootThreshold` towards solving this problem: prove
`P_v ≥ 0` for all lags `v ≥ V` with an explicit `V`, for one generic width, for `ζ` itself, when every
crystal and every finite off-line set has a first negative lag.

The knowledge contribution is significant when it meets these criteria:

1. An explicit unconditional `V`.
2. Or a visibility theorem at `ζ`-density for a non-attained top, with controlled lag.
3. Or a bound on off-diagonal prime pairs at bandwidth `λ > 1`, with its consequence for `P_v` stated.
4. Or the exact aperture, height and length tradeoff with the strongest unconditional estimate.
5. The proof says what replaces the attainment premise of grids.

Not significant: nonselective Weil-positivity apertures, invisibility theorems without a witness,
restatements of pair correlation.

**Tools to use:**
1. Search: use the search tool for our lean corpus, not just rg or grep. make good use of the search tool to find existing work, building blocks, and new ideas. Try to apply existing lean research, try to identify problems and questions the field with your contribution could explain or solve.

2. Conjecture loop: use an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

the goal is met when you have made 100 such significant contributions.

## WP3 — Aperture face (ACT, APT, OWU)

Create significant and novel knowledge contributions in `ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory`
and the OWU route towards solving this problem: prove `μ(A) ≥ 0` for all profiles at an aperture `A`
beyond the present one, and pass from the critical factorial family to the compact tests of the
receiver without the archimedean gain `log M`.

The knowledge contribution is significant when it meets these criteria:

1. The aperture through which `Ẑ ≥ 0` holds for all profiles increases.
2. Or compact approximants of critical sources inherit block positivity with a truncation-stable
   margin and no `log M` gain.
3. Or the odd sector is paid completely (reflected prime, cosh pole, negative `sinh` moment) at a
   stated aperture class for actual `Λ`.
4. Or a realization theorem names the Hilbert space and the Schatten class of the prime modification.
5. The statement fails for `ζ(s−a)ζ(s+a)`.

Not significant: new exact splits of the Weil form, auxiliary functionals, capacity-ratio
asymptotics, block thresholds, positivity on the critical family alone.

**Tools to use:**
1. Search: use the search tool for our lean corpus, not just rg or grep. make good use of the search tool to find existing work, building blocks, and new ideas. Try to apply existing lean research, try to identify problems and questions the field with your contribution could explain or solve.

2. Conjecture loop: use an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

the goal is met when you have made 100 such significant contributions.

## WP4 — Single-modulus dispersion (BVI)

Create significant and novel knowledge in `BezoutValuationIncidence` towards solving this problem:
bound `Σ_{p∼P} Σ_{q∼Q} a_p b_q 𝒢^{ec}(p,q)` on the pronic Gram at a single modulus, through the
reciprocity `{N/pq} ↔ p̄/q + q̄/p`, with exponent `θ > 1` and no character or modulus average;
equivalently bound the interior martingale `M^{int}_T` at one fixed `ε < 1/2`.

The knowledge is significant when it meets these criteria:

1. An exponent `θ > 1` for a stated coefficient class.
2. Or a cancellation rate per `log T` above `7/24` with means, endpoints and covariance retained.
3. Or a Type-II input at one modulus with its exact loss.
4. Or a proof that a named class of inputs cannot reach `θ > 1`, with the replacement hypothesis.

Not significant: the reciprocity error term, window constants, observability horizons, the
large-sieve factor two, anything at `ε ≥ 1/2`.

**Tools to use:**
1. Search: use the search tool for our lean corpus, not just rg or grep. make good use of the search tool to find existing work, building blocks, and new ideas. Try to apply existing lean research, try to identify problems and questions the field with your contribution could explain or solve.

2. Conjecture loop: use an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

the goal is met when you have made 100 such significant contributions.

## WP5 — Parity-breaking input (THIM with BVI)

Create significant and novel knowledge contributions in `TransHorizonIncidenceMechanics` towards solving this
problem: construct two weights with identical divisor-sum, Ramanujan and pronic Gram data but
opposite trans-horizon energy growth, or prove no such pair exists and name the additive observable
that separates them.

The knowledge contribution is significant when it meets these criteria:

1. The pair is constructed with both proofs.
2. Or its impossibility is proved with the separating observable and its exact loss.
3. Or the complete signed trans-horizon energy is bounded at one fixed `ε < 1/2` with all terms
   retained.
4. Or the odd-sector low-prime diagonal potential is bounded independently of the sign to be proved
   and moves the aperture unit in WP1 or WP3.
5. The proof names the step `k ↦ k+1`, `N ↦ N+1` or `k ↦ pk` where the arithmetic of `ℕ` enters.

Not significant: small-horizon thresholds, Buchstab band signs, second-order crossover terms,
schedule classifications.

**Tools to use:**
1. Search: use the search tool for our lean corpus, not just rg or grep. make good use of the search tool to find existing work, building blocks, and new ideas. Try to apply existing lean research, try to identify problems and questions the field with your contribution could explain or solve.

2. Conjecture loop: use an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

the goal is met when you have made 100 such significant contributions.

## WP6 — Node criticality and the band (BiScale)

Create significant and novel knowledge contributions in `BiScaleUncertainty` towards solving this problem: exhibit a
positivity argument that reads why `log 4` is indispensable and `log 6` redundant in the node set
`{log n}`, and deliver the blind-cone slack the sign-changing gauges need.

The knowledge contribution is significant when it meets these criteria:

1. A positivity statement that changes when `log 4` is deleted and not when `log 6` is, with the
   mechanism explicit.
2. Or the exact slack of the blind cone on two multiplicatively independent integers, or the infimum
   of `𝒥/h(0)` on the blind polar class, delivered as a constant and used in WP1 or WP3.
3. Or a band energy statement at square-root precision beyond polynomial length equal to the height.
4. Or an effective universal-probe criterion reading all multiplicities through finitely many primes.

Not significant: circle-moment closed forms on single towers, Müntz tail asymptotics, qualitative
packet persistence, growth dichotomies without a new unit.

**Tools to use:**
1. Search: use the search tool for our lean corpus, not just rg or grep. make good use of the search tool to find existing work, building blocks, and new ideas. Try to apply existing lean research, try to identify problems and questions the field with your contribution could explain or solve.

2. Conjecture loop: use an endless loop of conjecture -> succeed and move to next conjecture or fail and learn from it and move to next conjecture. never stop conjecturing no matter how often you fail.

do not conjecture or judge or assume or anything on your training data. your training data is outdated. use the search tool for our lean corpus to understand what the true frontier and true open questions are.

always look at the big picture, try to understand what all our research is trying to tell you about the nature of the field. do not blindly follow a route because it is in your training data. understand what our research is hinting at. your job is to create the missing mathematical knowledge through relentless conjecturing and learning from failures.

**Lean rules:**
1. Proofs must be unconditional, no hypotheses, no added axioms, no premises, ...
2. Always build in the foreground, one build process per agent at the time (other agents can also build in parallel to you).
3. No computations
4. Always use  lake env lean \<filmodule> for the final audit. Use --old flag to not unncessarily rebuild unchanged modules. Do not forget to wire new modules into the umbrellas.
5. do not run full builds. check ins that are needed, wirefinished modules into their umbrella but do not run full umbrella builds.
6. make sure you don't leave staleclean up after yourself.
7. Optimize lean code. No raising heartbeat hacks.
8. Add helpful, crisp, not verbose comments to lean code to make clear what the code is about.

Keep a knowledge ledger in logs/ for your own work (there are multiple agents active) - not a working log or history or diary, but a collection of crisp facts and failures to learn from in future research sessions.

the goal is met when you have made 100 such significant contributions.