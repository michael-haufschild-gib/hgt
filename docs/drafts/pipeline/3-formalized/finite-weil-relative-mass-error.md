# Quantitative relative error of logarithmic moment mass

Status: formalized; native leaf build and complete axiom/API audit passed.
Date: 2026-10-10. Only local Lean corpus and installed dependencies.

Predecessor: `finite-weil-quadratic-sqrt-cost.md` proves the square-root reference bound and factor-two comparison at quadratic starts. This follow-up retains the error term discarded by the Bernoulli step.

Notation: n=r+1, A=k+2, U=A+n, delta=n², G=finiteWeilArithmeticMass r, S=finiteWeilAbsMass(finiteWeilCanonicalCluster r k), q=(A/U)^n. All are nonnegative and A,U,G,q are positive.

Paper argument:
1. Bernoulli gives q >= 1-delta/U. Existing log-grid mass comparisons give qG<=S and qS<=G.
2. Multiply the Bernoulli lower bound by G and by S, using nonnegativity, then combine with the two mass comparisons. After clearing U, obtain (U-delta)G<=US and (U-delta)S<=UG.
3. Equivalently, U(G-S)<=delta G and (U-delta)(S-G)<=delta G. These two asymmetric error estimates hold for every r,k, without a width premise.
4. Under A>=2delta, U-delta>=A/2. If S>=G, the second estimate gives A(S-G)<=2delta G. If S<=G, the first estimate and A<=U give A(G-S)<=delta G<=2delta G. Therefore A*abs(S-G)<=2delta G.

Exact Lean results in `WeilLogShiftRelativeMass.lean`: `finiteWeil_power_bernoulli_error` (line9), unconditional `finiteWeilCanonicalCluster_mass_error_bounds` (line27), `finiteWeilCanonicalCluster_relative_mass_error` (line71), and the normalized `finiteWeilCanonicalCluster_relative_mass_ratio` (line101). No additional analytic premise. These are finite inequalities, not numerical approximations.

The next bridge is also complete: `finite-weil-cubic-mass-limit.md` combines the explicit relative error with the corpus's Wallis limit to identify normalized mass along an explicit cubic cluster-start sequence.

Prior local search `mass asymptotic`, module WeilLogShift, found only `exists_deficit_logBlock_bound_of_logShiftAsymptoticPositive` in WeilLogShiftDeficitTranslation (line88). Its statement concerns deficit mass under separate positivity/summability premises, not canonical nodal mass; it does not supply this result. Existing binomial, Wallis, and nodal-comparison producers are the direct inputs.

Verification shared with the cubic-limit companion: both native leaf builds exited0 with empty final logs; `/tmp/hgt-relative-final-audit.lean` exited0 with all 10 public declarations and 22 explicit API terms checked. Axioms are contained in `propext`, `Classical.choice`, `Quot.sound`. Metadata audit reports no source/direct-dependency freshness, axiom coverage, or exact umbrella-count issues. Incoming imports are the umbrella and internal companion chain. No full/umbrella build, heartbeat increase, web/paper lookup, or numerical experiment.

Final formal lint `/tmp/hgt-relative-final-lint.log` exits1 on three unrelated missing imports: `RHTower.JointAncestryLogWeightBernoulli`, `RHTower.JointAncestryLogWeightPrimeSum`, `HTGeometry.QKrawtchoukCompanionTriangular`. No errors in the authored leaves; foreign work untouched.

Local index refresh and the companion's exact final-root lookup passed. All owned native processes are terminal.
