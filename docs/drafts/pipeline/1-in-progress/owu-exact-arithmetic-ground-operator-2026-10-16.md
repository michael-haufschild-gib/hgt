# OWU: exact arithmetic ground operator

Status: paper proof under audit; Lean not started.

Objective: remove the nonlinear quadratic-constraint qualification obstruction in the attained odd blind problem. Produce an actual finite arithmetic correction and an actual blind eigenstate at every positive aperture, with zero tolerance and no sign assumption.

## Corpus baseline

- `OddSectorBlindVariationalAttainment.exists_blind_minimizer`: an actual normalized blind odd minimizer exists at every positive aperture.
- `OddSectorInteriorTraceCoordinates.exists_interior_signed_coordinates`: both signs of every strictly active arithmetic coordinate occur inside the same open aperture.
- `OddSectorInteriorTraceRepair.exists_interior_purification_moments`: every positive finite odd mixture has one smooth odd source with exactly the same profile, traces, and energy.
- `OddSectorExactFibreRecovery.exists_exact_fibre_recovery`: every odd complete form source has smooth same-aperture recovery with exact arithmetic traces and convergent profile and energy.
- `HTGeometry.FinsuppOneSidedFeasibility.exists_of_nonneg_on_null_cone`: algebraic two-sided conic feasibility.
- `WeilPaperCovarianceDualAttainment` gives a different certificate on observed spectral completions with strictly positive measurement tolerance. It does not supply the proposed zero-tolerance odd source eigenstate.

Search: `research "odd blind multiplier dual attainment" --mode deep --budget-seconds 300 --json`. Partial source-index results; compiler applicability must be checked directly. A second search examines positive quadratic kernels and compact embeddings.

## Conjecture sequence

1. A positive-tolerance covariance certificate can be sent directly to zero tolerance. Rejected as a proof: its coefficient compactness divides by tolerance, so it gives no zero-tolerance limit.
2. Instead, the exact attained blind minimum admits finite arithmetic multipliers by positive-mixture purification and full signed coordinate reachability. Under paper audit.
3. Those same multipliers make every blind minimizer a true eigenvector of one arithmetic-corrected represented operator. Under paper audit; an odd-sector variational equation alone is insufficient for full operator-domain membership.

## Dependency-closed paper argument

Fix positive aperture a. Let u be an attained blind unit minimizer and m=Q(u). For a smooth odd source f write N(f)=P_f(0), T(f) for its finitely many strictly active traces, and D(f)=Q(f)-m N(f).

For any positive finite mixture c with T(c)=0, exact purification gives one smooth odd source f with its entire autocorrelation and Q preserved. If its mass is zero then its physical source is zero, hence Q=0. Otherwise normalization makes f a blind unit source, so D(c)=D(f)>=0. Both signs of each active coordinate are available inside the exact aperture. The corpus two-sided conic feasibility theorem therefore supplies finite real lambda with lambda.T(f)<=D(f) for every smooth odd f.

For an arbitrary odd complete form source v, exact-fibre recovery keeps T fixed and sends Q and P(0) to Q(v) and ||Jv||^2. Passing to the limit gives

    Q(v)-lambda.T(v) >= m ||Jv||^2.

Equality holds at u because T(u)=0 and ||Ju||=1. Define C_lambda as the finite self-adjoint sum of compressed symmetric logarithmic translations normalized by sqrt(n). Its diagonal is lambda.T. Define the corrected closed form by the original gamma/pole form with bounded remainder R-C_lambda. Its shifted form is nonnegative on the entire odd subspace, and vanishes at u. Polarization forces its pairing with every odd v to vanish. Reflection invariance makes the pairing with every even v zero as well. Therefore the equation holds against every complete form vector. The existing bounded-perturbation representation theorem puts Ju in the actual operator domain and gives H_lambda Ju=m Ju.

The same argument applies to every blind minimizer for this single lambda: no simplicity assumption, constraint-gradient independence, positive tolerance, or sign assumption occurs.

## Open frontier retained

No assertion that m>=0. No cofinal compatibility or global positive arithmetic source. The original pole term remains intact. This task is not an RH equivalence.

## Verification and cleanup

Pending: paper audit, direct Lean checks, axiom audit, umbrella imports, formal lint/index, owned scratch cleanup.
