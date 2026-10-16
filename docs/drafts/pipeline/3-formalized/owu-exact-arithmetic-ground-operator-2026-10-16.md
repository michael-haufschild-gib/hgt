# OWU: exact arithmetic ground operator

Status: formalized; all three modules and all 48 public declarations kernel-audited.

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
2. Instead, the exact attained blind minimum admits finite arithmetic multipliers by positive-mixture purification and full signed coordinate reachability. Paper proof closed; `OddSectorExactDualAttainment.lean` passed direct Lean audit.
3. Those same multipliers make every blind minimizer a true eigenvector of one arithmetic-corrected represented operator. Paper proof closed; `OddSectorArithmeticGroundOperator.lean` passed direct Lean audit without warnings. An odd-sector variational equation alone is insufficient for full operator-domain membership; reflection supplies the missing even variations.
4. The whole set of blind minimizers lies in one produced finite-dimensional linear eigenspace. Paper proof: K=J*(mI-R+C_lambda)J is compact, and the full ground equation says Ku=u. Its eigenvalue-one space is finite dimensional. Conversely a blind unit vector in this space has Q=m. This gives an exact finite-dimensional classification of the nonlinear optimizer set. `OddSectorFiniteGroundReduction.lean` passed direct Lean audit without warnings.
5. Immediate real-rootedness from this finite space was tested against `CCMParityFreeOddGroundData` and `ccmGeneralParityOddGround_compactFourier_zero_im_eq_zero`. That implication is not justified: those results require a simple kernel and positivity of the even block as well as the odd block, plus the displacement data. Finite dimension supplies neither simplicity nor the missing even-sector sign. No real-zero conclusion is claimed; the positive result retained is the exact finite eigenspace reduction.

## Dependency-closed paper argument

Fix positive aperture a. Let u be an attained blind unit minimizer and m=Q(u). For a smooth odd source f write N(f)=Re P_f(0), T(f) for its finitely many strictly active traces, and D(f)=Q(f)-m N(f).

For any positive finite mixture c with T(c)=0, exact purification gives one smooth odd source f with its entire autocorrelation and Q preserved. If its mass is zero then its physical source is zero, hence Q=0. Otherwise normalization makes f a blind unit source, so D(c)=D(f)>=0. Both signs of each active coordinate are available inside the exact aperture. The corpus two-sided conic feasibility theorem therefore supplies finite real lambda with lambda.T(f)<=D(f) for every smooth odd f.

For an arbitrary odd complete form source v, exact-fibre recovery keeps T fixed and sends Q and P(0) to Q(v) and ||Jv||^2. Passing to the limit gives

    Q(v)-lambda.T(v) >= m ||Jv||^2.

Equality holds at u because T(u)=0 and ||Ju||=1. Define C_lambda as the finite self-adjoint sum of compressed symmetric logarithmic translations normalized by sqrt(n). Its diagonal is lambda.T. Define the corrected closed form by the original gamma/pole form with bounded remainder R-C_lambda. Its shifted form is nonnegative on the entire odd subspace, and vanishes at u. Polarization forces its pairing with every odd v to vanish. Reflection invariance makes the pairing with every even v zero as well. Therefore the equation holds against every complete form vector. The existing bounded-perturbation representation theorem puts Ju in the actual operator domain and gives H_lambda Ju=m Ju.

The same argument applies to every blind minimizer for this single lambda: no simplicity assumption, constraint-gradient independence, positive tolerance, or sign assumption occurs.

The corpus supplies full reflection invariance of the Weil form (`ccmRestrictedWeilForm_reflection`), translation-reflection transport, the quadratic null-direction lemma, and represented operator-domain membership. These close the paper dependencies. Compactness of the physical form embedding closes the finite-dimensional eigenspace argument in conjecture 4.

## Open frontier retained

No assertion that m>=0. No cofinal compatibility or global positive arithmetic source. The original pole term remains intact. The floor is on the odd sector; no ordering against the corrected operator's even sector is claimed. The finite space may also contain even eigenvectors at the same eigenvalue. Its blind odd unit section is the exact optimizer set. This task is not an RH equivalence.

## Formal result

All names below lie in `RHTower.OddSector`.

- `exists_exact_form_multiplier`: produces finite multipliers at the attained blind minimum, valid on every complete odd form source, with no tolerance or extra premise.
- `exists_exact_arithmetic_ground_state`: produces a blind unit source satisfying the exact odd-sector floor, full complex weak equation, and actual represented operator-domain eigen-equation.
- `exists_finite_arithmetic_ground_reduction`: produces a nonzero finite-dimensional submodule S with an actual blind unit member. For every blind unit u, Q(u)=m iff u belongs to S. Every vector of S belongs to the actual corrected operator domain at eigenvalue m.

The removed obstruction is exact multiplier and operator realization for nonlinear quadratic arithmetic constraints. Local independence of constraint gradients is not assumed. The mechanism is positive-mixture purification, signed finite coordinate reachability, exact-fibre recovery, polarization, reflection, and compactness of the physical embedding.

## Verification and cleanup

Each module passed a foreground `lake --old env lean -j 1` audit, with its `.olean` emitted for downstream checks:

- `GaloisForLFunctions/RHTower/OddSectorExactDualAttainment.lean`
- `GaloisForLFunctions/RHTower/OddSectorArithmeticGroundOperator.lean`
- `GaloisForLFunctions/RHTower/OddSectorFiniteGroundReduction.lean`

No full build or umbrella build ran. Each module is imported exactly once by `formal/GaloisForLFunctions/RHTower.lean`. Compiled artifacts are newer than their sources. No new heartbeat/recursion overrides or computational experiments were used.

An external scratch file imported the final module and ran `#print axioms` for all 48 public declarations. Every declaration uses exactly the standard foundations `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or `sorryAx` occurs. Direct checks produced no warnings. `git diff --check` passed.

The repository-wide `scripts/formal_tools.py lint --check-generated` did not pass. Its final captured run reported nine unrelated unwired concurrent modules: `PaperThetaNativeMeyerCompleteness`, `PaperThetaNativeQuantileComparison`, `PaperThetaNativeRootTransport`, `SuzukiCausalDepthGammaCesaroSource`, `SuzukiCausalDepthGammaJointCore`, `SuzukiCausalDepthGammaMaximalSource`, `SuzukiCausalDepthGammaSourceRegularization`, `SuzukiGammaJacobiTailCore`, and `XiNewtonDiscSourceMargin`. Concurrent edits also made `LEAN_API.md` and `LEAN_OVERVIEW.md` stale during that run. None of its errors concerns these three OWU modules. Unchecked concurrent work was not wired or changed.

After the captured lint run, `scripts/formal_tools.py index` regenerated all three generated indexes and refreshed the research index. All owned scratch search files, API/audit files, and logs were removed. No owned Lean or search process remains running.
