# Cyclotomic positivity and the complete affine overlap operator

Status: closing the existing formalization batch at the user's request. The complete-Weil comparison remains open. No new research branches.

## Objective and boundary

Transport cyclotomic positivity to the actual signed complete overlap form. The source decomposition subtracts `nonRatioForm`: an auxiliary prime-Gram lower bound cannot by itself prove complete-Weil positivity. The missing result must bound the adverse actual prime contribution above, or absorb it jointly with the retained Gamma and both polar terms.

No stronger complete-Weil positivity range, RH proof, improved zero strip, or improved critical-line proportion has been obtained in this batch.

## Existing proof inventory

All CACT paths below are in `formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/`.

| Existing paper result | Lean module | Status |
|---|---|---|
| Exact prefix-distance and centered Gram identities | `TheArithmeticCurvatureHasAnExactGramCompletion` | Certified; final direct audit queued |
| Radical exactly classified by cyclotomic divisibility | `CyclotomicDivisibilityClassifiesTheOverlapGramRadical` | Direct audit passed |
| Divisor completion gives `Q*min(i,j)-i*j` | `AllDivisorConductorsRecoverTheDiscreteBridge` | Certified; final direct audit queued |
| Uniform signed source comparison and unit-Gram lower bound | `PrimeResidueWindowsControlEveryGramPacket` | Certified; final direct audit queued |
| Positive conductor lift under rational refinement | `RationalRefinementCompletesTheCyclotomicGram` | Certified; final direct audit queued after removing an unused tactic |
| Real Gram positivity, conditional negativity, exact unit-cell kernel | `TheRealOverlapCurvatureIsConditionallyNegative` | Final direct audit passed; wired |
| Both affine parameters may move with height | `ActualAffinePrimeWindowsAreUniformInTheirParameters` | Draft awaiting audit |
| Exact identity with existing prime-block jump energy | `CyclotomicCompletionIsThePrimeBlockJumpEnergy` | Draft awaiting audit |
| Literal prime-prefix form dominates its full primitive Gram | `ActualPrimePrefixesDominateTheirCyclotomicGram` | Direct audit active |
| Smaller schedule for the already constructed Steklov profile | `TransMetzlerWeilPositivity/TheFixedProfileReachesAnIteratedLogEndpoint` | Existing draft awaiting audit; no further receiver research |

## Exact mathematical content

Write `E_m(k)` for the primitive-root prefix energy. Then

`K_m(i,j) = (E_m(i)+E_m(j)-E_m(dist(i,j)))/2`

is an actual real Gram kernel. Its full quadratic form is the sum of squared weighted primitive prefixes. For zero-total-mass coefficients, the raw distance form is minus twice that energy. If `P` is the packet prefix polynomial, energy vanishes exactly when `Phi_m` divides `P` over the reals. Multiple conductors intersect these divisibility conditions.

Summing nontrivial divisor conductors of `Q` gives the exact mixed kernel `Q*min(i,j)-i*j` on `[0,Q]`. On prime-supported packets this equals `Q` times the pronic energy of the cumulative prime jumps.

For `m>1`, `L>0`, rational refinement gives

`L^2*A_m(k/L) = sum_{e | mL, e/gcd(e,L)=m} E_e(k)`.

The same positive conductor decomposition holds entrywise for centered Grams. Continuity and common-grid approximation give real positivity. On `[0,1]`, the real centered kernel is exactly `phi(m)*min(x,y)`.

The actual residue masses supply one error tending to zero at fixed conductor and multiplicative window. This controls every signed pattern and every finite real or complex Gram packet, with coefficients and features allowed to depend on height. For lower bounds, non-unit prime powers are nonnegative: one horizon dominates `(log B-log A-epsilon)` times the unit Gram without an extra non-unit penalty. Prefix-phase specialization identifies that unit Gram exactly with the complete primitive Gram divided by `phi(q)`.

The already-written synthesis calculation uses the same Steklov profile at `c_N=L*(log L)^2*log(log L)`, `L=log(log N)`. It is smaller than every previously displayed `L*(log L)^beta`, `beta>2`. This is receiver work, not arithmetic positivity; it is being closed only to finish the existing paper proof.

## Failed conjectures and positive survivors

1. Raw scalar curvature need not be a positive translation kernel. Its diagonal is zero while its first off-diagonal is positive. Survivor: exact centering and conditional negativity, with all mixed terms retained.
2. A single primitive conductor cannot coerce arbitrary packets: cyclotomic divisibility gives its radical. Survivor: exact divisor-conductor completion and the discrete bridge.
3. A full-residue penalty is needed in the stated absolute comparison, but not in a lower bound. Survivor: positivity of non-unit prime powers yields unit-Gram domination.

These survivors are the existing formalization targets above. None establishes the missing complete-form comparison.

## Conjectures that are not paper proofs

Moving-endpoint/BV source transport, a coprime-frequency Fourier realization, a common-rounding radical classification, and the new-profile iterated-log Denjoy–Carleman construction remain conjectural extensions. No theorem or completed paper proof is claimed for them. They are outside this closing batch.

## Validation and persistence

Direct audits use `lake --old env lean <module>.lean`, one owned process at a time. Compiled dependency files are generated only for missing dependencies or new modules imported by another new module. No full or umbrella build, numerical experiment, added analytic premise, or limit increase. Finished modules are wired into their programme umbrellas. Capstone dependency checks must contain only `propext`, `Classical.choice`, and `Quot.sound`.

Research history: `logs/astra-rh-research.log`. Final audit queue: `logs/astra-final-audit-status.txt`. Formalized results: `../3-formalized/astra-curvature-gram-completion-and-radical.md`. Consolidated interpretation: `docs/reports/review-2910/astra.md`.
