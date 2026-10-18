# Asymmetric truncation of adjacent power-damped divisor means

- **ID:** BVI-ASYMMETRIC-ADJACENT-TRUNCATION-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM / dependency-closed paper proof and Lean audit
- **Parent:** `bvi-uniform-renormalized-interior-energy-remainder-2026-10-18.md`
- **Full objective:** Problem 4 strict interior contraction remains open.

## Exact statements

For positive e,h, put

    c_e(d) = mu(d)*d^(-e),
    F_e(n) = sum_{d|n} c_e(d),
    W_e(D) = sum_{1<=d<=D} |c_e(d)|,
    U_e(D) = sum_{d>D} |c_e(d)|/d,
    Q_N = (1/N)*sum_{n=1}^N F_e(n+1)*F_h(n).

Let Q_inf be the existing `pmAdjacentDivisorDensity e h`. For every
integer N>=1 and arbitrary nonnegative cutoffs A,D:

    |Q_N-Q_inf|
      <= 2*U_h(D) + 4*W_h(D)*U_e(A) + W_h(D)*W_e(A)/N
      <= 2*U_h(D) + 4*D*U_e(A) + A*D/N.

For A>=1:

    U_e(A) <= A^(-e/2)*K_e,
    K_e = sum_{d>=1} |c_(e/2)(d)|/d < infinity.

All summability and bounded-field inputs are existing theorems at positive
damping. No new analytic premise is imposed on the actual fields.

## Corpus inputs and scope of new work

- `pm_divisor_average_eq_tsum`: exact floor formula for divisor means.
- `pm_summable_real_mobius_reciprocal`: reciprocal summability.
- `pmPowerDampedDivisorCoeff_nonneg` and `_le_one`: full-field envelope.
- `tendsto_pm_adjacent_divisor_mean`: existing adjacent mean limit.
- `sievedDivisorSum`, `truncatedSieveWeight`, and the positive-index
  `sieveSeq` bridge: existing truncation representation.
- `abs_bezoutSawtoothDefect_le_one`: existing sharp CRT count discrepancy.
  The count estimate is reused, not claimed as new.
- `sum_Icc_one_split_head_and_shift`: exact shifted-prefix accounting.

The missing assembly is quantitative, with independent cutoffs. The
existing finite correlation expansion has one coefficient family and one
cutoff. The scratch extends it bilinearly and applies the existing unit
defect, then combines it with mean L1 tails.

## Dependency-closed paper proof

For nonnegative a with summable a(d)/d, the existing floor formula gives

    (1/N)*sum_{n<=N} sum_{d|n} a(d) <= sum_d a(d)/d.

Apply this to `a(d)=1_(d>D)*|c(d)|`. The triangle inequality within the
divisor sum bounds the mean absolute truncation error by the reciprocal
tail. For the shifted field at n+1, include the positive term at n=1 and
bound `(N+1)/N` by two. Thus the shifted mean absolute error is at most
twice that tail. The truncation at D has pointwise absolute value at most
the finite head mass W_h(D).

Write F_e,A and F_h,D for the truncated fields. The exact split

    F_e(n+1)*F_h(n)-F_e,A(n+1)*F_h,D(n)
      = F_e(n+1)*(F_h(n)-F_h,D(n))
        +(F_e(n+1)-F_e,A(n+1))*F_h,D(n)

and `|F_e|<=1` bound the mean error by
`B=U_h(D)+2*W_h(D)*U_e(A)`.

For fixed A,D, expand the truncated product over both divisor indices.
Each positive compatible pair has count discrepancy at most one; each
incompatible pair contributes zero. Therefore its normalized mean differs
from the finite coprime density L_(A,D) by at most `W_h(D)*W_e(A)/N`.
This also proves convergence of that truncated mean to L_(A,D).

Pass the uniform bound B through the existing actual adjacent mean limit.
It gives `|Q_inf-L_(A,D)|<=B`. The triangle inequality at the requested
horizon gives `|Q_N-Q_inf|<=2B+W_h(D)*W_e(A)/N`. Each positive-index
coefficient has absolute value at most one, so W_e(A)<=A and W_h(D)<=D.

Finally, for d>A>=1, factor the damping into two equal exponents:

    |c_e(d)|/d = d^(-e/2)*|c_(e/2)(d)|/d
               <= A^(-e/2)*|c_(e/2)(d)|/d.

The existing summability theorem at e/2 permits summing this inequality.
This proves all three displayed bounds.

## Relation to the remaining task

Choosing unequal power cutoffs gives a positive power rate for the
adjacent mean. That rate and its exact compensated-kernel consequence
are now formalized in `UniformAdjacentDivisorCompensatedRemainder.lean`,
with certificate on
`bvi-uniform-adjacent-compensated-remainder-2026-10-18.md`.
The predecessor-peak assembly and full O(1) interior-energy residual are
formalized in `UniformRenormalizedInteriorEnergyRemainder.lean`, with
certificate on
`bvi-uniform-renormalized-interior-energy-remainder-2026-10-18.md`.
No uniform actual energy bound or strict contraction is claimed.
Further research is paused at user request.

Newer corpus work also supplies collective ordered-gap bounds at finite
prefixes in `OrderedPronicGapCellsAndCollectivePrefixEnergy.lean`.
Its later signed tail remains outside that theorem. Reuse this stronger
frontier when returning to strict contraction; do not treat collective
finite-prefix control as wholly missing.

## Verification

- [x] Corpus candidates, source arguments, and exact input statements inspected.
- [x] Dependency-closed paper proof.
- [x] Lean original-source audit and artifact emission.
- [x] Public axiom closure and mathlib API probes.
- [x] Umbrella wiring, source index, formal lint, and owned-file whitespace check.
- [x] Archive and remove completed scratch files.

Scratch pass 3 (7389) exited 0 with no diagnostics. Original-source check
(68346) also exited 0 with no diagnostics and emitted fresh `.olean` and
`.ilean` artifacts for `AsymmetricAdjacentDivisorTruncation.lean`.
The leaf has 403 lines and SHA256
`b9871d714575b07e2ce005841c2428e9c73872559cb923f1df9f9fa21e680ab1`.
The final axiom/API audit (82766) exited 0: all three public theorems use
only `propext`, `Classical.choice`, and `Quot.sound`; twenty mathlib name
probes passed. The umbrella imports this leaf once; index refresh (96228)
passed and exact corpus retrieval returned all three public theorems.
Seventeen research outputs and fifteen proof/audit files were archived and
hash-verified. All thirty-two completed temporary files were removed and
verified absent. The later power-rate scratch is also complete and archived
under the uniform-adjacent certificate.
Full certificate: `logs/bvi-asymmetric-adjacent-truncation-2026-10-18-manifest.json`.

Formal lint (93967) exited 1 with 381 existing large-file warnings and
three unrelated errors: unreachable
`BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge`, unreachable
`BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge`, and package-root
placement of `TransHorizonIncidenceMechanics.lean`. None names this leaf.
This is not a global lint pass. Owned-file `git diff --check` passed.
