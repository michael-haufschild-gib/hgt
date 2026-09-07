# EDQ joint fifth-word phase asymptotic

Stage: 3-formalized; dependency-closed paper proof and Lean verified.
RH status: no zero-location implication.

Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. This component determines the first surviving weighted chronological word and its complete complex convergence boundary. It does not supply the missing zero-specific relation.

The source is the actual moduli-two-and-three chronological exponential product in the fixed
six-coordinate nilpotent target `DeletionJointSharpness.A`. No zeta-zero or closure premise is
introduced. Write `P_N` for its first `6N` factors, `E=topWord`, and `w=5s`.

## Exact derivation

Put `f_w(n)=(n+1)^(-w)` and
`d_w(k)=f_w(6k)-(sum_(j<6) f_w(6k+j))/6`.
For `Re(w)>0`, successive variation of `f_w` is absolutely summable. Each of the six shifted
block differences is therefore absolutely summable, hence so is `d_w`. Complete-block
regrouping gives the exact finite identity

`sum_(k<N) f_w(6k) = (sum_(n<6N) f_w(n))/6 + sum_(k<N) d_w(k)`.

The existing power-sum theorem proves, for `w!=1`, that the first term minus
`(6N)^(1-w)/(6*(1-w))` tends to `zeta(w)/6`. Thus the left side minus that same power tends to
`zeta(w)/6 + sum_k d_w(k)`. The correction is retained, not set to zero.

The already proved exact matrix decomposition is
`P_N = C_N - (sum_(k<N) f_(5s)(6k))/60 * E`, where the corrected product `C_N` converges
for every `Re(s)>0`. Consequently

`P_N + (6N)^(1-5s)/(360*(1-5s))*E`

converges to the corrected-product limit minus
`(zeta(5s)/6 + sum_k d_(5s)(k))/60 * E`.
The exceptional real parameter `s=1/5` has the harmonic counterterm `log(6N)/360`.
For `0<Re(s)<1/5`, multiplying the full product by `(6N)^(5s-1)` yields the nonzero limit
`-E/(360*(1-5s))`. This identifies both growth and complex logarithmic phase, without a
numerical calculation.

## Scope and remaining gate

This theorem concerns the actual weighted word, including its summable chronological correction.
A positive unweighted polygon moment is not itself a signed comparison for this complex source.
The product already converges nonselectively for `Re(s)>1/5`; the zero-specific relation and
signed arithmetic separation needed for RH remain open. No route is retired here.

Corpus sources: `EulerDeletionJointProductSharpness`, `EulerDeletionJointNilpotentWitness`,
`EulerDeletionJointProductOneFifth`, `EulerDeletionQuasiShuffleZeroLanding`,
`EulerDeletionJointPolygonMoment`, and `ZetaPartialSumStrip`.

## Complex boundary closure

On `Re(s)=1/5` with `s!=1/5`, the power counterterm has constant nonzero norm and a
nonzero imaginary exponent. If the actual products converged, their proved asymptotic would
force `(6N)^(1-5s)` to converge. Its limit has norm one. Comparing subsequences `N`, `2N`,
and `3N` forces both `2^(1-5s)=1` and `3^(1-5s)=1`. The corpus's injective two-prime
logarithmic phase clock then forces `1-5s=0`, a contradiction. Together with the real
logarithmic boundary and the scaled limit below it, this gives the full positive-half-plane
classification: actual source products in this fixed target converge exactly for `Re(s)>1/5`.
This closes a phase distinction, not an RH separator.


## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionJointFifthPhase.lean` (311 lines;
12 public theorems, one public correction definition, one private linear readout).
Namespace: `RHTower.DeletionJointSharpness`.

- `strideCorrection_summable`, `stride_sum_decomposition`: full averaging correction and exact finite source regrouping.
- `fifthCoefficient_eq_weight`: actual fifth word at the dilated complex exponent.
- `tendsto_stride_sum_sub_power`, `sourceProduct_power_asymptotic`: exact complex finite part and actual chronological source transfer.
- `sourceProduct_scaled_limit`, `sourceProduct_not_convergent_of_re_lt`: nonzero scaled leading term and full complex divergence below the boundary.
- `tendsto_stride_sum_sub_log`, `sourceProduct_log_asymptotic`: actual harmonic boundary, with Euler's constant and complete correction retained.
- `six_nat_cpow_not_convergent`, `sourceProduct_not_convergent_on_complex_boundary`: logarithmic unit phase and all remaining boundary points.
- `positive_halfPlane_convergence_iff`: unconditional full classification for every positive-real-part parameter in the fixed source target.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_fifth.lean`, exit 0, no diagnostics.
Final leaf audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionJointFifthPhase`, exit 0. Only the new leaf rebuilt (3.9 seconds); dependencies were cached. The umbrella import is wired; no full or umbrella build ran.
New-only axiom audit: `lake env lean /tmp/edq_fifth_axioms.lean`, exit 0. All 13 new public declarations use only `propext`, `Classical.choice`, and `Quot.sound`; the private readout is covered by their dependency closure. No numerical premise, external computational certificate, admission, or added axiom is used.

Repository lint ran once and returned exit 1 solely for twelve concurrent modules unreachable
from their umbrellas: RHTower's `ThetaCuspSecondAtomAllMoments`,
`ThetaCuspTwoAtomExponentialAdmission`, `ThetaCuspTwoAtomOddProfiles`,
`ThetaCuspTwoAtomOddReserves`; HTGeometry's `LogarithmicLaplaceMiddleAbsoluteBounds`,
`MiddleHankelPerturbation`, `TwoAtomMiddleEntryBounds`, `TwoAtomMiddleHighEntries`,
`TwoAtomMiddleLowEntries`, `TwoAtomOddAlgebra`, `TwoAtomOddHighReserve`,
`TwoAtomOddLowerReserve`. Those modules were not modified by this task. Existing size warnings
also remain. The new leaf is wired; global lint is not claimed to pass.

The index was refreshed once. Scratch sources were removed after their successful checks;
all owned Lean, build, axiom, lint, and index sessions finished. Logs remain in
`/tmp/edq_fifth.api.log`, `.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, and `.index.log`.
RH remains unproved and unfalsified; no route is retired by this certificate.
