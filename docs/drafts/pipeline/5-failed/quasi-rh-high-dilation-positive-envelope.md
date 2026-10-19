# Sharp positive-envelope cost on the exact power meshes

- **ID:** quasi-rh-high-dilation-positive-envelope
- **Stage:** 5-failed — direct positive normalization retired; sharp survivor formalized
- **Type:** THEOREM (Lean)
- **Source:** [quasi-rh.md §8.4](../../../report/quasi-rh.md)
- **Statement:** For every m≥1, the squared absolute-mass envelope of the actual high-dilation tail at M=j^m, D=j^(m−1), accumulated through j≤J, has sharp order J^(m+1).

## Arithmetic object and purpose

Let a(M,d) be the literal Möbius-divisor dilation channel, I(M,D)={d:D<d<M},
Q_tail(M,D)=Σ_I a(M,d)², and U_tail(M,D)=Σ_I |a(M,d)|. The coefficients remain the actual Möbius coefficients; no hypothetical source is substituted.

The two numerical strip routes need upper exponents m−1+ε on the signed tail-square average at m=6 and m=4. This component tests the specific attempt to obtain them by positive probability weighting and Cauchy–Schwarz. It does not retire signed Selberg estimates or the covariance route itself.

## Closed paper argument

The inspected theorem `exists_mobiusDivisorDiagonal_quadratic_lower` in `MobiusDivisorPositiveNormalizationCost` gives c>0 and N such that the full diagonal is at least cM² for M≥N. The pointwise channel ceiling is |a(M,d)|≤(3/5)√M≤√M. Therefore deleting D channels loses at most DM of diagonal energy:

    Q_tail(M,D) ≥ cM²−DM.

On M=j^m, D=j^(m−1), M=jD. Choosing j≥max(N,2/c,2) makes DM≤(c/2)M², uniformly in every integer m≥1. Hence the normalized tail diagonal lies between c/2 and 9/25. Since Q_tail≤√M U_tail, this also gives

    (c/2)M√M ≤ U_tail(M,D) ≤ (3/5)M√M.

Thus (U_tail/M)² is bounded above and below by positive multiples of j^m. Summing the upper bound through J gives at most (9/25)J^(m+1). For the lower bound, sum only over J/2<j≤J, once J exceeds twice the fixed threshold: there are at least J/2 indices and each j^m≥(J/2)^m. The cumulative lower constant may depend on m, and is positive.

For every nonnegative probability weight w on I with w(d)=0 only where a(M,d)=0, finite Cauchy–Schwarz gives

    U_tail(M,D)² ≤ Σ_I a(M,d)²/w(d).

The weights w(d)=|a(M,d)|/U_tail attain equality whenever U_tail>0. Therefore even the optimal positive normalization has the displayed J^(m+1) scale. At m=6 and m=4 it costs J^7 and J^5, whereas the signed arithmetic targets cost J^5 and J^3.

## Positive survivor and scope

The survivor is the unconditional two-sided scale law for the literal truncated diagonal, absolute source mass, and optimal positive envelope. The small quotient support q<j does not reduce the effective number of signed dilation coefficients to j: the high-dilation diagonal and absolute mass still retain their full M-scale orders.

The signed Selberg interval formula concerns divisor-step Gram matrices. Applying it directly to integrated square-root channels requires a comparison; the identity alone supplies no missing signed estimate. No statement here rules out a comparison that preserves cancellation.

## Gates

- [x] Inspect source definitions, full-diagonal lower bound, and actual channel ceiling.
- [x] Close paper proof with explicit deletion cost and half-window summation.
- [x] Formalize literal tail diagonal and mass lower bounds on all positive power meshes.
- [x] Formalize the sharp cumulative positive-envelope bounds and optimal-weight comparison.
- [x] Focused leaf check, standard-axiom audit, umbrella wiring, formal lint, report update.

## No-go closure

`not_mobiusDivisorDilationPositiveMeshEnergy_le_pow` rules out even an eventual O(J^m) bound on this positive envelope. The desired all-epsilon J^(m−1+ε) family therefore cannot follow by applying positive probability normalization directly to the unprocessed dilation coefficients. Signed grouping and signed covariance estimates remain live routes.

The strongest survivor is the sharp two-sided scale law for the actual tail diagonal and absolute mass, the cumulative J^(m+1) envelope, and its attained minimum over positive probability weights. The paper proof is dependency-closed. All ten public theorems in [QuasiRHHighDilationPositiveEnvelope.lean](../../../../formal/GaloisForLFunctions/RHTower/QuasiRHHighDilationPositiveEnvelope.lean) pass a warning-free focused `lake --old env lean` check and use only `propext`, `Classical.choice`, and `Quot.sound`. The leaf is wired into `RHTower` and the search index was refreshed.

The recorded global lint run flags only the unrelated unreachable module `SquareRootThreshold.WeilGroundStateLawOnLagLattices`; it reports no error in this leaf. No full or umbrella build was run.

Numerical 5/6 and 3/4 covariance bounds remain open. External novelty is unclaimed.
