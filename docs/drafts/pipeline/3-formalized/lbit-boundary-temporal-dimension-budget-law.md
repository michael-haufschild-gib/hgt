# L-bit boundary temporal-dimension budget law

- **ID:** `lbit-boundary-temporal-dimension-budget-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Labels:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** hostile repair of the recurrence--locality merger

## Exact claim

Use the explicit countable coefficient field
\(J_A=\texttt{quasiLocalInfiniteLBitCoefficient}(A)\) and its finite
diameter-weighted mass
\[
  K=\sum_A 2^{\operatorname{diam}(A)}|J_A|.
\]
For \(r\in\mathbb N\), put
\[
 F_r=\{1,\ldots,r\},\qquad y_r=r+1,\qquad D_r=2^r,
\]
and define the boundary-born packet
\[
 A_{r,S}=\{0,y_r\}\cup S,\qquad
 b_{r,S}=J_{A_{r,S}}\quad(S\subseteq F_r).
\]
Then:

1. the \(D_r\) coefficients \(b_{r,S}\) are rationally linearly
   independent;
2. adding \(y_r\) to the resolved environment of the flip at \(0\)
   doubles its temporal rank from \(D_r\) to \(2D_r\), and the new
   coefficient packet is exactly \((b_{r,S})_{S\subseteq F_r}\);
3. the same packet obeys the locality budget
   \[
     \sum_{S\subseteq F_r}|b_{r,S}|
       \le \frac{K}{2D_r};
   \]
4. for every coefficient threshold \(\delta>0\),
   \[
     \delta\,
     \#\{S\subseteq F_r:|b_{r,S}|\ge\delta\}
       \le \frac{K}{2D_r};
   \]
5. if every boundary-born direction is \(\delta\)-resolved, then
   \[
     2\delta D_r^2\le K.
   \]

The claim is about coefficient resolution. It is not yet a finite-time,
finite-noise measurement theorem.

## Paper proof

The map
\[
  S\longmapsto A_{r,S}=\{0,r+1\}\cup S
\]
is injective on subsets of \(F_r\), because \(F_r\) contains neither
\(0\) nor \(r+1\). The global field \(A\mapsto J_A\) is rationally
linearly independent on nonempty finite supports. Restriction along this
injective map proves clause 1.

The incident packet for environment \(F_r\) is
\[
  \{J_{\{0\}\cup S}:S\subseteq F_r\}.
\]
For \(F_r\cup\{r+1\}\), every subset either excludes \(r+1\), reproducing
the old packet, or is \(S\cup\{r+1\}\) for a unique \(S\subseteq F_r\),
producing \(b_{r,S}\). Global rational independence makes the two packets
jointly independent. Their cardinalities are \(D_r\) and \(D_r\), so the
local-flip temporal rank doubles from \(D_r\) to \(2D_r\). This proves
clause 2.

Every \(A_{r,S}\) contains \(0\) and \(r+1\), hence
\(\operatorname{diam}(A_{r,S})\ge r+1\). Therefore
\[
  2^{r+1}\sum_{S\subseteq F_r}|b_{r,S}|
  \le
  \sum_{S\subseteq F_r}
    2^{\operatorname{diam}(A_{r,S})}|J_{A_{r,S}}|
  \le K.
\]
Since \(2^{r+1}=2D_r\), clause 3 follows.

Let \(N_{r,\delta}\) count packet coefficients with magnitude at least
\(\delta\). Their absolute sum is at least
\(\delta N_{r,\delta}\), so clause 3 proves clause 4. If every one of the
\(D_r\) coefficients is at least \(\delta\), then
\(N_{r,\delta}=D_r\), and clause 4 gives
\[
  \delta D_r\le\frac{K}{2D_r},
\]
equivalently clause 5.

No compactness, probability, thermodynamic limit, Diophantine estimate or
microscopic-localization transfer is used.

## Hostile audit

The earlier candidate compared the rank of coefficients supported inside
\(F_r\) with a commutator controlled by coefficients containing the
external site \(r+1\). Those packets were disjoint; choosing distance equal
to environment size manufactured inverse-dimension scaling from two
independent variables. That candidate is `[BRIDGE]` and is not a coupled
law.

The present theorem survives that objection because the same coefficients
\(b_{r,S}\) both:

- create exactly the new temporal directions when the observer crosses the
  boundary; and
- pay the diameter-weighted spatial-locality budget across that boundary.

The coefficient-threshold objection is closed by the finite-time nonlinear
phase theorem in `operational-boundary-time-capacity-law.md`.

## Operational closure

Let \(\mathcal R_{r,t}\) be the exact demodulated double-endpoint-flip
phase response and let \(N_\eta(r,t)\) count its normalized Walsh
coefficients of magnitude at least \(\eta\). Walsh--Parseval, the
unit-circle chord bound and the same-packet locality budget prove
\[
  \eta^2 N_\eta(r,t)D_r^2\le 4K^2t^2.
\]
If all \(D_r\) directions are resolved, then
\[
  \eta^2D_r^3\le4K^2t^2.
\]
This is an unconditional nonlinear-response capacity law. It does not claim
a matching lower bound or retain the earlier unsupported \(D_r^2\) time
exponent.

## Formalization

Implemented in
`formal/GaloisForLFunctions/HTGeometry/LBitBoundaryTemporalDimensionBudgetLaw.lean`.
Capstones:

- `lbitBoundaryCoefficient_linearIndependent`;
- `quasiLocalInfiniteLBitIncidentRestriction_newEnvironmentSubset_eq_boundary`;
- `lbitBoundary_localFlipTemporalRank_doubles`;
- `two_pow_mul_lbitBoundaryPacketAbsMass_le_weightedMass`;
- `two_pow_mul_thresholdCount_le_weightedMass`;
- `two_mul_threshold_mul_sq_two_pow_le_weightedMass`.

The direct module check passed with `lake env lean`. The axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Promotion gates

- [x] exact same-packet statement
- [x] dependency-closed paper proof
- [x] hostile disjoint-packet audit
- [ ] external priority audit
- [x] exact Lean formalization and axiom audit
- [x] operational finite-time strengthening
