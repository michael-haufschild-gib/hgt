# Route E signed normalizer-flux circularity

- **ID:** `ROUTE-E-SIGNED-NORMALIZER-FLUX-CIRCULARITY-001`
- **Stage:** 3-formalized
- **Type:** `[LEAN-CERTIFIED] [EXACT WEIGHTED IDENTITY] [CIRCULARITY FIREWALL]`
- **Parent:** `route-e-entropy-complement-degree-variance-bridge.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteESignedNormalizerFluxCircularity.lean`

## Exact weighted identity

Let `U(i,j)=U(j,i)` have nonzero row masses `d_i`, and suppose every supported edge reverses
sign `s_i`. Put

\[
 F_i=\sum_jU_{ij}\left(\frac1{d_i}-\frac1{d_j}\right).
\]

For arbitrary vertex weight `w_i`, Lean proves

\[
\boxed{
2\sum_i s_iw_i
=\sum_i s_iw_iF_i
 +\sum_i s_i\sum_j\frac{U_{ij}}{d_j}(w_i-w_j).}
\tag{1}
\]

Second term is signed co-moving transport. For constant weights it vanishes:

\[
\boxed{2\sum_i s_i=\sum_i s_iF_i.}
\tag{2}
\]

If `|s_i|≤1`, triangle inequality gives

\[
\boxed{2\left|\sum_i s_i\right|\le\sum_i|F_i|.}
\tag{3}
\]

Symmetry also conserves raw degree across sign classes:

\[
\boxed{\sum_i s_i d_i=0,\qquad
\sum_i s_i=\sum_i s_i(1-d_i).}
\tag{4}
\]

Therefore

\[
\boxed{\left|\sum_i s_i\right|\le\sum_i|1-d_i|.}
\tag{5}
\]

Exact symmetric scaling to `d_i=1` is possible only after exact sign balance; approximate scaling
pays at least original imbalance in total row-degree defect.

## Proof mechanism

Row normalization transports all source weight. Sign reversal turns transported source sign into
negative target sign, so twice signed source weight equals signed incoming-weight defect. Symmetry
then fractures that defect into reciprocal-row-mass flux and change of vertex weight along the
same physical edges. No estimate enters.

## Consequence

Keeping the sign of normalizer flux avoids the large edge-mass factor introduced by absolute
Cauchy, but it does not create an independent cancellation quantity. At constant weight it is
exactly original signed imbalance; for Gibbs weights its only difference from twice signed current
is the already-budgeted co-moving term. A successful proof must derive a source-specific estimate
for this combined quantity or leave row-stochastic transport and bound unmatched mass directly.

## Lean theorem map

- `routeE_two_mul_signedWeightedSum_eq_signedWeightedIncomingDefect`
- `routeE_weightedIncomingDefect_eq_weightedNormalizerFlux_add_coMoving`
- `routeE_two_mul_signedWeightedSum_eq_signedNormalizerFlux_add_coMoving`
- `routeE_two_mul_signedSum_eq_signedNormalizerFlux`
- `routeE_two_mul_abs_signedSum_le_sum_abs_normalizerFlux`
- `routeE_sum_sign_mul_rowMass_eq_zero`
- `routeE_signedSum_eq_signedRowMassDefect`
- `routeE_abs_signedSum_le_sum_abs_rowMassDefect`

## Honest status

Exact finite identities and lower bound are closed in Lean. No normalizer-flux estimate, unmatched
mass bound, Mertens estimate, or RH proof is claimed.
