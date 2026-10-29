# Cyclotomic positivity and the complete affine overlap operator

Status: in progress.

## Objective

Find and formalize an unconditional new arithmetic comparison that transports cyclotomic positivity toward the actual complete overlap form. Secondary direction: reduce the overlap needed by Denjoy–Carleman synthesis. A scalar identity, a fixed-mode limit, and full operator positivity are distinct milestones.

## Current frontier

The report in docs/reports/review-2910/astra.md identifies conductor-uniform overlap curvature, actual fixed-conductor affine prime windows, annular Ramanujan frames, and complete positivity just beyond touching. The missing input is the completed operator comparison with mixed blocks, complement, Gamma and both poles.

## Research discipline

Search the local Lean corpus before source selection or Mathlib lookup. Work through conjecture, proof attempt, obstruction and positive survivor. Do not promote a receiver's premise to an unconditional result. No numerical experiments. Targeted foreground Lean checks only, one at a time; no full or umbrella builds. Preserve unrelated concurrent edits.

## Conjecture log

1. Pending source study: the cyclotomic curvature can enter an exact positive matrix identity for affine residue averages, providing an operator-level arithmetic survivor before the analytic comparison.

## Paper and Lean status

Certified: exact integer-grid Gram completion, cyclotomic divisibility classification of its radical, completion by divisor conductors to the discrete bridge, and simultaneous actual prime-source comparison for all real and complex Gram packets. The source module also proves a lower bound in the unit Gram itself, with no non-unit penalty. Capstone axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Completed modules are wired into the CACT umbrella; no umbrella build.

Drafts awaiting checks: actual affine prime windows uniform in both parameters; actual primitive-phase prefix Gram domination; the identity with the existing prime-block jump energy; real-variable Gram positivity and its exact unit-cell minimum kernel; the smaller fixed-profile synthesis endpoint.

Paper proof and Lean draft: rational refinement replaces the signed Möbius weights by positive conductor completion. For `m>1`, `L>0`,

`L² A_m(k/L) = sum_{e | mL, e/gcd(e,L)=m} E_e(k)`.

The same identity holds for every mixed entry of the centered Gram. Its proof uses Möbius inversion and the exact divisor/gcd dilation equivalence already in the corpus. Its targeted Lean check is active. A paper proof and separate Lean draft extend positivity to all nonnegative real points by continuity and common-grid approximation.

## Broader implications

To be established after identifying an exact unconditional theorem. Full RH, a macroscopic complete-form positivity theorem, and a synthesis improvement remain open until their actual inputs are proved.

## First mathematical outcome

The uncentered kernel E_m(|i-j|) is not positive semidefinite: E_m(0)=0 and E_m(1)=phi(m)>0. This kills only the naive scalar-to-kernel lift.

Positive survivor, paper argument ready for immediate formalization: put v_k(zeta)=sum_{j<k}zeta^j over primitive m-th roots. Prefix subtraction is a unit rotation of a shorter prefix, hence ||v_i-v_j||²=E_m(|i-j|). The centered kernel (E_m(i)+E_m(j)-E_m(|i-j|))/2 is the actual real Gram kernel. Its full quadratic form is the sum of squared weighted primitive-root prefixes. The uncentered form equals twice total coefficient mass times its weighted moment minus twice that square energy. In particular it is conditionally negative, with an exact equality criterion.

This is not yet a complete-Weil comparison. It determines the required centering and sign and retains all finite mixed entries. Next: classify the radical, test conductor-uniform coercivity after unit averaging, and transfer actual finite arithmetic averages before considering growing horizons.

## Further conjectures and paper outcomes

2. Fixed-conductor Gram radical. A prefix packet defines P(X)=sum_i a_i sum_{j<k_i} X^j. Its completed energy is zero iff Phi_m divides P over the reals. Across conductors, the radical is the intersection of those divisibility conditions. Draft formalization uses the existing exact Selberg recurrence theorem.

3. Conductor completion. Summing over nontrivial m dividing Q gives the exact mixed kernel Q min(i,j)-ij for 0<=i,j<=Q. This is a positive way to remove omitted cyclic frequencies; conductor one contributes ij. Draft formalization records the exact formula.

4. Actual source comparison. Let delta_N be the total absolute error of the actual residue masses from their logarithmic unit means. Existing residue Mertens convergence implies delta_N -> 0. Exact finite decomposition gives |window(F)-ell*kappa(F)| <= delta_N sum_r |F(r)| simultaneously for every signed F. For squared finite packets this is an operator comparison in the full residue Gram norm, uniform in both coefficients and feature family, including choices depending on N. All prime powers are retained. Draft formalization covers real and complex packets.

The full residue norm is necessary: non-unit prime powers can see directions invisible to the unit-only limiting Gram. For root-prefix features, the conductor-completion identity identifies that extra norm. The next task is the exact actual-affine specialization and then the comparison with the complete Weil source. No macroscopic-overlap or RH result is claimed by these finite-source statements alone.

## Secondary synthesis conjecture

The existing general `OverlapGrowthSuperGevrey` receiver is stronger than its displayed power-log schedule. Keeping its already constructed profile, test the explicit endpoint schedule

`c_N = L*(log L)^2*log(log L)`, `L=log(log N)`.

The final factor diverges, so it should satisfy the exact existing growth criterion; it is little-o of `L*(log L)^beta` for every beta>2. This is a genuine but smaller improvement than the proposed new-profile schedule `L*log L*(loglog L)^beta`. The latter still requires a new Denjoy–Carleman construction. Corpus novelty search is in progress; neither improvement is yet claimed formalized.

## One-sided source domination

The absolute error estimate uses the full residue norm. That does not impose the same cost on lower bounds: non-unit prime powers contribute nonnegatively to every Gram packet. The stronger paper statement is

`eventually N, for every F>=0, (log B-log A-epsilon)*kappa_q(F) <= residuePrimeWindow q F A B N`.

Proof: each residue indicator has nonnegative actual mass and nonnegative unit mean. A zero mean requires no estimate; a positive mean permits the strict margin epsilon times that mean by the existing limit. Finitely many indicators share one horizon, and every nonnegative pattern is their nonnegative linear combination. Applying this to norm squares yields an operator lower bound in the unit Gram itself, uniform in all feature and coefficient families, including height-dependent choices. Draft added to `PrimeResidueWindowsControlEveryGramPacket.lean`; check pending.

Next exact specialization: identify the unit mean of actual primitive-phase prefix packets with their cyclotomic Gram energy divided by phi(q). Existing root-power enumeration and residue/units decompositions supply the finite identification. This would transport the newly completed Gram into a concrete actual prime-prefix form. It would still not identify that form with the complete Weil correction.

## Moving windows and variation

The finite-part Mertens limit should also provide one horizon controlling every pair of endpoints above it. The existing `RHTower.Sieve.abs_sum_mul_le_of_bounded_partial_bv` can then transport this bound to envelopes varying with prime height, with an explicit endpoint-plus-variation cost. This is a proposed next theorem, not a proved full-Weil comparison.

## Closure scope

User requested completion of existing Lean drafts and paper proofs, followed by stopping. No further research branches are being opened. The existing finite/arithmetic and synthesis drafts will receive direct Lean audits; conjectural moving-window, Fourier and real-radical extensions remain explicitly unproved.

The source-sign check is decisive for interpreting this batch: `TransMetzlerDecomposition` subtracts the actual `nonRatioForm` from the complete form. A lower bound for an auxiliary positive prime Gram is therefore insufficient. The unresolved theorem must give an upper bound for the adverse actual prime contribution, or a joint lower bound after combining it with the retained Gamma and polar terms. No such theorem has been obtained in this batch.
