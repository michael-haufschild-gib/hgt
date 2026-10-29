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

Certified: exact integer-grid Gram completion, cyclotomic divisibility classification of its radical, and completion by divisor conductors to the discrete bridge. Capstone axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Completed modules are wired into the CACT umbrella; no umbrella build.

Drafts under check: the actual residue error controls all real and complex Gram packets, and actual affine prime windows converge uniformly in both affine parameters.

Paper proof and Lean draft: rational refinement replaces the signed Möbius weights by positive conductor completion. For `m>1`, `L>0`,

`L² A_m(k/L) = sum_{e | mL, e/gcd(e,L)=m} E_e(k)`.

The same identity holds for every mixed entry of the centered Gram. Its proof uses Möbius inversion and the exact divisor/gcd dilation equivalence already in the corpus. This is not yet certified. Extending the identity to all real points requires continuity or a direct real Hilbert realization.

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
