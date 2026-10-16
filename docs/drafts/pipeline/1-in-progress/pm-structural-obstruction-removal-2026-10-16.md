# PM: structural obstruction removal

Status: in progress. No contribution claimed yet.

## Contract

Produce one unconditional structural theorem removing a hard obstruction in route PM.
An estimate, an RH equivalence, a receiver, or a formalization-only increment does not satisfy
the task. Research from the current Lean corpus; no web search, external novelty audit, or
historical Markdown review. No numerical experiments, full builds, added axioms, or
heartbeat increases. Preserve unrelated work in the shared tree.

## Work plan

1. Read PM entry and search actual Lean statements across the corpus.
2. Identify an obstruction and formulate exact competing conjectures.
3. Attack each conjecture; record failures and immediately derive the next conjecture.
4. Complete a dependency-closed paper proof before formalization.
5. Formalize, audit with foreground `lake env lean`, check axioms and lint, and wire imports.
6. Assess whether the result actually removes the obstruction; continue if it does not.

## Current evidence

The PM entry identifies Haar approximation and small-damping L² admission on the FZZ branch;
complementary-rate two-response insertion, ordered cap, and all-divisor extinction on PW-B.
The Fourier reconstruction and exact energy identities do not construct an approximation.
Current source inspection includes both branches to avoid treating a receiver as progress.

## Conjecture ledger

1. A conserved full/native linear current could retain the full source contact.
   Verdict: FALSE in the corpus. `D4BMPWOperatorAnomaly.compatible_source_full_zero`
   includes nonlocal complex-linear readers; semilinear versions also vanish.
   Survivor: the actual full-minus-native lift is an admitted operator anomaly, already proved.
2. Prove nonvanishing of both finite-energy source responses.
   Verdict: ALREADY PROVED. `pwb_weakSourceMass_pos` closes this exact issue.
3. Identify the oriented CTP source with the crossed optical flux by fixed calibration.
   Verdict: FALSE as an amplitude-uniform mechanism. `completedCTP_amplitude_four`
   and `amplitudeCrossedFlux_eq` give degrees four and eight; the two-amplitude
   incidence theorem forces criticality rather than producing it.
4. Retain the anomaly and insert both literal retarded responses into the wave action.
   Current target: construct the compactly cut-off two-response action from the actual
   retarded fields, prove its exact source contact with the native bulk retained, and
   pass to an exhaustion of the physical wedge. This is an action-domain construction,
   not a claim of optical extinction or of equality to the PW magnitude.

## Current proof mechanism

Write U_b for the full retarded response and N_b for its native counterpart, H for
the full angular source vertex, and f_b for the physical reduced time source.
The existing weak equation is

    box U_b = H f_b + lambda sech(x)^2 (U_b + N_b).

For a smooth compact cutoff chi inside the physical wedge, use chi U_c and chi U_b
as the two weak tests. Their skew difference gives the actual cut-off action

    integral [U_b box(chi U_c) - U_c box(chi U_b)
      - chi lambda sech(x)^2 (N_b U_c - N_c U_b)]
      = H integral chi (f_b U_c - f_c U_b).

Both same-channel terms cancel algebraically; the native mixed term is retained.
The existing absolute two-event source admission controls the right-hand side on
an exhaustion, so the combined action has an unconditional limit. It does not
assert separate convergence of the cap and native bulk.

### Paper proof of the proposed construction

1. Set p=t+x and r=t-x, so the open physical wedge is 0<p<r. In source
   coordinates A=s+y and B=s-y, the Jacobian is 1/2. The source vanishes for
   A<=0; the radial wall is B=A. Direct causality imposes A<=p and B<=r.
   Image causality imposes A<=r and B<=p; together with B>=A this reduces
   to A<=p and B<=p. Thus the actual retarded event integral is exactly
   one quarter of the direct triangle integral minus the image triangle integral.
   Boundary discrepancies have zero source or zero Lebesgue measure. Each triangle
   is compact and its closed-cone integrand is continuous, so every split is admitted.
2. Rescale A=p alpha and B=A+(R-A) beta, where R=r in the direct arm and
   R=p in the image arm. The Jacobian is p(R-A). The corpus identity
   `triangleInvariant_factor` writes the invariant minus one as
   2(1-alpha)(1-beta) times a strictly positive smooth factor for 0<p<r.
   Put alpha=sin(theta)^2 and beta=sin(phi)^2 only as a parametrization of
   the integrand, not as a change of integration measure. The supplied
   `logarithmicRadius` is globally smooth in log p, log(r-p), theta, phi.
   Evaluation at the continuous angleMap of the fixed unit-square variables
   recovers the exact closed-cone radius. Compose with the smooth physical
   time source and smooth full angular field. Compact unit-cube parameter
   integration proves joint smoothness in p,r,X,k on 0<p<r.
3. Let chi be smooth with compact support in that wedge. The product chi U_b
   is globally smooth: within the wedge use step 2; off its support it vanishes
   on a neighborhood. It is therefore a valid test for the existing actual
   weak equation. Apply the equation twice with tests chi U_c and chi U_b.
   The reflected source vertex vanishes because the tests have negative radial
   support. All terms are integrable by compact target support and the existing
   full/native kernel growth admission. Subtract, retaining both bulk terms.
4. Choose chi_n from compact time/radial windows, multiplied by smooth onset
   and radial inner cutoffs, with 0<=chi_n<=1 and eventual value 1 at each
   point of the wedge. The source-response skew is absolutely integrable by
   `full_source_response_pairings_integrable`. Outside the wedge it vanishes
   by onset. Dominated convergence gives the combined two-response action limit
   H times the already literal `fullCausalSourcePair`, via its retarded-skew law.

5. For each compact response-valued test, multiply the test by
   lambda/cosh(x)^2. Existing absolute full-kernel Fubini admission identifies
   the full part of the coupled bulk with the target integral of
   lambda/cosh(x)^2 chi U_b U_c. It cancels under b,c interchange. Subtraction
   from the admitted coupled bulk admits the literal native-kernel integral
   itself. Thus the final action contains only the native kernel correction;
   it is not a redefinition of the contact pairing. The same dominated
   convergence argument works for every bounded smooth wedge exhaustion.

This closes the paper argument for admission of the combined action. Separate
cap/native limits, Einstein-current incidence, fixed-grade magnitude, and
extinction are not consequences. Formalization must verify every step before
any contribution is claimed.

## Corpus search notes

Hybrid and deep searches completed without partial results, but reported stale
coverage snapshot and unavailable semantic coverage. Source statements are therefore
checked directly. Serena symbol access rejects Lean files as ignored; use `rg`
and bounded source reads for Lean. No available `update_plan` tool was found;
the work plan is tracked here.

## Verification

- `ThetaCuspHawkingBMPWRetardedTriangle.lean`: direct Lean audit passed.
- `ThetaCuspHawkingBMPWRetardedRegularity.lean`: direct Lean audit passed.
- `ThetaCuspHawkingBMPWRetardedWeakNative.lean`: added absolute action-admission
  helpers and preserved the existing weak identity; direct Lean audit passed.
- Two-response insertion, exhaustion, and native bulk cancellation: written,
  audits in progress. No final contribution claimed.
- No heartbeat increases. No numerical experiments. Only one owned Lean process
  at a time; dependency objects emitted by direct foreground leaf checks.

## Exact analytic scope

The native term retains the order: integrate the target event, then the physical
source event. Inner native integrability holds for almost every source; the
resulting source function is integrable. No joint absolute native Fubini theorem
is claimed. Full/full cancellation uses the existing jointly integrable full
kernel and is therefore an admitted Fubini operation. The exhaustion limit is
for the combined wave-minus-native action, not for its two components separately.
