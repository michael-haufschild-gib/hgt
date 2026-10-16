# PM: admitted complementary-response event action

Status: formalized, 2026-10-17. All six module audits and the final dependency
audit passed. Repository lint reports unrelated umbrella-reachability errors,
listed below.

## Contract

Produce one unconditional structural theorem removing a hard obstruction in route PM.
An estimate, an RH equivalence, a receiver, or a formalization-only increment does not satisfy
the task. Research from the current Lean corpus; no web search, external novelty audit, or
historical Markdown review. No numerical experiments, full builds, added axioms, or
heartbeat increases. Preserve unrelated work in the shared tree.
`docs/reports/rh-current-frontier-map.md` is read-only for this task.

## Work plan

1. Read PM entry and search actual Lean statements across the corpus.
2. Identify an obstruction and formulate exact competing conjectures.
3. Attack each conjecture; record failures and immediately derive the next conjecture.
4. Complete a dependency-closed paper proof before formalization.
5. Formalize, audit with foreground `lake env lean`, check axioms and lint, and wire imports.
6. Assess whether the result actually removes the obstruction; continue if it does not.

## Starting frontier

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
   PROVED: construct the compactly cut-off two-response action from the actual
   retarded fields, prove its exact source contact with the native bulk retained, and
   pass to an exhaustion of the physical wedge. This is an action-domain construction,
   not a claim of optical extinction or of equality to the PW magnitude.

## Current proof mechanism

Write U_b for the full retarded response, H for the full angular source vertex,
and f_b for the physical reduced time source. Write B_b[phi] for the native
kernel action: integrate f_b times lambda sech(x)^2 K_native times phi over
the target event, then integrate over the physical source event. The order is
part of the definition. After admitting full-kernel Fubini, the existing weak
equation reads

    integral U_b box(phi) = H integral f_b phi
      + integral lambda sech(x)^2 U_b phi + B_b[phi].

For a smooth compact cutoff chi inside the physical wedge, use chi U_c and chi U_b
as the two weak tests. Their skew difference gives the actual cut-off action

    integral [U_b box(chi U_c) - U_c box(chi U_b)]
      - (B_b[chi U_c] - B_c[chi U_b])
      = H integral chi (f_b U_c - f_c U_b).

The full/full terms cancel algebraically; the native mixed action is retained.
The existing absolute two-event source admission controls the right-hand side on
an exhaustion, so the combined action has an unconditional limit. It does not
assert separate convergence of the cap and native bulk.

### Dependency-closed paper proof

1. Set p=t+x and r=t-x, so the open physical wedge is 0<p<r. In source
   coordinates A=s+y and B=s-y, the Jacobian is 1/2. The source vanishes for
   A<0; the radial wall is B=A. Direct causality imposes A<=p and B<=r.
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
   integration proves smoothness in p,r on 0<p<r, with X,k fixed.
3. Let chi be smooth with compact support in that wedge. The product chi U_b
   is globally smooth: within the wedge use step 2; off its support it vanishes
   on a neighborhood. It is therefore a valid test for the existing actual
   weak equation. Apply the equation twice with tests chi U_c and chi U_b.
   The reflected source vertex vanishes because the tests have negative radial
   support. Compact target support and existing full-kernel admission give
   integrability of the wave action. The weak equation then admits the coupled
   source action; subtracting its admitted contact admits the outer coupled
   bulk. Inner coupled admission follows from the kernel weak law and full
   target admission. Subtract the two identities, retaining both bulk terms.
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

The six checked modules formalize this construction and admission of the combined
action. Separate cap/native limits, Einstein-current incidence, fixed-grade
magnitude, and extinction are not consequences.

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
- `ThetaCuspHawkingBMPWTwoResponseAction.lean`: finite two-response insertion
  and absolute action admission passed direct Lean audit.
- `ThetaCuspHawkingBMPWTwoResponseActionLimit.lean`: exhaustion and cutoff
  independence passed direct Lean audit.
- `ThetaCuspHawkingBMPWNativeTwoResponseAction.lean`: literal native action,
  absolute iterated admission, full/full cancellation, and the unconditional
  complementary-rate limit passed direct Lean audit.
- All five new modules are imported by `GaloisForLFunctions.RHTower`.
- All six module checks used foreground `lake --old env lean -j 1`, with one
  owned Lean process at a time. Each emitted object is newer than its source.
- Final `lake --old env lean -j 1 /tmp/pm_final_audit.lean` exited 0. It checked
  both exported complementary-action theorem types, verified the used Mathlib
  names, and printed transitive axioms for the triangle identity, response
  regularity, native cancellation, action limit, and absolute admission.
  Every printed axiom list was exactly `propext`, `Classical.choice`, `Quot.sound`.
  No added axioms or proof placeholders occur. The temporary audit file was
  removed after recording the result.
- `scripts/formal_tools.py lint` exited 1: 11 unrelated modules are unreachable
  from their theorem-area umbrellas. No PM module is unreachable, and no banned
  declaration was reported. The reported modules are:
  `RHTower.CHMDCompactOrbitInertia`, `RHTower.CHMDCompactTestSynthesis`,
  `RHTower.CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection`,
  `RHTower.FiniteWeilNodalAdjacentCoupling`, `RHTower.FiniteWeilNodalMixtureTransport`,
  `RHTower.LeeYangPrimePivotSpinPartitionSpectrum`,
  `RHTower.OddSectorExactSpectralInterpolation`, `RHTower.OddSectorGroundZeroInterpolation`,
  `RHTower.WeilCompactNegativeSubspace`, `RHTower.WeilCompactOrbitInertia`, and
  `HTGeometry.DenseCoreFiniteConstraints`. These concurrent modules are outside
  this task's write scope; the global lint gate is not claimed clean.
- No heartbeat increases. No numerical experiments. Only one owned Lean process
  at a time; dependency objects emitted by direct foreground leaf checks.

## Exact analytic scope

The native term retains the order: integrate the target event, then the physical
source event. Inner native integrability holds for almost every source; the
resulting source function is integrable. No joint absolute native Fubini theorem
is claimed. Full/full cancellation uses the existing jointly integrable full
kernel and is therefore an admitted Fubini operation. The exhaustion limit is
for the combined wave-minus-native action, not for its two components separately.

## Final theorem interface

`D4BMPWNativeTwoResponseAction.complementary_native_action_tendsto` quantifies
only over the actual zero copy, angular branch, source amplitudes, and angular
base coordinates. Its canonical cutoffs are `D4BMPWTwoResponseAction.wedgeWindow`.
The finite action is defined from the actual retarded fields, the event wave
operator, and the original native Dirichlet kernel. No source pairing occurs in
that definition.

`complementary_native_action_admitted` supplies the four outer integrability
statements without analytic premises. `nativeBulk_target_integrable_ae` supplies
inner target admission. `nativeTwoResponseAction_tendsto_of_exhaustion` proves
independence across all smooth compact wedge cutoffs between zero and one that
converge to one in the wedge.

The removed obstruction is the two-response **event-action domain**. The prior
weak law accepted arbitrary smooth compact tests but did not admit the literal
retarded responses. Moving cone boundaries and the closed-cone radius obstructed
that insertion. Exact source triangles and smooth logarithmic coordinates now
give response regularity; explicit wedge cutoffs produce valid response-valued
tests and a cutoff-independent action limit.

Identification with the Einstein/optical current, the fixed-grade PW magnitude,
and the ordered extinction step remain open. Regularity is in the event
coordinates with angular base coordinates fixed. No uniform angular limit or
cusp integration is asserted. The next distinct obstruction is the ordered
top-time trace of this admitted action with its native correction retained.
