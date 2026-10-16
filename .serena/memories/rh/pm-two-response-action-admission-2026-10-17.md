# PM: complementary-response event-action admission

Completed 2026-10-17. Read source declarations before using this memory as mathematical evidence. The frontier map `docs/reports/rh-current-frontier-map.md` was read-only in this task and was not edited.

Main module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean`, namespace `RHTower.D4BMPWNativeTwoResponseAction`.

- `complementary_native_action_tendsto` has only actual zero-copy, branch, amplitude, and angular-coordinate parameters; no analytic premises. The canonical wedge cutoff action of the true/false physical-rate retarded fields converges to `fullAngularField q branch ![X, Real.exp k] * fullCausalSourcePair q branch true false a d X k`.
- `complementary_native_action_admitted` supplies the two wave integrabilities and two outer native integrabilities without analytic premises. `nativeBulk_target_integrable_ae` supplies inner admission for the smooth compact response tests.
- `nativeTwoResponseAction_tendsto_of_exhaustion` establishes independence across smooth compact wedge cutoffs between zero and one converging pointwise to one.
- The action definition uses actual retarded fields, the event wave operator, and the original native Dirichlet kernel, with no source pairing in the definition. Full/full terms cancel by admitted Fubini. The native correction remains.

New supporting modules: `ThetaCuspHawkingBMPWRetardedTriangle`, `ThetaCuspHawkingBMPWRetardedRegularity`, `ThetaCuspHawkingBMPWTwoResponseAction`, `ThetaCuspHawkingBMPWTwoResponseActionLimit`. Existing `ThetaCuspHawkingBMPWRetardedWeakNative` gained admission helpers while preserving its weak identity. All five new modules are wired into `GaloisForLFunctions.RHTower`.

Removed obstruction: event-variable response insertion. Exact moving source triangles and smooth logarithmic coordinates prove interior event regularity, making compact response-valued tests admissible. Source-response absolute admission then yields the combined action limit. Fixed angular coordinates only. Native integrals retain target-then-source order: inner absolute integrability a.e. source plus absolute outer integrability. No joint native Fubini theorem, separate cap/native limit, angular cusp limit, Einstein/optical incidence, fixed-grade PW magnitude, extinction, or RH result is claimed. Next obstruction: ordered top-time trace with native correction retained.

Verification: all six leaf module checks passed via foreground `lake --old env lean -j 1`; final scratch audit exited 0. Axioms printed for triangle identity, response regularity, native cancellation, main limit and admission were exactly `propext`, `Classical.choice`, `Quot.sound`. No heartbeat increases, numerical experiments, full or umbrella builds. Own scratch files cleaned. Repository lint exited 1 on 11 unrelated unreachable modules; no PM reachability error or banned declaration was reported. Full list is in the formalized card.

Paper proof, conjecture ledger, exact scope, and validation: `docs/drafts/pipeline/3-formalized/pm-structural-obstruction-removal-2026-10-16.md`.
