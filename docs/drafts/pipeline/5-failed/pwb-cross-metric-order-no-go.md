# PW-B single cross-metric CTP readout

- **ID:** PW-B-cross-metric-order
- **Stage:** 5-failed (subroute)
- **Type:** FALSIFIED
- **Statement:** A readout of the single literal complementary metric cannot retain a nonzero ordered CTP pairing in both leg orientations.

## No-go closure

- **Killing theorem:** `CrossMetricOrientationNoGo.crossBranchMetric_readout_orderDifference_zero` proves exchange fixes the entire metric field, hence every field readout has zero skew part. `metric_only_incidence_forces_fullCausalPair_zero` compares this with the literal full CTP skew law.
- **Positive survivor:** `complementaryMetricCurrentCarrier_exchange` proves the exact parity decomposition of the displayed pair `(crossBranchMetric, liftAngularCurrent)`: metric even, contact-completed Einstein current odd. This is a candidate boundary datum, not a proved physical incidence between the two fields.
- **Route consequence:** B2 must derive an ordered two-field current/source-contact incidence through the full/lift-defect cap; a single cross-metric readout cannot supply it.
- **Status:** Paper proof dependency-closed; direct `lake env lean` passes, umbrella wired. OLean emission hit a 75-second cap; transitive axiom audit pending. This does not retire the full B2 or PW-B route.
