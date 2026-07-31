# L-bit support-local reporter law

Status: formalized  
Label: `[LEAN-PROVED]`

## Result

Fix a target block \(L\), an outside block \(O\), and one outside
configuration \(\eta\). Varying only the target block requires exactly
\(2^{|L|}\) configurations. The alternating target-block contrast satisfies

\[
D_{L,\eta}=2^{|L|}K_{L,\eta},
\qquad
K_{L,\eta}
=\sum_{B\subseteq O}J_{L,B}\chi_B(\eta).
\]

Thus the support-local reporter measures the exact environment-dressed
coefficient. It does not identify the bare target coefficient from one
outside slice. The strict dressing mass gives the uniform bound

\[
|K_{L,\eta}-J_{L,\varnothing}|
\le \sum_{\varnothing\ne B\subseteq O}|J_{L,B}|.
\]

The centered finite-time phase response is exactly

\[
\operatorname{sinc}\!\left(
A\,2^{|L|}K_{L,\eta}
\right).
\]

Every nonzero dressed coefficient has a finite positive calibrated horizon
where this response vanishes, while a zero coefficient has response one.
Deterministic complex response errors smaller than \(1/2\) cannot confuse
those two calibrated responses.

## Formal trace

- `card_lbitSupportSliceConfigurations`
- `lbitBipartiteEnergy_lbitBipartiteCoefficientOf`
- `lbitSupportSliceDetuning_eq`
- `lbitSupportLocalFinitePhaseResponse_eq_sinc`
- `lbitSupportLocal_calibratedPhaseResponse`
- `lbitSupportLocal_measurementsSeparated`
- `abs_lbitDressedConditionalCoefficient_sub_bare_le`
- `abs_lbitSupportSliceDetuning_sub_bare_le`

Direct target check:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitSupportLocalReporterLaw.lean
```

passed on 30 July 2026.

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Physical boundary

This is a deterministic finite diagonal-l-bit reporter theorem. Cost depends
on target support size, not ambient system size, but remains exponential in
\(|L|\). The outside l-bit configuration must be controllable. The error
radius is not yet a shot-noise, decoherence, calibration, or gate-error
model. Quasi-local decay can control dressing mass only after a separate
microscopic decay theorem.

## Significance

This closes the ambient-\(2^N\) reporter objection and supplies the exact
locality interface needed by the recurrence paper. It is a methods theorem,
not the Nature headline.
