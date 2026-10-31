# Native two-response action on source data

- **ID:** native-two-response-action-on-source-data
- **Stage:** 3-formalized
- **Target:** Factor the existing native two-response action through explicit
  source functions, full/native kernels and angular coefficients, with no
  `XiZeroCopy` in the action's definition and no analytic proof fields.

## Construction

Raw data consist of the angular parameter and contact coefficient, full and
native event kernels, and two source functions with their amplitudes. Define
responses by the original source-event integrals. Define response tests,
native bulk and the skew wave-minus-native action from these data alone.
For actual source data, the response integrand is definitionally the existing
retarded integrand. Substitution identifies response tests, native bulk and
the entire action. The proved native action equality followed by the proved
contact identity gives the source-data contact identity. The existing
absolute-admission theorem supplies each of the four integrals. Its dominated
convergence theorem supplies the exhaustion limit; the skew retarded-pair
identity identifies the limit using source data alone. Equality of data then
gives equality of actions at every cutoff, independently of zero multiplicity.

This is the source-data restatement in A12. Existence of independently
constructed spectral source data is the distinct realization problem B7;
no arbitrary raw kernel is asserted to satisfy unproved admission laws.

## Verification

`RHTower/ThetaCusp/SourceActions/NativeTwoResponseActionOnSourceData.lean`
passed a direct `lake --old env lean` check. Exact pullback, absolute
admission, cutoff contact and exhaustion-limit capstones have transitive
axioms only `propext`, `Classical.choice`, and `Quot.sound`.
