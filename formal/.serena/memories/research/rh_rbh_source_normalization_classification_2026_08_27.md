# RBH source-normalization classification (2026-08-27)

Lean module `GaloisForLFunctions.RHTower.ReflectedBiHeatSourceNormalizationClassification` is formalized and wired.

Main result: for `F_(a,b)(z)=a L(z)+b R(z)`, exact reflection defect is `(a-b)(Re z-1/2)`. Thus reflection equality iff `a=b` (identically blind) or `Re z=1/2`; for `a≠b`, universal equality over `XiDivisorSupport` iff RH. Any common nonzero complex normalization of actual multiplicity-leading RBH jets cancels from norm balance and preserves same critical-wall locus.

No-go closure: fixed linear/common-scalar source normalization cannot produce RBH equality. Strongest survivor is unique one-dimensional antisymmetric horizontal coordinate. Remaining RBH producer must be relative/oriented cross-channel transport before norms or sign/phase-sensitive incidence.

Verification: direct Lean passed; targeted build `11455/11455`; axioms only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/3-formalized/reflected-bi-heat-source-normalization-classification.md`.

Frontier map is user-declared read-only; do not edit it.