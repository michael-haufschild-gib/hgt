# Steklov index certificates cover every integer horizon

- **Stage:** 3-formalized
- **Programme:** A4
- **Lean:** `EffectiveArithmeticHodgeTheory/SteklovIndexCertificatesAtEveryHorizon.lean`; direct Lean and transitive axiom audits passed.

Every finite part `d` of the full Weil index has a finite real logarithmic
Denjoy–Carleman witness family, constructed by the proved Steklov mollification.
Its actual negative eigenvectors give a compression `S` and margin `δ>0`.

At any integer horizon `N`, put `j=⌊N/blockSize(R)⌋`. For `j≥2` and inverse
width `k≥1`, the proved logarithmic synthesis gives the explicit error
`dcSynthErr(M,b,2 steklovBaseSup,12,k,∫|steklovDCProfile|,m,j)` and the
corresponding `emLip` bound. Polarization gives the full Weil entry budget.
If each compressed entry budget is at most `δ/(2(r²+1))`, the synthesized
matrix retains all `r≥d` negative directions. Zero extension from `j blockSize(R)`
to `N` preserves that Gram matrix. Thus the certificate covers every residue
class without an additional asymptotic threshold.

Taking `k=N/superGevreyRatio(β,N)` and `m=gevOrder(k)` gives a finite test
on the exact Steklov schedule. Every analytic input and every source derivative
bound is constructed. The existing exhaustion theorem guarantees eventual
index attainment; this statement exposes its finite synthesis inequalities.
It does not assert a dimension-only bound on unknown negative witnesses.

Caps: `exists_steklov_index_horizon_test`,
`exists_steklov_schedule_index_horizon_test`. Both depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.
