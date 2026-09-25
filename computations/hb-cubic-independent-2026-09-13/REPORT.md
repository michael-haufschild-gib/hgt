# Independent cubic tensor validation

All 24 parameter/polarization/correction/precision combinations passed, each checking four readers. The independent calculation differentiates explicit coordinate fields, then evaluates inverse metric, determinant and curvature directly. The discovery calculation instead propagated truncated perturbation series. This tests both the coordinate-jet construction and the cubic coefficient extraction.

Maximum scaled errors against the exact rational discovery coefficients:

| Decimal precision | Maximum error |
|---:|---:|
| 50 | 1.72e-30 |
| 100 | 2.38e-60 |
| 160 | 6.65e-97 |

Full family completed in 7.65 seconds, including explicit-coordinate jet preparation and guard overhead; summed worker time 30.41 seconds. Download checksums verified. Finite-radius quadrature error and roundoff decrease together; these are numerical checks, not rigorous error enclosures.

The local P_S^2 Q_V coefficient is zero for the sampled scalar readers while vector readers recover nonzero coefficients. At s=-5/4,r=2 with affine path, the same/opposite vector-reader coefficients are exactly the candidates 1079925/524288 and 1511895/524288. Known local correction changes those vector responses, without establishing any full-action cancellation. Other mixed-polarization values also agree.

Novelty challenge: angular coexact structure can plausibly explain scalar blindness; the generic zero pattern is not promoted as a new theorem. Positive residue is the independently validated explicit channel table and a concrete requirement to retain reader-visible mixed channels. Full literal angular incidence, complete causal corrections and every integrated boundary contribution remain open. No RH exclusion or extinction follows.
