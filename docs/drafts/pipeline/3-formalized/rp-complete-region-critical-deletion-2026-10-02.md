# RP: delete the complete divisor region at critical scale

- **ID:** RP-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/rh-current-frontier-map.md`, route RP; RP-24/25 quotient-ramp analysis.
- **Statement:** The complete-product region of the literal Möbius centered-divisor Abel source is critically negligible. RH is equivalent to uniform critical boundedness of the remaining smooth-plus-moving source.
- **Novelty:** Corpus extension; external novelty unaudited. This is a sector-deletion theorem, not an RH proof.

## Exact objects

Write r_j(t) for `HTGeometry.centeredModularRamp j t`, w(k)=sqrt(k+1)-sqrt(k), and

    c_m(k) = Σ_{d|m} μ(d) r_{m/d}(floor(k/d)),
    C(M) = Σ_{1<=m<=sqrt(M-1)} Σ_{m²<=k<M} c_m(k) w(k).

All square roots bounding natural indices are floored. Let

    V(k) = Σ_{1<=d<=k} μ(d)
             Σ_{1<=j<=sqrt(floor(k/d)), sqrt(k)<d*j} r_j(floor(k/d)),
    U(M) = Σ_{1<=k<M} w(k)
             (Σ_{1<=d<=k} μ(d) divisorHyperbolaSmoothRemainder(floor(k/d)) + 2 V(k)).

Then the existing `mobiusDivisorSquareRootAbelMoment M` is exactly `2*C(M)+U(M)`. Both summands retain original signs, coefficients, and endpoints.

## Dependency-closed paper proof

1. RP-25 proves the exact quotient lift r_j(floor(k/d))=r_{dj}(k)-r_d(k)/j for positive d,j. For d|m, both moduli m and d are aligned at k=m².
2. The existing centered modular Abel theorem bounds a nonnegative decreasing weighted prefix by its initial weight times modulus/8, and gives a nonpositive upper bound. The square-birth clock satisfies m*w(m²)<=1/2. Since d<=m, both lifted prefixes lie in [-1/16,0]. Dividing the smaller-modulus prefix by m/d>=1 preserves that interval. The quotient response therefore has absolute value <=1 uniformly in every endpoint, including an empty interval.
3. Retaining all μ coefficients, the triangle inequality gives |Σ_{m²<=k<M} c_m(k)w(k)|<=τ(m). The corpus fixed-divisor-moment theorem at exponent one gives Σ_{m<=R}τ(m)<=R(1+log R). Consequently |C(M)|<=R(1+log R), R=floor(sqrt(M-1)), for M>=2.
4. R<=sqrt(M) and log R<=log M imply |C(M)/M|<=(1+log M)/sqrt(M). The corpus positive-power logarithmic limit proves C(M)/M→0.
5. Finite Fubini converts C(M) to its literal time sum over m<=sqrt(k). The divisor swap converts the complete rows to d,j with d*j<=sqrt(k). These labels lie in the original active fibre j²<=floor(k/d). Splitting that finite fibre leaves exactly sqrt(k)<d*j; no padding, coefficients, or terminal blocks are discarded.
6. Apply the existing prime-free divisor identity D=Smooth+2*Centered and retain the Möbius sum. This gives the exact identity A(M)=2C(M)+U(M). A convergent real sequence is bounded, so C(M)/M is uniformly bounded. The triangle inequality in both directions transfers uniform critical boundedness between A and U. The existing unconditional equivalence RH iff bounded A/M completes the claimed equivalence.

All dependencies are corpus theorems or elementary finite identities. No RH, zero-location, Möbius-cancellation, or source-payment assumption appears.

## Frontier effect

Complete rows, including their previously proved positive full-period responses, cannot cause critical unboundedness: their entire aggregate vanishes after division by M. The unresolved arithmetic is the joint signed source U. Separate bounds for its smooth and complementary pieces are not supplied. Neither native Route-P square debt has been paid. A new equivalence alone is not counted as solving the remaining RH obstruction.

## Verification

Production leaf `formal/GaloisForLFunctions/RHTower/RoutePCompleteRegionCriticalDeletion.lean` has 320 lines and eight public theorems, and is wired once into `RHTower.lean`. Final foreground audit exited 0 with no diagnostics:

    lake --old env lean GaloisForLFunctions/RHTower/RoutePCompleteRegionCriticalDeletion.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/RoutePCompleteRegionCriticalDeletion.olean

A separate `/tmp` import audit printed axioms for all eight public theorems and exited 0. Each depends exactly on `[propext, Classical.choice, Quot.sound]`. No added axioms, proof placeholders, resource overrides, numerical experiments, full builds, or umbrella builds were used.

Selected whitespace and forbidden-token checks passed. Global formal lint exited 1 on eleven unrelated unreachable modules, none belonging to this result; no global lint pass is claimed. Detailed names and search coverage are in the RP working log.

## Log

- 2026-10-02 — Corpus-grounded paper proof completed. Unweighted sector prioritized because it welds directly to the RH criterion; logarithmic extension remains unused.
- 2026-10-02 — Final production leaf and all eight axiom audits passed; promoted to formalized.
