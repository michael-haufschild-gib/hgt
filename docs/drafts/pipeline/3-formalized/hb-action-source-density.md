# Volume and index raising in the actual cubic Einstein source

Status: formalized in Lean.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact result

Let `g(t)=G+tH+t²K+t³L` be the complete corrected metric path and `E(t)` its original covariant cosmological Einstein residual. Set

```text
v(t) = exp(log(det(g(t))/det(G))/2)
W(t) = v(t) g(t)^(-1) M (g(t)^(-1))^T
P(t) = sum_ij W(t)_ij E(t)_ij.
```

`M` is a fixed covariant testing tensor. The transpose retains the correct two-index contraction without imposing symmetry on arbitrary algebraic jets. For symmetric metrics this is the usual two-index raising formula. The volume branch has `v(0)=1`, is complex C³ near zero, and its square is the determinant ratio wherever that ratio is nonzero.

Write `D(G,H)` for the derivative of the determinant, evaluated by its full permutation-and-column-replacement formula. The verified first variation is

```text
W0 = G^(-1) M (G^(-1))^T
W1 = D(G,H)/(2 det(G)) W0
     -(G^(-1) H G^(-1)) M (G^(-1))^T
     -G^(-1) M (G^(-1) H G^(-1))^T.
```

On a vacuum background and a linearized solution, `E(0)=E'(0)=0`. The actual third-derivative product rule gives

```text
P'''(0)/6 = sum_ij [W0_ij E3_ij + W1_ij E2_ij]
E2 = L K + B(H,H)/2
E3 = L L + B(H,K) + C(H,H,H)/6.
```

Here `L` in operator position denotes the original cosmological linearization; the correction tensor named `L` is the cubic field coefficient. Every term is obtained from the literal rational Einstein contraction, not assigned source coefficients.

The first-variation premises are discharged for both literal fundamental BM branches with arbitrary independent scalar and vector amplitudes. Corrections may be any C² fields at the exterior point. The affine specialization sets both corrections to zero and has no field-equation or regularity hypotheses.

If every component of `E2` vanishes, then `P'''(0)/6=sum_ij W0_ij E3_ij`. This is a proved bulk invariance under the changing volume and index raising. It does not permit replacing the complete second-order equation by cancellation of selected angular components.

## Proof mechanism

Differentiate the finite determinant expansion column by column. Differentiate the local logarithm and exponential at determinant ratio one. Differentiate each inverse metric with the existing exact inverse-derivative theorem, retaining matrix order. Apply the third-order Leibniz formula to each source component and commute the derivative through the finite contraction. The vacuum and actual linearized Einstein equations remove precisely the zeroth- and first-source terms. The existing complete cubic metric-path theorem evaluates both surviving source derivatives.

## Formal declarations and audit

- `HTGeometry.MetricPathDensity` in `CoordinateMetricPathDensity`: determinant derivative, relative volume, raised testing tensor, and exact first variation.
- `HTGeometry.ComplexCoordinateMetricTwoJet.CubicSource` in `CoordinateEinsteinPairedCubicSource`: complete paired cubic coefficient and its full-quadratic-cancellation specialization.
- `RHTower.D4BMActionSource` in `ThetaCuspHawkingBMActionCubicCoefficient`: equality with actual field jets and both literal fundamental branches.

Three leaves, 335 lines, 23 new public declarations. Foreground scratch checks and all three individual final `lake build <module>` audits passed. Final builds had no warnings. The new-only axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. All three modules are wired into their owning umbrellas; no umbrella build was run.

Installed source, olean, and ilean hashes match all nine audited artifacts. Generated indexes were refreshed; `scripts/formal_tools.py lint --check-generated` and `git diff --check` passed. Lint retained the existing large-file warnings. No mathematical computations were run.

## Remaining hardest obligation

This identifies the metric-dependent **bulk contraction** needed in the proposed variational argument. It does not prove that contraction is the complete action variation, that the augmented third variation is cyclic, that the physical retarded/advanced maps induce the desired left-QNM pairing, or that its boundary current vanishes. No mixed `++-` coefficient extraction from this new weighted contraction is asserted. Fixed Hawking-clock extinction and RH remain unproved.

The calculation rules out using the varying bulk weight as an independent cancellation term after the full quadratic equation is solved: its extra term is then exactly zero. The [mixed-coefficient extension](hb-mixed-action-source-coefficient.md) supplies the subsequent actual mode derivative. The retained action boundary contribution remains open.
