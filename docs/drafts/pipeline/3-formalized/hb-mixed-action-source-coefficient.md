# Complete mixed coefficient of the weighted Einstein source

Status: formalized in Lean. Physical action boundary identity and extinction remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact result

The [weighted cubic source identity](hb-action-source-density.md) now has an actual mixed-amplitude derivative. Use two independent parameters: the metric perturbation parameter `ε` and the mode-amplitude parameter `z`. Neither is the spectral coordinate. Set

```text
H(z) = H0 + z H1 + z² H2 + z³ H3
g(ε,z) = g0 + ε H(z) + ε² K(z) + ε³ L(z),
```

where `K(z)` and `L(z)` retain all four polynomial slots. Let `E(ε,z)` be the original covariant cosmological Einstein residual, and use its actual relative-volume-weighted, raised-test contraction

```text
v(ε,z) = exp(log(det(g(ε,z))/det(g0))/2)
W(ε,z) = v(ε,z) g(ε,z)^(-1) M (g(ε,z)^(-1))^T
P(ε,z) = sum_ij W(ε,z)_ij E(ε,z)_ij
P_ppm = d/dz [∂ε³ P(0,z)/6] at z=0.
```

`M` is a fixed covariant testing tensor. The pairing is complex bilinear. Write `p=H0`, `m=H1`, `k_pp=K0`, `k_pm=K1`, and `l_ppm=L1`. With `Lop` denoting the original linearized cosmological Einstein operator, and `B,C` its second and third variations, the proved identity is

```text
E2_pp  = Lop k_pp + B(p,p)/2
E2_pm  = Lop k_pm + B(p,m)
E3_ppm = Lop l_ppm + B(p,k_pm) + B(m,k_pp) + C(p,p,m)/2

P_ppm = <W0,E3_ppm> + <W1(m),E2_pp> + <W1(p),E2_pm>.
```

Here `<A,E>=sum_ij A_ij E_ij`, `W0=g0^(-1) M (g0^(-1))^T`, and `W1(h)` is the exact first variation of the volume factor and both raised indices. The general theorem requires C² spatial fields and the full linearized equation for each `H` slot. Higher correction slots disappear by differentiating the original family; they were not omitted from its definition.

For the `++−` coefficient, vanishing of the complete `++` and `+−` quadratic grades suffices to remove both varying-weight terms:

```text
E2_pp = 0 and E2_pm = 0  ⇒  P_ppm = <W0,E3_ppm>.
```

Each equality here requires all 16 tensor components. The `−−` quadratic grade and other cubic slots remain unrestricted apart from regularity. These are mode grades, distinct from scalar/vector SS, SV, and VV sectors. The theorem does not assert that these two vanishing conditions are necessary for cancellation against a particular test. It retains `Lop l_ppm`; no unproved cokernel identity removes that term.

## Literal source specialization

The capstone substitutes the actual plus and minus fundamental BM fields, with arbitrary independent scalar and vector amplitudes and the same arbitrary complex spectral parameter. Their existing full linearized equations discharge every linearized-equation premise. Corrections remain arbitrary C² fields.

Setting all quadratic and cubic corrections to zero gives a further theorem with no field-equation or regularity hypotheses:

```text
P_ppm = <W0,C(p,p,m)/2>
        + <W1(m),B(p,p)/2>
        + <W1(p),B(p,m)>.
```

Thus the direct third Einstein variation alone is not the weighted affine mixed coefficient. In a corrected family solving the two relevant complete quadratic equations, the extra weight terms instead vanish exactly.

## Proof and audit

First prove linearity of `W1` in the perturbation using the full determinant slope and both inverse variations. Differentiate actual field jets through the independent polynomial mode path. Differentiate the full quadratic residual, retaining `Lop k_pm` and using symmetry of `B` to combine the two half-terms. Establish differentiability of the complete cubic source. Apply the product rule to the already-proved weighted cubic coefficient and then use the existing actual mixed cubic-source identity. Finally substitute the literal BM branches.

Four new leaves, 359 lines, 14 public declarations:

- `HTGeometry.CoordinateMetricTestModeVariation`: exact mode derivative of the testing-weight variation.
- `RHTower.ThetaCuspHawkingBMMixedActionModeDerivatives`: actual field-jet and quadratic/cubic source derivatives.
- `RHTower.ThetaCuspHawkingBMMixedActionCubicCoefficient`: complete mixed coefficient and quadratic-grade cancellation.
- `RHTower.ThetaCuspHawkingBMLiteralMixedActionCoefficient`: literal corrected and affine BM specializations.

All four foreground scratch checks and all four individual final `lake build <module>` audits passed. Final builds had no warnings. New-only `#print axioms` checks for all 14 public declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The four imports are wired into their owning umbrellas; no umbrella build was run. Installed source, olean, and ilean hashes match all 12 audited artifacts. No mathematical computations were run.

Generated indexes were refreshed. `scripts/formal_tools.py lint --check-generated` and `git diff --check` passed; lint retains existing large-file warnings. The frontier map's hash is unchanged from the start of this work. No Lean or Lake process remained after the audit.

## Remaining hardest obligation

This is a pointwise bulk coefficient identity. It does not yet supply the action variation formula including its boundary current, integration against background volume, cyclicity of the completed action, the physical retarded/advanced adjoint, or left-QNM admission. The complete radiative pairing `2 Ω(B(p,p)/2,B(m,m)/2)` has not been proved to vanish at the fixed Hawking clock. RH remains unproved.

The direct next obligation is to derive the boundary current of the actual Einstein action and evaluate the completed physical pairing with its horizon and AdS endpoint terms retained. The bulk calculation identifies what survives for that evaluation; it does not establish extinction.
