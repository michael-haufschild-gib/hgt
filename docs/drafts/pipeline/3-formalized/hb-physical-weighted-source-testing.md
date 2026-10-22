# HB: bounded physical testing of the complete original source

Status: formalized in four audited leaves and 15 new public theorems.
The construction admits the original physical source integral as a bounded
Hilbert-space functional, preserves every source channel, and proves source
meromorphy in the required stronger norm. RH remains open.

## Domain and exact weight cancellation

Let `E_r` be the complete original angular scalar field at the physical
parameter `(r-1)/2`, for any Xi zero copy `r`. Let `mu` be the original
modular fundamental-domain measure and `y` its height coordinate. The
existing `SelbergScatteringCuspNorm.scalarSource_native_cusp_not_integrable`
theorem proves that `E_r` has divergent native squared norm. This existing
classification is used to identify the domain issue; it is not re-audited
or reproved here.

The physical principal term is `Lambda(r-1) y^(1-r/2)`. Dividing the full
field by height gives principal term `Lambda(r-1) y^(-r/2)`. Since
`0 < Re r < 1`, its norm is bounded for `y>3`. The existing weighted bound
controls the complete Fourier tail there, and the compact quotient core
supplies the remaining bound. The original quotient has finite measure,
so `d_r=E_r/y` belongs to its angular L2 space.

For every fixed complex exponent `v`, `y^v S_q` also belongs to this L2
space: the native square residual has a global weighted bound on the
fundamental domain. Every differential cutoff `K_k` retains L2 admission
after multiplication by `y^v`, since its high cusp part is zero and its
compact part is continuous. These statements hold for every Xi source;
no right-half restriction on the source is needed here.

Define `b_r=conj(d_r)` as an angular L2 vector and the complex-linear
functional

```text
L_r(g) = <b_r,g> = integral d_r(z) g(z) dmu(z),
|L_r(g)| <= ||b_r||_2 ||g||_2.
```

Then exact cancellation gives

```text
L_r(y S_q) = integral E_r S_q dmu,
L_r(y K_k) = scalarCutoffBoundaryValue((r-1)/2,k).
```

The bilinear physical integral, original measure, complete Fourier field,
and full cutoff boundary-and-bulk value are all retained. The conjugation
in `b_r` implements that bilinear integral through the Hilbert convention;
it does not assert a causal time reversal.

## Complete joint source and radial projection

Write the original continued source, with its original radial measure
`nu`, as

```text
F_q(w;t,z) = A_q(w;t) S_q(z)
            + sum_(i:Fin 3) B_qi(w;t) K_pi(z).
```

All radial coefficients, principal exponents and source parameters are
those of `continuedCuspResidualForcing`. For nonreal `w` with
`|Re w|<2`, every radial coefficient is admitted in L2(nu). The complete
height-weighted source `y F_q(w)` is therefore admitted in L2(nu x mu),
and its actual L2 class equals the sum of the four separated products.
The fixed weighted angular vectors and the existing radial norm-valued
continuations prove meromorphy of this class in the stronger norm
`||y F_q(w)||_2` throughout that nonreal band.

For a target Xi copy `r`, tensor insertion

```text
I_r(h) = h tensor b_r
```

is bounded. Define `P_r=I_r*`, its Hilbert adjoint. The product inner-product
identity proves, for every radial `h` and angular `g`,

```text
P_r(h tensor g) = L_r(g) h.
```

Apply this identity to the complete four-channel source and use the exact
angular integral identities above. The result is

```text
physicalJointProjection r (weightedCuspResidualL2 q branch a w)
  = continuedAngularSourceL2 q branch (physicalAngularParameter r) a w.
```

This identifies one fixed bounded operator with the original complete
physical angular source integral, for arbitrary source and target Xi
copies. It strengthens source admission and supplies the bounded testing
map; the earlier radial projection meromorphy theorem already existed.

## Lean and verification

All new leaves use prefix `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawking`:

| Suffix | Content | Public theorems |
| --- | --- | --- |
| `BMPhysicalWeightedAngularData` | Full physical dual and all weighted channel admissions | 3 |
| `BMPhysicalAngularFunctional` | Bounded original bilinear integral and exact channel values | 7 |
| `BMWeightedJointSource` | Actual weighted source class, complete assembly and norm meromorphy | 3 |
| `BMPhysicalJointProjection` | Bounded tensor-adjoint projection and original source identity | 2 |

The four leaves contain 312 lines and 15 public theorems. All four scratch
`lake env lean` checks and four individual canonical `lake build <module>`
audits passed without warnings. Canonical audits reused existing dependency
artifacts in a private cache workspace and built only the new leaves.
Exactly the 15 new public theorem axiom probes returned only `propext`,
`Classical.choice` and `Quot.sound`. Four sources and eight olean/ilean
artifacts were installed with byte verification, and all four leaves were
wired into the umbrella. No numerical experiment, full build or umbrella
build was run.

All twelve installed source/artifact hashes, four unique umbrella imports,
source whitespace and proof-card links were verified. One index refresh
completed. The repository-wide static `lint --check-generated` returned
exit 1 because four separately added HTGeometry modules were unreachable
from their umbrella: `FokasLenellsRawTwistEndpoints`,
`FokasLenellsRawTwistKernels`, `FokasLenellsRawTwistPrimitives`, and
`FokasLenellsRawTwistScattering`. No new HB leaf was reported unreachable
or had proof debt. The global static gate therefore did not pass; the
four individual Lean audits and all new axiom checks above did pass.

## Remaining physical obligation

The adjoint constructed here is the adjoint of tensor insertion. A physical
advanced/adjoint resonance must still be derived from the original causal
operator and its continued boundary conditions. Source testing in a
stronger norm does not prove that the causal response belongs to a space
where that test is valid. The next required proof must construct the
outgoing joint inverse with those mapping properties, prove its original
causal overlap, and identify its residue on the complete source. Pole
survival, complete source nonvanishing, independent Hawking-clock
extinction and RH remain open.
