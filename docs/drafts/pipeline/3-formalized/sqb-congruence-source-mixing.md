# Exact averaging and currents of the original Maass congruence source

Status: dependency-closed structural proof, formalized and audited. The global
quarter comparison and the Xi occurrence theorem remain unproved. This is not
an RH proof.

## Original source and operator

Fix an actual Maass cusp eigenform of level Gamma(N+1), with eigenvalue lambda.
Let G be its literal finite deck group, n its cardinality, and F_q its complete
family of original translated component fields. The intrinsic source definition
supplies the common Maass equation, C² regularity, and every integral cusp
condition. No spectral gap, occurrence, or nonzero-average premise is added.

On the actual finite Euclidean space define U_g v(q)=v(qg) and
P v=n⁻¹ sum_g U_g v. Coordinate permutation proves U_g unitary; the complete
group sum proves P v is the constant vector with value n⁻¹ sum_q v(q).
The corpus Reynolds identity and its inner-product identity give

```
P²=P,
Pv=v iff every U_g fixes v,
||Pv||² + ||v-Pv||² = ||v||²,
(2n)⁻¹ sum_g ||U_g v-v||² = ||v-Pv||².
```

The original pullback law is exactly F(Az)=U_[A] F(z). Thus this operator acts
on the actual source; its coordinates are not substituted test functions.
Put m=n⁻¹ sum_q F_q and a_q=F_q-m. Then

```
sum_q a_q=0,
D=sum_q |F_q|²=n|m|²+sum_q |a_q|²,
(2n)⁻¹ sum_g ||U_g F-F||²=sum_q |a_q|².
```

Finite differentiation shows that m and every a_q retain the original Maass
equation. Finite limits preserve every integral cusp condition. The mean is
invariant under the full integral modular group, and every remainder retains
the original congruence invariance. The result explicitly distinguishes m=0
from a nonzero full-modular cusp eigenform of the same eigenvalue. It does not
assert that the mean is nonzero.

## Complete current identity

For a direction v write d for the actual directional derivative and
J(X,Y)=X dY-Y dX. Both sum_q a_q and sum_q da_q vanish. Set
H_q=m da_q-(dm)a_q and K_qr=a_q da_r-a_r da_q. Direct expansion gives

```
J(F_q,F_r)=H_r-H_q+K_qr.
```

Every row and column sum of K vanishes, so the full cross sum between H_r-H_q
and K_qr is zero. Also sum_q H_q=0, whence
sum_qr |H_r-H_q|²=2n sum_q |H_q|². Therefore the original pair energy is exactly

```
pairEnergy_v = (1/2) sum_qr |J(a_q,a_r)|² + n sum_q |J(m,a_q)|².
```

For the Hermitian pairing the two linear cross sums vanish separately:

```
sum_q dF_q conjugate(F_q)
  = n (dm) conjugate(m) + sum_q da_q conjugate(a_q).
```

Taking imaginary parts gives phase_v=n phaseMean_v+phaseCentered_v. The phase
contributions must add before squaring. Define

```
S_v = (1/2) sum_qr |J(a_q,a_r)|²
    + n sum_q |J(m,a_q)|²
    + (n phaseMean_v+phaseCentered_v)².
```

The existing original-source radial and curvature identities now yield

```
D * radialResidual_v = S_v,
R_e³ * curvatureWeight_e = S_x + S_y + e² * gradientDensity,
R_e² = D+e².
```

These are multiplied identities, with no division by a possibly zero source
amplitude. The mixed brackets give a nonnegative lower part of the complete
pair energy and regularized curvature numerator. The full regulator-gradient
term is retained.

The shared original equation also gives div J(m,a_q)=0: expand the divergence,
cancel the two mixed first-derivative products, and cancel m Delta(a_q)-a_q
Delta(m) using the common potential -lambda/y². Conservation does not establish
vanishing of periods on a quotient.

The common-zero locus is preserved exactly: all F_q vanish iff m and all a_q
vanish. If the mean is identically zero, a_q=F_q and every J(m,a_q)=0. The
centered currents then retain the full original family. No mass or nonzero
source is inferred from the averaging channel alone.

## Scope of the remaining comparison

The new operator and every term above are derived from the original source.
They do not compare finite group displacement with the full amplitude-normalized
integrated curvature at a uniform positive constant. In particular, the mixed
bracket lower bound supplies no positive contribution in the zero-average case.
The complete centered pair energy, combined phase square, and nodal residual
must still enter a source-derived core-plus-cusp comparison.

The Maass face still needs `totalOrbitCurvature >= amplitudeMass/8`. That would
supply the Selberg quarter bound through the existing mass identity. SQB's
transformed face separately needs independent occurrence of the full Xi
parameter in the constructed self-adjoint model, or another proved Xi-to-Maass
handoff. Neither missing statement is assumed or proved here.

## Corpus discovery and validation

Broad OR searches covered the following declaration metadata, without a
per-module cap. Counts are discovery coverage, not claims to have read every
proof.

| Search terms | Declarations | Modules |
| --- | ---: | ---: |
| congruence, mixing, entropy, Poincare, Hecke | 4,282 | 825 |
| Reynolds, averaging, barycenter, variance, projection | 6,241 | 1,641 |
| isoperimetric, Cheeger, holonomy, nodal, winding, uncertainty | 2,954 | 509 |
| expander, Kazhdan, mixing, Poincare, congruence | 3,188 | 594 |

The actual congruence, derivative, cusp, Reynolds, pair/phase and curvature
sources were inspected before construction. Further source inspection found
that the coframe completion dichotomy concerns continuity of an augmentation,
the L² Fourier uniqueness theorem requires bounded support, and the finite
torus Poincare proof uses its integer-frequency gap. None of those inspected
statements directly supplies the missing modular comparison.

| Lean module | Public declarations | Sole-target final build |
| --- | ---: | ---: |
| `HTGeometry.FiniteRegularReynolds` | 11 | 3.7 seconds |
| `RHTower.SelbergMaassCongruenceAverage` | 21 | 3.5 seconds |
| `RHTower.SelbergMaassAverageCurrents` | 26 | 4.1 seconds |

All three complete scratch proofs and tree source checks passed with
`lake env lean`. Each no-build preflight listed only its intended stale target;
each final `lake build <module>` rebuilt exactly that one module. The reported
dependency job totals were cached dependency graphs, not full builds.

All 58 public declarations passed a separate `/tmp` axiom audit. The complete
dependency union contains only `propext`, `Classical.choice`, and `Quot.sound`.
All 58 API rows exist, every new module is wired exactly once, and repository
formal lint passed with existing large-file warnings. No numerical results,
added axioms, proof placeholders, or full umbrella builds were used.

Audit files: `/tmp/sqb13_{regular,average,currents}_{preflight,build}.log`,
`/tmp/sqb13_axioms.lean`, `/tmp/sqb13_axioms.log`, `/tmp/sqb13_api_names.txt`,
`/tmp/sqb13_index.log`, and `/tmp/sqb13_lint.log`.

The frontier map was treated as read-only by this work. Concurrent changes to
that shared file were left untouched.
