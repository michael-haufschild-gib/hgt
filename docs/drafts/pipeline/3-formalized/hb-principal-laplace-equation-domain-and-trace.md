# HB principal causal transform: original radial equation, domain and endpoint

- **Stage:** formalized in Lean 4.
- **Type:** THEOREM (Lean).
- **RH goal:** open.
- **Frontier map:** read-only; not edited for this result.

## Exact result

Every actual principal causal Bochner transform `principalTimeLaplace` solves
its original radial frequency equation throughout its already established
half-plane `Re(w)>principalResponseGrowth(q,i)`:

```
w^2 * Uhat - Delta Uhat = Fhat + V Uhat,
V(x) = k*(k-1)*horizonCoordinate(x).
```

The equality holds in tempered distributions of the original spatial L²
classes. The forcing transform `Fhat` is exactly the actual principal
amplitude times the odd extension of `radialSourceLaplaceVector`, whose
negative-ray representative is

```
reducedCoefficient(physicalRate,w,a,onsetTransform(2*physicalRate,w),x).
```

Consequently `Uhat` belongs to spatial Sobolev order two. Its continuous
representative `principalLaplaceProfile` is a representative of that actual
L² class, is pointwise odd, has value zero at the original endpoint, and
tends to zero there from the negative ray. Its original negative-ray weak
frequency equation retains the literal source and physical onset transform.
No stronger half-plane or assumed decay of the response acceleration is used.

## Dependency-closed proof

For a fixed spatial Schwartz test `psi`, evaluation of the L² distribution
at `psi` is a bounded complex linear functional `P`. This follows by composing
the existing L²-to-tempered-distribution map with pointwise evaluation.
Bounded linear maps commute with the norm-convergent Bochner Laplace integral.

Let `U(t)` be the actual principal response, `F(t)` the actual forcing and
`P_D` the functional associated with `Delta psi`. Set
`Q=P_D+P compose V`. The already proved original wave equation gives

```
f(t) = P U(t),    v(t) = P U'(t),
g(t) = P U''(t) = Q U(t) + P F(t),
f' = v,          v' = g.
```

All time derivatives here are derived from the actual L² derivative
identities. The native horizon theorem, with decay parameter zero, gives
`||F(t)|| <= B` globally. The existing Volterra estimate gives
`||U(t)|| <= A exp(r t)` for `t>=0`, with `A,r>=0`. Hence

```
|f(t)| <= ||P|| A exp(r t),
|g(t)| <= (||Q|| A + ||P|| B) exp(r t).
```

The mean value inequality on `[0,t]` now bounds the actual velocity:

```
|v(t)| <= (|v(0)| + C t) exp(r t).
```

Exponential integrability and the degree-one Gaussian/Gamma integral estimate
show that all three weighted functions `exp(-w t)f(t)`,
`exp(-w t)v(t)` and `exp(-w t)g(t)` are integrable whenever `Re(w)>r`.
There is no loss in this strict half-plane.

For any differentiable scalar function `h` whose weighted function and
weighted derivative are integrable,

```
(exp(-w t)h(t))' = exp(-w t)h'(t) - w exp(-w t)h(t).
```

Its right side is integrable. The improper-integral theorem stating that an
integrable function with integrable derivative tends to zero supplies the
boundary limit at infinity. The half-line fundamental theorem of calculus
therefore proves

```
Laplace(h') = w Laplace(h) - h(0).
```

Apply it first to `f` and then to `v`, retaining both initial terms:

```
Laplace(g) = w^2 Laplace(f) - w f(0) - v(0).
```

Only now use the proved physical zero Cauchy data. Substitute the original
paired wave equation, use integrability to split the two terms, and commute
`Q` and `P` with their Bochner integrals. This gives the transformed original
equation against every Schwartz test, hence the claimed distributional
equality. The existing forcing-transform theorem supplies the literal
physical onset factor.

Rearrange this equality to obtain the actual L² preimage

```
Delta Uhat = w^2 Uhat - Fhat - V Uhat.
```

Both `Uhat` and its Laplacian therefore have Sobolev order zero. The corpus's
`euclidean_sobolev_gain_two` theorem gives order two. The previously proved
Sobolev continuous-representative theorem and the actual transformed
reflection identity then give pointwise oddness and zero endpoint trace.
This derives the trace in the transformed domain itself; it does not
interchange a time integral with an endpoint limit.

Finally, restrict the distributional equation to Schwartz tests supported
inside the negative ray. Test derivatives retain that support. Substitute
the actual almost-everywhere forcing transform and the continuous profile's
almost-everywhere equality with `Uhat`. This proves the original negative-ray
weak frequency equation, with the original L² admission retained.

## Lean audit

Seven canonical leaves, 24 public theorems, 466 source lines:

| Module suffix | Public theorems |
|---|---:|
| `HTGeometry.ScalarLaplaceDerivative` | 3 |
| `HTGeometry.ScalarLaplaceSecondOrder` | 2 |
| `HTGeometry.L2SchwartzProbe` | 3 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceProbe` | 3 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceEquation` | 3 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceTrace` | 7 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceRadial` | 3 |

Each final canonical leaf passed its own `lake build <module>` audit in an
isolated package backed by existing caches. Every command freshly compiled
exactly the requested new leaf, without warnings. Fourteen installed
`.olean`/`.ilean` artifacts match the audited copies. Each leaf is wired once
into its area umbrella. No existing dependency, umbrella or full project was
built during this result.

A scratch `lake env lean` audit checked exactly the 24 new public theorems;
each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
No old theorem's axioms were rechecked. Source-copy, artifact, whitespace,
unique-import and forbidden-declaration checks passed. No proof hole, added
axiom or computational certificate was used. No numerical experiment was run.

Generated indexes were refreshed. Repository-wide
`scripts/formal_tools.py lint --check-generated` reported 141 existing
large-file warnings and no new-leaf warning or error. Its generated-freshness
check passed, but the global gate failed on nine unrelated concurrently added
modules missing umbrella imports: `InwardPlaneDisplacementReturn`,
`InwardPlanePrescribedStream`, and the seven `Polyatomic` leaves `Beta`,
`Conservation`, `CorpusApplications`, `HilbertGeometry`, `Kinematics`,
`Laplace` and `PauliSelection`. Those unrelated modules were not modified.

The frontier map was not edited. Owned scratch and isolated audit directories
were removed after validation; no owned Lean or Lake process remained.
Concurrent work was preserved.

## Remaining hard obligation

On a common right half-plane, compare this transformed profile with
`principalDifference` at `T=onsetTransform(2*physicalRate,w)`.
The latter already has the matching classical radial equation and original
negative-ray L² admission under `PrincipalChamber`. Its endpoint conditions
must be transported to the same coordinate and the uniqueness comparison
proved. A weak equation and zero trace alone are not a completed comparison;
any regularity or horizon condition used by a uniqueness theorem must be
derived for these actual objects.

Only that equality identifies the assembled complete causal source transform
with `cuspResidualVector`. Response continuation to the physical QNM boundary,
adjoint/advanced left-QNM identification, evaluation of the retained
spin-two/AIME source and independent Hawking-clock extinction remain open.
This result is not an RH proof or a Xi-zero selection theorem.
