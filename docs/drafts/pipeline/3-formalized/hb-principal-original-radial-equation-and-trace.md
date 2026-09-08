# HB principal causal response: original radial equation and endpoint trace

- **Stage:** formalized in Lean 4.
- **Type:** THEOREM (Lean).
- **RH goal:** open.
- **Frontier map:** read-only; not edited for this result.

## Exact result

For every actual principal channel, at every physical time, the constructed
causal response belongs to spatial Sobolev order two. It has a unique
continuous representative `principalTimeProfile` of its original L² class.
That representative is odd, equals zero at the original endpoint, and tends
to zero as the spatial coordinate approaches zero from the negative ray.

Let `U` denote the actual whole-line L² response, `u` its continuous spatial
representative, `F` the original odd-extended forcing, and
`V(x)=k*(k-1)*horizonCoordinate(x)`. The proved distributional equation is

```
U''(tau) - d_x^2 U(tau) = F(tau) + V U(tau).
```

The double prime on `U` is the proved second time derivative in the original
L² norm. On the negative ray, every Schwartz test `psi` whose closed support
lies inside that ray satisfies

```
integral psi(x) * U''(tau)(x) dx - integral psi''(x) * u(tau,x) dx
  = integral psi(x) * amplitude * timeReducedCoefficient(rate,a,tau,x) dx
    + integral psi(x) * V(x) * u(tau,x) dx.
```

All four integrals here are over `x<0`. The source retains the literal physical
rate, amplitude and delayed onset. No auxiliary free-mass term remains.
The actual response theorems derive their Sobolev domain and endpoint trace;
they assume no new regularity or boundary condition.

## Dependency-closed proof

The existing second time derivative theorem gives the exact spatial graph
identity `U=A^(-2)[F+W U-U'']`, with `A=2*pi*<D>` and
`W=(2*pi)^2+V`. To identify this graph with differentiation, first compare
the actual bounded L² multiplier and its tempered-distribution multiplier.
Pairing either with an arbitrary Schwartz test gives the same integral,
because the pointwise multiplier identity holds almost everywhere.
Compatibility of L² Fourier transform and inverse transform with tempered
distributions transports this identity through Fourier conjugation.

The literal symbol `kgFreqInv(x)` equals `(1+norm(x)^2)^(-1/2)`.
Thus `kgFreqInvOp` is exactly the Bessel potential of order minus one on
the original distribution class. Its square has order minus two, and the
actual inverse elliptic operator is `(2*pi)^(-2)` times that potential.
Bessel composition proves Sobolev order-two admission, with the original
L² preimage retained.

The corpus theorem `besselPotential_two_euclidean` identifies the order-two
Bessel potential with `T-(2*pi)^(-2)*Delta T`. Applying it to the inverse
elliptic image, and cancelling the exact Fourier normalization, gives

```
(2*pi)^2 * A^(-2) f - Delta(A^(-2) f) = f.
```

Insert the actual causal graph identity. Expand the bounded original
potential, cancel its auxiliary mass, and rearrange the remaining terms.
This proves the stated distributional wave equation with precisely the
original potential. Evaluating the distribution equation at a Schwartz test
moves the spatial Laplacian onto that test and gives the whole-line weak
identity. No pointwise derivative of an arbitrary L² representative occurs.

For the trace, the Sobolev Fourier-L¹ theorem supplies an integrable Fourier
representative whenever the Sobolev order is greater than one half.
Its inverse Fourier integral is continuous. Fourier inversion on tempered
distributions, integral duality and density of smooth compactly supported
tests show that this continuous function equals the original L² class almost
everywhere. This proves existence of the actual continuous representative,
rather than specifying a value on a null set.

The proved L² reflection identity then gives oddness almost everywhere.
Continuity on both sides and positivity of Lebesgue measure on open sets
upgrade it to pointwise oddness. At zero, `u(0)=-u(0)` forces `u(0)=0`.
Continuity gives the original negative-ray boundary limit. The same
almost-everywhere-to-pointwise argument proves uniqueness of the continuous
representative.

Finally, the support of each derivative of an interior Schwartz test stays
inside the original test support. Its pairings outside the negative ray
therefore vanish. Restrict the whole-line weak equation to that ray,
substitute the proved almost-everywhere literal forcing identity, and use
almost-everywhere equality of `u` and `U` in both spatial pairings. This is
the displayed original radial weak equation.

## Lean audit

Seven canonical leaves, 22 public theorems, 409 source lines:

| Module suffix | Public theorems |
|---|---:|
| `HTGeometry.L2BesselDistribution` | 6 |
| `HTGeometry.RealSobolevContinuousRepresentative` | 1 |
| `HTGeometry.UnitWaveDistributionEquation` | 2 |
| `HTGeometry.RealSobolevOddTrace` | 2 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalSpatialTrace` | 7 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalSpatialEquation` | 3 |
| `RHTower.ThetaCuspHawkingBMJointSourcePrincipalRadialWeakEquation` | 1 |

Each final canonical leaf passed its own `lake build <module>` audit in an
isolated package using the existing dependency caches. Every successful final
command freshly compiled exactly its requested leaf, without warnings.
Fourteen installed `.olean`/`.ilean` artifacts match the audited copies, and
each new leaf is wired once into its area umbrella. No full or umbrella
build was run. Eleven missing existing dependency oleans were restored in
sequence with `lake env lean`; their source proofs were unchanged.

A scratch `lake env lean` audit checked exactly the 22 new public theorems.
Every result depends only on `propext`, `Classical.choice`, and `Quot.sound`.
No old theorem's axioms were rechecked. No proof holes, added axioms or
computational certificates occur in the new sources. No numerical experiment
was run. Source-copy, artifact, whitespace and unique-import checks passed.

The repository-wide `scripts/formal_tools.py lint --check-generated` audit
reported 141 existing large-file warnings and no new-leaf warning or error.
The global gate did not pass: concurrently added modules
`MobiusDivisorSqrtGrowthObstruction`, `SquareRootAbelSqrtContinuation`,
`WeightedScalarMergeAmplitude`, `QuadraticResponseCorpusApplications` and
`QuadraticResponseHierarchy` lacked umbrella imports, and concurrent source
changes made two generated indexes stale. These unrelated modules were not
modified. Generated indexes were refreshed after that audit; continued
concurrent source changes left `LEAN_API.md` and `LEAN_OVERVIEW.md` stale
at the final freshness check.

The frontier map was not edited. Owned scratch and isolated audit directories
were removed after validation; no owned Lean or Lake process remained.
Concurrent work was preserved.

## Remaining hard obligation

The result concerns each actual time slice. It does not establish pointwise
second spatial differentiability or interchange a boundary trace with an
improper time integral. In particular, no Laplace–Green identification follows
merely from time-slice continuity and oddness.

Prove the Laplace transform's original radial domain, equation and endpoint
conditions with the differentiated time boundary terms controlled. Then
identify the negative-ray restriction of `principalTimeLaplace` with
`principalDifference` at the actual onset transform. That equality is still
required to identify the assembled complete causal source transform with
`cuspResidualVector`.

Response continuation to the physical left-QNM pairing, evaluation of the
retained spin-two/AIME source and independent Hawking-clock extinction remain
open. The present equation and trace do not supply Xi-zero selection or RH.
