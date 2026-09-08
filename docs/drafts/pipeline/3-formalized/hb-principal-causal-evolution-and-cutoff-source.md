# HB principal causal evolution and complete cutoff source transform

- **Stage:** 3-formalized; targeted leaf and new-declaration audits passed.
- **Type:** THEOREM (Lean).
- **RH status:** open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and left-QNM pairing → independent Hawking-clock extinction → RH.

## Exact advance

For each of the three literal principal exponents, one frequency-independent
causal evolution is constructed from the native delayed source. Existence,
uniqueness among continuous integral solutions, odd spatial reflection,
exponential norm control, continuous first time derivative and zero Cauchy
data are proved. The evolution gains an exact spatial inverse-frequency
factor. Its Bochner transform converges in a nonempty common right half-plane.

All three original cutoff commutators are retained as bounded maps to the
original joint spatial Hilbert space. Their sum with the native square
remainder is one continuous causal source, and its norm-convergent Bochner
transform is identified with the sum of the native transform and the three
constructed response transforms.

The remaining equality with the existing endpoint Green response is **not**
assumed or proved by this construction. Consequently the assembled transform
is not yet identified with `cuspResidualVector`.

## Dependency-closed argument

Write `alpha=2*pi`, `Lambda=<D>` for the corpus Fourier frequency
`sqrt(1+xi^2)`, and `h(t)=1-tanh(t)^2`. The physical sine kernel is

`D(tau)=alpha^(-1) sin(alpha*tau*Lambda)/Lambda`.

The time rescaling retains unit spatial wave speed under the corpus Fourier
convention. For principal exponent k, the bounded complex multiplication
operator is

`W_k(t)=alpha^2+k*(k-1)*h(t)`.

Here `0<=h<=1`, and h is even on the whole real line. The added constant is
the mass of the rescaled free generator; the target original equation is
`U_tt-U_xx-k*(k-1)*h*U=F`. The second-order differential equation itself is
an outstanding identification below.

The odd extension E maps the original negative-ray L² space continuously to
whole-line L². It retains the original function almost everywhere on the
negative ray, satisfies reflection(Ef)=-Ef and has norm at most `2||f||`.
Restriction composed with E is exactly the identity.

Let `R(tau)` be the already proved native radial source vector and J_i the
literal principal amplitude. Set `F_i(tau)=J_i E(R(tau))`. These actual
forcings are continuous, zero for `tau<=0`, integrable in time, and have their
exact native source Bochner transform for `Re(w)>-2`.

The free forced term `g_i(tau)=integral_0^tau D(tau-sigma)F_i(sigma)` is
continuous and globally bounded by

`B_i=alpha^(-1) integral_0^infinity ||F_i(sigma)|| d sigma`.

The strongly continuous Volterra kernel `D(tau-sigma)W_i` has norm at most
`M_i=alpha^(-1)||W_i||`. The corpus factorial iteration therefore constructs
one actual solution

`U_i(tau)=integral_0^tau D(tau-sigma)(F_i(sigma)+W_i U_i(sigma)) d sigma`,

with `||U_i(tau)||<=B_i exp(M_i |tau|)`. It is the unique continuous solution
of this integral equation. Iteration retains negative-time support. Evenness
of the Fourier sine symbol and W_i makes reflection commute with the kernel;
the exact odd constraint survives every iterate and its norm limit.

Rescaling the proved Klein–Gordon Duhamel derivative gives

`U_i'(tau)=integral_0^tau cos(alpha*(tau-sigma)*Lambda)`
`                          (F_i(sigma)+W_i U_i(sigma)) d sigma`.

This derivative is continuous, and both U_i(0) and U_i'(0) vanish. Pulling the
bounded inverse-frequency operator through the integral also gives

`U_i(tau)=Lambda^(-1)[alpha^(-1) integral_0^tau`
`  sin(alpha*(tau-sigma)*Lambda)(F_i(sigma)+W_i U_i(sigma)) d sigma]`.

Thus the required spatial regularity starts with an actual operator-range
identity, not a supplied regularity premise. A boundary trace still requires
its own theorem.

For `Re(w)>M_i`, the response bound supplies an integrable exponential majorant
for `exp(-w*tau) U_i(tau)`. The resulting Bochner transform is also odd.
Define the exact cutoff map

`L_i u = [restriction_(t<0)(h(t) u(t))] tensor cutoffCommutator(k_i)`.

Both restriction and bounded multiplication are continuous linear maps, and
the original angular commutator is an admitted L² vector. Consequently L_i
is a bounded map to the original joint spatial space. With
`H=1+sum_i M_i`, the full assembled source

`S(tau)=timeCuspMainVector(tau)+sum_i L_i U_i(tau)`

is continuous, causal and Bochner-transform integrable for `Re(w)>H`, and

`Laplace(S)(w)=cuspMainLaplaceVector(w)+sum_i L_i Laplace(U_i)(w)`.

Every interchange follows from proved norm integrability and continuity of
the exact linear maps. No frequency-dependent time family is introduced.

## Canonical Lean audit

Fifteen canonical leaves, eighty public theorems, 1019 source lines. The eight
reusable leaves belong to `GaloisForLFunctions.HTGeometry`; the seven route
leaves belong to `GaloisForLFunctions.RHTower`. Route declarations use
namespace `RHTower.D4BMJointSource`.

| New leaf | Public theorems |
|---|---:|
| `VolterraCausalConstraints` | 4 |
| `L2SpatialReflectionMultipliers` | 5 |
| `L2NegativeHalfLineExtension` | 6 |
| `L2NegativeHalfLineRestriction` | 3 |
| `UnitWaveSine` | 7 |
| `UnitWaveDuhamel` | 4 |
| `UnitWavePotentialKernel` | 4 |
| `UnitWaveDuhamelDerivative` | 3 |
| `ThetaCuspHawkingBMJointSourcePrincipalWavePotential` | 8 |
| `ThetaCuspHawkingBMJointSourcePrincipalTimeForcing` | 8 |
| `ThetaCuspHawkingBMJointSourcePrincipalTimeResponse` | 8 |
| `ThetaCuspHawkingBMJointSourcePrincipalTimeLaplace` | 2 |
| `ThetaCuspHawkingBMJointSourcePrincipalTimeRegularity` | 6 |
| `ThetaCuspHawkingBMJointSourcePrincipalCutoffTime` | 6 |
| `ThetaCuspHawkingBMJointSourceCausalCuspSource` | 6 |

Every new canonical leaf passed its own `lake build <module>` audit in an
isolated package backed by the existing dependency caches. Each command
compiled exactly its requested leaf, with no warnings. No existing dependency
or umbrella was built. All fifteen installed source files and thirty
`.olean`/`.ilean` artifacts match the audited copies. Each leaf is imported
exactly once by its area umbrella.

A scratch `lake env lean` audit checked all eighty new public theorem axioms,
and only those theorems. Every result contains exactly `propext`,
`Classical.choice`, and `Quot.sound`. There are no added axioms or computational
certificates. Scoped source, artifact, whitespace and wiring checks passed.
No numerical experiment was run.

Generated source indexes were refreshed and their freshness check passed.
Repository-wide `scripts/formal_tools.py lint --check-generated` still fails
on the unrelated, unwired module
`GaloisForLFunctions.HTGeometry.BistochasticMixingMajorization`. It also
reports 141 existing large-file warnings. None of these fifteen new leaves is
flagged. Concurrent source files and their wiring were preserved.
Owned scratch and isolated audit directories were removed; no owned Lean or
Lake process remained after verification.

## Remaining hard obligations

Prove the original second-order radial equation and endpoint trace for this
constructed evolution, then identify its Laplace transform, on the negative
ray, with `principalDifference` at the actual onset transform. Only that
identity can turn the assembled transform above into `cuspResidualVector`.
Oddness of an L² class alone does not establish its boundary trace.

Convolve the complete source with the original joint causal response with
justified vector integral interchange. Continue the resulting response to
the physical left-QNM pairing and evaluate the retained spin-two/AIME source.
Independent Hawking-clock extinction remains unproved. The Volterra bound
permits exponential growth and supplies no Xi-zero selection or RH proof.
The source chamber `Re(w)>-2` does not continue the response inverse there.

The next analytic construction is the time derivative of the native L²
forcing. If its actual derivative is admitted and continuous, then
`G_i=F_i+W_i U_i` is C¹. Integration by parts with the bounded
`A^(-2)cos(A*tau)`, where `A=alpha*Lambda`, gives the precise next target

`U_i(tau)=A^(-2)[G_i(tau)-cos(A*tau)G_i(0)`
`  - integral_0^tau cos(A*(tau-sigma)) G_i'(sigma) d sigma]`.

This would gain two spatial inverse-frequency factors and expose the original
second-order equation. This displayed upgrade is a paper derivation awaiting
its actual-source derivative and Lean closure; it is not part of the audited
theorem claims above.
