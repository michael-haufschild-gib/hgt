# SQB entire-transform cusp occurrence

Status: original-source packet transport formalized; 30 public exports pass
individual module and axiom audits. RH remains unproved.

Full branch chain: original modular covariance → entire-transform operator with
lower bound −1 → independent Xi occurrence → critical-line classifier → RH.

The [operator construction](sqb-entire-native-operator.md) supplies the actual
domain and self-adjoint operator. This result supplies actual unit domain vectors
with vanishing residual at every transformed real cusp frequency, before selecting
a Xi zero. It also determines their exact defect at each full complex Xi target.
It does not prove that those defects vanish for all zeros.

## Exact source construction and proof

Use the original modular energy `A=1−Delta_H`, covariance `B=A⁻¹`, transformed
covariance `C=g(B)`, and `T=C⁻¹−2`. Here
`g(x)=1/(F(x⁻¹−1).re+2)` for x>0 and zero otherwise. The preceding construction
proves that C is positive, injective, and bounded with dense range, and that
`domain(T)=range(C)`, `T(Cu)=u−2Cu`.

The existing cusp construction supplies original unit domain vectors `u_n(tau)`
with `‖(A−a)u_n‖→0`, where `a=5/4+tau²>0`. The shift by one is retained.
Set `x=a⁻¹` and `c=g(x)>0`.

First, the original graph-inverse identity gives the exact relation

`(B−x)u = −x B(A−a)u`.

Boundedness of B therefore gives `‖(B−x)u_n‖→0`.

Second, g is differentiable at every positive x. This follows by restricting
the entire complex F to the real axis, composing with inversion, and using the
strictly positive denominator; the positive branch agrees with g on a whole
neighborhood of x. The function

`d(y)=dslope(g,x,y)`

is continuous on the compact spectrum of B. At x this is the derivative limit;
away from x it is the ordinary continuous quotient. Its exact identity is
`(y−x)d(y)=g(y)−g(x)`, including y=x. Functional-calculus multiplication yields

`(C−c)v = d(B)(B−x)v`.

Consequently

`‖(C−c)v‖ ≤ ‖d(B)‖ ‖(B−x)v‖`,

and `‖(C−c)u_n‖→0`. This requires no approximate-spectrum premise and no bound
on the vectors beyond what the original source already provides.

Because C is injective and each u_n is a unit vector, `C u_n≠0` for every n.
The reverse triangle inequality gives `‖C u_n‖→c>0`. Define

`v_n(tau)=C u_n(tau)/‖C u_n(tau)‖`.

These are explicit elements of the actual domain of T, with norm exactly one.
For `L=c⁻¹−2`, their complete normalized residual is

`‖(T−L)v_n‖ = ‖C u_n‖⁻¹ ‖u_n−(L+2)C u_n‖`.

The numerator is `−c⁻¹(C−c)u_n`; it tends to zero, while the denominator tends
to c>0. Thus `‖(T−L)v_n‖→0`. Entire square descent gives the exact target

`L = F(a−1).re = cosh(8*pi*tau)`.

All these source vectors and statements are defined for every real tau before
choosing any zero. The result is approximate spectral occurrence, not an assertion
of a normalizable eigenfunction.

## Full complex target and actual Xi copies

For every complex mu, the same packets satisfy

`‖(T−mu)v_n(tau)‖ → |cosh(8*pi*tau)−mu|`.

Indeed subtract `(L−mu)v_n` from the residual; the difference is `(T−L)v_n`,
whose norm tends to zero. The norm of `(L−mu)v_n` is exactly `|L−mu|` because
the packets are unit vectors. The reverse triangle inequality proves the limit.

For an actual multiplicity-marked Xi zero `rho`, choose `tau=Im(rho)/2` and retain
the full target

`mu=F((rho/2)(1−rho/2))`.

The exact limiting defect of these constructed unit domain packets is

`D(rho)=|cosh(4*pi*Im(rho))−F((rho/2)(1−rho/2))|`.

The preceding scalar preimage theorem proves `D(rho)=0` exactly when
`Re(rho)=1/2`. It applies because the existing Xi source proves the open unit
strip and nonzero ordinate. The real partner is `1/4+Im(rho)²/4`.
Therefore these actual packets have vanishing residual at the full transformed
Xi target exactly for critical copies. Their domain admission and unit norms
are unconditional; universal defect vanishing is not asserted.

D is the exact defect of this constructed sequence. It is not claimed to be the
greatest lower residual over every vector in T's domain.

An additional exact identity records a possible transport mechanism:

`F((s+1/4)(1−s−1/4)) = F(s(1−s))`.

It follows from `F(s(1−s))=cos(8*pi*(s−1/2))` and cosine periodicity. This scalar
quarter-shift identity supplies no domain intertwiner. The
[full-source multiplier audit](sqb-quarter-shift-source-equation.md) derives the
exact forced equation for y^(−1/4) times the original Eisenstein field. At Xi
parameters its forcing is a rapid Fourier remainder, but the multiplier breaks
scalar modular invariance. The unique compensating power density equals the
original density. A different source transformation or correction must still
produce the required modular-domain occurrence.

## Artifacts and validation

- `formal/GaloisForLFunctions/HTGeometry/CfcResidualTransport.lean`:
  3 public theorems for exact divided-difference factorization, norm control,
  and transport of vanishing residuals.
- `formal/GaloisForLFunctions/RHTower/SelbergScatteringEntireCusp.lean`:
  17 public declarations for positive-coordinate differentiability, original
  energy/covariance transport, normalized transformed packets, and exact residual limits.
- `formal/GaloisForLFunctions/RHTower/SelbergScatteringEntireXiPackets.lean`:
  10 public declarations for the quarter-shift identity, actual Xi packets,
  retained full target, and the exact defect and critical-placement criterion.

All proofs pass `lake env lean` scratch checks. Each final audit used only
`lake build` on its named module, after a read-only `lake --no-build build`
preflight established that only that module was stale. Build logs confirm exactly
one named module compiled per audit. Every compiler handle was collected before
the next compiler started. No full or umbrella build ran; all three modules are
wired exactly once into their umbrellas.

All 30 public exports pass `#print axioms` in a `/tmp` scratch with only
`propext`, `Classical.choice`, and `Quot.sound`, and all are in the research index.
Formal lint at this audit reports one unrelated unfinished module missing from
its umbrella: `HTGeometry.FokasLenellsRawSecondPrimitive`. Existing large-file
warnings remain. These new modules have no lint errors. No proof hole, added
axiom, external numerical certificate, or numerical proof input was introduced.

## Broad corpus discovery and next obligation

Unrestricted OR searches returned the following declaration metadata:

| Concepts | Declarations | Modules |
| --- | ---: | ---: |
| Wave, monodromy, scattering, resonance, cosine family, occurrence, continuation | 4,844 | 848 |
| Transfer operators, trace formulas, Eisenstein, unitary dilation, functional equations, periodic orbits | 3,215 | 809 |
| Shimura, metaplectic, theta lift, half weights, half densities, intertwining | 2,217 | 511 |
| Approximate eigenvectors, approximate spectrum, Weyl sequences, spectral mapping, divided differences, operator Lipschitz | 357 | 128 |

Counts describe search coverage, not reading every returned proof. Relevant
inspection found that `RelativeModularScattering` assumes incoming/outgoing
isometries; `SoninLogCoordinateScattering` constructs a translation-reversing
Fourier involution on a different carrier; the Hellinger–Beta/co-Poisson
transmutation retains nonzero half-integer poles. These inspected statements
do not produce the missing modular Xi occurrence. Mathlib's `DSlope` and the
existing actual cusp packets provide the constructive transport proved here.

The remaining RH-bearing input must match the full complex Xi target using
independent original-source identities. Normalization and occurrence at the
ordinate-only value do not prove that match. The goal remains active and
unproved. Frontier map is read-only and was not edited.
