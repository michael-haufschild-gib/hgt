# Receiver Abel escape detects effective pole order

- **ID:** receiver-abel-escape-detects-effective-pole-order
- **Stage:** 3-formalized
- **Type:** THEOREM — uncredited supporting mathematics
- **Source:** review-2610 B3.2; simplicity restriction in actual receiver atom laws
- **Status:** Exact paper statements formalized; individual source checks and transitive axiom audits passed.

## Statement

Let Θ be the supremum of real parts of zeta zeros, ε>0, and
θ=Θ−ε−1/2>0. Write Gε(c,y) for the actual receiver's Laplace symbol and
Qε for its centered meromorphic symbol. At a zero ρ with Re ρ=Θ, set

`mρ=max(0,ordρ ζ−ordρ−ε ζ)`.

This is the existing `ArithmeticOrientationTheory.visibleTranslatedZetaOrder`.
For mρ>0, let aρ be the canonical leading Laurent coefficient
`meromorphicTrailingCoeffAt (centeredReceiverSymbol ε) (ρ−ε)` and put
`cm=∫ℝ(1+x²)^(−m) dx`. Then aρ≠0, cmρ>0, and on every sufficiently
small symmetric window about Im ρ,

`e^(2mρ−1) ∫window |Gε(θ+e,y)|² w(y)dy → cmρ |aρ|² w(Im ρ)`.

The local declaration accepts bounded continuous weights. If mρ=0, the
symbol has an analytic extension and is uniformly bounded on a small box.

For any compact interval [a,b] whose endpoints are not ordinates of boundary
zeros, let Z be exactly its finite set of zeros on Re s=Θ and set
`M=max(1,maxρ∈Z mρ)`. For every continuous real weight w,

`e^(2M−1) ∫[a,b] |Gε(θ+e,y)|²w(y)dy
  → Σρ∈Z,mρ=M cM |aρ|² w(Im ρ)`.

This statement has no Θ<1, simplicity, noncancellation, or global weight-bound
premise. At Θ=1 the boundary set is empty and the limit is zero.

Finally, the actual receiver satisfies the unconditional alternative:

1. Effective orders at all attained rightmost zeros have a common finite bound; or
2. For every natural N, `e^N AbelGram(θ+e)(0,0)→+∞`, and each compact
   window's share of total spectral mass tends to zero.

The second branch follows whenever effective orders are unbounded. The first
branch makes no assertion of tightness or residue summability.

## Paper proof

### Local factorization and coefficient

Put s₀=ρ−ε, D=ordρ ζ, and N=ords₀ ζ. Analytic factorization supplies
`ζ(s₀+z)=z^N u(z)` and `ζ(ρ+z)=z^D v(z)` with analytic units u,v.
For D=N+m, m>0, the centered receiver is

`Qε(s₀+z)=H(z)/z^m`,
`H(z)=u(z)(1−mε ζ(ρ+z))/((s₀+z)v(z))`.

Here mε denotes the receiver's centering constant. Since ζ(ρ)=0,
`H(0)=u(0)/(s₀v(0))≠0`; this equals the canonical Laurent coefficient.
For D≤N, the same analytic quotient times z^(N−D) gives a regular extension.
The actual-abscissa energy estimate identifies this meromorphic expression
with the receiver's Laplace symbol on every nearby line to the right.

### Arbitrary-order atom

Substitute y−Im ρ=e x. The scaled integrand becomes

`1_{|ex|≤δ} |H(e(1+ix))|² (1+x²)^(−m) w(Im ρ+ex)`.

On the fixed small box H is bounded. For m≥1 the integrand is dominated by
a constant times (1+x²)^(−1). Dominated convergence gives the stated atom
and positivity of its mass. Multiplying by a positive power of e eliminates
lower orders at any higher pole scale.

### Sharp compact law

Zeros of the nonzero entire zeta residue unit are locally finite. Choose
one small radius so that windows around Z are disjoint, lie inside [a,b],
and satisfy their local factorizations. Order M contributes its atom;
smaller positive orders disappear after scaling; zero-order windows are
bounded and also disappear.

On the remaining compact rectangle the shifted residue unit is nonzero.
For e>0 this follows from the defining zero-free half-plane of Θ; for e=0
a zero would lie in Z and in one of the removed windows. Compactness bounds
the receiver symbol there. Its weighted integral is bounded and hence
vanishes after multiplication by e^(2M−1). Add the finitely many limits.
For an arbitrary continuous weight, clip it outside its compact bound on
[a,b]; this leaves the integral and all atom weights unchanged.

The preceding rectangle argument uses Θ<1. Since Θ≤1, the remaining case
is Θ=1. The known zero-free line makes Z empty; the residue unit remains
nonzero at its removable pole. For 0<e<ε/2 the numerator stays below Re s=1
and the shifted denominator lies above it. The actual-symbol identity and
compact bound therefore extend to e=0. The scaled integral tends to zero,
which is exactly the empty-set formula with M=1.

### Polynomial control and escape

Factor the entire residue unit into its finitely many zero factors on a ball
containing any fixed compact window and a nonvanishing analytic factor.
Every zero has real part at most Θ, so on Re s=Θ+e each zero factor has
modulus at least e. Compactness bounds the reciprocal analytic factor.
The remaining receiver factors are bounded. Thus every compact spectral
mass is at most C e^(−K) for some finite K.

Let T(e) be total spectral mass, equal by Plancherel to
`2π AbelGram(θ+e)(0,0)`. A pole of order m supplies a positive window W with
`e^(2m−1)W(e)→cm|a|²>0` and W(e)≤T(e). For N<2m−1,
`e^N W(e)→∞`. Unbounded orders therefore give `e^N T(e)→∞` for every N.
For a fixed compact window J, its polynomial bound then gives
`0≤WJ(e)/T(e)≤C/(e^K T(e))→0`.
The bounded-order / escape alternative follows by classical case division;
no unproved analytic hypothesis is inserted.

## Lean declarations and audit

Namespace: `GaloisForLFunctions.ArithmeticCorrespondencePositivity`.
All module paths below are relative to `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/`.

| Module | Main content |
|---|---|
| `TheAbelMassDetectsThePoleOrder.lean` | `tendsto_window_atom_of_pole_order`; comparison of pole scales |
| `CompactWindowsHavePolynomialPoleGrowth.lean` | Compact polynomial bounds for reciprocals of analytic functions |
| `TheReceiverPoleOrdersAreVisibleTranslatedZeroOrders.lean` | `exists_centeredReceiverSymbol_pole_factor`, `exists_centeredReceiverSymbol_regular_factor` |
| `TheReceiverSpectralDensityAtTheZeroAbscissa.lean` | `exists_receiver_window_mass_polynomial_bound` |
| `TheReceiverAbelAtomsHaveTheirEffectivePoleOrder.lean` | `receiver_pole_coefficient_ne_zero_and_atom`, `exists_receiver_pole_order_atom`, `exists_receiver_regular_window_bound` |
| `FiniteWindowPoleMassLimits.lean` | Finite disjoint-window gluing and bounded complement |
| `ReceiverBoundaryZerosAreLocallyFinite.lean` | Exact finite boundary zero set and compact complement control |
| `TheReceiverSymbolAtTheClosedZeroFrontier.lean` | Actual receiver at Θ=1 |
| `CompactReceiverWindowsSelectTheMaximalVisibleOrder.lean` | `exists_receiver_compact_maximal_order_law` |
| `UnboundedVisibleOrdersForceAbelEscapeToInfiniteHeight.lean` | `receiver_visible_order_or_infinite_height_escape` |

Each source passed `lake --old env lean <module>.lean` from `formal/`.
Main `#print axioms` outputs contain exactly `propext`, `Classical.choice`,
and `Quot.sound`. No placeholders, added axioms, trusted computation, raised
limits, or hidden analytic inputs. All ten modules are wired into the ACP
umbrella; the umbrella was not compiled. Supporting energy modules were
already checked and integrated.

## Novelty and significance decision

The corpus previously supplied simple-pole atom/capacity laws, model power-log
multiplicity, and the effective-order invariant. This package proves their
exact actual-source multiplicity classification and compact escape alternative.
It is retained as **uncredited supporting mathematics**: the mechanism remains
local analytic factorization, rescaling, and finite gluing. B3.2 already places
finite-height pole classification on the known side of the hard obstacle.
Residue summability, infinite-height tail control, and the general unattained
frontier remain unresolved. No significant-contribution credit is claimed.

- [x] Corpus audit and reuse of existing invariant.
- [x] Dependency-closed paper proof.
- [x] Exact Lean formalization and individual final source checks.
- [x] Transitive axiom audit and umbrella integration.
- [x] Significance audit: uncredited; accepted total remains 0 / 250.
