# Exceptional-layer theory of ζ

## Motivation

An isolated rightmost layer would make the prime error contain a persistent finite
oscillation above an infinite remainder. Exceptional-layer theory asks how the exact
Euler product and functional equation constrain their coexistence. Its target is the
asymptotic abscissa law (AAL), or a reduction of AAL to the finite-stratum problem B13.
The programme studies the actual infinite divisor of ζ; a finite exponential model is
useful only when its error against that divisor is proved.

Write Θ for the supremum of the real parts of nontrivial zeros, and
Θ∞ = inf{σ ≥ ½ : only finitely many zeros have real part greater than σ}.
AAL means Θ = Θ∞; ZAL means Θ∞ = ½. RH is AAL together with ZAL.
B13 is the implication that finitely many off-line zeros imply none.

## Objects and language

| Object | Meaning |
|---|---|
| Exceptional layer | The finite, nonempty set of zeros at Θ when AAL fails, counted with multiplicity |
| Isolation gap | Θ−Θ₂, where all remaining zeros have real part at most Θ₂<Θ |
| Layer polynomial | T(u)=−∑_{Re ρ=Θ} e^{i Im(ρ)u}/ρ, paired to be real |
| Remainder | The infinite divisor after the specified finite subtraction; its exponent must remain explicit |
| Prime current | Gaussian regularizations of ∑Λ(n)n^(−s), including pole and Gamma corrections when needed |
| Observation scale | The joint choice of height, damping and prime cutoff at which a current is read |
| Resonant tower | Logarithmic observation times kπ/γ for a selected ordinate γ |
| Repulsion | A restriction on the remainder imposed by the layer |
| Replication | New zeros at unbounded heights forced by an exceptional zero |
| Masking | A layer's contribution concealing another contribution in a one-sided observable |

Reflection sends ρ to 1−conj(ρ) at the same height. It does not replicate zeros.
Approximate-depth replication and exact-depth replication are different statements.

## Foundations

The following are inherited corpus results, not new claims of this programme.

| Pillar | Mathematical content | Source |
|---|---|---|
| Isolated-layer structure | Failure of AAL yields a finite isolated top and reflected bottom | `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean` |
| Prime-error expansion | ψ(x)−x=x^Θ T(log x)+O(x^E), with Θ₂<E<Θ; the leading polynomial is rigid | `ZeroConfigurationGeometry/PrimeErrorFiniteOscillationRigidityAndSignChanges.lean` |
| Persistent low jets | A rightmost zero gives a nonzero limiting prime moment despite a vanishing diagonal | `ZeroConfigurationGeometry/FiniteExceptionalLayersForcePersistentLowJets.lean` |
| High-strip subtraction | A finite subtraction controls the Gaussian error uniformly over a high strip | `EulerFETransportTheory/OnlyExceptionalGaussianModesRemain.lean` |
| Arithmetic rigidity | Integrable or square-integrable functional-equation defects in the specified Beurling class force the ordinary primes | `EulerFETransportTheory/README.md` |

Before using a pillar, check its exact Lean statement and transitive axioms. In particular,
uniformity in one parameter does not authorize a diagonal limit in two parameters.

## Exponential observation laws

Write `K(y,w)=½Γ(w/2)y^(−w/2)`, `s=σ+it`, and `y=e^(−at)`.
The Gaussian mode of a fixed zero ρ has exponential rate

    r(ρ,σ,a)=a(Re ρ−σ)/2−π/4.

Polynomial upper bounds for the mode and its reciprocal prove decay for
`r<0` and norm tending to infinity for `r>0`. The equality case is not
settled by these bounds. Under failure of AAL, finite F and `½≤θ<σ<1`
exist such that every omitted zero lies left of θ and, for every `a>0`,

    ΣΛ(n)n^(−s)e^(−yn²) + e^(−y)ζ′/ζ(s)
      − K(y,1−s) + Σ_{ρ∈F}K(y,ρ−s) → 0.

Convergence is uniform in `Re s∈[σ,1]`. The complete infinite complementary
divisor is bounded before taking the limit; no finite truncation replaces it.

The pole at 1 crosses its growth threshold before any member of F.
Consequently, some positive speeds make every retained zero mode vanish
while the literal prime current divided by `K(y,1−s)` tends to 1 and its
norm tends to infinity. This rules out extrapolating inverse-height raw-current
passage to arbitrary exponential observations. It also identifies the pole
subtraction needed before attributing high-current excursions to the layer.

These are the programme's first proved interaction laws:
`TheGaussianObservationBoundary.lean` supplies the mode boundary and
complete finite-part passage; `ThePrimeCurrentAtExponentialScales.lean`
supplies the raw expansion and pole dominance. They establish observation
scales, not repulsion or zero replication.

Above the top-layer boundary, the pole-subtracted current recovers the
actual top ordinates at escaping heights. Let β be the top and
`a(β−σ)>π/2`. Dividing the corrected current by `K(y,β−s)` gives

    [ΣΛ(n)n^(−s)e^(−yn²) + e^(−y)ζ′/ζ(s) − K(y,1−s)] / K(y,β−s)
      + Σ_{Re ρ=β} exp(π Im ρ/4) exp(i Im ρ·(at+log(t/2))/2) → 0.

`TheExceptionalLayerAtEscapingHeights.lean` proves this formula, including
the vertical Gamma quotient and the vanishing ratios of every lower layer.
The phase has a logarithmic correction; its coefficients retain multiplicity
and a Gamma weight. This is a high-height reading of low zeros through the
infinite prime current. It does not locate new zeros at those heights.

The profile has a sharp recurrent envelope
`S=Σ_{Re ρ=β} exp(π Im ρ/4)>0`. Its normalized current is eventually
bounded by `S+ε` and returns within ε of the complex value −S in every
sufficiently late interval of a fixed length. The length may depend on the
layer, speed and tolerance. The corrected unnormalized current consequently
has arbitrarily large excursions above every height.
`TheSharpRecurrentLayerEnvelope.lean` proves these assertions. The bridge
from Bohr recurrence to physical height uses
`φ_a(t)−φ_a(R)≥a(t−R)/2` for `t≥R≥2`.

## Mechanisms and tools

1. Subtract the actual finite divisor in an explicit formula, retaining all Gamma modes,
   pole terms and the infinite remainder. Track the gap in every error estimate.
2. Read a selected zero through prime-current moments or positive kernels. Derive mixed
   low-height/high-height information from the same arithmetic coefficients.
3. Compare tower excursions with current passage at the same observation scale. A
   conflict requires a proved common scale and compatible normalizations.
4. Use the functional equation together with Euler arithmetic to constrain the remainder.
   A height-reflection identity alone supplies no transport.

Tools sought: exceptional subtraction with joint parameter bounds; isolated-term Turán
estimates for the infinite divisor; positive kernels with an explicitly retained layer;
Gaussian-current laws at zeros and on high strips; Bohr sampling and tower density laws
that preserve the arithmetic relation between the layer and remainder.

## Questions and milestones

| Milestone | Required result |
|---|---|
| M1 | A usable, dependency-audited description of the finite-layer world |
| M2 | A graded repulsion law Θ∞−½ ≤ f(Θ−Θ₂, layer ordinates), with a genuine improvement over existing bounds |
| M3 | Failure of AAL implies finitely many off-line zeros, yielding AAL ⇔ B13 |
| M4 | Exclude an actual isolated exceptional quartet of ζ |
| M5 | Exclude every isolated top layer: prove AAL |

The precise M3 target is finiteness of the off-line remainder, as in §2.5 of the source
report. “Every other zero lies on the line” is stronger: reflection itself supplies a
bottom layer, and additional finite intermediate layers are not excluded by finiteness.
Neither assertion is assumed. M3 alone proves neither AAL nor B13.

Open questions include the correct graded repulsion function; whether a tower's
coefficient-density floor conflicts with the current at its observation scale; and
whether a top quartet forces replicas near multiples of its ordinate. Calibration must
recover the role of a real exceptional zero in the Dirichlet-L setting and distinguish
it from ζ's conjugate nonreal pair.

## Traps and calibration

- FE, reality and order one admit two-scale cosh models. Their layers coexist with
  off-line infinite remainders: these properties cannot prove M3.
- Euler positivity, integral coefficients and linear counting separately admit finite
  layers. A successful exclusion must use the exact FE and Euler product together.
- Positive theta sources and finitely many endpoint or Euler-deletion constraints
  survive off-line surgery. Finite preservation is not arithmetic reconstruction.
- Statistics restricted to either bounded heights or the high tail cannot decide AAL.
- A density lower bound is compatible with rare large current values. A contradiction
  requires matching both the density measure and the scale.
- A family-uniform finite-stratum law for the heat deformation already contains RH.
- A theorem assuming repulsion, transport, recurrence or a decisive current estimate
  does not supply that missing analytic input.

## Position in the corpus

ZeroConfigurationGeometry supplies the abscissa dial and exact finite-layer structure.
EulerFETransportTheory supplies the arithmetic current and FE rigidity; its central
transport question remains shared with this programme. InfiniteRankWeilTheory and
SurfaceOfSpecZ provide tower and prime sampling. ArithmeticCastelnuovoSeveri and
ArithmeticOrientationGeometry interpret these observables as intersection and index
data. Exceptional-layer theory owns interaction laws between a selected layer and the
infinite remainder, rather than duplicating those programmes' receiver equivalences.

## Contribution and success criteria

A contribution must prove a new constraint, identity or obstruction involving the
actual infinite arithmetic object and resolve a named part of the interaction problem.
Definitions, renamed implications, finite toy models, numerical experiments and sharper
constants without a new consequence do not qualify. A negative result must include its
strongest nontrivial positive survivor.

Every claimed theorem requires a complete Lean proof with no unproved analytic inputs,
no added axioms and no trusted computation. New modules belong in this directory and
are imported by `ExceptionalLayerTheory.lean`. The research target remains open until
the stated questions and tools are settled; foundational documentation is not its proof.
