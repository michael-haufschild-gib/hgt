# Exact-event theory of Euler products

## Motivation

An Euler product controls a Dirichlet series where it converges absolutely. Its functional
equation relates opposite sides of the critical line. Neither operation alone explains why
one zero should force zeros at arbitrarily large heights. This programme studies that missing
interaction for the continued, infinite Euler product.

For ζ, write Θ for the supremum of zero real parts and Θ∞ for the corresponding supremum
after arbitrary finite-height deletions. The asymptotic abscissa law (AAL) is Θ = Θ∞.
Its failure is an isolated finite top layer over an infinite remainder. The target is to
exclude such a layer using arithmetic, or construct one within a precisely specified class
of Dirichlet series with Euler product and functional equation.

## Objects and language

- An **exact event** is a zero of the continued Dirichlet series, equivalently a zero of
  every Euler tail at that point. A small value is an approximate event, not an exact one.
- At prime cutoff y, the Euler head E_y is nonzero in Re s > 0 and the continued tail is
  ζ/E_y. Exact cancellation is ζ−E_y = −E_y, including phase.
- **Transport** sends a zero to unbounded heights with arbitrarily small loss in real part.
  **Recurrence** concerns translates of functions; **zero-disc control** concerns their
  behavior around a particular zero. Neither word presupposes an arithmetic theorem.
- The **dial** records Θ, Θ∞ and the linear bounds
  Θ−½ ≤ C(Θ∞−½). Exceptional rank counts the finite modes above a chosen remainder.
- Prime phases, vertical translates, and conditional Euler tails must be studied together.
  An average over the prime torus does not by itself describe an exceptional orbit event.

## Mechanisms to investigate

1. Local analytic stability: identify precisely which boundary information preserves a
   zero and whether arithmetic supplies it along unbounded vertical shifts.
2. Vanishing targets: separate approximation of a zero-bearing function from universality
   for nonvanishing targets. Identify the compactness or noncollapse needed at this boundary.
3. Euler–functional-equation coupling: compare reflected and translated tail events without
   freezing a head whose length grows beyond the recurrence scale.
4. Exceptional-rank rigidity: combine finite top oscillations, positive annihilators and
   their oscillating inverses with information from the infinite remainder.
5. Relative thick counts: connect an arithmetic bound at the remainder's exponent to a
   fixed linear slope, then determine whether that slope can approach one.

## Foundations already available in the corpus

These are inherited results, not contributions claimed by this programme.

| Foundation | Mathematical role |
|---|---|
| AAL iff zero transport iff Euler-tail transport | Exact-event target |
| Near-full cancellation has positive lower density | Explains why η > 0 is insufficient |
| Uniform recurrence with local holomorphic control transports zeros | Analytic receiver; arithmetic recurrence remains to prove |
| Strict linear dial and finite-rank Chebyshev exponent | Quantifies intermediate goals |
| Finite Euler product plus appropriate FE forces local squares | Finite-rank calibration, not the infinite theorem |
| Two-scale blindness, precision cap, positive one-offs | Tests for invalid proposed mechanisms |

High reflected profiles require conductor normalization. The actual normalized
ζ-translate differs from its conjugate reflected profile by an error tending
uniformly to zero on every bounded part of the open strip. Ordinary escaping
translates cannot be locally bounded on a connected upper-half-plane domain
meeting `Re s>1` and crossing the critical line, regardless of prime phases.
The exact law and domain obstruction are in the
[Euler–FE foundations](../EulerFETransportTheory/README.md#conductor-normalized-height-reflection).
They constrain recurrence receivers; same-depth replication remains open.

The Euler–FE programme also admits the full prime current at escaping heights.
Under `¬AAL`, on an interior high strip whose left boundary lies below an actual
exceptional abscissa, `ΣΛ(n)n^(−s)e^(−n²/Im s)+ζ′/ζ(s)→0` uniformly as `Im s→+∞`.
The entire infinite tail is controlled; finite exceptional modes, continuum,
scalar and polar corrections vanish. This supplies a continued arithmetic
observable for transport. Its joint arithmetic control is supplied by the
conditioned mean and return law below. See
[raw prime passage](../EulerFETransportTheory/README.md#raw-prime-passage-at-inverse-height-damping).

The complete Gaussian rough tail also has its exact diagonal mean square
under every fixed smooth prime-head probe, with damping `1/T` on `[T,2T]`.
For the literal von Mangoldt coefficients at `σ>1/2`, this variance tends
to zero as the prime cutoff grows. This provides conditioned tail control. See
[infinite rough variance](../EulerFETransportTheory/README.md#infinite-rough-variance-under-prime-head-conditioning).

Under `¬AAL`, the same conditioned variance holds for the actual continued
current `ζ′/ζ+Σ_{p<Y}log p/(p^s−1)` on one high zero-free line below an
exceptional abscissa. Every small-prime power and the entire rough tail are
retained; Gaussian damping is removed from the observable. See
[continued-current variance](../EulerFETransportTheory/README.md#the-continued-current-retains-the-rough-variance).
Geometric box probes now select arbitrary prescribed finite prime phases
together with squared rough current below `A_Y(σ)+δ`, for any `δ>0`, in every
sufficiently high dyadic window. See
[joint prime-phase returns](../EulerFETransportTheory/README.md#the-continued-current-returns-with-its-prime-head).
The line is fixed across all cutoffs and probes. This scalar return law does
not identify a fixed low holomorphic profile; exact zero transport remains open.

## New pillar: integer support forces exact arithmetic

For a nonempty countable Beurling system whose generalized integers have natural-number
norms, an integrable **uncompleted** Riemann FE defect forces exactly the rational primes.
There is no smallness condition on the defect and no upper bound assumed for the pole residue.
The precise analytic class requires the inverse-3/2 moment and the Hamburger strip
continuity, holomorphy, decay and boundary identities stated in the
[Euler–FE foundations](../EulerFETransportTheory/README.md); the defect is measurable,
polynomially bounded and integrable.

The mechanism is an exact event in the Abel transform. Integer support identifies the cosine
means at frequencies zero and one. Integrable defects have zero radial residue, while the
unit generalized integer has mass one. Thus the pole residue is one. Unit-density rigidity
then fills the integer lattice with unit masses and identifies its prime generators.

The Lean declarations in `IntegerSupportForcesExactArithmetic.lean` are
`integer_support_pins_pole_residue`,
`integer_spectrum_of_integer_support_integrable_defect`, and
`beurlingSystem_rigidity_of_integer_support_integrable_defect`.
Direct Lean checks and transitive axiom audits pass with only `propext`, `Classical.choice`
and `Quot.sound`.

This strengthens the inherited small-defect theorem on integer-supported systems to arbitrary
finite defect. Any nonclassical system in this subclass must fail at least one displayed
regularity or integrability condition. It does not establish those conditions for the known
one-offs, classify noninteger systems, or exclude exceptional zeros of ζ.

## New pillar: asymptotic integer support is exact

Exact integer support can be replaced by asymptotic phase alignment:
cos(2πλₙ) → 1. For a strictly increasing positive spectrum with λ₀ = a₀ = 1,
aₙ ≥ 1 and Σ aₙ/λₙ² < ∞, the same integrable defective theta identity forces
λₙ = n+1 and aₙ = 1. No rate of alignment or bound on defect size is required.

For every δ > 0, phase alignment gives an index M for which the Abel means satisfy

    0 ≤ C₀(ε)−C₁(ε) ≤ 2ε Σ_{n<M} aₙ + δ C₀(ε).

The finite initial segment disappears as ε ↓ 0. The remaining error tends to zero as
δ ↓ 0, forcing pole residue at most one. Unit-density rigidity then identifies the
whole spectrum. Thus decaying displacements of generalized integer norms cannot evade
the classification. Near-integer prime labels alone do not supply this condition:
their products need not approach the integer lattice.

`AsymptoticIntegerSupportIsRigid.lean` proves `abelCos_gap_le_of_tail_phase`,
`pole_residue_le_of_asymptotic_integer_support`, and
`integer_spectrum_of_asymptotic_integer_support`. Its direct Lean check and transitive
axiom audit pass with only `propext`, `Classical.choice` and `Quot.sound`.

## New pillar: finite defect forces unique norm factorization

For countable nonempty Beurling systems in the same Hamburger strip class, integrability
of the uncompleted FE defect forces the generalized-integer norm map to be injective.
This holds for arbitrary real generator norms and arbitrary finite defect size.

The Abel residue at each distinct norm bounds its multiplicity Aₙ by the pole residue
2β. Euler multiplication amplifies any collision: if distinct factorizations u and v
have common norm r, the k+1 factorizations j·u+(k−j)·v have norm rᵏ and are distinct.
For large k this contradicts the uniform multiplicity bound. Thus every generalized
integer norm has a unique prime-label factorization.

`IntegrableDefectsForbidNormCollisions.lean` proves
`intNorm_injective_of_integrable_theta_defect` and
`intNorm_injective_of_integrable_critical_line_defect`.
The first two pillars locate the spectrum under lattice alignment; this pillar forces
unit multiplicities without alignment. Locating arbitrary real norms requires the
boundary and recurrence argument below.

## Boundary calculus for finite defects

An integrable defect has right-hand Laplace boundary values continuous away from zero,
bounded by `3‖g‖₁ |y|⁻¹ᐟ²/(2π)`. They are locally integrable and vanish at infinity.
Every compact continuous test passes to the boundary, including tests crossing zero.
`IntegrableDefectsHaveDecayingBoundary.lean` proves these facts by factoring the complex
power before approaching either imaginary ray, then applying dominated convergence.
Its direct Lean check and transitive axiom audit pass.

`TentPairingsOfIntegrableDefects.lean` pairs the FE with every tent of width `0 < h ≤ 1`
and centre `y > h`. Half its atomic mass equals a sinc-squared cosine pairing, the pole
term `hβ`, and its boundary-error integral. That error is bounded by
`(3h/π)‖g‖₁(y−h)⁻¹ᐟ²`, hence vanishes under distant translation. The inverse-square
moment justifies both limiting interchanges. The exact identity and decay theorem are
kernel checked with the three standard axioms above.

`TentRecurrenceOfIntegrableDefects.lean` derives common distant returns for these cosine
pairings and proves an exact nonlinear restriction. Write
`P_h(y) = hβ + h Σ_x sinc²(πh‖x‖) cos(2π‖x‖y)`. For an actual countable Beurling system
with integrable theta defect, `P_h(y) < 1/4` forces `P_{h/2}(y) = 0`, for `0 < h ≤ 1`.
The atom-mass floor excludes inner atoms whenever the outer half-mass is below `1/4`;
common returns transfer this exclusion after the boundary errors decay. Recurrence is
proved from absolute Fourier convergence. No alignment or defect-smallness condition is used.

`IntegrableDefectsVanishInTheUnitGap.lean` completes the local recurrence argument:
`Re J(iy) = 0` for `0 < y < 1`. Normalized shrinking tent averages recover the boundary
value, while the threshold forces their vanishing. Conjugation of the actual Laplace
identity proves evenness, hence vanishing also for `−1 < y < 0`. Both terminal theorems
are kernel checked with the three standard axioms.

## Complete integrable-defect rigidity

The joint classification with `EulerFETransportTheory` resolves B122 in the stated
Hamburger strip class. Its `IntegrableDefectsForceIntegerSupport.lean` pairs at the origin:
unit-gap vanishing and the locally integrable boundary majorant give
`Σ_x sinc²(π‖x‖) = 0`. Positivity forces natural-number norms without an alignment premise.

`IntegrableFunctionalEquationsDetermineThePrimes.lean` derives pole reality, excludes
empty prime-label systems, and applies integer-support rigidity. The conclusion is exactly
the rational-prime system: β = 1/2, unit integer masses, unique norm factorization, and
ζ_B = ζ on Re s > 1. No lattice, recurrence, residue bound or defect-size assumption is added.
The original inverse-3/2 moment, Hamburger strip conditions, and measurable polynomially
bounded uncompleted defect remain explicit.

`beurlingSystem_rigidity_of_integrable_defect` and
`nonclassical_beurling_defect_cost_eq_top` pass direct Lean checks with the three standard
axioms only. Every nonclassical system in this class has extended defect cost infinity;
therefore the nonclassical finite-layer cost `D_layer` is infinite. This settles the
finite-defect classification branch, without excluding exceptional zeros of ζ itself.

## Tools and questions

| Required tool | Question it must resolve |
|---|---|
| Weak recurrence with zero-disc control | Which arithmetic recurrence can transport a zero without uniform almost periodicity in the strip? |
| Exact-tail existence theorem (B96) | What supplies an event at η = 0 rather than a density estimate for η > 0? |
| FE-to-transport principle (B112) | How can height reflection and Euler arithmetic jointly produce new heights? |
| Relative thick crude count (B116) | Can a bound tied to Θ∞ force a finite slope, and ultimately slope one? |
| Finite-layer exclusion over an approaching remainder (B111) | Does Θ∞ = ½ force Θ = ½? |
| Euler–FE finite-layer classification (B103, B84) | Nonclassical systems in the stated Hamburger strip class have infinite defect cost; finite layers of ζ remain open. |
| Arbitrary finite-defect rigidity (B122) | Proved in that class for integrable or square-integrable uncompleted defects: exactly the rational primes. |
| Shift-family stability | Does the trivial linear slope remain bounded as the shift tends to zero? |

The finite-defect classification is complete in its explicit analytic class. The other
questions, including exact-event existence and zero transport, remain open here.
`EulerFETransportTheory` also proves the complete classification for square-integrable
defects. Strong Hardy boundaries, tent recurrence and Lebesgue differentiation
remove the origin Fejér error and force integer support. Vanishing radial residues
fix the pole and atomic masses; integer periodicity fills the lattice. The terminal
theorems are `beurlingSystem_rigidity_of_finiteEnergy_defect` and
`nonclassical_beurling_defect_energy_eq_top`: every nonclassical system in the same
strip class has infinite square energy. Both pass direct Lean checks with standard
axioms only. The `L¹` and `L²` conditions give separate admissible defect classes.
In the finite-energy branch, `FiniteEnergyRigidityAnnihilatesTheDefect.lean` also
proves that the defect itself is zero almost everywhere under the theta identity,
and pointwise under the original strip identity.
For the entire polynomial-growth class, `LocalThetaDataDetermineTheDefect.lean`
shows that the actual theta kernel on any nonempty open interval of positive
scales determines the defect almost everywhere. Gamma damping gives a holomorphic
Fourier transform in logarithmic scale; analytic continuation and Fourier
injectivity recover the source. `IntegrableRigidityAnnihilatesTheDefect.lean`
uses this identification to prove pointwise vanishing of the original integrable
strip defect as well. These statements concern the full infinite transform.
An implication assuming its missing arithmetic input does not count as construction
of the required tool.

## Traps and calibration

Positive-density near-cancellation does not supply exact cancellation. Convergence of small
values need not retain a nonzero analytic limit. The functional equation preserves absolute
height. A fixed Euler cutoff is a nonvanishing multiplier and cannot remove a zero. Absolute
convergence cannot be silently extended into the critical strip.

Rational zero relocation preserves ζ's Cesàro square means and Fourier means in
`½<Re s<1`, while destroying exact Dirichlet-series realization on `Re s>1`
(`ArithmeticPositiveDuality/FiniteZeroRelocationPreservesTheMeanSpectrum.lean`).
Agreement of mean spectra therefore cannot replace the exact Euler identity.

Even exact outward Euler resolvent covariance, positive source and seed, smooth
reflection and preservation of every real zero survive the corpus's finite
off-line quartet surgery. The literal Gaussian seed equation and complete
monotonicity under every prime deletion distinguish these deformations; the
[Euler–FE calibration](../EulerFETransportTheory/README.md#calibration-and-traps)
states the precise scope. Excluding a modified source does not exclude an
exceptional zero of the original ζ.

For the literal Gaussian, `EulerFETransportTheory/TheCausalGaussianDefect.lean`
identifies a complete admissible causal density from its differential defect on
one open interval. The domain includes every measurable complex kernel of
exponential order. An exact Gaussian rate substitution and local Laplace
uniqueness leave only the scalar identity term invisible. This supplies a
source-deformation test without asserting recurrence of ζ's original zeros.
The full-measure extension also recovers infinite atomic and singular continuous
sources from local defects. Gaussian-weighted admission is closed under
convolution, and a normalized real signed atomic Euler correction repairs continuous
surgery only in the trivial case; see
[causal measure reconstruction](../EulerFETransportTheory/README.md#infinite-atomic-corrections-and-the-causal-measure-algebra).

Gamma-completed decay is weaker than integrability of the uncompleted FE defect used in B84.
Subexponential growth of a Mellin correction alone cannot bridge that distinction.

AAL permits arbitrarily small loss in the transported real part. Exact tail cancellation means
an actual zero; it does not remove that loss. Replication at exactly the same depth is a stronger
endpoint claim when the maximal real part is attained and the tail only approaches it.

Every proposed transport mechanism must recover Bohr recurrence in its domain and the curve
and exponential-polynomial cases. Its arithmetic input must distinguish ζ from the relevant
cosh, heat, Beurling one-off, harmonic-depth, one-pair and Wolff calibrations. AAL must respect
vertical shifts. A line-dependent claim must explain its use of the FE involution and Hardy
zeros. Quantitative improvements with no effect on an open input are not contributions.

## Position in the wider research

TailArithmeticOfThePrimeOrbit supplies Euler heads, tails and exact cancellation.
ArithmeticInnerFunctionTheory studies recurrence and analytic rigidity.
ZeroConfigurationGeometry supplies transport, the dial and separating configurations.
InfiniteRankWeilTheory translates the dial into finite-rank prime-error and thick-tower laws.
ArithmeticPositiveDuality supplies Euler–FE calibrations, annihilators and surgery obstructions.
ArithmeticCastelnuovoSeveri and ArithmeticOrientationGeometry supply the curve comparison and
the count/positivity receivers. ExactEventTheory must provide arithmetic existence or rigidity
inputs for these receivers, rather than duplicate their equivalent formulations.

## Contribution and success criteria

Each module must prove a nontrivial theorem about the infinite problem, identify which open
input it advances, and distinguish its contribution from existing corpus results. A negative
result must expose and formalize its strongest positive survivor. Proofs must be dependency
closed, kernel checked, and free of unproved arithmetic assumptions or numerical evidence.

The programme is complete only when the original tools and questions above are resolved,
with the scope of every classification specified and all asserted proofs formalized. AAL,
ZAL ⇒ RH, and exclusion of an exceptional finite layer of ζ remain unproved here.
