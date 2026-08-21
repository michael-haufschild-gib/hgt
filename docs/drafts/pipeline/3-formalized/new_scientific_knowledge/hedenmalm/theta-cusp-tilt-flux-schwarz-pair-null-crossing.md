# Schwarz-pair null cone and transverse crossing

Status: Lean-formalized null cone, exact crossing, and tangent/normal Lorentz decomposition.
`[CORPUS-NEW SYNTHESIS]`.
Does not prove RH.

## Conjecture loop outcome

The Cauchy localization theorem identifies critical-line reflection `alpha ↦ conj alpha` as the
parity involution. Corpus search of the positive-paired source route exposed a second involution:
source Schwarz pairing is `alpha ↦ -conj alpha`. Lean now proves that the boundary test supported
on one fiber and its source-Schwarz partner,

```text
1_{alpha} + 1_{-conj alpha},
```

is disjoint from its critical-line reflection whenever `alpha` is nonzero and nonreal. Therefore
its Weil square and Hilbert quadratic are exactly zero.

This is not zero-vector degeneracy. On every hypothetical off-line Xi quartet, its
reflection-even and reflection-odd energies are equal and both strictly positive. Hence the
positive-paired Cauchy closure reaches a genuine Krein null direction at the divisor boundary.

The resulting higher principle is:

```text
Schwarz-paired boundary values lie on the parity null cone;
orientation lives in the first transverse crossing, not in boundary positivity.
```

This explains why paired-diagonal negativity appears only at nearby regular poles and why a
boundary-value coercivity argument cannot close RH. `FiniteHankelBoundaryKreinCrossing` exhibits
the same structure algebraically: a null state is oriented by its first extension coordinate.

## Lean source

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxWeilParitySchwarzPairNullCone.lean`

Key closed declarations:

```text
xiWeilSchwarzPairedFiberTest_product_eq_zero
xiWeilPolarization_schwarzPairedFiber_eq_zero
xiWeilSchwarzPairedFiber_evenEnergy_eq_oddEnergy
xiWeilHilbertQuadratic_schwarzPairedFiber_eq_zero
xiWeilSchwarzPairedFiber_evenEnergy_pos
xiWeilSchwarzPairedFiber_oddEnergy_pos
```

Verification:

- direct source check and exact target build passed; no umbrella/full build was run;
- all audited `#print axioms` reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden-token and whitespace scans passed;
- module is wired into `RHTower.lean` without building umbrella.

## Exact transverse crossing theorem

Lean now exports the exact transverse crossing rate hidden inside
`exists_xiReciprocalSquareUpperSector_neg_near_of_zero`. For canonical horizontal approach from
side opposite `alpha.re`, with `epsilon_n = 1/(n+1)`, it proves

```text
epsilon_n * ccmPositivePairedReducedKernel(z_n, z_n)
  -> -2 * |alpha.re| * ord_alpha(Xi) / normSq(alpha).
```

Lean also proves every mesh point eventually belongs to full continued-source domain, coefficient
is strictly negative, and source diagonal itself is eventually negative. Thus positive-paired
source diagonal is exact first Krein crossing form of nonzero parity-null boundary state,
including divisor multiplicity. Existing nearby-negativity existence is sharpened to canonical
spectral-flow law.

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxWeilParitySchwarzPairCrossing.lean`

Key closed declarations:

```text
tendsto_xiReciprocalSquareTransverseApproach
eventually_xiReciprocalSquareTransverseApproach_continuedDomain
tendsto_xiReciprocalSquareTransverse_sector
tendsto_ccmPositivePairedReducedKernel_transverse_crossing
ccmPositivePairedReducedKernel_transverse_crossingLimit_neg
eventually_ccmPositivePairedReducedKernel_transverse_neg
```

Verification:

- scratch proof, direct source check, and exact target build passed;
- all audited `#print axioms` reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`;
- no umbrella/full build was run;
- crossing module is wired into `RHTower.lean`.

## Tangent/normal Lorentz decomposition

Corpus comparison with reciprocal-square transverse-defect and source-entropy modules falsified
the tempting identification of crossing speed with RH defect. In rotated centered coordinates
`a = xiSpectralPoint q`, the canonical crossing varies `a.re`, which is original Xi height; it is
tangential to the critical line. Writing `lambda = a⁻²`, Lean proves exact complementary rates

```text
T(q) = 2 * |a.re| / normSq(a),
N(q) = |riemannReflectedSourceEntropy(q)| / normSq(a),

T(q)² = 2 * (|lambda| + Re lambda),
N(q)² = 2 * (|lambda| - Re lambda)
      = 2 * transverseDefect(lambda),
T(q)² + N(q)² = 4 / normSq(a).
```

With analytic multiplicity `m`, actual continued-source limit is `-m T(q)`. This coefficient is
strictly negative at every Xi divisor copy, including under RH, so its magnitude cannot be an RH
vanishing invariant. Orthogonal coefficient `m N(q)` vanishes pointwise exactly on critical line
and vanishes globally exactly iff RH. Thus earlier crossing is a genuine detector of interior
divisor contact, but RH-bearing information is conserved source-normal entropy channel.

This identifies reason fixed tangent positivity/crossing arguments stall: they control
`|lambda| + Re lambda`, while RH is radical of complementary `|lambda| - Re lambda`. Any producer
must transfer or annihilate normal channel; tightening tangent crossing estimates cannot suffice.

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxWeilParitySchwarzPairLorentzWeld.lean`

Key closed declarations:

```text
xiSchwarzPairTangentialCrossingRate_sq
xiSchwarzPairSourceNormalRate_sq
xiSchwarzPairLorentzPythagoras
xiSchwarzPairTangentialCrossingCoefficient_neg
forall_xiSchwarzPairSourceNormalCoefficient_eq_zero_iff_riemannHypothesis
xiSchwarzPairCoefficientPythagoras
tendsto_ccmPositivePairedReducedKernel_xiZeroCopy_tangentialCrossing
```

Verification:

- corpus search found separate crossing/source-entropy/transverse-defect laws but no weld;
- scratch proof, direct source check, and exact target build passed;
- all audited `#print axioms` reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden-token scan passed;
- no umbrella/full build was run; module is wired into `RHTower.lean`.

## Source-normal renewal phase dichotomy

Corpus search first tested finite Stokes-conditioned coenergy against constitutive KL renewal
price. That conjecture fails at a precise seam: coenergy is a summable scalar prime-power family,
but corpus has no measure realization identifying it with, or bounding, renewal KL action. Treating
the two as interchangeable would be unsupported.

The nonlinear shifted-Xi Weyl corpus supplies a genuine replacement. Lean now proves fixed actual
abelian class-law scale-orbit certificates exist exactly when Schwarz-pair normal coefficient is
zero. Off zero fibre, every finite degree admits an unconditional far-right positive Hankel block
whose nonlinear Jacobi/Weyl renewal injects exactly `|Im(xiSpectralPoint q)|`. Quantitatively,

```text
normSq(a) * normalCoefficient(q) = multiplicity(q) * |centeredRate(q)|,
2 * multiplicity(q) * WeylIncrement(q,w,n)
  = normSq(a) * normalCoefficient(q).
```

Hence fixed-source contiguity and changing-admission renewal are two complementary phases:
neutral normal charge is realized by a fixed class law, while nonzero normal charge necessarily
survives through positive nonlinear degree renewal. The obstruction is no longer existence at any
finite degree. It is cofinal degree--mass synchronization: current far-right witness may depend on
degree.

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxWeilParitySchwarzPairNormalRenewalWeld.lean`

Key closed declarations:

```text
sourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate_nonempty_iff_normalCoefficient_eq_zero
xiSchwarzPairSourceNormalRate_eq_abs_centeredRate_div_normSq
normSq_mul_xiSchwarzPairSourceNormalCoefficient_eq_multiplicity_mul_abs_centeredRate
xiSchwarzPairCompletedSourceWeylNormalizedIncrement_eq_normalDisplacement
xiSchwarzPair_offLine_finiteDegree_nonlinearRenewal
xiSchwarzPair_classLaw_or_nonlinearRenewalPhase
```

Verification:

- corpus research search, scratch proof, direct source check, and exact target build passed;
- audited theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-token and whitespace scans passed;
- module is wired into `RHTower.lean`; no umbrella/full build was run.

## Next hard conjecture

Construct one cofinal degree--mass schedule, or a compactness/diagonal limit replacing it, on which
shifted-Xi positive admission and exact source-normal Weyl renewal persist simultaneously. Then
compare resulting persistent nonlinear source capital with an actual finite source-action budget.
Do not identify Stokes coenergy with KL without a proved measure bridge.

## Log

- 2026-08-21 — Proved exact nonzero Schwarz-paired parity-null boundary law and
  multiplicity-exact negative crossing (subsequently classified as tangent in original Xi
  coordinates).
- 2026-08-21 — Proved exact tangent/normal Lorentz decomposition; crossing coefficient is always
  negative, while orthogonal source-normal coefficient is RH-bearing and globally zero iff RH.
- 2026-08-21 — Proved fixed-class-law/positive-nonlinear-renewal phase dichotomy and exact
  coefficient transfer at every finite degree; isolated cofinal degree--mass synchronization as
  remaining producer seam.
