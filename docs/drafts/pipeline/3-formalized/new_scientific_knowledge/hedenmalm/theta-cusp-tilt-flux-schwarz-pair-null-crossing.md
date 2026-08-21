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

## Next hard conjecture

Boundary nullity and negative tangent orientation are now fully classified; they are detector
geometry, not producer. Next target is source-normal channel: combine exact entropy-normal rate
with corpus nonlinear degree renewal or completed prime--archimedean source law to force
`m N(q) = 0`. Linear budget reporters are already firewalled, so viable producer must be nonlinear,
admission-sensitive, or conserved across degree renewal.

## Log

- 2026-08-21 — Proved exact nonzero Schwarz-paired parity-null boundary law and
  multiplicity-exact negative crossing (subsequently classified as tangent in original Xi
  coordinates).
- 2026-08-21 — Proved exact tangent/normal Lorentz decomposition; crossing coefficient is always
  negative, while orthogonal source-normal coefficient is RH-bearing and globally zero iff RH.
