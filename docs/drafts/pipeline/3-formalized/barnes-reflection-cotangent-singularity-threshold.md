# Barnes cotangent singularity is not an order-only hypertranscendence criterion

- **ID:** `barnes-reflection-cotangent-singularity-threshold`
- **Stage:** 3-formalized
- **Type:** CORRECTED NO-GO + PERIOD-SOURCE THEOREM
- **Scientific status:** `[ALGEBRAIC HALF LEAN-FORMALIZED]`
  `[ANALYTIC HALF IS AN UNAUDITED PAPER CANDIDATE, NOT LEAN-FORMALIZED]`
- **Formal modules:**
  - `formal/GaloisForLFunctions/HTGeometry/BarnesCotangentSingularityThreshold.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GammaPhaseCompletion.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ClockPeriodCommensurabilityBoundary.lean`
  - `formal/GaloisForLFunctions/HTGeometry/FiniteDifferentialCircuitBoundary.lean`

## Correct statement

For the normal-crossing polynomial

```text
f_N = product_(i=1)^N (t_i - 1),
```

the intrinsic derivational critical ideal is proper exactly for `N >= 2`.  This is an algebraic
threshold in the cotangent geometry of the presentation.

It is not, by itself, a hypertranscendence criterion for the Barnes multiple sine.  The analytic
classification depends on the arithmetic geometry of the period vector:

```text
rationally commensurable periods                 => differentially algebraic,
some non-real period ratio                       => hypertranscendental,
positive-real incommensurable periods            => not classified by these theorems.
```

Consequently there is no established order-only equivalence

```text
multiple sine is HT  <=>  N >= 2.
```

The project has a paper proof candidate for that equivalence under positive rational independence
in `all-order-multiple-sine-stanley-reisner-differential-matroid.md`.  That candidate is stronger
than the external literature located so far, depends on an unaudited simultaneous-telescoping
argument, and is not formalized on the actual multiple sine.  It therefore cannot be promoted here
as part of the Lean-formalized theorem.  The candidate remains live; only the unsupported promotion
to a checked analytic parent is retired.

## Lean-formalized algebraic theorem

The following declarations remain valid and unconditional:

- `normalCrossingCriticalIdeal_ne_top_iff`;
- `normalCrossingCotangentSingularityThreshold`;
- `normalCrossingRestriction_surjective`;
- `ker_normalCrossingRestriction`;
- `normalCrossingCotangentFittingIdeal_eq_singularIdeal`;
- `comap_normalCrossingCotangentFittingIdeal`;
- `normalCrossingRestrictionCertificate`.

They prove the exact restriction law from the normal-crossing hypersurface to its critical scheme
and the onset of cotangent singularity at order two.

`barnesReflection_cotangentSingularity_exactThreshold` is a theorem about an explicitly supplied
`BarnesReflectionAnalyticThresholdInput`.  It is logically valid, but that input is not an internal
proof of the classical multiple-sine claim and must not be cited as one.

## Period-sensitive replacement

`ClockPeriodCommensurabilityBoundary.lean` introduces:

```text
RationallyCommensurablePeriods omega
HasNonrealPeriodRatio omega
MultipleSineDifferentialRegimeInput F E I multipleSine
```

and proves unconditionally that rational commensurability excludes every non-real period ratio.
The analytic literature is represented by a named input structure rather than an axiom.

The positive observable statements are:

```text
HT(multipleSine omega) => not RationallyCommensurablePeriods omega,

DA(multipleSine omega) => not HasNonrealPeriodRatio omega.
```

For an exact finite factorization

```text
Z = product_(k in K) multipleSine(omega_k),
```

the formalized source-localization theorem gives

```text
HT(Z) => exists k in K, not RationallyCommensurablePeriods(omega_k).
```

This is the significant positive residue of the no-go.  Hypertranscendence is detecting the
observability structure of the clock lattice: finite multiplication of rationally locked clocks
cannot create it.

## Physics value

The period vector is geometric data of the observable, not an evolution parameter.

- Three-dimensional supersymmetric partition functions use the double sine or hyperbolic gamma
  as a basic one-loop factor.
- Perturbative partition functions on squashed five-spheres use the triple sine.
- Four-dimensional superconformal indices use elliptic-gamma factors, and higher-dimensional
  indices use multiple elliptic gamma functions.

The established differential-algebraic boundary therefore separates physical parameter sectors:
commensurable squashing or equivariant periods are DA; genuinely complex period directions can be
HT for the multiple sine; the common positive-real irrational squashing regime remains an analytic
research problem rather than a theorem.

## Elliptic-gamma warning

Kato proves that the multiple elliptic gamma function is differentially algebraic for rational
periods.  The non-rational-period case is stated there as open.  Therefore no blanket HT theorem
for the actual elliptic-gamma product in this corpus is currently justified.  The existing exact
commensurable factorization remains valuable, but it is not an HT proof.

## Literature boundary

1. Kurokawa--Wakayama, *Differential Algebraicity of Multiple Sine Functions*, Lett. Math. Phys.
   71 (2005), proves DA for rational periods.
2. Masaki Kato, *Hypertranscendence of the Multiple Sine Function for a Complex Period*, Proc.
   Japan Acad. Ser. A 95 (2019), proves HT when a period ratio is non-real.
3. Masaki Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational
   Period*, Funkcialaj Ekvacioj 64 (2021), proves DA in the rational-period multiple-elliptic-gamma
   sector and states the non-rational case as open.
4. Dolan--Spiridonov--Vartanov, *From 4d superconformal indices to 3d partition functions*,
   arXiv:1104.1787, identifies the double sine/hyperbolic gamma as the basic 3d building block.
5. Imamura, *Perturbative partition function for a squashed S5*, arXiv:1210.6308, identifies the
   triple sine in the one-loop partition function.

## RH pressure test

This correction does not prove RH and does not supply a sign or zero-location theorem.  It removes
an invalid unconditional producer from the RH search: cotangent singularity or reflection order
alone cannot be used to infer an HT source without the period-sensitive analytic parent.  A future Barnes-type bridge to the completed zeta source would have to
construct period-lattice data and show how it controls an RH-relevant positivity or orientation
statement.  At present, the result strengthens HTGeometry and is only a guardrail for RHTower.
