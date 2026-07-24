# Integer-string/dimensional-QED three-gauge-class universality law

- **ID:** integer-string-dimensional-qed-three-gauge-class-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `gammaIntegerOrbit_openClosedSpin_simultaneousCollapse`,
  `dimensionalQEDGamma_gaugePartitionUniversality`,
  `hypertranscendentalOver_gammaNatScaleMero`, and the exact Gamma normal forms
- **Statement:** At every integer channel parameter, generalized-spin, reduced open-string, and
  reduced closed-string Gamma carriers form one nonzero differential-algebraic multiplicative
  gauge class. Dimensionally regulated bubble, triangle, and scalar-QED carriers form a second,
  hypertranscendental gauge class. Spinor-QED forms a third hypertranscendental gauge class.
  The three classes are pairwise distinct.

## Goal

Extract the exact multiplicative-gauge partition shared by seven Gamma carriers from finite-spin
continuation, open/closed string amplitudes, dimensional regularization, and constant-field QED.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `gammaIntegerOrbit_openClosedSpin_simultaneousCollapse`
- `dimensionalQEDGamma_gaugePartitionUniversality`
- `hypertranscendentalOver_gammaNatScaleMero`
- `gammaNatScaleMero_one`
- `gammaShiftMero_ne_zero`
- `gammaNegativeShiftMero_reflection`
- `gammaReflectionGaugeMero_ne_zero`
- `differentialAlgebraicGaugeEquivalent_symm`
- `differentialAlgebraicGaugeEquivalent_trans`
- `differentialAlgebraicOver_div`

## Proof

**[PROVED HERE]** Fix `a,N ∈ ℂ` with `N` on the integer orbit. The simultaneous-collapse theorem
makes the generalized-spin channel, reduced Veneziano channel, and reduced Virasoro--Shapiro
channel differentially algebraic over `ℂ(z)`. Every positive-slope Gamma clock is nonzero.
Euler reflection writes every negative-slope clock as a product of a nonzero reflection gauge and
the inverse of a nonzero positive-slope clock. Expanding the three channel definitions therefore
shows that all three carriers are nonzero.

For any two nonzero differentially algebraic elements `x,y` in a differential field,
`g := x/y` is nonzero and differentially algebraic, and `x = g y`. Thus the three integer-string
carriers lie in one differential-algebraic multiplicative gauge class.

The scalar- and spinor-QED carriers are respectively `Γ(z+1/2)` and `Γ(z+1)`. The positive
integer-scale Gamma theorem at scale one makes each hypertranscendental. The existing
dimensional/QED gauge-partition certificate puts bubble, triangle, and scalar QED in one gauge
class and separates spinor QED from each of them.

Finally, a differentially algebraic element cannot be a nonzero differentially algebraic multiple
of a hypertranscendental element: if `x = g y` with `x,g` differentially algebraic and `g ≠ 0`,
then `y = g⁻¹x` is differentially algebraic, contradiction. Applying this to the generalized-spin
representative separates the integer-string class from both QED representatives. Symmetry and
transitivity of gauge equivalence propagate those representative separations to every carrier in
the corresponding classes. Hence the seven carriers split into exactly the three stated classes.
No computation is used. ∎

## Strict gain over corpus endpoints

The integer-orbit theorem synchronizes the differential phase of three string/spin channels but
does not classify their multiplicative gauge classes or compare them with QED/dimensional
carriers. The dimensional-QED theorem partitions four HT carriers but has no integer-string
sector. The scale-one Gamma theorem supplies individual HT status but no cross-physics partition.
Their closure produces one exact seven-carrier, three-class gauge law.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.IntegerStringDimensionalQEDThreeGaugeClassUniversalityLaw`
- Main theorem:
  `integerStringDimensionalQED_threeGaugeClassUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/HTGeometry/IntegerStringDimensionalQEDThreeGaugeClassUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for Gamma hypertranscendence, open/closed string Gamma amplitudes, dimensional regularization, and
constant-field scalar/spinor QED found no exact seven-carrier three-gauge-class partition. Closest
primary sources:

- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>, gives general difference-Galois
  hypertranscendence results and discusses Hölder's Gamma theorem, but no physical-carrier gauge
  partition.
- S. K. Blau, M. Visser, and A. Wipf, *Analytic results for the effective action*,
  <https://arxiv.org/abs/0906.2851>, derives constant-field scalar and spinor one-loop effective
  actions, but does not compare their Gamma carriers with string amplitudes or dimensional
  master-integral carriers under DA gauge equivalence.
- S. Stieberger, *Closed Superstring Amplitudes, Single-Valued Multiple Zeta Values and Deligne
  Associator*, <https://arxiv.org/abs/1310.3259>, relates open and closed superstring amplitudes
  algebraically, but not through the differential-algebraic gauge classification used here.
- J. Huang and T. W. Ng, *Hypertranscendency of Perturbations of Hypertranscendental Functions*,
  <https://arxiv.org/abs/2007.10037>, studies multiplicative and additive perturbations of
  hypertranscendental meromorphic functions, but not this integer-string/dimensional-QED
  three-class closure.

## Log

- 2026-07-23 — whole-corpus terminal-pair scan exposed shared Gamma orbit and gauge-class
  infrastructure across integer string/spin and dimensional-QED endpoints.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module was wired into HTGeometry umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
