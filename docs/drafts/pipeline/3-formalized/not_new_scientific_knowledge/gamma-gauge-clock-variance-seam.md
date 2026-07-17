# Gamma gauge--clock variance seam

- **ID:** gamma-gauge-clock-variance-seam
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../1-in-progress/hypertranscendental-source-face-vanishing-cycle-conservation.md
- **Statement:** The ordinary factorial `l2` pivot contains exactly the constant pure Gamma mode,
  although the maximal cyclic conormal contains every finite packet in the current nonnegative-
  frequency Fourier chart.  The source radial scale repairs this mismatch exactly: such a packet
  enters precisely when every active frequency lies below the scale, with no cancellation across
  the wall; every such finite packet
  enters somewhere, and crossing a frequency strictly enlarges the coefficient space.  Strict
  scale transitions are compact and injective.  The factorial reporters form a compatible cocone
  over this system and, at every positive scale, are compact injective maps with dense proper
  range.

## Goal

Separate actual periodic gauge directions from the Hilbert pivot used by the factorial reporter.
This prevents the reporter's proved injectivity from being misread as reconstruction of periodic
gauges which are not inputs to that operator, and forces the positive successor: a dual-polarized
relation across distinct variance spaces.

## Gates

- [x] 0 -> 1 in-progress: exact Gamma objects and a decisive `l2` discriminator
- [x] 1 -> 2 fully-proven: unconditional paper proof
- [x] 2 -> 3 formalized: Lean module
  `GaloisForLFunctions.HTGeometry.GammaGaugeClockVarianceSeparation`
- [ ] 3 -> 4 publication-ready: not a standalone novelty claim

## Theorem

For

```text
b_m(n) = gammaPeriodicFrequency(m)^(n+1),
```

the following statements hold.

1. If `m` is nonzero, then `norm(gammaPeriodicFrequency(m)) >= 1`, so every squared coordinate
   norm of `b_m` is at least one.  Hence its squared norms are not summable.
2. No element of `lp (fun _ : Nat => Complex) 2` has coordinates `b_m` for nonzero `m`.
3. Such an `lp` element exists if and only if `m = 0`; the realizing vector is then zero.
4. Every `b_m`, including every nonconstant mode, belongs to `gammaCoronaClockDomain`.
5. There is no function from the full `gammaCoronaClockDomain` to the factorial reporter `l2`
   space which preserves every raw coordinate.  No linearity or continuity assumption is needed.
6. At radial scale `rho > 0`, the rescaled tail
   `b_(m,rho)(n) = (gammaPeriodicFrequency(m) / rho)^(n+1)` has summable squared norms exactly when
   `norm(gammaPeriodicFrequency(m)) < rho`.
7. Every pure mode belongs to some finite radial Hilbert pivot, but every fixed finite pivot omits
   another pure mode.
8. For a finite nonnegative-frequency packet with coefficients `a_m`, radial square summability holds exactly when
   every active `m` satisfies `norm(gammaPeriodicFrequency(m)) < rho`.  Vandermonde recovery proves
   that distinct unstable modes cannot cancel into `l2`.
9. Every finite packet in this one-sided Fourier chart enters some finite radial pivot.  The coefficient spaces form an
   increasing filtration, and crossing an actual frequency makes the inclusion strict.
10. Radial transition maps compose exactly and are the identity at equal positive scales.  Every
    strict positive transition is Hilbert--Schmidt, hence compact, and injective.
11. At scale `rho`, the source-factorial reporter has diagonal coefficient
    `rho^(n+1)/(n+1)!`.  These coefficients are square-summable for every finite `rho`.
12. The reporter is independent of the chosen entry pivot:

    ```text
    D_sigma o T_(rho,sigma) = D_rho.
    ```

    At `rho=1`, `D_rho` is the original Gamma factorial observability operator.
13. Every nonzero-scale `D_rho` is compact and injective with dense, nonclosed, proper range.  Thus
    the vertical strictness phase `(K,C,S)=(0,0,nonzero)` persists coherently across the radial
    system.

The positive maximal statement is therefore an exact intersection law, not merely a no-go:

```text
{pure periodic Fourier tails} intersect {factorial reporter l2 vectors}
  = {constant-mode derivative tail}.

{radial pivots} form a cofinal scale on pure modes, with no terminal finite pivot.

{finite nonnegative-frequency packets in the rho pivot}
  = {packets supported strictly below the rho frequency wall}.

{D_rho} is a compact-injective dense-range cocone over the compact radial system.
```

## Lean certificate

File:
`formal/GaloisForLFunctions/HTGeometry/GammaGaugeClockVarianceSeparation.lean`

Declarations:

- `one_le_norm_gammaPeriodicFrequency`
- `natCast_le_norm_gammaPeriodicFrequency`
- `gammaPeriodicModeRadialTail`
- `summable_normSq_gammaPeriodicModeRadialTail_iff`
- `exists_radialPivot_summable_gammaPeriodicMode`
- `exists_gammaPeriodicMode_not_summable_at_radialPivot`
- `summable_normSq_gammaPeriodicFourierRadialTail_iff`
- `exists_radialPivot_summable_gammaPeriodicFourierRadialTail`
- `summable_normSq_gammaPeriodicFourierRadialTail_iff_mem`
- `gammaPeriodicFourierRadialCoefficientSpace_mono`
- `gammaPeriodicFourierRadialCoefficientSpace_lt_of_crossing`
- `gammaRadialClockTransition_trans`
- `gammaRadialClockTransition_refl`
- `gammaRadialClockTransition_compact_injective_of_lt`
- `gammaRadialReporter_transition`
- `gammaRadialReporter_one`
- `gammaRadialReporter_compact_injective_dense_nonsurjective`
- `not_summable_normSq_gammaPeriodicModeTail`
- `not_exists_lp_eq_gammaPeriodicModeTail`
- `exists_lp_eq_gammaPeriodicModeTail_iff`
- `gammaPeriodicModeTail_corona_not_lp`
- `gammaCoronaClockDomain_no_coordinatewise_lp_lift`

The exact target was built because its `.olean` was initially absent, and the source file then
passed direct `lake env lean` verification.  Axiom inspection reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Novelty and significance status

Finite exponential stability, Hilbert--Schmidt diagonals, compact linking maps, Silva spaces, and
Köthe sequence spaces are established parent mathematics.  This card is therefore not promoted
as a standalone novelty claim.  Its significance inside the Gamma program is now substantially
stronger than the original no-go: the source frequencies force an exact wall-crossing filtration,
compact-injective bonds, and a pivot-independent factorial reporter cocone carrying the same dense
nonclosed-range phase at every scale.  The candidate-new theorem is no longer “some rigged Hilbert
space exists.”  It is source-presentation invariance of this cocone and transport of the same
strictness class into a second natural HT realization inside the polarized strict-descent field.
