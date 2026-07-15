# Formalize the prime-seam damping aperture

- **Target:** `formal/GaloisForLFunctions/RHTower/PrimeClockDampingAperture.lean`
- **Paper provider:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/prime-seam-damping-aperture-law.md`
- **Successor paper providers:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/archimedean-meixner-root-seam-scale.md`,
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/meixner-root-prime-laplace-value-frame.md`,
  and
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/xi-global-meixner-shape-landau-rh.md`
- **Priority:** top-down RH bridge; exact source-interface filter

## Requested theorem surface

Formalize the paper-proved interpolation between the undamped Shale diagonal and the
reciprocal-prime/Gamma-damped logarithmic seam.

For `theta>=0`, define the weighted amplitude and logarithmic seam densities and prove:

```text
Summable (weightedPrimeClockReflectionEnergy theta sigma)
  <-> sigma=1/2 or theta>|2*sigma-1|

Summable (weightedNatPrimeSeamChargeNormSq theta rho)
  <-> rho.re=1/2 or theta>|2*rho.re-1|.
```

Then expose the aperture identity and global consumer:

```text
primeSeamDampingAperture sigma = |2*sigma-1|

(forall theta>0, forall rho:XiDivisorSupport,
    Summable (weightedNatPrimeSeamChargeNormSq theta rho))
  -> RiemannHypothesis.
```

## Existing providers to reuse

- `RHTower/PrimeClockShaleDiagonal.lean`:
  `primeClockReflectionEnergy`, the reflection identity, and prime-harmonic divergence.
- `RHTower/XiPrimeSeamCoherenceCollapse.lean`:
  `orbitwiseNatPrimeSeamCharge` and the exact critical-line zero locus.
- `RHTower/XiPrimeSeamReflectionEnergy.lean`:
  the per-prime norm-square reflection formula and logarithmic prime-power summability.
- `RHTower/XiPrimeSeamPairAsymptotics.lean`:
  the existing reciprocal-prime open-strip summability endpoint.
- `RHTower/XiHurwitzAnchorPrimeTwoOrientationEnergy.lean`:
  the orientation-energy-to-RH terminal implication.

Use the comparison

```text
p^(-theta)|A_p|^2
  = p^(-1-(theta-2*delta)) (1-p^(-2*delta))^2,
delta=|sigma-1/2|,
```

and bound the last factor above and below by positive constants off the line. For the logarithmic
case, reuse the existing `summable_abs_log_natCast_pow_mul_rpow_neg` family on the convergent side
and `Nat.Primes.not_summable_one_div` on the divergent side.

## Gamma--Meixner successor surface

After the power-weight theorem is stable, formalize the canonical source realization

```text
meixnerRootPrimeWeight theta p
  = (Real.cosh (2 * Real.log p)) ^ (-theta / 2)
```

and prove its exact value and two-sided comparison with `p^(-theta)`.  Compose that comparison with
the damping aperture theorem to expose:

```text
Summable (meixnerRootPrimeSeamEnergy theta rho)
  <-> rho.re=1/2 or theta>|2*rho.re-1|

(forall m>=1, Summable (meixnerRootPrimeSeamEnergy (1/m) rho))
  -> rho.re=1/2.
```

Then formalize the common exponential frame `p |-> p^(-x)` for `x>1`, its density in every
weighted `ell^2` root space, and the finite Riesz/Gram consumer from the paper card.  Reuse the
Dirichlet-series uniqueness architecture behind `PrimeLaplaceGramStrict.lean`; do not encode the
value relation as an opaque bounded functional.

The global continuation consumer should define

```text
A p = sum_rho xiHurwitzOrientationWeight rho
  * normSq (orbitwiseNatPrimeSeamCharge p rho)
```

and prove coefficient finiteness and safe convergence for real shape `theta>1`.  The holomorphic
Landau conclusion requires either a small general-Dirichlet-series lemma for increasing frequencies
or a dedicated theorem for `lambda_p=log(cosh(2log p))/2`.  Keep the analytic-continuation premise
explicit: the current corpus does not yet produce it.

## Wiring

After focused verification, import the new module from the appropriate RHTower umbrella and move
the paper card to stage 3 with theorem names and axiom audit. Do not claim that the all-positive-loss
source premise or the Gamma-shape continuation has been established; those are the remaining
analytic inputs.  Use targeted module checks only, not a full project build.
