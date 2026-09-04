# Valuation-frame audit: one prime already sees the shift singularity

- ID: ULF-VFCA-001
- Stage: 1-in-progress; bounded-realization audit, not a new primary conjecture.
- Type: `[BRIDGE]` candidate / hostile test of the MCCED frame replacement.
- Lean: read-only; no new certificate or build in this pass.

## Higher-law obligation

The missing law concerns actual arithmetic/theta completion, not a chosen frame's inability to
act boundedly. STATUS F634--635/MUST-198 separates the declared prime-only frame from Poisson
completion. Replacing `a log p/2` by `a k log p/2` repairs depth dependence but changes the claim.
Before investing in that repair, test whether its obstruction already occurs without cross-prime
arithmetic. A positive answer would remove this repaired frame from the evidence for a new
arithmetic completion mechanism, not refute the underlying relative-completion programme.

Exact surviving RH edge stays unchanged: one pre-divisor relative representative must both land
on Xi escape and inherit the primitive Euler sub-unit bound. The audit below proves neither edge.

## Corpus audit

Custom `scripts/formal_tools.py research --limit ...` queries:

```text
Burnol theta frame valuation clock Gram multiplier bounded interpolation
tanh Bergman multiplier Blaschke prime depth holonomy
Burnol aperture semigroup dense span eigenfeatures resolvent Cayley inverse
one prime powers dense Laplace span weighted shift tanh
Burnol tanh unbounded one prime shift Cayley
Cayley contraction maximal accretive dense range shift approximate spectrum
```

Inspected definitions/proofs:

- `PrimeBurnolThetaModularHolonomy`: frame uses `a log p/2`, independent of depth.
- `PrimeDepthAliasingModularEscape`: two fixed primes with close depth rates amplify their
  depth-independent frame mismatch. No valuation-frame theorem follows from that proof.
- `RoutePPrimitiveBurnolApertureDampingSemigroup`: literal shift
  `K_h f(t)=t/(t+h) f(t+h)`, contraction, semigroup, and exact primitive eigenfeatures.
  For one prime p, the features are nonzero scalar multiples of `t exp(-k log(p)t)`, k>=1.
- `DirectSubunitEscapeCapacityFusion` and `RoutePPrimitiveCollisionCapacityTerminal`: the two
  known estimates give a source/target gap; asserting the target capacity is exactly RH.
- `CubicClockExtensionLiftingObstruction`: powered-clock class is not the actual third transport
  derivative (ULF-CDMA-001). This audit does not restore that identification.

No exact one-prime valuation-frame boundedness classification surfaced in these searches; this
is not an exhaustive novelty claim. The proposed result is expected to be ordinary shift theory.

## Frozen audit target (derived theorem, not conjecture-distance claim)

Let H=L2((0,infinity),dt), ell>0, and f_k(t)=t exp(-k ell t), k>=1. Determine whether the
algebraic map `f_k -> tanh(a k ell/2) f_k` extends boundedly to H for a!=0. Also determine
whether its failure yields any arithmetic discriminator rather than a universal shift singularity.

Candidate stronger survivor: identify the exact norm of the attenuated Cayley family
`(I-r K_h)(I+r K_h)^(-1)`, 0<=r<1, and the domain/closedness of its unattenuated limit.
Attenuation is a diagnostic control, not a proposed RH regularization.

## External parents checked

- Phatak--Sholapurkar, [weighted translation models](https://arxiv.org/abs/1804.08981): analytic
  models and spectra of left-invertible weighted translations. Our left shift has a kernel,
  so their left-invertibility hypothesis cannot be silently applied to it.
- Eisner--Zwart, [semigroups and cogenerators](https://arxiv.org/abs/0805.2020): Cayley/resolvent
  criteria are established operator theory. No new-field claim for Cayley singularity.
- Horvath, [weighted Muntz density](https://arxiv.org/abs/1009.5777): broader density parent.
  Our equally spaced rates admit an elementary polynomial-moment proof instead.
- Connes--Consani--Moscovici, [Zeta Spectral Triples](https://arxiv.org/abs/2511.22755): finite
  Euler self-adjoint models do not discharge their limiting Xi identification. This audit must
  not replace our own missing identification by a named frame either.

## Proof attack and status

Working proof route: one-prime span is dense by `x=exp(-ell t)` and uniqueness of finite measures
from polynomial moments. On that span the contrast is the Cayley transform of K_|a|. Long
oscillatory packets far out on the aperture ray make K_|a| arbitrarily close to minus identity.
Bounded extension would therefore map an arbitrarily small vector to a vector of norm near two.

Hostile checks required before Stage 2: prove density with the correct transformed measure;
control both support-boundary and weight errors; distinguish source norm from coefficient norm;
prove domain density and closedness without assuming inverse boundedness; audit prime amplitudes;
do not infer Xi admission, modular-coefficient boundedness, or an index from this result.
