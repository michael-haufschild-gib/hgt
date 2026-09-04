# Valuation-frame audit: one prime already sees the shift singularity

- ID: ULF-VFCA-001
- Stage: 1-in-progress; bounded-realization audit, not a new primary conjecture.
- Type: `[BRIDGE]` / hostile test of the MCCED frame replacement; exact survivor paper-complete.
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

## Verdict and positive survivor

[ULF-BFCC-001](../../../2-fully-proven/universal-law-field/poisson-scale-history-completion-mechanics/burnol-frame-completion-classification.md)
closes those paper obligations. Lean status remains **not formalized**, per read-only instruction.

- Original prime-only frame: after literal Burnol synthesis, each prime's depth span is dense.
  Two distinct constant rotations force graph closure to be the whole doubled input/output space.
  This realization is maximally nonclosable at every nonzero grade, not just unbounded.
- Valuation-clock replacement: its scalar contrast has the unique closed realization
  `sgn(a)(I-K_|a|)(I+K_|a|)^(-1)`. The full frame splits into two phase-Cayley operators on
  their exact dense domains. Both are unbounded without invoking any Xi zero or second prime.
- Strongest survivor: for every unit phase zeta and h>0, attenuated Cayley operator
  `(I-r zeta K_h)(I+r zeta K_h)^(-1)` has norm AND essential norm `(1+r)/(1-r)`.
  Compact/nuclear perturbation of K_h cannot repair the unattenuated Cayley equation.

Additional checked corpus parent: `GraphSaturationCore.linearGraphSubmodule_closure_eq_top_iff_annihilator`
already gives the abstract graph criterion. `CompleteResolutionCofinalConditioningLaw` already
turns dense collapsing outputs into full vertical fibre. The source-specific two-prime application
is the audit delta, not a claim to have invented a graph-saturation theory.

**Verdict:** `FALSE` for a closable prime-only action on this synthesis space; `BRIDGE` for the
valuation action and its exact singular cost. These do not falsify the finite modular identities
or the separate coefficient-space representation.

## Failure-driven next constraint

The forced reinterpretation is precise: completion in the Burnol energy norm forgets enough
prime ancestry that each individual prime already spans the whole space. Prime-dependent
operations cannot then be treated as ordinary operators on that completed observation space.
Changing to the valuation clock repairs that compatibility but recovers a universal shift
boundary singularity, not a new arithmetic charge.

No new primary conjecture is frozen: neither adding a source-marked norm nor declaring a relative
graph would yet meet the conjecture-distance gate. The next discriminator must be an actual
Poisson-derived operation that retains source ancestry and differs from these generic Cayley
domains. It must predict the same Xi/Euler boundary comparison, not assume it. An immediate
hostile test for any proposed replacement is whether its claimed arithmetic obstruction already
occurs with one arbitrary geometric rate ladder and no cross-prime multiplication.
