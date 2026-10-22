# Suzuki aperture-dressed wall light completion

- **ID:** `suzuki-aperture-dressed-wall-light-completion`
- **Stage:** 3 — formalized and Lean-audited
- **Type:** PRE-SPLIT HILBERT COMPLETION / LIGHT-CONE TRANSPORT / SHARP NO-GO
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `suzuki-critical-aperture-quarter-shift-current.md`,
  `suzuki-wall-field-light-cone-kernel-completion.md`
- **RH used:** no
- **Computation used:** no

## Frontier attacked

Raw critical wall field `omega_(p,e)(t)` carries exact far phase and forced FE/Xi-real light split,
but

```text
sum_(p,e) |omega_(p,e)(t)|^2
 =sum_n Lambda(n)/sqrt(n)
```

diverges.  Corpus no-go shows common positive subtraction after light splitting is generically
impossible on multi-height packets.  Therefore any genuine Hilbert completion must act on wall
field before positive/negative light projection.

Actual source already contains one such pre-split operation: real cubically normalized dyadic
aperture innovation

```text
iota_(h,a)(p,e)=xiMobiusCubicNormalizedInnovationFeature(h,a;(p,e)).
```

Scientific question was whether `psi=omega*iota` merely defines finite/depthwise current or is an
actual all-prime Hilbert carrier preserving forced light geometry.

## Theorem `SUZUKI-APERTURE-DRESSED-WALL-LIGHT-COMPLETION`

Fix `h>0`, `a>0`.  For every real height `t`, define

```text
psi_t(p,e)=suzukiCriticalApertureBoundaryAtom(h,a,t,p,e)
           =omega_(p,e)(t)*iota_(h,a)(p,e).             (1)
```

Then:

1. `psi_t` belongs to `ell^2(Nat.Primes x N)`;
2. reflection is exact:

   ```text
   psi_(-t)=conj(psi_t);                                (2)
   ```

3. pre-split light vectors

   ```text
   PsiPlus_t =(psi_t+I*psi_(-t))/2,
   PsiMinus_t=(psi_t-I*psi_(-t))/2                      (3)
   ```

   belong to same `ell^2` space and coordinatewise equal

   ```text
   PsiPlus_t(p,e) =ellPlus_(p,e)(t) *iota_(h,a)(p,e),
   PsiMinus_t(p,e)=ellMinus_(p,e)(t)*iota_(h,a)(p,e);   (4)
   ```

4. completed Gram kernels `P=<PsiPlus_u,PsiPlus_t>` and
   `N=<PsiMinus_u,PsiMinus_t>` are PSD on every finite height packet;
5. for completed reflected current

   ```text
   F(t,u)=I/2*(<psi_u,psi_(-t)>-<psi_(-u),psi_t>),
   ```

   exact all-prime Ward laws hold:

   ```text
   P-N=F,       F+N=P;                                 (5)
   ```

6. diagonal wall energy is exactly height-flat:

   ```text
   <psi_t,psi_t>=<psi_u,psi_u>   for all real t,u.      (6)
   ```

## Paper proof

Equation `(1)` is definitional: critical aperture atom is conjugated critical Gamma boundary
multiplied by real innovation, and conjugated boundary is wall field.  Realness of `iota` plus wall
reflection proves `(2)`.  Equations `(3)--(5)` are Hilbert-space polarization identities; `(4)`
shows they are not fitted completions but exact transport of already forced source light legs.

Only non-formal-looking point is all-prime Hilbert existence.  Critical Gamma density satisfies

```text
|omega_(p,e)(t)|^2
 =log(p)/p^(e+1) * exp(log(p^(e+1))/2)
 <=log(p).                                               (7)
```

At fixed prime, existing dyadic innovation Gram identity gives exactly

```text
sum_e iota_(h,a)(p,e)^2
 =|(h*sqrt(h))^-1|^2 * I_p(h;a,a),                      (8)
```

where `I_p` is dyadic innovation kernel.  Existing positive Szego bound gives

```text
0<=I_p(h;a,a)<=2/p^2.                                   (9)
```

Thus

```text
sum_e |psi_t(p,e)|^2
 <=2*|(h*sqrt(h))^-1|^2*log(p)/p^2.                    (10)
```

Right side is summable even after enlarging primes to natural numbers.  Tonelli for nonnegative
series proves `(1)` is `ell^2`.  Phase is unimodular, so each coordinate norm square and therefore
the completed diagonal is independent of height, proving `(6)`.

## Scientific-method result

### Hypothesis H1 — innovation before splitting repairs wall divergence

**Confirmed.**  It yields an actual all-prime Hilbert vector and transports both forced light legs
without post-split subtraction.

### Hypothesis H2 — this Hilbert vector alone proves rectangular Ward semiboundedness

**Falsified exactly.**  By `(6)`, its source energy is constant in height.  Subtracting that energy
from Xi rectangular curvature changes it only by a constant.  Therefore proving resulting defect
bounded below is still equivalent to proving Xi curvature bounded below, hence still RH.  Hilbert
existence solves cofinal divergence but not arithmetic height dependence.

This no-go prevents a false RH claim and materially narrows live problem.

## New open core

### `SUZUKI-RESOLVENT-RECTANGULAR-LIGHT-INTERTWINER` `[CONJECTURE]`

For one fixed width `L>0`, construct from Suzuki's actual restricted-Weil resolvent, marked Robin
trace, polar--Gamma block, and Neumann holonomy a division-free rectangular transfer
`T_(L,x)` acting on dressed wall Hilbert carrier such that

```text
Re xiScrewWindowCurvature(L,x)
 =||PPlus T_(L,x) psi_x||^2
  -||PMinus T_(L,x) psi_x||^2 + r_L(x),                (11)
```

with these source-forced properties:

1. `PMinus T_(L,x)` contains exact dressed negative-light vector in `(4)` plus exact holonomy
   Schur debt;
2. transfer is uniformly contractive on negative-light channel;
3. marked midpoint part pays exact halfgap square already formalized;
4. `r_L(x)` is uniformly lower bounded on logarithmic arithmetic mesh;
5. construction occurs before characteristic division and before any light split.

Then `(6)` bounds negative channel uniformly, positive channel is nonnegative, and `(11)` makes Xi
rectangular curvature uniformly lower bounded.  Existing unconditional rectangular completeness
connector gives RH.

First unresolved theorem is now actual operator/trace identity `(11)` and negative-channel
contractivity—not all-prime convergence, not choice of a completion leg, and not a restatement that
Xi curvature is positive.

## Falsifiers

- Observer innovation after light split does not qualify.
- An arbitrary Hilbert vector with height-flat energy does not qualify.
- Normalized characteristic quotient does not qualify; wall density cancels projectively there.
- Transfer omitting restricted-Weil resolvent or holonomy Schur term does not qualify.
- Any negative-channel transfer norm unbounded on logarithmic mesh falsifies proposed route.
- Any proof using RH, Xi zero reality, Weil positivity, or desired lower bound as premise is
  circular.

## Novelty audit

- Suzuki's screw function, Weil Hilbert space, and finite-interval operator program are prior work.
- Dyadic innovation Gram and raw wall light split are corpus parents.
- Internal search found no all-prime theorem joining actual critical Gamma boundary, cubic aperture
  innovation, and FE/Xi-real light completion, nor exact height-flat obstruction `(6)`.
- Targeted arXiv searches through 2026-07-22 found Suzuki's source papers but no statement matching
  `(1)--(6)`.  This is collision evidence only; specialist priority audit remains required.

## Formal status

Formalized in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiApertureDressedWallLightCompletion.lean`.

Umbrella-reachable through `GaloisForLFunctions.RHTower`. Direct foreground Lean check, final
module build, standard-axiom audit, and formal lint are recorded in the promotion audit below.
