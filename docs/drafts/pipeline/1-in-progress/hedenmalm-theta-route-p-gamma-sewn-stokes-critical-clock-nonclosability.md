# Route-P critical Stokes clock nonclosability

- **ID:** `P-G74`
- **Stage:** `1-in-progress`
- **Type:** topology no-go / exact actual-prime graph-null witness / positive survivor
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-critical-information-schur-depletion.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalClockNonclosability.lean`

## Conjecture P-G74.A: Gamma--Schur Hardy completion can carry the critical Stokes clock

Let `j` be the coherent arithmetic Schur kernel map into reciprocal-prime Hardy space. Let `T`
apply the exact critical inverse Stokes tilt

```text
W(p) = log(p)/r_p * (1+r_p^2)/(c_p(1-r_p)),   r_p^2=1/p,
```

before the same Hardy tail embedding. Conjecture: `T` is sequentially closable through `j`, so its
graph closure could supply the missing non-diagonal Feshbach carrier.

**Verdict: false, retired unconditionally.** Choose an actual prime `R_p` with
`p^2<R_p<=2p^2` and the two-prime witness

```text
u_p = p/W(p) (delta_p-delta_Rp).
```

Lean proves `j(u_p) -> 0`, while `T(u_p) -> e_0`, the nonzero first Hardy basis vector. Therefore
`T` is not sequentially closable through `j`.

## Strongest positive survivor

The obstruction is topological, not merely quantitative. Exact critical source estimates prove

```text
log(p)/r_p < W(p) <= 14 log(p)/r_p,
p W(R_p)/(W(p)R_p) <= 42 r_p,
```

so the Stokes clock sees one half-height more than reciprocal-prime Hardy geometry. Any valid
Gamma/polar completion must preserve a graph/Köthe topology controlling that critical clock before
Hardy or scalar compact compression. This requirement is forced by actual primes, not an abstract
countermodel.

## Lean realization

Headline declarations:

- `gammaSewnMobiusApertureStokesCriticalInverseTilt_eq`;
- `criticalStokesInverseTilt_lower` and `criticalStokesInverseTilt_upper`;
- `criticalFarStokesSusceptibilityRatio_le`;
- `tendsto_primeHardyKernelMap_criticalStokesNullSequence`;
- `tendsto_primeCriticalStokesClock_nullSequence`;
- `not_closable_primeCriticalStokesClock`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalClockNonclosability
Build completed successfully (12727 jobs).
```

## New universal principle

P-G72 mass excess and P-G73 inadequate diagonal depletion are shadows of one loss-of-topology
law: scalarization forgets precisely the half-height direction on which critical inverse Stokes
transport becomes singular. Schur elimination after this quotient cannot repair information the
quotient erased. Completion order must be

```text
source graph/Köthe completion -> Gamma/polar Schur limit -> positive square pushforward,
```

never Hardy/scalar compression first.

## Next conjecture

Construct the critical clock graph carrier inside the already-built Deninger height Köthe source.
Prove finite Gamma-Schur valuation translations form a cofinal graph-Cauchy family there, identify
their exact limiting quadratic response, then test positivity and completed-seam moments before
any scalar compression.

## Honest boundary

P-G74 kills the coherent reciprocal-prime Hardy completion and forces a stronger source topology.
It does not construct the cofinal Gamma/polar Schur limit, identify its completed moments, or prove
RH.

