# Fixed-width FCRJ PNT decay boundary

- **ID:** fcrj-fixed-width-pnt-decay-boundary
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/critical-multiplicative-compensated-cancellation-rh.md
- **Statement:** Corpus power-log PNT unconditionally forces every fixed-aperture, fixed-width complete physical FCRJ carrier energy to tend to zero.

## Goal

Determine strongest unconditional consequence ordinary PNT supplies after exact theta--Abel
reduction, while separating qualitative extinction from RH-equivalent `X^-1 polylog(X)` rate.

## Gates

- [x] 0 → 1  in-progress: fixed-width carrier and normalized theta source identified
- [x] 1 → 2  fully-proven: dependency-closed paper proof and Lean proof
- [x] 2 → 3 formalized: direct check, targeted build, and axiom audit pass; global lint blocked by unrelated unwired modules
- [ ] 3 → 4  publication-ready: standalone exposition and external novelty review

## Statement

Put

```text
q(h)=[theta(exp h)-exp h] exp(-h),
E_(A,c)(m)=Energy(P(A,m,m+c),A,m,m+c).
```

For `c>=0`, if `|q(h)|<=B` throughout `[m-A,m+c]`, then for every `u in [0,A]`

```text
|R(m,m+c;u)| <= (2+c)B,
E_(A,c)(m) <= A((2+c)B)^2.
```

The corpus power-log PNT proves `q(h)->0`. Uniformity on a bounded translated band is immediate,
so for every fixed `A>0` and `c>=0`,

```text
E_(A,c)(m) -> 0 as m -> infinity.
```

## Proof

The two endpoint terms each cost `B`. Absolute interval integration costs at most `cB`; local
integrability follows from measurability of the Chebyshev step and constant domination on the
band. Feed `(2+c)B` into exact theta--Abel energy provider. For convergence, choose a response
tolerance whose squared provider budget is below the requested energy tolerance, then apply PNT
uniformly once `m-A` passes its threshold.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeAperturePNTDecay.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Targeted build: PASS
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- Capstones:
  - `abs_xiPhysicalPrimeLogThetaAbelResponse_le_of_normalizedThetaError`
  - `xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_of_normalizedThetaError`
  - `tendsto_xiPhysicalPrimeLogPNTCarrierEnergy_zero`

## No-go closure

- **Exact killing mechanism:** Ordinary pointwise PNT controls normalized theta error only at its
  zero-free-region scale. Exact provider squares this error but creates no `exp(-m)` factor.
- **Strongest positive survivor:** Fixed-width complete carrier energy nevertheless tends to zero
  unconditionally, with exact response constant `2+c` and aperture cost `A`.
- **New insight:** Remaining FCRJ burden is quantitative, not qualitative existence or source
  convergence: required `X^-1 polylog(X)=exp(-m) poly(m)` scale must come from mean-square
  cancellation beyond pointwise PNT.
- **Status:** Survivor paper- and Lean-proved; RH-rate core remains open.

## Novelty audit

PNT and bounded-band uniformity are classical. Candidate-new content is restricted to transport
through exact physical theta--Abel/FCRJ provider and resulting qualitative carrier theorem. No
claim is made that ordinary PNT proves FCRJ rate or RH.

## Log

- 2026-08-27 — paper proof, Lean proof, targeted build, umbrella wiring, and axiom audit complete
