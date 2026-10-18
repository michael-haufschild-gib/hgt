# Active sawtooth interpolation and sharp conditioning

- **ID:** thim-active-sawtooth-interpolation-conditioning
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Scope:** Explicit realization of arbitrary squarefree power-sample data with prescribed
  harmonic scalar; coordinate indispensability and exact coefficient noise amplification.

## Plan and gates

1. [x] Read current field motivation, traps, prior recovery, and corpus inversion tools.
2. [x] Dependency-closed paper proof of interpolation and sharp conditioning.
3. [x] Formalize a new leaf, audit actual source and every declaration's axioms.
4. [x] Wire umbrella, index/lint, persist ledger/memory, audit artifacts, clean scratch.

`update_plan` is unavailable; this card tracks work. Field README is read-only.

## Corpus audit

Hybrid search for active sawtooth interpolation and sharp stability found the previous
recovery/stability leaf, with no matching right inverse or sharp condition theorem.
Coverage: complete inventory snapshot, no partial search; compiler freshness mixed,
so candidate applicability must be checked in Lean. BVI lexical search found
`sievePrefixInterpolatingWeight_realizes`, which concerns initial prefix discrepancies,
not squarefree active self samples. Mathlib's restricted Möbius inversion supplies
the needed divisor-closed squarefree-domain inverse. No external novelty claim.

## Paper proof [PROVED HERE]

Normalize prescribed data by a(1)=0. Let L(a,d) be the existing inverse
`2d/(d-1) * sum_{uv=d} mu(u)*a(v)`. Set c(d)=L(a,d) on squarefree d in [2,N],
and zero elsewhere. On the divisor-closed set of squarefree n<=N,
`c(d)-c(d)/d=2*sum_{uv=d}mu(u)*a(v)` (also zero at d=1). Restricted Möbius
inversion gives `A_N(c,j)=a(j)` at every squarefree j in [2,N]. Radical invariance
moves all these observations to j^m for any m>=1. Unit shifting by H-H_c prescribes
an arbitrary finite harmonic sum H when N>=1, without changing any active sample.

Prescribing a single sample to be one and every other sample zero produces a
nonzero coefficient vector invisible after deleting that coordinate, even with
harmonic calibration fixed. Thus the canonical squarefree sampling scheme has
no redundant coordinate. This does not claim that every other sampling scheme
must contain the same observation positions.

For d>=2, the unit-normalized inverse row is
`L(a,d)=K_d*sum_{j|d,j!=1}mu(d/j)*a(j)`, where `K_d=2d/(d-1)>0`.
Hence sample error at most E on these divisors gives coefficient error at most
`K_d*(number of nonunit divisors of d)*E`. If d is squarefree, this is exact:
prescribe `a(j)=mu(d/j)` at nonunit j and a(1)=0. Each inverse summand is one
because every quotient divisor is squarefree. Interpolation realizes this bounded
sample pattern by a squarefree-supported weight at every horizon N>=d, with
any chosen harmonic scalar and every common power exponent.

Taking a second weight with the same harmonic scalar and zero active samples turns
this into an exact coefficient-error witness. Consequently, for every fixed H,
the universal implication `sample sup-error<=1 => |c(d)-b(d)|<=C` on the calibrated
squarefree class holds if and only if C is at least the displayed divisor-count
constant. The previous recovery equivalence also proves that synthesis recovers
the original visible coefficients when applied to their own power-sample data.

## Boundaries

The sharp constant is divisor-count dependent; distant power sampling itself adds
no amplification. This is a theorem for general squarefree-supported weights, not
a sign or stability statement specific to the Möbius/damped families. No recovery
of coefficients outside [1,N], no numerical experiments, no full builds, no axioms.

## Formal verification

- Leaf: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ActiveSawtoothInterpolationAndSharpConditioning.lean`.
- 20 public theorems, three public definitions, one private helper. Actual source
  audited with `lake --old env lean -o ... ActiveSawtoothInterpolationAndSharpConditioning.lean`:
  exit 0, no warnings. All 24 declaration axiom closures contain exactly
  `propext`, `Classical.choice`, `Quot.sound`; axiom scratch exit 0.
- Source SHA-256: `eb861d1b5d56ee2a5fa07b71b3b72b2b89364181f69537fcb988694694bab3a2`.
- Fresh compiled artifact, unique umbrella import, MainTheorems reachability, all
  23 public generated API entries, forbidden-token absence, and whitespace verified.
- Index exit 0. Authoritative `scripts/formal_tools.py lint --check-generated` exit 1:
  seven unrelated unwired leaves and existing THIM field-umbrella registration.
  No finding names this leaf; no stale generated file. Global clean status is not claimed.
- Evidence: `logs/thim-interpolation-{lean,axioms,index,lint}.txt`,
  `logs/thim-interpolation-audit.json`. Facts: `logs/thim-radical-sawtooth-knowledge.md`.
- Seven owned scratch files removed; all owned jobs terminal. No README edits,
  numerical experiments, full builds, added axioms, heartbeat changes, or commits.
- Fifth connected contribution completed; open-ended research goal remains active.
