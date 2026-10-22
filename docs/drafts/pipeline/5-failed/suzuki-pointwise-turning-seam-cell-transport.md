# Suzuki pointwise turning-seam cell transport — retired

- **Stage:** 5 — failed/retired
- **Type:** `[FALSIFIED]` pointwise per-atom transport
- **Parent:**
  `suzuki-positive-arch-mangoldt-quadrature-deficit.md`
- **Positive survivor:**
  `../3-formalized/new_scientific_knowledge/suzuki/suzuki-mangoldt-apex-lock-rigidity.md`

## Killed conjecture

Assign every seam atom `w_n delta_(tau_n)` a positive-volume Lebesgue cell `I_n` of mass `w_n`,
with cells used at multiplicity at most one and

```text
A_a(tau_n) <= A_a(t)  for every t in I_n.
```

This was `SUZUKI-TURNING-SEAM-BICAUSAL-SPLICE` in its pointwise form.

## Exact killing mechanism

Take `L=log 2` and aperture `a_n=(1/2)log(2n)`.  For every `n>=4`, the actual source node
`tau_n=2log n` is the unique positive-lag maximizer of the Suzuki positive channel.  Hence its
value-dominating superlevel is singleton `{tau_n}` and has zero Lebesgue measure.  Whenever
`Lambda(n)>0`, its required cell mass `2Lambda(n)/n` is strictly positive.  Powers `n=2^k` make
the obstruction cofinal.

Allowing non-interval cells, measurable densities bounded by one, or adaptive selection does not
repair pointwise domination: all such mass remains supported on a null superlevel.  The failure is
atomicity at a strict apex, not overlap bookkeeping between past and future interval partitions.

## Positive survivor and representation lesson

The exact apex-lock classification is paper-proved in the linked Stage-2 card and Lean-proved in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiMangoldtApexLock.lean`.  It identifies a source-aligned
rigidity absent from the prior transport picture.

Representation lesson: individual atomic payment is wrong primitive at turning seam.  A successful
transport must be blockwise, allowing flank surplus to compensate apex deficit before enforcing
capacity one.  The stronger successor is `SUZUKI-APEX-BLOCK-TRANSPORT`, not a weakened cell rule.

## Status

- `[FALSIFIED]` per-atom pointwise seam cells.
- `[LEAN-PROVED]` cofinal Mangoldt apex-lock rigidity.
- `[OPEN CORE]` source-canonical block transport with nonnegative aggregate surplus and retained
  Gamma boundary charge.
