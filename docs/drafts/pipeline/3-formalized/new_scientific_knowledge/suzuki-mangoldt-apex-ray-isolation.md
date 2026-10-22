# Suzuki--Mangoldt apex ray isolation

- **ID:** `suzuki-mangoldt-apex-ray-isolation`
- **Stage:** 3 — formalized in Lean 4
- **Type:** frontier falsifier / exact source classification / positive survivor
- **Parent:** `suzuki-positive-arch-mangoldt-quadrature-deficit.md`
- **Target:** `SUZUKI-APEX-BLOCK-TRANSPORT`
- **Scientific status:** `[PAPER PROVED] [LEAN FORMALIZED] [SOURCE-SPECIFIC] [NOT RH]`

## Question

At width `L = log 2`, aperture `a_n = log(2n)/2`, the Mangoldt node
`tau_n = 2 log n` is the unique positive-lag apex of the Suzuki sample channel.  Can its missing
pointwise transport mass be paid by flank atoms in the same Euler valuation ray?

## Exact proposed classification

For integers `n,m >= 2`, prove

```text
A_(a_n)(tau_m)
 =sqrt(m) max(0, log 2-|log(m/n)|).                       (AR1)
```

Consequently the aligned channel is supported exactly on the multiplicative annulus
`n/2 < m < 2n`.  For one prime-power ray `m=2^j`, `n=2^k`, the only exponent in this open annulus
is `j=k`; the neighboring valuations `2^(k-1)` and `2^(k+1)` lie at the zero boundary.  Hence

```text
A_(a_(2^k))(tau_(2^j))>0  iff  j=k.                      (AR2)
```

## Frontier consequence

If `(AR2)` holds, primewise/valuation-diagonal apex blocks are impossible.  The apex atom is
isolated inside its own Euler ray, so every viable `SUZUKI-APEX-BLOCK-TRANSPORT` must mix distinct
prime labels before positivity or capacity-one transport is imposed.  This is stronger than the
existing pointwise-cell no-go, which allows an unspecified block source.

The positive survivor is the exact annular kernel `(AR1)`: it identifies the only legal flank
pool and turns the next problem into a cross-prime block incidence theorem on
`n/2 < m < 2n`, with the restricted-Weil/Robin boundary channel retained.

## Falsifiers

- Any same-ray exponent `j != k` with positive aligned channel value falsifies `(AR2)`.
- A proof which uses only unique maximality does not establish ray isolation; the zero support
  boundary at ratios `1/2` and `2` is load-bearing.
- Cross-prime mixing is a conclusion only after `(AR1)` is derived from the actual rectangular
  channel, not from a replacement tent.

## Proof

The positive channel is the sum of its fixed and moving tents.  At
`L=log 2`, `t=2 log m`, and `m>=2`, the fixed height is

```text
log 2 - t/2 = log 2 - log m <= 0,
```

so the fixed channel vanishes.  At aperture `a_n=log(2n)/2`, the moving center is

```text
2a_n-log 2 = log n.
```

Its exponential prefactor is `exp(t/4)=exp(log m/2)=sqrt m`; substituting these two
identities into the actual channel gives `(AR1)`.

The positive support condition is

```text
|log(m/n)| < log 2,
```

equivalently `n/2<m<2n`.  If `m=b^j`, `n=b^k`, `b>=2`, and `j!=k`, the larger power is
at least `b` times the smaller, hence at least twice the smaller.  It lies outside the open
annulus (on its boundary when `b=2` and the exponents are adjacent), so its sample is zero.
At `j=k`, `(AR1)` is `sqrt(b^k) log 2>0`.  This proves `(AR2)` for every base `b>=2`,
strictly stronger than the proposed dyadic statement.

## Novelty audit

- Suzuki's 2023 paper derives the global triangular test as the autocorrelation of one rectangular
  function and relates it to the Weil functional.  It does not contain the moving two-edge aperture,
  the aligned Mangoldt sample law `(AR1)`, or the power-ray isolation theorem.
- Suzuki's 2026 screw-function framework retains the global Weil/Mangoldt quadratic form and localized
  operators.  Source-text search found no rectangular/tent aligned-aperture or prime-power ray theorem.
- Exact corpus search found no prior `n/2<m<2n` aligned-support classification or same-power-ray result.

This is an exact-source noncollision audit, not a claim of literature priority.

## Lean realization

Module `RHTower/Suzuki/SuzukiMangoldtApexRayIsolation.lean` proves:

- `suzukiMangoldtAlignedApex_sample_eq` — `(AR1)`;
- `suzukiMangoldtAlignedApex_sample_eq_zero_of_outside` — closed complement of the annulus;
- `suzukiMangoldtAlignedApex_self_pos` — positive diagonal;
- `suzukiMangoldtAlignedApex_samePowerRay_pos_iff` — all-base power-ray isolation.

`RHTower/RiemannHypothesisSOTA2026.lean` imports the module immediately after the parent apex-lock
module.

## Gates

- [x] prior pointwise transport failure audited
- [x] dependency-closed proof of `(AR1)`
- [x] support and all-base power-ray classification `(AR2)`
- [x] external parent/noncollision audit
- [x] Lean formalization and umbrella wiring
