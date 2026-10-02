# SZ: uniform matched even source bound

- **ID:** sz-matched-even-source-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** SZ, actual shifted prime-polar-Gamma covariance
- **Statement:** For every positive aperture, the actual even covariance energy at anchor `1/2` is at most `1/2`; its response's squared form norm plus physical mass is at most `1/8`.

## Exact objects

Write the physical bounded remainder as `B = k I + P - T`, with the
literal scalar, rank-two pole operator and finite von Mangoldt translation
operator from `CCMRestrictedWeilBoundedRemainder`. Let `c = ‖B_interval‖+1`
be the prescribed shift, and `q` the existing shifted form. No shift is
changed. The coordinate equivalence is unitary, so `‖B‖ ≤ ‖B_interval‖`.

Let `w = suzukiTaRawCoalescingEven a (1/2)`, `u = suzukiTaToFormCLM a w`,
and `f = ccmArchimedeanFormToAperture a u`. The source energy is the
unscaled `E = suzukiTaCoalescingEvenEnergy a (1/2) = ‖w‖²`.

## Dependency-closed paper proof [PROVED HERE]

For arbitrary physical `g`, choose a cofinal modulation clock on which
every one of the finitely many translation phases at the aperture's
prime-power shifts tends to one. Simultaneous finite phase recurrence
supplies this clock, without an independence assumption on those shifts.
Modulation preserves physical norm. Riemann-Lebesgue makes each of the
two fixed pole pairings tend to zero. Translation covariance and the
finite sum therefore give

`Re <B M_j g, M_j g> → Re(k <g,g> - <Tg,g>)`.

Each left side has absolute value at most `‖B‖ ‖g‖²`. Passing to the limit
proves the same bound for the right side. Only bounded physical operators
are modulated; no Gamma-energy estimate under modulation is asserted.

The exact shifted form identity consequently gives, for every existing
Suzuki Hilbert vector `z`, with response `v` and physical vector `h`,

`‖v‖form² + ‖h‖² ≤ ‖z‖Ta² - Re <Ph,h>`.

Indeed the scalar-minus-prime term is at least `-‖B‖ ‖h‖²`, while the
shift contributes `(‖B_interval‖+1) ‖h‖²`.

For the selected even source, covariance reflection fixes its physical
response. The two exponential pole charges are equal, and their average
is its cosh charge. The actual Riesz identity identifies that charge with
the real number `E`. Thus the complete polar energy is `2E²`. Substitution
gives

`0 ≤ ‖u‖form² + ‖f‖² ≤ E - 2E²`.

It follows that `E ≤ 1/2`. Completing the square gives
`E - 2E² = 1/8 - 2(E-1/4)² ≤ 1/8`, proving the response bound.

## Scope and remaining hard problem

This estimates one actual source channel uniformly, including its Gamma
form norm. The odd channel has negative polar energy, so this argument
does not bound it. Normalized V2 energies and completed formation
production are different quantities. Weighted aperture increments still
retain the shift increment times physical mass. Odd-source control and
the full source-derived signed Wronskian remain open; RH is unresolved.

## Verification

- `CCMRestrictedWeilPolarFreeShift.lean`: direct foreground leaf audit passed.
- `SuzukiMatchedEvenSourceBound.lean`: direct foreground leaf audit passed.
- Both final leaf audits use `lake --old env lean`; no umbrella build.
- Both leaves are wired into `GaloisForLFunctions/RHTower.lean`.
- All six public theorem axiom queries pass: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint ran and exited1 on14 unrelated unreachable modules. Neither new leaf is unreachable; no forbidden declaration was reported. Global lint remains non-green; exact unrelated names are recorded in the ongoing SZ working log.

The public contracts are `abs_ccmPolarFreeRemainderQuadratic_le`,
`suzukiMatchedEvenFormResponse_pole_charges`,
`suzukiMatchedEvenFormResponse_polar_energy`, `suzukiTa_energy_sub_polar_ge`,
`suzukiTaCoalescingEvenEnergy_half_le`, and
`suzukiMatchedEvenFormResponse_uniform_bound` (all in namespace `RHTower`).

## Log

- 2026-10-02 — extracted finite-prime modulation argument and completed paper proof; formalization underway.
- 2026-10-02 — both direct leaf audits and all six axiom queries pass; umbrella imports wired. RH goal remains active.
