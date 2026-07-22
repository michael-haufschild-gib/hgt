# Xi--Suzuki pole--zero normal-form universality law

- **ID:** xi-suzuki-pole-zero-normal-form-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-29 theorem-first scan of Suzuki shifted-target, exterior-sewing, Carleman/Weyl, and Euler-defect modules
- **Statement:** At every Xi zero, five Suzuki coordinate systems have the source-independent order
  ladder `+1, -1, -1, -1, -2`. Their zero/pole trailing coefficients satisfy exact reciprocal
  products `1`, `1`, and the oriented Weyl product `-1`.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and downstream consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs read

1. `meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero` and
   `meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero` turn every Xi zero into a simple
   zero with coefficient `z²/m`, independently of target shift.
2. `meromorphicOrderAt_suzukiCrossSewnNormalizedExterior_eq_neg_one` and its trailing-coefficient
   theorem give a simple pole with coefficient `m/z²`, independently of opposite shifts, source
   functions, interval parts, and gauges.
3. The affine-sewn normalized analogues give the same simple-pole germ for every distinct pair of
   source shifts and every target shift.
4. The admissible exterior Weyl quotient has simple-pole coefficient `-m/z²`.
5. Its Euler defect has exact order `-2` at every Xi zero; `XiC_zero_ne` supplies the sharp nonzero
   base-point hypothesis.

## Internal noncollision audit

Three `scripts/formal_tools.py research` searches recovered all component theorems but no common
consumer. Existing modules call the separate pole coefficients universal, but none relates them to
the reciprocal shifted-target zero coefficient or states the five-chart order ladder. Existing
universality laws do not mention Suzuki coordinates.

## Paper proof

Fix an Xi zero `z`, source shifts `alpha != beta`, a target shift `gamma`, and analytic source and
interval functions nonzero at `z`. The shifted-target theorem gives order `+1` and coefficient
`z²/m`, where `m > 0` is Xi's analytic order. Cross sewing and affine sewing each give order `-1`
and coefficient `m/z²`. The admissible Weyl quotient gives order `-1` and coefficient `-m/z²`.
Since Xi has no zero at the centered origin, `z != 0`; since `m > 0`, its complex cast is nonzero.
Cancellation therefore yields target-times-cross `= 1`, target-times-affine `= 1`, and
target-times-Weyl `= -1`. Finally the Euler-defect pole theorem lowers the Weyl order from `-1` to
`-2`. No RH assumption, estimate, source limit, or numerical computation enters.

## Lean formalization

`RHTower/XiSuzukiPoleZeroNormalFormUniversalityLaw.lean` defines a fourteen-field local certificate
and constructs it at every Xi zero from the component theorems. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiSuzukiPoleZeroNormalFormUniversalityLaw.lean
```

passed after namespace qualification and explicit target-shift inference corrections.

## Hostile literature noncollision audit

Primary-source searches and source-text inspection found adjacent, noncolliding results. Suzuki's
canonical-system paper studies the meromorphic-inner ratio
`xi(1/2-omega-iz)/xi(1/2+omega-iz)` and its de Branges Hamiltonian
([arXiv:1204.1827](https://arxiv.org/abs/1204.1827)); it does not construct affine/cross sewing or
the local coefficient duality here. Suzuki's screw-function paper develops RH equivalents,
Titchmarsh--Weyl functions, and shifted `Psi_omega`
([arXiv:2206.03682](https://arxiv.org/abs/2206.03682)), but its full TeX contains no cross-sewn,
affine-sewn, Euler-defect, trailing-coefficient, or reciprocal-coefficient statement. The 2026
Weil-form paper tracks Xi-zero multiplicities in finite-interval operator limits
([arXiv:2606.09096](https://arxiv.org/abs/2606.09096)); its full TeX likewise contains none of the
five-chart normal form or `1, 1, -1` products. This is a noncollision audit, not a priority claim.

## Log

- 2026-07-21 — Found bottom-up in Suzuki carrier scan. Rejected a conjunction of global
  RH-equivalent analyticity criteria; retained pointwise zero/pole normal form and its new exact
  reciprocal coefficient laws. Paper proof closed; Lean and literature audits pending.
- 2026-07-21 — Fourteen-field law formalized; exact direct Lean check passed. Hostile search plus
  primary TeX inspection of Suzuki 2012, 2023, and 2026 found adjacent canonical-system,
  screw-function, and Weil-operator results but no coefficient-duality collision.
