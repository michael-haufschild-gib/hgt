# T2 Wold-charge lower-semicontinuous collision no-go

- **ID:** t2-wold-charge-lsc-collision-no-go
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · T2 scalar-descent survivor
- **Statement:** No compact-open sequentially lower-semicontinuous scalar reporter is exact on reflected Wold orbit-charge energy across the canonical two-simple-to-double symmetric-shift collision.

## Goal

Kill T2's lower-semicontinuous coefficient-faithful scalar survivor. Together with the formalized
upper-semicontinuous escape no-go, this excludes every one-sided semicontinuous scalar descent and
forces source marking, a non-scalar carrier, or a genuinely singular relative selector.

## Gates

- [x] 0 → 1  in-progress: exact corpus energy and collision laws; explicit attack
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted build, axioms audit
- [ ] 3 → 4  publication-ready

## Corpus basis

- `principalPartOrbitChargeEnergy_two_single`: two off-wall orbit atoms of multiplicity `m` have energy `2m²`.
- `analyticOrderAt_symmetricShiftProduct_zero_shift`: collision doubles analytic multiplicity.
- `analyticOrderAt_symmetricShiftProduct_pair_eq_of_no_overlap`: separated translates retain multiplicity.
- `continuousAt_divisorPairing`: compactly supported linear-multiplicity divisor pairing is continuous.

## Conjecture and attack

Take `ρ = 3/4` and positive real shifts `aₙ = 1/(8(n+1))`. Let
`Fₙ(z)=((z+aₙ)-ρ)((z-aₙ)-ρ)` and `F∞(z)=(z-ρ)²`. Then `Fₙ→F∞` compact-open,
each `Fₙ` has two distinct simple off-wall roots `ρ±aₙ`, and `F∞` has one double off-wall root
`ρ`. Exact Wold energies are respectively `4` and `8`. Lower semicontinuity would give
`8 ≤ 4+ε`; choose `ε=1`.

## No-go closure

- **Exact killing theorem/mechanism:** quadratic multiplicity energy increases under collision, contradicting compact-open lower semicontinuity.
- **Strongest positive survivor:** collision-additive scalar multiplicity weights are exactly linear weights; linear divisor mass survives this collision.
- **New insight:** scalar T2 cannot retain Wold's quadratic multiplicity energy in either semicontinuous direction; collision-compatible descent must linearize multiplicity before any noncompact completion.
- **Status:** conjecture frozen after corpus and literature audit; paper proof next.

## Log

- 2026-09-01 — created in 1-in-progress after corpus-derived conjecture freeze.
