# Positive shared-plane Suzuki Stokes product no-go

- **ID:** CCM-FU-SHARED-POS-SL2
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `rh-current-frontier-map.md` · CCM-FU sole live source gate
- **Statement:** For `x_A(n)=suzukiCenterStokesCartanCell A n` and the canonical increasing-label product `P_A=∏_{n=2}^A [[1+x_A(n),sqrt(x_A(n))],[sqrt(x_A(n)),1]]`, the canonically completed observable `2 log((P_A)₀₀)+Σx_A(n)^2-regularWard(log A)` tends to `+∞` along `A=20n`.

## Goal
Kill canonical positive shared-`SL₂` ordered fusion as CCM-FU's required nonlocal producer. This is source-pure: actual Suzuki cells, natural checkpoint order, literal quadratic counterterm, literal regular-screw subtraction. It does not assume Green cancellation or RH.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## RH chain and attack
Write `D_A=∏(1+x_A(n))` and `C_A=log((P_A)₀₀)-log D_A≥0`. Exact completion gives
`W_A=Green(log A)+2*localCubicRemainder(A)+2*C_A`.

At `A=20n`, isolate contiguous labels `2n<k≤5n`. The corpus Chebyshev block theorem gives prime log-mass at least `n/4`, hence at least `n/(4 log(5n))` primes. Every such prime satisfies
`x_A(p)≥δ_n:=log(2n)/(4*sqrt(20n))`. Pairing consecutive prime factors in the positive `SL₂` word gives the exact multiplicative surplus
`floor(m/2)*log(1+δ_n/4)`, hence `≫sqrt n`. Inserting proper prime powers can reduce normalized surplus only by their local diagonal mass; the corpus square-root-width bound makes this `O(log² n)=o(sqrt n)`. Concatenation of positive blocks cannot reduce normalized surplus. Finally `Green(log(20n))/sqrt n→0`, while local cubic remainder is nonnegative. Therefore `W_(20n)→+∞`.

## Hostile attacks / exact scope
- Canonical increasing source order only; no claim yet for arbitrary cutoff-dependent permutations.
- Positive same-phase opposite-root amplitudes only; phase-twisted or indefinite shared planes survive.
- Any packet-growing counterterm that explicitly subtracts `C_A` survives, but becomes the next object requiring an independent coercive origin.
- Green cannot cancel the surplus: corpus proves `Green(log A)=o(sqrt A)` unconditionally.
- Proper prime powers cannot cancel it: their window von-Mangoldt mass has square-root width.

## Prior-art audit through 2026-08
Suzuki 2026 leaves convergence of nonlocal finite-interval realizations conjectural; Connes–Consani–Moscovici 2025 leave spectral/determinant convergence unproved. Total-positivity literature explains positivity of positive root-subgroup words but does not state this Suzuki-source `sqrt A` surplus/no-go. No collision found.

## No-go closure
- **Exact killing theorem/mechanism:** pending proof and Lean formalization.
- **Strongest positive survivor:** positive shared-plane path expansion creates a new prime-density Cartan surplus at the same `sqrt A` scale as atomic/regular Ward masses.
- **New insight:** nonlocality alone is insufficient; a survivor must introduce phase/indefinite cancellation or a source-derived packet-growing subtraction before positivity.
- **Status:** internal corpus and primary-literature audits complete; paper proof in progress.

## Log
- 2026-09-01 — conjecture frozen after corpus hard-lock audit.
