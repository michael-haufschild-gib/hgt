# Poisson–Weil decomposition at the critical scale

- **ID:** poisson-weil-critical-scale
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` §2.5 (thesis, target theorem, theta bridge).
- **Statement:** Carry the bounded-overlap Poisson repayment identity, as an identity, to every
  overlap `c` and horizon `N`; identify exactly what it pays at the critical scale.

## Goal

Thesis (§2.5): positivity at bounded overlap is an identity (Poisson summation of `|φ̂|²` on the
successor lattice); the breakthrough is to carry that identity, not an estimate, into the scaling
where RH lives. Two theorems are requested:

- **A. Poisson–Weil decomposition** `W(φ,c,N)=P+Z`, `P` explicit positive (Poisson remainders and
  archimedean zero density), `Z` the exact zero term.
- **B. One Poisson structure for theta and atomic positivity**: a Poisson-remainder identity for
  the theta center hierarchy.

## Notation

Pole mode `y_n=n^{-1/2}`, `X_N(s)=Σ_{n≤N}n^{-s}`. Euler–Maclaurin boundary
`B_N(s)=emPole N s − s·emTail N s`, so `X_N(s)=ζ(s)−B_N(s)` for `Re s>0`, `s≠1`
(`RHTower.zeta_eq_emCarrier_sub`). Bump factor `Φ_w(ρ)=ĝ(γ_ρ)·conj ĝ(conj γ_ρ)`, `g=φ(·/w)`.

## Approach (working)

1. **A1 (exact, every `c,N`).** On the zero side the pole-mode energy is
   `Σ_ρ m_ρ Φ_w(ρ) B_N(ρ) B_N(1−ρ)`: the Dirichlet polynomial vanishes at every zero up to the
   Euler–Maclaurin boundary of the horizon. No other information about zeros enters.
2. **A2 (Li term).** `emPole N ρ · emPole N (1−ρ) = N/(ρ(1−ρ))` exactly; the pole–pole part is
   `N Σ_ρ m_ρ Φ_w(ρ)/(ρ(1−ρ))`, a weighted first Li coefficient.
3. **A3 (Poisson dual).** The oscillatory part of `B_N` is the dual sum
   `χ(s) Σ_{k≤|t|/2πN} k^{s−1}`; its index `k` is the shell index of
   `E(c)=(2/M)Σ_k k⁻¹∫_{kc}^∞P`. Synthesized local tests split into a low-pass part (the
   semilocal Weil form) and Poisson-dual aliasing copies.
4. **A4 (critical curve).** Aliasing energy ≈ zero density × profile spectrum; the RH transition
   for local modes sits where `log N · P_φ(c) ≍ 1`.
5. **B.** Seek the analogue of A3 for the center tails `U_k(r)` of the theta hierarchy.

## Gates
- [x] 0 → 1  well-posed; source-pure (no zero-indexed inputs in P)
- [ ] 1 → 2  paper proofs of A1–A4, B
- [ ] 2 → 3  Lean

## Log
- 2026-10-30 — created; A1 reduced to `Wsummand_atomicTest` + `zeta_eq_emCarrier_sub`.
