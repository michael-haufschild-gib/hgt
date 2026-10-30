# Poisson–Weil decomposition at the critical scale

- **ID:** poisson-weil-critical-scale
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for A1–A3, B1; CONJECTURE for A4
- **Source:** `docs/reports/review-3010/obstacles-summary.md` §2.5 (thesis, target theorem, theta bridge).
- **Statement:** The bounded-overlap identity carries exactly to every overlap `c` and horizon `N`
  as the *horizon law*; its positive part is blind to the real parts of the zeros, and the theta
  source reads the same horizon boundary.

## Notation

`y` atomic coefficients on `1≤n≤N`, `x_n=√n y_n`, Möbius transform `a=x*μ` (so `x=a*1`).
`X_M(s)=Σ_{k≤M}k^{-s}`. Horizon boundary `B_M(s)=M^{1−s}/(s−1)−s·emTail M s`, so
`X_M(s)=ζ(s)−B_M(s)` on `Re s>0`, `s≠1`. Möbius horizon
`H_a(s)=Σ_{d≤N} a_d d^{-s} B_{⌊N/d⌋}(s)`. Bump factor `Φ_g(ρ)=ĝ(γ_ρ) conj ĝ(conj γ_ρ)`.
Depth of the horizon of `d`: `⌊N/d⌋`.

## Results

**A1. Horizon law (every vector, every `c`, every `N`).** For every C² compact atom `g`,
`W(f_y) = Re Σ_ρ m_ρ Φ_g(ρ) H_a(1−ρ) H_a(ρ)`.
Proof: `Σ_{n≤N}(a*1)(n)n^{-s}=Σ_{d≤N}a_d d^{-s}X_{⌊N/d⌋}(s)` (regroup `n=dk`); `ρ` and `1−ρ` are
zeros with positive real part, so `X_{⌊N/d⌋}=−B_{⌊N/d⌋}` there; the zero-side summand of an
atomic test is `m_ρ Φ_g(ρ) D(γ_ρ) conj D(conj γ_ρ)` with `D(γ_ρ)=X(1−ρ)`, `conj D(conj γ_ρ)=X(ρ)`.
The pole mode is `a=δ₁`: `W=Re Σ_ρ m_ρΦ_g(ρ)B_N(1−ρ)B_N(ρ)`.

**A2. Horizon charge.** `H_a=P_a−T_a`, `P_a(s)=(s−1)⁻¹Σ_d (a_d/d)N_d^{1−s}`, `N_d=d⌊N/d⌋≤N`.
`emPole N s·emPole N (1−s)=N/(s(1−s))`, and
`B_N(s)B_N(1−s)=N/(s(1−s)) − [(1−s)emPole(s)emTail(1−s)+s emTail(s)emPole(1−s)] + s(1−s)emTail(s)emTail(1−s)`.

**A3. Blindness.** On `0≤Re s≤1`: `‖P_a(s)P_a(1−s)‖≤N(Σ_d|a_d|/d)²/‖s(1−s)‖`; the real part
`β` enters only through `N_d^{1−β}N_e^{β}≤N`. For the pole mode
`Re 1/(ρ(1−ρ))=β/(β²+γ²)+(1−β)/((1−β)²+γ²)>0` at every zero in the open strip, on or off the
line: the pole charge is the Hadamard pair of Poisson kernels at abscissa 1.

**B1. Theta shares the horizon.** Every theta atom is the seed atom at `−log n` with weight
`n^{-1/2}`; the truncated source `Φ_N` is the mirrored pole mode of the seed atom.
`ĥ_{Φ_N}(γ_ρ)=−f̂₁(γ_ρ)B_N(ρ)`; the complete source has transform `Ξ`, so the theta tail
`Φ−Φ_N` has transform `f̂₁(γ_ρ)B_N(ρ)` at every nontrivial zero. The atomic pole mode carries
`B_N(1−ρ)` at the same zero.

## Answer to the thesis (working form)

The identity carries to every resolution as the horizon law A1. Split vectors by depth:

- **Deep horizons** (`⌊N/d⌋` above the zero height `/2π`, i.e. `d≲2πc` at the heights `≍N/c`
  resolved by atoms of width `c/N`: the conductors `m≲c`). Their zero-side products are the
  horizon charge (A2–A3: blind, Poisson-kernel positive at abscissa 1) and the Euler–Maclaurin
  tails, whose Fourier expansion is the successor-shell Poisson dual. No growth `N^{|β−1/2|}`.
- **Shallow horizons** (`⌊N/d⌋` below the height, Möbius support near the top of the horizon).
  There `B_M(ρ)=−X_M(ρ)` is a short partial Euler sum: semilocal data reading `β`. The RH
  receivers synthesize their witnesses here.

Theta: the TH current at aperture `a` is `|Ξ|²·2Re ξ'/ξ(½+a+ib)` [corpus], the Poisson balayage of
the zeros at abscissa `½+a`; the pole charge of A3 is the same balayage at abscissa 1.

## Open (next in the loop)

- **A4 (dual decomposition).** Exact identity for the tail–tail part of the pole mode:
  `Σ_ρ m_ρΦ ρ(1−ρ)T_N(ρ)T_N(1−ρ) = ∫K̂(t)Ω(t)|S_N(t)|²dt + pole − dual primes`, with
  `K=(¼−∂²)G`, `S_N(t)=∫_N^∞{x}x^{−3/2−it}dx`, `Ω` the archimedean density. The first term is
  the archimedean zero density against the squared sawtooth transform (the Poisson remainder).
- Deep-sector positivity at every overlap (A2+A4 with the dual primes bounded relative to
  `log N`).

## Lean

`RenormalizedArithmeticPotentialTheory/`:
- `ThePoleModeMeetsTheZerosOnlyAtTheHorizon`: `weilQuad_poleMode_eq_tsum`,
  `emPole_mul_emPole_one_sub`, `horizonBoundary_mul_one_sub`.
- `TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons`:
  `weilQuad_atomicTest_eq_tsum_mobiusHorizon`, `sum_divisorSum_mul_cpow`.
- `TheHorizonChargeIsBlindToTheRealPartsOfTheZeros`: `norm_mobiusPole_mul_le`,
  `re_one_div_mul_one_sub_eq`, `re_emPole_mul_emPole_one_sub_pos`.
- `TheThetaSourceSharesTheHorizonOfThePoleMode`: `paperFT_thetaHorizonSource_gammaOf`,
  `paperFT_thetaTail_gammaOf`.

All four pass direct `lake --old env lean`; RAPT umbrella wired.

## Gates
- [x] 0 → 1
- [ ] 1 → 2  A4 paper proof
- [ ] 2 → 3

## Log
- 2026-10-30 — created; A1–A3, B1 formalized.
