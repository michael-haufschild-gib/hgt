# Perron sign law of the half-window band

- **ID:** swc-perron-sign-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `swc-pole-pays-prime-three` (C2, C8)
- **Statement:** For `0 < c < log 2` the ground states of both parity sectors of the half-window band
  on `[−c, 0]` are nonnegative; hence at the odd ground state the primes pay (`s_n ≥ 0` on the
  large side) and at the even ground state they cost, with the pole in the opposite role.

## Goal
Half-window `f` on `W = [−c, 0]`, `L` the Lévy operator of `levyEnergy` (kernel `ω(|u − v|)`,
killing `κ(u) = Ω(u + c) + Ω(−u)`), `R(u, v) = ω(−u − v)` (trivial-zero squares
`m_*² + Σμ_k²`), `P_n f = f(−log n − ·)` on the sliver `I_n`, `sh = sinh(·/2)`, `ch = cosh(·/2)`:
- odd form `O = Γ + L + R + Σ w_n P_n − 4|sh⟩⟨sh|`;
- even form `E = Γ + L − R − Σ w_n P_n + 4|ch⟩⟨ch|`.
Frustration (Beurling–Deny): `L + R − 4|sh⟩⟨sh|` and `L − R − Σ w_n P_n` have nonpositive
off-diagonal kernels (`ω(−u − v) ≤ ω(|u − v|)` on `W²`); the odd kick `Σ w_n P_n` and the even pole
`4|ch⟩⟨ch|` have positive ones. So neither sector is Markov once a prime acts (odd) or at all (even),
and positivity of the ground states is a statement beyond Beurling–Deny.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
1. Reliable numerics for the sign near the window edges (the Legendre basis of `band2.py` cannot
   resolve the `(log 1/t)^{−1/2}` edge layer of the order-zero Lévy operator).
2. Euler–Lagrange structure: even ground state `ψ = a (λ − A_E)^{−1} ch` with
   `A_E = Γ + L − R − Σ w_n P_n` positivity improving and `λ > λ₀(A_E)` (anti-maximum regime);
   odd ground state `ψ = (λ − A_O)^{−1} Σ w_n P_n ψ` with `A_O = Γ + L + R − 4|sh⟩⟨sh|`.
3. Conjecture loop on the mechanism; survivor if false.

## Numerics [N]
Converged hp discontinuous Galerkin (`hp.py`: Legendre degree `p` on cells graded geometrically
toward both ends of `W`, singular kernels integrated in local offsets, exact reflections);
`p = 5` and `p = 7` agree to 5–7 digits (odd/even ground energies at `c = 0.3`:
`0.222556601`, `7.57146936·10⁻³`).

| `c` | odd `λ₀` | odd `λ₁` | even `λ₀` | even `λ₁` | even `ψ(−c + 10⁻⁹)/max ψ` |
|---|---|---|---|---|---|
| 0.5 | `1.9367·10⁻⁴` | `0.363` | `9.3317·10⁻⁷` | `1.80·10⁻²` | `6.8·10⁻⁴` |
| 0.55 | `1.4284·10⁻⁵` | `7.5·10⁻²` | `5.3034·10⁻⁸` | `1.42·10⁻³` | `1.8·10⁻⁴` |
| 0.5743 | `3.3006·10⁻⁶` | `2.7·10⁻²` | `1.0154·10⁻⁸` | `4.4·10⁻⁴` | `8.4·10⁻⁵` |
| 0.6 | `5.9440·10⁻⁷` | `8.5·10⁻³` | `1.5999·10⁻⁹` | `1.03·10⁻⁴` | `3.4·10⁻⁵` |
| 0.65 | `1.8321·10⁻⁸` | `4.9·10⁻⁴` | `3.79·10⁻¹¹` | `3.6·10⁻⁶` | `5.9·10⁻⁶` |
| 0.69 | `6.3004·10⁻¹⁰` | `3.7·10⁻⁵` | `|λ₀| < 10⁻¹²` (method floor) | `2.0·10⁻⁷` | `9.9·10⁻⁷` |

- Both ground states are strictly positive at every `c` tested (no negative part at any of
  `1.2·10⁴` sample points, edge layers resolved down to `10⁻⁹`); `s₂, s₃ > 0` at both.
- The odd ground state vanishes linearly at the centre `u = 0`; the even one has the
  `(log 1/t)^{−1/2}` edge layer at `−c` with a positive coefficient that decays like `√λ₀`.
- The negative edge values of the Legendre harness (`band2.py`, `−6.5·10⁻⁵` at `c = 0.5743`) and of a
  midpoint Nyström scheme are discretization artifacts.
- Near `log 2` the even sector has two near-critical modes (`λ₁/λ₀`-gap collapses: `λ₁ = 2·10⁻⁷`
  at `c = 0.69`).

## Partial results
- **Markov regimes (Beurling–Deny).** Odd sector Markov for `c ≤ ½ log 2` (frozen odd form,
  `TheFrozenOddFormIsMarkovAndTheKickIsNot`). Even sector: the defect is
  `E(f) − E(|f|) = ∬ D(u,v)[ω(|u − v|) + ω(−u − v) − 4ch(u)ch(v)] + Σ w_n ∫ D(u, ρ_n u)`,
  `D = |f(u)f(v)| − f(u)f(v) ≥ 0`, and with `p = −u, q = −v`, `M = max, m = min`:
  `ω(M − m) + ω(M + m) = 2Σ_k e^{−α_k M} cosh(α_k m) ≥ 2cosh(m/2) ω(M) ≥ 4cosh(M/2)cosh(m/2)`
  for `M ≤ t_* = log ρ` (plastic threshold, `ω(t_*) = 2cosh(t_*/2)`). So the even sector is Markov
  for `c ≤ t_* ≈ 0.2812`, sharp: for `c > t_*` the kernel is negative at `(−c, 0)` (edge against
  centre). **PROVED [L]**: `four_mul_cosh_mul_cosh_le`, `evenSector_abs_le`
  (`W(|f|) + 𝓗₀(|f|) ≤ W(f) + 𝓗₀(f)` for `C²` `f` on `[−c, 0]`, `0 ≤ c ≤ t_*`),
  `evenKernel_neg_of_threshold_lt` in
  `PerronSignLaw/TheEvenSectorIsMarkovUpToThePlasticThreshold.lean`.
- In the full-window picture the pole kernel `2cosh((x − y)/2)` is dominated by `ω(|x − y|)` only
  for `2c ≤ t_*`; the trivial-zero squares double the Markov range of the even sector.
- Beyond the Markov regimes (odd `c > ½ log 2`, even `c > t_*`) positivity of the ground states is an
  anti-maximum-principle statement: `ψ_E = a(λ − A_E)^{−1} ch`, `λ ∈ (λ₀(A_E), λ₁(A_E))`.

## Status
- C8 holds numerically on `0 < c ≤ 0.69` in both sectors (converged hp-DG).
- Proved: Perron by Beurling–Deny in the Markov regimes (odd `c ≤ ½ log 2`, corpus; even
  `c ≤ t_*`, Lean, sharp at the level of the kernel).
- Open: `t_* < c < log 2` (even) and `½ log 2 < c < log 2` (odd), where the pole (even) and the prime
  kick (odd) frustrate the sign and positivity is an anti-maximum principle for the frustration-free
  operator `A_E` (resp. `A_O`) at the band energy.

## Log
- 2026-11-04 — created in 1-in-progress
