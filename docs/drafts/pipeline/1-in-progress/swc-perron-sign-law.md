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

## The anti-maximum regime [N]
Pole-free even operator `A_E = E − 4|ch⟩⟨ch|`, kick-free odd operator `A_O = O − Σ w_n P_n`;
`t(λ) = (λ − μ₀)/(μ₁ − μ₀)` locates the band ground energy in the first gap of the frustration-free
operator.

| `c` | `A_E`: `μ₀`, `μ₁` | even `t(λ)` | `A_O`: `μ₀`, `μ₁` | odd `t(λ)` |
|---|---|---|---|---|
| 0.3 | `−1.120`, `0.727` | 0.611 | `0.223`, `1.071` | 0 |
| 0.4 | `−1.540`, `0.236` | 0.867 | `−0.078`, `0.782` | 0.108 |
| 0.5 | `−1.988`, `0.0119` | 0.994 | `−0.322`, `0.557` | 0.367 |
| 0.6 | `−2.417`, `1·10⁻⁴` | 1.000 | `−0.536`, `0.372` | 0.591 |
| 0.69 | `−2.823`, `≈ 0` | 1.000 | `−0.715`, `0.228` | 0.758 |

- **Two-level structure (even).** `A_E` has one negative eigenvalue (positive eigenfunction) and a
  second eigenvalue `μ₁ → 0`; the pole lifts the Perron mode exactly to the sign-changing level
  (avoided crossing), so `λ₀(E) ≈ μ₁(A_E) ≈ 0` from `c ≈ 0.5` on.
- **Perron is critical.** In the frustration strength the Perron region is `κ ∈ [0, κ_c]` (pole) and
  `t ∈ [0, t_c]` (kick); at the arithmetic point:

  | `c` | even `λ₀` | `κ_c − 4` | odd `λ₀` | `t_c − 1` |
  |---|---|---|---|---|
  | 0.4 | `1.81·10⁻⁴` | `4.96·10⁻²` | `1.47·10⁻²` | `0.730` |
  | 0.45 | `1.61·10⁻⁵` | `7.74·10⁻³` | `2.40·10⁻³` | `0.192` |
  | 0.5 | `9.33·10⁻⁷` | `6.01·10⁻⁴` | `1.94·10⁻⁴` | `3.48·10⁻²` |
  | 0.55 | `5.30·10⁻⁸` | `4.31·10⁻⁵` | `1.43·10⁻⁵` | `2.75·10⁻³` |
  | 0.6 | `1.60·10⁻⁹` | `1.75·10⁻⁶` | `5.94·10⁻⁷` | `2.00·10⁻⁴` |
  | 0.65 | `3.79·10⁻¹¹` | `5.28·10⁻⁸` | `1.83·10⁻⁸` | `6.95·10⁻⁶` |

  The margins vanish with the ground energy (`(κ_c − 4)/λ₀ ≈ 3·10²–1.4·10³`, slope
  `d log(κ_c − 4)/d log λ₀ → 0.93`; odd slope `≈ 0.8`). Positivity needs `κ ≥ κ_pos` with
  `κ_pos ≥ 4 − λ₀/C(ψ)²`: the arithmetic pole sits in the shrinking interval `[κ_pos, κ_c]` where
  positivity and Perron coexist.
- **Perron is lost at the window edge.** Just above `κ_c` (resp. `t_c`) the negative part is a layer
  `[−c, −c + 0.01]`: even against the maximum at the centre (the frustrated pair of
  `evenKernel_neg_of_threshold_lt`), odd against the positive inner sliver ends `c − log n` (kick
  partners).
- **Hadamard edge law.** With `ψ(−c + t) ≈ β (½ log 1/t)^{−1/2}` (`‖ψ‖ = 1`),
  `−dλ₀/dc = K β²`, `K = 1.77 ± 0.01` at `t = 10⁻⁹` in both sectors for `c = 0.45–0.6` (and `≈ 2.06`
  after extrapolating `β` in `1/log(1/t)`; conjecture `K = 2`, i.e.
  `−λ₀′(c) = lim_{t→0} ψ(−c+t)² log(1/t)`). The edge amplitude that carries Perron is the rate at
  which the window approaches criticality.

## No-go: robust Perron
Even band as a pole family `E_s = E_0 + s·P`, `P(f) = (∫ f·2ch)²` (pole `κ = 4s`); odd band as a
kick family `O_t = O_0 + t·K`, `K(f) = w₂(f⋆f)(−log 2) + w₃(f⋆f)(−log 3)`.
- **Killing mechanism [L]** (`PerronSignLaw/ThePerronMarginIsBoundedByThePoleSaturationGap.lean`).
  Let `λ ≤ E_{s₀}` at `ψ`, `‖ψ‖₂ = 1`, `ψ` an `ε`-ground state of `E_{s₁}` against a competitor `g`
  on the pole hyperplane `∫ g ch = 0` (where `E_s(g) = E_1(g)` for all `s`). Then
  `(s₁ − s₀) P(ψ) ≤ E_1(g) − λ + ε` (`evenPerronMargin_le`); for Perron `0 ≤ ψ ≤ M`,
  `4(s₁ − s₀) ≤ M²(E_1(g) − λ + ε)` (`evenPerronMargin_le_sup`), and past that margin the ground
  state changes sign (`exists_neg_of_evenMargin_gt`). Lower side: positivity at `s_w < s₀` forces
  `4(s₀ − s_w) ≤ M² E_{s₀}(ψ)` (`evenPositivityMargin_le_sup`). Odd: against `g` with `K(g) ≤ 0`,
  `(t₁ − t₀) K(ψ) ≤ O_0(g) − λ + ε`, and `K(ψ) ≥ 0` for Perron `ψ` (`oddPerronMargin_le`,
  `kickEnergy_nonneg`). Every nonzero test on the pole hyperplane changes sign
  (`exists_neg_of_poleHyperplane`). So an argument proving Perron at pole strength `4(1 + η)`
  certifies `4η ≤ M²(λ_⊥ − λ₀)`, `λ_⊥` the band ground energy on the pole hyperplane.
- **Beurling–Deny and kernel domination closed exactly at `t_*` [L]**
  (`PerronSignLaw/TheEvenBandIsNotMarkovPastThePlasticThreshold.lean`). For `t_* < c < log 2`, all
  weights `w₂, w₃` and every pole strength `κ ≥ 4`, a smooth test `f = a − b` (`a ≥ 0` at the edge
  `(−c, −c + r)`, `b ≥ 0` at the centre `(−r, 0)`) has `E_κ(f) < E_κ(|f|)`
  (`exists_evenPoleBand_lt_abs`); kernel form
  `E_κ(|f|) − E_κ(f) ≥ 4(∫a)(∫b)[4cosh((c − r)/2) − ω(c − 2r) − ω(c − r)]`, no prime reflection
  joins the bumps. With nonnegative weights the arithmetic even band is Markov iff `c ≤ t_*`
  (`evenBand_markov_iff`).
- **Numerical part [N].** The thresholds `c ≈ 0.45` (even) and `c ≈ 0.55` (odd) for gap-limited
  arguments, including gap-independent anti-maximum principles, are hp-DG values of `λ₀`,
  `λ_⊥ − λ₀ ≤ λ₁(E) − λ₀` and `κ_c − 4` (tables above). Lean has no certified bound on
  `λ_⊥ − λ₀` (that needs a certified eigenvalue computation) and no a priori bound on `M = sup ψ`;
  the observed `κ_c − 4 ∝ λ₀` is finer than the `[L]` bound `∝ λ_⊥ − λ₀`.
- **Strongest positive survivor (Lean).** Frustration localization
  `evenBand_abs_le_of_frustrationFree`: for every `c < log 2` and nonnegative prime weights, the even
  band form does not increase under `f ↦ |f|` unless `f` changes sign across a frustrated pair
  (`EvenFrustrationFree`); Markov regime `evenSector_abs_le` (`c ≤ t_*`), sharp at form level
  (`evenBand_markov_iff`). Odd analogue: the frozen odd form is Markov and the kick is the only
  frustration (`TheFrozenOddFormIsMarkovAndTheKickIsNot`).
- **New insight.** The Perron margin in the frustration strength is the pole saturation gap over the
  squared pole moment of the ground state [L]. Beyond the Markov regimes positivity of the ground
  state is controlled by the edge amplitude `β`, with `|β| = √(−λ₀′/K)` by the Hadamard law [N].
- **Status.** Mechanism and Beurling–Deny closure: Lean, axioms standard. Threshold values and
  Hadamard law: numerics [N] (converged hp-DG, `p = 5, 7`).

## Status
- C8 holds numerically on `0 < c ≤ 0.69` in both sectors (converged hp-DG).
- Proved: Perron by Beurling–Deny in the Markov regimes (odd `c ≤ ½ log 2`, corpus; even
  `c ≤ t_*`, Lean, sharp at the level of the form: `evenBand_markov_iff`); margin law for robust
  Perron in both sectors (Lean).
- Open: `t_* < c < log 2` (even) and `½ log 2 < c < log 2` (odd). There Perron holds numerically
  but critically (margins `∝ λ₀`); robust arguments reduce to the gap inequality [L], whose failure
  beyond `c ≈ 0.45 / 0.55` is numerical [N]. The Hadamard law gives only `|β| = √(−λ₀′/K)`: the
  edge amplitude vanishes exactly where `λ₀` stops decreasing in `c`; the sign of `β` and the
  absence of interior zeros remain open.

## Log
- 2026-11-04 — created in 1-in-progress
