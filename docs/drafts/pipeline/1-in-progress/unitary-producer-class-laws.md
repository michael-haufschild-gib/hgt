# Unitary (Lee–Yang / CMV / canonical-system) producers of Ξ: laws and open core

- **ID:** unitary-producer-class-laws
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (route W1C / Lee–Yang lanes), with THEOREM (Lean) components
- **Source:** loop card `rh-route-candidates-loop-2026-10-08.md`, rows 616–649; frontier map W1C
- **Statement:** a real-rooted unitary producer of Ξ must satisfy the laws below. The single open
  core is an arithmetic coupling law that resolves the divisor lattice into Ξ's zeros without a heat
  flow, while meeting the critical line and the Riemann–Siegel balance at once.

## Goal
A producer whose real-rootedness is structural (Lee–Yang / unitarity) and whose limit is `E·Ξ`
would prove RH by Hurwitz. This card records what such a producer must look like, which parts are
free, and where RH sits inside the class.

## Gates
- [x] 0 → 1  in-progress: well-posed producer class and laws
- [ ] 1 → 2  fully-proven: the WKB trilemma (rows 644–645) is heuristic, not a paper proof
- [ ] 2 → 3  formalized: partially (MUST-852, 854, 857, 858 below)

## Laws (free half)
1. **Real-rootedness is free.** Chains and trees with complex fugacities in the closed disc are
   real-rooted [L MUST-852, MUST-857]. They are self-dual multi-affine Lee–Yang data [L MUST-858],
   so every corpus Lee–Yang theorem applies. Uniform-field chains are OPUC/CMV, and the class is
   universal in the LP closure (row 622).
2. **Archimedean phase is free.** The continuum Riemann–Siegel chain (mass `κe^{αu}+c`) is
   Whittaker-solvable. Its zero condition is a Γ-ratio phase, `k = −½ − c/α`,
   `μ = (i/2α)√(z²−4c²)` (row 640).
3. **Field density is pinned to harmonic.** Producers of Ξ eventually have
   `Σ_j max(λ_j − 2π/T, 0) ≤ log(T/2π) − 1 + C/√T` [L, parallel session
   `LeeYangProducerFieldDensity`; chain form in MUST-858]. Harmonic fields `1/j` must start at
   `j ≥ 2` (excess exactly `γ`). The zero-gap law MUST-824 forces every field ratio into
   `(0.8007, 1.2489)`.
4. **No Euler factors of modulus `p^{−½}`** in unitary producers [L MUST-854].
5. **No mean-field / Gaussian-average step** (it is a heat flow, excluded by `Λ ≥ 0`), so producers
   are quenched samples (rows 617, 626, 628).
6. **No parallelism.** The field-density budget forbids parallel branches, so producers are
   one-dimensional in log scale (row 645).

## Where RH sits (RH half)
- **Divisor lattice.** Free harmonic spins have zeros `πm` with multiplicity `d(m)` (zero zeta
  `π^{−s}ζ(s)²`), which already matches Ξ's leading count. The coupling must resolve `ζ²` into
  `ζ′/ζ` (row 616).
- **Rigidity budget.** Matching `S(T) = O(log T)` needs log-discrepancy of the site Schur phases
  (row 641, via the parallel exact per-field count). Only the turning-point regime meets this a
  priori (row 642).
- **Trilemma (heuristic).** For fields `n^{−β}` and fugacities `n^{α−1}`, the turning point is
  `x* = (z/2κ)^{1/(α+β−1)}`. Harmonic density `β = 1`, critical weights `α = ½` and the balanced
  pivot `x* ∝ z` are never simultaneous (rows 643–644). At first order in the lattice the
  Riemann–Siegel chain gives `ζ` plus a double-counted middle Dirichlet polynomial.

## Approach (open)
- The only unexamined escape is higher-order lattice resummation in the turning-point regime (row
  637(b)). Its test needs numerics (pod rule), or an exact discrete solution of the Dirichlet
  nonlinear Fourier transform `∏_m(I + κ(m^{−s}σ₊ + m^{s−1}σ₋))`.
- CCM ground states are the class's named arithmetic coupling (row 630). Their convergence is the
  same open core.

## No-go closure (partial)
- **Exact killing mechanisms:** zero-gap law (fast fields), field-density budget (parallelism),
  Λ ≥ 0 (mean field), unitary Euler rigidity, WKB trilemma (power-law chains).
- **Strongest positive survivors:** MUST-852/854/857/858 [L]. The Whittaker continuum solution
  (paper) and the turning-point scaling law (paper).
- **New insight:** Lee–Yang producers realise either the critical line or the
  approximate-functional-equation balance, not both. This is the corpus's "no half / no slack" law
  inside the unitary class.
- **Status:** laws 1, 3 (chain form) and 4 in Lean; trilemma heuristic; open core unchanged.

## Dictionary (row 650)
Lee–Yang chains naturally realise Eisenstein constant terms `ξ(2s)y^s + ξ(2s−1)y^{1−s}`
(Lagarias–Suzuki): the frozen pivot is `y`, the arithmetic sits on the 1-line `ζ(1+2iτ)`, and
real-rootedness is the corpus line law MUST-625. Critical-line weights aim at `ξ(s)` and hit the
trilemma. This matches Lesson L (every RH-true object takes its line from a zero-free Euler half)
and twin rigidity (`ξ` has no half).

## Profile-independent trilemma and the Born window (rows 654–655)
- MUST-860 [L]: unimodular chains are free spins (rank-one transfer); the doubled harmonic chain
  is `2cos(xℓ) + 2κRe[e^{ixℓ}Σn^{−1−2ix}]` up to `κ²H²e^{|κ|H}`.
- The count condition (`c·ρ = n²` at the turning point) and the critical-line Born condition
  (`c·ρ = n^{½}`) are incompatible for every profile.
- No Born window at `Re s = ½`: the expansion parameter `κ√log M` cannot be small and large at
  once. On the 1-line the series converges and ζ enters as a monotone phase modulation (Lagarias–Suzuki).
- Spectral mismatch: free ends carry progression spikes at non-prime-power frequencies; Ξ's zero
  set has spikes only at `±log p^k` (Landau–Gonek).
