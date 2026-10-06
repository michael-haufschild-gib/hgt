# Every uncancelled triangular head oscillates beyond the three-quarter scale

- **ID:** MC-C12.99-S2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), positive survivor of the separate-payment test of MC-C12.99
- **Parent:** `../1-in-progress/mc-triangular-quadratic-pole-cancellation.md`; component
  `mc-triangular-shifted-pole-separation.md` (MC-C12.99-S1).
- **Lean:** `formal/GaloisForLFunctions/RHTower/LiouvilleTriangularHeadOscillation.lean`.

## Statement (unconditional)

`P(x) = Σ_{n≤x} λ(n)(x/n − 1)`, `W(y) = Σ_{k≤√y}(y/k² − 1)`, `A(x) = Σ_{m≤√x} μ(m)W(x/m)`.
For every real `c ≠ 0`, every `β < 3/4` and every `C ≥ 0`:

`C x^β < P(x) + cA(x)` for arbitrarily large `x`, and `P(x) + cA(x) < −C x^β` for arbitrarily large `x`.

`RHTower.LiouvilleTriangularHeadOscillation.frequently_gt_and_frequently_lt`. The case `c = −2` is
`P − 2A`, minus the quadratic remainder `B` of the hyperbola decomposition `P = 2A − B`.

## Proof (as formalized)

1. `P = xT − L` (`T = Σλ/n`, `L = Σλ`); two Abel integrals give `∫P(e^u)e^{−su}du = ζ(2s)/(s(s−1)ζ(s))`
   on `Re s > 2`.
2. `A = Z x H₁(√x) − 2√x H₂(√x) + E`, `|E(x)| ≤ ⌊√x⌋` from `|W(y) − Zy + 2√y| ≤ 1`. The scaling
   `u = 2v` and the Abel integral give the two head transforms `Z/((s−1)ζ(2s−1))` and
   `−2/((s−½)ζ(2s−½))`; `R(s) = ∫E(e^u)e^{−su}du` is holomorphic on `Re s > ½` (difference of two
   nonnegative Laplace transforms with abscissa `½`).
3. Generic one-sided Landau engine: density `ε e^{βu} − ηf(u) + K` with `|f(u)| ≤ Be^{γu}`; abscissa in
   `[β, γ]`, explicit transform on `Re z > γ`, and abscissa `= β` whenever the continuation is analytic
   at every real point `> β`.
4. Multiply the continuation identity by `D(z) = zU(z)(z−½)U(2z−½)U(2z−1)`; identity theorem on
   `Re z > β`. At the shifted zero `w` of MC-C12.99-S1 the left side vanishes and the right side is
   `η·2cZ·wU(w)(w−½)U(2w−½) ≠ 0`.

## Audit

Scratch compile clean (no warnings); targeted module build and `lake env lean` audit, axiom check: see
log. No sorry/axiom/heartbeat change.

## What it does not do

It does not bound `P`. It shows that the RH-critical lower bound `P(x) ≥ −C_ε x^{1/2+ε}` cannot be
obtained by estimating the short head and the quadratic remainder separately: any decomposition that
leaves a nonzero multiple of `A` carries forced oscillation of size `x^{3/4−ε}`.

## Log

- 2026-10-05 — formalized (Opus). Module wired after `LiouvilleTriangularPoleSeparation` in RHTower.lean.
- 2026-10-05 — audit: `lake --old build` of the leaf exit 0 (153 s); `lake --old env lean` on the leaf exit 0, no
  diagnostics; `#print axioms` for `frequently_gt_and_frequently_lt`, `integral_triangleCombination_exp_mul_cexp`,
  `isAbscissa_eq_of_analyticAt_real`: propext, Classical.choice, Quot.sound only. Lint: no error in this leaf
  (repository lint still reports unrelated unreachable HTGeometry modules). Index regenerated.
