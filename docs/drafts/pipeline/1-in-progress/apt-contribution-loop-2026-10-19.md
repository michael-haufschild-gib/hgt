# APT contribution loop (goal: 100 field-native contributions)

- **ID:** apt-loop-1019
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md (read-only)
- **Statement:** Develop Arithmetic Positivity Theory by a conjecture loop; each accepted
  contribution is an unconditional Lean theorem native to the field (factorial sources,
  critical kernels, Weil/Markov/pole channels, collar arithmetic, sampling forms).

## Goal
100 significant contributions. Each must use the field's objects and mechanisms, extend what
the field explains or solves (README §1, §5), and be proved unconditionally in Lean.

## Rules in force
No hgtl7 skill. No numerical experiments. No added axioms or hypotheses in capstones. One
foreground Lean process at a time (`lake env lean`; oleans only via
`lake --old env lean -j 1 -o ...`). No full or umbrella builds. Wire new modules into
`GaloisForLFunctions/ArithmeticPositivityTheory.lean`. README is read-only.

## Conjecture queue
1. **Critical kernel sign (README §5, frontier 1).** The continuous real kernel `R` is
   strictly negative on `[0,1]`; hence `P∞(S,b) ≤ -κ Σ b_j²` for every finite real pattern.
   Route: Poisson for the band-limited weight (`Σ_z γ(t+z) = π²/6`) turns each harmonic tail
   `S_m(t) = ½Σ_{j≥m}(γ(j+t)+γ(j+1-t))` into `π²/12 - ½W_m(t)` with a finite window
   `W_m(t) = Σ_{z=-m}^{m-1} γ(t+z)`; the triangle representation
   `γ(u) = ∫_0^{π/6}(π/6-ξ)cos(ξu)dξ` and the Dirichlet telescoping
   `Σ_z cos(ξ(t+z)) sin(ξ/2) = cos(ξ(t-½)) sin(ξm)` give
   `S_m(t) - J_m/m = -½∫(a-ξ) g(ξ,t-½) sin(ξm) dξ`, `|g| ≤ ξ/5.6`. With the proved mean
   `Σ A(m)J_m/m⁴ ≤ -log2/390` and `Σ|A(m)|/m³ ≤ 0.71` this leaves a negative margin.
2. Complete critical form: archimedean term at β = 1/2 plus prime and polar channels.
3. Affine model constant `N∫v⁻²|Φ_N-Ψ_N|² → 7ζ(3)/(256π²)`.
4. Odd-sector capacity ratio `S(g)²/(2M_N(g))` under aperture growth.

## Log
- 2026-10-19 — loop started; README read in full; frontier cards read; queue seeded.

## Contribution ledger (append-only)
