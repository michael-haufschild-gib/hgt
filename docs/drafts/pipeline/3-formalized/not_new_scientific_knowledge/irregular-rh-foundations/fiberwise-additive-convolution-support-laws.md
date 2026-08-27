# Fiberwise additive-convolution support laws

- **ID:** `fiberwise-additive-convolution-support-laws`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** support shadow of enhanced additive convolution
- **Statement:** `[LITERATURE] [BRIDGE]` Fiberwise additive convolution of subsets of `X×ℝ` is
  associative and commutative, with zero-section support as unit; the zero-phase epigraph is
  idempotent.

## Goal

Formalize exact support algebra beneath
`K₁ ⊗⁺ K₂ = Rμ₊(p₁⁻¹K₁ ⊗ p₂⁻¹K₂)` before constructing sheaf or derived layers.  This separates
set-theoretic obligations from proper direct image, derived tensor, and coefficient calculations.

## Frontier

- `[LITERATURE]` D'Agnolo--Kashiwara define additive convolution through
  `μ(x,t₁,t₂)=(x,t₁+t₂)`, identify `C_{t=0}` as unit, and identify the zero-phase epigraph as an
  idempotent: https://arxiv.org/abs/2408.04260, Section 6.
- `[CORPUS]` `StokesEnhancedEpigraphConvolution.lean` now proves exact convolution of exponential
  epigraph supports.  No prior corpus declaration supplied the general support-level monoidal laws.

## Complete paper proof

`[PAPER-PROVED]` Commutativity sends a witness `(u,v)` to `(v,u)` and uses `u+v=v+u`.
Associativity expands either side to the same data

\[
 (x,u)\in A,\quad (x,v)\in B,\quad (x,w)\in C,\quad u+v+w=t,
\]

with the two parenthesizations identified by associativity of real addition.  For zero-section
support `Z_X={(x,0)}`, every witness in `Z_X⋆_X A` has `u=0`, hence `v=t` and is exactly a point
of `A`; conversely choose `(u,v)=(0,t)`.  Right unitality follows symmetrically.  Finally,
`E_0⋆_X E_0=E_{0+0}=E_0` by the proved epigraph convolution theorem.

## Hostile audit

- These are support equalities, not derived sheaf isomorphisms.
- Fiberwise constraint on `x` is load-bearing; ordinary Minkowski addition has different laws.
- Properness, compact support, shifts, and higher cohomology remain open at sheaf level.
- No RH consequence follows from support monoid laws.

Verdict: `BRIDGE`.

## Gates

- [x] 0 → 1 in-progress: exact support claim and parent boundary recorded
- [x] 1 → 2 fully-proven: dependency-closed proof above
- [x] 2 → 3 formalized: exact Lean laws, direct check, targeted build, prior axiom audit, umbrella wiring, and authoritative repository lint pass
- [ ] 3 → 4 publication-ready: not applicable as standalone novelty

## Log

- 2026-08-24 — Support monoidal laws isolated and paper-proved.
- 2026-08-24 — Formalized in `StokesEnhancedEpigraphConvolution.lean` as
  `fiberwiseAdditiveConvolution_comm`, `fiberwiseAdditiveConvolution_assoc`,
  `fiberwiseAdditiveConvolution_zeroSection_left/right`, and
  `fiberwiseAdditiveConvolution_zeroPhase_idempotent`.  Direct Lean check and targeted module build
  pass; new theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- 2026-08-27 — Exact laws re-audited; direct check, targeted build, umbrella-wiring lint, and authoritative repository lint pass; promoted to Stage 3.
