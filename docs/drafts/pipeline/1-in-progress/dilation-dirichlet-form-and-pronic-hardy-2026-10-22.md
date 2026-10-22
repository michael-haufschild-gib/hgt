# The dilation Dirichlet form of the signed work and the pronic Hardy inequality

- **ID:** dilation-dirichlet-pronic-hardy
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `ArithmeticContinuationAndCriticalEnergy` open problems 2 and 5; shared target mechanism 2
- **Statement:** The pronic dilation form of a row is a Dirichlet form on the dilation graph
  (`2Q = M − J`), and the pronic measure satisfies a Hardy inequality with Dirichlet condition at
  the root, so the receiver is uniformly comparable to its one-step block energy.

## Goal

Two structural reductions of the continuation layer's open obligation.

1. **Dirichlet shape.** The dilation form has zero diagonal and is indefinite as a kernel, so no
   form positivity is available for arbitrary rows. Edgewise polarisation nevertheless writes it as
   edge mass minus a jump energy on the graph `n ↦ n/j` with prime conductances. The sign question
   therefore becomes a **Poincaré inequality** on that graph, which is the shape the odd-sector
   Markov machinery of `ArithmeticCriticalityTheory` and `TransHorizonIncidenceMechanics` attacks,
   and the form inherits the Beurling–Deny normal contraction: `Q(v) ≤ Q(|v|)`. The obstruction is
   carried by the sign changes of the source, matching the majorant no-go from the other side.
2. **Localization of the receiver.** The exact self-similarity of the pronic measure (a dilation
   fibre carries `1/q` of a level's mass) plus a Peter–Paul split gives
   `‖v‖² ≤ q/(√q − 1)² · Σ (v(n) − v(n/q))² w(n)` for every row with `v 0 = 0`, with the reverse
   inequality `Σ (v(n) − v(n/q))² w(n) ≤ 2(1 + 1/q)‖v‖²`. For the damped Möbius source the
   dilation step is the centred divisor sum over the **top block** `(n/q, n]`, so the receiver is
   comparable to a pronic mean square of *block* sums. The open obligation is no longer a long
   prefix: admission at one damping follows from a horizon-uniform bound on block cancellation,
   which is the object the window laws of `BezoutValuationIncidence` speak about.

Non-circularity: both statements are unconditional identities/inequalities with no arithmetic
input. The Hardy constant is absolute; the comparison is two-sided, so no information is lost in
passing from the prefix to the blocks.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper (elementary: edgewise polarisation; Peter–Paul against the
      self-similarity ratio `1/q`, optimised at `t = 1/(√q − 1)`)
- [ ] 2 → 3  formalized: `TheDilationDirichletFormOfTheWork.lean`,
      `TheDilationHardyInequalityOnThePronicMeasure.lean`
- [ ] 3 → 4  publication-ready

## Approach

Dirichlet shape: `2ab = a² + b² − (a−b)²` applied to every pair `(v(n), v(n/j))` under the
conductance `Λ(j)j^{-ε}/(n(n+1))`. Edge mass splits as creation potential (the damped prime prefix
`ψ_ε(n)` against `v²`) plus fibre potential, giving the unconditional floor
`2Q ≥ Σ v(n)²ψ_ε(n)w(n) − J`.

Hardy: `v(n)² = (d(n) + v(n/q))² ≤ (s/(s−1))d(n)² + s·v(n/q)²` with `s = √q`; summing and using
`Σ w(n)v(n/q)² ≤ (1/q)Σ w(n)v(n)²` closes on itself with the sharp constant `q/(√q − 1)²`
(`6 + 4√2` at `q = 2`).

Telescoping: `(n/p^i)/p = n/p^{i+1}` makes the jump at a prime power a chain of prime steps, with
the Cauchy–Schwarz multiplicity cost `k`.

## Log
- 2026-10-22 — paper proofs complete; Lean modules written, under audit.
