# Moving-Hermite unbounded-depth flat-limit no-go

- **ID:** moving-hermite-unbounded-depth-flat-limit-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local squarefree-half multiplicity-parity ladder route
- **Statement:** Every canonical boundary-Hermite schedule whose jet depth tends to infinity is incompatible with simultaneous Euler admissibility and local boundedness of any cofinal pole-factor schedule.

## Goal

Close exact critical slope `5/11` and every other depth schedule tending to infinity by a
representation-level analytic obstruction, without estimating the Hermite polynomial away from
its anchor.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit passed
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact claim

[PROVED HERE] Let `depth kappa : ℕ → ℕ`. Assume

`depth N → ∞` and `kappa N → ∞`.

Set

`C_N(s) = boundaryHermiteJetCounterterm N (depth N) s`.

Then it is impossible for both

1. `C` to be `SquarefreeHalfCountertermAdmissible`, and
2. the corrected family
   `poleClearedFirstTraceCountertermScheduledApprox C kappa N`
   to be locally bounded on `rightHalf`.

No slope assumption is used.

## Complete proof

Write `b = 6/11`,

`D_N(s) = exp(N(s-b)) S_N(s)`,

and let `P_{N,K}` be the degree-`K` Taylor polynomial of `D_N` at `b`. The canonical counterterm is

`C_{N,K}(s) = -exp(N(b-s)) P_{N,K}(s)`.

Since `exp(N(b-s)) exp(N(s-b)) = 1`, the corrected source has the exact factorization

`S_N(s) + C_{N,K}(s)`

`= exp(N(b-s)) (D_N(s) - P_{N,K}(s))`.

The defining Taylor formula gives, for every `j ≤ K`,

`D_N^(j)(b) = P_{N,K}^(j)(b)`.

Thus `D_N-P_{N,K}` has zero derivatives through order `K` at `b`. Leibniz's rule then gives

`(S_N+C_{N,K})^(j)(b)=0` for every `j≤K`.

Multiplying by the analytic pole approximant and dividing by the nonvanishing analytic Carleman
half-determinant preserves the same zero jet. Hence, with

`F_N = poleClearedFirstTraceCountertermScheduledApprox C kappa N`,

one has

`F_N^(j)(b)=0` whenever `j≤depth N`.

Now assume admissibility and local boundedness. The existing Vitali theorem on the connected open
set `rightHalf`, combined with `kappa N→∞`, produces a holomorphic `G` such that `F_N→G` locally
uniformly on `rightHalf`, and `G` agrees with `poleClearedFirstTraceSourceLimit` on `farHalf`.

Fix `j`. Since `depth N→∞`, eventually `j≤depth N`; hence eventually `F_N^(j)(b)=0`. Local uniform
convergence of holomorphic functions passes to every iterated derivative, so

`G^(j)(b)=0`.

This holds for every `j`. Analytic germ determinacy makes `G` zero on a neighborhood of `b`; the
identity theorem on connected `rightHalf` then makes `G` identically zero there.

But `2∈farHalf`, so

`G(2)=poleClearedFirstTraceSourceLimit(2)`.

The square of the right side is

`poleClearedFirstTraceExponentialContinuation(2)`,

which equals `(2-1) exp(coronaPrimeZeta(2))` and is nonzero. Contradiction.

## Hostile audit

- Exact finite-jet annihilation follows from Taylor coefficients and Leibniz's rule; no Cauchy,
  tail, or growth estimate is used.
- The pole-factor multiplier need not converge normally near `b`; Vitali supplies local uniform
  convergence from the stated local-boundedness hypothesis.
- Derivative convergence is legitimate because every corrected approximant is holomorphic on the
  open set and convergence is locally uniform there.
- `depth→∞` is used separately for each fixed derivative order; no interchange of two unrestricted
  limits occurs.
- Flatness is used only for the holomorphic Vitali limit, so the smooth-flat-function counterexample
  is irrelevant.
- Nonzero Euler value is unconditional: its square is `(2-1) exp(coronaPrimeZeta(2))`.

## No-go closure

- **Exact killing theorem/mechanism:** Increasing point-Hermite depth forces eventual exact
  annihilation of every fixed anchor jet. Any locally bounded admissible family therefore has a
  holomorphic limit flat at the anchor, while Euler fidelity requires that limit to be nonzero.
- **Strongest positive survivor:** The complete moving jet is an invariant of the representation:
  unbounded point-Hermite interpolation cannot cross the Euler boundary under a normal-family
  bound, independent of depth rate. Viable transition mechanisms must avoid eventual annihilation
  of every fixed jet at one interior anchor, for example by moving/distributed anchors or a nonlocal
  correction.
- **New insight:** `5/11` is only the phase boundary of value-growth estimates, not a genuine
  surviving critical regime. Jet rigidity closes exact critical slope and every schedule with
  `depth→∞`.
- **Status:** Dependency-closed paper proof and Lean formalization complete. Capstone:
  `not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm_of_depth_tendsto_atTop` in
  `SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo.lean`.

## Lean verification

- Module:
  `formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo.lean`
- Exact finite-jet theorems:
  `iteratedDeriv_boundaryHermiteJetPolynomial_at_boundary`,
  `iteratedDeriv_boundaryHermiteJet_correctedSource_at_boundary`, and
  `iteratedDeriv_poleClearedFirstTrace_boundaryHermiteJetCountertermScheduledApprox_at_boundary`.
- Capstone:
  `not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm_of_depth_tendsto_atTop`.
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo.lean`
  — passed.
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo`
  — passed, `13066/13066` jobs.
- Axiom audit for all three finite-jet layers and capstone:
  `[propext, Classical.choice, Quot.sound]` only.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean` imports module.

The same module now strengthens this result to unbounded oscillatory ranges via
`exists_cofinal_high_depth_subsequence`, and then to every depth schedule via the bounded/unbounded
dichotomy in `not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm`. See the companion
Stage-3 all-depth classification card.

## Log

- 2026-09-04 — conjectured from exact critical-slope failure mode; paper proof and hostile audit completed; promoted directly to Stage 2.
- 2026-09-04 — formalized exact jet annihilation, Vitali derivative passage, analytic flatness, and nonzero Euler contradiction; promoted to Stage 3.
