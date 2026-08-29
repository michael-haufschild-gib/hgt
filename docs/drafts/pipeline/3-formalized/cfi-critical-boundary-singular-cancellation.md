# CFI critical-boundary singular cancellation

- **ID:** CFI-CBSC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · CFI / CCM-FU critical incidence
- **Statement:** For every `0 < ω < 1/2`, the full normalized CFI coupled error has a square-integrable boundary value at `δ = 0`, and its `δ > 0` regularizations converge to that boundary strongly in `L²(0,∞)`.

## Goal

Discharge CFI's critical `LAND` premise without assuming RH.  The exact proof chain is:

```text
critical lower-minus-upper singular cancellation
  → closed CFI boundary carrier at δ = 0
  → existing pre-scalar affine boundary-renormalization/source-response identity
  → CFI / CCM-FU no longer owes construction of the singular boundary carrier
  → remaining burden is the existing graph-debt/source-order scalar
  → four-unit endpoint
  → RH.
```

This theorem does not assert the graph-debt/source-order scalar and therefore is not a disguised RH
assumption.  It removes the analytic carrier premise on which that final scalar is meant to act.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Conjecture

Write

```text
F_{ω,δ}(t) = exp(-(1+ω+δ)t) E_ω(exp t).
```

For every `ω ∈ (0,1/2)`:

1. `t ↦ F_{ω,0}(t)^2` is integrable on `(0,∞)`;
2. as `δ → 0` through `δ ≥ 0`,
   `∫₀∞ (F_{ω,δ}(t)-F_{ω,0}(t))² dt → 0`.

The final Lean capstone must quantify over `ω`; it will have no ambient premise, added axiom, or
unclosed hypothesis.

## Corpus basis and novelty audit

- `CoupledFloorMobiusShiftIncidence.lean` gives exact lower-minus-upper incidence and proves the
  common upper input `q_δ` has squared norm `1/(2δ)`, hence is not itself in `L²` at `δ = 0`.
- `ShiftedEulerFloorMobiusTailCoupling.lean` proves the natural-argument envelope
  `|E_ω(N)| ≤ C_ω N^(1-ω)`.
- `SuzukiTailSummatoryErrorTransform.lean` defines the real-argument error through `⌊X⌋₊`.
- Corpus searches for `coupledErrorVector critical boundary L2 singular cancellation damping
  convergence` found no critical combined-vector integrability or strong-boundary theorem.
- Literature searches through August 2026 found work on Möbius summatory distributions,
  Möbius/screw functions, and scaling-Hamiltonian RH criteria, but no theorem identifying this exact
  shifted-Euler lower-minus-upper incidence as an `L²` critical boundary value.  Novelty claim is
  confined to this exact carrier theorem and proof-chain use.

## Approach

1. Upgrade the corpus natural-argument envelope to real `X ≥ 1`.  With `N = ⌊X⌋₊`, split
   `E_ω(X) = E_ω(N) + M_ω(N)-M_ω(X)`.  The first term is in the corpus; a mean-value/rpow estimate
   bounds the one-cell main-term jump by `O(X^ω)`, hence by `O(X^(1-ω))` because `ω < 1/2`.
2. Substitute `X = exp t`: `|F_{ω,0}(t)| ≤ C exp(-2ωt)`.  Its square is dominated by an integrable
   exponential.
3. Prove the exact damping identity `F_{ω,δ}(t) = exp(-δt) F_{ω,0}(t)`.
4. For `δ ≥ 0`, the squared difference is dominated by `F_{ω,0}(t)^2` and converges pointwise to
   zero.  Dominated convergence gives strong `L²` convergence.

## Proof

**[PROVED HERE]** Fix `0 < ω < 1/2`.  The corpus theorem
`abs_suzukiCoupledError_le` supplies `C > 0` with

```text
|E_ω(N)| ≤ C N^(1-ω)                    (N ≥ 1).
```

For real `X ≥ 1`, put `N = ⌊X⌋₊`.  The summatory part is constant on the floor cell, so

```text
E_ω(X) = E_ω(N) + M_ω(N) - M_ω(X).
```

Here `N ≤ X < N+1`.  The corpus rpow Lipschitz theorem
`abs_rpow_sub_rpow_le_of_le`, applied with exponent `1+ω`, gives

```text
|N^(1+ω)-X^(1+ω)| ≤ (1+ω) X^ω |N-X| ≤ (1+ω) X^ω.
```

After multiplication by the main-term density and division by `1+ω`, the floor-cell correction is
at most `|r_ω|X^ω`.  Since `X ≥ 1` and `ω < 1/2`, `X^ω ≤ X^(1-ω)`.  Thus some `C' > 0` satisfies
`|E_ω(X)| ≤ C'X^(1-ω)` for every real `X ≥ 1`.

For `t ≥ 0`, substitute `X = exp t`:

```text
|F_{ω,0}(t)|
  = exp(-(1+ω)t) |E_ω(exp t)|
  ≤ C' exp(-2ωt).
```

Consequently `F_{ω,0}²` is dominated by `C'² exp(-4ωt)`, which is integrable on `(0,∞)`.
Directly from the definition,

```text
F_{ω,δ}(t) = exp(-δt) F_{ω,0}(t).
```

For `δ,t ≥ 0`, `|exp(-δt)-1| ≤ 1`; hence

```text
|F_{ω,δ}(t)-F_{ω,0}(t)|² ≤ |F_{ω,0}(t)|².
```

The left side tends pointwise to zero as `δ → 0` within `[0,∞)`.  Dominated convergence proves its
integral tends to zero, exactly strong `L²` convergence.  The existing incidence theorem identifies
`F_{ω,0}` pointwise with the full lower-minus-upper `tsum`, while the existing damping-mode theorem
shows the uncancelled upper input's squared norm tends to infinity.  This completes the claimed
singular-cancellation certificate with no open dependency.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.CoupledFloorMobiusCriticalBoundaryCancellation`
- Closed capstone:
  `RHTower.coupledFloorMobiusCriticalBoundary_singularCancellation`
- Supporting new theorems:
  `abs_suzukiCoupledErrorReal_le`, `integrableOn_coupledErrorVector_zero_sq`,
  `coupledErrorVector_eq_damping_mul_zero`,
  `tendsto_integral_coupledErrorVector_sqDistance_zero`.
- Direct `lake env lean` check: PASS.
- Targeted `lake build GaloisForLFunctions.RHTower.CoupledFloorMobiusCriticalBoundaryCancellation`:
  PASS.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint: new module is umbrella-reachable and contains no forbidden declaration.  Repository
  lint remains nonzero because unrelated concurrent files are unreachable and
  `HTGeometry/PolynomialProjectiveBoundary.lean` contains an existing `sorry`.

## Log

- 2026-08-29 — Conjectured from CFI incidence, real-error, and natural-envelope corpus modules;
  exact CFI→RH chain recorded before proof attempt.
- 2026-08-29 — `[PROVED HERE]`; formalized closed singular-cancellation capstone and wired it into
  `GaloisForLFunctions.RHTower`.
