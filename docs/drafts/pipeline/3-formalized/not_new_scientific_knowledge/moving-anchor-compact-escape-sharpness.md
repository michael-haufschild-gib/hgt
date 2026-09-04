# Moving-anchor compact-escape sharpness

- **ID:** moving-anchor-compact-escape-sharpness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `multiplicity-parity-ladder-route.md`
- **Statement:** Increasing-order zeros are compatible with compact-open convergence to a nonzero holomorphic limit when their anchors escape to infinity.

## Goal

Show that the compactness condition in the moving-anchor flatness obstruction is exact. This is a
representation theorem only: it does not construct the arithmetic half-divisor or preserve Euler
coefficients.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean module and targeted build green; axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper

## Statement and proof

For `n ≥ 0`, put

\[
  A_n=(n+1)^2,\qquad B_n(s)=\left(1-\frac{s}{A_n}\right)^{n+1}.
\]

Then every `B_n` is entire, `A_n` lies in `Re(s)>1/2`, and `B_n` has a zero of order `n+1` at
`A_n`. Hence all derivatives through order `n` vanish there. Also `A_n→+∞`, so the anchors
eventually avoid every compact subset of the half-plane.

On a compact set `K`, choose `R` with `|s|≤R` on `K`. The geometric estimate

\[
  |(1+w)^d-1|\le d(1+|w|)^d|w|
\]

with `w=-s/A_n` and `d=n+1` gives a bound controlled by

\[
  \frac{(n+1)R}{(n+1)^2}
  \exp\!\left(\frac{(n+1)R}{(n+1)^2}\right),
\]

which tends to zero. Therefore `B_n→1` locally uniformly on `ℂ`. `[PROVED HERE]`

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingAnchorEscapeSharpness`

Key declarations:

- `farRightFlatEscapeGauge_tendstoLocallyUniformly_one`
- `farRightFlatEscapeGauge_analyticOnNhd`
- `farRightFlatEscapeGauge_jet_zero`
- `farRightFlatEscapeAnchor_mem_rightHalf`
- `farRightFlatEscapeAnchor_re_tendsto_atTop`
- `farRightFlatEscapeAnchor_eventually_avoid_compact`

Verification:

- direct `lake env lean` check: pass
- targeted build: pass (`13173/13173`)
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- umbrella import: `GaloisForLFunctions/RHTower.lean`

## Interpretation

Interior clustering, not increasing multiplicity alone, drives the flat-limit contradiction.
Compact-open convergence cannot detect arbitrarily deep zeros whose anchors escape. Any stronger
no-go must add arithmetic/source control at the noncompact boundary. Conversely, this example is
not an RH route: its zeros and coefficients are inserted by hand and carry no squarefree-Euler
provenance.

## Log

- 2026-09-04 — paper proof completed
- 2026-09-04 — formalized, built, axiom-audited, and wired into umbrella
