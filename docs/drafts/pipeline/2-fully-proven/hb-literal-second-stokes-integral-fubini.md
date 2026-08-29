# Literal second Bochner--Stokes integral and Fubini bridge

- **ID:** C-A.9t4d
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/hb-complete-augmented-third-order-source-coefficient.md
- **Statement:** The standard truncated hyperbolic moment of the actual second Stokes defect equals the actual paired second-current cusp top for every truncation height at least one.

## Goal

Discharge final analytic integration bridge before actual balanced BM `++-` coefficient extraction.
Exact RH chain:

`literal second modular Green/Stokes + standard-measure Fubini -> vanishing regularized second
defect moment -> actual balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM
projection -> HC94 -> RH`.

Failure of joint third-jet regularity, Fubini, arc orientation, or the factor-two normalization
would kill HB before QNM work.

## Gates

- [x] 0 → 1 in-progress: exact source current, domain, and route-kill tests fixed
- [x] 1 → 2 fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted build, and axiom audit pending
- [ ] 3 → 4 publication-ready: standalone paper pending

## Frontier audit

- `[CORPUS]` `d4BM_actualSecondStokesDefectDensity_eq_divergence` identifies twice the literal
  second defect with `y²` times actual Bochner-current divergence.
- `[CORPUS]` `d4BM_actualSecondStokes_nonCuspPairedDefect_eq_zero` and
  `d4BM_actualSecondStokes_fullCuspBoundaryClosure` close the complete boundary algebra and cusp
  asymptotics.
- `[CORPUS]` first-Stokes compact-domain geometry and Fubini are formalized in
  `ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral` and
  `ThetaCuspHawkingBMEisensteinActualFirstStokesFubini`.
- `[LITERATURE]` Zagier regularization, Edwards' renormalized Eisenstein triple products, and Wu's
  extension of regularized `GL₂` integrals cover general truncation mechanisms, not this
  source-normalized completed-Poincare second Bochner current.
- **Hostile verdict:** `[BRIDGE]`. The source-specific theorem is absent from audited corpus and
  literature and closes a genuine RH proof burden, but its geometric mechanism is a specialized
  Green/Fubini theorem rather than broad new scientific theory.

## Complete paper proof

Fix actual completed-Poincare parameters `P,Q` and `Y ≥ 1`. Let
`D_Y = {(x,y) : -1/2 ≤ x ≤ 1/2, sqrt(1-x²) ≤ y ≤ Y}` and let `(H,V)` be the
actual second Bochner current. Define

`M₂(P,Q;Y) = ∫_{D_Y} 2 D₂(P,Q;x,y) dx dy / y²`,

where `D₂` is the literal second Stokes defect.

1. Each primitive-pair `xxx`, `xxy`, and `xyy` seed is continuous. The corpus pointwise bounds
   have form `||D³ seed|| ≤ C(P.s) y⁻³ ||seed||`. On compact cell
   `[-1/2,1/2] × [1/2,Y]`, this is at most `8 C(P.s)` times the existing summable value majorant.
   Weierstrass' theorem therefore gives joint continuity of the three completed third-jet sums.
   The `yyy` jet is the algebraic differentiated-eigen expression in the value, vertical first
   jet, `xxy`, and nonzero powers of `y`, hence is jointly continuous as well.
2. All lower jets are already jointly continuous on that compact cell. The definitions of energy,
   its two first and second derivatives, `(H,V)`, and `(∂x H, ∂y V)` are finite algebraic
   combinations of these jets; hence currents and divergences are jointly continuous and
   integrable on `D_Y`.
3. The corpus derivative theorems give `∂x H` and `∂y V` literally. One-dimensional FTC on every
   horizontal and vertical fibre, followed by Fubini, converts the standard set integral of
   `∂x H + ∂y V` into horizontal side/arc flux plus top-minus-arc vertical flux.
4. For heights `1 ≤ y ≤ Y`, translation identifies the two vertical sides, so their oriented
   difference is zero. For lower fibres the circular substitution
   `y = sqrt(1-x²)` combines horizontal and vertical arc contributions into radial current.
   C-A.9t4c's inversion anti-invariance pairs the two half-arcs pointwise, leaving exactly the two
   cusp-top vertical currents.
5. C-A.9t4b states `2 D₂ = y²(∂x H + ∂y V)`. Since `y>0` on `D_Y`, division by `y²` is valid;
   therefore `M₂(P,Q;Y)` equals the paired actual second-current cusp top. This also proves equality
   with the literal coordinate-split truncated bulk. `[PROVED HERE]`

C-A.9t4c then decomposes this cusp top exactly into its affine zero-frequency family plus a rapidly
decaying remainder, with finite part zero and remainder limit zero. No analytic, Fubini, boundary,
or decay premise remains.

## Log

- 2026-08-29 — corpus and literature audit; hostile verdict `[BRIDGE]`; dependency-complete paper proof closed
