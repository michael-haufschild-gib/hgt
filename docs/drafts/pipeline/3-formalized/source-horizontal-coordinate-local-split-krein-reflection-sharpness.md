# Coordinate-local split-Krein reflection sharpness

- **ID:** SH-LOCAL-SPLIT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · shared HB/FZZ-P/PW-B/RBH Ward chain
- **Statement:** One fixed bounded isometric involution on `ℓ²(ℕ,ℝ) ⊕ ℓ²(ℕ,ℝ)` negates the split form, preserves every coordinate-support sector, and realizes every finite source-horizontal packet and FE reflection inside that packet's finite prefix, including every hypothetical off-wall Xi copy.

## Goal

Kill causal/locality-only repair of shared four-route producer. Targeted chain is
`source-specific causal phase/sign law → fixed Ward orientation → shared receiver extinction → RH`.
Result leaves only source-coupled cross-coordinate phase/weight law, irreversible evolution, or nonlinear/singular/domain-changing dynamics.

## Gates

- [x] 0 → 1  in-progress: exact corpus-derived statement and attack
- [x] 1 → 2  fully-proven: dependency-closed paper proof
- [x] 2 → 3  formalized: Lean theorem, target build, axiom audit
- [ ] 3 → 4  publication-ready

## Corpus basis

- `SourceHorizontalUniversalSplitKreinReflectionSharpness`: fixed split carrier and exact all-packet reflection.
- `ThetaCuspHawkingHorizonRedshiftWindingLadder`: remaining observability producer is source-specific; generic scattering permits dark transmission zeros.
- `ThetaCuspHawkingTiltedMirrorOpticalTheoremEndpoint`: timelikeness and exact optical balance do not exclude dark modes.
- `ThetaCuspHawkingCentralAnchorSchwarzAllPassPairNoGo`: intensity, central phase anchor, and source reality retain off-line all-pass sectors.
- `ThetaCuspHawkingBMPhaseSensitiveReflectedPairCancellationNoGo`: reflected/global complex cancellation does not force copywise darkness.

## Attack

Define coordinate support by simultaneous vanishing of both `ℓ²` sectors outside `S ⊆ ℕ` and finite-prefix support by vanishing at every `n ≥ m`. Sector swap preserves all coordinate supports exactly, is norm-preserving and involutive, and negates the split form. Existing canonical packet embeddings use only coordinates `< m`; sector swap preserves that prefix. Re-run left/right orientation landing with these exact embeddings.

## Paper proof `[PROVED HERE]`

Let `H = ℓ²(ℕ,ℝ) ⊕ ℓ²(ℕ,ℝ)`, `Q(u,v)=‖u‖²-‖v‖²`, and `T(u,v)=(v,u)`. Product-norm symmetry gives `‖Tx‖=‖x‖`; directly `T²=I` and `Q(Tx)=-Q(x)`. For any `S ⊆ ℕ`, simultaneous vanishing of `u_n,v_n` outside `S` is unchanged by swapping them. Thus `T` preserves every coordinate-support sector in both directions.

For packet size `m`, weights `w_i≥0`, and `y_i=√w_i x_i`, put
`f₊(x)=((y_0,…,y_{m-1},0,…),(Σ_i y_i,0,…))` and `f₋=Tf₊`.
Both maps vanish at every coordinate `n≥m` because `m≥2`. Exact expansion gives
`Q(f₊x)=Σ_i w_i x_i²-(Σ_i √w_i x_i)²` and `Q(f₋x)=-Q(f₊x)`.
The corpus proves that this reservoir form is the literal source-horizontal packet form with sign `+` left of the wall and sign `-` right of it, while FE reflection reverses that sign and preserves the weights. Hence use `f₊` on a left copy and `f₋` on a right copy; applying `T` realizes the reflected packet. Every landing and reflected landing stays in the same prefix. This proves the closed route-kill statement.

## Hostile audit

- Not a degenerate filtration: invariance holds for every coordinate subset, hence for all prefixes, tails, and single-time sectors.
- Not merely receiver repackaging: theorem constructs off-wall countermodels satisfying stronger locality axioms.
- Does not kill source-dependent phase transport: cross-coordinate/source-labelled laws remain outside statement.
- Literature audit through 2026-08 found general Krein/Hardy realization theory and a 2026 critical-line-only Krein interpretation of `ξ`, but no exact coordinate-local sharpness theorem for the literal Xi source packets: arXiv:2606.22453, arXiv:2606.13932, arXiv:1804.05255.

## No-go closure

- **Exact killing mechanism:** sector exchange acts independently at each coordinate, so maximal support locality coexists with universal off-wall landing.
- **Strongest positive survivor:** any viable causal producer must impose source-semantic cross-coordinate phase/weight compatibility or abandon reversible bounded local dynamics.
- **New insight:** abstract causality/locality joins capacity, essential bipolarity, and bounded reflection existence as nonselective.
- **Status:** Lean theorem `sourceHorizontalCoordinateLocalBoundedSplitKreinReflectionRouteKilled` in `SourceHorizontalCoordinateLocalSplitKreinReflectionSharpness`; direct check and target `lake build` pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Formal lint reports only pre-existing unrelated unreachable modules.
