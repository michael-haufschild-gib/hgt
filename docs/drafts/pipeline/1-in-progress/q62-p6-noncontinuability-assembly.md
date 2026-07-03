# P6 (#118) both-connected rigidity — located to ONE sub-gap: hnb for interior-nonempty c₁

- **ID:** q62-p6-noncontinuability-assembly
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (most ingredients proven; one located sub-gap remains)
- **Source:** q62 both-connected close, task #118 (SmoothPieceRigidity / P6). Michael's chosen
  investment (2026-07-03).

## The precise state (mapped 2026-07-03 — NOT "the Montel/Fatou epic")
The both-connected pair `NoRelation` is delivered by
`RelativeRigidityNaturalBoundary.noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable`,
which takes these inputs — all PROVEN except one:
- `β` global branch analytic on `Kᶜ`, matching `bottcherCoord c₁`, carrying the modulus — proven
  (`exists_global_branch_covering_bijective_of_mem_mandelbrot`, Gap 2 closed).
- `γ = φ_{c₂}` analytic across `frontier K_{c₁}` — holds by exposure (`∂K_{c₁} ⊆ K_{c₂}ᶜ`, the
  HoleFreeTip clause), since `bottcherCoord c₂` is analytic on `K_{c₂}ᶜ`.
- transcendence of `φ_{c₂}` — proven (`phiMero_transcendental_of_mem_mandelbrot`, unconditional).
- `hinput` (a relation ⟹ a frontier point `z₀` with separable continued fibre + boundary limit) —
  the pigeonhole/repelling producer, scaffolded in `RelativeRigidityGlobalBranch`.
- **`hnb : ∀ z₀ ∈ frontier K_{c₁}, ¬ ContinuesAcross β Kᶜ z₀`** — the natural boundary of the
  Böttcher coordinate across the Julia frontier. THIS is the crux input.

**`hnb` is already PROVEN for empty-interior connected `c₁`:**
`ConnectedNaturalBoundaryMandelbrot.exists_global_branch_naturalBoundary_of_emptyInterior_of_mem_mandelbrot`
(`c ∈ mandelbrot`, `interior (filledJulia c) = ∅`) gives `β` with exactly the `hnb` clause, via
`hnb_of_emptyInterior_modulus` (empty interior + Böttcher modulus ⟹ no basin branch continues across
any frontier point). Unconditional. So for dendrite / Misiurewicz / ∂M-type connected `c₁`, the
both-connected rigidity is essentially assembled from proven pieces.

## THE located remaining sub-gap
`hnb` for **interior-NONEMPTY** connected `c₁` — the hyperbolic-component parameters (main cardioid
and other attracting-cycle components), where `K_{c₁}` is a quasidisk and `hnb_of_emptyInterior_modulus`
does NOT apply. For these, `K_{c₁}` is bounded by a quasicircle `J_{c₁}` (locally connected, Jordan).
Route (proven ingredients):
  1. `natural_boundary_of_even_fe` (PROVEN): the even-FE disk model `h` of `c₁` has a natural boundary
     on the unit circle for `c₁ ∉ {0,-2}` (its Fatou–Ritt step is the elementary `c_mem_of_even_holo_ball`).
  2. Bridge: if `β` continued across `frontier K_{c₁}` at `z₀`, the continuation SUPPLIES the boundary
     value `‖β z₀‖ = 1` and, via `z = ψ(w)`, `t = 1/w`, an analytic continuation of `h` across the arc
     at `ζ₀ = 1/β(z₀)` — contradicting (1). For a quasidisk `K_{c₁}`, `ψ` extends continuously to the
     circle (Carathéodory, quasicircle ⟹ locally connected boundary), so the point→arc correspondence
     is valid. This is the same even-FE natural boundary already powering the UNCONDITIONAL
     single-coordinate transcendence for ALL `c ∈ mandelbrot ∖ {0,-2}` — so the ingredient exists; only
     the `hnb`-shaped (analytic-continuation) packaging for interior-nonempty `c₁` is unwired.

So #118 is NOT the full Montel/Fatou epic — it is: (a) empty-interior `hnb` [PROVEN], plus
(b) interior-nonempty `hnb` via even-FE + quasidisk Carathéodory [the one located sub-gap], plus
(c) wiring `hinput`/γ into `noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable`.

## Refinement (2026-07-03, second pass)
- **Empty-interior both-connected NoRelation is ALREADY assembled in-tree**:
  `RelativeRigidityNaturalBoundary.noRelation_phiMero_of_emptyInterior_global_gamma_frontier_separable`
  derives `hnb` from the basin modulus (`hnb_of_emptyInterior_modulus`) internally, leaving only
  `hG` (proven), `γ`-exposure (HoleFreeTip / #124), and `hinput` (frontier-fibre producer, scaffolded
  via the pigeonhole/repelling machinery #112–117). So empty-interior `c₁` is close to done.
- **Interior-nonempty `hnb` — clean discharge framing (the DUAL of the empty-interior argument).**
  The empty-interior proof (`not_continuesAcross_of_emptyInterior_modulus`) needs
  `ball z₀ r ∩ interior K = ∅`, which FAILS at a frontier point when `interior K ≠ ∅`. But nonempty
  interior powers the dual: if `β` continues to `g` across `z₀`, then `u := log‖g‖` is harmonic near
  `z₀` (`g ≠ 0` there since `‖g‖ ≈ ‖φ‖ ≈ 1`), `u = G_{c₁} > 0` on the basin side, and `u = 0` on the
  frontier arc `J_{c₁} ∩ nbhd`. So `J_{c₁}` sits in the NODAL SET `{u = 0}` of a harmonic function.
  Dichotomy: either `{u=0}` has interior ⟹ `u ≡ 0` ⟹ `g` constant ⟹ contradiction (`g = φ`
  nonconstant); or the nodal arc is real-analytic ⟹ `J_{c₁}` locally real-analytic ⟹ (the proven
  `c_mem_of_even_holo_ball` even-FE rigidity) `c₁ ∈ {0,-2}` ⟹ contradiction. Either way `hnb` holds.
  Needs: (i) `log‖g‖` harmonic (mathlib-adjacent), (ii) harmonic nodal-set analyticity, (iii) the
  `J_{c₁}` analytic ⟹ `c₁∈{0,-2}` bridge (even-FE model at the arc). Genuine multi-step, not a tweak.

## PROGRESS (2026-07-03, verified Lean) — the `u ≡ 0` dichotomy branch is discharged
`GaloisForLFunctions/Bottcher/InteriorModulusObstruction.lean` (axiom-clean, in the Bottcher umbrella):
- `Bottcher.eqOn_const_of_norm_const` — analytic + constant modulus on preconnected open ⟹ constant
  (strong max modulus `eqOn_of_isPreconnected_of_isMaxOn_norm`).
- `Bottcher.false_of_norm_one_on_open_of_norm_ne` — if `g` is analytic on preconnected open `U`,
  `‖g‖ ≡ 1` on a nonempty open `V ⊆ U`, and `‖g‖ ≠ 1` somewhere in `U`, then `False` (ball inside `V` +
  identity theorem spread). This IS the `u ≡ 0` branch: a continuation `g` of `φ_{c₁}` cannot have
  `‖g‖ ≡ 1` on an open piece while equaling the nonconstant `φ_{c₁}` (`‖φ‖ > 1`) on the basin side.

- `Bottcher.norm_continuation_eq_one_at_frontier` — if `β` carries the Böttcher modulus on the basin
  and continues analytically across a frontier point `z₀`, the continuation `g` has `‖g z₀‖ = 1` (the
  frontier is the `G_c = 0` level). Unconditional; the entry-point brick for BOTH interior-empty and
  interior-nonempty routes (pins the boundary modulus regardless of `g`'s interior behaviour).

So the interior-nonempty `hnb` dichotomy now needs only the OTHER (hard) branch.

## Next brick (attack next tick)
The hard branch: the nodal arc `{u = 0} ⊇ J_{c₁} ∩ nbhd` is real-analytic ⟹ `J_{c₁}` locally analytic
⟹ `c₁ ∈ {0,-2}`. Two sub-bricks:
  (a) `u := log‖g‖` is harmonic near `z₀` and `= 0` on the frontier arc, `> 0` on the basin side
      (from `‖β‖ = exp(G)`, `G → 0` at the frontier) — sets up the nodal set.
  (b) the nodal arc of a harmonic function is real-analytic, and `J_{c₁}` real-analytic ⟹ `c₁∈{0,-2}`
      via the even-FE model at the arc (the proven `c_mem_of_even_holo_ball`). This is the substantive
      piece; check mathlib for harmonic nodal-set analyticity, else route through the even-FE reflection.
Then assemble both branches into `not_continuesAcross_of_nonemptyInterior` and wire it (with the
empty-interior case) into a unified `hnb_of_mem_mandelbrot` discharging the crux for all `c₁∈M∖{0,-2}`.

## Original next-brick note (superseded by the PROGRESS block above)
Prove `hnb_of_nonemptyInterior_even_fe`: for `c₁ ∈ mandelbrot ∖ {0,-2}` with `interior K_{c₁} ≠ ∅`,
the global branch `β` satisfies `∀ z₀ ∈ frontier, ¬ ContinuesAcross β Kᶜ z₀`, from
`natural_boundary_of_even_fe` + the `β`-continues ⟹ `h`-continues-across-arc bridge. First read
`DendriteContinuesAcross` (the bridge home) + `hnb_of_emptyInterior_modulus` to reuse the packaging,
and check whether the even-FE bridge in the UNCONDITIONAL transcendence proof already yields the
point→arc step without the empty-interior hypothesis (it may need only `β`-continuation, not interior).

## Gates
- [x] 0 → 1  in-progress: core located to `hnb` (interior-nonempty); all other inputs proven/scaffolded.
- [ ] 1 → 2  fully-proven: `hnb` for interior-nonempty `c₁` + final wiring.
- [ ] 2 → 3  formalized: `hnb_of_nonemptyInterior_even_fe`, wired through the natural-boundary rigidity.
- [ ] 3 → 4  publication-ready.

## Log
- 2026-07-03 — created. Located #118's true state: both-connected rigidity =
  `noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable`; crux input `hnb` PROVEN for
  empty-interior connected `c₁`; the one remaining sub-gap is `hnb` for interior-nonempty (hyperbolic)
  `c₁`, reachable from the PROVEN even-FE natural boundary + quasidisk Carathéodory. Reframes the epic
  from Montel/Fatou to one located natural-boundary packaging lemma.

## BREAKTHROUGH (2026-07-03) — the "quasidisk topology" wall was not real
The previous PROGRESS/next-brick blocks framed interior-nonempty `hnb` as gated on a deep topological
input (`FrontierSeparation` = the frontier locally separating basin from interior, quasidisk Jordan-arc
structure) plus an "arc assembly" also needing frontier local-connectivity. Both are now ELIMINATED —
they were an over-estimate. In the `deriv g z₀ ≠ 0` case (reached via the proven
`exists_frontier_deriv_ne_zero_of_connected`), the continuation `g` is a LOCAL BIHOLOMORPHISM, so the
level set `{|g| = 1}` near `z₀` is automatically the biholomorphic image of the unit circle. The
exterior side `{|g| > 1}` near `z₀` is then a CONNECTED set (biholomorphic image of the connected lune
`ball(w₀,ε) ∩ {|w|>1}`) disjoint from the frontier and meeting the basin; and since
`Kᶜ ⊔ interior K = frontierᶜ` is a disjoint union of two opens, a connected subset meeting `Kᶜ` lands
wholly in `Kᶜ`. That IS `FrontierSeparation`, from elementary topology — no nodal-set/harmonic/
quasicircle theory.

**Verified Lean (InteriorModulusObstruction.lean, axiom-clean, in the Bottcher umbrella, +7 decls):**
- `isPreconnected_ball_one_inter_exterior` / `isPreconnected_ball_inter_exterior` — the exterior lune
  at any unit-circle point is preconnected (star-convex at `p = (1+ε/2)·w₀`, `0<ε≤1/2`).
- `eqOn_lune_of_seed` — identity theorem on the lune (`γ = ψ` on the whole exterior side from one seed).
- `eventuallyEq_gamma_psi_seed` — the basin side supplies the seed agreement `γ = ψ`.
- `hγψ_of_continuation` — `γ = ψ` on the exterior near `w₀` with **no** `FrontierSeparation`.
- `continuesAcross_h_of_continuation_unconditional` — the `FrontierSeparation`-FREE single-point bridge:
  raw local-inverse data + connected Böttcher package ⟹ `ContinuesAcross h t₀` (`t₀·w₀ = 1`).
- `arc_of_continuesAcross` — `ContinuesAcross h t₀` ⟹ arc-continuation (the witness set is OPEN, so the
  arc is free); this is the exact hypothesis `natural_boundary_of_even_fe` refutes.

**Remaining work for interior-nonempty `hnb` is now pure WIRING of proven pieces (no new deep math):**
(a) reduce raw `ContinuesAcross β Kᶜ z₀` to `deriv ≠ 0` at a nearby frontier point + local inverse `γ`
    analytic on a ball (`exists_localInverse_of_continuation`, shrink `ε ≤ 1/2`);
(b) supply the connected Böttcher package — `ψ` analytic on the exterior + `hβmod` + `hψβ`
    (`exists_global_branch_covering_bijective_of_mem_mandelbrot`) + even-FE disk model `h` with bridge
    `h t = t·ψ(1/t)` (`exists_full_disk_model_of_mem_mandelbrot` / DiskModelGlobal);
(c) `natural_boundary_of_even_fe` (proven) fed by `arc_of_continuesAcross` ⟹ contradiction for
    `c ∉ {0,-2}`.
This does NOT close the full both-connected pair: `#124` exposure (`∂K_{c₁} ⊆ K_{c₂}ᶜ`) and the
`hinput` pigeonhole producer remain co-equal obligations; and full q62 still needs comparable-norm
(external OP16-A) and small-norm coverage. The full q62 proof is NOT complete.

## INTERIOR-NONEMPTY `hnb` CLOSED (2026-07-03) — the sub-gap of #118 is proven, unconditionally
`Bottcher.hnb_of_mem_mandelbrot_connected` (formal/GaloisForLFunctions/Bottcher/InteriorNonemptyHnb.lean,
axiom-clean): for EVERY connected `c ∈ mandelbrot ∖ {0,-2}` — interior-nonempty (hyperbolic / quasidisk)
included, with no empty-interior hypothesis — the global Böttcher branch `β` has the Julia frontier as a
genuine natural boundary, `∀ z₀ ∈ frontier, ¬ ContinuesAcross β (filledJulia c)ᶜ z₀`. This is the crux
input `hnb` of the both-connected rigidity engine, and it needed NONE of the quasidisk / harmonic-nodal
theory earlier feared. The package (`β, ψ, h` + modulus + bridge) is instantiated unconditionally from
`exists_full_disk_model_of_mem_mandelbrot` and `exists_global_branch_with_inverse_of_mem_mandelbrot`.

Reduction lemmas (all axiom-clean): `false_of_continuation_deriv_ne_zero_package`,
`false_of_continuation_connected_package` (deriv-dichotomy; no interior hypothesis, subsumes the
empty-interior case), `not_continuesAcross_beta_of_connected_package` (abstract-predicate adapter).

**Gate 1 → 2 (the `hnb` half): DONE.** What remains for the both-connected PAIR `NoRelation` is the
OTHER inputs of `noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable`: the exposure
clause `∂K_{c₁} ⊆ K_{c₂}ᶜ` (#124) and the `hinput` frontier-fibre producer (#112–117, scaffolded).
Full q62 additionally needs comparable-norm disconnected (external OP16-A) and small-norm coverage.
The full q62 proof is NOT complete. Next brick: instantiate the engine with
`hnb_of_mem_mandelbrot_connected` to reduce the both-connected capstone to exposure + `hinput` only.

## `hnb` WIRED — both-connected pair reduced to exposure + `hinput` only (2026-07-03, verified)
`Bottcher.noRelation_phiMero_bothConnected_hnbFree` (formal/GaloisForLFunctions/Bottcher/
Q62BothConnectedHnbFree.lean, axiom-clean): the both-connected pair `NoRelation (phiMero c₁) (phiMero
c₂)` for connected `c₁ ∈ mandelbrot ∖ {0,-2}`, with `hnb` discharged internally
(`hnb_of_branch_matching`). It is now conditional on **exactly**: `hG` (transcendence of `φ_{c₂}`,
proven), the **exposure** data (`γ = bottcherCoord c₂` analytic on `K_{c₁}ᶜ` and across `∂K_{c₁}` —
#124), and `hinput` (the pigeonhole frontier-fibre producer, #112–117 scaffolded). `hnb` (#118) is off
the critical path. Remaining both-connected obligations: #124 exposure + turning the `hinput` scaffold
into a theorem. Full q62 additionally needs comparable-norm (OP16-A) + small-norm. NOT complete.
