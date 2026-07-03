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

## SMOOTHPIECERIGIDITY (general #118 gatekeeper) REDUCED TO ONE INPUT (2026-07-03, verified)
`Bottcher.smoothPieceRigidity_of_reflectionCore` (formal/GaloisForLFunctions/Bottcher/
Q62SmoothPieceReduction.lean, axiom-clean): for connected `c₁ ∈ mandelbrot ∖ {0,-2}`,
`SmoothPieceRigidity c₁ c₂` (the *general* both-connected gatekeeper, route 2, used by
`q62_phiMero_bothconnected_of_op6`) reduces to **exactly** `ReflectionCore c₁` — Schwarz reflection
across an analytic Julia arc. Everything else is proven internally:
- `separable_of_distinct_roots` (degree-N poly with N distinct roots ⟹ separable);
- `wfam_analyticOnNhd_of_smoothPiece` (the branch-analyticity upgrade: continuous root ⟹ analytic on
  `ball ∩ K_{c₂}ᶜ`, via IFT + branch uniqueness);
- the constant-branch case (unit-root exclusion + identity theorem on the connected basin);
- the endgame (contradiction via the proven `hnb_of_mem_mandelbrot_connected`).

So the earlier note "hnb not load-bearing for the general case" is corrected: `hnb` **is** the endgame
of the general gatekeeper. What remains for general both-connected: `ReflectionCore` (Schwarz reflection
+ boundary regularity, mathlib-absent) + `ExposedOneSided` (OP6) + `OneSidedDense` (#133). Full q62 also
needs comparable-norm (OP16-A) and small-norm. NOT complete. Next brick: attack `ReflectionCore`.

---

## Progress: Schwarz/Painlevé reflection ENGINE built (mathlib-absent core, axiom-clean)

`formal/GaloisForLFunctions/Bottcher/SchwarzReflection.lean` (new, in umbrella, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, lint clean):

* `differentiableOn_of_off_horizontal_line` — **the crown brick.** `f` continuous on open `U`,
  holomorphic on `U ∖ {im = a}` ⟹ holomorphic on `U`.  Proof is fully mathlib-native: **Morera on
  disks** (`isConservativeOn_and_continuousOn_iff_isDifferentiableOn`) + split a line-straddling
  rectangle at height `a` into two closed sub-rectangles whose *open interiors avoid the line*, each
  with vanishing boundary integral by `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
  (needs holomorphy only on the interior), summed by `intervalIntegral.integral_add_adjacent_intervals`.
  No limiting argument at the crossing edge.  mathlib has NO Schwarz reflection / Morera-glue / removable-
  along-a-line theorem — this supplies it.
* `differentiableOn_of_off_line` — general straight line `{(c z + d).im = a}`, `c ≠ 0`; affine conjugate.
* `differentiableOn_of_off_biholom_preimage_line` — reflection off `{z ∈ V | (c·ψ z + d).im = a}` for a
  partial biholomorphism `ψ` with holomorphic inverse `ψinv`.  **This is the exact form the discharge
  consumes**: with `ψ = Log ∘ wfam k` the modulus-one arc `{‖wfam k‖=1}` becomes `{(I·ψ).im = 0}`.

### Why this reframes the whole P6 epic
The old plan ("Montel blow-up → J in analytic curve → Fatou classification → c∈{0,−2}") is NOT needed.
The reflection engine gives a direct route: a modulus-one Julia piece forces the Böttcher branch `β₁`
to continue analytically across `∂K₁`, contradicting the natural boundary `hnb_of_mem_mandelbrot_connected`.
Concretely, to discharge `SmoothPieceRigidity` (⟹ general both-connected q62), what remains is **wiring,
no further mathlib-absent deep theorem**:

1. Pick `z₀ ∈ Uop∩S` with `deriv (wfam k) z₀ ≠ 0`  — DONE (`exists_frontier_piece_deriv_ne_zero`).
2. Package `ψ = Log∘wfam k` as a local biholo on a small `V ∋ z₀` (holomorphic IFT, already used in
   `exists_localInverse_frontier_arc`); the arc `= {‖wfam k‖=1}∩V = ψ⁻¹{im=0}`.
3. Define `F := β₁` on `V∩K₁ᶜ`, `:= wfam k` on `V∖K₁ᶜ`.  Continuous on `V` (β₁→wfam k at arc points of
   `S` from the modulus-one supply; wfam k continuous), holomorphic off the arc.
4. `differentiableOn_of_off_biholom_preimage_line` ⟹ `F` holomorphic on `V`.
5. `F = β₁` eventually on `𝓝[K₁ᶜ] z₀` ⟹ `ContinuesAcross β₁ (filledJulia c₁)ᶜ z₀` — the witness IS `F`.
6. Contradicts `hnb` (`hnb_of_mem_mandelbrot_connected`).  ∎ (works uniformly for dendrite/empty-interior
   AND positive-interior `c₁`, since ContinuesAcross only needs `F=β₁` on the basin-side neighbourhood.)

Open wiring sub-input to verify against the producer internals: that the basin-limit of `β₁` at
`x ∈ Uop∩S` equals **`wfam k x`** (not merely "some modulus-one root") — trace `hspine` /
`PairComponentPropagation` / `holeFreeTip_modulus_one_supply`.

## Progress: unit-circle reflection corollary banked (axiom-clean)

`formal/GaloisForLFunctions/Bottcher/SchwarzReflectionArc.lean` (new, umbrella, lint clean,
`[propext, Classical.choice, Quot.sound]`):

* `differentiableOn_of_off_unit_circle` — on an open preconnected slit-plane region `V`, `f`
  continuous on `V` and holomorphic off `{‖z‖=1}` ⟹ holomorphic on `V`.  Direct application of
  `differentiableOn_of_off_biholom_preimage_line` with uniformiser `ψ = Complex.log`, global inverse
  `Complex.exp` (no IFT), which carries `{‖z‖=1}` to the line `{(I·log z).im = 0}`.  Image-open via the
  open-mapping theorem (`AnalyticOnNhd.is_constant_or_isOpen`; the constant branch is impossible on a
  nonempty open set by a two-point argument, `log` injective).

Reflection stack now: horizontal-line → general-line → biholom-preimage-of-line → unit-circle.  Next
brick = the **general modulus-one arc** `differentiableAt_of_off_modulus_arc` (`f` holo off `{‖g‖=1}`
for a general analytic `g` with `deriv g z₀ ≠ 0`): compose the unit-circle corollary with the local
inverse `γ` of `g` (`exists_localInverse_of_continuation`) after a rotation `ρ = (g z₀)⁻¹` placing
`g z₀` at `1 ∈ slitPlane`.  That is the exact interface the smooth-piece discharge's `F`-construction
consumes (`g = wfam k`).  Remaining after that: the `F`-construction + the one-sided/two-sided case
split (two-sided dendrite case needs the Green's-function odd-reflection, a separate argument).

## Structural finding: SmoothPieceRigidity splits one-sided vs two-sided (reflection stack ≠ sufficient)

Tracing the discharge precisely: at a piece point z₀ ∈ Uop∩S with `deriv (wfam k) z₀ ≠ 0`, `wfam k` is a
local biholo, so `{‖wfam k‖=1}` near z₀ is a real-analytic arc splitting the ball into `{‖wfam k‖>1}`
(side A) and `{‖wfam k‖<1}` (side B).  `β₁ = wfam k` on side A (basin, `‖β₁‖=‖wfam k‖>1`).  Two cases:

* **One-sided** (positive-interior `c₁`): side B ⊆ interior `K₁`, so side A = the *whole* local basin.
  Then `wfam k` (analytic across the arc, = β₁ on all local basin) IS a full `ContinuesAcross β₁ z₀`
  witness ⟹ contradicts `hnb_of_mem_mandelbrot_connected`.  **The reflection stack closes this.**
* **Two-sided** (dendrite / empty-interior `c₁`): side B is *also* basin, with `β₁ = wfam_{k'}` there,
  `k' ≠ k` (`‖wfam_{k'}‖>1` on B while `‖wfam k‖<1`).  Then β₁ has DISTINCT one-sided limits
  `wfam k(z₀) ≠ wfam_{k'}(z₀)` at z₀, so β₁ is *not continuous across* — no single analytic function
  equals β₁ on both sides.  `ContinuesAcross β₁ z₀` genuinely FAILS, `hnb` holds vacuously, and the
  reflection route gives NO contradiction.  **The reflection stack does NOT close this case.**

The two-sided case needs a different refutation: `greenFunctionDyn` is harmonic and `>0` on *both*
sides of the analytic arc, `=0` on the arc — impossible by harmonic odd-reflection (a nonneg harmonic
function vanishing on an interior analytic arc must be `≡0`).  Equivalently it is the even-FE dynamical
rigidity the project already carries (`natural_boundary_of_even_fe`, `c_mem_of_even_holo_ball`): a
smooth two-sided Julia arc forces `c₁ ∈ {0,−2}`.  So SmoothPieceRigidity = one-sided (reflection stack,
now built) ⊕ two-sided (harmonic odd-reflection / even-FE, project has the ingredient, wiring pending).

NET this session: the mathlib-absent Schwarz/Painlevé reflection engine is PROVEN through the unit
circle (4 axiom-clean lemmas), closing the one-sided half of the SmoothPieceRigidity discharge and
locating the two-sided half precisely.  Full q62 NOT complete (SmoothPieceRigidity two-sided + the
g-arc packaging + ExposedOneSided(OP6) + OneSidedDense(#133) + OP16-A + small-norm all remain).

## Correction: the one-sided discharge is DIRECT — reflection is not the tool it needs

Building `differentiableAt_of_off_modulus_arc` and tracing the concrete discharge revealed the
"Schwarz reflection core" framing was a detour.  Key fact (now verified against the producer):
`wfam k` is analytic on `ball z₁ ρ ∩ K₂ᶜ`, and the piece `S ⊆ K₂ᶜ` (the `hSK₂` clause), so at a piece
point `z₀ ∈ Uop∩S` **`wfam k` is already analytic ACROSS the Julia frontier** (a full 2-D neighbourhood,
`z₀ ∈ ball∩K₂ᶜ` open).  Therefore:

* **One-sided case** (the `{‖wfam k‖<1}` side is interior `K₁`): the local basin = the `{‖wfam k‖>1}`
  side, and `β = wfam k` there (root-matching + distinctness pin the branch index to `k`).  So
  `⟨wfam k, (analytic at z₀), (wfam k = β on 𝓝[Kᶜ]z₀)⟩` IS a `ContinuesAcross β z₀` witness — **directly,
  with no reflection**.  Contradicts `hnb`.
* **Two-sided case** (the `{‖wfam k‖<1}` side is ALSO basin): this is exactly the smooth-Julia-arc
  configuration — and a smooth two-sided Julia arc occurs precisely for `c ∈ {0,−2}` (`[-2,2]` / the
  circle).  Ruling it out for `c ∉ {0,−2}` is the even-FE dichotomy `c_mem_of_even_holo_ball` (the
  project has it), NOT holomorphic reflection.

So the SmoothPieceRigidity discharge = **direct one-sided** (root-matching + one-sidedness) ⊕
**even-FE two-sided** (`c_mem_of_even_holo_ball`).  Neither branch uses the Schwarz/Painlevé reflection
stack.  The 5 reflection lemmas (`SchwarzReflection*.lean`) are correct, axiom-clean, reusable
mathlib-absent infrastructure (Morera-gluing / reflection across a line / biholo-preimage / unit-circle
/ modulus-arc) — a formal Böttcher–Julia library legitimately wants them — but they are **not on the
q62 critical path**.  Kept in-tree as general infrastructure; not load-bearing for any capstone.

REAL remaining discharge bricks (no reflection): (1) the root-matching sub-fact `β = wfam k` on the
one-sided local basin (trace `hspine`/`PairComponentPropagation`: the pigeonhole index `k` = the
`β`-limit branch); (2) the one-sided/two-sided dichotomy as a clean Lean split; (3) wire
`c_mem_of_even_holo_ball` into the two-sided branch.  These are genuine dynamics/analysis, the true
content of #118.

## Confirmed: the branch-following machinery is already built; #118 gap = hinput + #124 + even-FE

Tracing the direct-discharge inputs shows the pieces I was about to build already exist:
* `eqOn_branch_of_relation_analytic` / `dendrite_branch_limit_analytic` (RelativeBranchFamily.lean 145,
  169) — given `hβrel` (β a root on a preconnected basin sector), β follows a single branch `w k` to a
  *simple-root* boundary limit `Tendsto β (𝓝[K₁ᶜ]z₀) (𝓝 w₀)`.  This IS the one-sided root-matching.
* `hβrel_all` (RelativeRigidityGlobalBranch.lean:486) — β is a root of the fibre polynomial on ALL of
  `K₁ᶜ` (identity theorem on the connected basin) — already proven.
* The natural-boundary engine `noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable`
  packages all this behind ONE hypothesis `hinput` (RelativeRigidityNaturalBoundary.lean:31): a producer
  giving, for any candidate relation, a frontier `z₀` + separable continued fibre + boundary limit.

So the genuine remaining q62 gaps are exactly the previously-identified deep/external inputs, unchanged
by this session's reflection work:
1. **`hinput` as a full theorem** — turn the pigeonhole scaffold (RelativeRigidityGlobalBranch, #112–117)
   into the producer the engine consumes.  (Load-bearing, deep — entangles the relation relocation onto
   the frontier.)
2. **Exposure / #124 collar** — `γ = φ_{c₂}` analytic across `∂K₁` (`∂K₁ ⊆ K₂ᶜ`), the Jordan/Schoenflies
   collar.  Co-equal deep input.
3. **even-FE two-sided** — wire `c_mem_of_even_holo_ball` into the two-sided (dendrite / `c∈{0,−2}`) branch.
4. External/other regimes: OP6, #133, OP16-A (external open problem), small-norm (tower degenerates as
   `h→0`; `1000→100` relaxable but does not close it).

Session net: reflection stack built (correct, reusable, OFF the q62 critical path); discharge structure
clarified (direct one-sided ⊕ even-FE two-sided); confirmed branch-following already assembled.  Full
q62 NOT complete — remaining work is the multi-session `hinput`/#124/even-FE sub-projects + external
open problems, not isolated bricks.

## hinput as a theorem — exact construction, single gap isolated

Traced `hinput` (RelativeRigidityNaturalBoundary.lean:31) to a composition of **five already-proven
reusable lemmas** plus **one isolated topological input**.  Given a candidate relation `(Q,s)` vanishing
on `U`, with continued-fibre coeffs `a i z = (Q i).eval₂ (evalRingHom z) (γ z)`:

1. **Minimal separable relation** — `exists_separable_relation_of_relation` (RelativeMinimalRelation.lean:319):
   reduce `(Q,s)` to a minimal `T'` with a separable-fibre witness + leading-coeff-nonzero + no-constant.
   (Subtlety: the engine's `hinput` conclusion names the *original* `(Q,s)` continued fibre, so the
   producer must carry separability of the fibre that the engine consumes — reconcile the minimal `T'`
   with the original `a s`, or restate `hinput` on the minimal relation.)
2. **Relocate onto the frontier** — `exists_sparse_fibre_separable_countableAvoidance` (RelativeFibreGeneric.lean:125):
   countable-avoidance against the discriminant zero-set (a countable set, `analyticOnNhd_zeros_countable`)
   using perfectness of `frontier (filledJulia c₁)` — gives `z₀ ∈ frontier` with `a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable`.
3. **Branch family at z₀** — `exists_branch_family_analytic` (RelativeBranchFamily.lean:84): the `N` continuous
   separated roots `w k` on `ball z₀ r` (`a i` are `ContDiffAt` at `z₀` since `γ` is analytic across the
   frontier, `hγfront`).
4. **β is a root on the whole basin** — `relation_eq_zero_basin_analytic_of_open` (BasinColimit.lean:1030):
   from the relation on `U` + `β`, `a` analytic on `K₁ᶜ`, the identity theorem gives `∀ z ∈ K₁ᶜ, ∑ a_i z (β z)^i = 0`.
5. **Boundary limit** — `dendrite_branch_limit_analytic` (RelativeBranchFamily.lean:169): from the branch
   family + a **preconnected basin neighbourhood `U ∈ 𝓝[K₁ᶜ] z₀`** + `β` root on `U`, produce
   `Tendsto β (𝓝[K₁ᶜ] z₀) (𝓝 w₀)` with `w₀` a simple root — the `hinput` tuple.

**The single isolated gap** is step 5's input: a *preconnected basin neighbourhood* at `z₀` (equivalently
a `𝓝[K₁ᶜ]z₀`-basis of preconnected basin sets = local connectivity / one-sidedness of the basin at `z₀`).
This is co-countable for connected `c₁` (dendrite: countable branch points; hyperbolic: quasicircle,
one-sided everywhere), so it combines with step 2's countable-avoidance — relocate to avoid BOTH the
discriminant AND the countably-many non-one-sided points.  Hence:

> **`hinput` ⟸ `{z ∈ frontier(filledJulia c₁) : the basin has no preconnected 𝓝[K₁ᶜ]z-basis}` is countable.**

That co-countable-one-sidedness statement is the genuine remaining topological content (the same
frontier-local structure as `FrontierSeparation` / #124).  The dense-approach variant
(`false_of_global_basin_branch_analytic_denseApproach`, RelativeDenseApproach.lean:129) trades it for a
`hApre`+`hAdense` dense preconnected basin approach — weaker, but still a per-point topological fact.

Everything except that one topological input is built and named above; `hinput` is a mechanical
assembly of steps 1–5 once it is supplied.

## hinput DISCHARGED as a theorem (2026-07-03, verified axiom-clean, plugs into the engine)

`formal/GaloisForLFunctions/Bottcher/Q62HinputAssembly.lean` (new, umbrella, lint clean,
`[propext, Classical.choice, Quot.sound]`).  The natural-boundary engine's `hinput` — previously
NOWHERE discharged in the tree, always passed up as a hypothesis — is now a theorem, built by composing
`exists_branch_family_analytic` + `relation_eq_zero_basin_analytic_of_open` + `dendrite_branch_limit_analytic`
+ `exists_sparse_fibre_separable_uncountable`.  Four decls:

* `hinput_tuple_of_basin_locally_connected` — back-half: separable frontier point + β-root-on-basin +
  local basis of preconnected basin nhds ⟹ the tuple (separable, frontier, `Tendsto β (𝓝[K₁ᶜ] z₀) w₀`).
* `hinput_tuple_of_relation` — middle: relocate a separable-fibre witness onto the frontier (avoiding the
  discriminant AND the non-locally-connected points) via the uncountable-LC input.
* `hinput_tuple_of_engine_relation` — wiring: instantiate with the engine's `a i = (Q i)(γ)`, deriving
  analyticity across the frontier and `β`-root-on-basin from the engine's own hypotheses.
* `hinput_of_witness_of_uncountableLC` — the ∀-form matching the engine's `hinput` signature EXACTLY;
  verified to discharge `noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable` (a
  `plug.lean` example produces `NoRelation` from it).

`hinput` is reduced to exactly **two isolated inputs**, both cleanly named:
1. `UncountableLocallyConnectedFrontier c₁` — the topological one-sidedness (co-countable for connected
   `c₁`: countable branch points on a dendrite, a quasicircle for hyperbolic parameters).
2. `hwitness` — a per-relation separable-fibre witness in the basin (the squarefree / minimal-relation
   content, from `exists_separable_relation_of_relation`).

NET: the natural-boundary route's `hinput` is off the open list — it is a theorem modulo (1)+(2).
Combined with `hnb` (PROVEN, `hnb_of_mem_mandelbrot_connected`) and the exposure/#124 collar, the
both-connected pair via the natural-boundary engine now needs only: exposure (#124) + the two hinput
inputs above.  Full q62 still open (SmoothPieceRigidity route, OP16-A, small-norm), but the `hinput`
gatekeeper the plan named is discharged.

## Input (2) DISCHARGED: hinput internalized via minimal reduction (2026-07-03, verified axiom-clean)

`formal/GaloisForLFunctions/Bottcher/Q62NaturalBoundaryMinimal.lean` (new, umbrella, lint clean,
`[propext, Classical.choice, Quot.sound]`, MainTheorems green 8920 jobs).  The separable-fibre witness
(`hinput` input (2)) is discharged: the engine's `hinput` names the ORIGINAL relation's continued fibre
(which need not be squarefree), so instead of feeding the engine, reduce to the MINIMAL relation `T'`
(`exists_separable_relation_of_relation` — squarefree by construction, separable-fibre witness free) and
replicate the natural-boundary contradiction on `T'`.  Separability transfers `bottcherCoord c₂ → γ` at
the witness `w ∈ U`.  Two theorems:

* `noRelation_phiMero_of_naturalBoundary_of_uncountableLC` — connected-pair `NoRelation` via natural
  boundary with `hinput` discharged internally; needs exposure + `hnb` + `UncountableLocallyConnectedFrontier c₁`.
* `noRelation_phiMero_bothConnected_of_uncountableLC` — the both-connected capstone: additionally
  discharges `hnb` (via `hnb_of_branch_matching`), so it needs ONLY `c₁ ∈ mandelbrot∖{0,-2}` connected +
  exposure (`hβan/hγan/hγfront/hγmatch`, the #124 collar) + the topological `hunc`.  `hG` proven.

NET: the both-connected pair via the natural-boundary route is reduced to EXACTLY two inputs —
**exposure (#124 collar)** and **`UncountableLocallyConnectedFrontier c₁`** (the topological one-sidedness,
co-countable for connected `c₁`).  Both `hnb` and `hinput` are off the open list.  Remaining for full q62:
#124 exposure, `hunc` (topological), the disconnected regimes (OP16-A, small-norm), and the separate
SmoothPieceRigidity route.

## CORRECTION: `UncountableLocallyConnectedFrontier` is hyperbolic-only, NOT co-countable for connected c₁

I mis-stated `hunc`'s applicability.  The predicate demands a preconnected `U ∈ 𝓝[K₁ᶜ] z` — a
preconnected basin *neighbourhood* (both sides).  Its truth by parameter type:

* **Empty-interior (dendrite) `c₁`**: at a non-branch frontier point the local basin is
  `ball ∖ arc` = TWO half-disks (both basin), separated by the arc.  Any `U ∈ 𝓝[K₁ᶜ] z` must contain
  both (they ARE the local basin) so is NOT preconnected.  **`hunc` is FALSE for dendrites.**  (This is
  also why `dendrite_branch_limit_analytic`'s full `𝓝[K₁ᶜ]`-limit needs a one-sided point — β has two
  distinct one-sided limits at a two-sided point.)
* **Positive-interior (hyperbolic) `c₁`**: basin on one side, interior `K₁` on the other ⟹ one-sided ⟹
  `hunc` holds (uncountably many, in fact all boundary points).

So `noRelation_phiMero_bothConnected_of_uncountableLC` covers **hyperbolic `c₁`**, and — via `hγan`
forcing `K₂ ⋐ K₁` (bottcherCoord c₂ can't continue across its OWN natural boundary `∂K₂`) — the nested
configuration `K₂ ⋐ interior(K₁)`.  A specific sub-case, not the general both-connected pair.  The
`hinput` DISCHARGE itself (Q62HinputAssembly + Q62NaturalBoundaryMinimal) is correct and axiom-clean;
only my claim "co-countable for connected c₁" was wrong.

The GENERAL (incl. dendrite) natural-boundary case uses the DENSE-APPROACH machinery already in the
tree (`dendrite_branch_limit_analytic_within`, `false_of_global_basin_branch_analytic_denseApproach`,
`OneSidedCofinal`), whose topological input is the weaker `ExposedOneSidedCofinal` / `OneSidedDense`
(#133) — a dense preconnected basin approach, which dendrites DO have.  My full-`𝓝` `hinput` is the
hyperbolic specialization; the general one reduces to the tree's existing `#133` one-sidedness lane.

## HARD CORRECTION: the natural-boundary route requires nesting K₂ ⊆ K₁ — restrictive, likely vacuous for the general pair

Deeper honesty check.  The natural-boundary engine's `hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ` with
`γ = bottcherCoord c₂` on `U` forces (identity theorem on the connected basin `K₁ᶜ`) `γ = bottcherCoord c₂`
on ALL of `K₁ᶜ`.  Since `bottcherCoord c₂` has `∂K₂` as a natural boundary (cannot continue into `K₂`),
`K₁ᶜ ∩ K₂ = ∅`, i.e. **`K₂ ⊆ K₁`** (global nesting).  For distinct connected quadratic Julia sets this
is a very special condition — plausibly empty (they don't nest).  So `noRelation_phiMero_bothConnected_of_
uncountableLC` and the whole natural-boundary lane (including my `hinput` discharge) apply to a
**restrictive, possibly vacuous** nested configuration — NOT the general both-connected pair.

The OPERATIVE general both-connected route is `SmoothPieceRigidity` (Q62SmoothPieceReduction / the
HbothconnAssembly engine): its coefficients come from `bottcherCoord c₂` analytic only on `ball ∩ K₂ᶜ`
around a frontier PIECE `S ⊆ K₂ᶜ` (LOCAL exposure — a bit of `∂K₁` outside `K₂`), NOT global nesting.
That is why it is the general route.

NET honest scope of this session's verified work: the reflection stack (correct, reusable, OFF the q62
path), the `hinput` assembly + minimal reduction (correct, axiom-clean, but serving the nested
natural-boundary route — restrictive/likely-vacuous for the general pair), the direct-discharge core.
Repeated framing as "the both-connected pair reduced to exposure + hunc" OVER-STATED generality: it is
the NESTED sub-case.  The general pair remains on `SmoothPieceRigidity` (one-sided direct ⊕ even-FE
two-sided) + local exposure.  The disconnected regimes (OP16-A, small-norm) are independent.

---

## Reflection engine landed on `ReflectionCore` (Q62ReflectionBridge.lean)

The Schwarz-reflection stack (`SchwarzReflection*.lean`), earlier noted as "off the critical path,"
is now wired directly onto the general both-connected gatekeeper. `smoothPieceRigidity_of_reflectionCore`
reduces #118 to `ReflectionCore c₁ β`; `Q62ReflectionBridge.lean` discharges its analytic core:

* `arcReflection_continuesAcross` — point-level bridge. At a frontier arc point `z₀`
  (`AnalyticAt φ z₀`, `deriv φ z₀ ≠ 0`, `‖φ z₀‖ = 1`), a function `f` continuous near `z₀`,
  holomorphic off `{‖φ‖=1}`, agreeing with `β` on `𝓝[K₁ᶜ] z₀`, IS a `ContinuesAcross β (K₁ᶜ) z₀`
  witness. Analyticity of `f` at `z₀` = `differentiableAt_of_off_modulus_arc` (mathlib-absent
  reflection across an analytic modulus-one arc); basin agreement = the `ContinuesAcross` clause
  verbatim. This is the exact hook contradicting `hnb`.

* `reflectionCore_of_arcReflectionData` — reduces `ReflectionCore` to `ArcReflectionData`: the
  existence, at some frontier arc point of the piece, of the reflected extension `f`. All reflection
  analysis is proven here.

Both axiom-clean (`propext, Classical.choice, Quot.sound`); Bottcher umbrella builds green (4246 jobs).

### The genuine residual, stated precisely
`ArcReflectionData` is NOT vacuous — it is the classical reflected continuation of `β` across a
smooth Julia arc. Its ONLY real content is: `β = bottcherCoord c₁` admits a continuous boundary
extension at the piece `S`, holomorphic off the arc (so that `f` exists). This is Carathéodory
boundary regularity of the exterior Böttcher map at `S`. Where the frontier piece is a genuine smooth
arc (the smooth-piece hypothesis itself), `K₁` is locally connected AT `S`, so the boundary extension
exists locally — "smooth piece ⟹ locally connected there ⟹ β extends there ⟹ reflect." Formalizing
THAT local-connectivity-from-smoothness step is the next load-bearing brick (deep, not open: needs
no global MLC, only local regularity forced by the smooth-arc hypothesis).

`SmoothPieceRigidity` never mentions `β`: the modulus-1 branch `wfam k` and the exterior branch `β`
are DIFFERENT branches (`‖wfam k‖=1` on the frontier vs `‖β‖=exp(green)>1` on the basin), which is
exactly why the discharge needs true reflection, not branch-following — killing the earlier
"direct branch-identification" idea for the interior-nonempty case.
