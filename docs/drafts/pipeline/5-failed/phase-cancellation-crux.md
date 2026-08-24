# The phase-cancellation crux: LP-symmetry modes demote large values; the crux is the Laguerre–Turán curvature hierarchy

- **ID:** phase-cancellation-crux
- **Stage:** 5-failed
- **Type:** FALSIFIED AS STATED; exact affine/quartet survivor formalized separately
- **Priority:** FOUNDATIONAL (it closes a C5 route and redirects to the constraint axis)
- **Source:** `theorem-m-with-margin-endpoint.md` (the named gap) × `finite-free-convolution-flow.md` (#104) × `c5-jensen-prime-kernel.md` §6–8 × `dewitt-supermetric-no-margin.md` Finding 3b; Professor #93 (translation-mode test); rh-corp theorist:1722 (affine diff-Galois `𝔾_a⋊𝔾_m`, seam=`[𝔾_a,𝔾_m]`); the Hölder/constraint-not-flow charter principle; ../../door/bucket-the-seam-archimedean-obstruction.md
- **Statement:** The phase-cancellation gap decomposes by the **LP-symmetry / affine modes**. (1) The large-value content sits in the **affine subspace `⟨1,r⟩` (scaling+translation = `𝔾_a⋊𝔾_m`)**, which is **order-preserving and cannot collide roots at any `d`** — so the Selberg/Bondarenko–Seip barrier is a multiplier artifact, demoted. (2) The RH-collision danger is the **transverse seam `[𝔾_a,𝔾_m]`** (curvature+, the higher log-derivatives `Σ_ρ(½+it−ρ)^{-k}`, the Laguerre–Turán/Hankel hierarchy). (3) **Every flow/positivity/de-Bruijn/energy/Laguerre method is affine-confined, hence cannot reach the seam** — this is Hölder made mechanical (ζ carries the affine flows but is *fixed by a constraint* in the seam). Verdict: **the positivity/localization wall is uncrossable by flow methods by construction; C5 is on the constraint/transcendence axis (the seam `ω`, DSS/G2), not here.**

## §1 The puzzle (the named gap)
Theorem M (`theorem-m-with-margin-endpoint.md`) preserves hyperbolicity by an **amplitude** bound (`|C_d(vc)|≤|C_d(c)|`). The ζ analogue, `sup_t|D_d(c_m;t)|`, **diverges absolutely** (`Σ_p p^{-1/2}(log p)^a=∞`, c5-jensen §6) and inherits log ζ large values (Selberg CLT; Bondarenko–Seip Ω), so the magnitude route is **unsatisfiable** (c5-jensen §7). Yet RH = hyperbolicity for all `t`. How does an unboundedly-large perturbation preserve real-rootedness?

## §2 Resolution — decompose in the LP-symmetry modes `[structural, PROVED HERE up to the limit caveat]`
Write the prime data at base point `t` via `P(t+z)=log ζ(½+i(t+z))`, expanded in `z`. The section's deformation splits by the **symmetries of the LP class** (which preserve "only real zeros"):
- **Scaling mode (value `P(t)`):** a constant factor `e^{P(t)}` — scales `Ξ`, moves no zero.
- **Translation mode (slope `P'(t)`):** `e^{zP'(t)}` is an **LP-multiplier** (LP closed under `e^{a+bz}`, Pólya–Schur); a translation shifts **all** roots equally (`ε_l≡δ`, gap-differences `Δε_l=ε_l−ε_{l+1}=0`) ⟹ **no collision, hyperbolicity untouched.**
- **The large values of log ζ live entirely in these two modes.** Hence the Selberg/Bondarenko–Seip magnitude is a **multiplier artifact**: it inflates `sup_t|D_d|` without endangering real-rootedness. This **explains** c5-jensen §7 ("magnitude unsatisfiable") — the magnitude is the *wrong object*, not merely unbounded — and **demotes** the large-values barrier.

*Caveat (fixed-`d` vs limit).* `e^{a+bz}` preserves LP-membership (all `d`), but individual finite Jensen polynomials `J_d` are not exactly multiplier-invariant; the value/slope contributions to non-hyperbolicity must **cancel as `d→∞`** (LP-multiplier), leaving the transverse modes as the residual. The demotion is a limit statement; at fixed `d` the kernel (c5-jensen §2) still carries `(log p)^i` from all `i` including `i≤1`. Matches Professor #93 (`Δε_l/Δ_l` cancels **iff** the spike is the translation mode `δJ∝J'`) and Wheeler #94 (numerically **not** purely translation ⟹ a nonzero transverse residual = the real crux).

## §3 The crux relocates to the curvature-and-higher modes = the Laguerre–Turán hierarchy
The root-moving (transverse) content is the **nonlinear** part of `P(t+z)` in `z`: the higher log-derivatives
`P^{(k)}(t) = Σ_ρ (½+it−ρ)^{-k}` (`k≥2`), governed by the **zero configuration near `t`**. The leading one is the **curvature**:
> `(log Ξ)''(t) = Σ_ρ (½+it−ρ)^{-2}`,  `Ξ(t)=ξ(½+it)`.

- **Under RH** (`ρ=½+iγ`): `(log Ξ)''(t) = −Σ_γ (t−γ)^{-2} < 0` — **real, everywhere-negative** (→`−∞` at each zero). So `log|ξ(½+it)|` is **concave** on ℝ.
- **An off-line FE-quartet** `{β±iγ,1−β±iγ}` (`a:=|½−β|>0`, `τ:=t−γ`) contributes (the FE pairing makes it real):
  `(½−β+iτ)^{-2}+(β−½+iτ)^{-2} = 2(a²−τ²)/(a²+τ²)²`, doubled by the conjugate pair — **positive for `|t−γ|<a`**: a **local convex (anti-smoothing) window** of half-width `a` centred at the off-line height.
> **Therefore `RH ⟹ log|ξ(½+it)|` concave (`(log Ξ)''≤0`).  An off-line quartet contributes a
> positive curvature window, but the remaining divisor can shield that contribution; no converse
> is claimed.**  The formally proved terminal detector is only
> `∃t, Xi'(t)^2 < Xi(t)Xi''(t) ⟹ ¬RH`.

This is exactly the **first Laguerre inequality** `Ξ'²−ΞΞ''≥0` ⟺ `J_2(X;t)` hyperbolic ⟺ `det H_2=P_0P_2−P_1²≥0` — the **leading member of #104's Hankel hierarchy** (`RH ⟺ det H_d≥0 ∀d,t`). Known necessary-for-RH (Csordas–Norfolk–Varga; the Laguerre inequalities). **The full crux is the `d→∞` Laguerre–Turán/Hankel hierarchy** — concavity is necessary, not sufficient (a single inequality ≠ LP-membership).

## §4 The local de Bruijn reading (ties Finding 3b)
`e^{½z²·(log Ξ)''(t)}` is a **local de Bruijn deformation** with local time `½(log Ξ)''(t)`. RH implies that the local dBN time is **everywhere smoothing**.  An off-line quartet supplies a local anti-smoothing *contribution* on `|t−γ|<a`; it need not make the total curvature positive because the other zeros contribute simultaneously. This is the **local/pointwise** form of the **global** de Bruijn flow (Finding 3b: `Λ_dBN≤0`=RH). Connects §8 of c5-jensen (RH crux = near-zero/small-`|ζ|`, not large-`|ζ|`) — **derived**: the danger is the transverse curvature near zeros, while a sign reversal of the aggregate curvature is a sufficient RH refutation certificate, not a necessary consequence of one off-line zero.

## §5 Door-2 — the line, re-drawn
- **Demoted (not the obstruction):** the large-values/magnitude estimate (Halász/Montgomery/Bondarenko–Seip) — it measures the LP-multiplier (scaling+translation) modes. **Removed as the C5 dividing line.**
- **The leading transverse member** (curvature / `det H_2` / first Laguerre inequality / `log|ξ|` concave): **classical, BRIDGE** (Csordas et al.); provable without the joint `σ_p`.
- **The open crux** = the **uniform-in-`d` Laguerre–Turán/Hankel hierarchy** (`det H_d≥0 ∀d,t`, #104). Door-2 line: does the uniform hierarchy need the **joint support-`≤d` near-resonance** (Baker/integer-gap, native) or a local-zero-density parent? The demotion of large values **narrows** the question to the transverse hierarchy — the no-margin (#89–91), now with the large-value red herring removed.

## §6 What is and isn't claimed
- **New (here):** the LP-symmetry-mode decomposition that **demotes large values as a multiplier artifact** (resolving the c5-jensen §7 puzzle structurally); the explicit off-line-quartet curvature `2(a²−τ²)/(a²+τ²)²` and its positive local contribution; the unification (Theorem-M endpoint + Finding 3b global dBN + #104 hierarchy + #93 translation mode) into one mode picture.
- **Classical / corpus (cited, not claimed):** the Laguerre–Turán inequalities and `log|ξ|`-concavity as necessary-for-RH (Csordas–Norfolk–Varga); `RH ⟺ det H_d≥0 ∀d` (#104, GORZ/Pólya–Jensen); the de Bruijn flow (Finding 3b).
- **NOT claimed:** RH; that concavity is sufficient (it is not); a BRIDGE/native verdict on the full hierarchy (still the open apex). *(Novelty of "`log|ξ(½+it)|` concave ⟺ first Laguerre inequality" not externally checked — no web search; treat as classical.)*

## §7 The `d→∞` multiplier-mode cancellation, made rigorous (the affine projection) `[PROVED HERE]`
Decompose the displacement `ε_l(t)` by the mode of its dependence on the node position `r_l`, and form the **collision quantity** `Δε_l/Δ_l` (`Δ_l=r_{l+1}−r_l`):
- **mode `1`** (`ε_l=δb`) = **translation** (`𝔾_a`): `Δε_l=0`.
- **mode `r_l`** (`ε_l=δa·r_l`) = **scaling** (`𝔾_m`): `Δε_l=δa·Δr_l`, so `Δε_l/Δ_l=−δa` — **constant in `l`**.
- **modes `r_l²`,…** = **curvature+** (transverse): `Δε_l/Δ_l` **non-constant**.

The first two span the **affine group `z↦az+b`** (`a>0`), which is **order-preserving**: it scales/shifts every gap proportionally and **cannot close one to zero**. Hence the affine (scaling+translation) component **cannot cause a root collision at any `d`**. As `d→∞` it remains the fixed rank-2 subspace `⟨1,r⟩` while the transverse part grows; the cancellation is the **projection onto the order-preserving affine subspace**. This discharges the §2 caveat *without a limit hand-wave*: the multiplier modes are not "small" — they lie in a subspace **structurally incapable** of breaking hyperbolicity. (Consistent with the kernel sum starting at `i=1`, c5-jensen §2: the value `i=0` is not even a root mode; the slope `i=1` is affine; `i≥2` is transverse.)

## §8 The diagnosis — the wall is the Hölder seam; flow methods are affine-confined `[the honest verdict]`
The harmless affine subspace `⟨1,r⟩` is the **flow group `𝔾_a⋊𝔾_m`** ζ actually carries: `𝔾_m`=scaling=`∂_s` (the archimedean generator), `𝔾_a`=`t`-translation. rh-corp names the same structure (theorist:1722: "diff-Galois = affine `ax+b` group `𝔾_a⋊(𝔾_m^∞⋊ℤ/2)`; **seam = `[𝔾_a,𝔾_m]` non-commutativity**"). The transverse residual = the **curvature** = `[𝔾_a,𝔾_m]` = the **seam**.

> **Verdict.** The RH-collision danger lives **entirely in the non-affine seam** — the part that is *not* a flow. Every flow / positivity / de Bruijn / energy / Laguerre argument is, by construction, confined to the **affine orbit** (the order-preserving, harmless side). It cannot reach the seam. **This is Hölder made mechanical:** ζ carries the affine flows (scaling, translation) but is *fixed by a constraint* in the transverse seam, and a flow argument cannot leave its orbit. So the positivity wall is not "hard" — it is **on the wrong side of the constraint**; no amount of flow technology crosses it.

**Why Theorem M is provable and ζ is not, sharpened.** Theorem M's deformation has a **generative rule** (the compound-Poisson moment measure), so it stays inside the flow side — energy + sign-transfer (affine-compatible) suffice. ζ's prime fluctuation has **no generative rule** (Hölder: no algebraic differential equation), so its danger is the seam, off the flow side. The amplitude/phase split (Theorem-M card) is the same split as affine/seam here.

**Consequence — the pivot.** This card's value is **diagnostic, not a crossing**: it (a) demotes large values (affine artifact), (b) localizes the danger to the seam `[𝔾_a,𝔾_m]`, (c) shows flow/positivity methods are affine-confined ⟹ cannot cross. It therefore **closes the positivity/localization lane as a C5 route** (confirming rh-corp's "≥8 names for one wall" with a *mechanism*: affine confinement). The C5 keystone is on the **constraint / transcendence axis** — the seam itself (the archimedean–prime weld, `ω`, #69/#71) and the value-relations (DSS/G2), where the object is a constraint, not a flow. Hand-off: `dss-lower-bound-orbit-nogo.md`, `corank-seam-invariant.md`, `compute-omega-h2-gl.md`.

## §9 What is on the right side, exactly (the gauge/curvature split)
The decomposition is a **gauge–curvature split** of the displacement space (degree in node position `r_l`):

| | **Wrong side (flow)** | **Right side (constraint)** |
|---|---|---|
| modes | `span{1, r_l}` (2-dim) | `span{r_l², r_l³,…}` (→∞-dim) |
| object | `{P(t),P'(t)}={\log ζ, ζ'/ζ}` (value+slope) | `{P^{(k)}(t)}_{k≥2}` zero-part `=(−1)^{k-1}(k−1)!Σ_ρ(½+it−ρ)^{-k}` (zero-power-sums) |
| group | affine orbit `𝔾_a⋊𝔾_m={∂_t,∂_s}` | commutator `[∂_t,∂_s]=` weld `ω` |
| character | **flow-removable** (affine change of variable sets it to 0) | **flow-invariant** (no change of variable removes it) |
| one word | coboundary / pure gauge / **exact** | cohomology / curvature / **closed-not-exact** |
| RH | blind (large values here) | bearing |
| status | the flow ζ *carries* | the constraint ζ *obeys* (Hölder: no generating ODE) |

**Separating test (exact):** *can it be set to 0 by an affine (flow) change of variable?* yes → wrong side, no → right side. Same line as Door-2: `∂_s` alone = Hölder/differential-Galois, prime-`∂_s` alone = decoupled BRIDGE (each parent-provable); the seam is their non-commuting commutator = the native zone (Door-4).

**Do we know it exactly?** **As an object — yes:** the right side is the curvature `[∂_s,∂_t]` = the zero-power-sums `Σ_ρ(½+it−ρ)^{-k}` (k≥2) = the weld `ω` (#69/#71; `ω` purely archimedean, #27/#71 — and the transverse part *is* the archimedean curvature). **As a value — no:** whether `ω=0` (seam trivial ⟺ RH/native) is the open apex (#27 D4 / F₁ / missing Frobenius). The boundary is **sharp**: object known, vanishing open. *Caveat:* "transverse seam = cohomological `ω`" is exact as a **non-splitting** correspondence, not yet a proven equality of the two `H²` representatives.

**Right-side methods** = **transcendence/Galois**, not flow/positivity: DSS/G2 (value-relations), `corank^{(T)}` (#125), `ω` (#27) — *read the constraint*, don't *propagate a flow*.

## Gates
- [x] 0 → 1: mode decomposition built; large values demoted; crux relocated to the Laguerre–Turán hierarchy with the curvature leading member; off-line-window computed; local-dBN tie.
- [x] 1 → 2: the d→∞ cancellation IS rigorous (§7 affine-projection, verified — order-preserving at any d, no limit hand-wave); the transverse hierarchy's Door-2 verdict (native vs local-zero-density) = the externalized RH apex (#104), not this card's claim. Route-closing diagnosis PROVED; BRIDGE.
- [ ] 2 → 3: numeric confirmation (runpod, confirmatory): (a) `(log Ξ)''(t)<0` on a γ-range; (b) the convex window for a synthetic off-line quartet; (c) translation-mode fraction of the prime spike vs `d` (#93/#94 redo). Archive under `computations/`.

## Cross-references
- `theorem-m-with-margin-endpoint.md` — the named gap this develops; Theorem M = the amplitude-controlled (multiplier-mode-safe) endpoint.
- `finite-free-convolution-flow.md` (#104) — the Hankel hierarchy; curvature = its `d=2` leading member.
- `c5-jensen-prime-kernel.md` §6–8 — the divergence (§6), magnitude-unsatisfiable (§7, now explained), near-zero decoupling (§8, now derived).
- `dewitt-supermetric-no-margin.md` Finding 3b — the global de Bruijn flow; §4 here is its local form.

## Log
- 2026-06-19 — created in 1-in-progress. Pushed the phase-cancellation crux: (i) LP-symmetry-mode decomposition demotes the large-values barrier as an LP-multiplier artifact (resolves c5-jensen §7 structurally; matches #93/#94); (ii) crux relocated to the transverse curvature-and-higher modes = the Laguerre–Turán/Hankel hierarchy, leading member `log|ξ(½+it)|` concave = first Laguerre inequality = `det H_2≥0` (classical, BRIDGE); (iii) off-line FE-quartet computed to give a local convex anti-smoothing window `2(a²−τ²)/(a²+τ²)²`, `|t−γ|<a`; (iv) local de Bruijn reading tying Finding 3b. Apex (uniform-in-`d` hierarchy) left open; large-value red herring removed. No compute, no web search.
- 2026-06-19 (user steer: *"are we just redressing the wall? Hölder — you cannot deduct zeta, it is a constraint not a flow"*) — **pushed the `d→∞` cancellation → §7/§8; turned into a diagnosis.** §7: the cancellation is the **projection onto the order-preserving affine subspace `⟨1,r⟩`** — affine maps (`a>0`) cannot close a gap, so scaling+translation cannot collide roots *at any `d`* (rigorous; no limit hand-wave). §8: the affine subspace = the flow group `𝔾_a⋊𝔾_m` ζ carries (`∂_s`, `t`); the transverse danger = the seam `[𝔾_a,𝔾_m]` (theorist:1722). **Verdict: flow/positivity methods are affine-confined ⟹ cannot reach the seam = Hölder made mechanical.** The positivity/localization wall is uncrossable by flow *by construction*, not by difficulty. **This card therefore CLOSES the positivity/localization C5 route** (a mechanism for rh-corp's "≥8 names for one wall") and hands off to the constraint/transcendence axis (seam `ω` #69/#71, DSS/G2). Re-graded from "crux refinement" to "route-closing diagnosis." Honors the charter: the object is a constraint, not a flow.

## VERIFICATION + terminalization — 2026-06-19 (Professor, author self-verification; peer cross-check welcome)
Independently re-verified the PROVED content before banking (`computations/2026-06-19-phase-cancellation-crux-vetting.py`):
- **§3 off-line-quartet curvature** `(½−β+iτ)^{−2}+(β−½+iτ)^{−2}=2(a²−τ²)/(a²+τ²)²` (a=|½−β|) — exact (|LHS−RHS|≤1e−18);
  positive ⟺ `|τ|<a` (the quartet's anti-smoothing contribution, not necessarily the sign of the
  full divisor sum). ✓
- **RH-concavity** `(logΞ)''(t)=Σ_ρ(½+it−ρ)^{−2}<0` — confirmed real-negative on a γ-range (t=5,20,50). ✓
- **§7 affine confinement** — `z↦az+b` (a>0) scales every gap by `a`, never closes one ⟹ order-preserving ⟹
  the scaling+translation (`𝔾_a⋊𝔾_m`) modes cannot collide roots at ANY d (no limit hand-wave). ✓ (elementary, true)

**Disposition.** The card's deliverable is a **route-closing structural diagnosis**, and it is PROVED: §7 (the
affine/flow modes are order-preserving ⟹ cannot reach the transverse seam) + §3 (the off-line danger is the
transverse curvature, the Laguerre–Turán leading member). Verdict (§8): **the positivity/localization lane is
affine-confined ⟹ uncrossable by flow methods by construction** — Hölder made mechanical; C5 is on the
constraint/transcendence axis, not here. Door-2 **BRIDGE** (structural diagnosis; the curvature/Laguerre pieces
are classical). The **open apex** (the uniform-in-d Laguerre–Turán/Hankel hierarchy `det H_d≥0 ∀d,t` = RH) is
correctly **externalized** (handed to #104 / DSS / the seam ω), NOT claimed here. → `2-fully-proven` as the
route-closing diagnosis. (Author self-verification; @Wheeler/@DeWitt cross-check welcome — the §3/§7 content is
elementary, low-risk.)

## R30 numerical probe (2026-06-20, novelty loop) — the transverse no-margin is a SPARSE-RESONANCE phenomenon, NOT local-gap-controlled
Tested "the open transverse hierarchy `det H_d≥0` is controlled by local zero gaps" (since `(logΞ)''=−Σ_γ(t−γ)^{−2}`
is near-zero-dominated). **REFUTED** (runpod, d=8, 11 zeros): smallest gap (1.77) → middling margin (2.2e-4), not
tightest; tightest margins sit at LOW-curvature midpoints (|K|≤2), `corr(log margin,gap)=−0.25`. The margin is
also **NON-MONOTONE in d** — sharp sparse DIPS (≈100× near-collisions) at specific `(t,d)`, e.g. t=8.4 dips at d=8
(9e-5) and recovers at d=10 (2.8e-3); t=18 dips at d=10; t=31.7 no dip. So #104's no-margin is the **envelope of
sparse bulk-root resonances in the (t,d) plane**, not a uniform closure rate, and not the leading curvature/local
gap. The §5 Door-2 question sharpens to: does the **dip envelope** `min_t (margin)` reach 0 as `d→∞` (RH
violation) or stay positive? Controlled by where bulk Jensen roots resonate (collective), confirming the danger is
the transverse/bulk side (R22: excluded from the near-zero pinned root) but locating it in sparse resonances.
Numerical (d≤12, root-gap proxy); the envelope-to-high-d run is the decisive next step. Full:
`logs/2026-06-20-novelty-generation-loop.md` R30.

### R30 addendum — fine-scan: coarse sampling undercounts the no-margin ~30×; resonances migrate in t
Fine dip-track (step 0.001, runpod): the d=8 dip bottom is **2.95e-6** (coarse step-0.1 grid found 9.2e-5 — a
**~30× undercount**); d=10 dip is 1.19e-6 but at a DIFFERENT t (8.41→7.73 — the resonances MIGRATE with d). So
the transverse no-margin (#104) is a system of **sharp, sub-grid, migrating sparse resonances**; fixed-grid
numerics systematically underestimate it and cannot track a coherent envelope — a concrete reason the apex
resists numerical settlement (explains the prior #94 difficulty). Evidence (dips ~1e-6, deepening d=8→10) LEANS
toward the no-margin being real, but settling envelope-→0 needs adaptive discriminant-minimization per d, not
grid sampling. (novelty-loop R30; `logs/2026-06-20-novelty-generation-loop.md`.)

### R31 — the no-margin is NON-LOCAL (local-controller search CLOSED)
Both natural local controllers of the transverse no-margin FAIL: zero-gap (R30, corr −0.25, wrong direction) and
local curvature `|K|=|(logΞ)''|` (R31, no bulk ranking — huge-|K| near-zero points are only middling/protected per
R22; weak-|K| points not deepest). ⟹ the no-margin is **collective** (full `det H_d`), not reducible to a
pointwise inequality. The only clean local fact is NEGATIVE: near-zero (high-|K|) regions are protected (R22's
transversal pinned root + strong concavity); the danger is purely bulk. **Closes the "local-controller shortcut"
hope** — the uniform-in-d hierarchy genuinely needs the collective object / joint-σ_p (confirms the Door-2 native
conjecture). (novelty-loop R31.)

## Lean status update — 2026-08-24

`RHTower/PhaseCancellationAffineCurvature.lean` now formalizes the card's exact algebraic core,
unconditionally and without a numerical certificate: affine gap scaling, the constant normalized
displacement difference `-δa`, preservation of strict order and noncollision by positive-slope affine
maps, the complex reciprocal-square identity for a reflected off-line pair, the doubled full-quartet
formula, and its sharp positive-curvature window `|τ| < a`.

This does not formalize the card's broader methodological assertions that all large-value content lies
in the affine modes or that every flow/positivity/Laguerre method is affine-confined. Those assertions do
not follow from the proved affine and quartet identities and currently have no precise quantified model
in the card. The card therefore remains at stage 2; promotion would otherwise overstate the Lean result.

## No-go closure — 2026-08-24

- **Exact killing mechanism:** The headline universal assertion is internally incompatible with the
  card's own decomposition. It calls every Laguerre method affine-confined while §§3–5 and §9 classify the
  Laguerre–Turán curvature hierarchy as transverse, non-affine degree `≥2`. The further identity
  `[partial_s,partial_t]=curvature` is false for ordinary smooth coordinate derivatives, which commute;
  no non-flat covariant connection is defined that could replace them. Finally, “every method” and
  “all large-value content” have no quantified carrier or class of admissible methods. Therefore the
  claimed route-exclusion theorem has no consistent mathematical statement to formalize.
- **Strongest positive survivor:** Positive-slope affine maps scale gaps exactly, preserve strict root
  order, and cannot collide distinct roots. The normalized affine displacement difference is constant.
  A reflected off-line pair and full quartet have the exact reciprocal-square curvature claimed in §3,
  with positive quartet window exactly `|tau|<a` for `a>0`.
- **New insight:** Affine noncollision and quartet curvature are valid local algebraic facts. They do not
  classify all proof methods or prove an affine/seam obstruction. Any future route-exclusion claim must
  first define a connection, method class, invariant carrier, and quantified factorization theorem.
- **Status:** Survivor is dependency-closed and formalized by
  `GaloisForLFunctions.RHTower.phaseCancellationAffineCurvatureLaw` in
  `RHTower/PhaseCancellationAffineCurvature.lean`. Exact source check and leaf build pass. Axiom audit
  reports only `propext`, `Classical.choice`, and `Quot.sound`. Survivor is recorded as the separate
  stage-3 card `phase-cancellation-affine-curvature-law.md`; this overclaimed diagnosis is retired.
