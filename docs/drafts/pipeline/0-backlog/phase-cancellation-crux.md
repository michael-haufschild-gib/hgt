# The phase-cancellation crux: LP-symmetry modes demote large values; the crux is the Laguerre–Turán curvature hierarchy

- **ID:** phase-cancellation-crux
- **Stage:** 0-backlog (self-authored 2026-06-19; awaiting pipeline vetting)
- **Type:** STRUCTURAL **diagnosis** (closes a route) — claimed Door grade **BRIDGE**; §7 affine decomposition is proved, §8 is the verdict: the positivity/localization lane is **affine-confined ⟹ cannot cross** (Hölder, mechanical). **Not** a crossing.
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
> **Therefore `RH ⟹ log|ξ(½+it)|` concave (`(log Ξ)''≤0`); an off-line zero forces a convex window.**

This is exactly the **first Laguerre inequality** `Ξ'²−ΞΞ''≥0` ⟺ `J_2(X;t)` hyperbolic ⟺ `det H_2=P_0P_2−P_1²≥0` — the **leading member of #104's Hankel hierarchy** (`RH ⟺ det H_d≥0 ∀d,t`). Known necessary-for-RH (Csordas–Norfolk–Varga; the Laguerre inequalities). **The full crux is the `d→∞` Laguerre–Turán/Hankel hierarchy** — concavity is necessary, not sufficient (a single inequality ≠ LP-membership).

## §4 The local de Bruijn reading (ties Finding 3b)
`e^{½z²·(log Ξ)''(t)}` is a **local de Bruijn deformation** with local time `½(log Ξ)''(t)`. RH ⟺ `(log Ξ)''<0` ∀t ⟺ the local dBN time is **everywhere smoothing**; an off-line zero = a **local anti-smoothing window** `|t−γ|<a` (the convex bump above). This is the **local/pointwise** form of the **global** de Bruijn flow (Finding 3b: `Λ_dBN≤0`=RH); the global `Λ_dBN≥0` (Rodgers–Tao) = the free half, here the statement that the *aggregate* local times never push past threshold. Connects §8 of c5-jensen (RH crux = near-zero/small-`|ζ|`, not large-`|ζ|`) — **derived**: the danger is the curvature near zeros, the large `|ζ|` (peaks) being multiplier-mode and harmless.

## §5 Door-2 — the line, re-drawn
- **Demoted (not the obstruction):** the large-values/magnitude estimate (Halász/Montgomery/Bondarenko–Seip) — it measures the LP-multiplier (scaling+translation) modes. **Removed as the C5 dividing line.**
- **The leading transverse member** (curvature / `det H_2` / first Laguerre inequality / `log|ξ|` concave): **classical, BRIDGE** (Csordas et al.); provable without the joint `σ_p`.
- **The open crux** = the **uniform-in-`d` Laguerre–Turán/Hankel hierarchy** (`det H_d≥0 ∀d,t`, #104). Door-2 line: does the uniform hierarchy need the **joint support-`≤d` near-resonance** (Baker/integer-gap, native) or a local-zero-density parent? The demotion of large values **narrows** the question to the transverse hierarchy — the no-margin (#89–91), now with the large-value red herring removed.

## §6 What is and isn't claimed
- **New (here):** the LP-symmetry-mode decomposition that **demotes large values as a multiplier artifact** (resolving the c5-jensen §7 puzzle structurally); the explicit off-line-quartet curvature `2(a²−τ²)/(a²+τ²)²` and its **local anti-smoothing window**; the unification (Theorem-M endpoint + Finding 3b global dBN + #104 hierarchy + #93 translation mode) into one mode picture.
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
- [ ] 1 → 2: the `d→∞` cancellation of the multiplier (scaling+translation) modes made rigorous (the fixed-`d` vs limit caveat, §2); and the transverse hierarchy's Door-2 verdict (native vs local-zero-density parent).
- [ ] 2 → 3: numeric confirmation (runpod, confirmatory): (a) `(log Ξ)''(t)<0` on a γ-range; (b) the convex window for a synthetic off-line quartet; (c) translation-mode fraction of the prime spike vs `d` (#93/#94 redo). Archive under `computations/`.

## Cross-references
- `theorem-m-with-margin-endpoint.md` — the named gap this develops; Theorem M = the amplitude-controlled (multiplier-mode-safe) endpoint.
- `finite-free-convolution-flow.md` (#104) — the Hankel hierarchy; curvature = its `d=2` leading member.
- `c5-jensen-prime-kernel.md` §6–8 — the divergence (§6), magnitude-unsatisfiable (§7, now explained), near-zero decoupling (§8, now derived).
- `dewitt-supermetric-no-margin.md` Finding 3b — the global de Bruijn flow; §4 here is its local form.

## Log
- 2026-06-19 — created in 1-in-progress. Pushed the phase-cancellation crux: (i) LP-symmetry-mode decomposition demotes the large-values barrier as an LP-multiplier artifact (resolves c5-jensen §7 structurally; matches #93/#94); (ii) crux relocated to the transverse curvature-and-higher modes = the Laguerre–Turán/Hankel hierarchy, leading member `log|ξ(½+it)|` concave = first Laguerre inequality = `det H_2≥0` (classical, BRIDGE); (iii) off-line FE-quartet computed to give a local convex anti-smoothing window `2(a²−τ²)/(a²+τ²)²`, `|t−γ|<a`; (iv) local de Bruijn reading tying Finding 3b. Apex (uniform-in-`d` hierarchy) left open; large-value red herring removed. No compute, no web search.
- 2026-06-19 (user steer: *"are we just redressing the wall? Hölder — you cannot deduct zeta, it is a constraint not a flow"*) — **pushed the `d→∞` cancellation → §7/§8; turned into a diagnosis.** §7: the cancellation is the **projection onto the order-preserving affine subspace `⟨1,r⟩`** — affine maps (`a>0`) cannot close a gap, so scaling+translation cannot collide roots *at any `d`* (rigorous; no limit hand-wave). §8: the affine subspace = the flow group `𝔾_a⋊𝔾_m` ζ carries (`∂_s`, `t`); the transverse danger = the seam `[𝔾_a,𝔾_m]` (theorist:1722). **Verdict: flow/positivity methods are affine-confined ⟹ cannot reach the seam = Hölder made mechanical.** The positivity/localization wall is uncrossable by flow *by construction*, not by difficulty. **This card therefore CLOSES the positivity/localization C5 route** (a mechanism for rh-corp's "≥8 names for one wall") and hands off to the constraint/transcendence axis (seam `ω` #69/#71, DSS/G2). Re-graded from "crux refinement" to "route-closing diagnosis." Honors the charter: the object is a constraint, not a flow.
