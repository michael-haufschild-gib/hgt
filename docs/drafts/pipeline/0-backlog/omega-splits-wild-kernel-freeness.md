# ω splits: K-freeness (DSS) vs polarization (RH) — the wild-kernel moonshot

- **ID:** omega-splits-wild-kernel-freeness
- **Stage:** 0-backlog (self-authored 2026-06-19; awaiting pipeline vetting)
- **Type:** CONJECTURE (native) + **moonshot** — claimed Door grade **BRIDGE** for the split-diagnosis (resolves an orthogonality conflict) and the `H²(free)=0` mechanism; the freeness route is the moonshot
- **Priority:** FIELDS MEDAL
- **Source:** `compute-omega-h2-gl.md` §R–§W (the team's `ω` program) · `corank-seam-invariant.md` §C–§F (graded corank, #125) · `phase-cancellation-crux.md` §9 (the curvature seam) · memory `exponential-period-dss-cross` (wild kernel `K=ker(G^exp↠G_mot)`) · orthogonality meta-theorem (#137) / faces-orthogonality (#54); ../../door/bucket-the-seam-archimedean-obstruction.md
- **Statement:** The obstruction `ω∈H²(G_L)` **splits** into a motivic/transcendence part `ω_mot` and a polarization/localization part `ω_pol`. `ω_mot=0 ⟺ the wild kernel K is a free pro-unipotent group ⟺ DSS` (via `H²(free)=0`); `ω_pol=0 ⟺ Q_W⪰0 ⟺ RH`. Full `ω=0 ⟺ DSS ∧ RH`. The moonshot: **decide `ω_mot=0` by proving `K` free via the Ramis/Stokes structure of the Γ-factor's irregular connection — a Galois-structural route that bypasses direct Schanuel.**

## §1 The conflation, and why ω must split `[diagnosis — BRIDGE]`
The `compute-omega` card asserts two equivalences:
- `ω=0 ⟺ Tannakian/motive ⟺ RH` (§S/§T: the polarization `Q_W⪰0`);
- `ω=0 ⟺ ABP GROUP→VALUES lift ⟺ DSS closes` (§U/§V: the missing F₁).

If both held literally, `RH ⟺ DSS`. But **RH (localization) and DSS (transcendence) are orthogonal** — independent faces, neither implies the other (faces-orthogonality #54; orthogonality meta-theorem #137; the project's two-axes split). **Contradiction ⟹ `ω` is not one obstruction but two.** The resolution:
> **`ω = ω_mot ⊕ ω_pol`** (a 2-step class; an extension, not necessarily a direct sum):
> - **`ω_mot`** — the **motive-existence / Tannakian** obstruction (does a genuine motive carry the zeros?) = the **transcendence/DSS** axis. §U/§V's ABP-lift face.
> - **`ω_pol`** — the **polarization positivity** obstruction (`Q_W⪰0`) = the **localization/RH** axis. §T's face; its leading member is my curvature condition (`log|ξ| concave`, `phase-cancellation-crux` §3).
>
> `ω=0 ⟺ ω_mot=0 ∧ ω_pol=0 ⟺ DSS ∧ RH` — *a genuine motive **with** a positive polarization*. This **respects orthogonality**: the two halves are independent, and the apparent `RH⟺DSS` was a conflation of the two faces of `ω`. (Matches §T treating `Q_W` as a **separate datum** from the motive; this card names the consequence.)

## §2 The moonshot — `ω_mot=0 ⟺ K free`, decided by Stokes, not Schanuel
**Setup (the team's, exact).** The wild kernel `1→K→G^exp→G_mot→1` (Fresán–Jossen exponential motives; memory `exponential-period-dss-cross`). `K` is **pro-unipotent**, with `dim gr^n_W K = 1` generator per Laurent order `n`, period `γ_n` (the Stieltjes constants = exponential periods, §W). Hypertranscendence (#134) ⟹ no finite ABP Φ-matrix ⟹ **`K` is infinite-rank** (§V).

**The mechanism [RIGOROUS].** `ω_mot` is the Tannakian gerbe class of the exponential-motivic category, localized in the `K`-part (§R/§S: `ω` is purely archimedean = the wild/`K` place). For a pro-unipotent group, the gerbe/`H²` obstruction is computed from `Lie(K)`. **A free Lie algebra has cohomological dimension 1: `H^n(free)=0` for `n≥2`** (the Chevalley–Eilenberg complex of a free Lie algebra is exact above degree 1). Therefore
> **`Lie(K)` free ⟹ `H²(K)=0` ⟹ `ω_mot=0`.**

**§2-cohomology — the mechanism is an IFF, and it grades the wild kernel `[RIGOROUS, sharpens §2 + addresses gate 1→2(a)]`.**
`K` is pro-unipotent (the `J_m=∂_s^m` generators, one per Laurent order), so `Lie(K)` is a **graded
pro-nilpotent** Lie algebra. The standard generators/relations theorem (the Lie analog of "a group is free
⟺ `H_2=0`"; Chevalley–Eilenberg, valid for graded (pro)nilpotent `𝔤`):
> `H_1(Lie K)` = **generators**, `H_2(Lie K)` = **relations**, and **`Lie(K)` free ⟺ `H_2(Lie K)=0`.**

This upgrades the mechanism from `⟹` to an **iff** and grades the wild kernel exactly:
- **`H_1(Lie K)` = the exponential-corank** — one generator `γ_n` per Laurent order (my §7 / the
  FE-triangular dictionary: the `J_m=∂_s^m` exist, one per order, `dim gr^n=1`). This is the **structural,
  parent-computable** generator count (the floor `≥1`/order), independent of period transcendence.
- **`H_2(Lie K)` = `ω_mot`** — the **relations** among the `{γ_n}` (beyond the period shuffle).
- Therefore **`DSS-cross ⟺ K free ⟺ H_2(Lie K)=0`** (a rigorous iff): DSS is *exactly* "the wild kernel's
  Lie algebra has **no relations** / cohomological dimension 1." The exponential-corank (`H_1`, structural)
  and `ω_mot` (`H_2`, the hard DSS relations) are cleanly separated as the two graded cohomology pieces of
  one object `Lie(K)`. (Caveat unchanged from §5: this identifies `ω_mot` with `H_2(K)`; the LHS
  cross-term `H¹(G_mot,H¹(K))` is the residual flagged for 1→2 — but `H_2(K)=0 ⟺ free` is itself exact.)

**The conjecture [MOONSHOT].**
> **`ω_mot=0 ⟺ K is a free pro-unipotent group ⟺ {γ_n} (and the wild seam) carry no relations beyond the period shuffle ⟺ DSS-cross.**

**Why this is ahead of SOTA — the apex is FREENESS, not infinitude.** §V correctly says hypertranscendence forbids a *finite* lift (`K` infinite-rank). But infinitude is **free** (hypertranscendence gives it). The real apex is whether the infinite `K` is **free** (no exponential-period relations) — and that is a **Galois-structural** question, not a direct transcendence one. The team's exponential-corank "`dim gr^n K ≥ 1 ∀n`" (each `γ_n` exists) is **weaker** than freeness (no relations among products); freeness is the full DSS-cross, and it is what kills `H²`.

**The decision procedure [the moonshot toolkit].** `K` is the wild kernel of the relevant archimedean irregular connection. By Ramis's wild fundamental group, the wild monodromy is generated by the **formal monodromy + Stokes operators + exponential torus**, and for many irregular connections the **Stokes group is free pro-unipotent** (the Stokes data are unconstrained generators). **Conjecture: the archimedean wild connection's Stokes structure makes `K` free** — provable, if so, by computing the Stokes matrices, **without** proving a single `γ_n` transcendental. This converts DSS from an analytic Schanuel problem into a **structural Stokes-freeness** problem.

**§2a Self-correction — which connection (the Γ-factor's Stokes is Tate, not wild) `[computed here]`.** The naive target — the **Γ-factor's** Stirling resurgence — is the **wrong** connection: its Borel transform (Binet) `(½−1/t+1/(e^t−1))/t` has simple poles only at the lattice `t=2πik`, residues `∼1/(2πik)`, so its Stokes constants are **powers of `2πi` = mixed-Tate (motivic)**, *not* exponential periods. (Consistent: `a_∞=½log2π=−ζ'(0)` is a Tate/motivic constant — §S's "local coboundary", not the obstruction.) **The genuinely wild periods `{γ_n}` live in a DIFFERENT connection** — the `γ_E`/digamma one (`γ_E=−∫_0^∞ e^{-x}\log x\,dx` = the `𝔾_a`-period of `ψ=∂_s\logΓ`, §W; an `e^{-x}·\log x` irregular×regular mix). So **retarget: `K` free ⟺ the `γ_E`/digamma exponential connection's wild kernel is free**, decided by *its* Stokes structure, not Γ's Stirling. The Γ-factor contributes only the Tate floor; the digamma/`γ_n` connection carries the actual `ω_mot` content. *(Frontier-science note: conjectured Γ-Stokes as the decider, computed it = Tate, corrected to the digamma connection — the genuine target is sharper for it.)*

## §2b Moonshot 2 — the missing F₁ IS the Stokes automorphism (resolves §V's residual)
§V proved the F₁ ABP-lift cannot be finite/algebraic (hypertranscendence #134 ⟹ no Φ-matrix) and concluded "the lift must be infinite-rank / ζ-regularized (Deninger)" — but left it **unidentified**. The wild/irregular setting names it:
> **Conjecture: the missing archimedean F₁ Frobenius (the GROUP→VALUES lift) IS the Stokes automorphism of the completed `Λ`'s archimedean irregular connection.**

Rationale (the constraint-not-flow fit is exact):
- In wild Hodge theory (Sabbah; Mochizuki–Stokes structures), the analog of Frobenius for an **irregular** connection is **not** a tame Galois element but the **Stokes automorphism** + exponential torus — the wild monodromy. It is the *transcendental* part of the monodromy that the **formal (algebraic) difference equation misses** — precisely the non-algebraic, infinite, regularized object §V says is required.
- It is **determined by the constraint, not propagated by a flow:** the Stokes data are fixed by the irregular connection (the Γ-factor / the FE-completed `Λ`), read off the resurgence of the asymptotic series — they are a property of the *fixed object*, not generated by an ODE. This is "the object is fixed by a constraint, not a flow" realized: the F₁ Frobenius is the **wild monodromy of the constraint**.
- It supplies a **GROUP→VALUES lift** because the Stokes automorphism acts on the *actual* (Borel-resummed) solutions, lifting formal/value relations to genuine ones — the wild analog of ABP's Frobenius lift, now non-algebraic.

So: **`ω_mot=0 ⟺ the Stokes automorphism acts transitively / freely on the exponential periods ⟺ K free ⟺ DSS.`** This identifies the F₁ (open since §U) with a concrete, computable object (the Γ-factor's Stokes matrices, explicit via Stirling resurgence), and explains *why* it is infinite/regularized: Stokes automorphisms are exponential (`exp` of alien derivatives), never finite-rank. **Ahead of §V:** not "a lift must exist" but "it is *the Stokes automorphism*," with a computation attached.

## §2c Honest caveat — difficulty is conserved; the tractable sub-target is `K_formal` free
**`K` free ⟹ DSS ⟹ `γ_E` irrational** (the first rung). Since `γ_E∉ℚ` is *open*, **`K` free is at least as hard as DSS — it relocates the difficulty, it does not bypass it** (consistent with the conserved-difficulty law, #103/#125). The value is the *toolkit* (Stokes/wild-Hodge, `H²(free)=0`), not a shortcut. The honest split:
- **`K_formal`** — the abstract wild monodromy / Stokes group, determined by the **irregular type** (slopes, exponential factors) of the digamma connection (Ramis). Its freeness is a **structural** fact, plausibly provable from the type — **independent of any period transcendence**. This is the *tractable* sub-target.
- **Fullness `K_mot = K_formal`** — the period realization is the whole group ⟺ the periods are maximally independent ⟺ **DSS** (the hard, period-transcendence part; `γ_E` irrationality is its rung 0).
- `ω_mot=0 ⟺ K_formal free **and** K_mot=K_formal`. So the moonshot's **decidable** half is "`K_formal` free" (Stokes/Ramis, structural); the **hard** half is fullness (= DSS). Proving `K_formal` free is a genuine, parent-independent sub-goal — *necessary* for `ω_mot=0` — even though sufficiency needs the conserved-hard fullness. **This is where to actually push: the structural freeness of the digamma connection's Stokes group, not the period values.**

## §2d The sub-target, pushed concretely — the local Stokes is Tate; the content is a global regulator `[worked here; partly corrects §2c]`
The correct connection for `γ_E` is the **exponential integral `E_1`** (`γ_E` is its connection constant): `E_1(z)=−γ_E−\log z−Σ_{k≥1}(−z)^k/(k·k!)` near `0`, `E_1(z)∼e^{-z}/z·Σ(−1)^n n!/z^n` at `∞`.
- **Irregular type:** at `∞`, slope `1`, two competing exponential factors `{0,−z}` ⟹ one Stokes line; the **Stokes multiplier is `2πi`** (the classical Stokes constant of `Σ(−1)^n n!/z^{n+1}`) — **Tate**, exactly like the Γ-factor (§2a).
- **`γ_E` is NOT local Stokes data** — it is the **global connection coefficient** between `0` and `∞` = a **period of the extension `E^{-x}⊗\mathrm{Kum}`** (a regulator / `Ext¹` class).

**Consequence (honest, corrects §2c).** For these slope-1 single-level connections, **`K_formal` (local Stokes) is Tate-determined**, *not* the carrier of the transcendence; the content is the **global regulator**. So "local structural freeness bypasses the period-hard part" **fails at rung 0** — the same Tate-collapse as the Γ-factor, now at `γ_E`. Difficulty conservation reaches even the structural half.

**The object, now pinned exactly.** `ω_mot` lives in the **exponential-motivic `Ext`-tower** `Ext¹_{M^{exp}}(ℚ, E^{-x}⊗ℚ(n))` with regulator `γ_n` (= the exponential corank, memory `exponential-period-dss-cross`; = the `𝔾_a`-period of digamma, §W). It splits cleanly:
- **dim `Ext¹` per order** — *structural*, computable from **irregular Hodge numbers** (the de Rham / rapid-decay dimension), independent of period values. This is the genuinely **parent-computable** sub-target (the generator *count* = the exponential-corank floor `≥1`).
- **regulator injectivity** — the `γ_n` nonzero & independent = **DSS** (the conserved-hard part; `γ_E∉ℚ` is rung 0).

**So the surviving tractable sub-target is: compute `dim Ext¹_{M^{exp}}(ℚ,E^{-x}⊗ℚ(n))` via irregular Hodge theory** (one regulator per order ⟹ the exponential-corank floor), reducing DSS to *regulator injectivity*. The Stokes-freeness route is corrected to a **regulator/`Ext`** route; `ω_mot=0 ⟺` the regulator tower is full (injective) ⟺ DSS — with the *dimension* count structural and the *injectivity* the apex.

## §3 The other half — `ω_pol` = RH = my curvature seam (slots in)
`ω_pol = 0 ⟺ Q_W⪰0 ⟺ RH` (§T). Its leading member is the **curvature condition** (`phase-cancellation-crux` §3): `log|ξ(½+it)|` concave = `Σ_ρ(½+it−ρ)^{-2}<0` = the first Laguerre inequality. So my earlier phase-cancellation/curvature work attacks **`ω_pol`** (localization); the `K`-freeness here attacks **`ω_mot`** (transcendence). They are the **two halves of the seam**, now cleanly separated — and the affine-confinement diagnosis (`phase-cancellation-crux` §8: flow methods can't cross) applies to `ω_pol`, while `ω_mot` is reached by reading the Galois/Stokes constraint (the goal's "transcendence/Galois" route). *The split is itself the realization of the project's two-axis structure inside one object `ω`.*

## §4 Falsifiable predictions
- **P1 (structural DSS):** `K` is free pro-unipotent on `{x_n}_{n≥1}` (one generator per Laurent order). ⟹ no algebraic relation among `{γ_n}` beyond the period-shuffle. **Kill:** exhibit a relation `γ_n ∈ \overline{ℚ}[γ_{<n}, motivic periods]` for some `n` ⟹ `K` not free ⟹ `ω_mot≠0` ⟹ no motive (DSS fails) — *and by orthogonality this does NOT touch RH* (consistency check on the split).
- **P2 (Stokes computation, retargeted §2a):** the **`γ_E`/digamma exponential connection's** Stokes matrices generate a free pro-unipotent group; the Γ-factor's own Stokes data are Tate (powers of `2πi`, computed §2a) and contribute no relations. **Test:** compute the digamma connection's first Stokes data; check no relation at orders matching `γ_0=γ_E, γ_1` (the `(0,1),(1,1)` exponential-corank rungs — `γ_E` irrationality, `γ_E∉ℚ+ℚlog2`).
- **P3 (the split is real):** `ω_pol` and `ω_mot` are independently nonzero-able — there is a fake (off-line Beurling, #85) with `ω_mot=0` (a motive-like structure) but `ω_pol≠0` (no polarization), and a non-motive with `ω_pol`-positive data. **Test:** the realization-converse / the `(E)/(A)/(P)` cuts (#82) should land `ω_pol` and `ω_mot` on different cuts.

## §5 Door / grade
- **§1 (the split):** BRIDGE — resolves an orthogonality conflict by structural reasoning; uses #54/#137 (corpus) + the two faces already in §S–§V.
- **`H²(free)=0` mechanism:** rigorous classical (free Lie algebra cohomological dimension 1).
- **§2 (`K` free ⟺ `ω_mot`=0 ⟺ DSS; Stokes route):** MOONSHOT / CONJECTURE (native). The reduction "ω_mot in `H²(K)`" relies on §R/§S (ω purely archimedean/wild) and the LHS spectral sequence (flagged: ω_mot could carry an `H¹(G_mot,H¹(K))` cross-term; the claim is it's the `H²(K)^{G_mot}` piece). "Γ-factor Stokes ⟹ K free" is the falsifiable bet.
- **Net:** the obstruction to ζ being a motive-with-polarization is `ω = ω_mot(DSS) ⊕ ω_pol(RH)`; `ω_mot` is **freeness of the wild kernel**, attackable by Stokes structure (Galois/constraint), not Schanuel.

## §6 What is and isn't claimed
- **New:** the **split** `ω = ω_mot ⊕ ω_pol` resolving the RH/DSS conflation (orthogonality); **`ω_mot=0 ⟺ K free`** via `H²(free)=0`; the **Stokes-freeness decision procedure** (apex = freeness, not infinitude); the slot-in of the curvature seam as `ω_pol`'s leading member.
- **Corpus (cited):** `ω` purely archimedean (§R/§S); ABP-lift = DSS / hypertranscendence forbids finite lift (§U/§V); `{γ_n}` exponential periods, wild kernel `K` (§W, memory); graded corank (#125); orthogonality (#54/#137).
- **NOT claimed:** DSS, RH, or `ω=0`; that `K` *is* free (the moonshot); that the spectral-sequence reduction is clean (flagged). No Schanuel proven; no web search (per protocol — this is conjecture ahead of SOTA, not a lookup).

## Gates
- [x] 0 → 1: the split diagnosed (orthogonality); `H²(free)=0 ⟹ ω_mot=0` pinned; `K`-free moonshot + Stokes route stated; curvature = `ω_pol` leading member slotted; falsifiable P1–P3.
- [ ] 1 → 2: (a) make the `ω_mot ∈ H²(K)` reduction rigorous (LHS spectral sequence; rule out the cross-term); (b) compute the Γ-factor's first Stokes data (resurgence of Stirling) and test freeness at the `(0,1)/(1,1)` rungs; (c) prove or disprove `K` free for the simplest sub-connection.
- [ ] 2 → 3: formalize `H²(free Lie alg)=0` for the relevant finite truncation; the `corank^{(2)}`/`gr` rungs (reuse #125 Lean anchors).
- [ ] 3 → 4: "ω splits; DSS = freeness of the wild kernel of the Γ-factor's irregular connection."

## Cross-references
- `compute-omega-h2-gl.md` §R–§W — the `ω` program this splits and sharpens (the conflation is in §S/§T vs §U/§V).
- `phase-cancellation-crux.md` §3/§8/§9 — `ω_pol`'s curvature leading member; the affine-confinement (flow can't cross `ω_pol`).
- `corank-seam-invariant.md` §C–§F — the graded/exponential corank; `K` free is the structural form of `corank^{(T)}=∞ ∀T`.
- memory `exponential-period-dss-cross` — the wild kernel `K`, the exponential corank; this card adds the **freeness ⟹ `H²`=0 ⟹ ω_mot=0** mechanism and the Stokes route.

## Log
- 2026-06-19 — created in 1-in-progress (goal: attack whether `ω` vanishes, via the constraint/Galois). **Diagnosed the conflation** (`ω=0⟺RH` §S/§T and `ω=0⟺DSS` §U/§V both can't hold — orthogonality #54/#137) ⟹ **`ω` splits** into `ω_mot` (DSS, motive) ⊕ `ω_pol` (RH, polarization). **Moonshot:** `ω_mot=0 ⟺ K (wild kernel) free pro-unipotent`, via the rigorous `H²(free Lie)=0`; decide it by the **Ramis/Stokes structure of the Γ-factor's irregular connection** (apex = freeness, not infinitude — bypasses Schanuel). `ω_pol` = my curvature seam (`log|ξ| concave` leading member). Falsifiable P1–P3. Honestly flagged: the `ω_mot∈H²(K)` reduction (spectral-sequence cross-term) and `K` free are the open bets. No web search; conjecture ahead of SOTA.
- 2026-06-19 — **Moonshot 2 (§2b): the missing F₁ Frobenius IS the Stokes automorphism** of the archimedean irregular connection (Sabbah wild-Hodge / Stokes-as-Frobenius). Resolves §V's residual ("the infinite/regularized lift must exist — *what is it?*") with a named, computable, constraint-determined object (read off resurgence, not flow-propagated). `ω_mot=0 ⟺ Stokes automorphism acts freely on the exponential periods ⟺ K free ⟺ DSS`.
- 2026-06-19 — **Self-correction (§2a), via computing P2.** Targeted the Γ-factor's Stirling resurgence as the freeness-decider; computed its Borel transform (Binet) = simple poles at `2πik`, residues `1/(2πik)` = powers of `2πi` = **mixed-Tate, NOT wild**. So Γ's Stokes data are motivic (the `a_∞=½log2π=−ζ'(0)` Tate floor), not the obstruction. **Retargeted** to the **`γ_E`/digamma connection** (`e^{-x}\log x`): `K` free ⟺ *its* Stokes structure is free. Conjectured → computed → found the flaw → sharpened the target.
- 2026-06-19 — **§2c honesty caveat:** `K` free ⟹ DSS ⟹ `γ_E∉ℚ` (open), so the moonshot **relocates, not bypasses, the difficulty** (conserved, #103/#125). Split the target: `K_formal` free (structural, irregular-type/Ramis — the tractable, parent-independent sub-goal) vs fullness `K_mot=K_formal` (= DSS, the conserved-hard period part). **Push target = `K_formal` freeness of the digamma connection's Stokes group**, not the period values. Moved card from self-promoted 1-in-progress back to **0-backlog** per user directive (new research → backlog; not self-promoted).
- 2026-06-19 — **§2d: pushed the `K_formal` sub-target concretely (goal).** Identified the right connection = exponential integral `E_1` (`γ_E` = its connection constant). Computed: irregular type slope 1, two factors `{0,−z}`, **Stokes multiplier `2πi` = Tate** — so the **local `K_formal` is Tate-determined, NOT the transcendence carrier** (corrects §2c; same Tate-collapse as the Γ-factor). `γ_E` is a **global regulator / `Ext¹(ℚ,E^{-x}⊗Kum)` class**. Pinned the object: `ω_mot` ∈ the exponential `Ext`-tower `Ext¹(ℚ,E^{-x}⊗ℚ(n))`, regulator `γ_n`. **Surviving tractable sub-target = `dim Ext¹` per order via irregular Hodge numbers** (structural, parent-computable, the generator count); the hard half = regulator injectivity (= DSS). Frontier arc: posed local-Stokes-freeness → computed → found it Tate/global → relocated to a regulator/`Ext` route with a structural dimension sub-target. Difficulty conserved; object sharpened. No web search.- 2026-06-19 (DeWitt) — **§2-cohomology added (rigorous sharpening, hypertranscendence-axis refocus).**
  Upgraded the §2 mechanism from `⟹` to an **iff** via the standard graded-pro-nilpotent theorem
  (`H_1`=generators, `H_2`=relations, `𝔤` free ⟺ `H_2=0`): so the wild kernel grades as
  **`H_1(Lie K)` = exponential-corank** (one `γ_n`/order, the structural generator count, my §7) and
  **`H_2(Lie K)` = ω_mot** (the relations), giving the rigorous reformulation **DSS-cross ⟺ K free ⟺
  `H_2(Lie K)=0`**. Cleanly splits the structural floor (`H_1`) from the hard relations (`H_2`=DSS).
  Addresses gate 1→2(a) partially (the `H_2=0⟺free` half is exact; the LHS cross-term residual stands).
  Card stays 0-backlog (FIELDS-MEDAL moonshot). No web, no runpod.
