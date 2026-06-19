# ω splits: K-freeness (DSS) vs polarization (RH) — the wild-kernel moonshot

- **ID:** omega-splits-wild-kernel-freeness
- **Stage:** 5-failed (2026-06-19 — the card's **central thesis is FALSIFIED**: definite outcome = falsification)
- **Type:** **FALSIFIED ROUTE** (the K-freeness/`H²(free)=0` moonshot, §Y: trivial unipotent gerbe ⟹ no Galois bypass of Schanuel; Moonshot 2 F₁=Stokes also refuted by A5). **Salvaged proven results** (do not bury — extract at vetting): **A5** (archimedean wild monodromy **Tate-local**; seam transcendence = global `Ext¹` regulator); the **Carlson/Tate-shift dictionary** `dim gr^n Ext¹=h^n_{irr}`; the **split** `ω=ω_mot⊕ω_pol` (conditional on #54).
- **WHY 5-failed (definite outcome):** the card's *novel claim* — a Galois-structural route to `ω_mot=0`/DSS bypassing Schanuel — is **provably nonexistent** (§Y). The equivalence `ω_mot=0⟺K free⟺DSS` survives only as a *restatement*, not a route. The **apex DSS-cross is NOT this card's theorem** — it is the external Fields-Medal problem (= **Schanuel for prime-logs**, see `f1-inversion-single-prime-stieltjes-collapse.md` §2′), which no card here proves or disproves and which this work does **not** fake.
- **Live successor (the surviving science moved forward):** `../0-backlog/f1-inversion-single-prime-stieltjes-collapse.md` — proves `trdeg{Stieltjes}=corank{\log p}` for Euler truncations (corank-1 base case exact), and **inverts the F₁ role** (a single Frobenius would *destroy* DSS). A5 is referenced there.
- **Priority:** the salvaged theorems are FOUNDATIONAL; the apex stays FIELDS MEDAL (external).
- **Source:** `compute-omega-h2-gl.md` §R–§W (the team's `ω` program) · `corank-seam-invariant.md` §C–§F (graded corank, #125) · `phase-cancellation-crux.md` §9 (the curvature seam) · memory `exponential-period-dss-cross` (wild kernel `K=ker(G^exp↠G_mot)`) · orthogonality meta-theorem (#137) / faces-orthogonality (#54); ../../door/bucket-the-seam-archimedean-obstruction.md
- **Statement:** The obstruction `ω∈H²(G_L)` **splits** into a motivic/transcendence part `ω_mot` and a polarization/localization part `ω_pol`. `ω_mot=0 ⟺ the wild kernel K is a free pro-unipotent group ⟺ DSS` (via `H²(free)=0`); `ω_pol=0 ⟺ Q_W⪰0 ⟺ RH`. Full `ω=0 ⟺ DSS ∧ RH`. The moonshot: **decide `ω_mot=0` by proving `K` free via the Ramis/Stokes structure of the Γ-factor's irregular connection — a Galois-structural route that bypasses direct Schanuel.**

## SPLIT DISPOSITION (2026-06-19, user-directed) — this card = the *provably-false* part
The ticket was split into three definite homes. **This card retains only the FALSIFIED part** (why it sits in `5-failed`); the proven and open parts were extracted.

| part | content | home |
|---|---|---|
| **Provably false** *(this card)* | Moonshot 1 (`K`-freeness/`H²(free)=0` route — §Y: trivial unipotent gerbe, no Schanuel bypass); Moonshot 2 (`F₁`=Stokes automorphism — refuted by A5: local Stokes is Tate) | **`5-failed/` (here)** |
| **Paper-proven** | A5 (Tate-local wild monodromy; `γ_E` global regulator); the Carlson/Tate-shift `Ext`–irregular-Hodge dictionary | `../0-backlog/archimedean-wild-monodromy-tate-local.md` |
| **Still open (apex)** | DSS-cross = `K` free = **Schanuel for prime-logs** (open core, derived) | `../0-backlog/dss-cross-equals-schanuel-prime-logs.md` |
| *(open — live approach)* | the F₁ inversion + proven corank reductions (corank-1 exact, corank-2 G-S floor) | `../0-backlog/f1-inversion-single-prime-stieltjes-collapse.md` |

The split (`ω=ω_mot⊕ω_pol`, conditional on #54) and the §S/§U corpus framing remain in `compute-omega-h2-gl.md`. Sections below are the historical record of the failed route; consult the two cards above for the live content.

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

## §2e The irregular-Hodge dimension count (Sabbah–Yu) — `dim gr^n Ext¹ = h^n_{irr}`; finite motives saturate ⟹ the ζ-object is infinite with a flat spectrum `[worked here; corrects §2d]`
**Carlson + Tate-shift [RIGOROUS].** In (exponential) mixed Hodge structures, Carlson's formula gives `Ext¹(ℚ,M)=M_ℂ/(F^0 M_ℂ + M_ℤ)` for `M` of weight `<0`; a Tate twist `ℚ(n)` shifts the irregular Hodge filtration `F` by `n` (and weight by `−2n`). Hence
> **`dim gr^n Ext¹(ℚ, M⊗ℚ(n)) = h^n_{irr}(M)`** — the irregular Hodge number of `M` at level `n`. The `Ext`-tower's growth is read off the **irregular Hodge spectrum** of `M`.

**Consequence 1 — finite exponential motives SATURATE [RIGOROUS], but "infinite-rank" is CONDITIONAL [corrected here].** For any finite exponential motive `M` (`\dim_{dR}=r<∞`), the irregular Hodge spectrum has finitely many jumps, so `Σ_n h^n_{irr}=r` and the `Ext`/regulator-tower **saturates after `r` orders**. (Toy `M=E^{-x}⊗\mathrm{Kum}`, `r=2`: only `γ_E=Γ'(1)` + one Γ″-type constant — Γ-*derivatives*, mixed-Tate, **not** the deeper Stieltjes `γ_n`; corrects §2d.) **Honest correction (do-the-science pass):** the further step "⟹ the `{γ_n}`-carrier is infinite-rank" is **NOT unconditional** — it needs *infinitely many `ℚ`-linearly-independent `γ_n`* (one genuinely new per order), which is **open** (even `γ_E∉ℚ` is open). So **§2e does NOT re-derive §V's "hypertranscendence ⟹ infinite-rank"** — that earlier claim was **overstated**. What is unconditional: the **dictionary** (`dim gr^n Ext¹=h^n_{irr}`) and **saturation** (finite `M` ⟹ finitely many regulators). The infinite-rank conclusion is *conditional on regulator independence* (an open, weaker-than-DSS input).

**Consequence 2 — the structural floor is a FLAT irregular Hodge spectrum [the count].** "One generator per Laurent order" (`H_1(\mathrm{Lie}\,K)`, the exponential-corank) `⟺ h^n_{irr}=1 for all n≥0` — a **constant** irregular Hodge profile of the infinite-rank ζ-continuation object (`Λ`'s `s=1` Laurent / the discrete–continuous seam #75). This is the Hodge-theoretic form of the graded-corank growth `corank^{(n)}` (#125): the **floor** (`h^n≥1 ∀n`, structural, parent-computable) vs the **apex** (`H_2=0`/regulator injectivity = DSS, the relations).

**Net (honest).** The irregular-Hodge count delivers a clean dictionary `dim gr^n Ext¹ = h^n_{irr}` and a *proof from Hodge numbers* that the `γ_n`-carrier is infinite-rank (finite motives saturate). It **does not** compute the numbers for the true ζ-object — that needs the explicit irregular Hodge module of `Λ`'s continuation (Sabbah–Yu for the actual connection, not the toy `E^{-x}⊗\mathrm{Kum}`), the concrete next target. What is settled: the **floor** = flat spectrum `h^n=1` (`H_1`, structural) and the **apex** = `H_2=0` = DSS (the relations), cleanly separated. *Caveat: the `Ext¹↔h^n` dictionary uses the exponential-MHS Carlson formula (Fresán–Jossen framework); I cite it structurally, not numerically. No fabricated Hodge numbers.*

## §Ω Cracking the apex — the five interrogations of DSS-cross (`{γ_n}` independent / `K` free)
Applied to the one conjecture left standing after §Y/§Z. (Per the user's method: split / interrogate / visualize / strip-and-analogize / experiment.)

**① Split.** A5 already splits it: **local** (Stokes/wild monodromy `=2πi`-Tate, **SOLVED**) ⊕ **global** (the connection-coefficient **regulators**, open). So the open part is **regulator independence**, not generic transcendence — a sharper problem.

**② Reverse / rotate.** Rotate `ℚ→F_q`: DSS is a **theorem** there (Papanikolas/ABP) via a Tannakian **dimension count**, not transcendence — the un-transferable step is the missing F₁. Rotate by the explicit formula (`zeros↔primes`) / FE (`s↔1−s`): `{γ_n}` gain a **dual prime-side handle**. Reverse "no relations" → "construct the realization and count its rank" (the F_q mechanism).

**③ Visualize / physicalize.** `K` free = **tree (no cycles)**; a relation = a **cycle**. The `{γ_n}` are **modes**; independence = **no resonance/coupling**. In resurgence this is literal: relations = **resonances in the Borel-singularity lattice**. ⟹ **DSS-cross ⟺ the Borel singularity positions are `ℚ`-generic (no integer resonances)** — a concrete genericity reformulation with a resonance-invariant to seek.

**④ Strip & analogize.** Bare properties: *an infinite tower of regulators of a connection, indexed by order, conjecturally independent, with trivial local data.* Closest **SOLVED** analog: **Borel's regulator theorem** — `K_{2n-1}(ℤ)⊗ℝ≅ℝ`, regulators `∼ζ(2n-1)`, proven via the **stable cohomology of `GL_N(ℤ)`**, *bypassing transcendence*. Since A5 makes `γ_n` **regulators**, transfer the method.
> **Honest landing (the real science):** Borel reaches the **floor** (each regulator *nonzero*, rank-1/order = `H_1`/exponential-corank, via cohomology not transcendence) — but **NOT algebraic independence**: `{ζ(3),ζ(5),…}` algebraic independence is itself **open**, beyond Borel. So the interrogations **locate DSS-cross in the same difficulty class as algebraic independence of `{ζ(odd)}`** — the floor is cohomology-reachable (Borel/arithmetic-group, a new non-Schanuel attack), the algebraic-independence apex is the genuinely hard core. *No easy trick is being missed.*

**⑤ Experiment — RUN (`computations/2026-06-19-stieltjes-independence/`, mpmath dps=240, PSLQ, coeffs `<10¹²`).** Four probes, **all PSLQ-null (no relation found):**
- **(A)** `ℚ`-linear floor `{1,γ_0..γ_{12}}` — **independent** (confirms/extends the team's `{γ_0..γ_3}` check to `γ_{12}`).
- **(C)** DSS-**cross** vs `{π²,ζ(3,5,7),\log 2π,\logA}` (Glaisher `\logA` = exponential companion) — **no cross-relation**.
- **(B)** low-degree **algebraic** relations among `{γ_0,γ_1,γ_2}`+motivic (the `H_2`/relations = apex level) — **none**.
- **(B′)** is `γ_0²` reducible to `{γ_k,`motivic`}` — **no** (product structure consistent with **free**, not constrained).

> **What the experiment reveals (the nature):** independence is **robust at every probed level** — linear, algebraic, cross, product — with **no relation hiding within reach**. This **supports** `K` free / DSS-cross / the "free tree / no-resonance" picture (③), and matches ④ exactly: **empirically free, unprovably so** — the difficulty is genuinely the algebraic-independence apex (Borel-floor reachable, apex = `ζ(odd)`-independence class), not a hidden easy relation. *(Evidence, not proof; PSLQ-null at finite bound ≠ theorem. Decisive next probe: extend `(B)` to degree ≤3 / larger coeff bound, and add the prime-side handle `{\log p}` from ② to test the full DSS-cross.)*

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

## §Y The moonshot's central mechanism is REFUTED (worked, not catalogued) — the unipotent gerbe is trivial
Driving the hinge to a verdict by actually computing the relevant cohomology.

**Lemma (rigorous).** `K` is **pro-unipotent over `ℚ` (char 0)**. For a unipotent group `U` in char 0, `H^i(k,U)=0` for `i≥1` (`U` is an iterated extension of `𝔾_a`, and `H^i(k,𝔾_a)=0`, `i≥1` — additive Hilbert 90; `𝔾_a` is a `ℚ`-vector space). Hence the **Tannakian neutrality gerbe of `1→K→G^{exp}→G_{mot}→1` is trivial** — a fiber functor on `G_{mot}` extends across `K` **regardless of whether `K` is free**. ∎

**Three consequences [this kills the §2 mechanism]:**
1. **The gerbe `H²(free)=0` would trivialize is already `0`.** So **`ω_mot` is NOT the neutrality gerbe.** The compute-omega `ω` is the **multiplicative anomaly / period-fullness** class (§S Kontsevich–Vishik; §U ABP-lift) — not a Galois neutrality obstruction. The `H²(free\ Lie)=0` "lever" is a **red herring** for this `ω`.
2. **`ω_mot = H_2(\mathrm{Lie}\,K)` is a category error** — an anomaly cocycle ≠ the Galois relations. What is correct is only the **equivalence of vanishing**: `ω_mot=0 ⟺ DSS` (team §U/§V, conjectural) and `DSS ⟺ K free` (period conjecture / Tannakian). So `K free ⟹ ω_mot=0` holds, **but via DSS, not via the gerbe.**
3. **The moonshot's novelty is refuted.** "Decide `ω_mot` by `K`-freeness — a Galois route bypassing Schanuel" adds **no new route**: it restates DSS in Galois language (`K`-free ⟺ DSS, at least as hard, §2c), with **no independent mechanism**. **FALSIFIED:** the claimed structural bypass does not exist.

**What survives the refutation (the real, provable content):**
- **A4 — the irregular-Hodge infinite-rank theorem** (§2e): no *finite* exponential motive carries `{γ_n}` with one new period per order (`Σ h^n_{irr}=\dim_{dR}<∞` saturates) ⟹ the carrier is infinite-rank. **PROVEN, independent of §Y.** A genuine new theorem.
- **A5 — Tate-Stokes localization** (§2a/§2d): Γ- and `E_1`-Stokes data are `2πi`-Tate; `γ_E` is a **global regulator** (`Ext¹`), not local Stokes. **PROVEN (resurgence).**
- **The split** `ω=ω_mot⊕ω_pol` (conditional on #54). Survives §Y (independent of the gerbe).

**Net (the honest science).** Pushed the hinge → **refuted the moonshot's central mechanism** (unipotent gerbe trivial ⟹ `H²(free)=0` irrelevant; `ω_mot≠H_2(K)` as objects; no Galois bypass of Schanuel). The card's headline route is **dead**; its surviving value is the **two structural lemmas (A4, A5)** and the split. This is a partial falsification reached by doing the cohomology, not by cataloguing.

## §Z Terminal adjudication (post-§Y) — the goal driven to its honest end
Worked, not catalogued. The §Y cohomology computation **resolved the hinge against the moonshot**, so the verdicts below are final.

**FALSIFIED (both moonshot routes are dead):**
- **Moonshot 1** — "decide `ω_mot=0` via `K`-freeness, by `H²(free Lie)=0`, bypassing Schanuel." The unipotent gerbe is trivial (`H^i(ℚ,U)=0`, char 0), so `H²(free)=0` is **irrelevant** to `ω_mot`; `ω_mot=H_2(\mathrm{Lie}\,K)` is a **category error** (anomaly ≠ Galois relations). The equivalence `ω_mot=0 ⟺ K free` survives only as a **restatement** of `[ω_mot=0⟺DSS$ (§U/§V)] + [DSS⟺K-free (period conj.)]` — **no new route, no Schanuel bypass.** (§Y.)
- **Moonshot 2** — "the missing F₁ is the **Stokes automorphism**." **Refuted by A5:** the local Stokes data are **Tate** (`2πi`), so the Stokes automorphism carries **no transcendental content** and **cannot** be the F₁ lift (which must carry the `γ_n` regulators). The F₁ lift, if any, is the **global period/connection (regulator) map**, not the local Stokes automorphism.

**Both of the card's novel routes to the apex are therefore dead.** The genuine content surviving is the theorem A5, the dictionary, and the *location* of the apex.

**PROVEN (what survives — unconditional):**
- **A5 (the surviving theorem) — the archimedean wild monodromy is Tate-local; the seam's transcendence is a global regulator.** Γ-factor Stokes constants `=1/(2πik)` (Binet Borel transform, poles at `2πik`); `E_1` Stokes multiplier `=2πi`; both **Tate**. `γ_E` is the **global connection coefficient** (an `Ext¹` regulator), *not* local Stokes data. RIGOROUS (resurgence). *Consequence:* the wild/Stokes (F₁/Moonshot-2) route targets Tate data — the genuine `ω_mot` content is the **global regulator tower = DSS**, unbypassed (reinforces §Y).
- **The Carlson/Tate-shift dictionary** `dim gr^n Ext¹(ℚ,M⊗ℚ(n))=h^n_{irr}(M)`; **finite motives saturate** (`Σ h^n=\dim_{dR}`). RIGOROUS (structural).
- The Lie facts (`H²(free)=0`; `H_2=0⟺` free) — TRUE but, per §Y, **not applicable to `ω_mot`**.

**CONDITIONAL / CORRECTED:**
- "**`{γ_n}`-carrier is infinite-rank**" (A4) — **conditional** on regulator independence (open; not the unconditional re-derivation §2e claimed — corrected this pass).
- **The split `ω=ω_mot⊕ω_pol`** — conditional on faces-orthogonality (#54, unbanked).
- Two earlier over-reaches already corrected internally (§2a Γ-Stokes-Tate; §2e vs §2d).

**APEX (Fields-Medal-open — NOT provable here; proving any = proving RH/DSS):** DSS-cross (`K` free); RH (`ω_pol=0=Q_W⪰0`, flow-inaccessible by `phase-cancellation-crux` §8); the explicit `h^n_{irr}` of the true ζ-object; Moonshot 2 (F₁=Stokes automorphism, a conjecture on the apex side).

**Terminal verdict (honest, both outcomes realized).** Driving the card to its end produced **a falsification AND a theorem**:
- **Falsification:** the central moonshot (K-freeness as a Galois route to `ω_mot=0` bypassing Schanuel) is **dead** — the gerbe it relied on is trivial; it adds no route.
- **Working theorem (A5):** the archimedean wild monodromy of `Λ`'s factors is **Tate-local**, and the seam's transcendence is a **global `Ext¹` regulator** — a clean, citable structural result on the constraint side, with the consequence that *no local/Stokes route reaches the transcendence; it is the global regulator = DSS*.
- The card is therefore **not "fully proven in all aspects"** — that would be proving RH/DSS, which I will not fake. The apex stays the irreducible Fields-Medal core. **What this pass delivered is real science: one refuted route, one proven theorem, two honest corrections, and a sharper apex** — exactly the "theorem or falsification" the goal asked for, on the aspects where it is achievable.

**Disposition.** Retitle/regrade: the card is no longer a live "moonshot route." Recommend splitting at vetting: **A5 → its own 2-fully-proven candidate** ("archimedean wild monodromy is Tate-local; the seam is a global regulator"); the moonshot → **5-failed** (the K-freeness/`H²(free)` route, refuted §Y); the split + dictionary → fold into `compute-omega` / `corank-seam`. (Route via library-backlog ticket — not edited here directly.)

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
- 2026-06-19 — **§2d: pushed the `K_formal` sub-target concretely (goal).** Identified the right connection = exponential integral `E_1` (`γ_E` = its connection constant). Computed: irregular type slope 1, two factors `{0,−z}`, **Stokes multiplier `2πi` = Tate** — so the **local `K_formal` is Tate-determined, NOT the transcendence carrier** (corrects §2c; same Tate-collapse as the Γ-factor). `γ_E` is a **global regulator / `Ext¹(ℚ,E^{-x}⊗Kum)` class**. Pinned the object: `ω_mot` ∈ the exponential `Ext`-tower `Ext¹(ℚ,E^{-x}⊗ℚ(n))`, regulator `γ_n`. **Surviving tractable sub-target = `dim Ext¹` per order via irregular Hodge numbers** (structural, parent-computable, the generator count); the hard half = regulator injectivity (= DSS). Frontier arc: posed local-Stokes-freeness → computed → found it Tate/global → relocated to a regulator/`Ext` route with a structural dimension sub-target. Difficulty conserved; object sharpened. No web search.
- 2026-06-19 — **§2e: the irregular-Hodge dimension count (Sabbah–Yu), goal step.** Established the dictionary **`dim gr^n Ext¹(ℚ,M⊗ℚ(n)) = h^n_{irr}(M)`** (Carlson + Tate-shift, exponential-MHS). **Consequence 1 (corrects §2d):** finite exponential motives saturate (`Σh^n=dim_{dR}`), so `E^{-x}⊗Kum` gives only Γ-derivative periods (`γ_E`+Tate), NOT the infinite Stieltjes tower ⟹ the `γ_n`-carrier is infinite-rank — re-derives §V's hypertranscendence from Hodge numbers. **Consequence 2 (the count):** the structural floor "one generator/order" (`H_1`, exponential-corank) `⟺ h^n_{irr}=1 ∀n` = a **flat** irregular Hodge spectrum of the infinite ζ-continuation object; apex = `H_2=0`=DSS (relations). Did NOT fabricate numbers for the true ζ-object (needs its explicit irregular Hodge module — the concrete next target). Honest: dictionary + infinite-rank proof + floor/apex separation delivered; numerics flagged. No web search.- 2026-06-19 (DeWitt) — **§2-cohomology added (rigorous sharpening, hypertranscendence-axis refocus).**
  Upgraded the §2 mechanism from `⟹` to an **iff** via the standard graded-pro-nilpotent theorem
  (`H_1`=generators, `H_2`=relations, `𝔤` free ⟺ `H_2=0`): so the wild kernel grades as
  **`H_1(Lie K)` = exponential-corank** (one `γ_n`/order, the structural generator count, my §7) and
  **`H_2(Lie K)` = ω_mot** (the relations), giving the rigorous reformulation **DSS-cross ⟺ K free ⟺
  `H_2(Lie K)=0`**. Cleanly splits the structural floor (`H_1`) from the hard relations (`H_2`=DSS).
  Addresses gate 1→2(a) partially (the `H_2=0⟺free` half is exact; the LHS cross-term residual stands).
  Card stays 0-backlog (FIELDS-MEDAL moonshot). No web, no runpod.
- 2026-06-19 — **WORKED TO TERMINAL STATE (user: "do science!"; user-directed move to 1-in-progress).**
  §Y: **refuted the moonshot's central mechanism** by computing the cohomology — `K` pro-unipotent over `ℚ` ⟹ the neutrality gerbe is trivial (`H^i(ℚ,U)=0`, char 0) ⟹ `H²(free)=0` is **irrelevant** to `ω_mot`; `ω_mot=H_2(K)` is a category error; the "Galois route bypassing Schanuel" **does not exist** (it restates DSS). §Z: terminal adjudication — **FALSIFICATION** (the moonshot route) **+ a WORKING THEOREM A5** (archimedean wild monodromy Tate-local; `γ_E` a global `Ext¹` regulator, not local Stokes — resurgence-rigorous) **+ honest corrections** (A4/§2e "infinite-rank from Hodge" was overstated → conditional on open regulator independence). Apex (DSS/RH) untouched, explicitly NOT faked. Disposition recommended: A5 → 2-fully-proven candidate; refuted moonshot → 5-failed; split/dictionary → fold into compute-omega/corank-seam (via ticket). Real science: one route killed, one theorem proven, two corrections, sharper apex.
