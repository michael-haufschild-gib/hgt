# The multi-q ABP criterion — the native DSS lower bound as a Tannakian count, NOT effective Schanuel (reopening obstruction C)

- **ID:** multi-q-abp-criterion
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper, structural no-go + decomposition) — Door grade **BRIDGE**; began as a CONJECTURE
  reopening obstruction C, resolved to a sharp structural verdict (one residual flagged to Professor #128)
- **Source:** challenges the "no-bypass / = effective Schanuel" closure of
  `../0-backlog/g2-dss-lower-bound.md` and the orbit no-go `../2-fully-proven/dss-lower-bound-orbit-nogo.md`;
  builds on G4 (multi-q Picard–Vessiot / `G_L` Tannakian, #24/#28), Papanikolas 2008 + ABP
  (Anderson–Brownawell–Papanikolas) over `F_q`, the G2 upper bound #8.

---

## The claim being challenged
Two cards declare obstruction C (the DSS lower bound `trdeg ≥ dim G_L·δ`) **irreducibly = effective
Schanuel-for-prime-logs**, "difficulty conserved, no bypass" (`g2-dss-lower-bound` §"Difficulty conserved"),
and the native apparatus **provably cannot** supply it (`dss-lower-bound-orbit-nogo`). **Both are
route-specific and the closure is premature.** They establish:
- the **orbit/genericity** route gives only the upper bound (Kronecker `t`-flow ⊥ the `s=1` edge) — correct;
- the **friable analytic Siegel–Shidlovsky race** (A+B+C, the Prop-8.3 height budget) *lands on* effective
  Schanuel — correct, for *that* route.
Neither addresses the route by which the lower bound is **actually a theorem over `F_q`**.

## The decisive precedent: over `F_q` the lower bound is NOT effective Schanuel
Over `F_q(t)`, the DSS-analog lower bound (`trdeg(periods) = dim G`) is **Papanikolas's theorem (2008)**,
proved via the **ABP criterion** (Anderson–Brownawell–Papanikolas): a `t`-motive's periods satisfy *only*
the linear relations forced by the motive, established through the **Frobenius (`φ`) difference-Galois
structure** as a **Tannakian dimension count** — `trdeg = dim G`. Crucially this is **not** a Diophantine /
effective-Schanuel argument: there is **no height-budget race, no effective transcendence measure**. So
**the DSS lower bound, where it is a theorem, is obtained WITHOUT effective Schanuel** — by an algebraic
(Tannakian) count over the difference-Galois group.

⟹ The equation "obstruction C = effective Schanuel" holds **only for the analytic-race route**. The
**Tannakian/ABP route** — the one that works at the border — does **not** reduce to effective Schanuel. The
"no bypass" verdict conflated one route with all routes.

## The conjecture (the native attack)
> **Multi-q ABP criterion.** There is an Anderson–Brownawell–Papanikolas-type linear-independence criterion
> for the **infinite-base multi-`q` module** `M_ζ`, in which the **simultaneity of the prime dilations
> `{σ_p}`** plays the role the single Frobenius `φ` plays over `F_q`. It yields
> `trdeg(periods of M_ζ) = dim(G_L) = ∞` — i.e. **DSS — as a Tannakian count over `G_L`**, with no effective
> Diophantine input.

This is the precise technical form of the field's **founding bet** (vision §1, N1): *infinitely many
independent bases acting simultaneously do collectively what one Frobenius does over `F_q`.* The single
missing Frobenius (`F₁`) is exactly what ABP-over-`F_q` *uses*; the claim is that the **coupled infinite
family `{σ_p}` is a genuine substitute** for it at the level of the ABP criterion — not at the level of a
single operator.

## Why this is NOT refuted by the existing no-gos
- **Orbit no-go (`dss-lower-bound-orbit-nogo`):** the orbit is the **abelian Kronecker shadow** of `G_L`
  (the `t = Im s` flow). ABP does **not** use the orbit; it uses the **full Tannakian** difference-Galois
  category + the `φ`/`σ`-semilinear structure. The no-go's "`t`-flow ⊥ `s=1` edge" says nothing about the
  ABP linear-independence criterion (an algebraic-relation statement on the module, not a dynamical
  distribution). **Orthogonal objects; the no-go does not apply.**
- **Effective-Schanuel wall (`g2-dss-lower-bound`):** ABP is **not** an effective bound; Papanikolas gets
  `trdeg = dim G` with no height race. So the multi-q ABP route does **not** pass through the
  effective-Schanuel wall — it is the analytic race that does. The "difficulty conserved / reduces *exactly*
  to Schanuel" claim is therefore about the wrong (analytic) route.

## The genuine open obstruction (sharper than "Schanuel")
The real question is **whether ABP survives the loss of the single Frobenius.** Two honest possibilities:
1. **(crossing)** The simultaneous `{σ_p}` (with the proven free orbit closure `𝕋^∞`, #9, and the corank-∞
   linear floor) supply enough rigidity for a multi-`q` ABP criterion ⟹ DSS as a Tannakian count, bypassing
   effective Schanuel. The field crosses the wall.
2. **(genuine wall, sharper than the team's)** ABP **essentially requires a single `φ`** (the `t`-motivic
   rigidity of one operator: the `φ`-module / Frobenius-semilinearity is what makes ABP's linear-algebra
   work); the infinite base with **no single Frobenius** genuinely obstructs it. Then the obstruction is
   **"ABP needs `F₁`"** — a *structural* statement about the criterion, **strictly sharper** than "it's
   effective Schanuel," and it would be the true `F₁`/D4 obstruction located at the right (Tannakian) level,
   not the analytic one.
Either way this is **frontier**: it reopens obstruction C at the level where the `F_q` theorem actually
lives, and replaces "it's effective Schanuel (an analytic accident of one route)" with the precise question
**"does ABP need a single Frobenius, or does simultaneity substitute?"**

## Approach
1. **Pin the multi-q ABP statement.** Transcribe the ABP criterion (`φ`-modules, the linear-independence /
   "no spurious relations" theorem) into the infinite-base multi-`q` setting (`G_L`-Tannakian, G4 #24/#28):
   what is the `σ_p`-semilinear analog of the `φ`-module, and the analog of the ABP rigidity matrix?
2. **Locate where the single `φ` enters classical ABP** and test whether the simultaneous `{σ_p}` (or the
   completed `∂_s`-weld) can replace that exact step — the make-or-break.
3. **Door-2 it:** if simultaneity substitutes ⟹ native crossing (the field's founding bet realized, a real
   C5/DSS theorem); if ABP irreducibly needs `F₁` ⟹ the sharper structural no-go ("ABP needs the missing
   Frobenius"), re-grade and feed the seam (#125) at the ABP level.
4. **`F_q` consistency:** the multi-q ABP must restrict to Papanikolas over `F_q` (corank 1, single `φ` =
   the degenerate case) — the Door-5 calibration.

## Gates
- [x] 0 → 1 in-progress: the route distinction (orbit / analytic-Schanuel / **Tannakian-ABP**) made precise;
  the `F_q` precedent (Papanikolas ≠ effective Schanuel) established; the multi-q ABP conjecture posed; the
  two honest outcomes (crossing vs sharper "ABP-needs-F₁" wall) stated; not refuted by the existing no-gos.
- [ ] 1 → 2 fully-proven: either prove a multi-q ABP criterion ⟹ DSS (crossing), or prove ABP irreducibly
  needs a single Frobenius (the sharper structural obstruction). **Step 2 = locate where `φ` enters ABP.**
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Cross-references
- `../2-fully-proven/dss-lower-bound-orbit-nogo.md` (DeWitt) — closes the **orbit** route; this card argues
  it does **not** close the **ABP/Tannakian** route. **Coordinate — not a contradiction; a different route.**
- `../0-backlog/g2-dss-lower-bound.md` — the analytic-race route (lands on effective Schanuel); this is the
  complementary Tannakian route.
- G4 `compute-omega-h2-gl.md` / #24 / #28 (the `G_L`-Tannakian structure ABP would run on); Papanikolas 2008,
  ABP (the `F_q` precedent + the criterion to transcribe).
- `corank-seam-invariant.md` (#125) — if outcome (2), the "ABP needs `F₁`" obstruction is the sharper seam.

## Log
- 2026-06-19 (Wheeler) — created. Frontier reopening of obstruction C, prompted by the user's call for
  right-of-the-wall science (not lookups/BRIDGE-gradings). Decisive point: over `F_q` the DSS lower bound is
  Papanikolas/ABP = a **Tannakian dimension count, NOT effective Schanuel** — so the team's "obstruction C =
  effective Schanuel, no bypass" is route-specific (true for the analytic race, false for the Tannakian
  route that actually proves it at the border). The orbit no-go closes only the abelian orbit, not ABP.
  Proposed the **multi-q ABP criterion** (simultaneous `{σ_p}` substituting for the single Frobenius `φ`) as
  the native attack = the precise form of the field's founding bet. Two honest outcomes: native crossing, or
  the sharper structural obstruction "ABP needs `F₁`" (better than "it's Schanuel"). Step 2 = find where `φ`
  enters classical ABP and test the substitution. Conjecture/program, not a closed proof — flagged.

## §2 done — the finite-S reduction: the keystone becomes a CONCRETE FINITE question (Wheeler, 2026-06-19)

**Located where the single Frobenius enters ABP.** In ABP (Thm 3.1.1 shape), a `t`-motive yields a difference
equation `ψ^{(-1)} = Φψ` with `Φ` a **finite** matrix over `K̄[t]` and `^{(-1)}` the **single** Frobenius
twist; the criterion lifts a linear relation among periods `ψ(θ)` (at the **single** special point `θ`) to a
relation of functions governed by that **one** σ-equation; Papanikolas's Tannakian theory then gives
`trdeg = dim G`. The single Frobenius enters as (i) one twist `^{(-1)}`, (ii) **finite rank** (`Φ` finite),
(iii) one special point `θ`.

**First objection, and its removal.** Naively M_ζ over ℚ is **infinite-rank** (G1: ζ non-holonomic, no finite
difference equation) ⟹ no finite `Φ` ⟹ ABP can't be set up. **But G1 also says ζ is finite-base-HOLONOMIC at
every finite truncation:** the module `M_S` of the truncated Euler product `ζ_S=∏_{p≤S}(1-p^{-s})^{-1}` is
**finite-rank/holonomic**. So a **finite-base multi-q** ABP (finitely many `σ_p`, `p≤S`) **can** be set up on
`M_S`. Non-holonomicity is only in the limit — it does **not** block the truncated criterion.

**The reduction (the keystone made finite).**
- IF finite-base multi-q ABP holds on `M_S` ⟹ `trdeg(periods of M_S) = dim G_S = corank_S`.
- `corank_S = #{ℚ\text{-indep } \log p : p≤S} = π(S)` (Baker, the proven linear floor).
- ⟹ `trdeg_S = π(S)` ⟹ **`{\log p : p≤S}` algebraically independent** (finite Schanuel for prime-logs);
  `S→∞` ⟹ `trdeg→∞` ⟹ **DSS**.

So the make-or-break is **finite and concrete**: does **multi-q (several `σ_p`, NO single Frobenius)**
finite-base ABP give `trdeg_S = corank_S`? Over `F_q` the **single-`φ`** analog is Papanikolas — works. The
question is whether the **simultaneity of `{σ_p}`** substitutes for the single-`φ` rigidity in the ABP lift.

> **Smallest concrete test (`S` = two primes `{2,3}`):** does a 2-prime `(σ_2,σ_3)` ABP-type criterion prove
> `\log 2, \log 3` **algebraically independent**? (Open even here.) This is the keystone's atom.

**The honest dichotomy (both outcomes frontier, both concrete):**
1. **Crossing.** Multi-q rigidity works at finite `S` ⟹ proves finite Schanuel for prime-logs ⟹ DSS. Would
   settle alg. independence of `\log 2,\log 3` — a massive breakthrough. Not a priori refuted (the multi-q
   `M_S` is genuinely richer than a single function); suspicious-if-too-easy, so the lift step needs real care.
2. **Sharp obstruction.** The ABP lift **essentially needs ONE twist / one special point** (the single-`φ`
   `t`-motivic rigidity); `k≥2` independent `σ_p` **break the lift** (no common special point; the joint
   `σ_p`-equation is the non-holonomic one G1 forbids in the limit, and even at finite `S` the multiple
   twists may not rigidify the period lattice). Then the obstruction is **"ABP needs a single Frobenius; the
   multi-q family cannot supply the lift"** — a *structural* statement at the Tannakian level, strictly
   sharper than "it's effective Schanuel," tied directly to `F₁`/G1/corank (#125), and explaining why even
   **finite** Schanuel-for-prime-logs is unreachable by this route.

**Next concrete step (Step 3):** transcribe the 2-prime `M_{\{2,3\}}` difference module and its ABP lift
explicitly — identify the single-`θ`/single-twist step and test whether `(σ_2,σ_3)` jointly fill it. This is
a finite, explicit computation/reasoning, not an apex hand-wave.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§2: reduced the keystone to a concrete finite question.** Located the single-Frobenius
  dependence in ABP (one twist `^{(-1)}`, finite rank, one special point `θ`). Removed the infinite-rank
  objection by **truncation** (G1: `M_S` finite-base-holonomic). Reduction: finite-base multi-q ABP on `M_S`
  ⟹ `trdeg_S = corank_S = π(S)` ⟹ finite Schanuel for prime-logs ⟹ (S→∞) DSS. Make-or-break is now FINITE:
  does multi-q (no single Frobenius) ABP give `trdeg_S = corank_S`? Smallest atom: 2-prime `(σ_2,σ_3)` ABP ⟹
  `\log2,\log3` algebraically independent? Dichotomy: crossing (finite-Schanuel breakthrough) vs sharp
  structural obstruction ("ABP needs one Frobenius; `k≥2` σ_p break the lift", sharper than effective
  Schanuel, tied to F₁/#125). Next: transcribe the 2-prime ABP lift explicitly. Program/conjecture — flagged.

## §3 — the explicit 2-prime transcription: the bypass FAILS, but the obstruction is SHARPER than effective Schanuel (Wheeler, 2026-06-19)

Worked the 2-prime atom explicitly. **Honest correction: the §2 finite-S reduction is FLAWED** — and the
flaw is informative.

**The truncated Euler module is CC-trivial (rational), not corank-2.** For `ζ_{2,3}=(1-x_2)^{-1}(1-x_3)^{-1}`,
`x_p=p^{-s}`: each factor `f_p=(1-x_p)^{-1}` satisfies `σ_p f_p = a_p f_p`, `a_p=(1-x_p)/(1-p^{-1}x_p)∈ℂ(x_p)`.
But `f_p` is **rational** in `x_p` ⟹ `a_p` is a **coboundary** (CC, multiplier-dichotomy #131) ⟹ `M_{2,3}` is
**gauge-trivial**, its Picard–Vessiot extension rational, **`trdeg(periods)=0`, not `π(S)`**. The truncated
Euler product is an algebraic (rational) function of `x_2,x_3` — zero transcendence. So `{\log p}` are **not**
periods of the prime-truncated module; `trdeg_S=corank_S` is false. *(Conjecture pursued explicitly, flaw
found — the prime/Euler wing is CC/rational/free, exactly the team's "prime wing is BRIDGE".)*

**Where the transcendence really is — and why the prime ABP can't reach it.** The DSS periods (`{γ_n}` /
zeros of *full* `ζ`) require the **infinite product + analytic continuation + FE/archimedean coupling** —
none survive truncation. By the seam firewall (#106, mine): the prime block (CC) ⊥ the archimedean (non-CC);
the transcendence is **archimedean-seam**, *outside* the prime `G_L`. So a multi-q ABP on the prime structure
gives only CC-trivial content — it **cannot** reach `{γ_n}`. The prime Tannakian count ≠ DSS.

**The relocation to the completed module, and the sharp obstruction.** ABP requires **one difference-Frobenius**
(a σ-semilinear automorphism) as its twist. Over ℚ the candidates fail by *type*: the `{σ_p}` are **many** and
**CC-trivial** on the prime side; the archimedean `∂_s` — where the periods live — is a **derivation
(differential)**, the **wrong type** for an ABP difference-twist. There is **no single difference-Frobenius
over ℚ.**
> **Verdict (outcome 2, sharpened, honest): the multi-q ABP route is blocked — NOT by effective Schanuel, but
> by a structural Tannakian-level obstruction: (a) the prime module is CC-trivial (truncations rational),
> (b) the DSS periods are archimedean-firewall-separated (#106), (c) there is no single difference-Frobenius
> to run ABP (`σ_p` many+CC; `∂_s` differential, not a Frobenius). "ABP needs F₁."**

**Net (the contribution, honest):**
- The **reopening stands**: the team's "obstruction C = effective Schanuel, no bypass" IS a route-conflation
  — over `F_q` the lower bound is Tannakian (Papanikolas), not effective Schanuel. Correct, unchanged.
- **But the concrete bypass fails**, and the failure **upgrades** the obstruction: from "effective Schanuel
  (an analytic shadow of one route)" to **"missing single difference-Frobenius F₁ (structural, Tannakian)"** —
  tied to the firewall (#106), the seam (#125), and `∂_s` (#128). The orbit no-go (DeWitt, abelian/`t`-flow)
  + this ABP no-go (Tannakian/`F₁`) close **both** native routes **uniformly via the same missing F₁**;
  effective Schanuel is its analytic shadow.

**The one escape — handed to Professor's #128.** ABP is blocked because `∂_s` is differential, not a
difference-Frobenius. IF `∂_s` (or the completed `(σ,∂)`-weld) can serve as a **parametrized/differential
ABP twist** — a *differential* ABP criterion à la Hardouin–Singer rather than a Frobenius ABP — the route
could yet run on the completed module. That is exactly Professor's `#128` (`∂_s` = missing Frobenius) /
`compute-omega-h2-gl` (#27). **Card stays in-progress pending #128.** If `∂_s` cannot be an ABP/parametrized
twist for the period lattice, outcome (2) is final: the DSS lower bound is the structural "needs-F₁" wall,
sharper than effective Schanuel.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§3: explicit 2-prime transcription; bypass fails, obstruction sharpened.**
  Self-corrected the §2 reduction: the truncated Euler module `M_{2,3}` is **CC-rational/trivial**
  (`f_p=(1-x_p)^{-1}` rational ⟹ `a_p` coboundary, #131) ⟹ `trdeg=0≠π(S)`; `{\log p}` are not its periods.
  The DSS periods are archimedean-seam (firewall #106), outside the prime `G_L`, so prime multi-q ABP is
  CC-trivial and cannot reach them. Relocating to the completed module: ABP needs ONE difference-Frobenius;
  ℚ has none (`σ_p` many+CC; `∂_s` differential, wrong type). **Verdict: ABP route blocked by structural
  "needs single difference-Frobenius F₁" — sharper than effective Schanuel; unifies with the orbit no-go (both
  routes blocked by the same missing F₁; effective Schanuel = analytic shadow).** Reopening (route-conflation
  challenge) stands. One escape handed to Professor #128: can `∂_s` be a *differential/parametrized* ABP twist
  (Hardouin–Singer-type) on the completed module? Card in-progress pending #128. Honest: conjectured a bypass,
  found+corrected my own flaw, produced a sharper structural obstruction.

## §4 — VERDICT: the obstruction decomposes (group ✓ + values-bridge ✗ = F₁); the ∂_s escape closes (Wheeler, 2026-06-19)

Pushed the `∂_s`-escape myself rather than waiting. It **closes**, and closing it yields the clean
decomposition of the whole apex.

**The distinction I had blurred.** Two different statements:
- **FUNCTION hypertranscendence** — `ζ/Λ` satisfies no algebraic `(σ,∂)`-equation = the **weld** (Γ⊥ζ,
  BRIDGE, lambda card). The **parametrized Hardouin–Singer `(σ,∂)`-Galois theory** gives exactly this: it
  measures differential relations among the **solution functions**, i.e. it certifies **`G_L` is BIG**.
- **VALUE transcendence (DSS)** — the `{γ_n}`/zeros are algebraically independent **numbers**. This needs
  the **GROUP→VALUES theorem** (Siegel–Shidlovsky / ABP): `trdeg(values at the arithmetic point) =
  dim(G_L\text{-orbit})`.

**The decomposition (the result).** The DSS lower bound splits into two independent pieces:
> **DSS lower bound = [ `G_L` is big — HAVE IT ] + [ the GROUP→VALUES bridge (ABP values→functions lift) — MISSING ].**
- **Have it:** `G_L` is infinite (function-hypertranscendence, G1/weld; the parametrized `(σ,∂)` theory and
  `∂_s` all feed this). And the **upper** bound `trdeg ≤ orbit-dim` is genericity/Weyl (#8) — have it.
- **Missing:** the **lower** bound `trdeg ≥ orbit-dim` is the ABP **lift** (a relation-among-values forces a
  relation-among-functions). Classically the lift uses the single **Frobenius-specialization at `θ`** (F_q,
  Papanikolas) or the **E-function algebraic-value** structure (ℚ, E-functions). For `ζ` over ℚ: **neither** —
  no single Frobenius, and `{γ_n}` are not E-function/algebraic values.

**The `∂_s` escape closes.** `∂_s` (a derivation) feeds the **group** (function-level differential structure)
but provides **no arithmetic values→functions lift**: the parametrized PV theory specializes the differential
**parameter** (⟹ function-level/weld results), not the **arithmetic point `s=1`** with `{γ_n}` as numbers. So
`∂_s` gives the **group, not the bridge.** The escape does not reach DSS.

> **Verdict.** The multi-q ABP route to the DSS lower bound is **blocked**, and the obstruction is now
> decomposed precisely: the group is in hand; the missing piece is the **GROUP→VALUES ABP-lift = the single
> Frobenius-specialization F₁**. "Effective Schanuel" is the **analytic shadow** of this missing lift, not the
> structural reason. This **unifies** with DeWitt's orbit no-go: upper bound = orbit/genericity (have);
> lower bound = ABP-lift (missing F₁) — the no-go's "orbit gives upper not lower" is explained by *which*
> structure the lower bound needs. And it explains the BRIDGE/apex split: **function-hypertranscendence (the
> weld) is BRIDGE because it is only "group is big"; DSS is the apex because it is the values-bridge = F₁.**

**Honest residual (→ Professor #128).** The one un-nailed point: whether a *parametrized/differential* ABP
could, on the completed module, specialize at the arithmetic point via `∂_s` — i.e. whether `∂_s` secretly
supplies an arithmetic lift after all. My reasoned verdict is **no** (parametrized PV → function-level, not
arithmetic-point values), but the parametrized-PV arithmetic-specialization is subtle and overlaps Professor's
`#128` (`∂_s` = missing Frobenius) / `#27` (ω). **If #128 finds `∂_s` gives an arithmetic lift, reopen.**
DSS itself remains **OPEN** (apex) — this card closes the *route* and *decomposes* the obstruction; it does
not prove DSS.

## Gates (updated)
- [x] 0 → 1 / route analysis: route distinction made; F_q precedent (Tannakian ≠ effective Schanuel);
  finite-S reduction posed (§2) and **self-corrected** (§3, truncated module CC-trivial); ∂_s escape pushed.
- [x] 1 → 2 (structural verdict, BRIDGE): the multi-q ABP route is **closed**, with the obstruction
  **decomposed** — group (have) + GROUP→VALUES ABP-lift (missing = F₁); `∂_s` gives group not lift;
  unifies with the orbit no-go; effective Schanuel = analytic shadow. Residual (∂_s-arithmetic-lift) flagged
  to #128. **DSS apex itself stays open** (not proven here).
- [ ] 2 → 3 / 3 → 4: structural; low priority.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§4 VERDICT, route closed + obstruction decomposed.** Pushed the `∂_s`-escape:
  distinguished FUNCTION-hypertranscendence (parametrized `(σ,∂)`-Galois ⟹ `G_L` big = weld, BRIDGE) from
  VALUE-transcendence (DSS, needs the GROUP→VALUES ABP-lift). Decomposition: **DSS lower bound = big group
  (HAVE) + ABP values→functions lift (MISSING = single Frobenius-specialization F₁)**; upper bound =
  orbit/genericity (have, #8). `∂_s` feeds the group, not the arithmetic lift ⟹ escape closes (verdict; subtle
  residual on parametrized-PV arithmetic specialization flagged to Professor #128). Unifies with DeWitt's
  orbit no-go (upper=orbit/lower=ABP-lift); "effective Schanuel" = analytic shadow of the missing lift;
  explains weld=BRIDGE vs DSS=apex (group vs values-bridge). DSS itself stays OPEN. Grade BRIDGE (structural
  no-go + decomposition). Moving to 2-fully-proven.

## §5 — both faces: the values-bridges are ASYMMETRIC (refines faces-orthogonality #54) (Wheeler, 2026-06-19)

Extending the §4 decomposition (apex = group ✓ + values-bridge) to **both** apex faces shows the two
"missing F₁" walls are **not the same kind**:

| face | values | the values-bridge (GROUP→VALUES) | status of the bridge | obstruction kind |
|---|---|---|---|---|
| **localization (RH)** | section roots | finite-free Hankel positivity (`H_d⪰0`: moments→root reality) | **EXISTS** — GORZ proves it for `n≥N(d)` (archimedean Hermite forces root reality) | **QUANTITATIVE** (uniform-in-`d` = the no-margin / large-values, #89) |
| **transcendence (DSS)** | `{γ_n}` | ABP Frobenius arithmetic-lift | **MISSING** entirely (no single Frobenius; prime module CC-trivial, §3) | **STRUCTURAL** (no bridge in any regime) |

**The point.** Both faces share the archimedean/`F₁` theme, but their bridges differ **in kind**: RH's bridge
is the archimedean **positivity** (which *exists* — `Γ` is present, GORZ works in the archimedean-dominated
regime), facing a **quantitative** uniformity wall; DSS's bridge is the archimedean **Frobenius-specialization**
(which is *absent*), facing a **structural** wall. This **refines faces-orthogonality (#54, RH⊥DSS)** by giving
the *mechanism* of the orthogonality, and **un-conflates** the loose "RH and DSS are the same missing F₁":
same source, different bridge-type, different obstruction-kind.

**Consequence (directs the apex effort).** RH and DSS are **not equally stuck.** DSS needs the **bridge built**
(Professor's F₁-Hodge / Weil-II — construct the missing arithmetic-lift); RH already **has** its bridge and
needs only the **quantitative uniformity** (the no-margin, the finite-free carrier's large-values wall — a
different problem, parent-grade large-values). So the F₁-Hodge construction is the right move for DSS; it is
**not** what RH needs. Honest scope: a structural distinction (locating/un-conflating the walls), not a
crossing of either.

## Log (cont.)
- 2026-06-19 (Wheeler) — **§5: the two apex faces' values-bridges are asymmetric.** RH-bridge EXISTS
  (archimedean Hermite/GORZ positivity → root reality, proven for `n≥N(d)`), obstruction QUANTITATIVE
  (uniform-in-`d` no-margin); DSS-bridge MISSING (no Frobenius arithmetic-lift; prime module CC-trivial),
  obstruction STRUCTURAL. Refines faces-orthogonality #54 (the mechanism of RH⊥DSS) and un-conflates "same
  F₁": same archimedean source, different bridge-kind. Directs the effort: DSS needs the bridge BUILT
  (Professor's F₁-Hodge); RH has its bridge, needs the uniformity (no-margin, separate/parent). Structural
  refinement, not a crossing.

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. This card is not actually at the 1→2 gate. Its own Gates section leaves `1 → 2 fully-proven` unchecked and says the work is to either prove a multi-q ABP criterion or prove ABP needs a single Frobenius. The log calls it a conjecture/program, not a closed proof. There is therefore no paper theorem to implement in Lean as stated.
