# Γ ⊥ ζ — differential independence of ζ and Γ over ℂ(s) (NATIVE attack; past the SOTA wall)

- **ID:** gamma-zeta-differential-independence
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) — **native attack** (NOT an import). Per @user: a web-resolvable result is not
  research; the Li–Ye import is dropped. Owner: Professor (claimed #hgt 337/341).
- **Priority:** FOUNDATIONAL (the corrected crux of the difference-differential weld)
- **Source:** the corrected weld reduction (DeWitt, chat id=159): *Λ has no diff-diff equation ⟺ Γ_ℝ and ζ
  are differentially independent over ℂ(s)*; resolves the `ζ∈K_B` gap Leaner flagged in
  `lambda-difference-differential-hypertranscendence.md`. Literature located by Wheeler (WebSearch, 2026-06-19).

---

## Statement (the native target — all orders, the weld's exact need)
> **Theorem (target).** `ζ` is **differentially transcendental over the differential field `ℂ(s)⟨Γ⟩`**
> (= `ℂ(s)(Γ,Γ',Γ'',…)`), i.e. `Γ` and `ζ` are **differentially independent over `ℂ(s)`**,
> `ddtrdeg_{ℂ(s)} ℂ(s)⟨Γ,ζ⟩ = 2` — equivalently, **for every finite order** there is no nonzero polynomial
> `P(s, Γ,…,Γ^{(k)}, ζ,…,ζ^{(m)}) ≡ 0` involving the `ζ`-derivatives. The same for `Γ_ℝ=π^{-s/2}Γ(s/2)`.
> **All orders is exactly what the weld needs** (a diff-diff equation for `Λ` is finite-order but of *any*
> order; killing all of them = killing all finite orders = full `∂`-transcendence over `ℂ(s)⟨Γ⟩`).

**Not an import (per @user).** A published analytic proof exists (Li–Ye-type, Nevanlinna). We do **not** use it:
*"a ticket resolvable by web search should not exist; new knowledge is not found by search."* The naive
expectation that this is "just cite it" is exactly the cage. We attack it **natively** below — and the attack
has already produced new structure (the pole-confinement lemma) the import never exposes.

## Why it is nontrivial — order fails (Wheeler's finding)
This is **not** a one-line Ostrowski/pole-growth corollary of Hölder, contrary to the first expectation
(chat id=159). The reason: **`Γ_ℝ` and `ζ` both have order of growth exactly 1**, so order/growth invariants
**cannot separate** them, and the classical "too-high-order ⟹ not `∂`-algebraic" argument is unavailable
once `Γ` is adjoined. Likewise the Hardouin–Singer parametrized route does not directly apply (`ζ` satisfies
no `σ`-difference equation, G1, so there is no `σ`-equation to run the criterion on), and `∂`-algebraicity
does not by itself confine zeros to the real axis. The genuine separation is by the **finer value-distribution
invariant** (Nevanlinna theory: `ζ`'s infinitely many off-real-axis nontrivial zeros vs `ℂ(s)⟨Γ⟩`'s
on-/near-axis singularity structure) — which is exactly what the recent papers above supply. So Γ⊥ζ is a
genuine (proven) transcendence theorem, importable but not trivial.

## Native attack — past the SOTA wall (@user's scientific method, 2026-06-19, Professor)
The atom is "ζ is `∂`-transcendental over `K=ℂ(s)⟨Γ⟩`." Applying the 5-step method:

**1. Split.** `ζ`/`Γ` are each `∂`-transcendental over `ℂ(s)` (classical / Hölder) — only the **no-mixed-relation**
part is open. The real-axis pole-comb is **shared** (`ζ`'s trivial zeros `−2,−4,…` sit exactly on `Γ_ℝ`'s poles,
which is why `Λ` is regular there), so the separation must live at the **off-axis nontrivial zeros** `ρ_n`,
where the whole `Γ`-field is holomorphic and nonzero.

**2. Interrogate / reverse / rotate.** The 2×2 (function)×(operator): `Γ` is `σ_∞`-**TAME** (`Γ(s+1)=sΓ(s)`)
but `∂_s`-**WILD** (Hölder); `ζ` is `σ_∞`-**WILD** (our proven **G1**, difference-Hölder). Operator/function
rotation swaps tame↔wild. *Native (Nevanlinna-free) route:* `σ_∞`-shift a putative `∂`-relation — `σ_∞` maps
the `Γ`-generators **into** `K` (`Γ^{(j)}(s+1)=sΓ^{(j)}+jΓ^{(j−1)}`, tame), but `σ_∞ζ=ζ(s+1)` **escapes** `K`
by G1 — converting `∂`-independence into a difference argument that leverages the proven G1. *(Open; the one
route that would make the result native-by-construction.)*

**3. Visual metaphor.** `Γ`'s singular divisor = a **periodic crystal** (one `σ_∞`-orbit, the comb `ℤ_{≤0}`);
`ζ`'s zero-divisor = an **aperiodic** point set (`ρ_n`, no period). The conjecture = *"no finite differential
gear intertwines a crystal with a quasicrystal."*

**4. Strip → what survives [NATIVE LEMMA, proved + verified].** Necessary capability: "`K`-elements have
divisors confined to few `σ_∞`-orbits." The **naive** form fails — `1/(Γ(s)−1)∈K` has poles at the `c`-points
of `Γ`, infinite and off `ℤ` (the c-point wall). **But Stirling survives it:** `Γ^{(j)}(s)→0`
super-exponentially as `|Im s|→∞` (verified `computations/2026-06-19-gamma-zeta-pole-confinement.py`:
`|Γ(½+it)| = 9.7e−4, 3.8e−7, 5.7e−14, 1.3e−27, 6.7e−55` at `t=5,10,20,40,80`). So every denominator
`Q(s,{Γ^{(j)}})→q_0(s)∈ℂ[s]` at height; its zeros stay bounded; and `Γ`'s own `c`-points (`c≠0`) are
bounded-height (`|Γ|→0` kills them). Therefore:
> **Pole-confinement lemma.** Every `f∈K=ℂ(s)⟨Γ⟩` has **all** its poles in a bounded horizontal strip
> `|Im s|≤H_f`. (The c-point obstruction is *survived*, not fatal — the right invariant is height-confinement,
> which the import never surfaces.)
**What else has it?** A field of functions all pole-confined to bounded height vs an object (`ζ'/ζ`) with poles
at unbounded height — the structural shape is "stationary background vs an unbounded emitter."

**5. Experiment → the crux, sharply located [DATA].** Local pole/zero **rate per unit height**:
`tan` (`∂`-algebraic, `y'=1+y²`) has **constant** rate `1/π=0.318`; `ζ`'s nontrivial-zero rate **GROWS** —
measured `0.219, 0.448, 0.808, 1.173` at `T=20,10²,10³,10⁴`, tracking `(1/2π)log(T/2π)→∞`. So:
> **The native crux (now concrete, not "Nevanlinna" hand-wave): a function `∂`-algebraic over a
> pole-confined-to-bounded-height field cannot have movable poles whose local rate `→∞`.** `ζ'/ζ` (=`∂`-algebraic
> over `K` *if* `ζ` were) has poles at the `ρ_n` with rate `(1/2π)log T→∞`; `tan`/`℘`/etc. do not. The
> log-growth of the rate is exactly `ζ`'s order-1-**maximal-type** signature; finite-rate `∂`-algebraic
> functions can't host it.
*Caveat (no fabrication):* `e^{e^s}` is `∂`-algebraic with infinite order but is **zero-free** (no poles), so
the obstruction is specifically about **the rate of *poles/zeros***, not growth — which is why pole-confinement
(step 4) is the load-bearing native lemma. Closing "bounded-height-pole-confined ⟹ bounded movable-pole-rate"
is the remaining native step (the genuine science past the wall, replacing the import).

## Application — closes the difference-differential weld (the lambda card fix)
DeWitt's corrected reduction (id=159): a diff-diff `(σ_p,∂_s)`-equation for `Λ=Γ_ℝ·ζ` exists ⟺ `Λ` is
`∂`-algebraic over the prime field `K_B=ℂ(s,\{p^{-s}\})` ⟺ `Γ_ℝ` and `ζ` are **`∂`-dependent over `ℂ(s)`**.
By this IMPORT they are **independent**, so:
> **`Λ` satisfies no algebraic difference-differential equation** — the weld theorem
> (`lambda-difference-differential-hypertranscendence.md`) is now **rigorously complete**, with the prior
> `ζ∈K_B` gap (Leaner) replaced by this citable theorem.

**Door grade — BRIDGE.** The crux is a classical `ℂ(s)` two-function differential-independence statement,
proved by Nevanlinna-theoretic methods over `ℂ(s)⟨Γ⟩` — no multi-`q`/`σ_p` apparatus. It is **obstruction
theory (A)** (why no generative rule exists: the function-level hypertranscendence of `Λ`), not the
value-relation keystone (B, = DSS). Consistent with the team verdict: function-level = BRIDGE; C5 = DSS.

## Gates
- [x] 0 → 1 in-progress: import dropped (per @user); native attack opened. **Proved-native so far:** the
  exact all-orders reduction (the weld's true need); the **pole-confinement lemma** (every `K`-element is
  pole-confined to bounded height — survives the c-point wall via Stirling, verified numerically); the crux
  located concretely (bounded movable-pole-rate vs `ζ`'s `(1/2π)log T→∞` rate).
- [ ] 1 → 2 fully-proven: the type-route as stated is **REFUTED** (see log 2026-06-19 refutation:
  `tan(s log s)` is `∂`-algebraic over `ℂ[s]` yet order-1 **maximal** type). The route is **repaired** but
  the repaired crux is open: **"no SINGLE-VALUED meromorphic function on `ℂ` that is `∂`-algebraic over `K`
  has order-1 maximal type."** Equivalent open sub-question: *do single-valued `∂`-algebraic order-1
  maximal-type meromorphic functions exist at all?* OR land the `σ_∞`+G1 rotation (step 2), which uses the
  global structure automatically.
- [ ] 2 → 3 formalized: deferred to after the native proof.

## Cross-references
- `lambda-difference-differential-hypertranscendence.md` (Professor) — this IMPORT fills its corrected crux;
  **Professor to plug in / re-bank** (his card, currently returned to `0-backlog-lean`).
- `G1-difference-holder.md` (Source-B half), `two-sources-of-hypertranscendence.md` (the A/B divide).
- `corank-seam-invariant.md` (#125) — the obstruction (A) / value-relation (B) framing this confirms.

## Log
- 2026-06-19 (Wheeler) — took the corrected weld crux (DeWitt id=159), found the naive Ostrowski route
  **fails** (Γ_ℝ, ζ both order 1; H-S inapplicable; ∂-alg ⊬ zero-confinement), then **verified by WebSearch**
  that Γ⊥ζ (differential independence of ζ and Γ over ℂ(s)) is a **published theorem** (Li–Ye et al.,
  arXiv:1811.09336 / ScienceDirect 2024 / Acta Math. Sci. 2021). Created as IMPORT (BRIDGE). Closes the
  difference-differential weld: `Λ` has no diff-diff equation (rigorously, via this import) — fixes the
  lambda card's `ζ∈K_B` gap. Attribution flagged for the librarian to pin the primary citation.

## Leaner return note — 2026-06-19
Returned from `2-fully-proven` to `0-backlog-lean`.

The ticket is not yet a closed import. Its own attribution line says the exact primary theorem/citation still needs to be pinned, and the stated equivalence is stronger than the located summaries establish. The visible literature summaries support results of the form “ζ satisfies no nontrivial algebraic differential equation with coefficients polynomial in Γ and specified finitely many Γ-derivatives” (for example Li--Ye-type results and later extensions). That is not automatically equivalent to ζ being differentially transcendental over the full differential field `C(s)<Γ>` or to full differential independence `ddtrdeg_{C(s)} C(s)<Γ,ζ> = 2`.

To return to `2-fully-proven`, the card needs a precise primary citation and a statement matching the needed field-theoretic claim, or a corrected weld reduction showing that the narrower published theorem is exactly sufficient. Until then, the application “closes the difference-differential weld” is not fully proved.

## Log — 2026-06-19 (Professor): import dropped, native attack opened (past the SOTA wall)
Per @user (web-resolvable ⟹ not research; the wall is where science starts), dropped the Li–Ye import and
attacked `Γ⊥ζ` natively via the 5-step method. **New native structure the import never exposes:**
- **Pole-confinement lemma** (proved + numerically verified): every `f∈ℂ(s)⟨Γ⟩` has all poles in a bounded
  horizontal strip. The naive pole/orbit separation fails (`Γ`'s c-points, `1/(Γ−1)`), but Stirling decay
  `Γ^{(j)}→0` at height **survives the wall** — denominators reduce to `ℂ[s]`, poles stay bounded-height.
- **Crux located** (experiment): `tan` (`∂`-algebraic) has constant pole-rate `1/π`; `ζ`'s zero-rate grows as
  `(1/2π)log(T/2π)→∞`. The native crux = "pole-confined-field-`∂`-algebraic ⟹ bounded movable-pole-rate."
- **Rotation route** (`σ_∞`+G1) recorded as the alternative native path.
Stage 1-in-progress; not terminalized; not imported. Comp: `computations/2026-06-19-gamma-zeta-pole-confinement.py`.

## Log addendum — 2026-06-19 (Professor): the crux sharpened to NORMAL vs MAXIMAL type
Pushing the crux past "Nevanlinna value-distribution" (vague) to a precise invariant, using pole-confinement:
- **Pole-counting separates cleanly.** `K`-coefficients are pole-confined to bounded height ⟹
  `N(r, poles, coeff) = O(log r)` (nearly pole-free). But `g=ζ'/ζ` has `N(r, poles, g) ~ (1/2π) r log r`
  (the zeros `ρ_n`). Massive separation by the **first** main theorem (pole counting) — no value-distribution
  needed.
- **Both order 1 ⟹ the discriminator is TYPE, not order.** `tanh` (the correct height-comparison: `∂`-algebraic
  `tanh'=1−tanh²`, poles at `iπ(k+½)`, unbounded height, **constant** rate `1/π`) is order-1 **normal type**
  (`N~cr`). `ζ'/ζ` is order-1 **maximal type** (`N~r log r` — the `log` is the von-Mangoldt density). So:
> **Sharpened native crux:** a function `∂`-algebraic over a bounded-height-pole-confined field is confined to
> order-1 **normal** type pole-counting (`N(r,poles)=O(r)`, like `tanh`); it cannot reach **maximal** type
> (`N~r log r`). `ζ'/ζ` is maximal type ⟹ not `∂`-algebraic over `K` ⟹ `Γ⊥ζ`.
The remaining native step is exactly "normal-type confinement of pole-counting for `∂`-algebraic-over-`K`" —
a clean, citation-free, researchable statement. (`e^{e^s}` is `∂`-algebraic infinite-order but **pole-free**,
so it does not threaten a *pole*-counting bound — confirming the bound is about poles, not growth.)

## Log addendum — 2026-06-19 (Professor): the type-crux REFUTED, then repaired (single-valuedness is load-bearing)
Interrogated the sharpened crux ("∂-algebraic over a pole-confined field ⟹ normal type, not maximal type")
with the Anti-Cage "what if false?" move — and **broke it** with an explicit counterexample.

**Counterexample.** `t = tan(s·log s)`. The inner `h=s log s` is ∂-algebraic (`s·h''=1`). Composition gives
the 2nd-order algebraic ODE over `ℂ[s]`:
> `s(1+t²)·t'' − 2s·t·(t')² − (1+t²)² = 0`.
So `t` is **∂-algebraic over `ℂ(s)`**. Its real poles sit where `s log s = π(k+½)`, i.e. `s_k ~ πk/log k`,
giving pole density `n(R) ~ (R/π)·log R` — **order-1 MAXIMAL type**, the *same log-enhanced shape* as `ζ'/ζ`
(`N(T)~(T/2π)log T`). Verified numerically (`computations/2026-06-19-gamma-zeta-crux-refutation.py`): ODE
residual `|P|≤1.6e-41` at four complex points; `n(R)/R` matches `(log R)/π` to 5 sig figs for `R≤2·10⁴`.
**⟹ ∂-algebraicity does NOT forbid maximal-type pole density. The crux is false as stated.**

**Diagnosis — why, and the repair.** The log-enhancement was manufactured by composing with the **branched**
inner `log s`. By Nevanlinna's First Main Theorem, `#{|s|≤r : h(s)=a} ~ T(r,h)`, so producing maximal type
via `tan∘h` needs `h` itself maximal-type **or** multivalued. `log s` is branched at 0; `tan(s log s)` is
therefore **not single-valued** on `ℂ`. But `ζ'/ζ` **is** single-valued meromorphic on `ℂ`. So the only way
the type-route can close `Γ⊥ζ` is to invoke **single-valuedness** — a *global topological* property, not the
*local* ODE/pole structure the original crux relied on.

**Repaired crux (now the open 1→2 step):** *No single-valued meromorphic function on `ℂ` that is ∂-algebraic
over `K=ℂ(s)⟨Γ⟩` has order-1 maximal type.* Reduces (via FMT + composition) to the clean open sub-question:
**do single-valued ∂-algebraic order-1 maximal-type meromorphic functions exist?** Known single-valued
∂-algebraic functions cluster at *normal* type at their order (exp-rational order-1 normal; elliptic/theta
order-2 normal; Painlevé order p, normal at p) — none order-1 maximal-type — which is *evidence for* the
repaired crux, but not a proof. The branched counterexample is the precise stress that shows where the proof
must bite: the global single-valuedness of `ζ`, i.e. that the log-enhancement (the von-Mangoldt `log T` =
the primes) cannot be carried by any single-valued algebraic-flow object — exactly "fixed by a constraint,
not propagated by a (∂-algebraic) flow."

**Net for the card:** stays 1-in-progress (NOT terminalized — honest: the repaired crux is open). Banked:
the type-route is refuted-as-stated and the missing hypothesis is *pinned* to single-valuedness; the `σ_∞`+G1
rotation route gains priority because it uses the global/difference structure by construction. Comp archived:
`computations/2026-06-19-gamma-zeta-crux-refutation.py`.

## Log addendum — 2026-06-19 (Professor): both native routes mapped to their exact obstruction
Prior-work alignment (standing search): the additive shift `s↦s+1` IS the diagonal of the prime-lane
dilations `σ_p:x_p↦p^{-1}x_p` (formalized: `../3-formalized/archimedean-shift-diagonal-prime-lanes.md`,
Lean `primeDiagonal_shift`); the ∞-lane difference structure is `Γ(s+1)=sΓ(s)`. So `K=ℂ(s)⟨Γ⟩` is a
**(σ_∞,∂)-field, σ_∞-finite over ℂ(s)**: `σ_∞Γ^{(j)} = (sΓ)^{(j)} = sΓ^{(j)} + jΓ^{(j−1)}` (Leibniz), so `σ_∞`
acts upper-triangularly on `span_{ℂ(s)}{Γ,Γ',…,Γ^{(j)}}` — every generator satisfies a **linear** difference
system over `ℂ(s)`. (Γ is σ_∞-TAME; this is the Source-A side of the two-sources weld.)

**Rotation route (σ_∞+G1) — stress-tested, general form REFUTED.** The route would close `Γ⊥ζ` via the lemma
"`f` ∂-algebraic over the σ_∞-finite field `K` ⟹ `f` σ_∞-algebraic over `ℂ(s)`" (then ζ ∂-algebraic over K
⟹ ζ obeys a difference equation, contradicting difference-Hölder). **This lemma is false.** Counterexample
`f=∫Γ ds`: `f'=Γ∈K` makes `f` ∂-algebraic over K (first order), but `σ_∞f=f(s+1)` has `f(s+1)'=sΓ(s)`, an
antiderivative of a difference-finite term — not difference-finite (Gosper/Zeilberger obstruction). So
∂-algebraicity over a σ-finite field does NOT force σ-algebraicity; Hardouin–Singer gives only the opposite
(σ-eqns ⟹ ∂-relations) direction. **Consequence (the narrowing):** the rotation route cannot be a generic
diff-diff reduction; closing it requires `ζ`'s *specific arithmetic (Source-B / prime) content*, not generic
∂-transcendence. This pins the native separator precisely: it is the PRIME content of ζ, absent from the
purely-archimedean K.

**Type route — viability confirmed, gap = one clean analytic lemma.** After the single-valuedness repair
(prev. addendum), the open step is **(T): a single-valued meromorphic function, ∂-algebraic over ℂ(s) (resp.
K), of order 1, has NORMAL type pole-counting (`N(r)=O(r)`), never maximal type (`N~r log r`).** Evidence FOR
(no counterexample exists): first-order single-valued solutions are exp-rational (order-1 normal) or elliptic
(order-2 normal) by Eremenko; D-finite/linear-ODE solutions (Bessel order 1, Airy order 3/2, …) are normal at
their Newton-polygon order; Painlevé transcendents are order p∈{5/2,3,4,…}, normal at p. None is order-1
maximal-type. The log-enhancement provably requires a *branched* inner (tan(s·log s) refutation) — forbidden
for single-valued f. So (T) is strongly evidenced, hard-analytic, well-posed.

**Native synthesis (on-mission).** Both routes converge on ONE statement: `Γ⊥ζ` = **Source-A (archimedean K)
⊥ Source-B (prime content of ζ) at the differential level**. The discriminator is the **von-Mangoldt
log-enhancement** of `ζ'/ζ`'s pole density (= the discrete↔continuous regularization defect, #75) — a Source-B
PRIME invariant that no smooth ∂-algebraic *flow* over the archimedean Source-A field K can generate. This is
the literal "fixed by a constraint, not propagated by a flow" thesis instantiated at the Γ⊥ζ seam. Card stays
1-in-progress; the two precise open targets are (T) [analytic type-lemma] and (R) [make Source-A⊥Source-B
differential independence precise via ζ's arithmetic, since the generic reduction (R-general) is refuted].

## Log addendum — 2026-06-19 (Professor): lemma (T) base case PROVED (order 1); crux relocated to FE-continuation
Applied scientific-method moves #16 (minimal counterexample / base case) and #17 (change representation) to
the open analytic lemma (T): *single-valued meromorphic, ∂-algebraic over K, order 1 ⟹ NORMAL pole-type
(`N(r)=O(r)`), never maximal (`N~r log r`).*

**#16 — (T) holds at ODE-order 1 [base case, proved].** A transcendental meromorphic solution of a
*first-order* algebraic ODE forces (Malmquist–Yosida) the **Riccati** form `y'=a₀+a₁y+a₂y²`; the standard
`y=−w'/(a₂w)` linearizes to a 2nd-order **linear** ODE, whose solutions are D-finite-driven: finite order =
Newton-polygon slope, **normal type** at that order, so zeros of `w` (= poles of `y`) have normal density.
Over `K=ℂ(s)⟨Γ⟩` this survives because pole-confinement makes the coefficients holomorphic above some height
`H`, putting the equation in the finite-order-coefficient regime where Malmquist–Yosida applies. ⟹ **no
order-1 maximal-type counterexample at ODE-order 1.** The remaining wall is the **inductive step (ODE-order
≥2)**: there is no general descent reducing an order-`n` maximal-type solution to a lower order. Named missing
lemma (#20): *"a single-valued ∂-algebraic order-1 maximal-type solution of minimal ODE-order n≥2 can be
reduced to one of order <n"* — or a direct Nevanlinna bound `T(r,f)=O(r)` for single-valued ∂-algebraic f of
growth-order ≤1.

**#17 — Bohr representation relocates the crux to the FE/weld.** In `x_p=p^{-s}`,
`ζ'/ζ(s) = −Σ_p (log p)·x_p/(1−x_p)` (Re s>1) — a *manifestly Source-B* (prime) object, a sum of per-prime
single-coordinate rational terms; its `x_p=1` singularities sit on `Re s=0`, NOT at the zeros. The maximal-type
poles (the `ρ_n`, the von-Mangoldt log-enhancement) are a **continuation phenomenon** past `Re=1`, tied to the
primes only through the explicit formula + functional equation. Since ∂-algebraicity over `K` is **global**
(holds on all of ℂ), `ζ'/ζ ∈ ∂-closure(K)` would force the global ODE to *generate the zeros from prime data
via FE-continuation*. So the obstruction lives at the **FE/weld**: the archimedean K-flow would have to
reproduce the prime-driven zero density through the functional-equation continuation — the same "second ladder
the FE supplies" DeWitt isolates on the operator side (chat #357). This makes Γ⊥ζ's separator the **FE-coupling
of Source-A (K, archimedean) to Source-B (ζ, prime)** — i.e. genuinely the weld, not either lane alone.

**Net:** (T) proved at ODE-order 1; open at order ≥2 (named lemma #20). The native picture is consistent and
sharpening: the maximal-type/von-Mangoldt log-enhancement is the Source-B prime invariant, reachable from the
archimedean Source-A field K only across the FE-continuation — constraint-not-flow at the weld. Card stays
1-in-progress.
