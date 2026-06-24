# The non-roleplay items — what actually survives, decomposed, and seen through the seven lenses

> **Register discipline.** This document is a *map*, not a proof. Anything stated as fact is marked
> `[PROVED]` / `[VERIFIED]` and traces to a lemma or computation; everything generative is marked
> `[CONJECTURE]` / `[REFRAME]` (a reformulation that is logically equivalent or heuristic, not a new
> theorem). The decompositions and lens-readings are *search-register* work: their job is to break one
> hard problem into named sub-problems and surface non-trivial identities, not to claim progress across
> the wall.

## 0. What "non-roleplay" means here, and the filter that produced this list

Three filters were applied to the whole programme:

1. **The SOTA sweep (§10).** Almost the entire apparatus is classical, reassembled in the seam
   coordinate: the moments `T_k` are Voros secondary-zeta values; `s_d` is the inverse Christoffel
   function (Szegő); the Uvarov kernel (proof11) is Uvarov 1969; the `N₁→N₀` rank-one transition
   (proof10) is Derkach–Hassi–de Snoo 2002; `Q_0≥0⟺RH` is the Weil/Li/Csordas–Varga moment-positivity
   family; the exterior-Christoffel rate is the non-regular regime of Stahl–Totik. All `reduce-to-known`.
2. **The roleplay audits (proof9/12/13 §-audits + our `[conditional]` flags).** proof7–11 are *algebraic
   consequences of assumed objects*, not the constructed source object; proof12 proves only the *easy*
   half `Q_0≥0 ⟹ RH` `[PROVED — classical moment theory]`; proof13 = proof9 re-derived.
3. **The orthogonality lens (lens 5).** `ω=0 ⇏ RH` (Davenport–Heilbronn): the functional equation /
   realization axis is RH-blind. Anything that factors through it is not the RH content.

**What survives all three** is a very short list. Everything else is scaffolding, coordinates, or a
re-derivation with a citation. The survivors are below.

---

## 1. The items: what they are, what they are good for, why they are hard

### NR-1 — The positivity transfer (the apex; RH-bearing) `[OPEN CORE]`

**What.** Derive `Q_0[p] = Σ_{ij} c_i c_j T_{i+j+1} ≥ 0 ∀p, ∀d` — equivalently the scalar Weyl gap
`s_d = a_* + 1/m_d = 1/K_{ν'}(y_*,y_*) > 0 ∀d` — **from source data** (the completion `Λ=Γ·ζ`, the
explicit formula tying `{T_k}` to `{log p}`, and the canonical Γ/pole/FE boundary), **without reading
the zeros**. Reading the zeros and checking they are real *is* RH, so a zero-fed argument is circular.

**Good for.** This is RH. By proof12 `[PROVED]`, `Q_0≥0 ∀p ⟹ RH` for the actual divisor; NR-1 is the
converse — the source-built direction — which is the entire open content of the bridge.

**Why hard.** (i) RH-equivalent, hence exactly as hard as RH. (ii) *No zero-feeding* — comp73
`[VERIFIED]` showed bare prime truncation diverges (pole-dominated `~√X·polylog`); the residual sign is
invisible without analytic pole subtraction, so the source object must be the completed `Ξ`, not a sum.
(iii) *No-margin* — comp74 `[VERIFIED]`: `s_d→0⁺`, depth pinned at `−1/a_*`, width curvature-controlled;
the statement is **sign-exact at zero margin**, so no soft/`ε`-inequality survives. (iv) *Off the moment
curve* — comp72 `[VERIFIED]`: an off-line defect raises the Pick `κ` to 2 in a polynomial-eigenvector
direction off the real moment curve, so real-axis kernel positivity alone is insufficient. (v) The
documented **Conrey–Li no-go** (arXiv:math/9812166): de Branges positivity *fails* for `ξ`, so naive
positivity packagings are known to break.

### NR-2 — The fake-family separation (the discriminating content of NR-1) `[OPEN CORE]`

**What.** Prove the *mechanism* of NR-1. **Refined to NR-2′ (see §6, comp81): the separator is the integer `κ₋`,
not the scalar `s_d`** — `Λ(n)≥0` (Euler-product positivity) `⟹ κ₋(H^-)=1` (exactly one negative square,
repairable by the single Γ-atom), while a fake gives `κ₋≥2`. The earlier framing "Euler keeps `s_d>0 ∀d` while a
fake crosses `s_d=0`" is the *height-limited rank-one shadow*: DH (a real off-line zero) does cross `s_d=0` at
`d*=62` (comp58), but a global sign-fake has `κ₋=2` with `s_d>0` (comp81), so the scalar is not the criterion.
Concretely: the Euler-product log-coefficient positivity (`ζ`: `c_n=Λ(n)≥0` for all `n`; DH: 59 negative of 62,
06-experimental-findings) is the input that forces `κ₋(H^-)=1`.

**Good for.** This is the *named source gate* the corpus demands — a proof that separates fakes at a
structural gate (`s_d=0`), not a restatement of an RH-equivalent positivity. It is the difference between
"RH is positivity" (known, vacuous) and "*this* positivity, and here is *why* the Euler product supplies
it." It is the only place the sweep flagged as possibly non-reducing (§10.B2: a *positivity*-framed
separator was not found in the literature; the standard separator is multiplicativity).

**Why hard.** The transfer from the prime side (`Λ(n)≥0`) to the zero side (`s_d>0`) goes through the
explicit formula, which is pole-dominated and distributional (comp73); and comp76 `[VERIFIED]` showed
`s_d=0` is a *global* condition, not a single off-line atom — so the separation must use the cumulative
Euler structure, a height-limited statement.

### NR-3 — A positivity-preserving Jensen/Pólya identification of `s_d` `[CONJECTURE — structural target]`

**What.** comp80 `[PROVED, classical]` writes `s_d = −det(H^0_d)/det(B_d)` (a Christoffel/Hankel-determinant
ratio) — but this identity is **not positivity-preserving** (it does not make the sign of `s_d` manifest;
it is true regardless of RH). NR-3 asks: is there a *different* identification of `s_d` with a Jensen /
Pólya / Laguerre–Pólya object in which positivity is *manifest* (e.g. `s_d` = a squared norm, a Gram
determinant of a definite form, an intersection number)?

**Good for.** If found, it would convert NR-1 from "prove a sign" into "exhibit a manifestly-positive
representation," the standard way hard positivity statements actually get proved.

**Why hard.** comp80 shows the *obvious* determinant route is sign-blind; the Connes–Consani prolate
operator (`scaling² + OP-grading`, with a positive/Sonin split) is the nearest object where such a
manifestly-positive representation lives — so this item is really "land our `s_d` inside the prolate /
archimedean-polarization positivity," which is open.

### NR-orth — The value/transcendence apex (Schanuel-for-prime-logs) `[OPEN — orthogonal, famous]`

**What.** Algebraic independence of `{log p}` (Schanuel-for-prime-logs), and its conjectural link to the
arithmetic of `{γ_n}` (Conjecture A). **Listed for completeness and explicitly set aside:** it is the
*value/realization* axis, orthogonal to RH (lens 5: `ω=0⇏RH`), and it reduces to a famous open problem
(Schanuel) — not a cell this programme is positioned to crack. NR-1/2/3 are the RH-bearing work.

---

## 2. Decomposition into a conjunction of smaller problems (iterated)

The question "is `s_d>0 ∀d` source-built?" decomposes. Each iteration refines the previous conjuncts.

### Iteration I — the explicit-formula split `[PROVED algebra + conjectural conjuncts]`

`H^0_d = H^-_d + a_* v_* v_*^T` with `H^-_d = M^{(≥2)}_{triv} + R^P` (archimedean trivial-zero bulk +
prime residual). `[PROVED — comp57/proof10 setup]`. Then

> **NR-1  ⟺  (I-a) ∧ (I-b)**, where
> **I-a `[the N₁ carrier]`** `inertia(H^-_d)=(d,1)` from source data (one negative square, not zero-fed);
> **I-b `[the scalar gap]`** given I-a, `s_d = a_*+1/m_d > 0 ∀d`.

Status: I-a is proved *conditionally* (proof10, on the 1-dim seam-quotient hypothesis); the *source* form
is open. I-b is the apex sign.

### Iteration II — split the gap into budget vs demand `[REFRAME — identity]`

Define the **critical archimedean mass** `a_c(d) := −1/m_d`. Then `s_d = a_* − a_c(d)`, and

> **I-b  ⟺  (II) the Γ budget beats the prime demand at every degree:  `a_* > a_c(d) ∀d`,**

where `a_* = (2.5)^{−2} = 0.16` is the **closed Γ-side datum** (the `j=1` trivial-zero atom, source-built,
no zeros) and `a_c(d) = −1/m_d = −1/(v_*^T(H^-_d)^{−1}v_*)` is the **prime-bulk inverse-Christoffel demand**.
comp48 `[VERIFIED]`: `a_c(−0.16)=0.16` exactly at the boundary point, the deficit `= a_*·margin_d`. So the
apex is a **competition between a fixed archimedean budget and a degree-growing prime demand**.

### Iteration III — separate the rate from the sign `[PROVED rate is generic]`

`a_c(d) → a_*^-` (so `s_d→0⁺`); the *rate* of approach is `s_d ~ ∏_{j≤d} γ_j^{−α}`,
`α≈4+[4(1−ln2)+2ln|y_*|]/L̄_d`. **§10.B1 `[RESOLVED]`: the rate is generic hard-edge geometry (non-regular
Stahl–Totik), RH-empty.** Therefore

> **(II) splits as (III-rate) ∧ (III-sign), and only (III-sign) carries RH:**
> **III-rate `[REDUCES-TO-KNOWN]`** the magnitude `a_*−a_c(d) ~ ∏γ_j^{−α}` — derivable, no content.
> **III-sign `[OPEN — = the apex]`** the *sign* `a_*−a_c(d) > 0` at every finite `d` — sign-exact, no margin.

### Iteration IV — route the sign through the Euler product `[CONJECTURE — the transfer]`

The prime demand `a_c(d)` is built from `R^P_k = (ζ'/ζ)^{(2k−1)}(½) = −Σ_n Λ(n)(\log n)^{2k−1}n^{−1/2}`
(distributional, comp64 `[VERIFIED]`). The Euler product is exactly `Λ(n)≥0`. So:

> **III-sign  ⟸  (IV) Euler-product positivity transfer `[CONJECTURE C]`:** the source positivity
> `Λ(n)≥0` (multiplicativity), pushed through the completed explicit formula, keeps the prime demand
> `a_c(d)` below the Γ budget `a_*` at every degree; and a fake with negative log-coefficients
> (Davenport–Heilbronn) eventually violates it (`d*=62`).

This is **NR-2**, now located precisely: it is the implication `{Λ(n)≥0} ⟹ {a_c(d)<a_* ∀d}`, with the
completed-`Ξ` (not bare-prime) pole subtraction baked in.

### The full conjunction (collecting the iterations)

> **NR-1 (RH)  ⟺  I-a `[N₁ carrier, source]`  ∧  III-sign `[a_*−a_c(d)>0 ∀d]`,**
> and **III-sign ⟸ IV `[Euler-product positivity transfer]` = NR-2.**
> III-rate and the determinant identity (comp80) are *reduces-to-known* and carry none of it; NR-3 asks
> whether a manifestly-positive representation of `a_*−a_c(d)` exists (which would prove III-sign directly).

So the irreducible kernel is the pair **{I-a from source, IV}** — "the bulk has exactly one negative
square, sourced without zeros, and the Euler product's coefficient positivity keeps the Γ-budget ahead of
the prime-demand at every degree." Both are open; everything else in the tower is closed algebra or
generic asymptotics.

---

## 3. The seven lenses on the apex (per-lens reframing and non-trivial identities)

Each lens projects NR-1 (`s_d>0`, i.e. `a_* > a_c(d)`) differently. The aim is non-trivial reformulations
and identities, all `[REFRAME]` unless tagged.

### Lens 1 — Constraint, not flow
The object is fixed by the FE constraint `ι:s↦1−s`, with `Fix(ι)={1/2}` and seam `Fix(ι∘conj)`, not propagated by a flow. **Reading:**
`s_d>0` is a **fixed-point** property of the constraint's archimedean polarization, not the limit of a
flow. **Non-trivial consequence:** this *explains the no-margin* (`s_d→0⁺`, comp74): there is no flow whose
limit is a positive number to bound below — the finite `s_d` are shadows of a constraint at the fixed
locus, so they may shrink to `0` while the **sign is held by the constraint, not by a gap**. The apex must
therefore be proved as a sign-exact fixed-point statement (a definiteness of `ι` on the archimedean-
polarized space, `κ₋=0`), never as `s_d ≥ ε>0`.

### Lens 2 — Transport, not amplitude
`ω = d log ξ = (A+P)ds`, `A=∂_s\log Γ_∞`, `P=ζ'/ζ`; RH-content in **holonomy**, not curvature
(`[∂_s,M_p]=−\log p` is universal, RH-blind). **Identity `[REFRAME]`:** `1/s_d = K_{ν'}(y_*,y_*) =
Σ_j |p_j(y_*)|²` is the **squared transport-norm of the boundary-evaluation vector** at the `j=1` trivial
zero `y_*`. So `s_d>0` ⟺ that boundary evaluation has finite, non-degenerate transport norm. **Reading:**
the apex is the **non-degeneracy of the holonomy of `ω` at the Γ-boundary point** — a connection
statement, with the universal curvature divided out.

### Lens 3 — The weld and the seam
Two sources (archimedean Γ, prime base `{σ_p}`), welded by the FE at `Re=½`. **Identity (Iteration II):**
`s_d = a_* − a_c(d)` with `a_*` the **archimedean (Γ) budget** and `a_c(d)` the **prime-bulk demand** —
the gap *is* the weld balance. **Reading:** `s_d>0` ⟺ the archimedean atom dominates the prime defect at
the boundary, at every degree. **Non-trivial overlap:** this is precisely the **Connes–Consani semilocal
weld** (archimedean + finite places) in finite-section form; the action item is to match `a_*−a_c(d)`
against their prolate positive/Sonin split (§10.A12) — if our finite weld is the compression of their
operator, the apex inherits their archimedean positivity machinery.

### Lens 4 — Faithful index `κ₋=0` (the RH lens)
RH `= κ₋=0`, an **integer** index. **Identity `[REFRAME]`:** `H^-_d` has `κ₋=1` (the `N₁` carrier); the
rank-one Γ-atom moves `κ₋: 1→0` iff `s_d>0` (Sherman–Morrison inertia). comp72 `[VERIFIED]`: each resolved
off-line pair adds `+2` to the all-order `κ₋`, so faithful `κ₋ = 2·#{off-line pairs}` and RH `⟺ κ₋=0`.
**Reading:** the scalar `s_d` is the **last continuous shadow of an integer**; its sign is governed by a
`ℤ`-valued index, which is *why* measured/soft positivity (density, variance, trace) cannot decide it
(blind to density-zero off-line dust). The apex must be an inertia/index argument, not an estimate.

### Lens 5 — Two orthogonal axes (`ω=0 ⇏ RH`)
The realization axis (FE, `ω=0`) is RH-blind (DH has it, fails RH); RH lives on the positivity axis.
**Reading:** `s_d>0` is *purely* positivity-axis — the FE is not enough, so the proof **must consume the
Euler product** (the ingredient DH lacks). **Identity (Iteration IV) `[CONJECTURE]`:** the Euler-product
log-coefficient positivity `Λ(n)≥0` is the missing input; the separation `s_d^{Euler}>0` vs
`s_d^{DH}` crossing is the fake-family theorem (NR-2). This lens **forbids** any apex proof that would also
apply to DH — a built-in correctness check on candidate arguments.

### Lens 6 — Affine confinement (the passport)
Affine-*volume* observables factor through `Π(S)=(|S|,Σ_{m∈S}m)` and are RH-blind. **Consistency check
`[REFRAME]`:** `1/s_d = K_{ν'}(y_*,y_*) = Σ_j|p_j(y_*)|²` is a **boundary-evaluation (point) functional** —
it reads the value at one exterior point `y_*`, not an affine volume — so it does **not** factor through
the passport, hence it is *eligible* to be RH-bearing (it passes lens-6's faithfulness filter). **Reading:**
the apex content lives in the transverse seam `[𝔾_a,𝔾_m]`; `s_d` is admissible precisely because it is a
**localization test**, not a volume test. (This is a guardrail, not a route: it certifies `s_d` is the
right *kind* of object.)

### Lens 7 — The missing single Frobenius (value/arithmetic)
`corank ∞` over `ℚ` (infinitely many independent prime "Frobenii") vs `1` over `𝔽_q`. **Reading:** over
`𝔽_q`, unitarity of the reflected critical-line constraint gives RH-over-`𝔽_q` automatically from one Frobenius
(Deligne, Weil II); over
`ℚ` the missing single Frobenius is exactly why the positivity is *not* automatic. **Identity (aspiration)
`[CONJECTURE]`:** `s_d>0` is the **"missing archimedean Frobenius positivity"** — what a Frobenius over
`𝔽₁` would hand us for free. This is the Connes–Consani arithmetic-site / Riemann–Roch program (§10.A12);
the value axis (Schanuel, NR-orth) is the obstruction to importing it. **Reading:** NR-1 is, in this lens,
the request to **supply by archimedean polarization what the single Frobenius supplies over `𝔽_q`.**

---

## 4. What this map is and is not

- **Is:** a decomposition of the one RH-bearing open cell (NR-1) into a conjunction `{I-a from source} ∧
  {III-sign}`, with `III-sign ⟸ NR-2` (the Euler-product transfer), plus seven equivalent re-projections,
  two genuine identities (`s_d = a_*−a_c(d)`; `1/s_d = Σ|p_j(y_*)|²` = boundary-transport-norm), and a
  consistency check (lens 6) that `s_d` is the right kind of functional.
- **Is not:** progress across the wall. Every conjunct that is *closed* (proof12 reduction, comp80
  determinant, III-rate) was already known or reduces-to-known; every conjunct that is *open* (I-a from
  source, III-sign / NR-2) is RH-equivalent or a famous open problem.
- **The single most promising concrete move it surfaces** was to test whether the finite weld `a_*−a_c(d)`
  (lens 3) is the compression of the Connes–Consani prolate operator's positive/Sonin split. **That test was
  run (§5):** the archimedean half matches *exactly* (our protector lattice `2|w|=4N+1` is the prolate Hermite
  grading; `a_*` = the N=1 level, same Gaussian origin), but the literal claim is **false** (the Sonin
  compression is *unconditional* archimedean Weil positivity, whereas `s_d>0` is RH-conditional). The corrected
  target: `s_d>0` is the **semilocal** prolate positivity (Connes–Consani arXiv:2310.18423) — the archimedean
  Sonin compression *plus the finite places* — and NR-3 (a manifestly-positive `s_d`) would live there.

---

## 5. The prolate-compression test — result `[2026-06-22]`

**Question.** Is the finite weld `s_d = a_* − a_c(d)` the compression of the Connes–Consani–Moscovici prolate
operator's positive/Sonin split? **Verdict: NO as literally stated — but the archimedean *half* matches exactly, and
the full comparison is a precise, well-posed open question against the *semilocal* prolate.** No fabrication: the
result is a partial match + a logical refutation of the literal claim.

**The prolate object (sourced, not recalled).** `W_λ = −𝕊² + 2πλ²(4N+1) − ¼` on `L²(ℝ)^ev` (Connes–Moscovici
arXiv:2112.05500; Connes–Consani–Moscovici arXiv:2310.18423): `𝕊` = scaling (dilation) generator, cyclic vector the
Gaussian; `N` = the Hermite/orthogonal-polynomial **grading**. The **Sonin space** = the *negative* eigenvalues, whose
UV behaviour **reproduces the squares of the zeta zeros** (`~γ_n²`). Cited feature: *"Weil's positivity at the
**archimedean place** uses the compression of the scaling action to the Sonin space."*

### (a) The archimedean half matches — exactly `[PROVED — verified, exact algebra]`
Our archimedean protector lives at `w = s−½` for the `s=1` pole and the trivial zeros `s=−2N` (`N≥1`):
> `2|w| = 4N+1` for **every** `N≥0` (verified): N=0 → pole `s=1`, `y=−4` (the `−4p(−4)²` term); **N=1 → `s=−2`,
> `y_*=−0.16`, weight `a_*=(5/2)^{−2}=0.16` — the boundary atom**; N=2 → `y=−0.0494`; …
So the archimedean **locations sit on the prolate Hermite grading lattice `4N+1`**, and `a_*` is the **N=1 level**.
This is not a coincidence: the archimedean Γ-factor `Γ_ℝ(s)=π^{−s/2}Γ(s/2)` and the prolate's Hermite grading both
descend from the **same Gaussian** (`Γ_ℝ` is the Mellin transform of `e^{−πx²}`, the prolate cyclic vector). The
zero-side `γ_n²` is the prolate Sonin scale; our `ν'` lives on its **reciprocals** `y_ρ=1/γ_n²`. (The eigenvalue/weight
*normalisation* — the prolate `2πλ²` factor — is undetermined without that paper's `λ`; only the **lattice** is pinned.)

### (b) The literal compression claim is FALSE `[PROVED — logical, no-go]`
The cited prolate result is **Weil positivity at the archimedean place**, which is **UNCONDITIONAL** (the local factor
`W_∞ ≥ 0`, no RH). Our `s_d > 0` is **RH-equivalent** (conditional). An unconditional positivity cannot equal an
RH-conditional one. Therefore `a_*−a_c(d)` is **not** the compression of the *archimedean* prolate Sonin split. The
mismatch is located precisely: the Sonin/scaling compression governs the **archimedean budget** `a_*` (= our `M_triv`,
manifestly `⪰0`, unconditional — the analog of `W_∞≥0`); it does **not** contain the **prime demand** `a_c(d)=−1/m_d`
(= the finite-places sum `Σ_p W_p`), which is exactly the part that carries RH.

### (c) The correct, well-posed statement `[CONJECTURE — the actual target]`
> `a_*` (archimedean budget) ↔ the **archimedean** Sonin/grading compression (Connes–Moscovici, unconditional);
> `s_d = a_* − a_c(d) > 0` (the full weld, RH) ↔ positivity of the **SEMILOCAL** prolate operator
> (Connes–Consani arXiv:2310.18423), which is precisely the archimedean prolate *plus the finite places*.

So the move "compare to the prolate" resolves cleanly: the *right* prolate object is the **semilocal** one, and our
weld is conjecturally its finite-section/Sonin compression — `H^-_d` a compression of `(−W_semilocal)^{−1}|_{Sonin}`,
with `y_*=−0.16` the `N=1` archimedean grading channel. This is the **same architecture** (archimedean positivity by
Sonin compression, finite places added, global positivity = RH) — which is why both programmes circle the same wall.

### (d) What is missing, and why no computation was run `[NO-ROLEPLAY note]`
Settling (c) would require the **explicit semilocal prolate matrix in a polynomial/OP basis** comparable to `H^0_d`,
to check whether `H^-_d` is literally its compression and whether `a_c(d)` equals the finite-place block. That matrix
is not in hand. A numerical comparison is therefore **impossible without the prolate operator's data** — so none was
run (running one would be theatre). What *was* established is exact and checkable: the `4N+1` lattice match (a), and
the unconditional-vs-conditional refutation (b). Status: **the archimedean correspondence is real and
exact; the full-weld correspondence is a precise open comparison against the semilocal prolate, not a proven
compression.**

---

## 6. Next step taken — the prime-sign / budget test (comp81) `[2026-06-22, no-roleplay]`

The §5 prolate finding localized the RH content to the **prime demand** `a_c(d)` (the finite-places side the
archimedean prolate match does not cover). So the concrete next step probed **NR-2** directly: split `T_k = T_k^A`
(archimedean: pole + Γ) `+ T_k^P` (prime: `g_{2k}=[w^{2k}]logζ`) and compare the boundary gap for `H^0=A+P` (ζ),
`H^A` alone, and `H^flip=A−P` (prime sign reversed). Genuinely-unknown outcome; result below.

**Findings `[VERIFIED — comp81]`:**
1. **The archimedean budget is `≈ a_*`.** `s_d(A only) ≈ 0.16 = a_*` at every `d`: the Γ-factor/trivial-zero
   structure *alone* sits ≈critically at its own boundary atom (`H^A` has inertia `(d,1)`, the pole's negative square).
2. **The prime eats the budget to the no-margin threshold.** `s_d(ζ,A+P) → 0⁺`: the prime contributes `≈ −a_*` to
   `1/m_d`, bringing `s_d` from `a_*` down to the sliver `s_d>0`. **RH = the prime eats up to, not past, `a_*`.** This
   *is* the budget-vs-demand identity (Iteration II) made concrete: `s_d = a_*` (budget) `− [a_* − s_d]` (prime demand).
3. **The prime SIGN controls the negative-square count `κ₋`, not the scalar sign of `s_d`.** Flipping the prime sign
   (`A−P`) gives `s_d ≈ 2a_* = 0.32` — *positive, not negative* — **but inertia `(d−1,2)`: TWO negative squares.**
   Since the rank-one Γ-atom repairs only one, `H^0_flip = H^-_flip + a_*v_*v_*^T` has inertia `(d,1)` — **not PSD** —
   so the flip "fails RH" via a *second* negative square that the rank-one scalar `s_d (=2a_*>0)` is blind to.

**What this refines `[CONCLUSION]`.** The naive hypothesis "the prime sign flips `s_d` negative" is **false**. The
true statement: **the fake-family separator (NR-2) is the integer `κ₋` (negative-square count), not the rank-one
scalar `s_d`.** Correct Euler-product sign ⟹ exactly one negative square (`N₁`, repairable by the single Γ-atom);
wrong sign ⟹ `N₂` (not repairable). This is exactly comp72 (off-line ⟹ `κ=2`) and **lens 4** (`κ₋` is the faithful
integer; `s_d` is its rank-one shadow). So NR-2 sharpens to:

> **NR-2′ `[CONJECTURE]`:** the Euler-product coefficient positivity `Λ(n)≥0` forces the prime residual to add
> *exactly one* negative square to the protector (`κ₋(H^-)=1`), eating the archimedean budget `a_*` to the no-margin
> threshold; a fake (wrong-sign log-coefficients) adds `≥2`, which the single Γ-atom cannot repair.

This is consistent with the lens-4 reading and the prolate `N`-grading: the **scalar gap is the wrong object to watch
for fakes** — watch the integer `κ₋`. The remaining open core is unchanged in content (source-built `κ₋=1` ∧ `s_d>0`),
but the *separation* mechanism is now correctly attributed to the index, not the scalar.

---

## 7. gpt/48 corrections folded — the apex restated on `κ₋`, and the integer-index agenda

gpt/48 (fed the comp81 finding) converges with §6 and adds four sharpenings, now consolidated:

1. **Corrected bridge-theorem name:** the *Faithful semilocal Uvarov–Krein index theorem* — "completion + explicit
   formula + semilocal Γ/prolate boundary ⟹ `κ₋=0`", with `κ₋ = #off-line zero-pairs`. The reciprocal `Q_0≥0`
   (Layer 1, proof12) is unchanged; the proof-grade *object* (Layer 2) is the integer index, not `s_d`.
2. **Divisor correction:** `σ=ν'−a_*δ_{y_*}` is the rank-one (`N=1`) *channel shadow*; the proof divisor is the
   completed **semilocal index carrier** (integer `κ₋`), of which `σ` is one projection — blind to negative
   directions off the `v_*` channel.
3. **Scalar-shadow lemma `[gpt/48]`:** `s_d>0 ∧ κ₋(v_*^⊥)=0 ⟺ κ₋=0` — `s_d>0 ⟹ κ₋=0` *only* given `inertia(H^-)=(d,1)`
   **and** rank-one exhaustion of the negative space. comp81 is the countercase. (Bars the scalar from posing as faithful.)
4. **Finite-rank boundary Weyl `[gpt/48]`:** promote `a_*v_*v_*^T → VCV^*` over the prolate `4N+1` channels
   `v_N=v(−(2N+½)^{−2})`, gate `κ₋(S_r)=0`, `S_r=C^{−1}+V^*B^{−1}V`. `s_d` is the `r=0` compression.

**Integer-index experiment agenda (gpt/48 §7 — outcomes genuinely unknown; the natural follow-ups to comp81/§5):**
- **(a) Multi-channel boundary Weyl / prolate-channel truncation:** build `V=(v_0..v_r)` on the `4N+1` lattice, track
  `κ₋(S_r)` vs the full `κ₋`; how many channels detect inserted off-line defects? (Tests whether the `4N+1` basis is
  faithful or decorative.)
- **(b) Scalar-shadow failure atlas:** collect fakes with `s_d>0` but `κ₋>0`; decompose `𝒩_- = 𝒩_{rank1} ⊕ 𝒩_{extra}`,
  measure overlap of the extra negative eigenvectors with `v_*`.
- **(c) Integer-index resolution law:** inject off-line quartets, measure `κ₋` *directly* (not `s_d`); is each off-line
  pair `+2` additive, or does `κ₋` interact globally?
- **(d) Uniform-in-degree index persistence:** `κ₋(d+1)−κ₋(d)` for ζ/DH/sign-fake — is the integer a reliable
  finite-section carrier, or do shadows move while the index is stable?
- **(e) Boundary-channel completeness:** project a negative eigenvector onto `span{v_N:N≤r}`; residual decay tells
  whether the defect lives in the arch boundary or the finite-place bulk.
- **(f) Semilocal-prolate comparison** — *only* once the operator matrix is in hand (no comparison without data, §5(d)).

**The methodological takeaway (gpt/48, matches §6):** *do not certify a fake by `s_d>0`; certify by `κ₋=0`.* The open
core is now stated on the index: **`κ₋(H^-)=1` from the Euler product (the carrier)** ∧ **`κ₋(H^0)=0`** (no negative
direction survives the full multi-channel repair) — with `s_d>0` retained as one finite scalar readout.

### §7 result — comp82: the `4N+1` channel basis is faithful, but height-limited (not a finite-rank shortcut)

Ran agenda (a)/(e). **The prolate `4N+1` channel basis is faithful `[VERIFIED — comp82]`:** every tested fake's
negative eigenvector lies in `span{v_N}`. The comp81 sign-fake's defect is the **N=0 pole channel** `v(−4)` (captured
at `r=0`, `|cos(u_-,v_*)|~10^{−5}` — orthogonal to the `N=1` scalar channel, so `s_d` is blind). A real off-line
quartet (`g0=8`) lives in **mid channels `N≈3–5`** matching its height (residual `1.0→0.98→0.26→0.025→0`), invisible
to the low channels. **But the channel index needed = the defect's height scale**, so a finite-`r` boundary Weyl is
**height-limited** (the same `d*≈γ0/3` law as the moment matrix and the Pick kernel, comp72) — *not* a finite-rank
simplification. **Channel map:** `N=0` = pole/entireness (sign-fakes); `N=1` = `v_*` = the only channel `s_d` sees;
`N≥2` = protector tail (real off-line zeros at the channel matching their height). The scalar is blind to both ends
(`N=0` and `N≥3`). ⟹ the faithful object is the **full all-channel semilocal carrier** (`κ₋`); any finite truncation —
scalar `s_d` or finite-`r` boundary Weyl — inherits the height limit. This is consistent throughout: the index is
all-order; finite sections are height-graded.

---

## 8. Lens 8 reclassification — NR-1/NR-2/NR-3 are mirrors; the real move is orthogonal `[2026-06-22]`

Lens 8 (big-picture §1, *no target, only byproduct*) forces a reclassification of everything above. **NR-1
(`s_d>0`/`Q_0≥0`), NR-2 (the fake-family separation), NR-3 (the manifestly-positive `s_d`) are all RH-equivalent —
they are *mirrors* of RH, not levers on it.** Proving any of them *is* proving RH directly, which is the deduction
the charter forbids and which a century of renamings has failed at; the equivalences are horizontal and
content-preserving (proof12 is one line). So the "open cores" NR-1/2/3, though correctly identified as where RH lives,
are **the wrong things to attack** — attacking them is walking back into the hall of mirrors.

**The redirection (the project's charter, restored).** The one direction in this document that is **not** a mirror is
**NR-orth** — the value/transcendence axis (lens 7): Schanuel-for-prime-logs and the arithmetic of `{γ_n}`. It connects
to RH only *conjecturally*, which is exactly the point — it is a **non-RH-equivalent constraint** that, *if* it forces
the divisor's arithmetic, yields RH as a **byproduct**, never as a proved target. The provable, non-equivalent ground
to stand on is the project's home: **hypertranscendence** (Hölder/Ostrowski — ζ, Γ have no algebraic-differential rule,
*proven*), **Baker** (`{log p}` linearly independent, *proven*), and the **weld category `𝓜⁺`**. The work is to build
the constraint-structure *there* — for its own sake, the way Grothendieck built étale cohomology — and let any
RH-content fall out, not to engineer it.

**Operational consequence for this document.** NR-1/2/3 are retained as a *faithful map of the mirror wall* (useful: it
proves the mirrors are mirrors, which is why one stops polishing them). But the **forward agenda is NR-orth and the
hypertranscendence home**, not another positivity restatement. Concretely: the next genuinely-new question is not "is
`κ₋=0` source-built?" (a mirror) but **"does the transcendence/independence structure of `{log p}` (or the `𝓜⁺` weld)
impose a constraint that *forbids* off-line zeros as a side effect?"** — a constraint that does not mention RH, from
which RH cannot-be-otherwise. That is the byproduct stance; it is the only move lens 8 permits.
