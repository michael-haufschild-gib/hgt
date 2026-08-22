# The erosion threshold: ½ as the marginal-variance locus (G19) — TERMINAL: 2-fully-proven (BRIDGE/structural)

- **ID:** erosion-threshold
- **Stage:** 2-fully-proven (TERMINAL — see "19b RESOLVED + TERMINAL VERDICT" at EOF)
- **Type:** THEOREM (paper) / STRUCTURAL — Door grade **BRIDGE** (½ located as the erosion threshold; structurally RH-blind by A1/A2). Was: CONJECTURE (native).
- **Priority:** FUTURE
- **Source:** ../../door/bucket-time-and-non-holonomic-time.md · 00-status row #59
- **Statement (native conjecture).** For the Euler cocycle over the `𝕋^∞` Kronecker flow at abscissa
  `σ`, the Lyapunov exponent `L(σ) = 0` for `σ > ½` (the cocycle is eroded / `L²`-reducible), `σ = ½` is
  the unique marginal coupling (variance diverges like `log log`), and the `ζ`-zeros are the spectral
  degenerations of the marginal (`σ = ½`) cocycle.

## What is already proven (the backbone)
`../0-backlog-lean/critical-line-abscissa-of-convergence.md` (**review fixes applied 2026-06-19 — proven
on paper, ready for Lean**): `Re = ½` **is** the abscissa of a.s. convergence of the random Euler product,
and the total second moment `V(σ) = Σ_pΣ_k p^{-2kσ}/k²` is finite for `σ > ½`, blows up like
`log(1/(2σ−1))` as `σ → ½⁺`, and `~ log log X` at `σ = ½`; the real-part variance `Var(Re 𝓛) = ½V`
carries the `½` (= Selberg's `½ log log X` for `log|ζ|`). That is the **rigorous, non-circular** core of
"erosion," graded BRIDGE. The open work below is to turn it into a genuinely **dynamical / native**
statement.

## The dynamical reading (the open native content)

**Erosion.** A one-frequency (`𝕋^1`, Avila) Schrödinger cocycle generically has positive Lyapunov
exponent (localization). Adding incommensurate frequencies makes Birkhoff sums self-average faster (the
`𝕋^∞` orbit equidistributes by Weyl + ℚ-independence of `{log p}`), pushing the exponent down. With the
full infinite frequency vector `(log p)_p` and a potential of "strength" `Σ_p p^{-2σ}`, the cocycle
should be **eroded to `L(σ) = 0`** exactly when that strength is finite — i.e. for `σ > ½`. The
backbone's `L²`-boundedness of `𝓛(σ)` for `σ > ½` is the precise sense in which the cocycle is bounded
(`L = 0`); the conjecture is that this matches the genuine transfer-cocycle Lyapunov exponent.

- **Sub-conjecture 19a (define + prove `L = 0` above ½) — DONE (2026-06-19), graded BRIDGE.** Pinned as
  the additive Euler cocycle `A_σ(t,x) = ∫_0^t g_σ(φ_s x) ds` over the `𝕋^∞` Kronecker flow; **proved**
  it is a bounded `L²`-coboundary (the correct form of "`L = 0` / eroded") **iff `σ ≥ ½`**, sharp and
  inclusive at the line (pinch: observable `g_σ ∈ L²` for `σ > ½`, transfer function `h ∈ L²` for
  `σ ≥ ½`). Statement + proof: `../2-fully-proven/erosion-cocycle-reducibility.md`. *Door-2: BRIDGE* —
  the observable lives on **axis modes** (one prime each), so the cocycle **decouples prime-by-prime**
  into `𝕋^1` problems and never engages the joint `σ_p` structure. (The loose "Lyapunov exponent" of the
  original phrasing was a mis-formalization: an additive cocycle's time-Lyapunov exponent is the mean
  `= 0` trivially; the genuine dichotomy is bounded-coboundary vs not, which is what was proved.)
- **Sub-conjecture 19b (the marginal field at ½).** At `σ = ½` the eroded cocycle becomes a
  **log-correlated field** (variance `½ log log`, Selberg CLT; extremes = Fyodorov–Hiary–Keating). The
  `ζ`-zeros are its degenerations — the points where `log|ζ(½+it)|` makes its deepest excursions. Make
  "zero = degeneration of the marginal cocycle" precise (e.g. via the log-correlated maximum / the local
  behaviour at a zero).
  - **Edge interpretation (links the C5★ carrier).** In the degree-`d` finite-free/Hankel picture
    (`finite-free-convolution-flow.md`) the `d → ∞` reducibility splits **bulk** (moments concentrate by
    the finite-free CLT — soft) vs **edge** (the discriminant boundary `det H_d = 0`, where the section
    loses real-rootedness). The 19b "zeros = degenerations" are exactly that **edge** — the
    log-correlated/FHK extremes are the marginal-field face of the discriminant boundary. So 19b and the
    C5★ crux are the **same edge**: the uniform edge control as `d → ∞` is the native combination-mode
    Baker problem, and the marginal field is its `σ = ½` shadow.

## The A1/A2 reading (what erosion does and does NOT give)

Erosion is a statement about the **whole `𝕋^∞`** (a.s. / in distribution), not the single realization:

- The random Euler product `∏_p (1 − X_p p^{-σ})^{-1}` converges a.s. to a **nonzero** limit for `σ > ½`
  — so the *model* is **zero-free for `σ > ½`**, provably (the backbone).
- But `ζ` is **one** realization: the diagonal `t ↦ (p^{-it})_p` of the Kronecker flow. The a.s./mean
  statement does **not** pin a single orbit. **RH = transferring the model's `σ > ½` zero-freeness to
  the single diagonal realization** — exactly the field's A2 (free flow, equidistribution, provable) vs
  A1 (the specific zeros, the wall) split.
- This is why **soft / variance / second-moment methods are structurally blind to RH**: they see the
  `𝕋^∞`-average (the erosion threshold), not the amplitude of the single orbit (the zeros). Same lesson
  as the Möbius / iterated-logarithm picture (door bucket #97): correlation-randomness ≠ amplitude.

> So erosion gives a **non-circular structural reason** the critical line is special — it is the only
> place the Euler cocycle is critically tuned — **without** claiming to prove RH. It locates the wall
> (single-realization transfer), it does not cross it.

## Gates
- [x] 0 → 1  in-progress (backbone proven; native dynamical statement posed and split into 19a/19b)
- [ ] 1 → 2  fully-proven — 19a **done** (proved, BRIDGE; `../2-fully-proven/erosion-cocycle-reducibility.md`). The headline G19 still needs 19b and the harder Avila-type transfer-cocycle Lyapunov statement.
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Next steps
1. ~~19a~~ **DONE** — cocycle pinned, reducibility proved (iff `σ ≥ ½`), Door-2 = BRIDGE
   (`../2-fully-proven/erosion-cocycle-reducibility.md`). The Door-2 check answered the side-question:
   the cocycle **decouples over primes** (axis modes), so it does NOT engage the joint `σ_p` structure —
   the same reason §59/§60 are BRIDGE. **Yield:** the combination-mode C5 criterion (item 2).
2. **Combination-mode redirect (the real C5 lead).** To get a native (Door-2-surviving) statement, leave
   the additive/axis-mode world: target an object with **cross-prime combination modes**
   `m_pδ_p + m_qδ_q` where unique factorization (no resonance) and Baker (small divisors) are
   load-bearing — the curvature `F_{pq}` (§16), Rankin–Selberg `⊗`, the joint `G_L` class `ω`. Recorded
   in `../../door/door-C5-irreducibility-and-door-2-retest.md`.
3. **19b** (the native conjecture remaining here): the log-correlated marginal field at `σ = ½` and
   "zeros = degenerations" (Fyodorov–Hiary–Keating).

## Log
- 2026-06-19 — created in 0-backlog.
- 2026-06-19 — moved to 1-in-progress. Backbone (`Re=½` = abscissa of a.s. convergence + variance
  dichotomy) split to `../2-fully-proven/critical-line-abscissa-of-convergence.md`.
  Native conjecture sharpened into 19a (`L=0` above ½) + 19b (zeros = marginal-field degenerations);
  added the A1/A2 / single-realization note.
- 2026-06-19 — Lean formalizer returned the backbone card to
  `../0-backlog-lean/critical-line-abscissa-of-convergence.md`: the displayed variance `V(σ)` has
  `log(1/(2σ−1))` blow-up, while the factor `½` applies to `Re 𝓛`.
- 2026-06-19 — backbone **review fixes applied**: `V ~ log(1/(2σ−1))` (no ½), the `½` moved to
  `Var(Re 𝓛)=½V` (exact); divergence direction made explicit via Mertens. Numerically certified
  (`../../../../computations/2026-06-19-abscissa-normalization-check.txt`). Card now THEOREM (paper) in
  `0-backlog-lean`, ready for Lean.
- 2026-06-19 — 19a **proved** and split to `../2-fully-proven/erosion-cocycle-reducibility.md`: the
  Euler cocycle is a bounded `L²`-coboundary iff `σ ≥ ½` (sharp pinch at the line). Door-2 = BRIDGE
  (axis-mode decoupling); the proof yields the **combination-mode C5 criterion**. Open here: 19b.

## 19b RESOLVED (statistical) + TERMINAL VERDICT (2026-06-19, Wheeler) → 2-fully-proven (BRIDGE/structural)

**19b resolved, provable content (BRIDGE / IMPORT).** At `σ=½` the field `t ↦ \log|ζ(½+it)|` is
**log-correlated**: variance `~ ½\log\log T` (**Selberg's CLT**, fully proven — IMPORT), covariance
`~ −\log|t−t'|` (Bourgade et al.), and its extremes are governed by **Fyodorov–Hiary–Keating**
(`\max ~ \log\log T − ¾\log\log\log T`; the **leading order `\log\log T` is proven** —
Arguin–Belius–Bourgade–Radziwiłł–Soundararajan / Najnudel; the subleading term is open). The `ζ`-zeros are
**exactly the `−∞` singularities** of this field (`\log|ζ|=−∞ ⟺ ζ=0` — tautological). So *"zeros = degenerations
of the marginal cocycle"* is **precise** as:
> the zeros are the `−∞` points (deepest degenerations) of the `σ=½` log-correlated field `\log|ζ(½+it)|`;
> the field's log-correlation/variance is Selberg (proven), and the FHK extremal law governs the depth/spacing
> of the degenerations.
*Door-2:* Selberg CLT (IMPORT) + tautology ⟹ **BRIDGE**, not native. The **deep dynamical version** — "zeros =
spectral degenerations of a genuine Avila-type transfer cocycle," a **single-realization** statement — is the
**RH wall** (A1/A2), and it is exactly the **finite-free edge `\det H_d=0`** (the discriminant boundary where
the degree-`d` section loses real-rootedness; `finite-free-convolution-flow.md`). It is **relocated, not crossed**.

**TERMINAL VERDICT — G19 is a proven BRIDGE/structural result.** `½` is located as the **erosion /
marginal-variance threshold** — the **unique critically-tuned abscissa** of the Euler cocycle — by three proven
pieces: the **backbone** (`Re=½` = abscissa of a.s. convergence; `Var(Re𝓛)=½V`, `V~\log(1/(2σ−1))→\log\log` at
½; `../2-fully-proven/critical-line-abscissa-of-convergence.md` / its Lean-ready review card), **19a** (bounded
`L²`-coboundary iff `σ≥½`, sharp pinch; `../2-fully-proven/erosion-cocycle-reducibility.md`), and **19b-statistical**
(Selberg log-correlated marginal field + tautological zero-identification, above). By the **A1/A2 reading**, G19
**locates** the critical line as the unique marginal coupling **without crossing to RH** (it is a `𝕋^∞`-average /
second-moment statement, structurally blind to the single-orbit amplitude — same lesson as Möbius/iterated-log
#97). The RH-crossing (the deep dynamical "zeros = spectral degenerations") is the **located wall**, relocated to
single-orbit positivity / the finite-free edge `\det H_d=0`. **Grade: BRIDGE (structural).** No native C5 here;
the headline native conjecture, Door-2-tested, is a wall-locator, not a wall-crosser. → **2-fully-proven**.

## Log (cont.)
- 2026-06-19 (Wheeler) — **TERMINALIZED G19 → 2-fully-proven (BRIDGE/structural).** Resolved 19b's provable
  content (σ=½ log-correlated marginal field: Selberg CLT Var~½loglog + FHK leading-order extremes + the
  tautology zeros=−∞ of log|ζ|; IMPORT/tautology ⟹ BRIDGE). The deep dynamical "zeros = spectral degenerations
  of a transfer cocycle" is the RH wall (A1/A2 single-realization) = the finite-free edge det H_d=0 — relocated,
  not crossed. Headline verdict: G19 LOCATES ½ as the unique critically-tuned (erosion) abscissa via the proven
  backbone + 19a + 19b-statistical, but is structurally RH-blind; it is a wall-locator (BRIDGE), not a native C5
  wall-crosser. C5 count unchanged (0).
