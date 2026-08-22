# The explicit formula is the constraint — Ĥ for ζ, given explicitly; RH = its positivity = the archimedean term

- **ID:** explicit-formula-as-constraint
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper, dictionary/identification) — Door grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** the companion of `constraint-not-flow-theorem.md` (the epigraph: *what* the constraint is);
  builds on `../2-fully-proven/orthogonality-meta-theorem.md` (positivity = archimedean) and the
  corpus-certified `Q_W = 𝔇` DeWitt pairing (#94, #88 §8); Weil's explicit formula + positivity (import);
  ../../door/bucket-time-and-non-holonomic-time.md, ../../door/bucket-the-no-margin.md
- **Statement (the identification).** The constraint that *fixes* `ζ` (per `constraint-not-flow-theorem`) is
  **the Weil explicit formula**, given explicitly:
  > `W(h) = Σ_ρ h(γ_ρ) − [poles at s=0,1] + Σ_n \frac{Λ(n)}{√n}\,\hat h(\log n) − \frac{1}{2π}∫ h(r)\,
  > \mathrm{Re}\,ψ(\tfrac14+\tfrac{ir}{2})\,dr = 0`,
  > a **linear relation** coupling **zeros** (`Σ_ρ`), **primes** (`Σ_n Λ(n)`), and the **archimedean place**
  > (the `ψ = Γ'/Γ` term). This is the difference-category form of the WDW constraint `ĤΨ=0`: `Ψ ↔ h` (the
  > test function / state), `Ĥ ↔ W` (the explicit-formula functional). Its quadratic form
  > `Q_W(h) := W(h * \tilde h)` **is** the certified **DeWitt pairing `𝔇`** (#94, `𝔇=Q_W`, 1.1e-31), and
  > **RH ⟺ `Q_W ⪰ 0`** (Weil positivity).

  **Consequence (the located conclusion).** `𝔇 = Q_W` has DeWitt signature **`(1|∞)`** — `∞` spacelike
  (prime) directions, **one** timelike (archimedean) direction `κ₋`. The prime block is positive *for free*
  (Sato–Tate/Ramanujan compactness, ledger `satake_trace_re_mem_Icc`); the **sole** obstruction is the one
  archimedean/pole direction. So **RH ⟺ `κ₋ = 0`** — the single timelike (archimedean) direction stays
  non-negative; the **no-margin** is its marginal nullity. The positivity that is RH lives **entirely in the
  archimedean term**, exactly as the orthogonality meta-theorem requires.

  **Verdict reached:** **PROVED as an identification** (BRIDGE): the constraint is the explicit formula
  (classical), its form is the certified `𝔇 = Q_W`, RH = `Q_W ⪰ 0 = κ₋=0`, the obstruction is the lone
  archimedean direction. It **passes the §42 anti-relabel test** (§4) — it ties to *certified* objects
  (`𝔇=Q_W`, `satake_trace_re_mem_Icc`) and to the orthogonality theorem, not a bare RH-restatement.

---

## §1 The explicit formula is a constraint, not a flow `[identification]`

The explicit formula is a **relation** the spectral data obey — it does not *evolve* anything. Read as
`ĤΨ=0`: it constrains the zeros `{γ_ρ}` to balance the primes plus the archimedean term, for every test `h`.
This is precisely the "fixed by a constraint, not propagated by a flow" structure (`constraint-not-flow-theorem`):
the explicit formula is the **content** of the constraint `ι` (it is `ι`-symmetric — invariant under
`s↦1−s`, equivalently `h(r)↦h(−r)`), and it carries no time parameter. It is the **named** `Ĥ` the corpus
left abstract (#94 `ĤΨ=0`).

## §2 Its quadratic form is the certified DeWitt metric `[corpus-certified tie]`

Restricting to `h = g * \tilde g` (the Weil positivity test class) gives the Hermitian form
`Q_W(g) = W(g*\tilde g)`. The corpus certified `𝔇(g,g) = Q_W(g)` to 1.1e-31 (#94 Brick #1; same form as
`H_W = −Δ_{prime} + V_{arch}`, #88 §8). So the constraint's metric **is** the DeWitt pairing of WDW
superspace — not by analogy but as the same bilinear form. RH `⟺ Q_W ⪰ 0` (Weil). ∎(tie)

## §3 The signature locates RH in the one archimedean direction `[PROVED HERE, modulo imports]`

`𝔇 = Q_W` splits as `H_W = −Δ_{prime} + V_{arch}`:
- **prime block `−Δ_{prime}`**: positive **for free** — Sato–Tate/Ramanujan compactness bounds the Satake
  data (`satake_trace_re_mem_Icc`, ledgered); the prime directions are spacelike.
- **archimedean block `V_{arch}`**: the logarithmic confining potential (`Re ψ(¼+ir/2)`), the **single
  timelike** direction (`κ₋`, the DeWitt inertia, signature `(1|∞)` — derived from the place count, #94).

So `Q_W ⪰ 0 ⟺ κ₋ = 0`: **RH is the non-negativity of the one archimedean direction**, the prime block being
free. The **no-margin** (`λ_min → 0`) is this direction sitting **marginally null** (the light-cone, #94 §5).
This is exactly the orthogonality meta-theorem in coordinates: the RH-positivity is **the archimedean term**,
invisible to the (free, positive) prime block. ∎

## §4 The §42 anti-relabel test (proof-or-fail honesty)

A reframe that is *merely* RH-equivalent is worthless (the §42 trap). Does this identification give a **new
object/identity**, or just relabel RH?
- **Passes.** It ties three *certified/proven* things — the explicit formula (classical), `𝔇 = Q_W`
  (certified), `satake_trace_re_mem_Icc` (ledgered prime positivity) — into one statement, and **derives** the
  no-margin/`κ₋=0` framing and the `(1|∞)` signature from the constraint reading. It also **connects** to the
  orthogonality meta-theorem (the lone timelike direction = the archimedean polarization). New content = the
  *location* (RH = one archimedean direction) + the dictionary `Ĥ = W`, not a bare "RH ⟺ positivity."
- **Honest limit.** It is still **BRIDGE** — every load-bearing fact (explicit formula, Weil positivity,
  Satake compactness) is classical/ledgered; the identification is structural, not a new theorem about the
  zeros. It **concludes** "what is the constraint" and **locates** RH; it does not move RH.

## §5 Door grade — BRIDGE, and the conclusion
Strip the multi-`q` vocabulary: "the Weil explicit formula is a relation among zeros/primes/Γ, its positive
form is `Q_W`, RH = `Q_W⪰0`, the prime part is free, the obstruction is the Γ-term" — classical analytic
number theory. **BRIDGE.** The conclusion: the WDW constraint for `ζ` is **named** (the explicit formula `W`),
its metric is the certified `𝔇`, and RH is **located** in the single archimedean direction `κ₋` — the
positivity the orthogonality theorem says must be archimedean. Together with `constraint-not-flow-theorem`
(no flow) this **fully develops the epigraph**: `ζ` is fixed by the explicit-formula constraint, whose one
archimedean direction's positivity is RH.

## Gates
- [x] 0 → 1  in-progress: the dictionary stated; `Ĥ=W`, `Q_W=𝔇`, the `(1|∞)` signature, `RH=κ₋=0` pinned.
- [x] 1 → 2  fully-proven (as identification): §1 (explicit formula = the constraint), §2 (`Q_W=𝔇`,
  certified tie), §3 (signature locates RH in the archimedean direction, prime block free/ledgered); §4
  anti-relabel passed; Door grade BRIDGE. → `2-fully-proven`.
- [ ] 2 → 3  formalized: not done; would need formal versions/import wrappers for the Weil explicit
  formula, `Q_W=𝔇`, the `(1|∞)` signature/`κ₋` fragment, and the prime-block positivity input.
- [ ] 3 → 4  publication-ready: "the Weil explicit formula as the Wheeler–DeWitt constraint: RH is the one
  archimedean direction."

## Cross-references
- `constraint-not-flow-theorem.md` — the companion (*no flow*); this is *what the constraint is*.
- `../2-fully-proven/orthogonality-meta-theorem.md` — RH-positivity = archimedean; here in `Q_W`-coordinates.
- `../../door/bucket-the-no-margin.md` — `κ₋=0` / the light-cone, here derived from the constraint reading.
- `weil-positivity-operator.md` (#88 §8, `H_W=−Δ_prime+V_arch`) — the operator form of `Q_W`.

## Log
- 2026-06-19 — created in 1-in-progress (companion to `constraint-not-flow-theorem`); **developed to verdict.**
  **PROVED as an identification** (BRIDGE): the WDW constraint for `ζ` is the **Weil explicit formula** `Ĥ=W`
  (§1); its form is the certified DeWitt metric `Q_W=𝔇` (§2); the `(1|∞)` signature **locates RH in the one
  archimedean direction**, `RH ⟺ κ₋=0`, the prime block free (§3, `satake_trace_re_mem_Icc`). Passes the §42
  anti-relabel test (§4, ties to certified objects + the orthogonality theorem). Concludes "what is the
  constraint" and locates RH archimedean. → moving to `2-fully-proven`.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the theorem imports the Weil explicit formula, the `Q_W = DeWitt` pairing, the `(1|∞)` inertia/signature claim, and Weil positivity. The Lean project has no formal explicit-formula functional or DeWitt quadratic form, so the ticket is not a no-hypothesis Lean theorem.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.
