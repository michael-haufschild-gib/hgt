# 2πi is the Frobenius (log-monodromy at infinity) — FALSE LEAD (the log-monodromy is the identity on the base field; the windings are degree-1, not a Frobenius)

- **ID:** moonshot-2pi-monodromy-frobenius
- **Stage:** 5-failed (the monodromy-Frobenius identification breaks when made precise + experiment; closed 2026-06-19, DeWitt)
- **Type:** MOONSHOT CONJECTURE → **FALSE LEAD / REFUTED** (monodromy = identity on the base field, not a field endomorphism; `a_∞`'s `2π` is the REAL Stirling/ζ-reg constant `−ζ'(0)=½log2π`, not the imaginary period `2πi`; `N(T)` = archimedean Γ-phase winding, degree-1, not a deck-Frobenius) — tested first as flagged
- **Priority:** FIELDS MEDAL (+)
- **Target of attack:** **untie `ω∈H²(G_L)` / construct the missing archimedean Frobenius F₁** (#27/#71;
  `compute-omega-h2-gl.md` §S, `a_∞=½log2π`).
- **Source:** chat thread 2026-06-19 (archimedean-Frobenius moonshots).

## Verdict — REFUTED: the log-monodromy is the identity on the base field; the 2π's are distinct (worked + experiment, 2026-06-19, DeWitt)
Worked by the scientific method (split / interrogate / metaphor / strip / **experiment**), self-contained. The
conjecture splits into P1–P5; the central identification fails, and the one true sub-claim is the standard
zero-count with no Frobenius content.

- **P1 — "missing F₁ = the 2πiℤ deck transformation" is FALSE: the monodromy is the identity on the base
  field.** A Frobenius / the missing `σ` must be a **nontrivial field endomorphism** (`x↦x^p`; the `σ_p` move
  the variable). The deck transformation of `exp:ℂ→ℂ*` is `log x ↦ log x + 2πi`, i.e. `x ↦ x·e^{2πi} = x` — the
  **identity** on single-valued functions of `x`. It acts nontrivially only on the multivalued `log` itself,
  trivially on the base field `ℂ(x)`. So it is `π₁(ℂ*)=ℤ` acting on the cover — a **degree-1 topological
  winding**, not a Galois/difference operator. (This makes precise the card's own admission that it "conflates
  a period with a field endomorphism.")
- **P2 — "ω = the 2πi-monodromy class" is a degree mismatch.** `ω∈H²(G_L)` is degree 2; the monodromy class is
  degree 1 (`π₁`/`H¹`). A degree-1 winding cannot **be** a degree-2 gerbe class. FALSE as an identity.
- **P3 — "a_∞'s 2π comes from the log-monodromy" is FALSE: it is the REAL Stirling/ζ-reg 2π, not the imaginary
  period.** Experiment E1 (`computations/2026-06-19-2pi-monodromy-frobenius-test.txt`): `a_∞ = −ζ'(0) =
  ½log(2π) = 0.91893853…`, with **imaginary part 0** (`|a_∞−½log2π| < 10^{-41}`). The log-monodromy period is
  `2πi = 6.2831…i`, **purely imaginary**. `a_∞` contains `log(2π)` (a real regularization magnitude, from the
  theta/Gaussian functional equation, `∏k "=" √2π`), categorically distinct from the imaginary period `2πi`.
- **P4 — "FE-gluing of a_∞ = winding N(T)" is TRUE but deflationary (the standard Riemann–von Mangoldt
  structure), with no Frobenius content.** Experiment E2: `N(T) = θ(T)/π + 1 + S(T)`, `θ` = Riemann–Siegel
  phase `= arg Γ(¼+iT/2) − (T/2)logπ` (the **archimedean Γ-factor's phase**). Numerically `θ(T)/π+1` vs the
  actual `nzeros(T)`: `T=50 → 9.423` vs `10`; `T=100 → 29.0024` vs `29`. So `a_∞` and `N(T)` **do** share the
  archimedean Γ-factor's Stirling `2π` (same source) — but this is the known zero-count: `N(T)=(1/2πi)∮ξ'/ξ` is
  the **argument-principle winding** of the archimedean phase, a **degree-1 real-analytic** object, **not** a
  `2πi` deck-Frobenius. No new content beyond Riemann–von Mangoldt / Riemann–Siegel `θ`.
- **P5 — "untie: ω=0 ⟺ winding trivial" is FALSE.** `N(T)→∞` (infinitely many zeros) so the "winding" is never
  trivial; and `ω=0` is the realization/DSS statement, **decoupled** from the zero-count (the #275 decoupling).
  Equating `ω=0` with a trivial zero-count conflates realization with localization.

### Interrogation (metaphor / strip / rotate — per CLAUDE.md scientific method)
- **Metaphor:** `log` is a spiral staircase over `ℂ*` (the universal cover); the deck transformation `2πiℤ` is
  "climb one floor." What am I trying to DO? Climb = analytically continue. Climbing returns to the **same
  point on the base floor** (`x` unchanged) — the step is **invisible downstairs**. A Frobenius must act
  visibly downstairs (permute residues, move `x`). The staircase-step does nothing downstairs ⇒ not a
  Frobenius. The metaphor exposes P1.
- **Strip** to essentials: F₁ needs an object that is (a) a nontrivial endomorphism of the difference field and
  (b) carries a degree-2 (`H²`) gerbe class `ω`. The `2πi`-monodromy has **neither** (identity on the base;
  degree-1). The property-search ("infinite-order, archimedean, refines `Frob_∞`") points to **other**
  in-tree candidates (Connes' scaling/Frobenius flow; the Γ-factor's irregular/Stokes structure) — not the
  log-deck-transformation.
- **Rotate** (A2↔RH, joining the M3 skyrmion result): `κ₋=(1/2πi)∮Z'/Z` and `N(T)=(1/2πi)∮ξ'/ξ` are **both
  degree-1 argument-principle windings** of the archimedean phase. Together with `moonshot-prime-skyrmion-no-
  clock` (REFUTED: A2 axis is degree-1 only), this establishes that **the archimedean "knot" is not a higher /
  monodromy charge — every winding in play is a degree-1 real-analytic Γ-phase object.**

**Corrected statement (what survives).** The `2π` shared by `a_∞=½log2π` and `N(T)`'s main term is the
**archimedean Γ-factor's Stirling / ζ-regularization `2π`** (the theta/Gaussian functional equation), and
`N(T)` is its **degree-1 argument-principle winding** (Riemann–Siegel `θ`). It is **not** a deck-transformation
Frobenius: the log-monodromy is trivial on the base field and lives in degree 1, while `ω` lives in degree 2.
The missing F₁ is not the `2πi`-monodromy.

---

## The wild claim
At a finite prime, cyclotomy gives roots of unity and Frobenius. ℝ has **no roots of unity past `±1`**, so the
"cyclotomic Frobenius at ∞" is missing — *that* is the knot. But ∞ has one infinite-order object finite primes
lack: **the monodromy of `log`.** `x^s = e^{s log x}` is multivalued; encircling `0` adds `2πi`.

> **Conjecture (2πi-Frobenius).** The missing archimedean Frobenius is the **deck transformation `2πiℤ`** of
> the universal cover of `ℂ*` — the **infinite-order refinement of complex conjugation** (which is only the
> order-2 `Frob_∞` in the archimedean Weil group). `ω` = the **`2πi`-monodromy class**; `a_∞=½log2π` contains
> the `2π` by construction. **"Untie the knot" = unwind `log` around the `s=1` pole; the knot IS the branch
> cut.**

## Untie move / test (concrete, near-term)
1. Is `[ω]` exactly the class of the **`log`-monodromy** in `H²(G_L)`?
2. Does the **FE-gluing of `a_∞`** (the open Layer-2 of `compute-omega §S`) reduce to the **winding number
   around the `s=1` pole** `= N(T)` (the zero-count; the `moonshot-rh-spectral-flow-index` `[ω]=N(T)`
   quantization)? — **checkable against the existing `compute-omega §S` machinery.**
3. **Untie:** if so, the Frobenius is the integer winding; `ω=0` ⟺ the winding is trivial after FE-gluing.

## Why <5%
"`2πi` as a Frobenius" conflates a transcendence period with a field endomorphism; the refinement of the
order-2 `Frob_∞` to infinite order has no current mechanism. But it is the **only** idea here with a
ready-made test and it explains the `2π` in `a_∞`.

## Door / grade
MOONSHOT. If `[ω] =` log-monodromy `= N(T)`, it instantly fuses the archimedean knot with the
topological-charge moonshots (Frobenius = winding = `a_∞`'s `2π`, one object) — a strong D2 unification.

## Cross-references
- `compute-omega-h2-gl.md` (#27, §S) — `a_∞`, the FE-gluing; the test target.
- `moonshot-rh-spectral-flow-index.md` (M2, `[ω]=N(T)` quantization) — this gives the **Frobenius reading** of
  that winding; `moonshot-prime-skyrmion-no-clock.md` (M3) — the winding/texture sibling.
- `omega-splits-wild-kernel-freeness.md` — the wild-kernel/`ω` splitting the monodromy would refine.

## Log
- 2026-06-19 — filed (archimedean-Frobenius moonshot set). Missing F₁-Frobenius = `2πiℤ` log-monodromy /
  deck transformation, infinite-order refinement of order-2 complex conjugation; `ω` = the monodromy class;
  untie = unwind `log` at `s=1`. SO-1: "monodromy" is used for function-field Deligne–Katz and the winding
  moonshots; the *log-branch-as-archimedean-Frobenius* reading is distinct. **Flagged to test first.**
- 2026-06-19 (DeWitt) — **REFUTED → 5-failed.** Worked by the scientific method incl. experiment
  (`computations/2026-06-19-2pi-monodromy-frobenius-test.{py,txt}`). P1: log-monodromy = identity on the base
  field (`x↦x·e^{2πi}=x`) ⇒ not a field endomorphism / not a σ-Frobenius; it is degree-1 `π₁`. P3 (E1):
  `a_∞=−ζ'(0)=½log2π` is REAL (im=0), the Stirling/ζ-reg 2π — not the imaginary period `2πi`. P4 (E2): `N(T)`
  is the archimedean Γ-phase winding `θ(T)/π+1+S(T)` (29.0024 vs 29 at T=100) — the standard Riemann–von
  Mangoldt count, degree-1, no Frobenius content. P2 degree mismatch (1 vs 2); P5 conflates realization with
  zero-count (#275). Rotate-move joins M3 (skyrmion): every archimedean winding (`κ₋`, `N(T)`) is degree-1 —
  the knot is not a higher/monodromy charge. Corrected: the shared 2π is the Γ-factor Stirling/theta constant.
