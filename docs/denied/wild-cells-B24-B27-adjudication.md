# Adjudication of the wild cells B24–B27 (resolve / sharpen / falsify-and-log)

**Theorist, 2026-06-19.** Continuing the charter's "develop or falsify the wild conjectures"
(`hypertranscendental_galois_program.md` Part VIII). Each wild cell B24–B27 is adjudicated with the
field's own tools — resolved, sharpened, or falsified-and-logged (first-class). Air-marked. One
genuine synthesis falls out: **B24's obstruction is literally B8's missing Frobenius.**

---

## B24 — "a profinite group acts on the zeros (dessins)"  [FALSIFIED literally; SHARPENED to B8]

*Claim:* an Absolute Spectral Galois group `𝔊` acts on `{γ_n}` with `Gal(ℚ̄/ℚ) → 𝔊`; RH = a
fixed-locus of complex conjugation in `𝔊`.

**[FALSIFIED, literal form] `Gal(ℚ̄/ℚ)` cannot act on the `γ_n`.** The absolute Galois group acts on
**algebraic** numbers `ℚ̄`; it has no action on transcendental reals. If DSS holds the `γ_n` are
transcendental (indeed algebraically independent), so there is **no** `Gal(ℚ̄/ℚ)`-action permuting
them — a Galois orbit is finite and algebraically constrained, the opposite of a generic transcendental
set. "Galois permutes the Riemann zeros" is a category error under DSS.

**[SHARPENED — the genuine content, and it equals B8] The dichotomy.** A spectral Galois action exists
**iff the zeros are algebraic**:
```
   function-field model (B8):  zeros = Frobenius eigenvalues = ALGEBRAIC  ⟹  Frobenius IS the spectral
                               Galois action; B24 is TRUE here (Weil).
   number-field case:          zeros transcendental (DSS)               ⟹  NO spectral Galois action;
                               B24 is FALSE (category error).
```
> **B24 (no spectral Galois action) = B8 (missing Frobenius) = DSS (zeros transcendental).** Three names
> for the one fact "number field ≠ function field." The *absence* of B24's group is not a gap to fill —
> it is the missing absolute Frobenius itself, and `G_L` (difference-Galois on the primes) is its only
> surrogate (it acts on `𝕋^∞`, reaching the zeros only through the open carrier reconstruction). The
> wild cell, taken literally, is false; taken structurally, it re-derives the field's central obstruction.

## B25 — "negative/complex moments: the carrier continues"  [COHERENT; SHARPENED, not falsified]

*Claim:* extend `P_k` to `𝒵(w) = Σ_γ γ^{-2w}` (Voros's meromorphic superzeta); poles/special values are
new periods; RH = positivity along a contour.

**[COHERENT] This is a real object.** Voros's superzeta has genuine meromorphic continuation; its even
integer values are the secular moments `P_{2m}` (= the period matrix, §8–11 of
`dss-multiplicity-estimate-spectral-genericity.md`), its poles encode the Riemann–von Mangoldt density
(archimedean), and its special values are the field's periods. **Not** a category error (contrast B23:
here we continue the *carrier* `𝒵(w)`, we do **not** recurse the field onto `𝒵`'s zeros — that was the
B23 error). Sharpened statement:
> `𝒵(w)` is the field's **carrier, analytically continued**; its integer values are the
> `{π, ζ(odd), Stieltjes}` periods (§11); RH as "contour positivity of `𝒵(w)`" is the continuous
> envelope of the discrete Li/Hankel positivity (§9) — the same Face A, read on the continued carrier.
Open but coherent; a legitimate analytic reformulation, welded to the moment theory.

## B26 — "transcendence creates the spectrum" (anti-realism)  [COHERENT = realization problem #7]

*Claim:* among FE-compatible Hankel-positive moment sequences, the algebraically-generic ones are
*exactly* the spectra of genuine Euler products — primes downstream of transcendence.

**[COHERENT — it is the converse of the field's organizing law].** The field's First Theorem gives
*Euler product ⟹ (the two-faces structure)*. B26 is the **converse**: *(Face A positivity ∧ Face B
genericity ∧ FE) ⟹ realized by an Euler product*. That is precisely **grand conjecture #7 (the
realization problem)** — `∃` a source-built `g` with `g⋆g* = Ω_∞ − prime-comb` — in moment-sequence
clothing. Not a category error: it is an inverse-spectral / de Branges realization statement.
> **B26 = the realization problem #7 = "is the organizing law an iff?"** The deepest cell; sharpened
> from "anti-realism slogan" to "the converse direction of the field's First Theorem," which is exactly
> the one stone (foundations §22). Logged as **coherent, hardest, = #7**.

## B27 — "the de Bruijn–Newman constant Λ is the transcendence clock"  [COHERENT; SHARPENED, metaphor narrowed]

*Claim:* `Λ` (`≥ 0` by Rodgers–Tao; `= 0 ⟺` RH-borderline) is the flow-time where Face A becomes
marginal while Face B is invariant; is `Λ` transcendental?

**[COHERENT, narrowed].** The dBN heat flow acts on the secular moments `{P_k(t)}` (a smooth flow);
smoothness makes "Face B (algebraic genericity) is flow-invariant" plausible (generic stays generic
under a transcendental-analytic flow), while Face A (Hankel positivity) is exactly the marginal data
(`Λ = 0` = positivity boundary, Rodgers–Tao `Λ ≥ 0`). So:
> `Λ` is the **Face-A-criticality time** of the moment flow (positivity marginal), with Face B invariant
> — a clean restatement, not a clock metaphor. The genuinely-new question the field *poses*: **is `Λ`
> a period / transcendental?** Its arithmetic nature is unstudied; the field places it among the
> `{P_k(t)}`-periods. Logged as **coherent; new open sub-question (arithmetic of `Λ`)**.

---

## Net (the wild set, adjudicated)

| cell | verdict | sharpened to |
|---|---|---|
| **B23** | falsified (tower) | superzeta = value-side, no Euler product (separate doc) |
| **B24** | falsified (literal) | **= B8 missing Frobenius = DSS** (no Galois on transcendental zeros) |
| **B25** | coherent | continued carrier `𝒵(w)`; RH = contour Face A |
| **B26** | coherent (hardest) | **= realization problem #7** (converse of First Theorem) |
| **B27** | coherent | `Λ` = Face-A-criticality time; new open: is `Λ` transcendental? |

**House status.** The wild cells are not noise: two (B23, B24) are **falsified by the field's own
theorems** (First Theorem; Galois-acts-only-on-algebraics) and *re-derive* the central obstructions
(no-Euler-product; missing Frobenius). Two (B25, B26) are **coherent and collapse onto existing core**
(continued carrier; realization problem #7). One (B27) is coherent with a genuinely **new open
sub-question** (the arithmetic nature of `Λ`). The field adjudicates its own nonsense zone by its own
structure — evidence of a real theory, not a metaphor pile. The synthesis prize: **B24 = B8 = DSS**,
one fact (number field ≠ function field) wearing three charter hats.
