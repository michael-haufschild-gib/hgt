# Why DSS is strictly harder than the Grothendieck Period Conjecture: it crosses the period / non-period divide

**Theorist, 2026-06-19.** Status: SPECULATION / conjectural frame, air-marked throughout. No proof of
DSS or RH is claimed. This is a "what-if" locating *where* the DSS difficulty actually sits — directive:
conjecture and speculate on the open apex, do not fake. Companion: `carrier-unifies-dss-and-rh-faces.md`
(DSS = the infinite jet of the carrier), `period-comparison-primes-zeros-the-planet.md`.

## 0. The claim in one line

DSS = algebraic independence of `{π} ∪ {ζ(3), ζ(5), …} ∪ {γ₁, γ₂, …}` (Stieltjes). The first two
groups are (conjecturally) **periods of mixed Tate motives over ℤ**; the Stieltjes constants are
(conjecturally) **not periods at all** — they are exponential-period-like / "regularization
constants." So DSS is not merely a period-independence statement (which the **Grothendieck Period
Conjecture, GPC**, would settle); it asserts independence *across the period / non-period boundary*,
which is strictly more than GPC delivers. **This is the locus of the difficulty** — and it is *not*
the part the field's tools (multiplicity estimate, carrier rigidity) naturally address.

## 1. The period side — `{π, ζ(odd)}` is GPC-conditional `[KNOWN-CONDITIONAL]`

`π = (2πi)/i` is the period of the Tate motive `ℚ(1)`. The odd zeta values `ζ(2k+1)` are periods of
the mixed Tate motives `ℚ(2k+1)` (framed extensions in the category `MTM(ℤ)` of mixed Tate motives
unramified over `ℤ`). The motivic Galois group of `MTM(ℤ)` is known (Deligne–Goncharov): a semidirect
product `𝔾_m ⋉ (free pro-unipotent on generators in degrees 3,5,7,…)`. **Granting GPC** (period
trdeg = dim motivic Galois group), the motivic periods `{π, ζ(3), ζ(5), …}` are algebraically
independent. So the *period half* of DSS is "known modulo GPC" — a famous but **well-located**
conjecture with a motivic Galois group computing the answer.

`[CONJECTURE, standard]` The `{π} ∪ {ζ(odd)}` half of DSS ⟸ GPC for `MTM(ℤ)`.

## 2. The non-period side — the Stieltjes constants escape the period world `[SPECULATION]`

The Stieltjes constants `γₙ` are the Laurent coefficients of `ζ` at its pole `s = 1`:
`ζ(s) = 1/(s−1) + Σₙ ((−1)ⁿ/n!) γₙ (s−1)ⁿ`, with `γ₀ = γ_E` (Euler–Mascheroni). Key point:
- `γ_E` is **conjecturally not a period** in Kontsevich–Zagier's sense. It is expected to be an
  *exponential period* (e.g. `γ_E = −∫₀^∞ e^{−x} log x dx`), a strictly larger class, and conjecturally
  transcendental and *not* a Kontsevich–Zagier period.
- The higher `γₙ` are likewise regularization constants of the same exponential-period flavor
  (Hadamard-finite-part / Euler–Maclaurin tails), not periods of `MTM(ℤ)`.

So the Stieltjes constants live **outside** the motivic-period algebra that GPC controls. GPC says
nothing about `γₙ` because `γₙ` is not a period of any motive in the relevant Tannakian category.

`[SPECULATION]` `{γₙ}` are exponential periods, not Kontsevich–Zagier periods; they are not in the
period algebra of `MTM(ℤ)`.

## 3. The consequence — DSS is GPC + a genuinely-extra transcendence input `[SPECULATION, the new content]`

Combine §1–§2. DSS asks for joint algebraic independence of a period set `{π, ζ(odd)}` **and** a
non-period set `{γₙ}`. Even granting GPC (settling the period side), DSS additionally requires:

> **(DSS-cross)** the Stieltjes constants `{γₙ}` are algebraically independent *of the entire period
> algebra of `MTM(ℤ)`* (and of each other).

This is a statement *across* the period / non-period divide — exactly the kind of independence that
neither GPC nor the motivic Galois group sees, because one side is invisible to the period torsor.
The right framework is the **exponential-motives / Nori-motive** enlargement (Fresán–Jossen), whose
period conjecture *would* cover exponential periods — but that conjecture is even less accessible and
its Galois group for the relevant exponential motives (the ones whose periods are the `γₙ`) is not
computed. **This is the genuinely-open core of DSS, and it is the Stieltjes side, not the zeta side.**

### 3a. Why this matters for the field's strategy

The field's bet (`dss-multiplicity-estimate-spectral-genericity.md`) is a Nesterenko-type argument:
multiplicity estimate (✓ ledgered, `MultiplicityEstimate`) + arithmetic lower bound (the missing
Liouville substitute). This frame predicts **where that arithmetic input must bite**: not on the
`ζ(odd)` (GPC/period territory, where Nesterenko-style methods already have purchase — cf. Nesterenko's
own theorem on `{π, e^π, Γ(1/4)}`), but on the **Stieltjes constants**, which are the exponential-period
side. So the multiplicity estimate should be deployed against the *Laurent data of ζ at `s=1`* (where
the `γₙ` live), i.e. against the carrier's behaviour near the `s=1` ⟷ `z`-image, not near the integer
special values. The carrier germ (`carrier-unifies-dss-and-rh-faces.md`) makes this concrete: the
`a_j = [sʲ](ζ'/ζ)(0)` closed forms (`a₁ = ζ(2)/2 − γ_E² − 2γ₁`, …) are exactly the place where the two
worlds **mix in a single coefficient** — so the secular moment `P_k` is itself a period/non-period
*sum*, and the algebraic-independence question is whether that mixing is "generic."

### 3b. A sharper sub-conjecture `[CONJECTURE — falsifiable target]`

`[CONJECTURE]` Modulo GPC for `MTM(ℤ)`, DSS is **equivalent** to (DSS-cross): the exponential periods
`{γₙ}` are algebraically independent over the field generated by the Kontsevich–Zagier periods. This
*localizes* DSS to a single statement entirely on the exponential-period side — removing the `ζ(odd)`
from the open part (they go to GPC). Falsifiable handle: any algebraic relation among `{P_k}` would,
after subtracting the GPC-controlled `ζ`-value part, produce an algebraic relation among `{γₙ}` over
the period field — testable in principle by high-precision PSLQ on `γₙ` against `{π, ζ(odd)}`
(numerically: none found to date; `computations/dss_secular_moments_pslq/` is the secular-moment
shadow of this).

## 4. Honest status

`[KNOWN-CONDITIONAL]` §1 (period half ⟸ GPC). `[SPECULATION]` §2 (Stieltjes = exponential periods),
§3 (DSS = GPC + cross-divide independence), §3b (the localization to (DSS-cross)). None of this is a
proof; it is a **relocation** of the open core: DSS's hardness is not the zeta values (period side,
GPC-shaped) but the Stieltjes constants crossing into the period world (exponential-period side,
beyond GPC). The field's Nesterenko strategy should therefore aim its arithmetic lower bound at the
`s=1` Laurent data. **The finite shadow is fully proven** (`spectrum_esymm_algIndep` — finite spectra
have full trdeg); the infinite apex is this cross-divide statement, and it is genuinely open
mathematics — conjectured and located here, not faked.

---

## UPDATE (2026-06-19) — `[NUMERIC]` evidence for (DSS-cross)

PSLQ (mpmath, maxcoeff `1e12`, dps=150 and dps=300 with the `dps > 1.5·n·log₁₀H` guard, all
precision-safe; `computations/dss_cross_divide/`): **no low-height algebraic relation** among
`{1, γ₀, γ₁, γ₂, γ₃}` (Stieltjes ℚ-linearly independent), nor in the **cross set**
`{1, π², ζ3, ζ5, γ₀, γ₁, γ₂}` (periods + Stieltjes), nor in a degree-2 cross
`{1, γ₀, γ₀², π², ζ3, γ₁}`. Confirmed at two precisions (no artifact). This is numeric support for
(DSS-cross): the Stieltjes constants show no low-height dependence on the period field — consistent
with the conjectured cross-divide independence being the open core of DSS. `[NUMERIC, not a proof]`

---

## UPDATE (2026-06-19) — broader meta-principle + a methodological positive control

`[SPECULATION → meta-principle]` The cross-divide independence may be one instance of a broader
pattern: **regularization-derived constants are transcendentally fresh relative to periods.** Beyond
the Stieltjes `{γₙ}` (Laurent/finite-part data of `ζ` at `s=1`), the *derivative-at-special-point*
constants `log 2π = −2ζ'(0)` and Glaisher's `ζ'(−1) = 1/12 − log A` are also exponential-period-like
(values/derivatives of `ζ` outside the convergent locus), and should likewise be free of the period
field. `[CONJECTURE]` zeta-regularization / Hadamard-finite-part is a *transcendence-creating*
operation: it manufactures constants algebraically independent of the input's Kontsevich–Zagier
periods. (DSS-cross) is the `s=1`-Laurent instance.

`[NUMERIC]` PSLQ (mpmath, maxcoeff `1e12`, dps=150 & 300, guard-safe; `computations/dss_cross_divide/
regularization_test.txt`):
- **positive control** — the *known* relation `2·ζ'(0) + log 2π = 0` is correctly **detected**
  (`[2,1]`), confirming PSLQ finds genuine relations at this precision/height, so the negatives below
  are meaningful (not false negatives).
- `{1, γ₀, γ₁, log 2π, ζ'(−1)}`: **no relation** — the regularized/derivative constants are mutually
  ℚ-linearly independent.
- cross `{1, γ₀, log 2π, ζ'(−1), π², ζ3, ζ5}`: **no relation** — regularized constants free of periods.

So the period/non-period divide is *robust and broad*: a whole class of regularization-derived
constants resists low-height algebraic dependence on periods, with the method validated by recovering
a known identity. Numeric tier; not a proof — but it strengthens (DSS-cross) and locates DSS's open
core firmly on the regularization/exponential-period side.
