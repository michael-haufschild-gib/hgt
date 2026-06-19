# The seam IS the period / non-period divide: one archimedean obstruction behind both RH and DSS

**Theorist, 2026-06-19.** Status: SYNTHESIS / conjectural frame, air-marked. No proof of RH or DSS is
claimed. This ties together the session's threads — the carrier germ
(`carrier-unifies-dss-and-rh-faces.md`), the period/non-period divide
(`dss-across-the-period-nonperiod-divide.md`), the regularization meta-principle, and the field's
core architecture (the **seam**, where `infinite-base-difference-galois-for-L-functions.md` locates
the difficulty). Directive: synthesize a novel frame several levels deep on the open apex.

## 0. The synthesis in one line

The field says the difficulty lives at the **seam** `[𝔾_a, 𝔾_m]` — the gluing of the archimedean wing
(`W_ℝ`, "the frontier") to the multiplicative wing (`𝕋^∞`, "free, zero-blind"). This note identifies
that seam, concretely, as the **period / non-period divide**:
- the **multiplicative wing** (Euler product, `ζ`-values at integers) supplies **periods** (mixed Tate,
  `{π, ζ(odd)}`, GPC-shaped);
- the **archimedean wing** (the `Γ`-factor of completed `ξ`, the pole at `s=1`) supplies the
  **non-periods** (`{γₙ}` Stieltjes, `log 2π`, Glaisher — exponential/regularization constants);
- the **seam = the completion `ξ = (Γ-factor) × ζ`** glues period to non-period.

And this single divide is the obstruction behind **both** apex faces: DSS (the jet) and RH (the type).

## 1. The two wings carry the two sides of the divide `[derivation + SPECULATION]`

The completed `Ξ(z) = ξ(½+iz)` factors as the archimedean `Γ`-factor times the multiplicative `ζ`. Its
logarithmic derivative — the **carrier** `m_ξ = −Ξ'/Ξ` — is therefore a *sum* of the two wings'
log-derivatives:
```
   m_ξ = (−Γ'/Γ-type, archimedean: digamma ψ, brings γ_E and pole-Laurent data)
        + (−ζ'/ζ-type, multiplicative: prime/Euler data, brings the ζ-values).
```
Concretely (this project's verified formula): the secular moments — the Taylor coefficients of `m_ξ` —
are
```
   P_k = 1 − (−1)ᵏ ζ(k)/2ᵏ − a_{k−1},   a_j = [sʲ](ζ'/ζ)(0),
```
with the **period part** `ζ(k)` (multiplicative wing) and the **non-period part** `a_j` (the
Stieltjes-constant closed forms — `a₁ = ζ(2)/2 − γ_E² − 2γ₁`, …, archimedean wing). So **each secular
moment is literally a period + non-period sum**, glued at the seam. The carrier germ doesn't merely
*carry* both faces (RH type, DSS jet) — its very coefficients are the seam's period/non-period
gluing made arithmetic.

## 2. DSS difficulty = the archimedean side of the seam `[CONJECTURE, from companion]`

`dss-across-the-period-nonperiod-divide.md` showed: modulo GPC (period side, multiplicative wing), DSS
reduces to **(DSS-cross)** — the Stieltjes/exponential-period constants are independent of the period
field. (DSS-cross) is *entirely on the archimedean wing* (the `Γ`-factor / `s=1`-Laurent data).
Numerically supported (no low-height cross relation, with positive control;
`computations/dss_cross_divide/`). So: **DSS's open core lives on the archimedean side of the seam.**

## 3. RH difficulty = the archimedean side of the seam `[SPECULATION — the new claim]`

The field's RH-face obstruction is the **no-margin archimedean positivity** (the carrier `m_ξ` Herglotz;
equivalently `κ₋ = 0`; the parent project's recurring "wall" is archimedean Weil positivity / the
`C > 0` / Connes-type semilocal positivity). The **finite RH face is fully understood and quantitative**
(`multiPair_carrier_exact_neg_inertia`: `κ₋ = #off-line zeros`, proven this session); what is *not*
finite — the regularized infinite passage — is precisely the **archimedean `Γ`-factor's Herglotz
contribution** in the Hadamard product (the on-line/regularized part). The off-line poles (the finite,
now-fully-handled part) are "multiplicative-visible"; the regularization that completes the carrier is
**archimedean**. So **RH's open core also lives on the archimedean side of the seam.**

`[SPECULATION]` Both apex difficulties are the *same* archimedean obstruction, read two ways: DSS reads
it as "is the non-period jet generic?"; RH reads it as "is the archimedean-completed type positive?"
The multiplicative wing is, in both readings, the *solved/period/GPC-shaped* side — consistent with
the field's slogan that the multiplicative wing is "free and zero-blind."

## 4. The unified bet and a concrete prediction `[CONJECTURE]`

If §1–§3 hold, the field needs **one** archimedean input feeding both faces:
- **a quantitative archimedean rigidity** — a bound on the `Γ-factor`/`s=1`-Laurent data — that is
  simultaneously (a) the Nesterenko arithmetic lower bound forcing (DSS-cross) [DSS face], and (b) the
  positivity/Herglotz input forcing `κ₋(m_ξ) = 0` [RH face]. The **multiplicity estimate**
  (`MultiplicityEstimate`, ledgered) is the common algebraic ingredient; the missing piece is the
  archimedean arithmetic/positivity bound.

**Prediction (falsifiable in spirit).** Any genuine progress on the apex must engage the **`Γ`-factor /
`s=1`-Laurent (Stieltjes) data**, not the integer `ζ`-values. Tool-independence corollary: methods that
only see the multiplicative wing (Euler product, prime sums, `ζ`-values) are **structurally blind** to
both apex obstructions — they live on the period/GPC side, which is *not* where the difficulty is. This
predicts the parent project's repeated finding that prime-side / Euler-side constructions are
"RH-blind" or "circular": they are on the wrong side of the seam.

## 5. Honest status

`[derived]` §1 (each `P_k` is a period+non-period sum — from the verified `P_k`/`a_j` formulas).
`[CONJECTURE/SPECULATION]` §2–§4 (the seam = the divide; both apex faces are the archimedean
obstruction; the unified archimedean bet). **Proven anchors:** the finite RH face
(`multiPair_carrier_exact_neg_inertia`) and the finite DSS face (`spectrum_esymm_algIndep`) — both
finite layers are theorems; the infinite apex is the single archimedean obstruction, here *named and
localized* (the seam = the period/non-period divide), not faked. The value: it predicts where to push
(archimedean `s=1`-Laurent / `Γ`-factor) and why multiplicative-only tools cannot reach the apex —
turning the parent project's empirical "RH-blindness of prime-side methods" into a structural
statement.
