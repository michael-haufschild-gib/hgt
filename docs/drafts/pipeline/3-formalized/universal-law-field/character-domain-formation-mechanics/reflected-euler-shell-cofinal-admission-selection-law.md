# Reflected Euler-shell cofinal admission and selection law

- **ID:** ULF-CDFM-2
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveReflectedShellCofinalSelection`
- **Type:** LITERAL SOURCE FORMATION / COFINAL PROPERNESS / GLOBAL SELECTION GATE
- **Statement:** Every fixed real character and its reflected mate are jointly admitted by some
  marked Euler-shell Gibbs fibre. Requiring the same pair to be admitted by every fibre above the
  normalization wall forces the neutral character exactly.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LITERAL ARITHMETIC SOURCE]`
  `[FINITE-TO-COFINAL SELECTION] [FUNCTIONAL-EQUATION SYMMETRIC] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS]`
  `[PRE-ZERO] [NOT RH]`

## 1. Literal source family

Fix shell depth `m >= 12`. For `sigma > 1`, let

\[
 P_{m,\sigma}(n)=\frac{a_m(n)n^{-\sigma}}{Z_m(\sigma)},
 \qquad
 X_{m,\sigma}(n)=-\log n+\mathbb E_{m,\sigma}[\log n].
\]

The corpus already proves the exact term identity

\[
 P_{m,\sigma}(n)e^{tX_{m,\sigma}(n)}
 =c_{m,\sigma,t}\,a_m(n)n^{-(\sigma+t)},
 \qquad c_{m,\sigma,t}>0,
 \tag{RS.1}
\]

and divergence at the normalization wall `sigma+t=1`.

Define global reflected admission by

\[
 \operatorname{Adm}^{\pm}_m(t)
 \iff
 \forall\sigma>1:\quad
 \sum_nP_{m,\sigma}(n)e^{tX_{m,\sigma}(n)}<\infty
 \text{ and }
 \sum_nP_{m,\sigma}(n)e^{-tX_{m,\sigma}(n)}<\infty.
 \tag{RS.2}
\]

This is one source genealogy, not a family chosen from an RH divisor.

## 2. Finite survival

### Theorem 2.1

For every `t in R`, some finite fibre admits both `t` and `-t`.

### Proof

Take `sigma=2+|t|`. Then `sigma+t>1` and `sigma-t>1`. Equation `(RS.1)` reduces both series to
convergent shell Mellin series. QED.

Thus no fixed-stage route can see the selector. Failure is genuinely cofinal.

## 3. Functional-equation symmetry

### Theorem 3.1

\[
 \operatorname{Adm}^{\pm}_m(-t)\iff\operatorname{Adm}^{\pm}_m(t).
 \tag{RS.3}
\]

### Proof

The sign action exchanges the two summability clauses in `(RS.2)`. QED.

Functional-equation reflection is therefore information-neutral on this global admission law. It
does not select by itself; it forces both orientations to face the same wall.

## 4. Literal cofinal properness

### Theorem 4.1

\[
 \boxed{\operatorname{Adm}^{\pm}_m(t)\iff t=0.}
 \tag{RS.4}
\]

### Proof

The neutral character is admitted because its two series are the normalized shell probability.

Suppose `t != 0` and set `sigma=1+|t|`. If `t>0`, the reflected shift satisfies
`sigma-t=1`. If `t<0`, the direct shift satisfies `sigma+t=1`. In either case one clause of
`(RS.2)` is exactly the already-proved divergent wall series, contradiction. QED.

No estimate, limit exchange, zero hypothesis, or fitted detector enters the proof.

## 5. Fusion meaning

The same marked shell source already has four Lean-certified faces:

1. positive Gibbs transport under real tilt;
2. phase/recurrence under imaginary tilt;
3. complete centered-moment and analytic-jet tower;
4. normalization-wall lifetime.

The present theorem supplies their missing global formation law. Real and imaginary interventions
are not separate objects: they are gauges of one complex-time source germ. Phase recurrence is
vertical and survives every finite fibre; reflected real admission is horizontal and collapses
cofinally. The new conservation statement is exact:

> finite formation preserves every character somewhere, while complete reflected formation
> preserves only zero.

This is a concrete mechanism behind the corpus pattern “closed observer projection, open lifted
history.” Compact phase observation cannot repair lost real admission.

## 6. Selection interface and hard boundary

For a physical transverse grade `g`, a source-first RH application now needs only the typed landing

\[
 \text{physical law event}\Longrightarrow\operatorname{Adm}^{\pm}_m(g).
 \tag{RS.5}
\]

Then `(RS.4)` forces `g=0`. The theorem does **not** prove `(RS.5)`. In particular:

- a divisor zero does not automatically imply global shell admission;
- functional equation and common recovery cannot manufacture admission;
- one finite shell fibre never selects;
- post-zero insertion of `(RS.5)` would be circular.

The remaining problem is now sharply typed: construct one coefficient-faithful pre-divisor
comparison showing that the physical horizontal grade is a globally admitted character of the
complete reflected source genealogy. No additional positivity, recurrence, moment, or properness
theorem is missing at this interface.

## 7. Lean certification

`HTGeometry.ConstitutiveReflectedShellCofinalSelection` certifies exactly:

1. summability inside the shifted shell half-plane;
2. finite reflected admission for every real character;
3. sign-action invariance;
4. global admission iff neutrality;
5. one capstone packaging finite survival and cofinal selection.

No numerical computation, extra axiom, or RH premise is permitted.

## 8. Log

- 2026-08-14 — literal shell genealogy and cofinal reflected selector proved on paper and in Lean.
