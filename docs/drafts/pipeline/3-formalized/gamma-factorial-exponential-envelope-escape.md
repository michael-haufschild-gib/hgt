# Gamma pole germ escapes its exponential-reciprocal harmonic envelope

- **ID:** `gamma-factorial-exponential-envelope-escape`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVEN IN LEAN] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The complete dominant harmonic envelope of the factorial Gamma pole germ is
  differential algebraic, but the exact germ crosses its common third-order differential
  discriminant at pure-factorial order two with nonzero coefficient `-24ζ(2)`.

## Goal

Identify what remains after every dominant harmonic coefficient has cancelled.  This is the first
test that distinguishes the exact Gamma pole germ from the whole two-parameter model produced by
its unbounded harmonic deformation.

## Theorem

Let

\[
 s_n=\frac{(-1)^{n+1}}{n!},\qquad g_n(x)=\Gamma(-n+s_nx),
\]

and define the denominator-free third-jet discriminant

\[
 \mathcal E_3(y)=
 (y^2y'''-3yy'y''+2(y')^3)^2-4(yy''-(y')^2)^3.
\]

Every exponential-reciprocal germ `y(x)=-C e^{ax}/x` satisfies `𝔈₃(y)=0`.  Nevertheless, for
every `x ≠ 0`, Lean proves

\[
 \frac{\mathcal E_3(g_n)(x)}{s_n^2}
   \longrightarrow -\frac{4\pi^2}{x^{10}}.
\]

Equivalently, if `q_n=g_n'/g_n`, then

\[
 \frac{(q_n'')^2-4(q_n')^3}{s_n^2}
   \longrightarrow -\frac{4\pi^2}{x^4}
   =-\frac{24\zeta(2)}{x^4}.
\]

## Meaning

The pole microscope is not governed by a single harmonic valuation.  Its dominant coefficients
collapse onto a differential-algebraic exponential-reciprocal envelope.  The first transverse
datum below that envelope is the even zeta value `ζ(2)`.  The exact germ therefore carries a
lexicographic harmonic-zeta signature rather than a one-scale asymptotic signature.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/GammaFactorialExponentialEnvelopeEscape.lean`.

Headline declarations:

- `exponentialReciprocalJetDiscriminant`
- `gammaFactorialExponentialEnvelopeDefect_eq`
- `tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq`
- `tendsto_gammaFactorialExponentialEnvelopeDefect_div_factorialScale_sq`

The module compiles directly; its individual Lake target builds.  Axiom audits for the two limit
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.  Formal lint passes.  No full build
and no numerical computation were used.

## Gates

- [x] 0 → 1 in-progress: exact source-pure invariant and falsifier isolated
- [x] 1 → 2 fully-proven: complete symbolic proof with nonzero coefficient
- [x] 2 → 3 formalized: headline theorems in Lean, targeted build and axiom audit pass
- [ ] 3 → 4 publication-ready: independent priority audit and standalone exposition complete

## Approach

Differentiate the exact digamma shift law.  The shifted square-harmonic sum converges to `ζ(2)`,
while the local trigamma contributes a second copy of `ζ(2)`.  The second polygamma correction is
smaller by one factorial scale.  Substitution into `q''²-4q'³` gives `-24ζ(2)/x⁴`; clearing the
logarithmic denominators multiplies this by the reciprocal boundary factor `x⁻⁶`.

## Log

- 2026-07-15 — proved and formalized after the quadratic Schwarzian residue exposed the dominant
  exponential-reciprocal envelope and falsified harmonic-only injectivity.
