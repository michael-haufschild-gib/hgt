# Positive-shift Hurwitz and polygamma asymptotic

- **ID:** `positive-shift-hurwitz-polygamma-asymptotic`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For every positive integer `q`, the scaled positive-real Hurwitz value and the
  corresponding polygamma jet have their exact first asymptotic constants.

## Result

Lean proves

\[
x^q\zeta(q+1,x)\longrightarrow\frac1q,
\qquad
x^q\psi^{(q)}(x)\longrightarrow(-1)^{q+1}(q-1)!.
\]

The proof identifies the Hurwitz value with a shifted power tail and applies the real-mesh
antitone Riemann-sum theorem.

## Lean

`formal/GaloisForLFunctions/Hurwitz/ShiftedPowerTailAsymptotic.lean`, imported by the `Hurwitz`
umbrella.

## Gates

- [x] shifted power-tail limit
- [x] Hurwitz value specialization
- [x] polygamma specialization
- [x] consumed by the completed prime--Gamma source asymptotic
