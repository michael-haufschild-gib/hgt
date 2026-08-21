# CCM wall-Gram light-cone jet recovery

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadWallGramLightConeJetRecovery`.
This closes prime-power negative-light occurrence inside the differentiated actual wall-Gram
channel; global completed producer comparison and RH remain open.

## New knowledge

For one prime-power wall, let `C(ξ)` be reflected Mellin-wall chord energy, `B(ξ)` literal Suzuki
positive-minus-negative light energy, and `w` critical Mellin mass. Lean proves the function-level
identity

\[
C'(\xi)=4\pi\log(n)B(\xi).
\]

Thus the two-sheet ambiguity of a single scalar chord value disappears under the natural spectral
connection: differentiation selects orientation without division by mass, amplitude, or phase.
Combining this with the scalar center reserve gives exact negative-light occurrence

\[
8\pi\log(n)\|\ell_-(2\pi\xi)\|^2+C'(\xi)
=4\pi\log(n)w.
\]

At center, chord curvature is strictly positive:

\[
C''(0)=2w(2\pi\log n)^2>0.
\]

It is itself a positive dressing of the literal CCM/Suzuki prime-entry third-jet scale `q_n`:

\[
C''(0)=\frac{\pi^2}{4}\log(n)^5q_n.
\]

Finally, matched polar wall-light contact is not a separate source. If `M_n` is its oriented first
moment and `Q''(0)` its quadratic jet, Lean proves the division-free transmutation square

\[
(2\pi\log n)Q''(0)=M_nC''(0).
\]

## Frontier consequence

Prime-power source occurrence is sharper than previously stated. Raw negative light is already in
the actual wall-Gram carrier after adjoining its canonical spectral derivative; no external
square-root sheet choice is needed. Remaining work moves up one level: commute this derivative
through finite actual-head integration and Gamma/holonomy completion, then prove the completed
Schur residual uniformly lower-semi-bounded.

## Lean audit

- direct leaf check: passed;
- exact module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
