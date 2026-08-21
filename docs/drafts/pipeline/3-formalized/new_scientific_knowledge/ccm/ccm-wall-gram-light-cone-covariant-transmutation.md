# CCM wall-Gram light-cone covariant transmutation

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadWallGramLightConeCovariantTransmutation`.
This supplies coefficient-faithful occurrence of differentiated wall orientation inside the
literal matched prime-minus-polar producer. Completed finite-block sign/Schur closure remains open.

## New knowledge

Raw chord jet `C_n'(ξ)` is reflection-odd and cannot factor through the scalar completed producer.
The corpus already contains the required covariant connection: matched polar sine profile `S_n(ξ)`,
which is also reflection-odd. Define

\[
K_n(f)=\int C_n'(\xi)S_n(\xi)|\widehat f(\xi)|^2\,d\xi.
\]

For every prime-power label `(p,e)` with `n=p^(e+1)`, Lean proves the exact transmutation

\[
K_n(f)=\bigl(2\pi\log(n)\,w_n\bigr)I_n(f),
\]

where `I_n(f)` is the existing actual matched Suzuki current. The coefficient is strictly
positive. No new fitted carrier is introduced.

Because both odd factors reverse together, Lean proves

\[
K_n(\mathcal R f)=K_n(f).
\]

Thus covariantization bypasses the reflection-fiber no-go without violating it: raw orientation
does not descend to the even quotient, but its contraction with the odd polar connection does.

Most importantly, multiplying the actual matched cell by its forced positive rate gives

\[
(2\pi\log n\,w_n)\,(\text{prime}_n-\text{polar}_n)
=
(2\pi\log n\,w_n)\,\text{symmetric}_n-K_n.
\]

The covariant jet occurs with coefficient exactly `-1`. Lean also transfers the corpus's
quadratic-aperture bound to `K_n` and proves a finite labeled packet assembly preserving every
prime and valuation depth.

## Higher principle

Orientation transport is not scalar sheet selection. It is covariant differentiation followed by
contraction with a connection of the same parity. This turns a forbidden reflection-odd scalar
into the already-summable reflection-even current of the actual producer. Earlier square-root,
center-reserve, and parity obstructions were shadows of omitting this connection.

Next hard problem is now precise: compare the positive light slacks from the uncontracted jet with
the symmetric matched-cell remainder after the same positive scaling, then insert the resulting
completed square into the actual finite exceptional Schur block. No separate prime/polar absolute
envelope is licensed.

## Lean audit

- scratch check: passed;
- direct leaf check: passed;
- exact leaf-module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
