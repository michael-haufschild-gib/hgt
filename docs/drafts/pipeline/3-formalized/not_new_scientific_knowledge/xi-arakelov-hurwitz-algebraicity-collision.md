# Xi Arakelov--Hurwitz algebraicity collision

- **ID:** `xi-arakelov-hurwitz-algebraicity-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN ARITHMETIC VALUE COLLISION
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiArakelovHurwitzAlgebraicityCollision.lean`

## Statement

Attach to a complex point `rho` the two independently occurring coordinates

\[
w(\rho)=1-\frac1\rho,
\qquad
q(\rho)=e^{-2\pi i\rho}.
\]

The first is the Arakelov functional-equation coordinate. The second is the monodromy character
which classifies the differential-dependence fibers of the continued Hurwitz family.

Lean proves the general constraint law

\[
w(\rho)\in\overline{\mathbb Q},\quad \operatorname{Im}\rho\ne0
\quad\Longrightarrow\quad
q(\rho)\notin\overline{\mathbb Q}.
\]

More precisely,

\[
w(\rho),q(\rho)\in\overline{\mathbb Q}
\quad\Longrightarrow\quad
-2\rho\in\mathbb Q
\quad\Longrightarrow\quad
\operatorname{Im}\rho=0.
\]

The proof is a direct Gelfond--Schneider collision. Algebraicity of `w(rho)` pulls back through the
inverse Möbius transformation and makes `rho` algebraic. On the principal branch,

\[
q(\rho)=(-1)^{-2\rho}.
\]

If `-2rho` were algebraic irrational, Gelfond--Schneider would make this value transcendental.

Since the completed Xi function is strictly positive on the real segment `0 < rho < 1`, Lean then
proves

\[
\left.
\begin{array}{l}
w(\rho)\in\overline{\mathbb Q},\\
q(\rho)\in\overline{\mathbb Q}
\end{array}
\right\}
\quad\text{for every hypothetical right-half Xi zero }\rho
\quad\Longrightarrow RH.
\]

The chain is

```text
right-half Xi-zero Arakelov algebraicity
  + right-half Xi-zero Hurwitz-character algebraicity
  -> exponent rationality by Gelfond--Schneider
  -> the hypothetical zero is real
  -> positivity of Xi on the open real critical strip gives a contradiction
  -> RH.
```

## Anti-redressing attack

This is not a disguised zero-location sign.

- Algebraicity of `w(rho)` alone says only that `rho` is algebraic. It supplies no critical-line
  orientation.
- Algebraicity of `q(rho)` alone permits nonreal exponents: logarithms of algebraic character values
  produce such points.
- The contradiction occurs only when the two coordinates are required to be algebraic
  simultaneously. Their coupling is detected by the principal power `(-1)^(-2rho)`.

The theorem is nevertheless a bridge, not new scientific knowledge. After erasing the project
coordinates, its mathematical engine is a short corollary of Gelfond--Schneider.

## Open core and plausibility

`[OPEN CORE]` Produce a source-defined arithmetic mechanism which puts both coordinates of every
hypothetical right-half Xi zero into an algebraic extension, or prove the weaker local statement
that any right-half zero with algebraic Arakelov coordinate has algebraic Hurwitz monodromy.

A sufficient provider would be an algebraic monodromy realization whose characteristic polynomial
contains `q(rho)`, together with an algebraic Arakelov divisor model. Neither provider is presently
in the corpus.

This route is fringe. There is no evidence that Xi-zero Arakelov coordinates are algebraic; expected
transcendence makes a global algebraicity theorem implausible. Its value is different: it gives an
exact firewall. Any proposed arithmetic model placing both coordinates in one number field already
proves RH and must explain why off-line points cannot enter.

## Formal verification

Lean proves:

- `isAlgebraic_rho_of_arakelovW`;
- `monoScalar_eq_negOne_cpow`;
- `exists_rat_eq_neg_two_mul_of_arakelovW_algebraic_of_monoScalar_algebraic`;
- `monoScalar_transcendental_of_arakelovW_algebraic_of_im_ne_zero`;
- `im_eq_zero_of_arakelovW_algebraic_of_monoScalar_algebraic`;
- `xi_ne_zero_of_openCriticalStrip_of_arakelovW_algebraic_of_monoScalar_algebraic`;
- `riemannHypothesis_of_xiRightArakelovHurwitzAlgebraic`.

The module contains no new axiom or admitted proof.
