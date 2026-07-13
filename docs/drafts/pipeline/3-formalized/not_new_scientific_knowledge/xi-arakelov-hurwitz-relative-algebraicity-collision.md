# Xi Arakelov--Hurwitz relative algebraicity collision

- **ID:** `xi-arakelov-hurwitz-relative-algebraicity-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN ARITHMETIC VALUE-RELATION COLLISION
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiArakelovHurwitzRelativeAlgebraicityCollision.lean`

## Statement

For one complex point define

\[
w(\rho)=1-\rho^{-1},
\qquad
q(\rho)=e^{-2\pi i\rho},
\qquad
K_\rho=\mathbb Q(w(\rho)).
\]

Lean proves the relative value law

\[
w(\rho)\in\overline{\mathbb Q},\quad \operatorname{Im}\rho\ne0
\quad\Longrightarrow\quad
q(\rho)\text{ is transcendental over }K_\rho.
\]

Indeed, `K_rho/Q` is algebraic when `w(rho)` is algebraic. If `q(rho)` were algebraic over
`K_rho`, transitivity would make it algebraic over `Q`, contradicting the already formalized
Gelfond--Schneider collision.

The resulting RH chain is

```text
every Xi-zero Arakelov coordinate is an algebraic integer
  + every hypothetical right-half Hurwitz character is algebraic over Q(w(rho))
  -> q(rho) is algebraic over Q
  -> Gelfond--Schneider forces rho real
  -> Xi positivity on the open real critical strip excludes rho
  -> RH.
```

The capstone theorem is
`riemannHypothesis_of_xiArakelovCoordinatesIntegral_of_hurwitzCharacterAlgebraicOverArakelov`.

## Why this is a value relation rather than an orientation restatement

The two hypotheses have different blind spots.

- Integrality of `w(rho)` controls an arithmetic coordinate and its conjugate product, but does not
  locate the distinguished complex embedding on the unit circle.
- Algebraicity of `q(rho)` over `Q(w(rho))` is a mixed algebraic-curve constraint. Without
  algebraicity of `w(rho)`, it does not make either coordinate algebraic over `Q` and carries no
  critical-line sign.
- Their collision is rigid because an algebraic base extension cannot absorb the
  Gelfond--Schneider transcendence of the exponential character.

This is still a fringe bridge, not new scientific knowledge. Its engine is algebraicity
transitivity plus the previously formalized Gelfond--Schneider law.

## Open core

`[OPEN CORE]` Produce a source-defined polynomial or finite-module relation proving that
`q(rho)` is algebraic over `Q(w(rho))` at hypothetical right-half Xi zeros, and independently
produce arithmetic integrality of `w(rho)` there.

A concrete provider may be stated as a nonzero polynomial

\[
P_\rho(Y)\in\mathbb Q(w(\rho))[Y],
\qquad P_\rho(q(\rho))=0,
\]

arising from a finite source monodromy module. The relation must be constructed before selecting
the Xi divisor; merely choosing a polynomial after seeing `q(rho)` would be circular.

There is presently no evidence that either global provider is true. The theorem is useful as a
firewall: any arithmetic source model simultaneously producing integral Arakelov coordinates and
a finite algebraic Hurwitz-character module has already crossed the RH wall.

## Formal verification

Lean proves:

- `isAlgebraic_of_isAlgebraic_arakelovCoordinateField`;
- `monoScalar_transcendental_over_arakelovCoordinateField`;
- `xiRightArakelovHurwitzAlgebraic_of_integral_of_relativeAlgebraic`;
- `riemannHypothesis_of_xiArakelovCoordinatesIntegral_of_hurwitzCharacterAlgebraicOverArakelov`.

The module contains no new axiom or admitted proof.
