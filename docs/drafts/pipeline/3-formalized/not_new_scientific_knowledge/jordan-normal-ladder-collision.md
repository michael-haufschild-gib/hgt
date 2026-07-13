# Jordan-normal Hedenmalm blocks collide with the first RH ladder

- **ID:** `jordan-normal-ladder-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN CROSS-ROUTE COLLISION / OPERATOR NORMALITY
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiHedenmalmJordanNormalCollision.lean`

## Statement

At an Xi divisor point `rho`, the canonical Hedenmalm divided-chain block is

\[
J_\rho=\lambda_\rho I+N_{m_\rho},
\]

where `m_rho` is the exact Xi multiplicity and `N_m` is the one-step nilpotent Jordan shift.
Lean proves

\[
J_\rho J_\rho^*=J_\rho^*J_\rho
\quad\Longleftrightarrow\quad
m_\rho=1.
\]

The eigenvalue `lambda_rho` need not be real.  Normality therefore detects simplicity only;
Hermiticity detects the stronger conjunction of simplicity and critical-line orientation.

It is enough to assume normality only at existing right-half Xi divisor points.  Combining this
with any positive RH-ladder rung gives

```text
right-half local Hedenmalm Jordan normality
  -> every hypothetical right-half Xi zero has order one

one positive RH-ladder rung
  -> every hypothetical right-half Xi zero has even order

order one + even order
  -> no right-half Xi zero
  -> RH.
```

Formally,

\[
RHLadder(k),\quad k\ge1,
\quad
\forall\rho\in Z_\Xi\cap\{\Re s>1/2\},\ J_\rho\text{ normal}
\quad\Longrightarrow\quad RH.
\]

No condition is imposed on critical-line or left-half local blocks.

## Anti-redressing attack

The normality premise is not RH in operator notation.  A simple off-critical zero gives a
one-dimensional scalar block, which is normal regardless of its nonreal eigenvalue.  Thus local
normality alone allows off-critical zeros.  The contradiction appears only after importing the
independent dyadic multiplicity constraint from the RH ladder.

The existing Hermitian condition is unsuitable for this purpose because Hermiticity of every
block is already equivalent to `RH + XiZerosSimple`.  Passing from Hermitian to normal strips away
exactly the orientation content and leaves a genuine multiplicity-only interface.

## Open core

`[OPEN CORE]` Supply one positive ladder rung and right-half local Jordan normality from independent
source constraints.  Equivalently, prove that the nilpotent divided-chain shift vanishes at every
right-half divisor point without assuming its position or importing global Xi simplicity.

Possible providers already isolated in the corpus are:

- the first removable Hedenmalm quotient-value constraint;
- density of the Hedenmalm theta evaluation span;
- the continued-Cauchy-to-Hedenmalm closure inclusion.

Each of these currently yields global simplicity.  The new capstone shows that only the
right-half local normality fragment is required when paired with one ladder rung.

## Formal verification

Lean proves:

- `xiSupportMultiplicity_eq_analyticOrderAt_toNat`;
- `xiLocalJordanNormal_iff_multiplicity_one`;
- `all_xiLocalJordanNormal_iff_simple`;
- `riemannHypothesis_of_rhLadder_of_rightHalfLocalJordanNormal`;
- `riemannHypothesis_of_rhLadder_one_of_rightHalfLocalJordanNormal`;
- the corresponding global-normality capstones.

The named module build passes in the repository toolchain.
